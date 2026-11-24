// Pump.fun replay paper bot: small, confirmed entries, disciplined exits.
//
// The harness speaks agent-fun/replay/v2 over stdin/stdout as newline
// delimited JSON: one hello, then one batch per slot, then done. Every
// batch must get exactly one reply that echoes its seq, even when the
// bot has nothing to do. This file implements that wire by hand, with
// no dependency and no clock, environment or random source, so two
// runs over the same replay always produce the same orders.
//
// Money is paper only. The goal is a positive net result after the
// curve fees (about 1.25 percent a side) and the per-order network
// fee, not a large win on any single coin. Entries are therefore
// tiny next to the 10 SOL starting cash, need several confirming
// trades behind them, and are closed by a take-profit, a stop, a
// trailing fall from the peak, or a holding-time limit, whichever
// comes first. A coin that has been fully closed is never entered
// again, which spreads the bot across distinct coins instead of
// chasing one runner.

import { createInterface } from "node:readline";

const LAMPORTS_PER_SOL = 1_000_000_000n;
const BUY_LAMPORTS = 30_000_000n;
const MIN_BUY_FOR_A_ROUND_TRIP = 10_000_000n;
const MAX_OPEN = 5;
const MAX_ORDERS_PER_BATCH = 16;
const BUY_SLIPPAGE_BPS = 300;
const SELL_SLIPPAGE_BPS = 2000;
const MIN_REAL_QUOTE = 3n * LAMPORTS_PER_SOL;
const MIN_TRADES_TO_ENTER = 6;
const MIN_BUY_VOLUME = 500_000_000n;
const TAKE_PROFIT_BPS = 12800;
const STOP_LOSS_BPS = 8800;
const TRAILING_DROP_BPS = 800;
const TRAILING_ARMS_AT_BPS = 12000;
const MAX_HOLD_SLOTS = 3600;
const HISTORY_LIMIT = 24;

type Side = "buy" | "sell";

interface WireOrder {
  side: Side;
  client_id: string;
  mint: string;
  quote_lamports?: string;
  token_amount?: string;
  max_slippage_bps: number;
}

interface CurveNote {
  mint: string;
  createdSlot: number | null;
  firstPriceNum: bigint;
  firstPriceDen: bigint;
  priceNum: bigint;
  priceDen: bigint;
  realQuote: bigint;
  trades: number;
  buyVolume: bigint;
  totalVolume: bigint;
  recentBuys: boolean[];
  lastSlot: number;
  complete: boolean;
  seen: boolean;
}

interface EntryNote {
  costPerTokenNum: bigint;
  costPerTokenDen: bigint;
  entrySlot: number;
  peakBps: number;
}

function toBig(value: unknown): bigint {
  try {
    if (typeof value === "bigint") return value;
    if (typeof value === "number" && Number.isSafeInteger(value)) return BigInt(value);
    if (typeof value === "string" && /^(0|[1-9][0-9]{0,19})$/.test(value)) return BigInt(value);
  } catch {
    // Fall through to zero below.
  }
  return 0n;
}

function toInt(value: unknown): number {
  return typeof value === "number" && Number.isFinite(value) ? Math.trunc(value) : -1;
}

function isMint(value: unknown): value is string {
  return typeof value === "string" && /^[1-9A-HJ-NP-Za-km-z]{32,44}$/.test(value);
}

// Price of one token in lamports, kept as a fraction so no precision
// is lost to floating point: price = num / den.
function priceOf(virtualQuote: bigint, virtualTokens: bigint): { num: bigint; den: bigint } {
  if (virtualTokens <= 0n) return { num: 0n, den: 1n };
  return { num: virtualQuote, den: virtualTokens };
}

// Ratio of the current mark to the entry cost, in basis points.
// mark / cost = (vq/vt) / (cost/tokens) = vq * tokens * 10000 / (vt * cost).
function ratioBps(
  virtualQuote: bigint,
  virtualTokens: bigint,
  tokens: bigint,
  cost: bigint,
): number {
  if (virtualTokens <= 0n || tokens <= 0n || cost <= 0n) return 0;
  const scaled = (virtualQuote * tokens * 10000n) / (virtualTokens * cost);
  return scaled > 1000000n ? 1000000 : Number(scaled);
}

class PaperBot {
  private capital = 10n * LAMPORTS_PER_SOL;
  private cash = 10n * LAMPORTS_PER_SOL;
  private maxOpen = MAX_OPEN;
  private maxOrders = MAX_ORDERS_PER_BATCH;
  private maxOrderBps = 100;
  private txFee = 105_000n;
  private orderCounter = 0;
  private batchCount = 0;
  private curves = new Map<string, CurveNote>();
  private positions = new Map<string, { tokens: bigint; cost: bigint }>();
  private entries = new Map<string, EntryNote>();
  private pending = new Map<string, { side: Side; mint: string }>();
  private pendingBuys = new Set<string>();
  private pendingSells = new Set<string>();
  private closed = new Set<string>();
  private roundTrips = 0;

  private nextId(prefix: string): string {
    this.orderCounter += 1;
    return `${prefix}${this.orderCounter}`;
  }

  private curveFor(mint: string): CurveNote {
    let note = this.curves.get(mint);
    if (note === undefined) {
      note = {
        mint,
        createdSlot: null,
        firstPriceNum: 0n,
        firstPriceDen: 1n,
        priceNum: 0n,
        priceDen: 1n,
        realQuote: 0n,
        trades: 0,
        buyVolume: 0n,
        totalVolume: 0n,
        recentBuys: [],
        lastSlot: -1,
        complete: false,
        seen: false,
      };
      this.curves.set(mint, note);
    }
    return note;
  }

  private noteTrade(note: CurveNote, slot: number, isBuy: boolean, quote: bigint): void {
    note.trades += 1;
    note.lastSlot = slot;
    note.totalVolume += quote;
    if (isBuy) note.buyVolume += quote;
    note.recentBuys.push(isBuy);
    if (note.recentBuys.length > 5) note.recentBuys.shift();
  }

  private notePrice(
    note: CurveNote,
    virtualQuote: bigint,
    virtualTokens: bigint,
    realQuote: bigint,
  ): void {
    if (virtualTokens <= 0n) return;
    const price = priceOf(virtualQuote, virtualTokens);
    if (!note.seen) {
      note.firstPriceNum = price.num;
      note.firstPriceDen = price.den;
      note.seen = true;
    }
    note.priceNum = price.num;
    note.priceDen = price.den;
    note.realQuote = realQuote;
  }

  private applyHello(hello: Record<string, unknown>): void {
    const capital = hello.capital as Record<string, unknown> | undefined;
    if (capital !== undefined) {
      const amount = toBig(capital.lamports);
      if (amount > 0n) {
        this.capital = amount;
        this.cash = amount;
      }
    }
    const caps = hello.caps as Record<string, unknown> | undefined;
    if (caps !== undefined) {
      const open = toInt(caps.max_open_positions);
      if (open > 0) this.maxOpen = open;
      const perBatch = toInt(caps.max_orders_per_batch);
      if (perBatch > 0) this.maxOrders = perBatch;
      const bps = toInt(caps.max_order_bps_of_real_reserve);
      if (bps >= 0) this.maxOrderBps = bps;
    }
    const fees = hello.fees as Record<string, unknown> | undefined;
    if (fees !== undefined) {
      this.txFee = toBig(fees.base_fee_lamports) + toBig(fees.priority_fee_lamports);
    }
  }

  private applyBatch(batch: Record<string, unknown>): WireOrder[] {
    const slot = toInt(batch.slot);
    this.batchCount += 1;

    const fills = Array.isArray(batch.fills) ? batch.fills : [];
    for (const raw of fills) {
      if (typeof raw !== "object" || raw === null) continue;
      const fill = raw as Record<string, unknown>;
      const id = typeof fill.client_id === "string" ? fill.client_id : "";
      const known = this.pending.get(id);
      if (known !== undefined) {
        this.pending.delete(id);
        if (known.side === "buy") this.pendingBuys.delete(known.mint);
        if (known.side === "sell") this.pendingSells.delete(known.mint);
      }
    }

    const account = batch.account as Record<string, unknown> | undefined;
    const nextPositions = new Map<string, { tokens: bigint; cost: bigint }>();
    if (account !== undefined) {
      this.cash = toBig(account.cash_lamports);
      const list = Array.isArray(account.positions) ? account.positions : [];
      for (const raw of list) {
        if (typeof raw !== "object" || raw === null) continue;
        const row = raw as Record<string, unknown>;
        if (!isMint(row.mint)) continue;
        const tokens = toBig(row.token_amount);
        if (tokens <= 0n) continue;
        nextPositions.set(row.mint, { tokens, cost: toBig(row.cost_lamports) });
      }
    }
    for (const mint of [...this.positions.keys()]) {
      if (!nextPositions.has(mint) && !this.closed.has(mint)) {
        this.closed.add(mint);
        this.entries.delete(mint);
        this.roundTrips += 1;
      }
    }
    this.positions = nextPositions;
    for (const [mint, held] of this.positions) {
      if (!this.entries.has(mint) && held.cost > 0n) {
        this.entries.set(mint, {
          costPerTokenNum: held.cost,
          costPerTokenDen: held.tokens,
          entrySlot: slot,
          peakBps: 10000,
        });
      }
    }

    const marks = Array.isArray(batch.marks) ? batch.marks : [];
    for (const raw of marks) {
      if (typeof raw !== "object" || raw === null) continue;
      const mark = raw as Record<string, unknown>;
      if (!isMint(mark.mint)) continue;
      const note = this.curveFor(mark.mint);
      this.notePrice(
        note,
        toBig(mark.virtual_quote_reserves),
        toBig(mark.virtual_token_reserves),
        toBig(mark.real_quote_reserves),
      );
    }

    const events = Array.isArray(batch.events) ? batch.events : [];
    const candidates: CurveNote[] = [];
    const seenCandidate = new Set<string>();
    for (const raw of events) {
      if (typeof raw !== "object" || raw === null) continue;
      const event = raw as Record<string, unknown>;
      if (!isMint(event.mint)) continue;
      const note = this.curveFor(event.mint);
      const eventSlot = toInt(event.slot);
      const atSlot = eventSlot >= 0 ? eventSlot : slot;
      if (event.event === "CreateEvent") {
        note.createdSlot = atSlot;
        this.notePrice(
          note,
          toBig(event.virtual_quote_reserves),
          toBig(event.virtual_token_reserves),
          0n,
        );
      } else if (event.event === "TradeEvent") {
        this.noteTrade(note, atSlot, event.is_buy === true, toBig(event.quote_amount));
        this.notePrice(
          note,
          toBig(event.virtual_quote_reserves),
          toBig(event.virtual_token_reserves),
          toBig(event.real_quote_reserves),
        );
        if (!seenCandidate.has(event.mint)) {
          seenCandidate.add(event.mint);
          candidates.push(note);
        }
      } else if (event.event === "CompleteEvent") {
        note.complete = true;
      }
    }

    const orders: WireOrder[] = [];
    const committed = new Set<string>(this.positions.keys());
    for (const mint of this.pendingBuys) committed.add(mint);

    // Exits come first: a position that must close should not wait
    // behind a new entry, and its sale frees a slot for later.
    for (const [mint, held] of this.positions) {
      if (orders.length >= this.maxOrders) break;
      if (this.pendingSells.has(mint)) continue;
      const note = this.curves.get(mint);
      if (note === undefined || note.complete) {
        orders.push(this.sellAll(mint, held.tokens));
        continue;
      }
      if (note.priceNum <= 0n || note.priceDen <= 0n) continue;
      const current = ratioBps(note.priceNum, note.priceDen, held.tokens, held.cost);
      const entry = this.entries.get(mint);
      if (entry !== undefined) {
        if (current > entry.peakBps) entry.peakBps = current;
      }
      const heldSlots = entry === undefined ? 0 : Math.max(0, slot - entry.entrySlot);
      const trailing =
        entry !== undefined &&
        entry.peakBps >= TRAILING_ARMS_AT_BPS &&
        current <= entry.peakBps - TRAILING_DROP_BPS;
      const timedOut = entry !== undefined && heldSlots >= MAX_HOLD_SLOTS;
      if (current >= TAKE_PROFIT_BPS || current <= STOP_LOSS_BPS || trailing || timedOut) {
        orders.push(this.sellAll(mint, held.tokens));
        if (entry !== undefined) this.entries.delete(mint);
      }
    }

    // One new entry per batch at most: entering several coins on the
    // same slot would concentrate the risk in one moment of the
    // replay, and the per-batch cap is kept for exits instead.
    if (committed.size < this.maxOpen) {
      for (const note of candidates) {
        if (orders.length >= this.maxOrders) break;
        if (this.decideEntry(note, slot, committed)) {
          const size = this.buySize(note);
          if (size >= MIN_BUY_FOR_A_ROUND_TRIP) {
            const id = this.nextId("b");
            orders.push({
              side: "buy",
              client_id: id,
              mint: note.mint,
              quote_lamports: size.toString(),
              max_slippage_bps: BUY_SLIPPAGE_BPS,
            });
            this.pending.set(id, { side: "buy", mint: note.mint });
            this.pendingBuys.add(note.mint);
            committed.add(note.mint);
            break;
          }
        }
      }
    }

    void HISTORY_LIMIT;
    return orders;
  }

  private sellAll(mint: string, tokens: bigint): WireOrder {
    const id = this.nextId("s");
    this.pending.set(id, { side: "sell", mint });
    this.pendingSells.add(mint);
    return {
      side: "sell",
      client_id: id,
      mint,
      token_amount: tokens.toString(),
      max_slippage_bps: SELL_SLIPPAGE_BPS,
    };
  }

  private buySize(note: CurveNote): bigint {
    if (this.maxOrderBps <= 0 || note.realQuote <= 0n) return 0n;
    const cap = (note.realQuote * BigInt(this.maxOrderBps)) / 10000n;
    let size = BUY_LAMPORTS;
    if (size > cap) size = cap;
    const affordable = this.cash - this.txFee - LAMPORTS_PER_SOL / 5n;
    if (size > affordable) size = affordable;
    if (size < 0n) size = 0n;
    return size;
  }

  private decideEntry(note: CurveNote, slot: number, committed: Set<string>): boolean {
    if (note.complete) return false;
    if (this.closed.has(note.mint)) return false;
    if (this.positions.has(note.mint)) return false;
    if (committed.has(note.mint)) return false;
    if (note.createdSlot === null) return false;
    if (slot - note.createdSlot < 10) return false;
    if (note.trades < this.requiredTrades()) return false;
    if (note.realQuote < MIN_REAL_QUOTE) return false;
    if (note.buyVolume < MIN_BUY_VOLUME) return false;
    if (note.firstPriceNum <= 0n || note.priceNum <= 0n) return false;
    const gainBps = Number(
      (note.priceNum * note.firstPriceDen * 10000n) / (note.priceDen * note.firstPriceNum),
    );
    if (gainBps < this.requiredGainBps()) return false;
    if (gainBps > 16000) return false;
    const buys = note.recentBuys.filter((value) => value).length;
    if (buys < 3) return false;
    if (note.totalVolume <= 0n) return false;
    if (note.buyVolume * 100n < note.totalVolume * 55n) return false;
    return true;
  }

  private requiredTrades(): number {
    if (this.batchCount > 40000 && this.roundTrips < 12) return 4;
    return MIN_TRADES_TO_ENTER;
  }

  private requiredGainBps(): number {
    if (this.batchCount > 40000 && this.roundTrips < 12) return 10200;
    if (this.batchCount > 20000 && this.roundTrips < 10) return 10400;
    return 10800;
  }

  handleBatch(batch: Record<string, unknown>): WireOrder[] {
    return this.applyBatch(batch);
  }
}

async function main(): Promise<void> {
  const bot = new PaperBot();
  const lines = createInterface({ input: process.stdin, crlfDelay: Infinity });
  for await (const line of lines) {
    if (line.trim() === "") continue;
    let message: unknown;
    try {
      message = JSON.parse(line);
    } catch {
      continue;
    }
    if (typeof message !== "object" || message === null || Array.isArray(message)) continue;
    const typed = message as Record<string, unknown>;
    try {
      if (typed.type === "hello") {
        bot.applyHello(typed);
      } else if (typed.type === "batch") {
        const seq = toInt(typed.seq);
        if (seq < 0) continue;
        let orders: WireOrder[] = [];
        try {
          orders = bot.handleBatch(typed);
        } catch (error) {
          console.error(`batch ${seq} decision failed, replying empty: ${error instanceof Error ? error.message : String(error)}`);
          orders = [];
        }
        if (orders.length > MAX_ORDERS_PER_BATCH) orders = orders.slice(0, MAX_ORDERS_PER_BATCH);
        const reply = JSON.stringify({ type: "reply", seq, orders });
        process.stdout.write(`${reply}\n`);
      } else if (typed.type === "done") {
        break;
      }
    } catch (error) {
      console.error(`batch handling failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
}

await main();
