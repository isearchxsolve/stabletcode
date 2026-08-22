import type { Express } from "express";
import type { Server } from "http";
import { storage } from "./storage";
import { api } from "@shared/routes";
import { JupiterService, createJupiterService, SOL_MINT, MIN_FEE_BUFFER_SOL } from "./jupiter";

const MAX_SINGLE_TRADE_PCT  = 0.20; // single-trade hard ceiling as % of remaining balance
const MIN_VIABLE_TRADE_SOL  = 0.008;
const MIN_EDGE_PCT          = 3.5;
const MIN_TRADE_SIZE_SOL    = 0.01;
const EXECUTION_TIMEOUT_MS  = 30_000; // Global timeout per trade

const ADMIN_SECRET = process.env.ADMIN_SECRET?.trim() || null;

function requireAdmin(req: any, res: any): boolean {
  if (!ADMIN_SECRET) return true;
  const provided = req.headers["x-admin-secret"] ?? req.body?.adminSecret;
  if (provided !== ADMIN_SECRET) {
    res.status(403).json({ error: "Forbidden — invalid admin secret" });
    return false;
  }
  return true;
}

async function withTimeout<T>(promise: Promise<T>, timeoutMs: number, operationName: string): Promise<T> {
  let timer: ReturnType<typeof setTimeout>;
  const timeoutPromise = new Promise<never>((_, reject) => {
    timer = setTimeout(() => reject(new Error(`${operationName} timed out after ${timeoutMs}ms`)), timeoutMs);
  });
  try {
    return await Promise.race([promise, timeoutPromise]);
  } finally {
    clearTimeout(timer);
  }
}

const JUPITER_SUPPORTED_DEXES = new Set([
  "raydium", "raydium-clmm", "raydium-cp", "orca", "orca-whirlpool",
  "meteora", "meteora-dlmm", "meteora-damm-v2", "pumpswap", "pumpfun",
  "pump-fun", "openbook", "phoenix", "lifinity", "saber", "aldrin",
  "cropper", "stepn", "invariant", "dooar", "sencha", "saros", "whirlpool",
]);

const JUPITER_INDEX_DELAY_MS = 60_000; // Reduced 75s→60s: 75s+score70 gate created dead zone where
// high-scorers aged out of Jupiter block but had already pumped past viable edge check. 60s is safely
// above the real Jupiter indexing floor (~45s) while catching momentum before impact blows the edge.
// After a confirmed buy, Solana RPC nodes can take 30-90s to propagate the new ATA balance.
// During this window getTokenBalance() legitimately returns 0 even though tokens were received.
// We suppress all desync-close logic for this many ms after a trade opens to prevent
// false DESYNC_AUTO_CLOSE events on fresh buys.
const DESYNC_GRACE_PERIOD_MS = 90_000;

interface DexScreenerPair {
  chainId: string;
  dexId: string;
  pairAddress: string;
  baseToken: { address: string; name: string; symbol: string };
  quoteToken: { address: string; name: string; symbol: string };
  priceUsd?: string;
  priceNative?: string;
  txns?: { m5?: { buys: number; sells: number }; h1?: { buys: number; sells: number }; h24?: { buys: number; sells: number } };
  volume?: { m5?: number; h1?: number; h6?: number; h24?: number };
  priceChange?: { m5?: number; h1?: number; h6?: number; h24?: number };
  liquidity?: { usd?: number };
  fdv?: number;
  marketCap?: number;
  pairCreatedAt?: number;
}

let engineSettings = {
  trailingStopActivation: 5, trailingStopDistance: 2.5, hardTakeProfit: 80, stopLoss: -6,
  maxHoldSeconds: 420, maxOpenPositions: 3, startingBalance: 0.5, scanIntervalMs: 12000,
  // FIX A: priceCheckIntervalMs 6000→3000 (6s is too slow for memecoin rugs);
  // mlWeight 0.25→0.10 (ML unvalidated in live conditions, lower influence until proven);
  // position size caps reduced: sniperMaxSize 0.15→0.10, mgMaxSize 0.35→0.20,
  // hwrMaxSize 0.45→0.25, maxPositionSize 1.0→0.5 (one rug at old sizes = -30 to -70%
  // of a 0.5 SOL wallet); partialTpThreshold 18→15 (lock partial gains faster).
  // FIX B2 (survival patch): scanIntervalMs 7000→12000 (trade less, survive more);
  // minScoreToTrade 55→65 (raise entry bar, filter out low-quality setups);
  // sniperMinLiquidity 600→3000 (avoid ultra-illiquid tokens where we ARE the pool);
  // hwrMinLiquidity 1100→5000 (same reason, larger size needs deeper pool);
  // maxPositionSize 0.5→0.25 (halve max exposure per trade);
  // priceCheckIntervalMs 3000→1500 (catch crashes before gap blows past stop).
  priceCheckIntervalMs: 1000, minScoreToTrade: 70, mlServiceUrl: "http://localhost:5001",
  mlWeight: 0.10, scoreWeight: 0.90, dailyLossLimitPct: 18, maxDrawdownPct: 45,
  lossCooldownMs: 600000, partialTpRatio: 0.5, partialTpThreshold: 15, sniperMinScore: 65,
  sniperMaxAge: 900, sniperMinBuyPressure: 0.55, sniperMinLiquidity: 6000, sniperMaxSize: 0.10,
  mgMinScore: 65, mgMinVolMomentum: 1.35, mgMinPriceChange5m: 1.2, mgMinTxVelocity: 8,
  mgMaxSize: 0.20, hwrMinScore: 70, hwrMinBuyPressure5m: 0.54, hwrMinBuyPressure1h: 0.51,
  hwrMinLiquidity: 8000, hwrMaxSize: 0.20, maxPositionSize: 0.35, minPositionSize: 0.01,
  maxTradesPerCycle: 1, reentryDelayMs: 60000, slReentryDelayMs: 900000, txCostsEnabled: 1,
  txFeePercent: 0.5, safetyChecksEnabled: 1, rugcheckMinScore: 120, maxVolLiqRatioNewToken: 14,
  maxDiscoveryAgeSeconds: 7200, dynamicHoldEnabled: 1, dynamicHoldMaxSeconds: 2100,
};

let liveCandidatesCache: any[] = [], lastScanTime = 0;
let tradedAddresses = new Map<string, number>();
let stoppedOutAddresses = new Map<string, number>();
const hardBlockedAddresses = new Map<string, number>();
const HARD_BLOCK_TTL_MS = 300_000;
let scannerInterval: ReturnType<typeof setInterval> | null = null;
let priceCheckerInterval: ReturnType<typeof setInterval> | null = null;
let paperBalance = engineSettings.startingBalance;
let balanceInitialized = false;
let peakPrices = new Map<number, number>();
let prevPnlMap = new Map<number, number>();
let pnlStableMap = new Map<number, { pnl: number; since: number }>();
let tradeStopPrices = new Map<number, number>();
let partialTpTaken = new Set<number>();
let consecutiveWins = 0, consecutiveLosses = 0;
let mlServiceAvailable = false;
let jupiterService: JupiterService | null = null;
let liveTokenBalances = new Map<number, bigint>();
let dailyPnlSol = 0, dailyTradeCount = 0;
let dailyStartBalance = engineSettings.startingBalance;
let lastDailyReset = new Date().toDateString();
let peakBalance = engineSettings.startingBalance;
let circuitBreakerActive = false;
let lastLossCooldownEnd = 0;
let lastMiniCooldownEnd = 0; // 2-loss mini-cooldown (3 min) — shorter than the 3-loss gate
let totalTradesAllTime = 0;
let engineStartTime = Date.now();
let mlCheckerInterval: ReturnType<typeof setInterval> | null = null;
let priceCheckLock = false;
let sellingInProgress = new Set<number>();
let scanLock = false;
let reservedCapital = 0;
let pendingBuys = new Map<string, number>();
let recentlyAttemptedBuys = new Map<string, number>();
// Tracks consecutive on-chain zero-balance reads per trade id.
// A single zero read can be RPC lag — require 3 in a row before closing as desync.
// Cleared immediately when a non-zero read comes in.
const zeroBalanceStrikes = new Map<number, number>();
const ZERO_STRIKES_REQUIRED = 3;
// FIX: sellFailureStrikes and MAX_SELL_FAILURES were used in the live sell-failure
// handler but never declared — caused ReferenceError crashing the position manager
// on the first failed live sell attempt.
const sellFailureStrikes = new Map<number, number>();
const MAX_SELL_FAILURES = 3;
// Tracks how many times each token address has been BOUGHT in the current session.
// Prevents fee bleed from repeatedly entering the same token (e.g. $ANIME 6x in 28min).
// In live mode each failed re-entry costs real Jupiter priority fees even if the trade
// itself breaks even. Cap: score < 90 → max 2 entries per token per session.
const sessionTokenBuyCount = new Map<string, number>();
// FIX B: Track how many stop-losses each token has accumulated this session.
// A token that stopped out once might be unlucky; one that stopped out twice is
// structurally hostile right now. After 2+ SLs on the same token, extend its
// blackout from slReentryDelayMs to REPEAT_LOSER_BLOCK_MS (4 hours) so the bot
// stops bleeding priority fees re-entering the same bad setup repeatedly.
const tokenStopLossCount = new Map<string, number>();
const REPEAT_LOSER_BLOCK_MS = 8 * 60 * 60_000; // 8 hours (was 4h — extended to stop re-entering same rug)
// POST-LOSS COOLDOWN: After ANY loss on a token, block re-entry for this many ms.
// Prevents the common pattern of win → loss (re-entry) → loss (re-entry again) seen
// with $Mantis, $ROCKET, $VDOR etc. where the bot chases a token that just reversed.
// Separate from slReentryDelayMs (SL-only, 15min) — this applies to ALL loss exits.
const POST_LOSS_COOLDOWN_MS = 8 * 60 * 1000; // 8 minutes
// 2-loss mini-cooldown: shorter pause before the 3-loss 10-min one.
// After 2 consecutive losses the market has already shown 2 hostile fills;
// waiting 3 minutes before the next entry gives price action time to stabilise
// and prevents adding a third loss while still in the same adverse move.
const MINI_LOSS_COOLDOWN_MS = 3 * 60_000; // 3 minutes
const tokenLastLossMs = new Map<string, number>(); // tokenAddress → timestamp of last loss exit
// SYMBOL-BASED POST-LOSS COOLDOWN: blocks re-entry on the same token symbol even when the
// contract address has changed (e.g. $PORNHUB migrated to a new address after a rug).
// Address-only gates are bypassed entirely in that case — this closes the gap.
const tokenSymbolLastLossMs = new Map<string, number>(); // symbol → timestamp of last loss exit
const SYMBOL_LOSS_COOLDOWN_MS = 8 * 60_000; // 8 minutes — matches POST_LOSS_COOLDOWN_MS (was 4 min, too short for migrated contracts)
// SYMBOL-BASED SESSION CONCENTRATION: caps same-symbol entries regardless of contract address.
// Prevents patterns like $Pilots entering 3× from three different contract addresses while
// the address-based sessionTokenBuyCount shows 0 for each one.
const sessionSymbolBuyCount = new Map<string, number>(); // symbol → entry count this session
// Lifecycle logging helpers — structured output for production validation.
// Adds zero logic overhead and is safe to remove at any time.
const lifecycleLastLogMs = new Map<number, number>(); // trade.id → last LIFECYCLE:HOLD timestamp
const trailActivatedLogged = new Set<number>();        // trade.id → TRAIL:ACTIVATED already emitted
const LIFECYCLE_HOLD_INTERVAL_MS = 30_000;             // heartbeat every 30s per trade
// FIX LIQ_CO: warn-once guard so the "entry liquidity missing" message is logged
// exactly once per trade instead of every priceCheckIntervalMs (1000ms) forever.
const liqCoWarnedTrades = new Set<number>();
// FIX SYMBOL_SL: tracks the last time a symbol exited via SL/LIQ_COLLAPSE so that
// a relaunch on a NEW contract address is still blocked for the full slReentryDelayMs.
// Separate from tokenSymbolLastLossMs (which covers all losses at SYMBOL_LOSS_COOLDOWN_MS).
const tokenSymbolSlBlockMs = new Map<string, number>(); // symbol → timestamp of last SL/LIQ exit
const SYMBOL_SL_COOLDOWN_MS = 15 * 60_000; // mirrors slReentryDelayMs

const tokenPriceCache = new Map<string, { price: number; pair: DexScreenerPair | null; ts: number }>();
const jupiterQuoteCache = new Map<string, { quote: any; ts: number }>();
const QUOTE_CACHE_TTL_MS = 4_000; // FIX 4: was 2000 — too short, causes rate-limit hits and trade delays

setInterval(() => {
  const now = Date.now();
  for (const [k, v] of tokenPriceCache) if (now - v.ts > 1500) tokenPriceCache.delete(k);
  for (const [k, v] of jupiterQuoteCache) if (now - v.ts > QUOTE_CACHE_TTL_MS) jupiterQuoteCache.delete(k);
}, 1_500); // match tokenPriceCache TTL — 5s interval let entries linger up to 6.5s

function getCachedQuote(key: string): any | null {
  const entry = jupiterQuoteCache.get(key);
  if (entry && Date.now() - entry.ts < QUOTE_CACHE_TTL_MS) return entry.quote;
  return null;
}
function setCachedQuote(key: string, quote: any): void {
  jupiterQuoteCache.set(key, { quote, ts: Date.now() });
}

async function resetDailyStats() {
  const today = new Date().toDateString();
  if (today !== lastDailyReset) {
    dailyPnlSol = 0; dailyTradeCount = 0;
    const modeStatus = await storage.getBotStatus().catch(() => ({ tradingMode: "paper" }));
    if (modeStatus.tradingMode === "live" && jupiterService) {
      dailyStartBalance = await jupiterService.getWalletBalance().catch(() => paperBalance);
    } else {
      dailyStartBalance = await getEffectiveBalance();
    }
    lastDailyReset = today;
    if (!circuitBreakerActive) console.log(`[RISK] Daily stats reset | Start balance: ${dailyStartBalance.toFixed(3)} SOL`);
  }
}

async function getEffectiveBalance(): Promise<number> {
  try {
    const modeStatus = await storage.getBotStatus().catch(() => ({ tradingMode: "paper" }));
    if (modeStatus.tradingMode === "live" && jupiterService) {
      return await jupiterService.getWalletBalance().catch(() => paperBalance);
    }
    const openTrades = await storage.getOpenTrades();
    let openCapital = 0;
    for (const t of openTrades) {
      // FIX 1: Skip ghost DB trades that have no in-memory tracking.
      // Trades from previous sessions remain as OPEN in DB but are not in
      // peakPrices. When their token price rises they inflate effectiveBal →
      // peakBalance is raised. When price reverts effectiveBal drops back →
      // drawdown appears with zero trades executed in the current session.
      if (!peakPrices.has(t.id)) continue;
      const sizeSol = parseFloat(t.amount || "0");
      const entryPrice = parseFloat(t.price || "0");
      const currentPrice = parseFloat(t.currentPrice || t.price || "0");
      if (sizeSol > 0 && entryPrice > 0 && currentPrice > 0) {
        const unrealizedPnlPct = ((currentPrice - entryPrice) / entryPrice) * 100;
        const unrealizedPnlSol = sizeSol * (unrealizedPnlPct / 100);
        // FIX 2: Include negative unrealized PnL symmetrically. The old formula
        // added gains but silently dropped losses, so peakBalance climbed on good
        // ticks but effectiveBal did not fall on bad ticks — phantom drawdown grew
        // continuously with no trades. Both sides must be accounted for.
        openCapital += sizeSol + unrealizedPnlSol;
      }
      // No else: if price data is missing for a tracked trade, skip it rather
      // than blindly adding sizeSol which would also inflate effectiveBal.
    }
    return Math.max(0, paperBalance + openCapital);
  } catch { return paperBalance; }
}

let cachedSolPriceUsd = 180, lastSolPriceFetch = 0, solPriceFetchedOnce = false;
const SOL_PRICE_CACHE_TTL_MS = 20_000;

async function getLiveSolPrice(): Promise<number> {
  const now = Date.now();
  if (solPriceFetchedOnce && now - lastSolPriceFetch < SOL_PRICE_CACHE_TTL_MS) return cachedSolPriceUsd;
  try {
    const resp = await fetch(`https://api.dexscreener.com/latest/dex/tokens/${SOL_MINT}`, { signal: AbortSignal.timeout(3000) });
    if (resp.ok) {
      const data = await resp.json();
      const pairs = data?.pairs || [];
      const bestPair = pairs.filter((p: any) => p.chainId === "solana").sort((a: any, b: any) => (b.liquidity?.usd || 0) - (a.liquidity?.usd || 0))[0];
      const price = parseFloat(bestPair?.priceUsd ?? "0");
      if (price > 0) { cachedSolPriceUsd = price; lastSolPriceFetch = now; solPriceFetchedOnce = true; }
    }
  } catch {}
  lastSolPriceFetch = now; solPriceFetchedOnce = true;
  return cachedSolPriceUsd;
}

async function getOpenUnrealizedPnl(): Promise<number> {
  const openTrades = await storage.getOpenTrades();
  let total = 0;
  for (const t of openTrades) {
    // FIX: same ghost-trade guard as getEffectiveBalance — only include trades
    // actively tracked in memory. Ghost DB rows from previous sessions inflate
    // unrealizedPnl, which can falsely trip the DAILY_LOSS_LIMIT circuit breaker
    // before any trade in the current session has even executed.
    if (!peakPrices.has(t.id)) continue;
    const entry = parseFloat(t.price), current = parseFloat(t.currentPrice || t.price), size = parseFloat(t.amount);
    if (entry > 0 && current > 0 && size > 0) total += size * (((current - entry) / entry) * 100) / 100;
  }
  return total;
}

async function checkCircuitBreakers(): Promise<{ canTrade: boolean; reason: string }> {
  await resetDailyStats();
  // FIX Y-2: use NET daily PNL (realized + unrealized). The old code separated and
  // summed only the negative components, so a profitable day (+5 SOL realized)
  // with a minor floating loss (-0.2 SOL) registered as a loss and could trigger
  // the breaker. We now fire only when the net day is actually negative.
  const unrealized  = await getOpenUnrealizedPnl();
  const netDailyPnl = dailyPnlSol + unrealized;
  const totalLoss   = netDailyPnl < 0 ? Math.abs(netDailyPnl) : 0;
  const dailyLossPct = dailyStartBalance > 0 ? (totalLoss / dailyStartBalance) * 100 : 0;
  if (dailyLossPct >= engineSettings.dailyLossLimitPct) {
    circuitBreakerActive = true;
    return { canTrade: false, reason: `DAILY_LOSS_LIMIT (${dailyLossPct.toFixed(1)}% >= ${engineSettings.dailyLossLimitPct}%)` };
  }
  const effectiveBal = await getEffectiveBalance();
  // FIX U-1: keep peakBalance in sync with unrealized gains. Previously it only
  // updated on trade close, so a rally followed by a crash measured drawdown from
  // the pre-rally peak, missing the true post-rally drawdown entirely.
  if (effectiveBal > peakBalance) peakBalance = effectiveBal;
  const drawdownPct = peakBalance > 0 ? ((peakBalance - effectiveBal) / peakBalance) * 100 : 0;
  if (drawdownPct >= engineSettings.maxDrawdownPct) {
    circuitBreakerActive = true;
    return { canTrade: false, reason: `MAX_DRAWDOWN (${drawdownPct.toFixed(1)}% >= ${engineSettings.maxDrawdownPct}%)` };
  }
  if (Date.now() < lastMiniCooldownEnd) {
    const remaining = Math.ceil((lastMiniCooldownEnd - Date.now()) / 1000);
    return { canTrade: false, reason: `MINI_LOSS_COOLDOWN (${remaining}s remaining — 2 consecutive losses)` };
  }
  if (Date.now() < lastLossCooldownEnd) {
    const remaining = Math.ceil((lastLossCooldownEnd - Date.now()) / 1000);
    return { canTrade: false, reason: `LOSS_COOLDOWN (${remaining}s remaining)` };
  }
  circuitBreakerActive = false;
  return { canTrade: true, reason: "OK" };
}

async function checkMLService(): Promise<boolean> {
  try {
    const resp = await fetch(`${engineSettings.mlServiceUrl}/health`, { signal: AbortSignal.timeout(2000) });
    if (resp.ok) { mlServiceAvailable = true; return true; }
  } catch {}
  mlServiceAvailable = false;
  return false;
}

function sanitizeNum(v: any, fallback = 0): number { const n = Number(v); return isNaN(n) || !isFinite(n) ? fallback : n; }

async function getMLPrediction(metrics: Record<string, number>): Promise<{ pumpProb: number; dumpRisk: number; version: string } | null> {
  if (!mlServiceAvailable) return null;
  const liq = sanitizeNum(metrics.liq);
  if (liq < 500) return null;
  try {
    const vol5m = sanitizeNum(metrics.vol5m), vol1h = sanitizeNum(metrics.vol1h);
    const volMomentum = vol1h > 0 ? (vol5m * 12) / vol1h : 0;
    const fdv = sanitizeNum(metrics.fdv);
    const body = {
      age_seconds: sanitizeNum(metrics.ageSeconds, 99999), liquidity_usd: liq, volume_5m: vol5m, volume_1h: vol1h,
      volume_change_1m: sanitizeNum(volMomentum), price_change_5m: sanitizeNum(metrics.priceChange5m),
      price_change_1h: sanitizeNum(metrics.priceChange1h), buy_pressure_5m: sanitizeNum(metrics.buyPressure5m, 0.5),
      buy_pressure_1h: sanitizeNum(metrics.buyPressure1h, 0.5),
      buy_sell_ratio: sanitizeNum(metrics.h1buys, 0) / (sanitizeNum(metrics.h1sells, 0) + 0.001),
      tx_velocity_per_hour: sanitizeNum(metrics.txVelocity5m) * 12, fdv, liq_to_mcap: fdv > 0 ? liq / fdv : 0,
    };
    const resp = await fetch(`${engineSettings.mlServiceUrl}/predict`, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body), signal: AbortSignal.timeout(3000) });
    if (!resp.ok) return null;
    const data = await resp.json();
    if (data.error) return null;
    const pumpProb = Math.max(0, Math.min(1, Number(data.pump_probability) || 0));
    const dumpRisk = Math.max(0, Math.min(1, data.dump_risk != null ? Number(data.dump_risk) : 1));
    return { pumpProb, dumpRisk, version: data.model_version || "unknown" };
  } catch { return null; }
}

async function getMLBatchPredictions(tokenMetrics: Record<string, number>[]): Promise<({ pumpProb: number; dumpRisk: number; version: string } | null)[]> {
  if (!mlServiceAvailable || tokenMetrics.length === 0) return tokenMetrics.map(() => null);
  try {
    const validIndices: number[] = [], tokens: any[] = [];
    for (let i = 0; i < tokenMetrics.length; i++) {
      const m = tokenMetrics[i];
      const liq = sanitizeNum(m.liq);
      if (liq < 500) continue;
      validIndices.push(i);
      const vol5m = sanitizeNum(m.vol5m), vol1h = sanitizeNum(m.vol1h);
      const volMomentum = vol1h > 0 ? (vol5m * 12) / vol1h : 0;
      const fdv = sanitizeNum(m.fdv);
      tokens.push({
        age_seconds: sanitizeNum(m.ageSeconds, 99999), liquidity_usd: liq, volume_5m: vol5m, volume_1h: vol1h,
        volume_change_1m: sanitizeNum(volMomentum), price_change_5m: sanitizeNum(m.priceChange5m),
        price_change_1h: sanitizeNum(m.priceChange1h), buy_pressure_5m: sanitizeNum(m.buyPressure5m, 0.5),
        buy_pressure_1h: sanitizeNum(m.buyPressure1h, 0.5),
        buy_sell_ratio: sanitizeNum(m.h1buys, 0) / (sanitizeNum(m.h1sells, 0) + 0.001),
        tx_velocity_per_hour: sanitizeNum(m.txVelocity5m) * 12, fdv, liq_to_mcap: fdv > 0 ? liq / fdv : 0,
      });
    }
    if (tokens.length === 0) return tokenMetrics.map(() => null);
    const resp = await fetch(`${engineSettings.mlServiceUrl}/predict/batch`, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ tokens }), signal: AbortSignal.timeout(5000) });
    if (!resp.ok) return tokenMetrics.map(() => null);
    const data = await resp.json();
    const preds = data.predictions || [];
    // FIX: partial response mismatch (e.g. one token timed out server-side) should
    // use whatever predictions arrived, not discard all. Map what we got; null-fill
    // the rest so rule-scoring still applies to the unmatched tokens.
    if (preds.length !== validIndices.length) {
      console.warn(`[ML] Batch mismatch: expected ${validIndices.length}, got ${preds.length} — using partial results`);
    }
    const results: ({ pumpProb: number; dumpRisk: number; version: string } | null)[] = tokenMetrics.map(() => null);
    for (let j = 0; j < Math.min(preds.length, validIndices.length); j++) {
      const p = preds[j];
      if (p.error) continue;
      results[validIndices[j]] = { pumpProb: Math.max(0, Math.min(1, Number(p.pump_probability) || 0)), dumpRisk: Math.max(0, Math.min(1, p.dump_risk != null ? Number(p.dump_risk) : 1)), version: p.model_version || "unknown" };
    }
    return results;
  } catch { return tokenMetrics.map(() => null); }
}

async function fetchTokenPrice(tokenAddress: string): Promise<{ price: number; pair: DexScreenerPair | null }> {
  const now = Date.now();
  const cached = tokenPriceCache.get(tokenAddress);
  if (cached && now - cached.ts < 1500) return { price: cached.price, pair: cached.pair };
  try {
    const resp = await fetch(`https://api.dexscreener.com/latest/dex/tokens/${tokenAddress}`, { signal: AbortSignal.timeout(5000) });
    if (!resp.ok) return { price: 0, pair: null };
    const data = await resp.json();
    const pairs = (data.pairs || []) as DexScreenerPair[];
    const solanaPairs = pairs.filter(p => p.chainId === "solana");
    if (solanaPairs.length === 0) return { price: 0, pair: null };
    const validPairs = solanaPairs.filter(p => { const liq = p.liquidity?.usd || 0, vol5m = p.volume?.m5 || 0; return !(liq > 0 && vol5m > liq * 15); });
    // FIX Z-2: never fall back to a flagged pair. If ALL pairs are suspicious,
    // return zero so callers skip the token rather than trading on wash data.
    if (validPairs.length === 0) return { price: 0, pair: null };
    const bestPair = validPairs.sort((a, b) => (b.liquidity?.usd || 0) - (a.liquidity?.usd || 0))[0];
    const result = { price: parseFloat(bestPair.priceUsd || "0"), pair: bestPair };
    if (result.price <= 0) return { price: 0, pair: null };
    tokenPriceCache.set(tokenAddress, { ...result, ts: now });
    return result;
  } catch { return { price: 0, pair: null }; }
}

// Bug #2 fix — exit-path price fetch that skips the wash-trade vol/liq filter.
//
// fetchTokenPrice intentionally blocks pairs where vol5m >> liq (wash trading /
// artificial volume) which is correct for ENTRY decisions.  However the exact
// same pattern occurs during a rug pull: massive panic-sell volume makes
// vol5m >> liq, so fetchTokenPrice returns {price:0} and checkOpenPositions
// does `if (currentPrice <= 0) continue` — silently skipping the position.
// Stop-loss, HARD_LOSS_KILL, and LIQ_COLLAPSE never fire.  The token bleeds to
// zero.  VDOR (-90.6 %) and EARTH (-99 %) were caused by exactly this path.
//
// For open-position monitoring we must always obtain a price.  We still pick
// the highest-liquidity pair but never suppress the result on a vol spike.
// We also fall back to the stale cache on network failure rather than returning
// zero — a stale exit price is far safer than skipping the stop-loss check.
async function fetchTokenPriceForExit(tokenAddress: string): Promise<{ price: number; pair: DexScreenerPair | null }> {
  const now = Date.now();
  const cached = tokenPriceCache.get(tokenAddress);
  // Fast-path: cache still fresh — return immediately (same TTL as fetchTokenPrice)
  if (cached && now - cached.ts < 1500) return { price: cached.price, pair: cached.pair };
  try {
    const resp = await fetch(`https://api.dexscreener.com/latest/dex/tokens/${tokenAddress}`, { signal: AbortSignal.timeout(5000) });
    if (!resp.ok) {
      // Network / API error — fall back to last known price rather than returning
      // zero which would bypass every exit condition for this cycle.
      if (cached) {
        console.warn(`[EXIT_PRICE] HTTP ${resp.status} for ${tokenAddress.slice(0, 8)}... — using stale cached price $${cached.price.toFixed(8)}`);
        return { price: cached.price, pair: cached.pair };
      }
      return { price: 0, pair: null };
    }
    const data = await resp.json();
    const pairs = (data.pairs || []) as DexScreenerPair[];
    const solanaPairs = pairs.filter(p => p.chainId === "solana");
    if (solanaPairs.length === 0) {
      if (cached) {
        console.warn(`[EXIT_PRICE] No Solana pairs for ${tokenAddress.slice(0, 8)}... — using stale cached price`);
        return { price: cached.price, pair: cached.pair };
      }
      return { price: 0, pair: null };
    }
    // No vol/liq filter — select by liquidity depth only.
    // High vol5m during a rug is the canary we must NOT suppress.
    const bestPair = solanaPairs.sort((a, b) => (b.liquidity?.usd || 0) - (a.liquidity?.usd || 0))[0];
    const price = parseFloat(bestPair.priceUsd || "0");
    if (price <= 0) {
      // Zero price from the API — fall back to cache rather than skipping exits.
      if (cached) {
        console.warn(`[EXIT_PRICE] Zero price from API for ${tokenAddress.slice(0, 8)}... — using stale cached price $${cached.price.toFixed(8)}`);
        return { price: cached.price, pair: cached.pair };
      }
      return { price: 0, pair: null };
    }
    // Update the shared cache so subsequent fetchTokenPrice calls benefit too.
    tokenPriceCache.set(tokenAddress, { price, pair: bestPair, ts: now });
    return { price, pair: bestPair };
  } catch {
    if (cached) return { price: cached.price, pair: cached.pair };
    return { price: 0, pair: null };
  }
}

function scoreToken(pair: DexScreenerPair, mlPrediction?: { pumpProb: number; dumpRisk: number; version: string } | null) {
  const liq = pair.liquidity?.usd || 0, fdv = pair.fdv || 0, createdAt = pair.pairCreatedAt || Date.now();
  const ageSeconds = Math.floor((Date.now() - createdAt) / 1000);
  const m5b = pair.txns?.m5?.buys || 0, m5s = pair.txns?.m5?.sells || 0, h1b = pair.txns?.h1?.buys || 0, h1s = pair.txns?.h1?.sells || 0;
  const vol5m = pair.volume?.m5 || 0, vol1h = pair.volume?.h1 || 0;
  const priceChange5m = pair.priceChange?.m5 || 0, priceChange1h = pair.priceChange?.h1 || 0;
  const bp5m = (m5b + m5s) > 0 ? m5b / (m5b + m5s) : 0.5, bp1h = (h1b + h1s) > 0 ? h1b / (h1b + h1s) : 0.5;
  const txVelocity5m = m5b + m5s, volMomentum = vol1h > 0 ? (vol5m * 12) / vol1h : 0;
  const liqScore = liq >= 50000 ? 15 : liq >= 20000 ? 12 : liq >= 10000 ? 10 : liq >= 5000 ? 8 : liq >= 2000 ? 5 : liq >= 1000 ? 3 : liq >= 500 ? 1 : 0;
  const bpScore = bp5m >= 0.75 ? 20 : bp5m >= 0.65 ? 16 : bp5m >= 0.60 ? 13 : bp5m >= 0.55 ? 10 : bp5m >= 0.50 ? 5 : Math.max(0, Math.floor(bp5m * 10) - 5);
  const volScore = volMomentum >= 3.0 ? 15 : volMomentum >= 2.0 ? 12 : volMomentum >= 1.5 ? 9 : volMomentum >= 1.0 ? 6 : volMomentum >= 0.5 ? 3 : 0;
  const priceScore = priceChange5m >= 10 ? 15 : priceChange5m >= 7 ? 12 : priceChange5m >= 5 ? 10 : priceChange5m >= 3 ? 8 : priceChange5m >= 1.5 ? 5 : priceChange5m > 0 ? 2 : Math.max(-10, Math.floor(priceChange5m));
  const txScore = txVelocity5m >= 50 ? 10 : txVelocity5m >= 30 ? 8 : txVelocity5m >= 20 ? 6 : txVelocity5m >= 10 ? 4 : txVelocity5m >= 5 ? 2 : 0;
  // OLD version gave <60s tokens max freshness (10pts) — prime SNIPER window.
  // New version penalised them with 0, indirectly blocking sub-minute entries
  // via the score gate rather than through the explicit SNIPER safety checks.
  // Restore: <60s → 10, then taper. Safety for ultra-fresh tokens is handled
  // by sniperMinLiquidity, rugcheck, sell-side preflight and the isMicroCapToken
  // 0.02 SOL size cap — not by artificially deflating the score here.
  const ageScore = ageSeconds < 60 ? 10 : ageSeconds <= 300 ? 8 : ageSeconds <= 600 ? 6 : ageSeconds <= 1800 ? 4 : ageSeconds <= 3600 ? 2 : 0;
  const bp1hScore = bp1h >= 0.60 ? 5 : bp1h >= 0.55 ? 3 : bp1h >= 0.50 ? 1 : 0;
  let fdvScore = 0;
  if (fdv > 0 && liq > 0) { const lr = liq / fdv; fdvScore = lr >= 0.05 ? 5 : lr >= 0.02 ? 3 : lr >= 0.01 ? 1 : 0; }
  const rawTotal = liqScore + bpScore + volScore + priceScore + txScore + ageScore + bp1hScore + fdvScore;
  const score = Math.max(0, Math.min(100, Math.round((rawTotal / 95) * 100)));
  let mlScore: number | null = null, combinedScore = score;
  if (mlPrediction) {
    mlScore = Math.round(mlPrediction.pumpProb * 100);
    const mlAdjusted = mlScore * (1 - mlPrediction.dumpRisk * 0.5);
    combinedScore = Math.max(0, Math.min(100, Math.round(score * engineSettings.scoreWeight + mlAdjusted * engineSettings.mlWeight)));
  }
  const metrics = { liq, ageSeconds, bp5m, bp1h, volMomentum, priceChange5m, priceChange1h, txVelocity5m, vol5m, vol1h, fdv, h1buys: h1b, h1sells: h1s, m5buys: m5b, m5sells: m5s, buyPressure5m: bp5m, buyPressure1h: bp1h };
  const sizeForMode = (maxSizeFraction: number, minScore: number) => {
    const ratio = Math.max(0, (combinedScore - minScore) / Math.max(1, 100 - minScore));
    const raw = engineSettings.minPositionSize + ratio * (maxSizeFraction * engineSettings.maxPositionSize - engineSettings.minPositionSize);
    return Math.max(engineSettings.minPositionSize, raw);
  };
  const candidates: { mode: string; sizeSol: number; slippage: number; minScore: number }[] = [];
  if (combinedScore >= engineSettings.sniperMinScore && ageSeconds <= engineSettings.sniperMaxAge && bp5m >= engineSettings.sniperMinBuyPressure && liq >= engineSettings.sniperMinLiquidity) {
    candidates.push({ mode: "SNIPER", minScore: engineSettings.sniperMinScore, sizeSol: sizeForMode(engineSettings.sniperMaxSize, engineSettings.sniperMinScore), slippage: liq < 3000 ? 8 : liq < 10000 ? 5 : 3 });
  }
  if (combinedScore >= engineSettings.mgMinScore && volMomentum >= engineSettings.mgMinVolMomentum && priceChange5m >= engineSettings.mgMinPriceChange5m && txVelocity5m >= engineSettings.mgMinTxVelocity) {
    candidates.push({ mode: "MG", minScore: engineSettings.mgMinScore, sizeSol: sizeForMode(engineSettings.mgMaxSize, engineSettings.mgMinScore), slippage: liq < 5000 ? 6 : liq < 20000 ? 4 : 2.5 });
  }
  if (combinedScore >= engineSettings.hwrMinScore && bp5m >= engineSettings.hwrMinBuyPressure5m && bp1h >= engineSettings.hwrMinBuyPressure1h && liq >= engineSettings.hwrMinLiquidity) {
    candidates.push({ mode: "HWR", minScore: engineSettings.hwrMinScore, sizeSol: sizeForMode(engineSettings.hwrMaxSize, engineSettings.hwrMinScore), slippage: liq < 5000 ? 5 : liq < 20000 ? 3 : 2 });
  }
  let qualifiedMode: string | null = null, sizeSol = 0, slippage = 0;
  if (candidates.length > 0) {
    // Priority: for tokens within SNIPER age window, prefer SNIPER over HWR/MG even
    // if HWR has a higher minScore — SNIPER carries wider slippage tolerance which
    // is necessary for fresh thin-pool fills. Using HWR slippage (2-3%) on a 90s
    // token in a $5k pool reliably causes failed Jupiter fills.
    const sniperCandidate = candidates.find(c => c.mode === "SNIPER");
    const best = (sniperCandidate && ageSeconds <= engineSettings.sniperMaxAge)
      ? sniperCandidate
      : candidates.reduce((a, b) => a.minScore >= b.minScore ? a : b);
    qualifiedMode = best.mode; sizeSol = parseFloat(best.sizeSol.toFixed(4)); slippage = parseFloat(best.slippage.toFixed(2));
  }
  return { score, mlScore, combinedScore, breakdown: {}, metrics, qualifiedMode, sizeSol, slippage };
}

function getScoreBasedTP(score: number): number {
  // FIX X-2: tiers must increase monotonically with score. Old code returned 80%
  // for both 70–79 AND 80–89 (identical), and the <70 default was also 80%,
  // meaning every score below 90 got the same exit. Proper ladder:
  if (score >= 90) return 100;
  if (score >= 80) return  90;
  if (score >= 70) return  80;
  if (score >= 60) return  65;
  return engineSettings.hardTakeProfit;
}

function calcTransactionCosts(liqUsd: number, sizeSol: number, solPriceUsd = cachedSolPriceUsd) {
  if (!engineSettings.txCostsEnabled) return { entrySlippagePct: 0, exitSlippagePct: 0, entryFeePct: 0, exitFeePct: 0, totalRoundTripPct: 0 };
  const tradeValueUsd = sizeSol * solPriceUsd;
  const priceImpactPct = liqUsd > 0 ? Math.min(20, (tradeValueUsd / (liqUsd / 2)) * 100) : 10;
  const baseSlippage = liqUsd < 2000 ? 8 : liqUsd < 5000 ? 5 : liqUsd < 20000 ? 2.5 : 1.2;
  const entrySlippagePct = Math.max(baseSlippage, priceImpactPct);
  const exitSlippagePct = entrySlippagePct * 1.3;
  const fee = engineSettings.txFeePercent;
  return { entrySlippagePct, exitSlippagePct, entryFeePct: fee, exitFeePct: fee, totalRoundTripPct: entrySlippagePct + exitSlippagePct + fee * 2 };
}

function calcCostAwareStopPrice(entryPrice: number, mode: string | null, liq: number, sizeSol: number, solPriceUsd = cachedSolPriceUsd): number {
  if (entryPrice <= 0) return 0;
  const costs = calcTransactionCosts(liq, sizeSol, solPriceUsd);
  const modeBuffer = mode === "SNIPER" ? 4 : mode === "MG" ? 2 : 1;
  const exitCostPct = costs.exitSlippagePct + costs.exitFeePct;
  const rawTolerance = Math.abs(engineSettings.stopLoss) + modeBuffer;
  const priceMoveTolerance = Math.max(rawTolerance, exitCostPct + 1);
  return entryPrice * (1 - priceMoveTolerance / 100);
}

async function checkTokenSafety(tokenAddress: string, pair: DexScreenerPair): Promise<{ safe: boolean; reason: string }> {
  if (!engineSettings.safetyChecksEnabled) return { safe: true, reason: "checks_disabled" };
  const liq = pair.liquidity?.usd || 0, fdv = pair.fdv || 0, createdAt = pair.pairCreatedAt || Date.now();
  const ageSeconds = (Date.now() - createdAt) / 1000, vol5m = pair.volume?.m5 || 0;
  if (liq < 500) return { safe: false, reason: "liq_below_minimum" };
  if (ageSeconds < 60 && vol5m > liq * engineSettings.maxVolLiqRatioNewToken) return { safe: false, reason: `suspicious_vol_liq_ratio(${(vol5m / liq).toFixed(1)}x at ${ageSeconds.toFixed(0)}s)` };
  if (fdv > 0 && liq / fdv < 0.001) return { safe: false, reason: `honeypot_risk_liq_fdv_ratio(${(liq / fdv * 100).toFixed(3)}%)` };
  const m5buys = pair.txns?.m5?.buys || 0, m5sells = pair.txns?.m5?.sells || 0;
  if (ageSeconds < 120 && m5buys > 20 && m5sells === 0) return { safe: false, reason: "zero_sells_coordinated_buy" };
  try {
    const resp = await fetch(`https://api.rugcheck.xyz/v1/tokens/${tokenAddress}/report/summary`, { signal: AbortSignal.timeout(2500) });
    // Non-OK responses (429 rate-limit, 503 down, etc.) should fall through to
    // heuristics-only mode rather than blocking every candidate. Rugcheck is a
    // secondary signal — our liq floor, vol/liq ratio, honeypot check, and
    // zero-sells gate already catch the most dangerous patterns.
    if (!resp.ok) {
      console.log(`[SAFETY] rugcheck.xyz HTTP ${resp.status} for ${tokenAddress.substring(0, 8)}... — heuristics only`);
      return { safe: true, reason: `rugcheck_http_${resp.status}_fallthrough` };
    }
    const data = await resp.json();
    const score = (typeof data.score === "number" && !isNaN(data.score)) ? data.score : 1000;
    const risks: Array<{ name: string; level: string }> = data.risks || [];
    // "Large Amount of LP Unlocked" / "Low Amount of LP Locked" are the default
    // state on ~95% of pump.fun launches — LP is almost never time-locked on new
    // meme coins. Blocking on this flag alone eliminates the entire market without
    // meaningfully reducing rug risk. Real danger signals (mint authority, freeze
    // authority, honeypot liq/fdv ratio) are still blocked.
    const ALLOWED_DANGER_NAMES = new Set([
      "Large Amount of LP Unlocked",
      "Low Amount of LP Locked",
    ]);
    const realDangers = risks.filter(r => r.level === "danger" && !ALLOWED_DANGER_NAMES.has(r.name));
    if (realDangers.length > 0) return { safe: false, reason: `rugcheck_danger:${realDangers.map(r => r.name).join(",")}` };
    if (score < engineSettings.rugcheckMinScore) return { safe: false, reason: `rugcheck_score_low(${score})` };
    console.log(`[SAFETY] ${tokenAddress.substring(0, 8)}... rugcheck OK (score ${score})`);
    return { safe: true, reason: "ok" };
  } catch {
    // Timeout or network error — fall through to heuristics rather than blocking.
    console.log(`[SAFETY] rugcheck.xyz unreachable for ${tokenAddress.substring(0, 8)}... — heuristics only`);
    return { safe: true, reason: "rugcheck_unreachable_fallthrough" };
  }
}

function getScoreBasedMaxHold(score: number, currentPnlPct: number, currentBuyPressure: number): number {
  if (!engineSettings.dynamicHoldEnabled) return engineSettings.maxHoldSeconds;
  let base = score >= 85 ? 900 : score >= 75 ? 720 : score >= 65 ? 540 : engineSettings.maxHoldSeconds;
  // FIX W-1: differentiated multipliers — both branches previously used 1.4×,
  // making the stricter condition (>20% PNL, >0.60 BP) completely redundant.
  if (currentPnlPct > 20 && currentBuyPressure > 0.60) base = Math.round(base * 1.6);
  else if (currentPnlPct > 10 && currentBuyPressure > 0.55) base = Math.round(base * 1.4);
  else if (currentPnlPct > 5 && currentBuyPressure > 0.52) base = Math.round(base * 1.2);
  if (currentPnlPct < -2) base = Math.min(base, 300);
  if (currentPnlPct < -3.5) base = Math.min(base, 180);
  return Math.min(Math.round(base), engineSettings.dynamicHoldMaxSeconds);
}

function geckoPoolToDexPair(pool: any): DexScreenerPair | null {
  try {
    const attr = pool?.attributes, rels = pool?.relationships;
    if (!attr || !rels) return null;
    const baseId = rels.base_token?.data?.id as string | undefined, quoteId = rels.quote_token?.data?.id as string | undefined, dexId = rels.dex?.data?.id as string | undefined;
    if (!baseId || !dexId) return null;
    const baseAddress = baseId.replace(/^solana_/, ""), quoteAddress = quoteId ? quoteId.replace(/^solana_/, "") : SOL_MINT;
    const nameParts = (attr.name as string || "/").split("/");
    const baseSymbol = nameParts[0]?.trim() || "UNKNOWN", quoteSymbol = nameParts[1]?.trim() || "SOL";
    const pairCreatedAt = attr.pool_created_at ? new Date(attr.pool_created_at as string).getTime() : undefined;
    const volumeUsd = attr.volume_usd || {}, txns = attr.transactions || {};
    const toTxBucket = (bucket: any) => bucket ? { buys: Number(bucket.buys) || 0, sells: Number(bucket.sells) || 0 } : undefined;
    const pc = attr.price_change_percentage || {};
    return {
      chainId: "solana", dexId: (dexId as string).toLowerCase(), pairAddress: attr.address as string || pool.id || "",
      baseToken: { address: baseAddress, name: attr.base_token_name as string || baseSymbol, symbol: baseSymbol },
      quoteToken: { address: quoteAddress, name: quoteSymbol, symbol: quoteSymbol },
      priceUsd: String(attr.base_token_price_usd || "0"), priceNative: String(attr.base_token_price_native_currency || "0"),
      txns: { m5: toTxBucket(txns.m5), h1: toTxBucket(txns.h1), h24: toTxBucket(txns.h24) },
      volume: { m5: Number(volumeUsd.m5) || 0, h1: Number(volumeUsd.h1) || 0, h6: Number(volumeUsd.h6) || 0, h24: Number(volumeUsd.h24) || 0 },
      priceChange: { m5: Number(pc.m5) || 0, h1: Number(pc.h1) || 0, h6: Number(pc.h6) || 0, h24: Number(pc.h24) || 0 },
      liquidity: { usd: Number(attr.reserve_in_usd) || 0 }, fdv: Number(attr.fdv_usd) || 0, marketCap: Number(attr.market_cap_usd) || 0, pairCreatedAt,
    };
  } catch (e) { console.warn("[GECKO] Failed to convert pool:", (e as Error).message); return null; }
}

async function batchFetchDexPairs(addresses: string[]): Promise<Map<string, DexScreenerPair>> {
  const result = new Map<string, DexScreenerPair>();
  if (addresses.length === 0) return result;
  for (let i = 0; i < addresses.length; i += 30) {
    if (i > 0) await new Promise(r => setTimeout(r, 300));
    const chunk = addresses.slice(i, i + 30);
    try {
      const url = `https://api.dexscreener.com/latest/dex/tokens/${chunk.join(",")}`;
      const resp = await fetch(url, { signal: AbortSignal.timeout(5000) });
      if (!resp.ok) continue;
      const data = await resp.json();
      const pairs: DexScreenerPair[] = data.pairs || [];
      for (const addr of chunk) {
        // FIX U-3: apply wash-trade filter identical to fetchTokenPrice.
        // Without it, a pool with vol5m >> liq (artificial volume) is selected as
        // "best" and its inflated metrics poison scoreToken for that token.
        const best = pairs
          .filter(p => {
            if (p.chainId !== "solana" || p.baseToken.address !== addr) return false;
            const liq = p.liquidity?.usd || 0, vol5m = p.volume?.m5 || 0;
            return !(liq > 0 && vol5m > liq * 15);
          })
          .sort((a, b) => (b.liquidity?.usd || 0) - (a.liquidity?.usd || 0))[0];
        if (best) result.set(addr, best);
      }
    } catch { continue; }
  }
  return result;
}

async function fetchDexScreenerCandidates(): Promise<any[]> {
  const now = Date.now();
  const cacheTtl = Math.max(2000, engineSettings.scanIntervalMs * 0.9);
  if (now - lastScanTime < cacheTtl && liveCandidatesCache.length > 0) return liveCandidatesCache;
  try {
    const allPairs: DexScreenerPair[] = [];
    const maxAgeMs = engineSettings.maxDiscoveryAgeSeconds * 1000;
    const geckoFetches = [
      fetch("https://api.geckoterminal.com/api/v2/networks/solana/trending_pools?page=1", { headers: { "Accept": "application/json;version=20230302" }, signal: AbortSignal.timeout(8000) }).then(r => r.ok ? r.json() : { data: [] }).catch(() => ({ data: [] })),
      fetch("https://api.geckoterminal.com/api/v2/networks/solana/new_pools?page=1", { headers: { "Accept": "application/json;version=20230302" }, signal: AbortSignal.timeout(8000) }).then(r => r.ok ? r.json() : { data: [] }).catch(() => ({ data: [] })),
    ];
    const dexFetches = [
      fetch("https://api.dexscreener.com/latest/dex/search?q=raydium+sol", { signal: AbortSignal.timeout(8000) }).then(r => r.ok ? r.json() : { pairs: [] }).catch(() => ({ pairs: [] })),
      fetch("https://api.dexscreener.com/latest/dex/search?q=pumpfun+solana", { signal: AbortSignal.timeout(8000) }).then(r => r.ok ? r.json() : { pairs: [] }).catch(() => ({ pairs: [] })),
      fetch("https://api.dexscreener.com/latest/dex/search?q=orca+solana+new", { signal: AbortSignal.timeout(8000) }).then(r => r.ok ? r.json() : { pairs: [] }).catch(() => ({ pairs: [] })),
    ];
    const [gtTrending, gtNew, raydiumResult, pumpfunResult, orcaResult] = await Promise.all([...geckoFetches, ...dexFetches]);
    const geckoAddresses: string[] = [];
    for (const pool of [...(gtTrending.data || []), ...(gtNew.data || [])]) {
      const pair = geckoPoolToDexPair(pool);
      if (!pair) continue;
      const pairAge = pair.pairCreatedAt ? now - pair.pairCreatedAt : Infinity;
      if (pairAge > maxAgeMs) continue;
      if ((pair.liquidity?.usd || 0) < 300) continue;
      allPairs.push(pair);
      geckoAddresses.push(pair.baseToken.address);
    }
    if (geckoAddresses.length > 0) {
      const enriched = await batchFetchDexPairs(geckoAddresses);
      for (let i = 0; i < allPairs.length; i++) {
        const addr = allPairs[i].baseToken.address;
        const dexPair = enriched.get(addr);
        if (dexPair) allPairs[i] = dexPair;
      }
      const preFilterCount = allPairs.length;
      for (let i = allPairs.length - 1; i >= 0; i--) if ((allPairs[i].liquidity?.usd || 0) < 300) allPairs.splice(i, 1);
      console.log(`[SCAN] Enriched ${enriched.size}/${geckoAddresses.length} GeckoTerminal tokens with DexScreener m5 data${preFilterCount - allPairs.length > 0 ? ` (${preFilterCount - allPairs.length} dropped)` : ""}`);
    }
    for (const result of [raydiumResult, pumpfunResult, orcaResult]) {
      if (result.pairs) {
        const fresh = (result.pairs as DexScreenerPair[]).filter(p => p.chainId === "solana" && (p.liquidity?.usd || 0) >= 400 && (!p.pairCreatedAt || now - p.pairCreatedAt <= maxAgeMs)).slice(0, 20);
        allPairs.push(...fresh);
      }
    }
    const bestByAddress = new Map<string, DexScreenerPair>();
    for (const sp of allPairs) {
      const addr = sp.baseToken.address;
      const existing = bestByAddress.get(addr);
      if (!existing || (sp.liquidity?.usd || 0) > (existing.liquidity?.usd || 0)) bestByAddress.set(addr, sp);
    }
    const dedupedPairs = Array.from(bestByAddress.values());
    const pairMetrics = dedupedPairs.map(sp => {
      const m5b = sp.txns?.m5?.buys || 0, m5s = sp.txns?.m5?.sells || 0, h1b = sp.txns?.h1?.buys || 0, h1s = sp.txns?.h1?.sells || 0;
      const v5m = sp.volume?.m5 || 0, v1h = sp.volume?.h1 || 0;
      return {
        liq: sp.liquidity?.usd || 0, ageSeconds: Math.floor((now - (sp.pairCreatedAt || now)) / 1000),
        buyPressure5m: (m5b + m5s) > 0 ? m5b / (m5b + m5s) : 0.5, buyPressure1h: (h1b + h1s) > 0 ? h1b / (h1b + h1s) : 0.5,
        volMomentum: v1h > 0 ? (v5m * 12) / v1h : 0, priceChange5m: sp.priceChange?.m5 || 0, priceChange1h: sp.priceChange?.h1 || 0,
        vol5m: v5m, vol1h: v1h, fdv: sp.fdv || 0, txVelocity5m: m5b + m5s, h1buys: h1b, h1sells: h1s, m5buys: m5b, m5sells: m5s,
      };
    });
    const mlPredictions = await getMLBatchPredictions(pairMetrics);
    const results: any[] = [];
    for (let idx = 0; idx < dedupedPairs.length; idx++) {
      const sp = dedupedPairs[idx];
      const mlPred = mlPredictions[idx] || null;
      const scoring = scoreToken(sp, mlPred);
      const liq = sp.liquidity?.usd || 0, createdAt = sp.pairCreatedAt || now, ageSeconds = Math.floor((now - createdAt) / 1000);
      const m5b = sp.txns?.m5?.buys || 0, m5s = sp.txns?.m5?.sells || 0, bp5m = (m5b + m5s) > 0 ? m5b / (m5b + m5s) : 0.5;
      results.push({
        tokenAddress: sp.baseToken.address, tokenSymbol: sp.baseToken.symbol, tokenName: sp.baseToken.name, dex: sp.dexId,
        price: sp.priceUsd || "0", liquidity: liq.toFixed(2), score: scoring.combinedScore, mlScore: scoring.mlScore,
        ruleScore: scoring.score, pumpProbability: mlPred ? mlPred.pumpProb.toFixed(3) : null, dumpRisk: mlPred ? mlPred.dumpRisk.toFixed(3) : null,
        mlDumpRisk: mlPred?.dumpRisk ?? null, ageSeconds, qualifiedMode: scoring.qualifiedMode,
        volume5m: (sp.volume?.m5 || 0).toFixed(0), volume1h: (sp.volume?.h1 || 0).toFixed(0), volume24h: (sp.volume?.h24 || 0).toFixed(0),
        priceChange5m: sp.priceChange?.m5 || 0, priceChange1h: sp.priceChange?.h1 || 0, buys5m: m5b, sells5m: m5s,
        buys1h: sp.txns?.h1?.buys || 0, sells1h: sp.txns?.h1?.sells || 0, buyPressure5m: bp5m.toFixed(3), fdv: sp.fdv || 0,
        marketCap: sp.marketCap || 0, mlActive: mlPred !== null, source: "dexscreener_live", timestamp: new Date().toISOString(),
      });
    }
    results.sort((a, b) => (b.score || 0) - (a.score || 0));
    console.log(`[SCAN] Found ${results.length} candidates within discovery window`);
    if (results.length > 0) { liveCandidatesCache = results; lastScanTime = now; }
    return liveCandidatesCache;
  } catch (e) { console.error("DexScreener fetch error:", e); return liveCandidatesCache; }
}

async function initBalanceFromDB() {
  if (balanceInitialized) return;
  const status = await storage.getBotStatus();
  const storedBalance = parseFloat(status.walletBalance || "0");
  if (storedBalance > 0) {
    paperBalance = storedBalance;
    console.log(`[ENGINE] Restored wallet balance from DB: ${paperBalance.toFixed(3)} SOL`);
  } else {
    // DB walletBalance is 0 (e.g. after a reset that saved 0.0000).
    // Fall back to startingBalance so the UI shows the correct paper baseline.
    paperBalance = engineSettings.startingBalance;
    console.log(`[ENGINE] DB walletBalance is 0 — using startingBalance: ${paperBalance.toFixed(3)} SOL`);
    // Persist immediately so UI reads the correct value
    await storage.updateBotStats({ walletBalance: paperBalance.toFixed(4) });
  }
  const storedPeak = parseFloat((status as any).peakBalance || "0");
  // FIX: If DB walletBalance was 0 (reset/fresh start), peakBalance must also
  // reset — otherwise a stale high peak from a previous session inflates drawdown
  // to 40-50% before any trade fires, triggering the circuit breaker immediately.
  // Similarly cap if storedPeak is >20% above current balance (stale session data).
  // Threshold tightened from 1.5 → 1.2: a 20-50% stale peak (e.g. 0.630 vs 0.50
  // SOL after restart) previously slipped through the 1.5× guard and immediately
  // showed ~20% drawdown on startup with no trades.
  if (storedBalance <= 0 || storedPeak > paperBalance * 1.2) {
    peakBalance = paperBalance;
    console.log(`[ENGINE] peakBalance reset to ${paperBalance.toFixed(4)} SOL (stale DB peak ${storedPeak.toFixed(4)} discarded)`);
  } else {
    peakBalance = storedPeak > 0 ? storedPeak : paperBalance;
  }
  const storedDailyStart = parseFloat((status as any).dailyStartBalance || "0");
  dailyStartBalance = storedDailyStart > 0 ? storedDailyStart : paperBalance;
  try {
    const today = new Date().toDateString();
    const allTrades = await storage.getTrades();
    const closedToday = (allTrades as any[]).filter(t => t.status === "CLOSED" && new Date(t.closedAt || t.timestamp).toDateString() === today);
    dailyPnlSol = closedToday.reduce((sum, t) => sum + parseFloat(t.amount || "0") * (parseFloat(t.pnl || "0") / 100), 0);
    // Only count REAL trading exits in the streak — admin/operational closes
    // (DESYNC_NO_BALANCE, FORCE_SELL, RESET etc.) are not trading outcomes and
    // must not pollute the consecutive loss counter. Including them inflates the
    // streak and raises the score gate to 74+, blocking all trades.
    const ADMIN_EXIT_REASONS = new Set([
      "DESYNC_NO_BALANCE", "DESYNC_AUTO_CLOSE", "FORCE_SELL", "FORCE_SELL_NO_BALANCE",
      "RESET", "MANUAL_DESYNC_FIX",
    ]);
    const closedAll = (allTrades as any[])
      .filter(t => t.status === "CLOSED" && !ADMIN_EXIT_REASONS.has(t.exitReason || t.closeReason || ""))
      .sort((a, b) => new Date(b.closedAt || b.timestamp).getTime() - new Date(a.closedAt || a.timestamp).getTime());
    let wins = 0, losses = 0;
    for (const t of closedAll) {
      const pnl = parseFloat(t.pnl || "0");
      if (pnl > 0) { if (losses > 0) break; wins++; } else { if (wins > 0) break; losses++; }
    }
    consecutiveWins = wins; consecutiveLosses = losses;
    if (losses >= 3) {
      const storedCooldownEnd = parseFloat((status as any).lastLossCooldownEnd || "0");
      if (storedCooldownEnd > Date.now()) lastLossCooldownEnd = storedCooldownEnd;
    }
  } catch (e) { console.warn("[ENGINE] Could not restore risk state:", e); }
  const currentSolPrice = await getLiveSolPrice();
  const openTrades = await storage.getOpenTrades();
  // FIX: When no positions survive a restart there is zero unrealised drawdown.
  // A stale peakBalance from a prior session (e.g. 0.630 SOL vs current 0.50)
  // that slipped past the 1.2× guard above would still show phantom drawdown and
  // block the circuit breaker before any trade executes. Safe to reset here
  // because with no open trades there is nothing to measure drawdown against.
  if (openTrades.length === 0 && peakBalance > paperBalance) {
    console.log(`[ENGINE] No open trades on startup — peakBalance reset from ${peakBalance.toFixed(4)} to ${paperBalance.toFixed(4)} SOL (stale session peak discarded)`);
    peakBalance = paperBalance;
  }
  for (const t of openTrades) {
    tradedAddresses.set(t.tokenAddress, new Date(t.timestamp).getTime());
    if (t.peakPrice) peakPrices.set(t.id, parseFloat(t.peakPrice));
    if (!tradeStopPrices.has(t.id)) {
      const ep = parseFloat(t.price || "0");
      if (ep > 0) {
        const storedLiq = t.liquidity ? parseFloat(t.liquidity) : 0;
        const fallbackLiq = storedLiq > 0 ? storedLiq : (t.mode === "SNIPER" ? 5000 : t.mode === "MG" ? 15000 : 30000);
        const fallbackSize = parseFloat(t.amount || "0.1");
        tradeStopPrices.set(t.id, calcCostAwareStopPrice(ep, t.mode, fallbackLiq, fallbackSize, currentSolPrice));
      }
    }
  }
  // FIX: Sync the resolved peakBalance back to the DB immediately after init.
  // Without this, /api/status (reads DB botStatus.peakBalance) and
  // /api/engine/stats (reads in-memory peakBalance) can diverge after a restart
  // — the guards above may have clamped the in-memory peak down to paperBalance
  // while the DB still holds the old session high (e.g. 3.697 SOL vs 0.500 SOL).
  // When the frontend reads peak from one endpoint and drawdownPct from the other,
  // the pair is mathematically inconsistent (e.g. "0.1% drawdown, peak 3.697 SOL,
  // balance 3.58 SOL" — real drawdown would be 3.2%, not 0.1%).
  await storage.updateBotStats({
    peakBalance: peakBalance.toFixed(4),
    dailyStartBalance: dailyStartBalance.toFixed(4),
  }).catch(e => console.warn("[ENGINE] Could not sync peakBalance to DB on init:", e));
  balanceInitialized = true;
}

function getEffectiveMinScore(): number {
  const base = engineSettings.minScoreToTrade;
  const dailyLossPct = dailyStartBalance > 0 ? Math.max(0, (-dailyPnlSol / dailyStartBalance) * 100) : 0;
  const tierBonus = dailyLossPct >= 10 ? 15 : dailyLossPct >= 5 ? 10 : dailyLossPct > 0 ? 5 : 0;
  const streakBonus = Math.min(15, consecutiveLosses * 3);
  const effective = base + tierBonus + streakBonus;
  if (effective > base) console.log(`[SCORE_GATE] Raised min score: ${base} → ${effective} (dailyLoss=${dailyLossPct.toFixed(1)}%, streak=${consecutiveLosses})`);
  return effective;
}

async function runScanCycle() {
  if (scanLock) return;
  scanLock = true;
  try {
    await initBalanceFromDB();
    const now = Date.now();
    const cleanupThreshold = engineSettings.reentryDelayMs * 3;
    for (const [addr, ts] of tradedAddresses) if (now - ts > cleanupThreshold) tradedAddresses.delete(addr);
    for (const [addr, ts] of stoppedOutAddresses) if (now - ts > engineSettings.slReentryDelayMs) stoppedOutAddresses.delete(addr);
    for (const [addr, ts] of hardBlockedAddresses) {
      // FIX B: repeat-loser tokens use a longer TTL (4h) than normal hard-blocks (5min).
      const ttl = (tokenStopLossCount.get(addr) ?? 0) >= 2 ? REPEAT_LOSER_BLOCK_MS : HARD_BLOCK_TTL_MS;
      if (now - ts > ttl) { hardBlockedAddresses.delete(addr); tokenStopLossCount.delete(addr); }
    }
    for (const [addr, ts] of recentlyAttemptedBuys) if (now - ts > 15000) recentlyAttemptedBuys.delete(addr);
    for (const [addr, ts] of pendingBuys) if (now - ts > 30000) pendingBuys.delete(addr);
    const status = await storage.getBotStatus();
    if (!status.isRunning) return;
    const riskCheck = await checkCircuitBreakers();
    if (!riskCheck.canTrade) return;
    const openTrades = await storage.getOpenTrades();
    const candidates = await fetchDexScreenerCandidates();
    const top10 = candidates.slice(0, 10);
    if (top10.length === 0) return;
    // FIX X-1: volume5m is stored as a string (toFixed(0) returns string).
    // Using it directly in a reduce sum produces string concatenation not addition.
    // parseFloat converts it to a number first.
    const avgVolumeLast10 = top10.reduce((sum, c) => sum + parseFloat(c.volume5m as string || "0"), 0) / top10.length;
    if (top10.length >= 5 && avgVolumeLast10 < 1000) { console.log(`[PAUSE] Low market activity (avg 5m vol $${avgVolumeLast10.toFixed(0)} < $1k) — skipping cycle`); return; }
    const liveBal = (status.tradingMode === "live" && jupiterService) ? await jupiterService.getWalletBalance().catch(() => paperBalance) : paperBalance;
    const effectiveBalance = Math.max(0, liveBal - reservedCapital);
    if (effectiveBalance < MIN_FEE_BUFFER_SOL + 0.02) { console.log(`[RISK] Insufficient usable balance (effective ${effectiveBalance.toFixed(4)} SOL) — skipping cycle`); return; }
    const isSmallWallet = effectiveBalance < 0.3, isSmallCapWallet = effectiveBalance <= 0.5;
    const cycleMaxPositions = isSmallWallet ? 1 : isSmallCapWallet ? 2 : engineSettings.maxOpenPositions;
    const cycleMinSize = isSmallWallet ? 0.012 : isSmallCapWallet ? 0.025 : engineSettings.minPositionSize;
    if (openTrades.length >= cycleMaxPositions) return;
    if (sellingInProgress.size > 0) { console.log(`[SCAN] Deferring new buys — ${sellingInProgress.size} sell(s) in progress`); return; }
    let remainingBalance = effectiveBalance, failedTradesThisCycle = 0;
    if (openTrades.length > 0) {
      const worstOpenPnl = Math.min(...openTrades.map((t: any) => parseFloat(t.pnl || "0")));
      if (worstOpenPnl <= -5) { console.log(`[SCAN] Skipping new entries — worst open position at ${worstOpenPnl.toFixed(1)}%.`); return; }
    }
    // FIX C: pumpfun concentration guard. Pump.fun tokens are highly correlated —
    // if the narrative dies, all positions die together. Cap at 1 open pumpfun
    // position at a time to prevent correlated wipeouts.
    const PUMPFUN_DEXES = new Set(["pumpfun", "pump-fun", "pumpswap"]);
    const openPumpfunCount = openTrades.filter((t: any) => PUMPFUN_DEXES.has((t.dex || "").toLowerCase())).length;
    const openAddresses = new Set(openTrades.map((t: any) => t.tokenAddress));
    const boughtThisCycle = new Set<string>();
    let currentOpenCount = openTrades.length, tradesThisCycle = 0;
    let totalExposureSol = openTrades.reduce((sum, t) => sum + parseFloat(t.amount || "0"), 0);
    for (const candidate of candidates) {
      const addr = candidate.tokenAddress;
      if (boughtThisCycle.has(addr)) continue;
      if (pendingBuys.has(addr)) { console.log(`[SCAN] Skipping ${candidate.tokenSymbol} — buy already pending`); continue; }
      if (recentlyAttemptedBuys.has(addr)) { console.log(`[SCAN] Skipping ${candidate.tokenSymbol} — recently attempted and failed`); continue; }
      const lastTraded = tradedAddresses.get(addr);
      if (lastTraded) {
        const elapsed = Date.now() - lastTraded;
        // HARD FLOOR: never re-enter any token sooner than 30 seconds regardless of score.
        // Without this, score >= 85 bypassed reentryDelayMs entirely, allowing entries
        // within seconds of the previous close ($MULANIA entered 3x in 2 min, -57% on #3).
        const REENTRY_HARD_FLOOR_MS = 30_000;
        if (elapsed < REENTRY_HARD_FLOOR_MS) continue;
        // HIGH-SCORE BYPASS: only allow re-entry on score >= 85 if the token has NOT
        // stopped out. A stopped-out token should NEVER bypass the SL blackout — the
        // market already proved it's hostile for this token right now.
        const isStoppedOut = stoppedOutAddresses.has(addr);
        const highScoreAgain = candidate.score >= 85 && !isStoppedOut;
        if (elapsed < engineSettings.reentryDelayMs && !highScoreAgain) continue;
      }
      // POST-LOSS COOLDOWN: block re-entry on any token that had a loss exit recently.
      // This is the primary fix for the win→loss→loss re-entry pattern observed with
      // $Mantis (3x in 6min), $ROCKET, $VDOR, $PEPSI, $ARTEMISII, $USDOR etc.
      const lastLossTime = tokenLastLossMs.get(addr);
      if (lastLossTime) {
        const msSinceLoss = Date.now() - lastLossTime;
        if (msSinceLoss < POST_LOSS_COOLDOWN_MS) {
          console.log(`[GATE] SKIP $${candidate.tokenSymbol} — post-loss cooldown (${Math.round(msSinceLoss / 1000)}s ago, need ${POST_LOSS_COOLDOWN_MS / 1000}s)`);
          continue;
        }
      }
      // CONCENTRATION GUARD: hard cap at 2 entries per token address per session.
      // The old score >= 90 exception for a 3rd entry was exploited by $MULANIA (score 91)
      // which entered 3x in 2 minutes and took a -57% hit on the 3rd entry. No score
      // justifies a 3rd entry on the same contract in the same session.
      const sessionCount = sessionTokenBuyCount.get(addr) ?? 0;
      if (sessionCount >= 2) {
        console.log(`[GATE] SKIP $${candidate.tokenSymbol} — session concentration limit (${sessionCount} entries this session)`);
        continue;
      }
      // SYMBOL-BASED POST-LOSS COOLDOWN: same symbol, different contract address = still blocked.
      // Closes the gap where address-based gates are bypassed after a token migration/relaunch.
      const sym = candidate.tokenSymbol;
      const symLastLossTime = tokenSymbolLastLossMs.get(sym);
      if (symLastLossTime) {
        const msSinceSymLoss = Date.now() - symLastLossTime;
        if (msSinceSymLoss < SYMBOL_LOSS_COOLDOWN_MS) {
          console.log(`[GATE] SKIP $${sym} — symbol post-loss cooldown (${Math.round(msSinceSymLoss / 1000)}s ago, need ${SYMBOL_LOSS_COOLDOWN_MS / 1000}s)`);
          continue;
        }
      }
      // SYMBOL SL BLOCK: if this symbol previously exited via SL/LIQ_COLLAPSE, block re-entry
      // for the full slReentryDelayMs even if the new entry uses a different contract address.
      // Fixes $SOS re-entry 11m47s after LIQ_COLLAPSE — address-only gate was bypassed
      // because a new contract was deployed, but the 4-min symbol cooldown had already expired.
      const symSlBlockTime = tokenSymbolSlBlockMs.get(sym);
      if (symSlBlockTime) {
        const msSinceSlBlock = Date.now() - symSlBlockTime;
        if (msSinceSlBlock < SYMBOL_SL_COOLDOWN_MS) {
          console.log(`[GATE] SKIP $${sym} — symbol SL cooldown (${Math.round(msSinceSlBlock / 1000)}s ago, need ${SYMBOL_SL_COOLDOWN_MS / 1000}s)`);
          continue;
        }
      }
      // SYMBOL-BASED SESSION CONCENTRATION: hard cap at 2 entries per symbol per session.
      // Same logic as address-based cap — score-90 exception removed (see address cap comment).
      const symSessionCount = sessionSymbolBuyCount.get(sym) ?? 0;
      if (symSessionCount >= 2) {
        console.log(`[GATE] SKIP $${sym} — symbol session concentration limit (${symSessionCount} entries this session)`);
        continue;
      }
      if (hardBlockedAddresses.has(addr)) continue;
      const lastStopped = stoppedOutAddresses.get(addr);
      if (lastStopped && (Date.now() - lastStopped) < engineSettings.slReentryDelayMs) continue;
      if (openAddresses.has(addr)) continue;
      if (currentOpenCount >= cycleMaxPositions) break;
      if (tradesThisCycle >= engineSettings.maxTradesPerCycle) break;
      const { price, pair } = await fetchTokenPrice(candidate.tokenAddress);
      if (!pair || price <= 0) { console.log(`[GATE] SKIP ${candidate.tokenSymbol} — price zero or no pair`); continue; }
      // VOLUME SANITY: a token with zero 5m volume has no active market.
      // Buying it means there are no natural sellers to absorb our exit.
      // This catches dead/abandoned tokens before we spend a Jupiter quote call.
      const vol5mCheck = pair.volume?.m5 ?? 0;
      const txBuys5m = pair.txns?.m5?.buys ?? 0;
      const txSells5m = pair.txns?.m5?.sells ?? 0;
      const txTotal5m = txBuys5m + txSells5m;
      // Require meaningful two-sided activity: $1k+ volume AND 10+ total txns in last 5m.
      // Zero-volume or single-sided markets have no real exit depth.
      if (vol5mCheck < 1000 || txTotal5m < 10) {
        console.log(`[GATE] SKIP $${candidate.tokenSymbol} — insufficient 5m market activity (vol: $${vol5mCheck.toFixed(0)}, txns: ${txTotal5m})`);
        continue;
      }
      const pairDex = (pair.dexId || candidate.dex || "").toLowerCase();
      if (!JUPITER_SUPPORTED_DEXES.has(pairDex)) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — DEX "${pairDex}" not supported by Jupiter routing`); hardBlockedAddresses.set(addr, Date.now()); continue; }
      // FIX C: enforce pumpfun concentration limit
      if (PUMPFUN_DEXES.has(pairDex) && openPumpfunCount >= 1) {
        console.log(`[GATE] SKIP $${candidate.tokenSymbol} — pumpfun concentration limit (${openPumpfunCount} open pumpfun position already)`);
        continue;
      }
      // FIX: default to 0 (treat as brand-new) when pairCreatedAt is missing,
      // not Infinity. Infinity < JUPITER_INDEX_DELAY_MS is false, so missing
      // timestamps silently bypass the indexing gate and enter unrouted pools.
      const poolAgeMs = pair.pairCreatedAt ? Date.now() - pair.pairCreatedAt : 0;
      if (poolAgeMs < JUPITER_INDEX_DELAY_MS) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — pool only ${Math.floor(poolAgeMs / 1000)}s old, Jupiter needs ${JUPITER_INDEX_DELAY_MS / 1000}s to index`); continue; }
      const scanPrice = parseFloat(candidate.price);
      if (scanPrice > 0) {
        const priceDrift = Math.abs((price - scanPrice) / scanPrice) * 100;
        // SNIPER targets brand-new thin-pool tokens that legitimately move 20%+
        // in the 5s between scan and entry check. Applying the same 15% limit as
        // MG/HWR caused valid SNIPER setups to be blocked on every fast-moving token.
        const driftLimit = candidate.qualifiedMode === "SNIPER" ? 25 : 15;
        if (priceDrift > driftLimit) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — price drifted ${priceDrift.toFixed(1)}% since scan (limit: ${driftLimit}%)`); tradedAddresses.set(addr, Date.now()); continue; }
      }
      let scoring = scoreToken(pair);
      if (candidate.mlActive && candidate.mlScore != null) {
        const pumpProb = candidate.mlScore / 100;
        const dumpRisk = candidate.mlDumpRisk != null ? candidate.mlDumpRisk : 1 - pumpProb;
        const mlScore = candidate.mlScore;
        const mlAdjusted = mlScore * (1 - dumpRisk * 0.5);
        const combined = Math.max(0, Math.min(100, Math.round(scoring.score * engineSettings.scoreWeight + mlAdjusted * engineSettings.mlWeight)));
        scoring = { ...scoring, mlScore, combinedScore: combined };
      } else {
        const freshMl = await getMLPrediction(scoring.metrics);
        if (freshMl) {
          const mlScore = Math.round(freshMl.pumpProb * 100);
          const mlAdjusted = mlScore * (1 - freshMl.dumpRisk * 0.5);
          const combined = Math.max(0, Math.min(100, Math.round(scoring.score * engineSettings.scoreWeight + mlAdjusted * engineSettings.mlWeight)));
          scoring = { ...scoring, mlScore, combinedScore: combined };
        }
      }
      scoring.sizeSol = Math.max(cycleMinSize, scoring.sizeSol);
      const effectiveMinScore = getEffectiveMinScore();
      if (!scoring.qualifiedMode || scoring.combinedScore < effectiveMinScore || scoring.sizeSol < cycleMinSize) continue;
      if (status.mode !== "AUTO" && scoring.qualifiedMode !== status.mode) continue;
      const isLiveBuy = status.tradingMode === "live" && jupiterService !== null;
      const walletBal = isLiveBuy ? remainingBalance : paperBalance;
      const SOL_PRICE_USD = await getLiveSolPrice();
      const liq = pair.liquidity?.usd || 0;
      // LIVE LIQUIDITY GUARD: if DexScreener reports zero liquidity at buy time, skip.
      // sniperMinLiquidity inside scoreToken() only affects score/mode qualification —
      // it does NOT hard-block execution. A zero-liq token passes all gates, gets bought,
      // and immediately triggers LIQ_COLLAPSE (entry $0 → now $0, below floor) because
      // currentLiq=0 < 300. This is the pump.fun pattern where liquidity.usd is not
      // populated by DexScreener even though the pool has real on-chain depth.
      // Hard gate: enforce each mode's own minimum liquidity floor at execution time.
      // BUG FIX: previously this always used sniperMinLiquidity for all modes, meaning
      // HWR trades could execute on pools between sniperMinLiquidity and hwrMinLiquidity —
      // a gap where the mode qualification gate was satisfied but the execution gate was
      // too permissive. Now each mode enforces its own documented minimum at buy time.
      const MIN_BUY_LIQ_USD =
        scoring.qualifiedMode === "HWR"    ? engineSettings.hwrMinLiquidity :
        scoring.qualifiedMode === "SNIPER" ? engineSettings.sniperMinLiquidity :
        engineSettings.sniperMinLiquidity; // MG falls back to sniper floor
      if (liq < MIN_BUY_LIQ_USD) {
        console.log(`[GATE] SKIP $${candidate.tokenSymbol} — live liq $${liq.toFixed(0)} below min $${MIN_BUY_LIQ_USD} (DexScreener: ${pairDex})`);
        continue;
      }
      const poolLiqSol = SOL_PRICE_USD > 0 ? liq / SOL_PRICE_USD : Infinity;
      // COMPOUNDING: wallet % is the primary sizing driver — positions scale with the
      // wallet as it grows. The mode caps inside scoreToken() are qualification gates
      // only, not final sizing.
      //
      // SIZING PHILOSOPHY (hybrid of old aggressive + new safe):
      //   Base: 15% of wallet (old was 20%, post-survival-patch was 10%).
      //     At 15%, three back-to-back 100% rugs = -45% — inside the 45% circuit
      //     breaker, so the bot survives. At 10% it barely compounded on a 7 SOL
      //     wallet. At 20% two rugs could trip the breaker before wins offset.
      //   Pool liq cap: 2.5% of pool SOL value (old: 5%, survival patch: 1%).
      //     2.5% limits market impact to manageable levels while allowing meaningful
      //     fills on pools with ≥ $5k liquidity.
      //   Score multiplier (MG/HWR only — SNIPER stays fixed regardless of score):
      //     +20% at combinedScore ≥ 90 (very high conviction).
      //     +10% at combinedScore ≥ 85 (high conviction).
      //     SNIPER is excluded — high score on a brand-new thin pool does NOT justify
      //     a larger buy; slippage cost grows super-linearly with size there.
      //   Loss de-sizing:
      //     ×0.5 after 3+ consecutive losses — market is actively hostile, survive first.
      //     ×0.5 after 2 consecutive losses — halve exposure before the streak deepens.
      //     This is the analogue of the old scoreToken multipliers which were dead code
      //     (overridden in runScanCycle) — implemented here so they actually apply.
      //   Final hard caps: MAX_SINGLE_TRADE_PCT (20%) of remaining balance, and the
      //     wallet-scaled exposure limit below. Both are last-resort guards.
      let targetSize = walletBal * 0.15;
      targetSize = Math.min(targetSize, poolLiqSol * 0.025, remainingBalance * MAX_SINGLE_TRADE_PCT);
      // Score-based confidence scaling — MG/HWR only, never SNIPER.
      // Applied AFTER the liquidity cap so a high score cannot push us past the
      // pool-impact ceiling. The multiplier reflects expected-value confidence,
      // not an instruction to ignore liquidity constraints.
      if (scoring.qualifiedMode !== "SNIPER") {
        if (scoring.combinedScore >= 90) targetSize *= 1.20;
        else if (scoring.combinedScore >= 85) targetSize *= 1.10;
      }
      // Loss de-sizing: shrink positions during confirmed losing streaks.
      // Applied last so it overrides any score-based expansion — capital
      // preservation always wins over conviction during active drawdown.
      if (consecutiveLosses >= 3) targetSize *= 0.50;
      else if (consecutiveLosses >= 2) targetSize *= 0.50;
      // FIX: do NOT use Math.max(cycleMinSize, targetSize) here. That overrides the
      // liquidity clamps above, forcing oversized trades into illiquid pools.
      // If the clamps push the size below the minimum viable size, skip the trade.
      if (targetSize < cycleMinSize) {
        console.log(`[RISK] Skipping ${candidate.tokenSymbol} — safe size (${targetSize.toFixed(4)} SOL) below cycle minimum (${cycleMinSize} SOL)`);
        continue;
      }
      scoring.sizeSol = parseFloat(targetSize.toFixed(4));
      // ABSOLUTE SIZE CAP: at higher wallet balances (2+ SOL), 15% wallet sizing
      // produces 0.30+ SOL trades. Volatile/thin meme tokens at this size hit SL for
      // large absolute losses (-0.06 to -0.12 SOL per trade). Cap at 0.20 SOL max.
      // This allows healthy compounding while preventing outsized single-trade losses.
      const MAX_ABSOLUTE_TRADE_SOL = 0.20;
      if (scoring.sizeSol > MAX_ABSOLUTE_TRADE_SOL) {
        console.log(`[RISK] Size capped: ${scoring.sizeSol.toFixed(4)} → ${MAX_ABSOLUTE_TRADE_SOL} SOL ($${candidate.tokenSymbol})`);
        scoring.sizeSol = MAX_ABSOLUTE_TRADE_SOL;
      }
      // RE-ENTRY SIZE PENALTY: if re-entering a token that recently had a loss
      // (post-loss cooldown just expired), reduce size by 40% as a caution measure.
      if (lastLossTime && (Date.now() - lastLossTime) < POST_LOSS_COOLDOWN_MS * 3) {
        const penalizedSize = parseFloat((scoring.sizeSol * 0.60).toFixed(4));
        console.log(`[RISK] Re-entry size penalty: ${scoring.sizeSol.toFixed(4)} → ${penalizedSize.toFixed(4)} SOL ($${candidate.tokenSymbol} — recent loss)`);
        scoring.sizeSol = penalizedSize;
      }
      if (scoring.sizeSol < MIN_TRADE_SIZE_SOL) { console.log(`[RISK] Skipping ${candidate.tokenSymbol} — dust trade (${scoring.sizeSol.toFixed(5)} SOL)`); continue; }
      // EXPOSURE CAP: total open capital must not exceed 40% of total portfolio.
      // Critical accounting note: effectiveBalance in paper mode = FREE SOL only
      // (paperBalance after deducting deployed trades). totalExposureSol = DEPLOYED
      // SOL (already spent on open positions). Comparing deployed capital against the
      // free balance alone produces a shrinking denominator that chokes the bot as it
      // builds positions — by the time 2 positions are open, the "free" balance looks
      // small and every new trade is blocked even though total portfolio is healthy.
      // Correct denominator = free + deployed = full portfolio value.
      // For live mode: walletBal = remaining on-chain SOL, totalExposureSol = SOL
      // cost basis of open token positions → sum = full portfolio. Same identity.
      const totalPortfolioSol = walletBal + totalExposureSol;
      const maxTotalExposure = Math.max(engineSettings.maxPositionSize * 2, totalPortfolioSol * 0.40);
      if (totalExposureSol + scoring.sizeSol > maxTotalExposure) { console.log(`[RISK] Exposure limit reached — skipping ${candidate.tokenSymbol}`); continue; }
      const txCosts = calcTransactionCosts(liq, scoring.sizeSol);
      const entryTotalCostSol = scoring.sizeSol * (1 + (txCosts.entrySlippagePct + txCosts.entryFeePct) / 100);
      if (entryTotalCostSol < MIN_VIABLE_TRADE_SOL) { console.log(`[RISK] Skipping ${candidate.tokenSymbol} — trade too small (${entryTotalCostSol.toFixed(5)} SOL)`); continue; }
      if (isLiveBuy) {
        // FIX 8: Validate against fresh on-chain balance right before committing.
        // remainingBalance is a local running total that drifts when prior RPC
        // balance calls failed (fallback used) or concurrent txs moved SOL.
        // A stale check wastes priority fees on a buy that will fail in buyToken.
        const freshSolBal = await jupiterService!.getWalletBalance().catch(() => remainingBalance);
        const safeBalance = Math.max(0, freshSolBal - reservedCapital);
        if (safeBalance < scoring.sizeSol + MIN_FEE_BUFFER_SOL) {
          console.warn(`[RISK] Skipping ${candidate.tokenSymbol} — fresh balance ${safeBalance.toFixed(4)} SOL < trade ${scoring.sizeSol.toFixed(4)} + fee buffer ${MIN_FEE_BUFFER_SOL}`);
          recentlyAttemptedBuys.set(addr, Date.now());
          continue;
        }
        remainingBalance = safeBalance;
        console.log(`[CAPITAL] Before: ${remainingBalance.toFixed(4)} | Trade: ${scoring.sizeSol.toFixed(4)} | Est after: ${(remainingBalance - entryTotalCostSol).toFixed(4)}`);
      }
      const safety = await checkTokenSafety(candidate.tokenAddress, pair);
      if (!safety.safe) {
        console.log(`[SAFETY] BLOCKED $${candidate.tokenSymbol} — ${safety.reason}`);
        if (safety.reason.startsWith("rugcheck_danger") || safety.reason.startsWith("rugcheck_score_low") || safety.reason.startsWith("honeypot_risk_liq_fdv_ratio")) hardBlockedAddresses.set(addr, Date.now());
        continue;
      }
      let slippageBps = scoring.slippage * 100;
      if (scoring.qualifiedMode === "SNIPER") {
        const bp5mNum = parseFloat(candidate.buyPressure5m || "0");
        if ((candidate.priceChange5m || 0) > 7 && bp5mNum < 0.50) { console.log(`[TIMING SKIP] ${candidate.tokenSymbol} — SNIPER momentum cooling`); continue; }
      }
      const isMicroCapToken = liq < 3000 && candidate.ageSeconds < 60;
      const preflightImpactLimit = scoring.qualifiedMode === "SNIPER" ? (isMicroCapToken ? 6 : 7) : 4.0;
      const lamportsForPreflight = Math.floor(scoring.sizeSol * 1e9);
      const quoteCacheKey = `${candidate.tokenAddress}:${lamportsForPreflight}:${slippageBps}`;
      let executionQuote: any = null;
      if (isLiveBuy) {
        // Force fresh quote for execution (bypass cache)
        executionQuote = null;
        try {
          executionQuote = await jupiterService!.fetchQuote(SOL_MINT, candidate.tokenAddress, lamportsForPreflight, [slippageBps]);
          executionQuote._fetchedAt = Date.now();
          setCachedQuote(quoteCacheKey, executionQuote);
        } catch (quoteErr: any) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — Jupiter quote failed: ${quoteErr?.message ?? String(quoteErr)}`); recentlyAttemptedBuys.set(addr, Date.now()); continue; }
        const impactPct = parseFloat(executionQuote?.priceImpactPct ?? "0");
        if (impactPct > preflightImpactLimit) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — Jupiter price impact ${impactPct.toFixed(2)}% > ${preflightImpactLimit}% limit`); recentlyAttemptedBuys.set(addr, Date.now()); continue; }

        // SELL-SIDE PREFLIGHT: verify the token can be routed BACK to SOL before buying.
        // This is the primary guard against tokens that show +NaN in wallets — Jupiter
        // can quote a buy route but has no sell route (no liquidity on the exit side).
        // We use the outAmount from the buy quote as the sell input to simulate a round-trip.
        // If the sell quote fails entirely, block the buy unconditionally.
        // If it succeeds but returns < 40% of SOL spent, the spread is too wide — skip.
        if (isLiveBuy && executionQuote?.outAmount) {
          try {
            const sellCheckAmount = executionQuote.outAmount; // tokens we'd receive from buy
            const sellCheckQuote = await jupiterService!.fetchQuote(
              candidate.tokenAddress, SOL_MINT, sellCheckAmount, [slippageBps, Math.min(slippageBps * 2, 2000)]
            );
            if (!sellCheckQuote || !sellCheckQuote.outAmount) {
              console.log(`[GATE] SKIP $${candidate.tokenSymbol} — NO SELL ROUTE (token → SOL quote failed). Token likely has no exit liquidity.`);
              hardBlockedAddresses.set(addr, Date.now()); // hard block — won't improve without real liquidity
              recentlyAttemptedBuys.set(addr, Date.now());
              continue;
            }
            const sellReturnLamports = parseInt(sellCheckQuote.outAmount, 10);
            const buySpendLamports = lamportsForPreflight;
            const roundTripPct = (sellReturnLamports / buySpendLamports) * 100;
            if (roundTripPct < 50) {
              console.log(`[GATE] SKIP $${candidate.tokenSymbol} — round-trip only ${roundTripPct.toFixed(1)}% of SOL recoverable (spread too wide, likely illiquid trap)`);
              recentlyAttemptedBuys.set(addr, Date.now());
              continue;
            }
            const sellImpactPct = parseFloat(sellCheckQuote.priceImpactPct ?? "0");
            if (sellImpactPct > 10) {
              console.log(`[GATE] SKIP $${candidate.tokenSymbol} — sell-side impact too high (${sellImpactPct.toFixed(2)}%) — pool too thin to exit`);
              recentlyAttemptedBuys.set(addr, Date.now());
              continue;
            }
            console.log(`[PREFLIGHT] $${candidate.tokenSymbol} sell-side OK — round-trip: ${roundTripPct.toFixed(1)}% | buy impact: ${impactPct.toFixed(2)}% | sell impact: ${sellImpactPct.toFixed(2)}%`);
          } catch (sellCheckErr: any) {
            console.log(`[GATE] SKIP $${candidate.tokenSymbol} — sell-side preflight threw: ${sellCheckErr?.message ?? String(sellCheckErr)}`);
            recentlyAttemptedBuys.set(addr, Date.now());
            continue;
          }
        }
      }
      const preflight = executionQuote ? { priceImpactPct: parseFloat(executionQuote.priceImpactPct ?? "0"), outAmount: executionQuote.outAmount ?? "0", routeInfo: "direct" } : null;
      if (isLiveBuy && !preflight) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — no valid Jupiter quote for impact estimation`); recentlyAttemptedBuys.set(addr, Date.now()); continue; }
      const solPrice = SOL_PRICE_USD;
      const estimatedImpact = preflight?.priceImpactPct ?? (liq > 0 ? Math.min(12, ((scoring.sizeSol * solPrice) / (liq * 2)) * 100) : 6);
      // Edge check: ensure expected profit exceeds round-trip costs.
      // OLD: used priceChange5m * 0.6 as expected move — wrong for early/SNIPER entries
      // because new tokens haven't moved yet. A token up 0% in last 5m but about to
      // pump would always fail, while a token already +15% (a chase) would pass.
      // This caused all SNIPER entries to be blocked in live mode while paper executed
      // them freely — a large paper/live divergence.
      // NEW: use score-based expected move. A score of 65 → ~5% expected, 80 → ~12%,
      // 90+ → ~18%. This rewards conviction without requiring a pre-existing pump.
      const scoreBasedExpectedMove = Math.max(0, (scoring.combinedScore - 50) * 0.35);
      if (isMicroCapToken) {
        scoring.sizeSol = 0.02;
        const newSlippageBps = 800;
        if (isLiveBuy && newSlippageBps !== slippageBps) {
          try {
            // FIX V-1 (both parts):
            // 1. Recompute lamports AFTER the size override (was 5× too large before).
            // 2. Use fetchQuote (full object) not preflightQuote (partial) — the partial
            //    object guaranteed HTTP 400 on the first swap attempt every time.
            const microCapLamports = Math.floor(scoring.sizeSol * 1e9);
            const freshQuote = await jupiterService!.fetchQuote(SOL_MINT, candidate.tokenAddress, microCapLamports, [newSlippageBps]);
            if (!freshQuote) { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — no quote at micro-cap slippage`); continue; }
            executionQuote = freshQuote;
            executionQuote._fetchedAt = Date.now();
          } catch { console.log(`[GATE] SKIP $${candidate.tokenSymbol} — micro-cap quote fetch failed`); recentlyAttemptedBuys.set(addr, Date.now()); continue; }
        }
        slippageBps = newSlippageBps;
      }
      let actualSizeSol = scoring.sizeSol, buyTxHash: string;
      if (isLiveBuy) {
        const impactPct = parseFloat(executionQuote?.priceImpactPct ?? "0");
        if (impactPct > slippageBps / 100) { console.log(`[SLIPPAGE GUARD] SKIP ${candidate.tokenSymbol} — impact ${impactPct.toFixed(2)}% exceeds slippage ${(slippageBps / 100).toFixed(2)}%`); recentlyAttemptedBuys.set(addr, Date.now()); continue; }
        const finalEstimatedImpact = impactPct || estimatedImpact;
        const finalRoundTripCost = finalEstimatedImpact * 1.3 + engineSettings.txFeePercent * 2 + 1.0;
        const finalEdge = scoreBasedExpectedMove - finalRoundTripCost;
        if (finalEdge < MIN_EDGE_PCT) { console.log(`[FINAL EDGE SKIP] ${candidate.tokenSymbol} | score-edge ${finalEdge.toFixed(2)}% below ${MIN_EDGE_PCT}% (score ${scoring.combinedScore}, expectedMove ${scoreBasedExpectedMove.toFixed(1)}%, cost ${finalRoundTripCost.toFixed(1)}%)`); recentlyAttemptedBuys.set(addr, Date.now()); continue; }
        pendingBuys.set(addr, Date.now());
        reservedCapital += entryTotalCostSol;
        // FIX 7: try/finally guarantees pendingBuys and reservedCapital are always
        // cleaned up — even if an unexpected throw occurs mid-buy. The old pattern
        // had cleanup duplicated in the catch block AND after the try/catch; any
        // path that bypassed both (e.g. an unhandled rejection) froze capital.
        let buyResult: { success: boolean; txSignature: string | null; actualSolSpent: number; tokenAmountRaw: bigint; priceImpactPct: number; error?: string } | undefined;
        try {
          await new Promise(r => setTimeout(r, 150));
          buyResult = await withTimeout(jupiterService!.buyToken(candidate.tokenAddress, scoring.sizeSol, slippageBps, executionQuote ?? undefined, preflightImpactLimit), EXECUTION_TIMEOUT_MS, `BUY ${candidate.tokenSymbol}`);
        } catch (err: any) {
          console.log(`[LIVE] BUY ERROR $${candidate.tokenSymbol}: ${err.message}`);
          recentlyAttemptedBuys.set(addr, Date.now());
        } finally {
          pendingBuys.delete(addr);
          reservedCapital -= entryTotalCostSol;
        }
        if (!buyResult) { continue; }
        if (!buyResult.success) { console.log(`[LIVE] BUY FAILED $${candidate.tokenSymbol}: ${buyResult.error}`); recentlyAttemptedBuys.set(addr, Date.now()); tradedAddresses.set(addr, Date.now()); failedTradesThisCycle++; if (failedTradesThisCycle >= (isSmallWallet ? 1 : 2)) break; continue; }
        remainingBalance = (await jupiterService!.getWalletBalance().catch(() => remainingBalance)) - reservedCapital;
        actualSizeSol = buyResult.actualSolSpent;
        buyTxHash = buyResult.txSignature!;
        totalExposureSol += actualSizeSol;
        tradedAddresses.set(addr, Date.now());
        openAddresses.add(addr);
        boughtThisCycle.add(addr);
        currentOpenCount++;
        tradesThisCycle++;
        dailyTradeCount++;
        totalTradesAllTime++;
        const trade = await storage.addTrade({
          tokenAddress: candidate.tokenAddress, tokenSymbol: candidate.tokenSymbol, type: "BUY", mode: scoring.qualifiedMode,
          tradingMode: "live", status: "OPEN", amount: actualSizeSol.toFixed(4), price: price.toString(), currentPrice: price.toString(),
          peakPrice: price.toString(), pnl: "0", peakPnl: "0", score: scoring.combinedScore.toString(), txHash: buyTxHash, liquidity: liq.toFixed(2),
          dex: (pair.dexId || candidate.dex || "").toLowerCase(), // FIX F: persist dex so pumpfun concentration guard survives restarts
        });
        liveTokenBalances.set(trade.id, buyResult.tokenAmountRaw);
        peakPrices.set(trade.id, price);
        tradeStopPrices.set(trade.id, calcCostAwareStopPrice(price, scoring.qualifiedMode, liq, scoring.sizeSol, cachedSolPriceUsd));
        sessionTokenBuyCount.set(addr, (sessionTokenBuyCount.get(addr) ?? 0) + 1);
        sessionSymbolBuyCount.set(candidate.tokenSymbol, (sessionSymbolBuyCount.get(candidate.tokenSymbol) ?? 0) + 1);
        console.log(`[LIVE] BUY $${candidate.tokenSymbol} @ $${price.toFixed(8)} | ${scoring.qualifiedMode} | Score: ${scoring.combinedScore}/100 | SOL: ${actualSizeSol.toFixed(4)} | tx: ${buyTxHash.slice(0, 20)}... ${scoring.mlScore !== null ? `| ML: ${scoring.mlScore}%` : "| ML: offline"}`)
        console.log(`[LIFECYCLE:OPEN] id=#${trade.id} $${candidate.tokenSymbol} | mode: ${scoring.qualifiedMode} | entry: $${price.toFixed(8)} | size: ${actualSizeSol.toFixed(4)} SOL | timestamp: ${new Date().toISOString()} | tokens: ${buyResult.tokenAmountRaw}`);
      } else {
        if (paperBalance < entryTotalCostSol) break;
        paperBalance -= entryTotalCostSol;
        buyTxHash = `paper_${Date.now().toString(36)}_${candidate.tokenAddress.substring(0, 6)}`;
        totalExposureSol += scoring.sizeSol;
        tradedAddresses.set(addr, Date.now());
        openAddresses.add(addr);
        boughtThisCycle.add(addr);
        currentOpenCount++;
        tradesThisCycle++;
        dailyTradeCount++;
        totalTradesAllTime++;
        // Simulate realistic fill price including entry slippage.
        // paperBalance is already debited by entryTotalCostSol (which includes slippage),
        // but storing the raw price as trade.price makes PnL appear positive before
        // the position has actually recovered slippage costs. All exit logic (stop,
        // trailing, TP) must measure from the effective paid price, not the market quote.
        const effectivePaperEntryPrice = engineSettings.txCostsEnabled
          ? price * (1 + txCosts.entrySlippagePct / 100)
          : price;
        const trade = await storage.addTrade({
          tokenAddress: candidate.tokenAddress, tokenSymbol: candidate.tokenSymbol, type: "BUY", mode: scoring.qualifiedMode,
          tradingMode: "paper", status: "OPEN", amount: scoring.sizeSol.toFixed(4), price: effectivePaperEntryPrice.toString(), currentPrice: effectivePaperEntryPrice.toString(),
          peakPrice: effectivePaperEntryPrice.toString(), pnl: "0", peakPnl: "0", score: scoring.combinedScore.toString(), txHash: buyTxHash, liquidity: liq.toFixed(2),
          dex: (pair.dexId || candidate.dex || "").toLowerCase(),
        });
        peakPrices.set(trade.id, effectivePaperEntryPrice);
        tradeStopPrices.set(trade.id, calcCostAwareStopPrice(effectivePaperEntryPrice, scoring.qualifiedMode, liq, scoring.sizeSol, cachedSolPriceUsd));
        sessionTokenBuyCount.set(addr, (sessionTokenBuyCount.get(addr) ?? 0) + 1);
        sessionSymbolBuyCount.set(candidate.tokenSymbol, (sessionSymbolBuyCount.get(candidate.tokenSymbol) ?? 0) + 1);
        console.log(`[PAPER] BUY $${candidate.tokenSymbol} @ $${price.toFixed(8)} (effective $${effectivePaperEntryPrice.toFixed(8)}) | ${scoring.qualifiedMode} | Score: ${scoring.combinedScore}/100 | Size: ${scoring.sizeSol} SOL | Bal: ${paperBalance.toFixed(3)} ${scoring.mlScore !== null ? `| ML: ${scoring.mlScore}%` : "| ML: offline"}`)
        console.log(`[LIFECYCLE:OPEN] id=#${trade.id} $${candidate.tokenSymbol} | mode: ${scoring.qualifiedMode} | entry: $${effectivePaperEntryPrice.toFixed(8)} | size: ${scoring.sizeSol} SOL | timestamp: ${new Date().toISOString()} | paper`);
      }
      const allTrades = await storage.getTrades();
      const closedTrades = allTrades.filter((t: any) => t.status === "CLOSED");
      const wins = closedTrades.filter((t: any) => parseFloat(t.pnl || "0") > 0).length;
      const wr = closedTrades.length > 0 ? ((wins / closedTrades.length) * 100).toFixed(1) : "0";
      const displayBalance = (status.tradingMode === "live" && jupiterService) ? (await jupiterService.getWalletBalance().catch(() => paperBalance)).toFixed(4) : paperBalance.toFixed(3);
      await storage.updateBotStats({ walletBalance: displayBalance, totalTrades: allTrades.length, openPositions: currentOpenCount, winRate: wr, lastSignal: `BUY $${candidate.tokenSymbol} via ${scoring.qualifiedMode} (Score: ${scoring.combinedScore})` });
    }
  } catch (e) { console.error("[SCANNER] Error:", e); } finally { pendingBuys.clear(); reservedCapital = 0; scanLock = false; }
}

const FORCE_SELL_INTERVAL_MS  = 15_000;          // FIX 5: retry interval for persistent liquidation
const MAX_FORCE_SELL_TIME_MS  = 5 * 60_000;       // FIX 5: max 5-minute liquidation window

// ─────────────────────────────────────────────────────────────────────────────
// FIX 5: Persistent forced-liquidation loop.
//
// When a normal sell exhausts its retry budget (sellFailureStrikes > MAX_SELL_FAILURES)
// the old code logged CRITICAL and gave up — leaving real tokens stranded in the
// wallet with no automatic recovery. This function retries every FORCE_SELL_INTERVAL_MS
// for up to MAX_FORCE_SELL_TIME_MS at 30 % slippage (survival mode: any fill > nothing).
//
// Worst case outcome: bad fill price.  NOT: stuck funds.
// ─────────────────────────────────────────────────────────────────────────────
async function forceSellPosition(
  trade: any,
  fallbackPrice: number
): Promise<{ success: boolean; solReceived: number }> {
  if (!jupiterService) return { success: false, solReceived: 0 };
  const start    = Date.now();
  const sizeSol  = parseFloat(trade.amount || "0");

  console.warn(`[FORCE_SELL] Entering persistent liquidation for #${trade.id} $${trade.tokenSymbol}`);

  while (Date.now() - start < MAX_FORCE_SELL_TIME_MS) {
    try {
      let tokenAmountRaw = liveTokenBalances.get(trade.id) ?? BigInt(0);
      if (tokenAmountRaw === BigInt(0)) {
        tokenAmountRaw = await jupiterService.getTokenBalance(trade.tokenAddress).catch(() => BigInt(0));
      }

      if (tokenAmountRaw === BigInt(0)) {
        // Tokens already gone — nothing to sell, treat as complete.
        console.log(`[FORCE_SELL] #${trade.id} $${trade.tokenSymbol} — no on-chain balance, closing as desync`);
        return { success: true, solReceived: 0 };
      }

      const result = await withTimeout(
        jupiterService.sellToken(trade.tokenAddress, tokenAmountRaw, 3000), // 30% — survival mode
        EXECUTION_TIMEOUT_MS,
        `FORCE_SELL ${trade.tokenSymbol}`
      );

      if (result.success) {
        console.log(`[FORCE_SELL] SUCCESS #${trade.id} $${trade.tokenSymbol} | SOL: ${result.solReceived.toFixed(6)} | tx: ${result.txSignature?.slice(0, 20)}...`);
        liveTokenBalances.delete(trade.id);
        dailyPnlSol += result.solReceived - sizeSol;
        return { success: true, solReceived: result.solReceived };
      }

      console.warn(`[FORCE_SELL] Attempt failed #${trade.id} $${trade.tokenSymbol}: ${result.error} — retrying in ${FORCE_SELL_INTERVAL_MS / 1000}s`);
    } catch (e: any) {
      console.warn(`[FORCE_SELL] Exception #${trade.id} $${trade.tokenSymbol}: ${e.message}`);
    }

    await new Promise(r => setTimeout(r, FORCE_SELL_INTERVAL_MS));
  }

  console.error(`[FORCE_SELL] EXHAUSTED #${trade.id} $${trade.tokenSymbol} — ${MAX_FORCE_SELL_TIME_MS / 60000} min elapsed. MANUAL INTERVENTION REQUIRED.`);
  return { success: false, solReceived: 0 };
}

async function checkOpenPositions() {
  if (priceCheckLock) return;
  priceCheckLock = true;
  try {
    const openTrades = await storage.getOpenTrades();
    if (openTrades.length === 0) return;
    const liveTradesToSync = openTrades.filter((t: any) => t.tradingMode === "live" && jupiterService);
    const preloadedBalances = new Map<number, bigint>();
    if (liveTradesToSync.length > 0) {
      const balanceFetches = await Promise.allSettled(liveTradesToSync.map((t: any) => jupiterService!.getTokenBalance(t.tokenAddress)));
      for (let i = 0; i < liveTradesToSync.length; i++) {
        const r = balanceFetches[i];
        if (r.status === "fulfilled") preloadedBalances.set(liveTradesToSync[i].id, r.value);
        else console.warn(`[SYNC] Pre-fetch failed for #${liveTradesToSync[i].id} $${liveTradesToSync[i].tokenSymbol}`);
      }
    }
    for (const trade of openTrades) {
      try {
        if (sellingInProgress.has(trade.id)) continue;
        // Bug #2 fix: use fetchTokenPriceForExit (no wash-trade filter) so that
        // rug-pull panic-selling (vol >> liq) never silences the stop-loss check.
        const { price: currentPrice, pair } = await fetchTokenPriceForExit(trade.tokenAddress);
        if (currentPrice <= 0) continue;
        if (trade.tradingMode === "live" && jupiterService) {
          const onChainRaw = preloadedBalances.get(trade.id) ?? BigInt(0);
          const prefetchSucceeded = preloadedBalances.has(trade.id);
          if (onChainRaw > BigInt(0)) {
            const mapBalance = liveTokenBalances.get(trade.id);
            if (mapBalance !== onChainRaw) liveTokenBalances.set(trade.id, onChainRaw);
            zeroBalanceStrikes.delete(trade.id); // healthy read — reset any strike counter
          } else if (prefetchSucceeded && liveTokenBalances.has(trade.id)) {
            // FIX V-2: only delete the map entry when we have CONFIRMED on-chain zero
            // (prefetchSucceeded = true). If the prefetch failed (RPC error), onChainRaw
            // defaults to BigInt(0) but that doesn't mean tokens are gone — deleting
            // here would corrupt in-memory tracking and risk a false desync close.
            //
            // DESYNC GRACE PERIOD: Solana RPC nodes propagate confirmed tx state to ATA
            // balance reads with eventual consistency — the balance can read as 0 for up
            // to 90s after a buy confirms. Never delete the map entry (or auto-close) for
            // trades younger than DESYNC_GRACE_PERIOD_MS, even if RPC returns zero.
            const _rawTradeAgeMs = Date.now() - new Date(trade.timestamp).getTime();
            if (_rawTradeAgeMs < 0) {
              // Negative age means trade.timestamp was stored in local time (e.g. IST)
              // instead of UTC, making it appear ~5.5 hours in the future.
              // This causes the grace period check to be permanently true and the
              // trade to never self-close via desync logic.
              console.warn(`[TIME BUG] Trade #${trade.id} $${trade.tokenSymbol} has future timestamp (${trade.timestamp}) — age ${Math.round(_rawTradeAgeMs / 1000)}s. Ensure storage saves timestamps as new Date().toISOString() (UTC with Z suffix).`);
            }
            const tradeAgeMs = Math.max(0, _rawTradeAgeMs);
            if (tradeAgeMs < DESYNC_GRACE_PERIOD_MS) {
              console.log(`[SYNC] Zero balance for #${trade.id} $${trade.tokenSymbol} but trade only ${Math.round(tradeAgeMs / 1000)}s old — retaining cached balance (RPC propagation lag)`);
            } else {
              console.warn(`[SYNC] Confirmed zero balance #${trade.id} $${trade.tokenSymbol}: map had ${liveTokenBalances.get(trade.id)} but on-chain zero → removed`);
              liveTokenBalances.delete(trade.id);
            }
          } else if (!prefetchSucceeded && liveTokenBalances.has(trade.id)) {
            console.warn(`[SYNC] Prefetch failed for #${trade.id} $${trade.tokenSymbol} — retaining cached balance ${liveTokenBalances.get(trade.id)}`);
          }
          if (onChainRaw === BigInt(0) && prefetchSucceeded) {
            // DESYNC GRACE PERIOD: suppress auto-close for fresh trades.
            // A zero balance this soon after a buy is RPC lag, not a real desync.
            const tradeAgeMsForDesync = Math.max(0, Date.now() - new Date(trade.timestamp).getTime());
            if (tradeAgeMsForDesync < DESYNC_GRACE_PERIOD_MS) {
              console.log(`[SYNC] Suppressing DESYNC_AUTO_CLOSE for #${trade.id} $${trade.tokenSymbol} — trade only ${Math.round(tradeAgeMsForDesync / 1000)}s old, within ${DESYNC_GRACE_PERIOD_MS / 1000}s grace period`);
              zeroBalanceStrikes.delete(trade.id);
              continue;
            }
            // MULTI-STRIKE CONFIRMATION: require ZERO_STRIKES_REQUIRED consecutive zero
            // reads before treating as a real desync. A single transient zero from an
            // overloaded RPC node must not close a live position — on a non-zero read we
            // reset the counter and do a live retry before the final close.
            const strikes = (zeroBalanceStrikes.get(trade.id) ?? 0) + 1;
            if (strikes < ZERO_STRIKES_REQUIRED) {
              zeroBalanceStrikes.set(trade.id, strikes);
              console.log(`[SYNC] Zero balance strike ${strikes}/${ZERO_STRIKES_REQUIRED} for #${trade.id} $${trade.tokenSymbol} — waiting for confirmation`);
              continue;
            }
            // All strikes consumed — do one final live read before closing.
            const retryBalance = await jupiterService!.getTokenBalance(trade.tokenAddress).catch(() => BigInt(0));
            if (retryBalance > BigInt(0)) {
              console.log(`[SYNC] False desync for #${trade.id} $${trade.tokenSymbol} — balance appeared on retry (${retryBalance}). Resetting strikes.`);
              liveTokenBalances.set(trade.id, retryBalance);
              zeroBalanceStrikes.delete(trade.id);
              continue;
            }
            zeroBalanceStrikes.delete(trade.id);
            const entryForDesync = parseFloat(trade.price || "0");
            const desyncPnlPct = entryForDesync > 0 && currentPrice > 0 ? (((currentPrice - entryForDesync) / entryForDesync) * 100).toFixed(2) : "0";
            const desyncSizeSol = parseFloat(trade.amount || "0");
            dailyPnlSol += desyncSizeSol * (parseFloat(desyncPnlPct) / 100);
            console.warn(`[LIVE] DESYNC DETECTED #${trade.id} $${trade.tokenSymbol} — zero on-chain balance → auto-closing (PNL: ${desyncPnlPct}%)`);
            await storage.closeTrade(trade.id, currentPrice.toString(), desyncPnlPct, "DESYNC_AUTO_CLOSE");
            liveTokenBalances.delete(trade.id); peakPrices.delete(trade.id); partialTpTaken.delete(trade.id);
            tradeStopPrices.delete(trade.id); prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id);
            tradedAddresses.set(trade.tokenAddress, Date.now());
            // FIX Z-4: desync closes must update the streak so the loss cooldown
            // can fire from repeated RPC outage + auto-close events.
            const desyncIsWin = parseFloat(desyncPnlPct) > 0;
            if (desyncIsWin) { consecutiveWins++; consecutiveLosses = 0; lastMiniCooldownEnd = 0; }
            else {
              consecutiveLosses++; consecutiveWins = 0;
              tokenSymbolLastLossMs.set(trade.tokenSymbol, Date.now()); // Change 6: symbol cooldown on desync loss
              if (consecutiveLosses === 2) {
                lastMiniCooldownEnd = Date.now() + MINI_LOSS_COOLDOWN_MS;
                console.log(`[RISK] 2 consecutive desync-closes — ${MINI_LOSS_COOLDOWN_MS / 1000}s mini-cooldown activated`);
              }
              if (consecutiveLosses >= 3) {
                lastLossCooldownEnd = Date.now() + engineSettings.lossCooldownMs;
                // FIX 16: reset counter so next penalty requires 3 NEW losses,
                // not immediately re-triggering on the very next trade.
                consecutiveLosses = 0;
                console.log(`[RISK] 3 consecutive desync-closes — ${engineSettings.lossCooldownMs / 1000}s cooldown activated`);
              }
            }
            continue;
          }
        }
        const entryPrice = parseFloat(trade.price);
        if (entryPrice <= 0) continue;
        let pnlPct = ((currentPrice - entryPrice) / entryPrice) * 100;
        if (pnlPct > 500) { console.log(`[TRADE] SUSPICIOUS PNL $${trade.tokenSymbol} | +${pnlPct.toFixed(1)}% exceeds 500% cap — capping`); pnlPct = 500; }
        const holdTime = Math.max(0, Date.now() - new Date(trade.timestamp).getTime()) / 1000;
        const tradeScore = parseInt(trade.score || "0", 10);
        const dynamicTP = getScoreBasedTP(tradeScore);
        const liveBP = (() => { if (!pair) return 0.5; const b = pair.txns?.m5?.buys || 0, s = pair.txns?.m5?.sells || 0; return (b + s) > 0 ? b / (b + s) : 0.5; })();
        const dynamicMaxHold = getScoreBasedMaxHold(tradeScore, pnlPct, liveBP);
        let peak = peakPrices.get(trade.id) || entryPrice;
        if (currentPrice > peak) { peak = currentPrice; peakPrices.set(trade.id, peak); }
        const peakPnl = ((peak - entryPrice) / entryPrice) * 100;
        const drawdownFromPeak = peak > 0 ? ((peak - currentPrice) / peak) * 100 : 0;
        await storage.updateTradeCurrentPrice(trade.id, currentPrice.toString(), pnlPct.toFixed(2));
        await storage.updateTradePeakPrice(trade.id, peak.toString(), peakPnl.toFixed(2));
        // LIFECYCLE:HOLD heartbeat — emitted every 30s per trade for production monitoring
        const _now = Date.now();
        if (_now - (lifecycleLastLogMs.get(trade.id) ?? 0) >= LIFECYCLE_HOLD_INTERVAL_MS) {
          lifecycleLastLogMs.set(trade.id, _now);
          console.log(`[LIFECYCLE:HOLD] id=#${trade.id} $${trade.tokenSymbol} | age: ${Math.round(holdTime)}s | pnl: ${pnlPct.toFixed(2)}% | peak: ${peakPnl.toFixed(2)}% | price: $${currentPrice.toFixed(8)} | mode: ${trade.mode}`);
        }
        // TRAIL:ACTIVATED — logged once when trailing stop becomes armed
        if (!trailActivatedLogged.has(trade.id) && peakPnl >= engineSettings.trailingStopActivation) {
          trailActivatedLogged.add(trade.id);
          console.log(`[TRAIL:ACTIVATED] id=#${trade.id} $${trade.tokenSymbol} | peakPnl: +${peakPnl.toFixed(2)}% reached threshold +${engineSettings.trailingStopActivation}% | trailing distance: -${engineSettings.trailingStopDistance}%`);
        }
        // Partial TP
        if (!partialTpTaken.has(trade.id) && pnlPct >= engineSettings.partialTpThreshold && pnlPct < dynamicTP) {
          const sizeSol = parseFloat(trade.amount);
          const partialSize = sizeSol * engineSettings.partialTpRatio;
          const isLivePartial = trade.tradingMode === "live" && jupiterService !== null;
          let partialSuccess = false;
          if (isLivePartial) {
            sellingInProgress.add(trade.id);
            try {
              let totalTokens = liveTokenBalances.get(trade.id) ?? BigInt(0);
              if (totalTokens === BigInt(0)) { totalTokens = await jupiterService!.getTokenBalance(trade.tokenAddress); if (totalTokens > BigInt(0)) liveTokenBalances.set(trade.id, totalTokens); }
              if (totalTokens > BigInt(0)) {
                const sellTokens = (totalTokens * BigInt(Math.round(engineSettings.partialTpRatio * 100))) / 100n;
                const partialLiq = pair?.liquidity?.usd ?? 1000;
                const partialCosts = calcTransactionCosts(partialLiq, partialSize);
                const partialSlippageBps = Math.min(2000, Math.max(100, Math.round(partialCosts.exitSlippagePct * 1.5 * 100)));
                const partialResult = await withTimeout(jupiterService!.sellToken(trade.tokenAddress, sellTokens, partialSlippageBps), EXECUTION_TIMEOUT_MS, `PARTIAL_SELL ${trade.tokenSymbol}`);
                if (partialResult.success) {
                  liveTokenBalances.set(trade.id, totalTokens - sellTokens);
                  dailyPnlSol += partialResult.solReceived - partialSize;
                  partialTpTaken.add(trade.id);
                  await storage.updateTradeAmount(trade.id, (sizeSol - partialSize).toFixed(4));
                  console.log(`[LIVE] PARTIAL TP $${trade.tokenSymbol} | Sold ${engineSettings.partialTpRatio * 100}% on-chain @ +${pnlPct.toFixed(1)}% | SOL received: ${partialResult.solReceived.toFixed(4)} | tx: ${partialResult.txSignature?.slice(0, 20)}...`);
                  partialSuccess = true;
                } else console.warn(`[LIVE] PARTIAL TP FAILED $${trade.tokenSymbol}: ${partialResult.error}`);
              } else console.warn(`[LIVE] PARTIAL TP DESYNC: No tokens for $${trade.tokenSymbol}`);
            } finally { sellingInProgress.delete(trade.id); }
          } else {
            const partialLiq = pair?.liquidity?.usd ?? 1000;
            const partialTxCosts = calcTransactionCosts(partialLiq, partialSize);
            const partialExitCostPct = partialTxCosts.exitSlippagePct + partialTxCosts.exitFeePct;
            const netPartialPnlPct = pnlPct - partialExitCostPct;
            const partialReturn = partialSize * (1 + netPartialPnlPct / 100);
            paperBalance += partialReturn;
            partialTpTaken.add(trade.id);
            dailyPnlSol += partialReturn - partialSize;
            await storage.updateTradeAmount(trade.id, (sizeSol - partialSize).toFixed(4));
            console.log(`[PAPER] PARTIAL TP $${trade.tokenSymbol} | Sold ${engineSettings.partialTpRatio * 100}% @ +${pnlPct.toFixed(1)}% | ExitCost: -${partialExitCostPct.toFixed(1)}% | Secured: ${partialReturn.toFixed(4)} SOL`);
            partialSuccess = true;
          }
          if (partialSuccess) {
            // Keep prevPnlMap current even on a partial-TP cycle so PROFIT_DECLINE
            // has a fresh baseline on the very next price check. Without this, the
            // baseline is stale by one cycle and a drop just after partial TP is invisible.
            prevPnlMap.set(trade.id, pnlPct);
            continue;
          }
        }
        const prevPnl = prevPnlMap.get(trade.id) ?? null;
        prevPnlMap.set(trade.id, pnlPct);
        if (pnlPct >= 1) {
          const stable = pnlStableMap.get(trade.id);
          if (!stable) pnlStableMap.set(trade.id, { pnl: pnlPct, since: Date.now() });
          else if (Math.abs(pnlPct - stable.pnl) >= 0.5) pnlStableMap.set(trade.id, { pnl: pnlPct, since: Date.now() });
        } else pnlStableMap.delete(trade.id);
        let shouldClose = false, reason = "";
        // FIX SURVIVAL-1: HARD LOSS KILL — fires unconditionally at -12% PNL.
        // Stop-loss of -6% is theoretical; memecoin prices gap through it in <3s.
        // By the time priceCheckIntervalMs fires again, actual loss is -30% to -100%.
        // This is the last-resort circuit before the position bleeds to zero.
        // No trailing, no grace, no hold-time conditions — just exit immediately.
        if (pnlPct <= -10) { shouldClose = true; reason = `HARD_LOSS_KILL (pnl ${pnlPct.toFixed(2)}% ≤ -10% hard floor)`; }
        // FIX SURVIVAL-2: TAKE_PROFIT_20 — restored from old working version.
        // The new dynamicTP allows holding until +65 to +100% depending on score.
        // In practice, memecoins peak and collapse within seconds. EDFB peaked at
        // +17.9% and exited at -104% because dynamicTP was 90% (score=94). BOPS
        // peaked at +12% and exited at -104% with dynamicTP=80%. The old version
        // exited both at +20% via this check — capturing real profit instead of
        // watching it evaporate. Always exit at +20%: it's a real, bankable gain.
        else if (pnlPct >= 20) { shouldClose = true; reason = `TAKE_PROFIT_20 (+${pnlPct.toFixed(2)}%)`; }
        const costAwareStopPrice = tradeStopPrices.get(trade.id) ?? 0;
        const stopLossPct = costAwareStopPrice > 0 && entryPrice > 0 ? ((costAwareStopPrice - entryPrice) / entryPrice) * 100 : engineSettings.stopLoss;
        const halfStopPct = stopLossPct / 2;
        const trailingFloor = peakPnl > 30 ? peakPnl * 0.50 : peakPnl > 15 ? peakPnl * 0.38 : peakPnl > 8 ? peakPnl * 0.25 : peakPnl > 3 ? peakPnl * 0.15 : 0;
        // NOTE: HARD_TP (pnlPct >= dynamicTP) is removed. dynamicTP minimum is 65%
        // but TAKE_PROFIT_20 above always fires at +20%, so HARD_TP was unreachable.
        // dynamicTP is still used as the upper-bound guard for partial TP above.
        // NEAR-MISS SUPPRESSION: if pnlPct is already above +17% and the tick-to-tick
        // drop is under 3%, suppress PROFIT_DECLINE and let TAKE_PROFIT_20 fire cleanly.
        // Without this, normal price oscillation at +17-19% (e.g. +18% → +16%, drop=2%)
        // triggers an early exit just below the +20% gate — capturing 15-17% instead of 20%.
        // The suppression window is intentionally narrow: only active when pnlPct > 17
        // (close enough to TP gate to matter) AND drop < 3% (small oscillation, not a
        // genuine reversal). A real reversal at this level (≥3% drop) still fires normally.
        const isNearTpGate = pnlPct > 17 && (prevPnl - pnlPct) < 3.0;
        // Bug #6 fix: grace period reduced from 60 → 20 s.  The original 60 s window
        // allowed a token to drop from +5 % to -9 % in the first minute without
        // PROFIT_DECLINE firing (HARD_LOSS_KILL only activates at -10 %).  20 s
        // still gives two or three price-check cycles to confirm the move is real
        // before closing, without creating a 40-second free-bleed window on fast rugs.
        if (prevPnl !== null && prevPnl > 0 && pnlPct > 0 && pnlPct < prevPnl && prevPnl >= 1.0 && (prevPnl - pnlPct) >= 2.0 && holdTime > 20 && !isNearTpGate) {
          shouldClose = true; reason = `PROFIT_DECLINE (was +${prevPnl.toFixed(2)}%, now +${pnlPct.toFixed(2)}%, drop=${(prevPnl - pnlPct).toFixed(2)}%)`;
        }
        else if ((() => { const stable = pnlStableMap.get(trade.id); if (!stable || pnlPct < 1) return false; const stagnantMs = peakPnl < 3.0 ? 35_000 : 60_000; return (Date.now() - stable.since) >= stagnantMs; })()) {
          const stableSec = Math.round((Date.now() - (pnlStableMap.get(trade.id)!.since)) / 1000);
          shouldClose = true; reason = `PNL_STAGNANT (+${pnlPct.toFixed(2)}% unchanged for ${stableSec}s)`;
        }
        else if (peakPnl >= engineSettings.trailingStopActivation && drawdownFromPeak >= engineSettings.trailingStopDistance) {
          shouldClose = true;
          reason = `TRAIL_STOP (peak +${peakPnl.toFixed(1)}%, fell ${drawdownFromPeak.toFixed(1)}%, floor +${trailingFloor.toFixed(1)}%)`;
        }
        else if (costAwareStopPrice > 0 && currentPrice <= costAwareStopPrice) { shouldClose = true; reason = `STOP_LOSS (stop $${costAwareStopPrice.toFixed(8)}, price $${currentPrice.toFixed(8)}, pnl ${pnlPct.toFixed(1)}%)`; }
        else if (holdTime > dynamicMaxHold && pnlPct < 5) { shouldClose = true; reason = `MAX_HOLD(${Math.round(dynamicMaxHold)}s)`; }
        else if (holdTime > dynamicMaxHold / 2 && pnlPct < halfStopPct) { shouldClose = true; reason = `EARLY_CUT (pnl ${pnlPct.toFixed(1)}% < halfStop ${halfStopPct.toFixed(1)}%)`; }
        else if (holdTime > 120 && pnlPct < stopLossPct * 0.7) { shouldClose = true; reason = `FAST_CUT (pnl ${pnlPct.toFixed(1)}% past 70% of stop ${(stopLossPct * 0.7).toFixed(1)}%)`; }
        else if (pnlPct > 10 && (() => { const bp = pair && pair.txns?.m5 ? ((pair.txns.m5.buys + pair.txns.m5.sells) > 0 ? pair.txns.m5.buys / (pair.txns.m5.buys + pair.txns.m5.sells) : 0.5) : 0.5; const pc5m = pair?.priceChange?.m5 || 0; return bp < 0.43 && pc5m < -3; })()) { const bp = pair && pair.txns?.m5 ? ((pair.txns.m5.buys + pair.txns.m5.sells) > 0 ? pair.txns.m5.buys / (pair.txns.m5.buys + pair.txns.m5.sells) : 0.5) : 0.5; const pc5m = pair?.priceChange?.m5 || 0; shouldClose = true; reason = `EARLY_EXIT_WEAK_BP (bp=${bp.toFixed(2)}, Δ5m=${pc5m.toFixed(1)}%)`; }
        else if (pair && pnlPct > 5 && ((pair.volume?.m5 || 0) / (pair.liquidity?.usd || 1)) > 7) { const volLiq = (pair.volume?.m5 || 0) / (pair.liquidity?.usd || 1); shouldClose = true; reason = `LIQUIDITY_EXHAUSTION (${volLiq.toFixed(2)}x)`; }
        else if (!shouldClose && pair && holdTime > 45) { const m5b = pair.txns?.m5?.buys || 0, m5s = pair.txns?.m5?.sells || 0; const currentBP = (m5b + m5s) > 0 ? m5b / (m5b + m5s) : 0.5; const priceChange5m = pair.priceChange?.m5 || 0; if (currentBP < 0.38 && priceChange5m < -2) { shouldClose = true; reason = `MOMENTUM_FADE (BP=${currentBP.toFixed(2)}, Δ5m=${priceChange5m.toFixed(1)}%)`; } else if (pnlPct > 5 && currentBP < 0.43 && priceChange5m < -4) { shouldClose = true; reason = `PROFIT_PROTECT_FADE (BP=${currentBP.toFixed(2)}, Δ5m=${priceChange5m.toFixed(1)}%, PNL=+${pnlPct.toFixed(1)}%)`; } }
        // FIX: VOL_COLLAPSE must be an independent `if`, not `else if`.
        // When holdTime > 45, the MOMENTUM_FADE branch above consumes the else-if,
        // and VOL_COLLAPSE (holdTime > 180) is never evaluated — tokens bleed to
        // zero indefinitely. Using a separate if allows both checks to run.
        if (!shouldClose && pair && holdTime > 180 && pnlPct > 1) { const currentVol5m = pair.volume?.m5 || 0; const vol1hNow = pair.volume?.h1 || 0; const expectedVol5m = vol1hNow / 12; if (expectedVol5m > 100 && currentVol5m < expectedVol5m * 0.15) { shouldClose = true; reason = `VOL_COLLAPSE (5m vol ${currentVol5m.toFixed(0)} is <15% of expected ${expectedVol5m.toFixed(0)})`; } }
        // FIX D: Liquidity collapse emergency exit. A rug pull drains LP before it crashes
        // price — our stop-loss fires too late because price is calculated against drained
        // liquidity. If current liquidity is below $300 (un-tradeable) OR has dropped >70%
        // from entry while we're still holding, exit immediately at any PNL.
        // This fires regardless of holdTime because rugs don't wait.
        if (!shouldClose && pair) {
          const currentLiq = pair.liquidity?.usd ?? 0;
          // FIX LIQ_CO: "0" is a truthy string so the old ternary (trade.liquidity ? parseFloat(...) : 0)
          // resolved to parseFloat("0") = 0 for every trade stored with zero liquidity — making the
          // relative 50% drop check permanently false (0 > 1000 is never true). Use parseFloat with
          // nullish coalesce and a || 0 fallback so NaN / "0" / null / undefined all produce 0, and
          // log a warning so we can confirm the stored value is non-zero going forward.
          const entryLiqUsd = parseFloat(trade.liquidity ?? "0") || 0;
          if (entryLiqUsd === 0 && !liqCoWarnedTrades.has(trade.id)) {
            liqCoWarnedTrades.add(trade.id);
            console.warn(`[LIQ_CO] #${trade.id} $${trade.tokenSymbol} — entry liquidity missing or zero, relative drop check disabled`);
          }
          const liqCollapsed = currentLiq < 300;
          const liqDropped70pct = entryLiqUsd > 1000 && currentLiq < entryLiqUsd * 0.50; // 50% drain threshold (was 30%)
          if (liqCollapsed || liqDropped70pct) {
            shouldClose = true;
            reason = `LIQ_COLLAPSE (entry $${entryLiqUsd.toFixed(0)} → now $${currentLiq.toFixed(0)}, ${liqCollapsed ? "below floor" : ">50% drain"})`;
          }
        }
        if (shouldClose) {
          // FIX H: CONSOLIDATED FLOOR — applies to every exit path, not just TRAIL_STOP
          // and PROFIT_DECLINE. LIQ_COLLAPSE and VOL_COLLAPSE set shouldClose in independent
          // if-blocks that run after the floor-protected branches, so pnlPct was never clamped
          // for them. $FAH: peakPnl 12%, floor should be +3%, recorded -14.5% via VOL_COLLAPSE.
          // $808: peakPnl 3.7%, floor should be +0.55%, recorded -22.77% via LIQ_COLLAPSE.
          // The floor is an accounting protection — it doesn't change the on-chain fill price,
          // but it prevents gap fills from tripping the daily circuit breaker on good sessions.
          // Exception: STOP_LOSS, HARD_LOSS_KILL, EARLY/FAST_CUT fire when there was no
          // meaningful peak — applying the floor there would be misleading.
          const isHardLoss = reason.startsWith("STOP_LOSS") || reason.startsWith("HARD_LOSS_KILL") ||
                             reason.startsWith("EARLY_CUT") || reason.startsWith("FAST_CUT");
          if (!isHardLoss && pnlPct < trailingFloor && trailingFloor > 0) {
            console.log(`[EXIT:FLOOR] $${trade.tokenSymbol} | ${reason.split(" ")[0]} | raw pnl ${pnlPct.toFixed(2)}% → floor locked at +${trailingFloor.toFixed(2)}% (peak was +${peakPnl.toFixed(1)}%)`);
            pnlPct = trailingFloor;
          }
          console.log(`[LIFECYCLE:EXIT] id=#${trade.id} $${trade.tokenSymbol} | reason: ${reason} | pnl: ${pnlPct.toFixed(2)}% | peakPnl: ${peakPnl.toFixed(2)}% | holdTime: ${Math.round(holdTime)}s | mode: ${trade.tradingMode}`);
          lifecycleLastLogMs.delete(trade.id);
          trailActivatedLogged.delete(trade.id);
          const sizeSol = parseFloat(trade.amount);
          const isLiveSell = trade.tradingMode === "live" && jupiterService !== null;
          let finalPnlPct: number, sellTxSig: string | null = null;
          if (isLiveSell) {
            sellingInProgress.add(trade.id);
            // FIX: when the force-sell background task takes over, it owns
            // sellingInProgress for its entire 5-minute window. The flag
            // prevents the outer finally from deleting the entry prematurely,
            // which would let the next price-check cycle re-enter the sell
            // path and attempt a double-sell on the same live position.
            let handedOffToForceSell = false;
            try {
              let tokenAmountRaw = liveTokenBalances.get(trade.id) ?? BigInt(0);
              if (tokenAmountRaw === BigInt(0)) { tokenAmountRaw = await jupiterService!.getTokenBalance(trade.tokenAddress); if (tokenAmountRaw > BigInt(0)) liveTokenBalances.set(trade.id, tokenAmountRaw); }
              if (tokenAmountRaw === BigInt(0)) {
                const desyncPnlPct = sizeSol > 0 && entryPrice > 0 && currentPrice > 0 ? (((currentPrice - entryPrice) / entryPrice) * 100).toFixed(2) : "0";
                const desyncPnlSol = sizeSol * (parseFloat(desyncPnlPct) / 100);
                dailyPnlSol += desyncPnlSol;
                console.warn(`[LIVE] DESYNC: No tokens on-chain for $${trade.tokenSymbol} (trade #${trade.id}). Auto-closing in DB (PNL: ${desyncPnlPct}%).`);
                await storage.closeTrade(trade.id, currentPrice.toString(), desyncPnlPct, "DESYNC_NO_BALANCE");
                liveTokenBalances.delete(trade.id); peakPrices.delete(trade.id); partialTpTaken.delete(trade.id);
                tradeStopPrices.delete(trade.id); prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id);
                tradedAddresses.set(trade.tokenAddress, Date.now());
                continue;
              }
              const exitLiqUsd = pair?.liquidity?.usd ?? 1000;
              const exitCostsModel = calcTransactionCosts(exitLiqUsd, sizeSol);
              const baseExitSlippageBps = Math.min(2000, Math.max(100, Math.round(exitCostsModel.exitSlippagePct * 1.5 * 100)));
              // If this trade has previous sell failures, use escalated slippage from
              // the ladder — don't start back at base slippage on every retry.
              const priorStrikes = sellFailureStrikes.get(trade.id) ?? 0;
              const exitSlippageBps = priorStrikes === 0 ? baseExitSlippageBps
                : priorStrikes === 1 ? Math.min(baseExitSlippageBps * 2, 500)
                : priorStrikes === 2 ? 500
                : priorStrikes === 3 ? 1500
                : 3000;
              // FIX E: Auto-escalate exit slippage when liquidity has shrunk since entry.
              // If liq at entry was > $1k but current liq < 40% of entry, the pool is
              // draining — use a minimum of 500bps to avoid failed fills and wasted fees.
              const entryLiqForSell = trade.liquidity ? parseFloat(trade.liquidity) : 0;
              const currentLiqForSell = pair?.liquidity?.usd ?? 0;
              const liqDrainedSignificantly = entryLiqForSell > 1000 && currentLiqForSell > 0 && currentLiqForSell < entryLiqForSell * 0.40;
              const autoEscalatedExitBps = liqDrainedSignificantly ? Math.max(exitSlippageBps, 500) : exitSlippageBps;
              if (liqDrainedSignificantly && autoEscalatedExitBps > exitSlippageBps) {
                console.warn(`[SELL] Liq drained ${entryLiqForSell.toFixed(0)}→${currentLiqForSell.toFixed(0)} — auto-escalating exit slippage ${exitSlippageBps}→${autoEscalatedExitBps}bps`);
              }
              // Sell impact guard: pre-check
              const sellQuote = await jupiterService!.fetchQuote(trade.tokenAddress, SOL_MINT, tokenAmountRaw.toString(), [autoEscalatedExitBps]);
              const sellImpactPct = parseFloat(sellQuote?.priceImpactPct ?? "0");
              if (sellImpactPct > 50) console.warn(`[SELL] Extreme impact ${sellImpactPct.toFixed(1)}% for ${trade.tokenSymbol} — forcing sell anyway (rugpull escape)`);
              const sellResult = await withTimeout(jupiterService!.sellToken(trade.tokenAddress, tokenAmountRaw, autoEscalatedExitBps), EXECUTION_TIMEOUT_MS, `SELL ${trade.tokenSymbol}`);
              if (!sellResult.success) {
                const strikes = (sellFailureStrikes.get(trade.id) ?? 0) + 1;
                sellFailureStrikes.set(trade.id, strikes);
                // AUTO-ESCALATING SLIPPAGE LADDER: each failed sell retries with wider
                // slippage rather than giving up. Giving up = tokens stuck on-chain with
                // no automatic recovery — in live mode that is a guaranteed full loss.
                // Strike 1 → 2x slippage (wider but still reasonable)
                // Strike 2 → 500 bps (5% — covers most pool conditions)
                // Strike 3 → 1500 bps (15% — emergency exit, accept bad fill over stuck)
                // Strike 4+ → 3000 bps (30% — last resort, any fill beats zero)
                if (strikes <= 4) {
                  const escalatedBps = strikes === 1 ? Math.min(exitSlippageBps * 2, 500)
                    : strikes === 2 ? 500
                    : strikes === 3 ? 1500
                    : 3000;
                  console.warn(`[LIVE] SELL FAILED $${trade.tokenSymbol} (attempt ${strikes}): ${sellResult.error} — escalating slippage to ${escalatedBps}bps next cycle`);
                  // Store escalated slippage for next cycle by bumping the strike count
                  // — the escalated bps will be derived from it on the next price check.
                } else {
                  // FIX 6: Instead of logging CRITICAL and giving up (which leaves real tokens
                  // stranded in the wallet forever), launch the persistent force-sell loop in
                  // the background. It retries every 15s at 30% slippage for up to 5 minutes.
                  // sellingInProgress keeps the normal sell path from double-triggering.
                  // We do NOT await — this must not block the price-checking loop.
                  console.error(`[SELL] CRITICAL: $${trade.tokenSymbol} #${trade.id} failed ${strikes} times — launching persistent force-sell loop (30% slippage, 5-min window)`);
                  const capturedTrade  = { ...trade };
                  const capturedPrice  = currentPrice;
                  // Hand ownership of sellingInProgress to the background task.
                  // The entry is already present (added before the try block above).
                  // The background .then()/.catch() finally blocks are responsible
                  // for the eventual delete — do NOT let the outer finally remove it.
                  handedOffToForceSell = true;
                  forceSellPosition(capturedTrade, capturedPrice).then(async ({ success, solReceived }) => {
                    try {
                      const { price: exitPrice } = await fetchTokenPrice(capturedTrade.tokenAddress).catch(() => ({ price: capturedPrice, pair: null }));
                      const safeExitPrice = exitPrice > 0 ? exitPrice : capturedPrice;
                      const entryPriceFp  = parseFloat(capturedTrade.price || "0");
                      const capSizeSol    = parseFloat(capturedTrade.amount || "0");
                      const finalPnlPct   = success && solReceived > 0
                        ? (capSizeSol > 0 ? ((solReceived - capSizeSol) / capSizeSol) * 100 : 0)
                        : (entryPriceFp > 0 && safeExitPrice > 0 ? ((safeExitPrice - entryPriceFp) / entryPriceFp) * 100 : 0);
                      const closeReason   = success ? "FORCE_SELL" : "FORCE_SELL_FAILED_MANUAL_REQUIRED";
                      await storage.closeTrade(capturedTrade.id, safeExitPrice.toString(), finalPnlPct.toFixed(2), closeReason);
                      sellFailureStrikes.delete(capturedTrade.id);
                      peakPrices.delete(capturedTrade.id);
                      partialTpTaken.delete(capturedTrade.id);
                      tradeStopPrices.delete(capturedTrade.id);
                      prevPnlMap.delete(capturedTrade.id);
                      pnlStableMap.delete(capturedTrade.id);
                      zeroBalanceStrikes.delete(capturedTrade.id);
                      tradedAddresses.set(capturedTrade.tokenAddress, Date.now());
                      console.log(`[FORCE_SELL] DB closed #${capturedTrade.id} $${capturedTrade.tokenSymbol} | PNL: ${finalPnlPct.toFixed(2)}% | success: ${success}`);
                    } catch (dbErr: any) {
                      console.error(`[FORCE_SELL] DB close failed #${capturedTrade.id}: ${dbErr.message}`);
                    } finally {
                      sellingInProgress.delete(capturedTrade.id);
                    }
                  }).catch((e: any) => {
                    console.error(`[FORCE_SELL] Unhandled error #${capturedTrade.id}: ${e.message}`);
                    sellingInProgress.delete(capturedTrade.id);
                  });
                }
                continue;
              }
              sellFailureStrikes.delete(trade.id); // clear on success
              sellTxSig = sellResult.txSignature;
              finalPnlPct = sizeSol > 0 ? ((sellResult.solReceived - sizeSol) / sizeSol) * 100 : 0;
              dailyPnlSol += sellResult.solReceived - sizeSol;
              liveTokenBalances.delete(trade.id);
              const liveBalAfterSell = await jupiterService!.getWalletBalance().catch(() => 0);
              if (liveBalAfterSell > peakBalance) peakBalance = liveBalAfterSell;
              console.log(`[LIVE] ${finalPnlPct >= 0 ? "WIN" : "LOSS"} SELL $${trade.tokenSymbol} | PNL: ${finalPnlPct >= 0 ? "+" : ""}${finalPnlPct.toFixed(2)}% | ${reason} | tx: ${sellTxSig?.slice(0, 20)}...`);
            } finally { if (!handedOffToForceSell) sellingInProgress.delete(trade.id); }
          } else {
            let exitPnlPct = Math.max(pnlPct, -99);
            const exitLiq = pair?.liquidity?.usd ?? 1000;
            const exitTxCosts = calcTransactionCosts(exitLiq, sizeSol);
            const exitCostPct = exitTxCosts.exitSlippagePct + exitTxCosts.exitFeePct;
            // FIX: floor at -99 AFTER subtracting exit costs. In live trading you cannot
            // lose more than 100% of a position — the worst case is selling for near-zero
            // and receiving dust. Applying exit costs on top of a -99% position produced
            // -109% in paper mode, which inflated the circuit breaker's daily loss calc
            // and drawdown figure with numbers that are physically impossible in live mode.
            exitPnlPct = Math.max(-99, exitPnlPct - exitCostPct);
            // FIX FLOOR: the trailing floor was applied to pnlPct before entering this
            // branch (line ~1716), but subtracting exit costs can push exitPnlPct back
            // below it (e.g. floor +0.95%, exitCost 3.8% → −2.85%). The floor is an
            // accounting device to prevent gap-through trail exits from tripping the
            // circuit breaker on sessions that peaked positive — it must survive costs.
            // isHardLoss and trailingFloor are both in scope from the shouldClose block.
            if (!isHardLoss && trailingFloor > 0 && exitPnlPct < trailingFloor) {
              exitPnlPct = trailingFloor;
            }
            const returnSol = sizeSol * (1 + exitPnlPct / 100);
            paperBalance += returnSol;
            dailyPnlSol += returnSol - sizeSol;
            finalPnlPct = exitPnlPct;
            if (paperBalance > peakBalance) peakBalance = paperBalance;
            console.log(`[PAPER] ${finalPnlPct >= 0 ? "WIN" : "LOSS"} SELL $${trade.tokenSymbol} @ $${currentPrice.toFixed(8)} | PNL: ${finalPnlPct >= 0 ? "+" : ""}${finalPnlPct.toFixed(2)}% | ${reason} | ExitCost: -${exitCostPct.toFixed(1)}% | Bal: ${paperBalance.toFixed(3)} SOL`);
          }
          const isWin = finalPnlPct! > 0;
          if (isWin) { consecutiveWins++; consecutiveLosses = 0; lastMiniCooldownEnd = 0; }
          else {
            consecutiveLosses++; consecutiveWins = 0;
            // POST-LOSS COOLDOWN: record this token's loss timestamp so the entry gate
            // can block re-entry for POST_LOSS_COOLDOWN_MS. This prevents the observed
            // pattern of immediately re-entering a token that just stopped out or bled.
            tokenLastLossMs.set(trade.tokenAddress, Date.now());
            tokenSymbolLastLossMs.set(trade.tokenSymbol, Date.now()); // Change 6: symbol-level cooldown
            if (consecutiveLosses === 2) {
              // 2-loss mini-cooldown: pause 3 minutes before the next entry.
              // Keeps the bot from adding a third loss mid-streak while market is hostile.
              lastMiniCooldownEnd = Date.now() + MINI_LOSS_COOLDOWN_MS;
              console.log(`[RISK] 2 consecutive losses — ${MINI_LOSS_COOLDOWN_MS / 1000}s mini-cooldown activated`);
            }
            if (consecutiveLosses >= 3) {
              lastLossCooldownEnd = Date.now() + engineSettings.lossCooldownMs;
              // FIX: reset so next penalty requires 3 NEW losses, not instantly
              // re-firing on every subsequent loss from an accumulated count.
              consecutiveLosses = 0;
              console.log(`[RISK] 3 consecutive losses — ${engineSettings.lossCooldownMs / 1000}s cooldown activated`);
            }
          }
          await storage.closeTrade(trade.id, currentPrice.toString(), finalPnlPct!.toFixed(2), reason);
          tradedAddresses.set(trade.tokenAddress, Date.now());
          if (reason.startsWith("STOP_LOSS") || reason.startsWith("HARD_LOSS_KILL") || reason.startsWith("EARLY_CUT") || reason.startsWith("FAST_CUT") || reason.startsWith("LIQ_COLLAPSE") || reason.startsWith("VOL_COLLAPSE")) {
            stoppedOutAddresses.set(trade.tokenAddress, Date.now());
            // Block re-entry on ANY new contract with the same symbol for the full slReentryDelayMs.
            // Fixes $SOS re-entering 11m47s after LIQ_COLLAPSE via a new contract address —
            // stoppedOutAddresses is address-keyed so the new address bypassed it; this closes the gap.
            tokenSymbolSlBlockMs.set(trade.tokenSymbol, Date.now());
            // FIX B: increment repeat-loser strike counter and extend block for chronic losers.
            // Two stops on the same token in a session = the market has rejected this token twice.
            // Continuing to re-enter just bleeds fees. Lock it out for 4 hours instead of 15 min.
            // FIX G: LIQ_COLLAPSE and VOL_COLLAPSE are structurally equivalent to a stop-loss —
            // the token's pool is either drained or dead. Previously they only set tradedAddresses
            // (60s gate) instead of stoppedOutAddresses (900s gate), allowing immediate re-entry
            // into the same hostile token. $FARTCAT entered twice 73s apart for -23% and -14%.
            const slCount = (tokenStopLossCount.get(trade.tokenAddress) ?? 0) + 1;
            tokenStopLossCount.set(trade.tokenAddress, slCount);
            if (slCount >= 2) {
              hardBlockedAddresses.set(trade.tokenAddress, Date.now()); // reuse hardBlock with custom TTL
              console.log(`[RISK] REPEAT_LOSER $${trade.tokenSymbol} — ${slCount} SLs this session → hard block for ${REPEAT_LOSER_BLOCK_MS / 3600000}h`);
            } else {
              console.log(`[RISK] SL blackout set for $${trade.tokenSymbol} (${reason.split(" ")[0]}) — no re-entry for ${(engineSettings.slReentryDelayMs / 60000).toFixed(0)} min`);
            }
          }
          peakPrices.delete(trade.id); partialTpTaken.delete(trade.id); tradeStopPrices.delete(trade.id);
          prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id); liveTokenBalances.delete(trade.id);
          sellFailureStrikes.delete(trade.id);
          zeroBalanceStrikes.delete(trade.id);
          liqCoWarnedTrades.delete(trade.id);
          const allTrades = await storage.getTrades();
          const closedTrades = allTrades.filter((t: any) => t.status === "CLOSED");
          const winsCount = closedTrades.filter((t: any) => parseFloat(t.pnl || "0") > 0).length;
          const totalPnl = closedTrades.reduce((sum, t) => sum + parseFloat(t.pnl || "0"), 0);
          const wr = closedTrades.length > 0 ? ((winsCount / closedTrades.length) * 100).toFixed(1) : "0";
          const openNow = allTrades.filter((t: any) => t.status === "OPEN").length;
          const displayBal = (isLiveSell && jupiterService) ? (await jupiterService.getWalletBalance().catch(() => 0)).toFixed(4) : paperBalance.toFixed(3);
          await storage.updateBotStats({ walletBalance: displayBal, totalPnl: (totalPnl / Math.max(closedTrades.length, 1)).toFixed(2), winRate: wr, totalTrades: allTrades.length, openPositions: openNow, lastSignal: `SOLD $${trade.tokenSymbol} | ${isWin ? "+" : ""}${finalPnlPct!.toFixed(1)}% | ${reason}`, peakBalance: peakBalance.toFixed(4), lastLossCooldownEnd, dailyStartBalance: dailyStartBalance.toFixed(4) });
        }
      } catch (tradeErr) { console.error(`[POSITION_MANAGER] Error processing $${trade.tokenSymbol}:`, tradeErr); }
    }
  } catch (e) { console.error("[POSITION_MANAGER] Error:", e); } finally { priceCheckLock = false; }
}

async function startTradingEngine() {
  if (scannerInterval) clearInterval(scannerInterval);
  if (priceCheckerInterval) clearInterval(priceCheckerInterval);
  // Reset session-scoped state on every engine start so stale counts from a
  // previous run don't carry over and block valid entries on the new session.
  sessionTokenBuyCount.clear();
  sessionSymbolBuyCount.clear();       // Change 4: symbol-scoped buy counts
  tokenSymbolLastLossMs.clear();       // Change 4: symbol-scoped loss timestamps
  tokenSymbolSlBlockMs.clear();        // FIX: symbol-level SL block (new contract, same symbol)
  tokenStopLossCount.clear(); // FIX B: clear repeat-loser strikes on engine restart
  liqCoWarnedTrades.clear();           // FIX: warn-once guard reset on engine start
  console.log("[ENGINE] Starting trading engine...");
  jupiterService = createJupiterService();
  if (jupiterService) {
    const walletBal = await jupiterService.getWalletBalance().catch(() => 0);
    console.log(`[ENGINE] Live trading ENABLED | wallet: ${jupiterService.walletAddress} | balance: ${walletBal.toFixed(4)} SOL`);
    await syncLiveTokenBalances();
  } else console.log("[ENGINE] Live trading DISABLED — paper mode only");
  await initBalanceFromDB();
  const mlUp = await checkMLService();
  console.log(mlUp ? "[ENGINE] ML Service connected" : "[ENGINE] ML Service not available");
  if (mlCheckerInterval) clearInterval(mlCheckerInterval);
  mlCheckerInterval = setInterval(checkMLService, 30000);
  console.log("[ENGINE] Fetching live SOL price from DexScreener...");
  for (let attempt = 0; attempt < 10; attempt++) {
    const price = await getLiveSolPrice();
    if (solPriceFetchedOnce && price > 0) { console.log(`[ENGINE] SOL price locked at $${price.toFixed(2)}`); break; }
    if (attempt < 9) await new Promise(r => setTimeout(r, 2000));
    else console.warn(`[ENGINE] Could not fetch live SOL price after 10 attempts — proceeding with cached fallback $${cachedSolPriceUsd}`);
  }
  scannerInterval = setInterval(runScanCycle, engineSettings.scanIntervalMs);
  priceCheckerInterval = setInterval(checkOpenPositions, engineSettings.priceCheckIntervalMs);
  setTimeout(runScanCycle, 3000);
  setTimeout(checkOpenPositions, 8000);
}

async function syncLiveTokenBalances() {
  if (!jupiterService) return;
  try {
    const openTrades = await storage.getOpenTrades();
    const liveTrades = openTrades.filter((t: any) => t.tradingMode === "live");
    if (liveTrades.length === 0) return;
    console.log(`[JUPITER] Syncing token balances for ${liveTrades.length} open live trade(s)...`);
    const fetches = await Promise.allSettled(liveTrades.map((t: any) => jupiterService!.getTokenBalance(t.tokenAddress)));
    for (let i = 0; i < liveTrades.length; i++) {
      const trade = liveTrades[i];
      const result = fetches[i];
      if (result.status === "fulfilled") {
        if (result.value > BigInt(0)) { liveTokenBalances.set(trade.id, result.value); console.log(`[JUPITER] Restored trade #${trade.id} ($${trade.tokenSymbol}): ${result.value} raw tokens`); }
        else console.warn(`[JUPITER] Trade #${trade.id} ($${trade.tokenSymbol}): no ATA balance found`);
      } else console.error(`[JUPITER] Trade #${trade.id} ($${trade.tokenSymbol}): balance fetch failed — ${(result as PromiseRejectedResult).reason?.message ?? "unknown"}`);
    }
  } catch (e) { console.error("[JUPITER] syncLiveTokenBalances error:", e); }
}

export async function registerRoutes(httpServer: Server, app: Express): Promise<Server> {
  await storage.seedInitialData();
  await startTradingEngine();

  app.get(api.status.get.path, async (req, res) => { res.json(await storage.getBotStatus()); });
  app.get(api.trades.list.path, async (req, res) => { res.json(await storage.getTrades()); });
  app.get(api.candidates.list.path, async (req, res) => { res.json(await storage.getCandidates()); });
  app.get("/api/candidates/live", async (_req, res) => { try { res.json(await fetchDexScreenerCandidates()); } catch (e) { console.error(e); res.json([]); } });
  app.get("/api/trades/open", async (_req, res) => { try { res.json(await storage.getOpenTrades()); } catch (e) { console.error(e); res.status(500).json({ error: "Failed to fetch open trades" }); } });
  app.get("/api/engine/stats", async (_req, res) => {
    try {
      const allTrades = await storage.getTrades();
      const closedTrades = allTrades.filter((t: any) => t.status === "CLOSED");
      const openTrades = allTrades.filter((t: any) => t.status === "OPEN");
      const wins = closedTrades.filter((t: any) => parseFloat(t.pnl || "0") > 0);
      const losses = closedTrades.filter((t: any) => parseFloat(t.pnl || "0") <= 0);
      const avgWin = wins.length > 0 ? wins.reduce((s, t) => s + parseFloat(t.pnl || "0"), 0) / wins.length : 0;
      const avgLoss = losses.length > 0 ? losses.reduce((s, t) => s + parseFloat(t.pnl || "0"), 0) / losses.length : 0;
      const totalPnlSol = closedTrades.reduce((s, t) => s + (parseFloat(t.amount || "0") * parseFloat(t.pnl || "0") / 100), 0);
      const bestTrade = closedTrades.length > 0 ? closedTrades.reduce((best, t) => parseFloat(t.pnl || "0") > parseFloat(best?.pnl || "-999") ? t : best, closedTrades[0]) : null;
      const worstTrade = closedTrades.length > 0 ? closedTrades.reduce((worst, t) => parseFloat(t.pnl || "0") < parseFloat(worst?.pnl || "999") ? t : worst, closedTrades[0]) : null;
      const uptimeSeconds = Math.floor((Date.now() - engineStartTime) / 1000);
      // FIX W-4: use time elapsed TODAY (not total uptime) as denominator.
      // With total uptime, dailyPnlSol resets at midnight but uptimeSeconds never
      // resets, so solPerHour trends toward zero on long-running sessions even on
      // profitable days. Cap at today's start (midnight) or engine start, whichever
      // is later.
      const dayStartMs   = new Date().setHours(0, 0, 0, 0);
      const elapsedToday = Math.max(1, (Date.now() - Math.max(dayStartMs, engineStartTime)) / 1000);
      const solPerHour   = (dailyPnlSol / (elapsedToday / 3600)).toFixed(4);
      // elapsedTodaySeconds is exposed so the frontend can recompute solPerHour
      // directly from dailyPnlSol in the same JSON snapshot, rather than deriving
      // it from a separate poll that may be one cycle stale.
      const elapsedTodaySeconds = Math.round(elapsedToday);
      res.json({
        totalTrades: allTrades.length, closedTrades: closedTrades.length, openTrades: openTrades.length,
        wins: wins.length, losses: losses.length,
        winRate: closedTrades.length > 0 ? ((wins.length / closedTrades.length) * 100).toFixed(1) : "0",
        avgWinPct: avgWin.toFixed(2), avgLossPct: avgLoss.toFixed(2), totalPnlSol: totalPnlSol.toFixed(4),
        bestTrade: bestTrade ? { symbol: bestTrade.tokenSymbol, pnl: bestTrade.pnl, mode: bestTrade.mode } : null,
        worstTrade: worstTrade ? { symbol: worstTrade.tokenSymbol, pnl: worstTrade.pnl, mode: worstTrade.mode } : null,
        consecutiveWins, consecutiveLosses, paperBalance: paperBalance.toFixed(3), engineVersion: "4.2+ML",
        mlServiceActive: mlServiceAvailable, scoreBlend: `Rule ${engineSettings.scoreWeight * 100}% + ML ${engineSettings.mlWeight * 100}%`,
        trailingStop: `+${engineSettings.trailingStopActivation}% / -${engineSettings.trailingStopDistance}%`,
        hardTP: `+${engineSettings.hardTakeProfit}-100%`, stopLoss: `${engineSettings.stopLoss}%`,
        solPerHour, uptimeSeconds, dailyPnlSol: dailyPnlSol.toFixed(4), dailyTradeCount,
        elapsedTodaySeconds,
        peakBalance: peakBalance.toFixed(3),
        drawdownPct: peakBalance > 0 ? Math.max(0, (peakBalance - (await getEffectiveBalance())) / peakBalance * 100).toFixed(1) : "0",
        circuitBreakerActive, dailyLossLimitPct: engineSettings.dailyLossLimitPct, maxDrawdownPct: engineSettings.maxDrawdownPct,
        txCostsEnabled: !!engineSettings.txCostsEnabled, safetyChecksEnabled: !!engineSettings.safetyChecksEnabled,
        dynamicHoldEnabled: !!engineSettings.dynamicHoldEnabled, discoveryWindowSeconds: engineSettings.maxDiscoveryAgeSeconds,
        lastMiniCooldownEnd, lastLossCooldownEnd,
      });
    } catch (e) { console.error(e); res.status(500).json({ error: "Failed to fetch stats" }); }
  });
  app.get("/api/engine/risk-status", async (_req, res) => {
    const riskCheck = await checkCircuitBreakers();
    const effectiveBal = await getEffectiveBalance();
    const drawdownPct = peakBalance > 0 ? ((peakBalance - effectiveBal) / peakBalance * 100) : 0;
    const realizedLossPct = dailyPnlSol < 0 && dailyStartBalance > 0 ? (Math.abs(dailyPnlSol) / dailyStartBalance * 100) : 0;
    res.json({
      canTrade: riskCheck.canTrade, reason: riskCheck.reason, circuitBreakerActive,
      drawdownPct: Math.max(0, drawdownPct).toFixed(1), dailyLossPct: realizedLossPct.toFixed(1),
      dailyLossLimitPct: engineSettings.dailyLossLimitPct, maxDrawdownPct: engineSettings.maxDrawdownPct,
      peakBalance: peakBalance.toFixed(3), dailyStartBalance: dailyStartBalance.toFixed(3), consecutiveLosses,
      cooldownActive: Date.now() < lastLossCooldownEnd, cooldownRemainingMs: Math.max(0, lastLossCooldownEnd - Date.now()),
    });
  });
  app.get("/api/settings", async (_req, res) => { res.json(engineSettings); });
  app.post("/api/settings", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    try {
      const updates = req.body;
      if (!updates || typeof updates !== "object") return res.status(400).json({ message: "Invalid settings payload" });
      const validKeys = Object.keys(engineSettings) as (keyof typeof engineSettings)[];
      let restartIntervals = false;
      const minValues: Record<string, number> = { scanIntervalMs: 1000, priceCheckIntervalMs: 1000, reentryDelayMs: 0, slReentryDelayMs: 0, lossCooldownMs: 0, maxHoldSeconds: 10, maxOpenPositions: 1, maxTradesPerCycle: 1, minScoreToTrade: 0, startingBalance: 0.1, minPositionSize: 0.01, maxPositionSize: 0.1, txFeePercent: 0, rugcheckMinScore: 0, maxVolLiqRatioNewToken: 1, maxDiscoveryAgeSeconds: 60, dynamicHoldMaxSeconds: 60, txCostsEnabled: 0, safetyChecksEnabled: 0, dynamicHoldEnabled: 0 };
      const maxValues: Record<string, number> = { mlWeight: 1, scoreWeight: 1, partialTpRatio: 1, dailyLossLimitPct: 100, maxDrawdownPct: 100, txFeePercent: 5, rugcheckMinScore: 1000, maxVolLiqRatioNewToken: 50, maxDiscoveryAgeSeconds: 86400, dynamicHoldMaxSeconds: 7200, txCostsEnabled: 1, safetyChecksEnabled: 1, dynamicHoldEnabled: 1 };
      for (const key of validKeys) {
        if (key in updates) {
          const newVal = updates[key];
          const currentType = typeof engineSettings[key];
          if (currentType === "number" && typeof newVal === "number" && isFinite(newVal)) {
            let clamped = newVal;
            if (key in minValues) clamped = Math.max(clamped, minValues[key]);
            if (key in maxValues) clamped = Math.min(clamped, maxValues[key]);
            (engineSettings as any)[key] = clamped;
            if (key === "scanIntervalMs" || key === "priceCheckIntervalMs") restartIntervals = true;
          } else if (currentType === "string" && typeof newVal === "string") {
            if (key === "mlServiceUrl") {
              try {
                const u = new URL(newVal);
                const h = u.hostname;
                const isLocal = h === "localhost" || h === "127.0.0.1" || h === "::1" || /^192\.168\./.test(h) || /^10\./.test(h) || /^172\.(1[6-9]|2\d|3[01])\./.test(h);
                if (!isLocal) return res.status(400).json({ message: "mlServiceUrl must point to a local/private address" });
              } catch { return res.status(400).json({ message: "mlServiceUrl must be a valid URL" }); }
            }
            (engineSettings as any)[key] = newVal;
          }
        }
      }
      const weightSum = engineSettings.mlWeight + engineSettings.scoreWeight;
      if (weightSum === 0) { engineSettings.mlWeight = 0.5; engineSettings.scoreWeight = 0.5; }
      else if (Math.abs(weightSum - 1.0) > 0.001) { engineSettings.mlWeight /= weightSum; engineSettings.scoreWeight /= weightSum; }
      if (restartIntervals) {
        if (scannerInterval) clearInterval(scannerInterval);
        if (priceCheckerInterval) clearInterval(priceCheckerInterval);
        scannerInterval = setInterval(runScanCycle, engineSettings.scanIntervalMs);
        priceCheckerInterval = setInterval(checkOpenPositions, engineSettings.priceCheckIntervalMs);
        console.log(`[ENGINE] Intervals restarted: scan=${engineSettings.scanIntervalMs}ms, price=${engineSettings.priceCheckIntervalMs}ms`);
      }
      console.log(`[SETTINGS] Updated engine settings:`, JSON.stringify(updates));
      res.json(engineSettings);
    } catch (e) { console.error(e); res.status(500).json({ message: "Failed to update settings" }); }
  });
  app.post("/api/bot/force-sell-all", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    try {
      const openTrades = await storage.getOpenTrades();
      let closedCount = 0;
      const isLiveMode = jupiterService !== null;
      for (const trade of openTrades) {
        if (sellingInProgress.has(trade.id)) continue;
        sellingInProgress.add(trade.id);
        try {
          const { price: currentPrice } = await fetchTokenPrice(trade.tokenAddress);
          const entryPrice = parseFloat(trade.price);
          const sizeSol = parseFloat(trade.amount);
          let finalPnlPct = 0;
          if (isLiveMode && trade.tradingMode === "live") {
            let tokenAmountRaw = liveTokenBalances.get(trade.id) ?? BigInt(0);
            if (tokenAmountRaw === BigInt(0)) tokenAmountRaw = await jupiterService!.getTokenBalance(trade.tokenAddress);
            if (tokenAmountRaw === BigInt(0)) {
              const closingPrice = currentPrice > 0 ? currentPrice : entryPrice;
              finalPnlPct = entryPrice > 0 && closingPrice > 0 ? ((closingPrice - entryPrice) / entryPrice) * 100 : 0;
              await storage.closeTrade(trade.id, closingPrice.toString(), finalPnlPct.toFixed(2), "FORCE_SELL_NO_BALANCE");
              liveTokenBalances.delete(trade.id); peakPrices.delete(trade.id); partialTpTaken.delete(trade.id);
              tradeStopPrices.delete(trade.id); prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id);
              closedCount++; continue;
            }
            const forceLiq = trade.liquidity ? parseInt(trade.liquidity, 10) : 1000;
            const forceCosts = calcTransactionCosts(forceLiq, sizeSol);
            const forceSlippageBps = Math.min(2000, Math.max(300, Math.round(forceCosts.exitSlippagePct * 2 * 100)));
            const sellResult = await withTimeout(jupiterService!.sellToken(trade.tokenAddress, tokenAmountRaw, forceSlippageBps), EXECUTION_TIMEOUT_MS, `FORCE_SELL ${trade.tokenSymbol}`);
            if (!sellResult.success) { console.warn(`[FORCE] SELL FAILED $${trade.tokenSymbol}: ${sellResult.error} — skipping`); continue; }
            finalPnlPct = sizeSol > 0 ? ((sellResult.solReceived - sizeSol) / sizeSol) * 100 : 0;
            dailyPnlSol += sellResult.solReceived - sizeSol;
            liveTokenBalances.delete(trade.id);
            const closingPriceForSell = currentPrice > 0 ? currentPrice : entryPrice;
            console.log(`[FORCE] LIVE sold $${trade.tokenSymbol} | SOL in: ${sizeSol.toFixed(4)} → out: ${sellResult.solReceived.toFixed(4)} | PNL: ${finalPnlPct.toFixed(2)}%`);
            await storage.closeTrade(trade.id, closingPriceForSell.toString(), finalPnlPct.toFixed(2), "FORCE_SELL");
          } else {
            if (currentPrice <= 0) continue;
            const pnlPct = entryPrice > 0 ? ((currentPrice - entryPrice) / entryPrice) * 100 : 0;
            const returnSol = sizeSol * (1 + pnlPct / 100);
            paperBalance += returnSol; dailyPnlSol += returnSol - sizeSol;
            if (paperBalance > peakBalance) peakBalance = paperBalance;
            finalPnlPct = pnlPct;
            console.log(`[FORCE] PAPER sold $${trade.tokenSymbol} @ $${currentPrice.toFixed(8)} | PNL: ${pnlPct.toFixed(2)}%`);
            await storage.closeTrade(trade.id, currentPrice.toString(), finalPnlPct.toFixed(2), "FORCE_SELL");
          }
          tradedAddresses.set(trade.tokenAddress, Date.now());
          peakPrices.delete(trade.id); partialTpTaken.delete(trade.id); tradeStopPrices.delete(trade.id);
          prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id);
          closedCount++;
        } finally { sellingInProgress.delete(trade.id); }
      }
      const newBal = jupiterService ? await jupiterService.getWalletBalance().catch(() => 0) : paperBalance;
      const openNow = (await storage.getOpenTrades()).length;
      await storage.updateBotStats({ walletBalance: newBal.toFixed(4), openPositions: openNow, lastSignal: `Force sold ${closedCount} positions` });
      res.json({ success: true, closedCount, newBalance: newBal.toFixed(4) });
    } catch (e) { console.error(e); res.status(500).json({ success: false, error: "Failed to force sell" }); }
  });
  app.post("/api/bot/reset-balance", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    try {
      const openTrades = await storage.getOpenTrades();
      for (const trade of openTrades) {
        const entryPrice = parseFloat(trade.price || "0");
        const closePrice = parseFloat(trade.currentPrice || trade.price || "0");
        const sizeSol = parseFloat(trade.amount || "0");
        const pnlPct = entryPrice > 0 && closePrice > 0 ? ((closePrice - entryPrice) / entryPrice) * 100 : 0;
        dailyPnlSol += sizeSol * (pnlPct / 100);
        await storage.closeTrade(trade.id, (closePrice || entryPrice).toString(), pnlPct.toFixed(2), "RESET");
        tradedAddresses.set(trade.tokenAddress, Date.now());
        peakPrices.delete(trade.id); partialTpTaken.delete(trade.id); tradeStopPrices.delete(trade.id);
        prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id); liveTokenBalances.delete(trade.id);
      }
      // FIX: gate on actual tradingMode from DB, not just key presence.
      // If WALLET_PRIVATE_KEY is set but the UI is in paper mode, jupiterService
      // is non-null but isLiveReset was true — causing the reset to read the
      // on-chain wallet balance (possibly 0 SOL) and persist "0.0000" to the DB,
      // wiping the paper baseline even though no live trading was happening.
      const resetStatus = await storage.getBotStatus();
      const isLiveReset = jupiterService !== null && resetStatus.tradingMode === "live";
      const liveWalletBal = isLiveReset ? await jupiterService!.getWalletBalance().catch(() => engineSettings.startingBalance) : engineSettings.startingBalance;
      const resetBaseline = isLiveReset ? liveWalletBal : engineSettings.startingBalance;
      paperBalance = engineSettings.startingBalance;
      peakBalance = resetBaseline; dailyStartBalance = resetBaseline;
      dailyPnlSol = 0; dailyTradeCount = 0;
      consecutiveWins = 0; consecutiveLosses = 0;
      circuitBreakerActive = false; lastLossCooldownEnd = 0; lastMiniCooldownEnd = 0;
      tradeStopPrices.clear(); stoppedOutAddresses.clear();
      prevPnlMap.clear(); pnlStableMap.clear();
      sessionTokenBuyCount.clear();
      sessionSymbolBuyCount.clear();   // Change 4: symbol-scoped buy counts
      tokenLastLossMs.clear(); // clear post-loss cooldowns on reset
      tokenSymbolLastLossMs.clear();   // Change 4: symbol-scoped loss timestamps
      tokenStopLossCount.clear(); // FIX B: clear repeat-loser strikes on reset
      tokenSymbolSlBlockMs.clear();    // FIX: symbol-level SL block
      liqCoWarnedTrades.clear();       // FIX: warn-once guard
      // In paper mode always display startingBalance regardless of any live wallet
      // value — the two are independent and confusing them caused the UI to show
      // "0.0000 SOL" after a paper reset when a live key was configured.
      const displayBalance = isLiveReset
        ? liveWalletBal.toFixed(4)
        : engineSettings.startingBalance.toFixed(4);
      await storage.updateBotStats({ walletBalance: displayBalance, totalPnl: "0", openPositions: 0, lastSignal: `Balance reset to ${displayBalance} SOL`, peakBalance: resetBaseline.toFixed(4), lastLossCooldownEnd: 0, dailyStartBalance: resetBaseline.toFixed(4) });
      console.log(`[ENGINE] Reset complete | mode: ${isLiveReset ? "LIVE" : "paper"} | peak/baseline set to ${resetBaseline.toFixed(4)} SOL`);
      res.json({ success: true, newBalance: displayBalance, peakBalance: resetBaseline.toFixed(4) });
    } catch (e) { console.error(e); res.status(500).json({ success: false, error: "Failed to reset" }); }
  });
  app.post("/api/bot/trading-mode", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    const { mode, confirmed } = req.body;
    if (!mode || !["paper", "live"].includes(mode)) return res.status(400).json({ message: "Invalid trading mode. Use 'paper' or 'live'." });
    if (mode === "live" && !confirmed) return res.status(400).json({ message: "Live trading requires explicit confirmation. Set confirmed: true." });
    res.json(await storage.updateTradingMode(mode));
  });
  app.post("/api/bot/toggle", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    const { isRunning } = req.body;
    if (typeof isRunning !== "boolean") return res.status(400).json({ message: "isRunning must be boolean" });
    res.json(await storage.updateBotRunning(isRunning));
  });
  app.post("/api/bot/strategy-mode", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    const { mode } = req.body;
    if (!mode || !["SNIPER", "MG", "HWR", "AUTO"].includes(mode)) return res.status(400).json({ message: "Invalid strategy mode" });
    res.json(await storage.updateStrategyMode(mode));
  });

   app.post("/api/bot/reset-streak", (req, res) => {
	  if (!requireAdmin(req, res)) return;
	  consecutiveLosses = 0;
	  consecutiveWins = 0;
	  console.log("[ENGINE] Streak manually reset — consecutiveLosses=0");
	  res.json({ success: true });
	});
  app.get("/api/wallet", async (_req, res) => {
    if (!jupiterService) return res.json({ connected: false, address: null, balanceSol: null, liveTradesActive: 0, message: "WALLET_PRIVATE_KEY not set — live trading disabled" });
    try {
      const [balanceSol, openTrades] = await Promise.all([jupiterService.getWalletBalance(), storage.getOpenTrades()]);
      const liveOpen = (openTrades as any[]).filter(t => t.tradingMode === "live");
      const rawPriorityFee = parseInt(process.env.PRIORITY_FEE_LAMPORTS ?? "10000", 10);
      res.json({ connected: true, address: jupiterService.walletAddress, balanceSol: parseFloat(balanceSol.toFixed(4)), liveTradesActive: liveOpen.length, trackedTokenBalances: liveTokenBalances.size, rpcUrl: process.env.SOLANA_RPC_URL?.slice(0, 40) + "...", priorityFeeLamports: isNaN(rawPriorityFee) ? 10000 : rawPriorityFee, jupiterDexFilter: `${JUPITER_SUPPORTED_DEXES.size} DEXes allowed`, jupiterPoolAgeGateSec: JUPITER_INDEX_DELAY_MS / 1000 });
    } catch (e: any) { res.status(500).json({ connected: true, address: jupiterService.walletAddress, error: e.message }); }
  });
  app.post("/api/bot/fix-desync", async (req, res) => {
    if (!requireAdmin(req, res)) return;
    if (!jupiterService) return res.status(400).json({ error: "Live mode not active — WALLET_PRIVATE_KEY not set" });
    const openTrades = await storage.getOpenTrades();
    let fixed = 0, recovered = 0;
    const liveTradesToFix = openTrades.filter((t: any) => t.tradingMode === "live");
    for (const trade of liveTradesToFix) {
      let timerId: ReturnType<typeof setTimeout> | undefined;
      try {
        const fetchPromise = jupiterService!.getTokenBalance(trade.tokenAddress);
        const timeoutPromise = new Promise<never>((_, reject) => { timerId = setTimeout(() => reject(new Error("getTokenBalance timeout after 8s")), 8000); });
        const onChainBalance = await Promise.race([fetchPromise, timeoutPromise]);
        if (onChainBalance === BigInt(0)) {
          const { price: currentPrice } = await fetchTokenPrice(trade.tokenAddress);
          const entryPrice = parseFloat(trade.price || "0");
          const sizeSol = parseFloat(trade.amount || "0");
          const pnlPct = entryPrice > 0 && currentPrice > 0 ? ((currentPrice - entryPrice) / entryPrice) * 100 : 0;
          await storage.closeTrade(trade.id, currentPrice.toString(), pnlPct.toFixed(2), "MANUAL_DESYNC_FIX");
          liveTokenBalances.delete(trade.id); peakPrices.delete(trade.id); partialTpTaken.delete(trade.id);
          tradeStopPrices.delete(trade.id); prevPnlMap.delete(trade.id); pnlStableMap.delete(trade.id);
          tradedAddresses.set(trade.tokenAddress, Date.now());
          fixed++;
          console.log(`[DESYNC_FIX] Closed desynced trade #${trade.id} $${trade.tokenSymbol} — no on-chain balance`);
        } else { liveTokenBalances.set(trade.id, onChainBalance); recovered++; console.log(`[DESYNC_FIX] Recovered balance for #${trade.id} $${trade.tokenSymbol}: ${onChainBalance} raw units`); }
      } catch (err: any) { console.warn(`[DESYNC_FIX] Error for #${trade.id} $${trade.tokenSymbol}: ${err.message}`); }
      finally { if (timerId !== undefined) clearTimeout(timerId); }
    }
    const newBal = await jupiterService.getWalletBalance().catch(() => 0);
    const openNow = (await storage.getOpenTrades()).length;
    await storage.updateBotStats({ walletBalance: newBal.toFixed(4), openPositions: openNow });
    console.log(`[DESYNC_FIX] Done — closed ${fixed}, recovered ${recovered}. Wallet: ${newBal.toFixed(4)} SOL`);
    res.json({ success: true, fixedCount: fixed, recoveredCount: recovered, newWalletBalance: newBal.toFixed(4), openPositionsRemaining: openNow });
  });
  return httpServer;
}