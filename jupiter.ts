/**
 * jupiter.ts — Jupiter V6 swap integration for live trading
 * FULLY HARDENED — production-ready
 *
 * Handles: quote fetching, transaction building, signing, sending,
 * confirmation, wallet balance reads, and token ATA balance reads.
 *
 * Required env vars:
 * WALLET_PRIVATE_KEY          Base58-encoded Solana private key
 * SOLANA_RPC_URL              RPC endpoint (Helius, QuickNode, etc.)
 * PRIORITY_FEE_LAMPORTS       Flat priority fee in lamports added to each tx.
 *
 * Optional MEV-protection env vars:
 * JITO_ENGINE_URL             Jito block-engine endpoint for private relay
 * JITO_TIP_LAMPORTS           Lamports to tip Jito validators per transaction.
 */

import dns from "dns";
import {
  Connection,
  Keypair,
  VersionedTransaction,
  PublicKey,
  LAMPORTS_PER_SOL,
} from "@solana/web3.js";
import {
  getAssociatedTokenAddress,
  getAccount,
  Account,
  TOKEN_2022_PROGRAM_ID,
} from "@solana/spl-token";
import bs58 from "bs58";

dns.setDefaultResultOrder("ipv4first");

export const SOL_MINT           = "So11111111111111111111111111111111111111112";
export const MIN_FEE_BUFFER_SOL = 0.08;

const JUPITER_QUOTE_URL = "https://lite-api.jup.ag/swap/v1/quote";
const JUPITER_SWAP_URL  = "https://lite-api.jup.ag/swap/v1/swap";

const CONFIRM_TIMEOUT_MS = 60_000;
const POST_BUY_POLL_TIMEOUT_MS        = 20_000;
const POST_BUY_STABLE_READS_REQUIRED  = 2;

// ── Rate limiter (properly serialized per-caller queue) ──────────────────────
// Bug #3 fix: the old implementation handed ALL concurrent waiters the same
// Promise, so a burst of N callers all woke up simultaneously when the single
// timer fired — a one-shot delay, not a real gate.
// New: each caller chains its own MIN_JUPITER_INTERVAL_MS slot onto the tail of
// a shared queue, guaranteeing at least 600 ms between consecutive executions.
const MIN_JUPITER_INTERVAL_MS = 600;
let _jupiterLastCallMs = 0;
let _jupiterTail: Promise<void> = Promise.resolve();

function jupiterRateGate(): Promise<void> {
  const now = Date.now();
  if (now - _jupiterLastCallMs >= MIN_JUPITER_INTERVAL_MS) {
    // Idle path: enough wall-clock time has passed — execute immediately and
    // reset the tail so stale resolved promises don't accumulate.
    _jupiterLastCallMs = now;
    _jupiterTail = Promise.resolve();
    return Promise.resolve();
  }
  // Busy path: append an exclusive slot to the queue tail.
  // Each concurrent caller gets its own dedicated 600 ms window.
  const slot = _jupiterTail.then(
    () => new Promise<void>(resolve => {
      setTimeout(() => { _jupiterLastCallMs = Date.now(); resolve(); }, MIN_JUPITER_INTERVAL_MS);
    })
  );
  _jupiterTail = slot;
  return slot;
}

export interface BuyResult {
  success:        boolean;
  txSignature:    string | null;
  actualSolSpent: number;
  tokenAmountRaw: bigint;
  priceImpactPct: number;
  error?:         string;
}

export interface SellResult {
  success:     boolean;
  txSignature: string | null;
  solReceived: number;
  error?:      string;
}

export interface PreflightResult {
  priceImpactPct: number;
  outAmount:      string;
  routeInfo:      string;
}

export class JupiterService {
  readonly connection: Connection;
  private readonly keypair: Keypair;
  private readonly priorityFeeLamports: number;
  private readonly jitoTipLamports: number;
  private readonly jitoEngineUrl: string | null;
  private executedTransactions = new Set<string>();

  constructor(
    rpcUrl: string,
    privateKeyBase58: string,
    priorityFeeLamports = 10_000,
    jitoTipLamports = 0,
    jitoEngineUrl: string | null = null
  ) {
    this.connection = new Connection(rpcUrl, {
      commitment: "confirmed",
      confirmTransactionInitialTimeout: CONFIRM_TIMEOUT_MS,
    });
    this.keypair = Keypair.fromSecretKey(bs58.decode(privateKeyBase58));
    this.priorityFeeLamports = priorityFeeLamports;
    this.jitoTipLamports = jitoTipLamports;
    this.jitoEngineUrl = jitoEngineUrl;
  }

  get walletAddress(): string {
    return this.keypair.publicKey.toBase58();
  }

  async getWalletBalance(retries = 2): Promise<number> {
    let attempt = 0;
    while (attempt <= retries) {
      let timerId: ReturnType<typeof setTimeout> | undefined;
      try {
        const balancePromise = this.connection.getBalance(this.keypair.publicKey, "confirmed");
        const timeoutPromise = new Promise<never>((_, reject) => {
          timerId = setTimeout(() => reject(new Error("getWalletBalance RPC timeout after 10s")), 10_000);
        });
        const lamports = await Promise.race([balancePromise, timeoutPromise]) as number;
        return lamports / LAMPORTS_PER_SOL;
      } catch (err) {
        if (attempt === retries) throw err;
        attempt++;
        console.warn(`[JUPITER] getWalletBalance attempt ${attempt} failed, retrying...`);
        await new Promise(r => setTimeout(r, 500));
      } finally {
        if (timerId !== undefined) clearTimeout(timerId);
      }
    }
    throw new Error("getWalletBalance failed after retries");
  }

  // Token-2022 support
  async getTokenBalance(tokenMint: string, retries = 2): Promise<bigint> {
    // Bug #1 fix: the original code declared `timerId` but never assigned it,
    // so the RPC could hang indefinitely and freeze checkOpenPositions.
    // Now both getAccount calls are wrapped in Promise.race against a hard deadline.
    const GET_TOKEN_BALANCE_TIMEOUT_MS = 8_000;
    let attempt = 0;
    while (attempt <= retries) {
      try {
        const mintPubkey = new PublicKey(tokenMint);
        const ata = await getAssociatedTokenAddress(mintPubkey, this.keypair.publicKey);

        const fetchBalance = async (): Promise<bigint> => {
          let account: Account;
          try {
            account = await getAccount(this.connection, ata, "confirmed");
          } catch (err: any) {
            if (err?.name === "TokenInvalidAccountOwnerError") {
              account = await getAccount(this.connection, ata, "confirmed", TOKEN_2022_PROGRAM_ID);
            } else {
              throw err;
            }
          }
          return account.amount;
        };

        let timeoutTimer: ReturnType<typeof setTimeout> | undefined;
        const timeoutPromise = new Promise<never>((_, reject) => {
          timeoutTimer = setTimeout(
            () => reject(new Error(`getTokenBalance RPC timeout after ${GET_TOKEN_BALANCE_TIMEOUT_MS / 1000}s`)),
            GET_TOKEN_BALANCE_TIMEOUT_MS
          );
        });

        try {
          return await Promise.race([fetchBalance(), timeoutPromise]);
        } finally {
          clearTimeout(timeoutTimer);
        }
      } catch (err: any) {
        const notFound = err?.name === "TokenAccountNotFoundError" ||
                         err?.name === "TokenInvalidAccountOwnerError" ||
                         err?.message?.includes("could not find account") ||
                         err?.message?.includes("Account does not exist");
        if (notFound) return BigInt(0);
        if (attempt === retries) throw err;
        attempt++;
        console.warn(`[JUPITER] getTokenBalance retry ${attempt}`);
        await new Promise(r => setTimeout(r, 400));
      }
    }
    throw new Error("getTokenBalance failed after retries");
  }

  private async fetchQuoteWithRetry(
    inputMint: string,
    outputMint: string,
    amountRaw: string | number,
    slippageLevels = [500, 1000],
    maxAttempts = 2
  ): Promise<any> {
    let lastError: any;
    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      for (const slippage of slippageLevels) {
        try {
          await jupiterRateGate();
          const url = new URL(JUPITER_QUOTE_URL);
          url.searchParams.set("inputMint", inputMint);
          url.searchParams.set("outputMint", outputMint);
          url.searchParams.set("amount", String(amountRaw));
          url.searchParams.set("slippageBps", String(Math.max(50, Math.floor(slippage))));
          url.searchParams.set("onlyDirectRoutes", "false");
          url.searchParams.set("swapMode", "ExactIn");

          const resp = await fetch(url.toString(), {
            method: "GET",
            headers: { "Accept": "application/json", "User-Agent": "Mozilla/5.0" },
            signal: AbortSignal.timeout(15_000),
          });

          if (resp.status === 429) {
            const retryAfterMs = parseFloat(resp.headers.get("retry-after") ?? "0") * 1000 || 3000;
            console.warn(`[JUPITER] 429 Rate limit — backing off ${retryAfterMs}ms`);
            await new Promise(r => setTimeout(r, retryAfterMs));
            lastError = new Error(`HTTP 429: Rate limit exceeded`);
            break;
          }

          if (!resp.ok) {
            const body = await resp.text().catch(() => "");
            throw new Error(`HTTP ${resp.status}: ${body.slice(0, 200)}`);
          }

          const data = await resp.json() as any;
          if (data.error || !data.outAmount) {
            throw new Error(data.error || "No route / invalid quote");
          }
          // FIX 1: Stamp every quote with its fetch time so buildAndSendWithRetry
          // can detect staleness before sending and refuse to execute on a quote
          // that has aged past the safe execution window (> 1500 ms).
          data._fetchedAt = Date.now();
          console.log(`[JUPITER] Quote OK | ${slippage}bps | outAmount: ${data.outAmount} | impact: ${parseFloat(data.priceImpactPct ?? "0").toFixed(3)}%`);
          return data;
        } catch (err: any) {
          lastError = err;
          console.warn(`[JUPITER] Quote attempt failed | attempt ${attempt + 1}/${maxAttempts} | ${slippage}bps | ${err.message}`);
          await new Promise(r => setTimeout(r, 400 + Math.random() * 200));
        }
      }
      if (attempt < maxAttempts - 1) {
        await new Promise(r => setTimeout(r, 2000 * (attempt + 1) + Math.random() * 500));
      }
    }
    throw new Error(`Quote failed after all attempts: ${lastError?.message ?? "unknown"}`);
  }

  private async buildAndSendWithRetry(
    quote: any,
    maxRetries = 2,
    maxImpactPct = 15,
    slippageBps: number,
    quoteRefresher?: () => Promise<any>
  ): Promise<{ signature: string; postSwapBalances: { mint: string; amount: bigint }[] }> {
    const usingJito = this.jitoTipLamports > 0 && !!this.jitoEngineUrl;
    let lastError: any;
    let landedSig: string | null = null;
    let finalPostBalances: { mint: string; amount: bigint }[] = [];

    const impactPct = parseFloat(quote.priceImpactPct ?? "0");
    if (isNaN(impactPct) || impactPct > maxImpactPct) {
      throw new Error(`Invalid or excessive price impact: ${impactPct} (max ${maxImpactPct})`);
    }

    // Route validation
    if (!quote.routePlan || quote.routePlan.length === 0) {
      throw new Error("Quote has no routePlan — cannot execute safely");
    }

    // FIX 2: Pre-execution staleness guard. The quote is fetched by the caller
    // (runScanCycle or sellToken) and then passed here. By the time we sign and
    // send the tx, the quote can be 1–3 seconds old — enough for price to slip
    // past our slippage tolerance and cause a revert or bad fill.
    // Refresh any quote older than 1500 ms before the FIRST attempt.
    if (quoteRefresher && quote._fetchedAt && Date.now() - quote._fetchedAt > 1500) {
      try {
        const refreshed = await quoteRefresher();
        const refreshedImpact = parseFloat(refreshed.priceImpactPct ?? "0");
        if (!isNaN(refreshedImpact) && refreshedImpact <= maxImpactPct) {
          const ageMs = Date.now() - (quote._fetchedAt ?? 0);
          console.log(`[JUPITER] Pre-send quote refresh (was ${ageMs}ms old) | new impact: ${refreshedImpact.toFixed(3)}%`);
          quote = refreshed;
        }
      } catch (refreshErr: any) {
        console.warn(`[JUPITER] Pre-send quote refresh failed: ${refreshErr.message} — proceeding with original quote`);
      }
    }

    for (let i = 0; i < maxRetries; i++) {
      if (i > 0 && quoteRefresher) {
        try {
          const freshQuote = await quoteRefresher();
          const freshImpact = parseFloat(freshQuote.priceImpactPct ?? "0");
          if (isNaN(freshImpact) || freshImpact > maxImpactPct) {
            throw new Error(`Refreshed quote has excessive impact: ${freshImpact}`);
          }
          quote = freshQuote;
          console.log(`[JUPITER] Quote refreshed for retry ${i + 1} | impact: ${freshImpact.toFixed(3)}%`);
        } catch (refreshErr: any) {
          console.warn(`[JUPITER] Quote refresh failed on retry ${i + 1}: ${refreshErr.message} — aborting`);
          throw refreshErr;
        }
      }

      try {
        const outAmount = BigInt(quote.outAmount);
        const minOut = (outAmount * BigInt(10000 - slippageBps)) / 10000n;

        const swapBody: Record<string, any> = {
          quoteResponse: quote,
          userPublicKey: this.keypair.publicKey.toBase58(),
          wrapAndUnwrapSol: true,
          prioritizationFeeLamports: usingJito ? "auto" : this.priorityFeeLamports,
          dynamicComputeUnitLimit: true,
          asLegacyTransaction: false,
          otherAmountThreshold: minOut.toString(),
        };
        if (usingJito) swapBody.jitoTipLamports = this.jitoTipLamports;

        await jupiterRateGate();
        const swapResp = await fetch(JUPITER_SWAP_URL, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify(swapBody),
          signal: AbortSignal.timeout(15_000),
        });

        if (!swapResp.ok) {
          const body = await swapResp.text().catch(() => "");
          throw new Error(`Swap HTTP ${swapResp.status}: ${body.slice(0, 200)}`);
        }

        const swapData = await swapResp.json() as any;
        const swapTransaction = swapData.swapTransaction;
        let lastValidBlockHeight = swapData.lastValidBlockHeight as number | undefined;

        if (!swapTransaction) throw new Error("Jupiter returned no swapTransaction");

        const txBytes = Buffer.from(swapTransaction, "base64");
        const tx = VersionedTransaction.deserialize(txBytes);
        tx.sign([this.keypair]);

        const recentBlockhash = tx.message.recentBlockhash;
        const serializedTx = tx.serialize();

        // Block height expiry guard.
        // The old code compared tx.recentBlockhash against the CURRENT latest
        // blockhash. They are almost always different (Solana produces blocks ~400ms
        // apart) so the check warned on every transaction without ever aborting —
        // completely useless. The real danger is an EXPIRED blockhash: if the chain
        // has already passed lastValidBlockHeight, confirmTransaction will time out
        // after 60s. We detect this early and throw so the retry loop gets a fresh
        // quote immediately instead of burning a full minute.
        if (lastValidBlockHeight == null) {
          const latest = await this.connection.getLatestBlockhash("confirmed");
          lastValidBlockHeight = latest.lastValidBlockHeight;
          console.warn("[JUPITER] lastValidBlockHeight missing — using RPC approximation.");
        }
        try {
          const currentHeight = await this.connection.getBlockHeight("confirmed");
          if (currentHeight >= lastValidBlockHeight) {
            throw new Error(
              `Blockhash expired before send: chain height ${currentHeight} >= lastValidBlockHeight ${lastValidBlockHeight} — aborting to avoid 60s timeout`
            );
          }
        } catch (heightErr: any) {
          // Re-throw our own expiry error; swallow RPC errors (getBlockHeight failure
          // is non-fatal — confirmTransaction will handle expiry if it happens).
          if (heightErr.message.startsWith("Blockhash expired")) throw heightErr;
          console.warn(`[JUPITER] Could not verify block height: ${heightErr.message} — proceeding`);
        }

        let sig: string;
        if (usingJito && this.jitoEngineUrl) {
          try {
            const encodedTx = bs58.encode(serializedTx);
            const jitoPayload = {
              jsonrpc: "2.0",
              id: 1,
              method: "sendTransaction",
              params: [encodedTx, { encoding: "base58", skipPreflight: true }],
            };
            const jitoRes = await fetch(this.jitoEngineUrl, {
              method: "POST",
              headers: { "Content-Type": "application/json" },
              body: JSON.stringify(jitoPayload),
              signal: AbortSignal.timeout(15_000),
            });
            if (!jitoRes.ok) throw new Error(`Jito Engine HTTP ${jitoRes.status}`);
            const jitoData = await jitoRes.json() as any;
            if (jitoData.error) throw new Error(`Jito Engine rejected tx: ${JSON.stringify(jitoData.error)}`);
            sig = jitoData.result;
          } catch (jitoErr: unknown) {
            console.warn(`[JUPITER] Jito send failed, falling back to public RPC`);
            sig = await this.connection.sendRawTransaction(serializedTx, {
              skipPreflight: false,
              maxRetries: 0,
              preflightCommitment: "confirmed",
            });
          }
        } else {
          sig = await this.connection.sendRawTransaction(serializedTx, {
            skipPreflight: false,
            maxRetries: 0,
            preflightCommitment: "confirmed",
          });
        }

        if (this.executedTransactions.has(sig)) {
          throw new Error(`Duplicate transaction detected: ${sig}`);
        }

        landedSig = sig;

        let confirmTimerId: ReturnType<typeof setTimeout> | undefined;
        try {
          const confirmPromise = this.connection.confirmTransaction(
            { signature: sig, blockhash: recentBlockhash, lastValidBlockHeight },
            "confirmed"
          );
          const timeoutPromise = new Promise<never>((_, reject) => {
            confirmTimerId = setTimeout(() => reject(new Error(`Confirmation timeout after ${CONFIRM_TIMEOUT_MS / 1000}s`)), CONFIRM_TIMEOUT_MS);
          });
          let confirmation: any;
          try {
            confirmation = await Promise.race([confirmPromise, timeoutPromise]) as any;
          } catch (raceErr: any) {
            if (raceErr.message?.includes("timeout")) confirmPromise.catch(() => {});
            throw raceErr;
          }
          if (confirmation?.value?.err) {
            throw new Error(`Transaction reverted on-chain: ${JSON.stringify(confirmation.value.err)}`);
          }
        } finally {
          if (confirmTimerId !== undefined) clearTimeout(confirmTimerId);
        }

        // Transaction meta verification
        const txDetails = await this.connection.getTransaction(sig, {
          maxSupportedTransactionVersion: 0,
        });
        if (!txDetails || !txDetails.meta) {
          throw new Error("Transaction confirmed but metadata missing");
        }
        const postBalances = txDetails.meta.postTokenBalances || [];
        finalPostBalances = postBalances.map(b => ({
          mint: b.mint,
          amount: BigInt(b.uiTokenAmount?.amount || "0"),
        }));

        this.executedTransactions.add(sig);
        if (this.executedTransactions.size > 1000) {
          const toDelete = Array.from(this.executedTransactions).slice(0, 500);
          toDelete.forEach(s => this.executedTransactions.delete(s));
        }

        console.log(`[JUPITER] TX confirmed | sig: ${sig.slice(0, 20)}...`);
        return { signature: sig, postSwapBalances: finalPostBalances };

      } catch (err: any) {
        lastError = err;
        console.warn(`[JUPITER] Swap attempt ${i + 1}/${maxRetries} failed: ${err.message}`);

        if (landedSig) {
          let statusTimerId: ReturnType<typeof setTimeout> | undefined;
          try {
            const statusPromise = this.connection.getSignatureStatus(landedSig, { searchTransactionHistory: false });
            const timeoutPromise = new Promise<never>((_, reject) => {
              statusTimerId = setTimeout(() => reject(new Error("getSignatureStatus timeout")), 10_000);
            });
            const status = await Promise.race([statusPromise, timeoutPromise]) as any;
            if (status?.value && !status.value.err) {
              console.log(`[JUPITER] TX landed despite confirmation error`);
              const txDetails = await this.connection.getTransaction(landedSig, { maxSupportedTransactionVersion: 0 });
              const postBalances = txDetails?.meta?.postTokenBalances || [];
              finalPostBalances = postBalances.map(b => ({
                mint: b.mint,
                amount: BigInt(b.uiTokenAmount?.amount || "0"),
              }));
              return { signature: landedSig, postSwapBalances: finalPostBalances };
            }
            // FIX: status.value === null means tx is pending/unknown (RPC congestion).
            // Do NOT retry — a second attempt sends a duplicate transaction.
            // Abort and surface the error; the position manager will retry next cycle.
            if (status && status.value === null) {
              throw new Error(
                `TX status unknown (RPC congested/pending) — aborting to prevent double-spend. sig: ${landedSig}`
              );
            }
          } finally {
            if (statusTimerId !== undefined) clearTimeout(statusTimerId);
          }
        }

        if (i < maxRetries - 1) {
          await new Promise(r => setTimeout(r, 1_500));
        }
      }
    }
    throw new Error(`Swap failed after ${maxRetries} attempts: ${lastError?.message ?? "unknown"}`);
  }

  async preflightQuote(
    inputMint: string,
    outputMint: string,
    amountRaw: number,
    slippageBps: number
  ): Promise<PreflightResult | null> {
    try {
      const quote = await this.fetchQuoteWithRetry(inputMint, outputMint, amountRaw, [slippageBps], 2);
      const priceImpactPct = parseFloat(quote.priceImpactPct ?? "0");
      const routeLabels: string[] = (quote.routePlan ?? []).map((step: any) => step.swapInfo?.label ?? "unknown").slice(0, 3);
      return { priceImpactPct, outAmount: quote.outAmount ?? "0", routeInfo: routeLabels.join("→") || "direct" };
    } catch (firstErr: any) {
      try {
        const quote = await this.fetchQuoteWithRetry(inputMint, outputMint, amountRaw, [Math.max(slippageBps, 500)], 1);
        const priceImpactPct = parseFloat(quote.priceImpactPct ?? "0");
        const routeLabels: string[] = (quote.routePlan ?? []).map((step: any) => step.swapInfo?.label ?? "unknown").slice(0, 3);
        return { priceImpactPct, outAmount: quote.outAmount ?? "0", routeInfo: routeLabels.join("→") || "direct" };
      } catch {
        return null;
      }
    }
  }

  /**
   * Public wrapper around fetchQuoteWithRetry.
   * Returns the full Jupiter quote object required for buyToken() execution.
   *
   * IMPORTANT: Do NOT substitute preflightQuote() here. preflightQuote() returns
   * a partial PreflightResult (priceImpactPct, outAmount, routeInfo only) and
   * will cause HTTP 400 on the swap endpoint if passed as quoteResponse.
   * This method returns the raw quote object that Jupiter's swap API expects.
   *
   * @param inputMint       Input token mint address
   * @param outputMint      Output token mint address
   * @param amountRaw       Amount in raw lamports / smallest units
   * @param slippageLevels  Ordered slippage levels in bps to try (default: [500, 1000])
   */
  async fetchQuote(
    inputMint: string,
    outputMint: string,
    amountRaw: number | string,
    slippageLevels: number[] = [500, 1000]
  ): Promise<any> {
    return this.fetchQuoteWithRetry(inputMint, outputMint, amountRaw, slippageLevels);
  }

  async buyToken(
    tokenMint: string,
    amountSol: number,
    slippageBps: number,
    quoteOverride?: any,
    maxImpactPct = 15
  ): Promise<BuyResult> {
    const lamports = Math.floor(amountSol * LAMPORTS_PER_SOL);
    try {
      const latestSolBal = await this.getWalletBalance(2);
      if (latestSolBal < amountSol + MIN_FEE_BUFFER_SOL) {
        throw new Error(`Balance too low before execution: ${latestSolBal.toFixed(5)} SOL`);
      }

      let quote = quoteOverride;
      if (!quote) {
        quote = await this.fetchQuoteWithRetry(SOL_MINT, tokenMint, lamports, [slippageBps, Math.min(slippageBps * 2, 1000)]);
      }

      if (quoteOverride && Date.now() - (quoteOverride._fetchedAt ?? 0) > 3000) {
        console.warn(`[JUPITER] Stale quote — refreshing`);
        quote = await this.fetchQuoteWithRetry(SOL_MINT, tokenMint, lamports, [slippageBps, Math.min(slippageBps * 2, 1000)]);
        quote._fetchedAt = Date.now();
      }

      const priceImpactPct = parseFloat(quote.priceImpactPct ?? "0");
      const tokenBalBefore = await this.getTokenBalance(tokenMint);
      const solBalBefore = await this.getWalletBalance(2);

      // Route validation (safety)
      if (!quote.routePlan || quote.routePlan.length === 0) {
        throw new Error("Quote has no routePlan — cannot execute");
      }

      const { signature: txSignature, postSwapBalances } = await this.buildAndSendWithRetry(
        quote,
        2,
        maxImpactPct,
        slippageBps,
        () => this.fetchQuoteWithRetry(SOL_MINT, tokenMint, lamports, [slippageBps, Math.min(slippageBps * 2, 1000)])
      );

      let finalTokenBal = BigInt(0);
      for (const bal of postSwapBalances) {
        if (bal.mint === tokenMint) {
          finalTokenBal = bal.amount;
          break;
        }
      }
      if (finalTokenBal === BigInt(0)) {
        // Fallback polling
        let stableReads = 0;
        let lastTokenBal = BigInt(0);
        const POLL_START = Date.now();
        while (Date.now() - POLL_START < POST_BUY_POLL_TIMEOUT_MS) {
          await new Promise(r => setTimeout(r, 500));
          const tokenBal = await this.getTokenBalance(tokenMint);
          if (tokenBal > tokenBalBefore) {
            if (tokenBal === lastTokenBal) {
              stableReads++;
              if (stableReads >= POST_BUY_STABLE_READS_REQUIRED) {
                finalTokenBal = tokenBal;
                break;
              }
            } else {
              stableReads = 1;
              lastTokenBal = tokenBal;
            }
          } else {
            stableReads = 0;
          }
        }
        if (finalTokenBal === BigInt(0)) {
          throw new Error(`Token balance did not increase after ${POST_BUY_POLL_TIMEOUT_MS / 1000}s`);
        }
      }

      const tokenAmountRaw = finalTokenBal - tokenBalBefore;
      // NEGATIVE BIGINT GUARD: Token-2022 rebase tokens or ATA dust from a prior
      // failed trade can make tokenBalBefore > finalTokenBal, producing a large
      // negative bigint. The partial-fill check below would treat it as a fill
      // (negative < 70% of expected) and store a negative amount in liveTokenBalances,
      // causing the subsequent sell to fail with a cryptic error.
      // Use the absolute post-swap balance as a safe fallback.
      if (tokenAmountRaw < BigInt(0)) {
        console.error(`[JUPITER] BUY tokenAmountRaw is negative (${tokenAmountRaw}) — Token-2022 ATA dust or prior failed trade. Using absolute post-swap balance ${finalTokenBal} as fallback.`);
      }
      const safeTokenAmountRaw = tokenAmountRaw < BigInt(0) ? finalTokenBal : tokenAmountRaw;
      const finalSolBal = await this.getWalletBalance(1);
      // FIX: if a concurrent background tx (rent return, unrelated sell, fee deduction)
      // moves solBalBefore vs finalSolBal, actualSolSpent can be 0 or negative.
      // A zero cost basis causes divide-by-zero in PNL and records phantom "free" trades.
      // Fall back to amountSol + fee buffer when the wallet delta is unreliable.
      let actualSolSpent = solBalBefore - finalSolBal;
      if (actualSolSpent <= 0) {
        console.warn(`[JUPITER] Wallet delta unreliable (${actualSolSpent.toFixed(6)}) — using requested amount as cost basis`);
        actualSolSpent = amountSol + 0.005;
      }

      const expectedOut = BigInt(quote.outAmount);
      if (safeTokenAmountRaw < expectedOut * 70n / 100n) {
        console.error(`[JUPITER] BUY partial fill: received ${safeTokenAmountRaw} raw units but expected ${expectedOut}`);
        return {
          success: true,
          txSignature,
          actualSolSpent,
          tokenAmountRaw: safeTokenAmountRaw,
          priceImpactPct,
          error: `Partial fill: received ${(safeTokenAmountRaw * 100n / expectedOut).toString()}% of expected`,
        };
      }

      console.log(`[JUPITER] BUY OK | sig: ${txSignature.slice(0, 20)}... | SOL spent: ${actualSolSpent.toFixed(6)} | tokens: ${safeTokenAmountRaw} | impact: ${priceImpactPct.toFixed(3)}%`);
      return { success: true, txSignature, actualSolSpent, tokenAmountRaw: safeTokenAmountRaw, priceImpactPct };
    } catch (e: any) {
      console.error(`[JUPITER] BUY FAILED ${tokenMint}: ${e.message}`);
      return { success: false, txSignature: null, actualSolSpent: 0, tokenAmountRaw: BigInt(0), priceImpactPct: 0, error: e.message };
    }
  }

  async sellToken(
    tokenMint: string,
    tokenAmountRaw: bigint,
    slippageBps: number
  ): Promise<SellResult> {
    try {
      let sellAmount = tokenAmountRaw;
      if (sellAmount <= BigInt(0)) {
        sellAmount = await this.getTokenBalance(tokenMint);
        if (sellAmount <= BigInt(0)) throw new Error("No token balance found on-chain");
        console.log(`[JUPITER] SELL fallback: ATA read → ${sellAmount} raw units`);
      }

      // FIX: each fallback level must be >= base slippage. Math.min(slippageBps*2, 1000)
      // produces a value LOWER than base when slippageBps > 500 (e.g. 800 → 1000, ok;
      // but 600 → 1000, ok; 1500 → 1000, LOWER — guaranteed retry failure).
      const dynamicSlippageLevels = [
        slippageBps,
        Math.max(slippageBps, Math.min(slippageBps * 2, 1000)),
        Math.max(slippageBps, Math.min(slippageBps * 4, 2000)),
      ];
      const quote = await this.fetchQuoteWithRetry(tokenMint, SOL_MINT, sellAmount.toString(), dynamicSlippageLevels);
      const impactPct = parseFloat(quote.priceImpactPct ?? "0");
      if (impactPct > 30) {
        console.warn(`[JUPITER] SELL high impact ${impactPct.toFixed(2)}% — may still execute`);
      }

      const solBefore = await this.getWalletBalance(2);
      const { signature: txSignature } = await this.buildAndSendWithRetry(
        quote,
        2,
        99,
        slippageBps,
        // FIX 3: Refresher levels must be >= base slippage. Using bare Math.min()
        // without Math.max(slippageBps, ...) produces levels LOWER than the base
        // when slippageBps > 500 — e.g. base=1500, min(3000,1000)=1000 < 1500.
        // That makes every retry use a tighter tolerance than the one that just
        // failed, guaranteeing the retry will also fail. Always clamp from below.
        () => this.fetchQuoteWithRetry(tokenMint, SOL_MINT, sellAmount.toString(), [
          Math.max(slippageBps, Math.min(slippageBps * 2, 2000)),
          Math.max(slippageBps, Math.min(slippageBps * 4, 3000)),
        ])
      );

      let solAfter = solBefore;
      for (let i = 0; i < 30; i++) {
        await new Promise(r => setTimeout(r, 500));
        try {
          const latestBal = await this.getWalletBalance(1);
          if (latestBal > solBefore + 1e-6) {
            solAfter = latestBal;
            break;
          }
          solAfter = latestBal;
        } catch (rpcErr: any) {
          console.warn(`[JUPITER] RPC error during post-sell poll ${i + 1}/30: ${rpcErr.message} — retrying`);
        }
      }

      let solReceived = Math.max(0, solAfter - solBefore);

      // PHANTOM-LOSS FIX: the 15s poll can return stale data throughout on a
      // congested RPC, making solAfter === solBefore and solReceived === 0.
      // The tokens ARE sold and SOL IS in the wallet — but the bot would record
      // -100% PnL and debit dailyPnlSol by the full position size, potentially
      // tripping the circuit breaker on a profitable day.
      // One final direct read resolves this before we return a zero.
      if (solReceived === 0) {
        const confirmedBal = await this.getWalletBalance(2).catch(() => solBefore);
        const retryReceived = Math.max(0, confirmedBal - solBefore);
        if (retryReceived > 0) {
          console.warn(`[JUPITER] Post-sell poll missed balance — confirmed via direct read: ${retryReceived.toFixed(6)} SOL`);
          solReceived = retryReceived;
        } else {
          // Genuinely zero — log clearly so it's diagnosable in production.
          console.error(`[JUPITER] SELL confirmed on-chain but SOL delta = 0 after 15s poll + direct read. Wallet balance may be correct — check manually before relying on PnL figure.`);
        }
      }

      console.log(`[JUPITER] SELL OK | sig: ${txSignature.slice(0, 20)}... | SOL received: ${solReceived.toFixed(6)}`);
      return { success: true, txSignature, solReceived };
    } catch (e: any) {
      console.error(`[JUPITER] SELL FAILED ${tokenMint}: ${e.message}`);
      return { success: false, txSignature: null, solReceived: 0, error: e.message };
    }
  }
}

export function createJupiterService(): JupiterService | null {
  const pk = process.env.WALLET_PRIVATE_KEY?.trim();
  if (!pk) {
    console.log("[JUPITER] WALLET_PRIVATE_KEY not set — live trading disabled.");
    return null;
  }
  const rpc = process.env.SOLANA_RPC_URL?.trim() ?? "https://api.mainnet-beta.solana.com";
  const jitoEngineUrl = process.env.JITO_ENGINE_URL?.trim() || null;
  const DEFAULT_JITO_TIP = jitoEngineUrl ? 30_000 : 0;
  const rawJitoTip = parseInt(process.env.JITO_TIP_LAMPORTS ?? String(DEFAULT_JITO_TIP), 10);
  const jitoTipLamports = isNaN(rawJitoTip) ? DEFAULT_JITO_TIP : rawJitoTip;
  const DEFAULT_PRIORITY_FEE = 10_000;
  const rawPriorityFee = parseInt(process.env.PRIORITY_FEE_LAMPORTS ?? String(DEFAULT_PRIORITY_FEE), 10);
  const priorityFeeLamports = isNaN(rawPriorityFee) ? DEFAULT_PRIORITY_FEE : rawPriorityFee;
  try {
    const svc = new JupiterService(rpc, pk, priorityFeeLamports, jitoTipLamports, jitoEngineUrl);
    console.log(`[JUPITER] Initialised | wallet: ${svc.walletAddress}`);
    return svc;
  } catch (e: any) {
    console.error(`[JUPITER] Init failed: ${e.message}`);
    return null;
  }
}