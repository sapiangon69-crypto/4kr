#!/usr/bin/env node
"use strict";

const fs = require("node:fs/promises");
const path = require("node:path");
const process = require("node:process");
const crypto = require("node:crypto");
const readline = require("node:readline/promises");
const { setTimeout: sleep } = require("node:timers/promises");

let puppeteer;
let StealthPlugin;
try {
  puppeteer = require("puppeteer-extra");
  StealthPlugin = require("puppeteer-extra-plugin-stealth");
  puppeteer.use(StealthPlugin());
} catch {
  try {
    puppeteer = require("puppeteer");
  } catch {
    puppeteer = null;
  }
}

const DEFAULT_CONFIG_FILE = "config.json";
const DEFAULT_ACCOUNTS_FILE = "accounts.json";
const DEFAULT_TOKENS_FILE = "tokens.json";
const DEFAULT_PROXY_FILE = "proxy.txt";

// Proxy support: per-account proxy mapping (account name -> proxy URL)
const proxyByAccount = new Map();

const rawBrowserChallengeConcurrency = Number(process.env.ROOTSFI_MAX_BROWSER_CONCURRENCY);
const BROWSER_CHALLENGE_MAX_CONCURRENT =
  Number.isFinite(rawBrowserChallengeConcurrency) && rawBrowserChallengeConcurrency > 0
    ? Math.floor(rawBrowserChallengeConcurrency)
    : 1;
const BROWSER_LAUNCH_TIMEOUT_MS = 120000;
const BROWSER_CHALLENGE_MAX_ATTEMPTS = 20;
const BROWSER_CHALLENGE_MAX_ATTEMPTS_ON_429 = 20;
const BROWSER_CHALLENGE_RETRY_ATTEMPTS_ON_429 = 10;
const BROWSER_CHALLENGE_RETRY_DELAY_MS = 15000;
const rawSessionReuseConcurrency = Number(process.env.ROOTSFI_MAX_SESSION_REUSE_CONCURRENCY);
let SESSION_REUSE_MAX_CONCURRENT =
  Number.isFinite(rawSessionReuseConcurrency) && rawSessionReuseConcurrency > 0
    ? Math.floor(rawSessionReuseConcurrency)
    : 1;
let activeBrowserChallenges = 0;
const browserChallengeWaitQueue = [];
let activeSessionReuseChallenges = 0;
const sessionReuseWaitQueue = [];
const cachedSecurityCookies = new Map();
let browserChallengeRateLimitedUntilMs = 0;

// Track all spawned Chromium PIDs so we can kill zombies
const trackedBrowserPids = new Set();

function trackBrowserPid(browser) {
  try {
    const proc = browser.process();
    if (proc && proc.pid) {
      trackedBrowserPids.add(proc.pid);
      return proc.pid;
    }
  } catch { }
  return null;
}

function untrackBrowserPid(pid) {
  if (pid) trackedBrowserPids.delete(pid);
}

function killZombieBrowsers() {
  for (const pid of trackedBrowserPids) {
    try {
      process.kill(pid, 0); // test if alive
      process.kill(pid, "SIGKILL");
      console.log(`[browser-cleanup] Killed zombie Chromium pid ${pid}`);
    } catch {
      // Process already dead — clean up tracking
    }
    trackedBrowserPids.delete(pid);
  }
}

// Run zombie cleanup every 2 minutes
setInterval(killZombieBrowsers, 120000).unref();

// Also clean up on exit
process.on("exit", killZombieBrowsers);

// ============================================================================
// CONNECTION POOL RESET FOR SOFT RESTART RECOVERY
// ============================================================================
// Node.js native fetch uses undici under the hood with a global connection pool.
// When timeouts happen repeatedly, the connection pool can get "stuck".
// This function resets the global dispatcher to force fresh connections.
// ============================================================================

let undiciAvailable = false;
let undiciModule = null;
let connectionPoolResetInFlight = null;
let lastConnectionPoolResetAt = 0;
const CONNECTION_POOL_RESET_MIN_INTERVAL_MS = 12000;

try {
  undiciModule = require("undici");
  undiciAvailable = true;
} catch {
  // undici not available as explicit dependency, will try global reset
}

/**
 * Reset the global fetch connection pool.
 * This helps recover from "stuck" connections that cause repeated timeouts.
 * After calling this, subsequent fetch requests will use fresh connections.
 */
async function resetConnectionPool(options = {}) {
  const forceReset = Boolean(options.forceReset);

  if (connectionPoolResetInFlight) {
    console.log("[connection] Reset already in progress, waiting for existing reset...");
    return connectionPoolResetInFlight;
  }

  const nowMs = Date.now();
  const sinceLastResetMs = nowMs - lastConnectionPoolResetAt;
  if (!forceReset && lastConnectionPoolResetAt > 0 && sinceLastResetMs < CONNECTION_POOL_RESET_MIN_INTERVAL_MS) {
    const remainingSeconds = Math.max(1, Math.ceil((CONNECTION_POOL_RESET_MIN_INTERVAL_MS - sinceLastResetMs) / 1000));
    console.log(`[connection] Reset skipped (throttled), retry window in ${remainingSeconds}s`);
    return true;
  }

  if (forceReset) {
    console.log("[connection] Force reset requested (bypass throttle)");
  }

  connectionPoolResetInFlight = (async () => {
    console.log("[connection] Attempting to reset connection pool...");

    try {
      if (undiciAvailable && undiciModule) {
        // Create a new Agent with fresh settings
        const newAgent = new undiciModule.Agent({
          keepAliveTimeout: 10000,  // 10 seconds
          keepAliveMaxTimeout: 30000,  // 30 seconds max
          connections: 100,
          pipelining: 1
        });
        undiciModule.setGlobalDispatcher(newAgent);
        lastConnectionPoolResetAt = Date.now();
        console.log("[connection] Connection pool reset via undici.setGlobalDispatcher()");
        return true;
      }

      // Fallback: try to access undici through global symbol (Node.js 18+)
      const dispatcherSymbol = Symbol.for("undici.globalDispatcher.1");
      if (globalThis[dispatcherSymbol]) {
        // Close existing connections
        try {
          const currentDispatcher = globalThis[dispatcherSymbol];
          if (typeof currentDispatcher.close === "function") {
            await currentDispatcher.close();
            console.log("[connection] Closed existing dispatcher connections");
          }
        } catch (closeErr) {
          const closeMessage = String(closeErr && closeErr.message ? closeErr.message : closeErr || "");
          if (closeMessage.toLowerCase().includes("destroyed")) {
            console.log("[connection] Dispatcher already destroyed, continuing with fresh reset");
          } else {
            console.log(`[connection] Could not close dispatcher: ${closeMessage}`);
          }
        }

        // Force garbage collection if available (Node.js with --expose-gc)
        if (typeof global.gc === "function") {
          global.gc();
          console.log("[connection] Forced garbage collection");
        }

        lastConnectionPoolResetAt = Date.now();
        console.log("[connection] Connection pool soft reset completed");
        return true;
      }

      console.log("[connection] No undici dispatcher found, connection pool not reset");
      return false;
    } catch (error) {
      console.log(`[connection] Failed to reset connection pool: ${error.message}`);
      return false;
    }
  })();

  try {
    return await connectionPoolResetInFlight;
  } finally {
    connectionPoolResetInFlight = null;
  }
}

// ============================================================================
// AUTO-FILL ETH BASE
// ============================================================================
// Monitors ETH balance on Base chain for each RootsFi account.
// When balance drops below ETH_REFILL_THRESHOLD (0.0001 ETH), automatically
// sends ETH_REFILL_AMOUNT (0.00044 ETH) from the master wallet configured
// in accounts.json (masterWalletPrivateKey field).
// ETH addresses are auto-fetched from the RootsFi API (wallets.ethAddress).
// ============================================================================

let ethAutoFillProvider = null;
let ethAutoFillWallet = null;
let ethAutoFillEnabled = false;
const ethAddressByAccount = new Map();
const ethRefillInFlight = new Map();
const ETH_REFILL_THRESHOLD = 0.0001;
const ETH_REFILL_AMOUNT = "0.00044";
const BASE_CHAIN_ID = 8453;
const BASE_RPC_URL = "https://mainnet.base.org";

function initEthAutoFill(privateKey) {
  if (!privateKey || privateKey === "ISI_PRIVATE_KEY_MASTER_WALLET_DISINI") {
    console.log("[eth-fill] Master wallet not configured in accounts.json — auto-fill disabled");
    ethAutoFillEnabled = false;
    return;
  }
  try {
    const { ethers } = require("ethers");
    ethAutoFillProvider = new ethers.JsonRpcProvider(BASE_RPC_URL, BASE_CHAIN_ID);
    ethAutoFillWallet = new ethers.Wallet(privateKey, ethAutoFillProvider);
    ethAutoFillEnabled = true;
    console.log(`[eth-fill] ✓ Master wallet: ${ethAutoFillWallet.address}`);
    console.log(`[eth-fill]   Threshold: <${ETH_REFILL_THRESHOLD} ETH → refill ${ETH_REFILL_AMOUNT} ETH`);
    console.log(`[eth-fill]   Chain: Base (${BASE_CHAIN_ID}) via ${BASE_RPC_URL}`);
    ethAutoFillProvider.getBalance(ethAutoFillWallet.address).then(balance => {
      const balEth = Number(ethers.formatEther(balance));
      console.log(`[eth-fill]   Master balance: ${balEth.toFixed(6)} ETH`);
      if (balEth < 0.001) {
        console.log("[eth-fill]   ⚠ Master wallet balance low!");
      }
    }).catch(err => {
      console.log(`[eth-fill]   Could not check master balance: ${err.message}`);
    });
  } catch (error) {
    console.log(`[eth-fill] Failed to initialize: ${error.message}`);
    ethAutoFillEnabled = false;
  }
}

function cacheEthAddress(accountName, balanceData) {
  if (!accountName || !isObject(balanceData)) return null;
  const wallets = isObject(balanceData.wallets) ? balanceData.wallets : {};
  const ethAddr = String(wallets.ethAddress || "").trim();
  if (ethAddr && ethAddr.startsWith("0x") && ethAddr.length === 42) {
    ethAddressByAccount.set(accountName, ethAddr);
    return ethAddr;
  }
  return ethAddressByAccount.get(accountName) || null;
}

function maybeRefillEth(accountName, balanceData) {
  if (!ethAutoFillEnabled || !ethAutoFillWallet) return;
  const name = String(accountName || "").trim();
  if (!name) return;

  const ethBalance = otcGetAccountBalance("ETH", balanceData);
  const ethAddress = cacheEthAddress(name, balanceData);

  if (!ethAddress) return;
  if (ethBalance >= ETH_REFILL_THRESHOLD) return;
  if (ethRefillInFlight.has(name)) return;

  console.log(`[eth-fill] ${name}: ETH ${ethBalance.toFixed(6)} < ${ETH_REFILL_THRESHOLD} → refilling ${ETH_REFILL_AMOUNT} ETH to ${ethAddress}`);

  const refillPromise = (async () => {
    try {
      const { ethers } = require("ethers");
      const tx = await ethAutoFillWallet.sendTransaction({
        to: ethAddress,
        value: ethers.parseEther(ETH_REFILL_AMOUNT),
      });
      console.log(`[eth-fill] ${name}: TX sent ${tx.hash}`);
      const receipt = await tx.wait(1);
      console.log(`[eth-fill] ${name}: ✓ Refilled ${ETH_REFILL_AMOUNT} ETH (block ${receipt.blockNumber})`);
    } catch (error) {
      console.log(`[eth-fill] ${name}: ✗ Refill failed: ${error.message}`);
    } finally {
      ethRefillInFlight.delete(name);
    }
  })();

  ethRefillInFlight.set(name, refillPromise);
}

// ============================================================================
// ADAPTIVE INTERNAL RECIPIENT STRATEGY
// ============================================================================
// Goals:
// - Recipient tidak monoton (rotating offset per round)
// - Hindari kirim balik langsung ke sender sebelumnya (server cooldown 10m)
// - Tetap support fallback recipient saat candidate utama cooldown
// ============================================================================

const SEND_PAIR_COOLDOWN_MS = 20 * 60 * 1000; // 20 minutes (server rule)
const SEND_PAIR_COOLDOWN_BUFFER_SECONDS = 5; // Small safety buffer (send-back allowed after 20 min)

// Per-account TX cooldown is now driven by config.send.minDelayTxSeconds /
// maxDelayTxSeconds (humanLikeDelay between TXs). Small safety buffer remains.
const PER_ACCOUNT_TX_COOLDOWN_BUFFER_MS = 5 * 1000;
// key: accountName, value: timestamp (ms) of last successful send
const lastTxTimestampByAccount = new Map();
// key: accountName, value: number[] (timestamps ms of last successful sends, last hour)
const txTimestampsByAccount = new Map();
// Adaptive hourly cap — learned from server behavior (HTTP 400 = hourly limit).
// Starts with safe default. Auto-lowers when server rejects, auto-probes up over time.
const HOURLY_TX_WINDOW_MS = 60 * 60 * 1000;
const HOURLY_TX_BUFFER_MS = 30 * 1000;
const ADAPTIVE_HOURLY_DEFAULT = 10;     // Starting safe guess
const ADAPTIVE_HOURLY_MIN = 3;          // Never guess below 3/hr
const ADAPTIVE_HOURLY_MAX = 50;         // Never guess above 50/hr
let HOURLY_MAX_TX_PER_ACCOUNT = ADAPTIVE_HOURLY_DEFAULT;
let hourlyCapSource = "default";        // "default" | "server" | "config"
let lastServerCapLearnedAt = 0;         // Timestamp of last 400-based learning
const ADAPTIVE_PROBE_INTERVAL_MS = 3 * 60 * 60 * 1000; // Try +1 every 3 hours

function setHourlyMaxTx(value) {
  const n = clampToNonNegativeInt(value, 0);
  if (n > 0) {
    // Explicit config override
    HOURLY_MAX_TX_PER_ACCOUNT = n;
    hourlyCapSource = "config";
  } else {
    // No config value → use adaptive default
    HOURLY_MAX_TX_PER_ACCOUNT = ADAPTIVE_HOURLY_DEFAULT;
    hourlyCapSource = "default";
  }
}

/**
 * Called when server returns HTTP 400 hourly send limit.
 * Learns the actual cap from the number of successful TXs this hour.
 */
function learnHourlyCapFromServer(accountName, error) {
  const successfulThisHour = getHourlyTxCount(accountName);
  // Try to parse exact limit from server message: "Hourly send limit reached (2 per hour)"
  const serverParsedCap = parseHourlyLimitFromError(error);
  const learnedCap = serverParsedCap || Math.max(ADAPTIVE_HOURLY_MIN, successfulThisHour);

  if (hourlyCapSource === "config") {
    console.log(
      `[adaptive-cap] Server rejected ${accountName} after ${successfulThisHour} TX/hr ` +
      `(server says: ${serverParsedCap || "??"}/hr) but hourly cap is pinned by config (${HOURLY_MAX_TX_PER_ACCOUNT}/hr)`
    );
    return;
  }

  const previousCap = HOURLY_MAX_TX_PER_ACCOUNT;
  HOURLY_MAX_TX_PER_ACCOUNT = learnedCap;
  hourlyCapSource = "server";
  lastServerCapLearnedAt = Date.now();

  if (learnedCap !== previousCap) {
    console.log(
      `[adaptive-cap] Learned from server: cap ${previousCap} → ${learnedCap}/hr ` +
      `(${accountName} got 400, server says "${serverParsedCap || "??"} per hour", ` +
      `successful this hr: ${successfulThisHour})`
    );
  } else {
    console.log(
      `[adaptive-cap] Server confirmed cap ${learnedCap}/hr (parsed=${serverParsedCap || "??"})`
    );
  }
}

/**
 * Periodically probe if server allows more TXs (cap may have been raised server-side).
 * Called after successful TX. Only probes up if last 400 was long ago.
 */
function maybeProbeHigherCap() {
  if (hourlyCapSource === "config") return; // Pinned by config
  if (hourlyCapSource !== "server") return; // Only probe after we've learned from server
  if (HOURLY_MAX_TX_PER_ACCOUNT >= ADAPTIVE_HOURLY_MAX) return;

  const timeSinceLearnedMs = Date.now() - lastServerCapLearnedAt;
  if (timeSinceLearnedMs >= ADAPTIVE_PROBE_INTERVAL_MS) {
    const previousCap = HOURLY_MAX_TX_PER_ACCOUNT;
    HOURLY_MAX_TX_PER_ACCOUNT = Math.min(ADAPTIVE_HOURLY_MAX, previousCap + 1);
    console.log(
      `[adaptive-cap] Probing: cap raised ${previousCap} → ${HOURLY_MAX_TX_PER_ACCOUNT}/hr ` +
      `(no 400 in ${Math.round(timeSinceLearnedMs / 60000)}min)`
    );
    lastServerCapLearnedAt = Date.now(); // Reset probe timer
  }
}

function recordTxTimestamp(accountName) {
  const name = String(accountName || "").trim();
  if (!name) return;
  const nowMs = Date.now();
  const list = txTimestampsByAccount.get(name) || [];
  list.push(nowMs);
  const cutoff = nowMs - HOURLY_TX_WINDOW_MS;
  while (list.length > 0 && list[0] < cutoff) {
    list.shift();
  }
  txTimestampsByAccount.set(name, list);
  lastTxTimestampByAccount.set(name, nowMs);
}

function getHourlyTxCount(accountName) {
  const list = txTimestampsByAccount.get(String(accountName || "").trim()) || [];
  const cutoff = Date.now() - HOURLY_TX_WINDOW_MS;
  while (list.length > 0 && list[0] < cutoff) {
    list.shift();
  }
  return list.length;
}

function getHourlyResetWaitMs(accountName) {
  const name = String(accountName || "").trim();
  const list = txTimestampsByAccount.get(name) || [];
  const cutoff = Date.now() - HOURLY_TX_WINDOW_MS;
  while (list.length > 0 && list[0] < cutoff) {
    list.shift();
  }
  if (list.length < HOURLY_MAX_TX_PER_ACCOUNT) return 0;
  // Per-account hard cooldown: setelah hit cap, wajib tunggu penuh 1 jam dihitung dari TX pertama akun ini.
  const firstTx = list[0];
  const waitMs = firstTx + HOURLY_TX_WINDOW_MS + HOURLY_TX_BUFFER_MS - Date.now();
  return Math.max(0, waitMs);
}

// key: "sender=>recipient", value: timestamp (ms) of successful send
const sendPairHistory = new Map();
// key: "sender=>recipient", value: block-until timestamp (ms)
const reciprocalSendCooldowns = new Map();

// OTC counterparty take history — global across all taker accounts.
// Resets every Saturday 00:00 UTC (= Saturday 07:00 WIB), aligned with Roots'
// rewards weekly snapshot. /api/account/rewards penalties counter resets too.
// key: makerUsername (lowercased), value: number[] of successful take timestamps (ms)
const otcCounterpartyTakeHistory = new Map();

function normalizeOtcUsername(name) {
  return String(name || "").trim().toLowerCase();
}

// Returns timestamp (ms) of the most recent Saturday 00:00:00 UTC at or before nowMs.
// UTC day index: Sun=0, Mon=1, ..., Sat=6. Days back to Saturday: (dayUTC + 1) % 7.
function getLastSaturdayMidnightUTC(nowMs) {
  const d = new Date(nowMs);
  const dayUTC = d.getUTCDay();
  const daysBack = (dayUTC + 1) % 7;
  return Date.UTC(
    d.getUTCFullYear(),
    d.getUTCMonth(),
    d.getUTCDate() - daysBack,
    0, 0, 0, 0
  );
}

function getNextCounterpartyResetMs(nowMs) {
  return getLastSaturdayMidnightUTC(nowMs) + 7 * 24 * 60 * 60 * 1000;
}

function pruneOtcCounterpartyHistory(username, nowMs) {
  const key = normalizeOtcUsername(username);
  if (!key) return [];
  const arr = otcCounterpartyTakeHistory.get(key);
  if (!Array.isArray(arr) || arr.length === 0) {
    if (arr) otcCounterpartyTakeHistory.delete(key);
    return [];
  }
  const cutoff = getLastSaturdayMidnightUTC(nowMs);
  const fresh = arr.filter((t) => t >= cutoff);
  if (fresh.length === 0) {
    otcCounterpartyTakeHistory.delete(key);
  } else if (fresh.length !== arr.length) {
    otcCounterpartyTakeHistory.set(key, fresh);
  }
  return fresh;
}

function getOtcCounterpartyTakeCount(username) {
  return pruneOtcCounterpartyHistory(username, Date.now()).length;
}

function recordOtcCounterpartyTake(username) {
  const key = normalizeOtcUsername(username);
  if (!key) return;
  const nowMs = Date.now();
  const fresh = pruneOtcCounterpartyHistory(key, nowMs);
  fresh.push(nowMs);
  otcCounterpartyTakeHistory.set(key, fresh);
}

// ═══════════════════════════════════════════════════════════════════
// Per-account swap window — 100% LOCAL counting.
// Semua counting dilakukan lokal (recordOtcAccountSwap).
// Server sync TIDAK digunakan untuk count — menghindari race condition.
// Timer 60 menit dimulai saat swap pertama di round.
// 5 swap sukses = 1 round. Round naik via completeOtcAccountSwapRound().
// key: account name, value: { count, windowStartMs, roundNumber }
// ═══════════════════════════════════════════════════════════════════
const otcAccountSwapWindow = new Map();
const SWAP_WINDOW_MS = 60 * 60 * 1000;

function getOtcAccountSwapWindow(accountName) {
  const key = String(accountName || "");
  if (!key) return { count: 0, windowStartMs: 0, roundNumber: 1 };
  const w = otcAccountSwapWindow.get(key);
  if (!w) return { count: 0, windowStartMs: 0, roundNumber: 1 };
  // TIDAK ada auto-reset. State hanya berubah via:
  //   recordOtcAccountSwap()        → count++
  //   completeOtcAccountSwapRound() → round++, count=0
  //   resetOtcAccountSwapWindow()   → count=0 (window expired tanpa cap)
  return w;
}

function getOtcAccountSwapCount(accountName) {
  return getOtcAccountSwapWindow(accountName).count;
}

function getOtcAccountSwapRound(accountName) {
  return getOtcAccountSwapWindow(accountName).roundNumber || 1;
}

// Record 1 swap sukses. Jika ini swap pertama di round, mulai countdown.
function recordOtcAccountSwap(accountName) {
  const key = String(accountName || "");
  if (!key) return;
  const w = getOtcAccountSwapWindow(key);
  const nowMs = Date.now();
  const next = {
    count: w.count + 1,
    windowStartMs: w.count === 0 ? nowMs : w.windowStartMs,
    roundNumber: w.roundNumber || 1
  };
  otcAccountSwapWindow.set(key, next);
}

// Returns ms until the current window ends (0 if no active window or expired).
function getOtcAccountSwapResetMs(accountName) {
  const w = getOtcAccountSwapWindow(accountName);
  if (!w.windowStartMs) return 0;
  return Math.max(0, w.windowStartMs + SWAP_WINDOW_MS - Date.now());
}

// Cek apakah window countdown sudah expired.
function isOtcAccountSwapWindowExpired(accountName) {
  const w = getOtcAccountSwapWindow(accountName);
  if (!w.windowStartMs) return false; // belum ada window
  return Date.now() >= w.windowStartMs + SWAP_WINDOW_MS;
}

// Dipanggil saat cap tercapai (5/5) DAN cooldown selesai → round naik.
function completeOtcAccountSwapRound(accountName) {
  const key = String(accountName || "");
  if (!key) return { count: 0, windowStartMs: 0, roundNumber: 1 };
  const w = getOtcAccountSwapWindow(key);
  const next = {
    count: 0,
    windowStartMs: 0,
    roundNumber: (w.roundNumber || 1) + 1
  };
  otcAccountSwapWindow.set(key, next);
  return next;
}

// Reset window saat countdown expired tapi cap belum tercapai.
// Count reset ke 0, round tetap sama. Next swap akan mulai countdown baru.
function resetOtcAccountSwapWindow(accountName) {
  const key = String(accountName || "");
  if (!key) return;
  const w = getOtcAccountSwapWindow(key);
  const next = {
    count: 0,
    windowStartMs: 0,
    roundNumber: w.roundNumber || 1
  };
  otcAccountSwapWindow.set(key, next);
}

// Status order yang dihitung sebagai swap (filled + failed).
// Cancelled / canceled / expired TIDAK dihitung sebagai swap.
function isOtcSwapCountedStatus(status) {
  const s = String(status || "").toLowerCase();
  return s === "filled" || s === "failed";
}

// Status terminal (final) yang membuat order keluar dari in-flight.
function isOtcTerminalStatus(status) {
  const s = String(status || "").toLowerCase();
  return s === "filled" || s === "failed" || s === "expired"
    || s === "cancelled" || s === "canceled" || s === "rejected";
}

// Poll /orders (mine=true) sampai order ID tertentu mencapai status terminal,
// atau hilang dari /orders mine. Dipakai untuk verifikasi setelah take/create
// sebelum kita cek cap & lanjut swap berikutnya.
// Return: { resolved, status, order } — resolved=true kalau dapat status final
// atau order hilang. status="missing" kalau order tidak ditemukan.
async function waitForOtcOrderResolution(client, orderId, opts = {}) {
  const timeoutMs = Math.max(1000, Number(opts.timeoutMs) || 30000);
  const pollIntervalMs = Math.max(500, Number(opts.pollIntervalMs) || 2000);
  const allowMissing = opts.allowMissing !== false; // default true
  const deadline = Date.now() + timeoutMs;
  let lastStatus = null;
  let lastOrder = null;
  while (Date.now() < deadline) {
    try {
      const res = await client.getCrossOtcOrders(true);
      const list = Array.isArray(res && res.data && res.data.orders)
        ? res.data.orders
        : (Array.isArray(res && res.data) ? res.data : []);
      const found = list.find(o => String(o.id) === String(orderId));
      if (!found) {
        if (allowMissing) return { resolved: true, status: "missing", order: null };
      } else {
        lastOrder = found;
        lastStatus = String(found.status || "").toLowerCase();
        if (isOtcTerminalStatus(lastStatus)) {
          return { resolved: true, status: lastStatus, order: found };
        }
      }
    } catch (_) { /* swallow & retry */ }
    await sleep(pollIntervalMs);
  }
  return { resolved: false, status: lastStatus, order: lastOrder };
}

// Short-lived blacklist for orders that returned HTTP 409 (already reserved/closed)
// or HTTP 400 "balance below required" on take. key: orderId, value: until-ms
const otcOrderBlacklist = new Map();

function blacklistOtcOrder(orderId, ttlMs) {
  if (!orderId) return;
  const ttl = Math.max(1000, Number(ttlMs) || 60000);
  otcOrderBlacklist.set(String(orderId), Date.now() + ttl);
}

function isOtcOrderBlacklisted(orderId) {
  if (!orderId) return false;
  const until = otcOrderBlacklist.get(String(orderId));
  if (!until) return false;
  if (until <= Date.now()) {
    otcOrderBlacklist.delete(String(orderId));
    return false;
  }
  return true;
}

function pruneOtcOrderBlacklist() {
  const now = Date.now();
  for (const [id, until] of otcOrderBlacklist.entries()) {
    if (until <= now) otcOrderBlacklist.delete(id);
  }
}

function isOtcBalanceLockError(errMsg) {
  const text = String(errMsg || "").toLowerCase();
  return text.includes("400") && text.includes("available canton balance is below");
}

function isOtcOrderClosedError(errMsg) {
  const text = String(errMsg || "").toLowerCase();
  return (text.includes("409") && (text.includes("no longer open") || text.includes("reserved by someone")))
    || text.includes("order is no longer open");
}

// HTTP 409 dari /reserve dengan pesan "settlement in progress for this asset".
// Order belum tentu tertutup — maker wallet sedang menyelesaikan transaksi lain
// untuk aset yang sama. Aman di-retry beberapa detik lagi.
function isOtcMakerSettlementInProgressError(errMsg) {
  const text = String(errMsg || "").toLowerCase();
  if (!text.includes("409")) return false;
  return text.includes("settlement in progress")
    || (text.includes("already has a settlement") && text.includes("asset"))
    || text.includes("try again shortly");
}

// Continuous scheduler state
// key: accountName, value: earliest timestamp (ms) the account may send again
const nextAvailableAtByAccount = new Map();
// key: recipientName, value: expiresAtMs (short lock while a sender is targeting them)
const claimedRecipients = new Map();
const RECIPIENT_CLAIM_TTL_MS = 120 * 1000;

function claimRecipient(recipientName) {
  if (!recipientName) return false;
  const nowMs = Date.now();
  const expiresAt = Number(claimedRecipients.get(recipientName) || 0);
  if (expiresAt > nowMs) {
    return false;
  }
  claimedRecipients.set(recipientName, nowMs + RECIPIENT_CLAIM_TTL_MS);
  return true;
}

function releaseRecipient(recipientName) {
  if (!recipientName) return;
  claimedRecipients.delete(recipientName);
}

function isRecipientClaimed(recipientName) {
  if (!recipientName) return false;
  const expiresAt = Number(claimedRecipients.get(recipientName) || 0);
  if (expiresAt <= Date.now()) {
    claimedRecipients.delete(recipientName);
    return false;
  }
  return true;
}

let roundRobinOffset = 0;
let lastRoundPrimaryOffset = 0;
const cachedRoundOffsets = new Map();

function buildSendPairKey(senderName, recipientName) {
  return `${String(senderName || "").trim()}=>${String(recipientName || "").trim()}`;
}

function cleanupExpiredSendPairs() {
  const nowMs = Date.now();

  for (const [pairKey, timestamp] of sendPairHistory.entries()) {
    if (!Number.isFinite(Number(timestamp))) {
      sendPairHistory.delete(pairKey);
      continue;
    }

    if (nowMs - Number(timestamp) > SEND_PAIR_COOLDOWN_MS) {
      sendPairHistory.delete(pairKey);
    }
  }

  for (const [pairKey, expiresAt] of reciprocalSendCooldowns.entries()) {
    if (!Number.isFinite(Number(expiresAt)) || Number(expiresAt) <= nowMs) {
      reciprocalSendCooldowns.delete(pairKey);
    }
  }
}

function getReciprocalCooldownSeconds(senderName, recipientName) {
  const key = buildSendPairKey(senderName, recipientName);
  const expiresAt = Number(reciprocalSendCooldowns.get(key));
  if (!Number.isFinite(expiresAt)) {
    return 0;
  }

  const remainingMs = expiresAt - Date.now();
  if (remainingMs <= 0) {
    reciprocalSendCooldowns.delete(key);
    return 0;
  }

  return Math.max(1, Math.ceil(remainingMs / 1000) + SEND_PAIR_COOLDOWN_BUFFER_SECONDS);
}

function recordSendPair(senderName, recipientName) {
  const sender = String(senderName || "").trim();
  const recipient = String(recipientName || "").trim();
  if (!sender || !recipient || sender === recipient) {
    return;
  }

  const nowMs = Date.now();
  const pairKey = buildSendPairKey(sender, recipient);
  const reciprocalKey = buildSendPairKey(recipient, sender);

  sendPairHistory.set(pairKey, nowMs);
  reciprocalSendCooldowns.set(reciprocalKey, nowMs + SEND_PAIR_COOLDOWN_MS);
}

function isReciprocalPairInCooldown(senderName, recipientName) {
  return getReciprocalCooldownSeconds(senderName, recipientName) > 0;
}

function getShortestReciprocalCooldownSeconds(senderName, sortedAccounts) {
  if (!Array.isArray(sortedAccounts) || sortedAccounts.length === 0) {
    return 0;
  }

  let shortest = 0;
  for (const account of sortedAccounts) {
    const recipientName = String(account && account.name ? account.name : "").trim();
    if (!recipientName || recipientName === senderName) {
      continue;
    }

    const cooldownSeconds = getReciprocalCooldownSeconds(senderName, recipientName);
    if (cooldownSeconds <= 0) {
      continue;
    }

    shortest = shortest === 0 ? cooldownSeconds : Math.min(shortest, cooldownSeconds);
  }

  return shortest;
}

function getRoundRobinOffset() {
  return roundRobinOffset;
}

function getRotatingOffset(totalAccounts, loopRound = null) {
  const normalizedTotal = clampToNonNegativeInt(totalAccounts, 0);
  if (normalizedTotal < 2) {
    return 1;
  }

  const maxOffset = normalizedTotal - 1;
  // Simple +1 offset per round: round 1 -> offset 1, round 2 -> offset 2, etc.
  // This guarantees a unique recipient each round and never sends to self.
  const roundSeed = Number.isFinite(Number(loopRound))
    ? Math.max(1, clampToNonNegativeInt(loopRound, 1))
    : Math.max(1, clampToNonNegativeInt(getRoundRobinOffset(), 1));

  const selectedOffset = ((roundSeed - 1) % maxOffset) + 1;

  lastRoundPrimaryOffset = selectedOffset;
  return selectedOffset;
}

function buildInternalOffsetPriority(totalAccounts, primaryOffset) {
  const normalizedTotal = clampToNonNegativeInt(totalAccounts, 0);
  const maxOffset = normalizedTotal - 1;
  if (maxOffset < 1) {
    return [];
  }

  const safePrimary = Math.min(
    maxOffset,
    Math.max(1, clampToNonNegativeInt(primaryOffset, 1))
  );

  // Primary offset first, then fallback chain across ALL other offsets so a sender
  // can still send when the primary pair is in reciprocal cooldown. Server rules
  // (10m reciprocal + 60s per-account) stay enforced downstream.
  const offsets = [safePrimary];
  for (let step = 1; step <= maxOffset; step += 1) {
    const candidate = ((safePrimary - 1 + step) % maxOffset) + 1;
    if (candidate !== safePrimary && !offsets.includes(candidate)) {
      offsets.push(candidate);
    }
  }
  return offsets;
}

function incrementRoundRobinOffset() {
  roundRobinOffset += 1;
}

function resetRoundRobinOffset() {
  roundRobinOffset = 0;
  lastRoundPrimaryOffset = 0;
  cachedRoundOffsets.clear();
}

/**
 * Build internal send candidates using rotating offsets + reciprocal cooldown guard.
 * The first candidate is primary target; remaining entries are fallback recipients.
 */
function buildInternalSendRequests(
  accounts,
  senderName,
  sendPolicy,
  loopRound = null,
  avoidRecipientNames = [],
  preferRecipientNames = []
) {
  const validAccounts = Array.isArray(accounts)
    ? accounts.filter((acc) => String(acc && acc.address ? acc.address : "").trim())
    : [];
  const avoidRecipientsSet = new Set(
    Array.isArray(avoidRecipientNames)
      ? avoidRecipientNames
        .map((item) => String(item || "").trim())
        .filter((item) => Boolean(item))
      : []
  );

  if (validAccounts.length < 2) {
    console.log(
      `[internal] Internal mode requires at least 2 accounts with valid addresses. ` +
      `Found ${validAccounts.length} valid accounts.`
    );
    return {
      requests: [],
      reason: "not-enough-accounts",
      retryAfterSeconds: 0,
      primaryOffset: 1
    };
  }

  const sortedAccounts = [...validAccounts].sort((a, b) => a.name.localeCompare(b.name));
  const senderIndex = sortedAccounts.findIndex((acc) => acc.name === senderName);
  if (senderIndex === -1) {
    console.log(`[internal] Sender ${senderName} not found in sorted account list`);
    return {
      requests: [],
      reason: "sender-not-found",
      retryAfterSeconds: 0,
      primaryOffset: 1
    };
  }

  cleanupExpiredSendPairs();

  const primaryOffset = getRotatingOffset(sortedAccounts.length, loopRound);
  const offsetPriority = buildInternalOffsetPriority(sortedAccounts.length, primaryOffset);
  const senderTierKey = getAccountTierKey(senderName);
  const amount = generateRandomCcAmount(sendPolicy, senderTierKey);
  const requests = [];
  let shortestBlockedCooldownSeconds = 0;
  let skippedByAvoidCount = 0;

  for (const offset of offsetPriority) {
    const recipientIndex = (senderIndex + offset) % sortedAccounts.length;
    const recipient = sortedAccounts[recipientIndex];
    if (!recipient || recipient.name === senderName) {
      continue;
    }

    if (avoidRecipientsSet.has(recipient.name)) {
      skippedByAvoidCount += 1;
      continue;
    }

    // Skip quarantined accounts as recipients (low score protection)
    if (isAccountQuarantined(recipient.name)) {
      continue;
    }

    const reciprocalCooldownSeconds = getReciprocalCooldownSeconds(senderName, recipient.name);
    if (reciprocalCooldownSeconds > 0) {
      shortestBlockedCooldownSeconds = shortestBlockedCooldownSeconds === 0
        ? reciprocalCooldownSeconds
        : Math.min(shortestBlockedCooldownSeconds, reciprocalCooldownSeconds);
      continue;
    }

    requests.push({
      amount,
      label: recipient.name,
      address: recipient.address,
      username: getAccountUsername(recipient.name) || null,
      source: "internal-rotating",
      offset,
      internalRecipientCandidate: true
    });
  }

  // Prioritize preferred recipients (low-balance/deferred accounts that need inbound)
  const preferSet = new Set(
    Array.isArray(preferRecipientNames)
      ? preferRecipientNames.map((n) => String(n || "").trim()).filter(Boolean)
      : []
  );

  if (preferSet.size > 0 && requests.length > 1) {
    const preferred = [];
    const others = [];
    for (const req of requests) {
      if (preferSet.has(req.label)) {
        preferred.push(req);
      } else {
        others.push(req);
      }
    }
    if (preferred.length > 0) {
      // Shuffle within each group for randomness, but preferred comes first
      const shuffledPreferred = preferred.length > 1 ? shuffleArray(preferred) : preferred;
      const shuffledOthers = others.length > 1 ? shuffleArray(others) : others;
      requests.length = 0;
      requests.push(...shuffledPreferred, ...shuffledOthers);
      console.log(
        `[internal] Prefer recipients for ${senderName}: [${[...preferSet].join(", ")}] ` +
        `matched=${preferred.map((r) => r.label).join(", ")}`
      );
      return {
        requests,
        reason: requests.length > 0 ? null : "no-eligible-recipients",
        retryAfterSeconds: 0,
        primaryOffset: primaryOffset
      };
    }
  }

  // Balance-smart fallback: if no explicit prefer matched, auto-detect deficit
  // recipients from cached balance data and prioritize them.
  if (requests.length > 1) {
    const accountNamesForDist = sortedAccounts.map((a) => a.name);
    const balancePreferNames = getBalanceBasedPreferredRecipients(senderName, accountNamesForDist);
    if (balancePreferNames.length > 0) {
      const balancePreferSet = new Set(balancePreferNames);
      const balancePreferred = [];
      const balanceOthers = [];
      for (const req of requests) {
        if (balancePreferSet.has(req.label)) {
          balancePreferred.push(req);
        } else {
          balanceOthers.push(req);
        }
      }
      if (balancePreferred.length > 0) {
        const shuffledBP = balancePreferred.length > 1 ? shuffleArray(balancePreferred) : balancePreferred;
        const shuffledBO = balanceOthers.length > 1 ? shuffleArray(balanceOthers) : balanceOthers;
        requests.length = 0;
        requests.push(...shuffledBP, ...shuffledBO);
        console.log(
          `[internal] Balance-smart for ${senderName}: prefer deficit=[${balancePreferred.map((r) => r.label).join(", ")}]`
        );
      }
    }
  }

  // Randomize fallback candidate order (keep primary target first)
  if (requests.length > 2 && requests[0] && !requests[0]._balanceSorted) {
    const primary = requests[0];
    const shuffledFallbacks = shuffleArray(requests.slice(1));
    requests.length = 0;
    requests.push(primary, ...shuffledFallbacks);
  }

  if (requests.length === 0) {
    const shortestCooldownSeconds =
      shortestBlockedCooldownSeconds > 0
        ? shortestBlockedCooldownSeconds
        : getShortestReciprocalCooldownSeconds(senderName, sortedAccounts);
    const sendBackGuardSeconds = Math.ceil(SEND_PAIR_COOLDOWN_MS / 1000);
    const hasAvoidOnlyBlock = skippedByAvoidCount > 0 && shortestCooldownSeconds <= 0;
    const retryAfterSeconds = hasAvoidOnlyBlock
      ? sendBackGuardSeconds
      : (shortestCooldownSeconds || 0);
    const reason = hasAvoidOnlyBlock
      ? "internal-avoid-sendback"
      : "internal-reciprocal-cooldown";
    console.log(
      `[internal] ${senderName}: no eligible recipient. ` +
      `cooldownRetry=${shortestCooldownSeconds || 0}s avoidBlocked=${skippedByAvoidCount} ` +
      `(retryAfter=${retryAfterSeconds}s reason=${reason})`
    );
    return {
      requests: [],
      reason,
      retryAfterSeconds,
      primaryOffset
    };
  }

  const preview = requests.slice(0, 4).map((entry) => entry.label).join(", ");
  const suffix = requests.length > 4 ? ` (+${requests.length - 4} more)` : "";
  console.log(
    `[internal] ${senderName}: offset=${primaryOffset} candidates=${requests.length}/${offsetPriority.length} ` +
    `primary=${requests[0].label} | pool=[${preview}${suffix}]`
  );

  return {
    requests,
    reason: null,
    retryAfterSeconds: 0,
    primaryOffset
  };
}

// ============================================================================

// Global TX Tracking - accumulates totals across all accounts for dashboard banner
let globalSwapsTotal = 0;
let globalSwapsOk = 0;
let globalSwapsFail = 0;

// Per-account TX tracking - accumulates totals per account for TX Progress column
const perAccountTxStats = {};

function resetGlobalTxStats() {
  globalSwapsTotal = 0;
  globalSwapsOk = 0;
  globalSwapsFail = 0;
  // Clear per-account stats
  for (const key of Object.keys(perAccountTxStats)) {
    delete perAccountTxStats[key];
  }
}

function addGlobalTxStats(completed, failed) {
  globalSwapsTotal += completed + failed;
  globalSwapsOk += completed;
  globalSwapsFail += failed;
}

function addPerAccountTxStats(accountName, completed, failed) {
  if (!perAccountTxStats[accountName]) {
    perAccountTxStats[accountName] = { total: 0, ok: 0, fail: 0 };
  }
  perAccountTxStats[accountName].total += completed + failed;
  perAccountTxStats[accountName].ok += completed;
  perAccountTxStats[accountName].fail += failed;
}

function getPerAccountTxStats(accountName) {
  return perAccountTxStats[accountName] || { total: 0, ok: 0, fail: 0 };
}

// ============================================================================
// PASSIVE CC BALANCE TRACKING (Zero extra API calls)
// ============================================================================
// Caches CC balance from existing balance checks (session reuse, pre-TX, post-TX).
// No additional API requests — only stores results from calls that already happen.
// Used by smart balancing to route sends from surplus → deficit accounts.
// ============================================================================

const latestCcBalanceByAccount = new Map();
const latestUsdcBaseByAccount = new Map();

function updateAccountCcBalance(accountName, ccNumeric) {
  const name = String(accountName || "").trim();
  if (!name) return;
  const cc = Number(ccNumeric);
  if (!Number.isFinite(cc) || cc < 0) return;
  latestCcBalanceByAccount.set(name, { cc, updatedAt: Date.now() });
}

function getAccountCcBalance(accountName) {
  const entry = latestCcBalanceByAccount.get(String(accountName || "").trim());
  return entry ? entry.cc : null;
}

function updateAccountUsdcBalance(accountName, usdcNumeric) {
  const name = String(accountName || "").trim();
  if (!name) return;
  const usdc = Number(usdcNumeric);
  if (!Number.isFinite(usdc) || usdc < 0) return;
  latestUsdcBaseByAccount.set(name, usdc);
}

function getAccountUsdcBalance(accountName) {
  return latestUsdcBaseByAccount.get(String(accountName || "").trim()) ?? null;
}

// Per-account send target tracking (who is the current/last recipient)
const lastSendTargetByAccount = new Map();
function updateLastSendTarget(accountName, recipientName) {
  const name = String(accountName || "").trim();
  if (name && recipientName) lastSendTargetByAccount.set(name, String(recipientName).trim());
}
function getLastSendTarget(accountName) {
  return lastSendTargetByAccount.get(String(accountName || "").trim()) || null;
}

// Per-account cooldown end timestamp tracking (for dashboard CD column)
const accountCooldownEndMs = new Map();
function setAccountCooldownEnd(accountName, endMs) {
  const name = String(accountName || "").trim();
  if (name) accountCooldownEndMs.set(name, endMs);
}
function getAccountCooldownRemainingSec(accountName) {
  const endMs = accountCooldownEndMs.get(String(accountName || "").trim()) || 0;
  const remaining = endMs - Date.now();
  return remaining > 0 ? Math.ceil(remaining / 1000) : 0;
}

// ============================================================================
// GLOBAL USERNAME CACHE
// ============================================================================
// Caches resolved Roots usernames per account (from login or /api/send/resolve).
// RootsFi now requires username-based transfers (recipientType: "user") instead
// of Canton address-based ones (recipientType: "canton_wallet"). This cache
// avoids redundant resolve API calls after the first successful resolution.
// ============================================================================

const cachedUsernameByAccount = new Map();

function updateAccountUsername(accountName, username) {
  const name = String(accountName || "").trim();
  const user = String(username || "").trim();
  if (!name || !user) return;
  cachedUsernameByAccount.set(name, user);
}

function getAccountUsername(accountName) {
  return cachedUsernameByAccount.get(String(accountName || "").trim()) || null;
}

/**
 * Update cached balance after a successful send (no API call).
 * Sender balance decreases, recipient balance increases.
 */
function adjustAccountCcBalanceAfterSend(senderName, recipientName, amountSent) {
  const sender = String(senderName || "").trim();
  const recipient = String(recipientName || "").trim();
  const amount = Number(amountSent);
  if (!sender || !Number.isFinite(amount) || amount <= 0) return;

  const senderEntry = latestCcBalanceByAccount.get(sender);
  if (senderEntry) {
    senderEntry.cc = Math.max(0, senderEntry.cc - amount);
    senderEntry.updatedAt = Date.now();
  }

  if (recipient) {
    const recipientEntry = latestCcBalanceByAccount.get(recipient);
    if (recipientEntry) {
      recipientEntry.cc += amount;
      recipientEntry.updatedAt = Date.now();
    }
  }
}

// ============================================================================
// SMART BALANCE DISTRIBUTION
// ============================================================================
// Computes surplus/deficit classification from cached balances.
// Returns preferred recipients sorted by biggest deficit first.
// Surplus = >1.3x average, Deficit = <0.7x average.
// ============================================================================

function computeBalanceDistribution(accountNames) {
  const names = Array.isArray(accountNames) ? accountNames : [];
  const entries = [];
  let totalCc = 0;
  let trackedCount = 0;

  for (const name of names) {
    const cc = getAccountCcBalance(name);
    if (cc !== null) {
      entries.push({ name, cc });
      totalCc += cc;
      trackedCount += 1;
    } else {
      entries.push({ name, cc: null });
    }
  }

  if (trackedCount < 2) {
    return { entries, averageCc: 0, tracked: trackedCount, surplus: [], deficit: [] };
  }

  const averageCc = totalCc / trackedCount;
  const surplus = entries
    .filter((e) => e.cc !== null && e.cc > averageCc * 1.3)
    .sort((a, b) => b.cc - a.cc);
  const deficit = entries
    .filter((e) => e.cc !== null && e.cc < averageCc * 0.7)
    .sort((a, b) => a.cc - b.cc);

  return { entries, averageCc, tracked: trackedCount, surplus, deficit };
}

/**
 * Get preferred recipient list based on CC balance deficit.
 * Only suggests deficit accounts if sender has above-average balance.
 * Returns array of account names sorted by lowest balance first.
 */
function getBalanceBasedPreferredRecipients(senderName, accountNames) {
  const distribution = computeBalanceDistribution(accountNames);
  if (distribution.tracked < 2) return [];

  const sender = String(senderName || "").trim();
  const senderCc = getAccountCcBalance(sender);

  // Only route to deficit accounts if sender has above-average balance
  if (senderCc === null || senderCc <= distribution.averageCc * 0.8) return [];

  return distribution.deficit
    .filter((e) => e.name !== sender)
    .map((e) => e.name);
}

function logBalanceDistribution(accountNames, roundLabel) {
  const dist = computeBalanceDistribution(accountNames);
  if (dist.tracked < 2) {
    console.log(
      `[balance-smart] ${roundLabel} Waiting for balance data (${dist.tracked}/${accountNames.length} tracked)`
    );
    return;
  }

  const avgLabel = dist.averageCc.toFixed(1);
  const surplusLabel =
    dist.surplus.map((e) => `${e.name}(${e.cc.toFixed(0)})`).join(", ") || "none";
  const deficitLabel =
    dist.deficit.map((e) => `${e.name}(${e.cc.toFixed(0)})`).join(", ") || "none";
  console.log(
    `[balance-smart] ${roundLabel} avg=${avgLabel} CC | ` +
    `surplus=[${surplusLabel}] | deficit=[${deficitLabel}]`
  );
}

/**
 * Pre-compute round send plan for parallel-safe execution.
 * Assigns each surplus sender exactly ONE unique deficit recipient.
 * This prevents race conditions where multiple parallel senders
 * all target the same deficit account simultaneously.
 *
 * Returns Map<senderName, string[]> — per-sender prefer list.
 * Senders NOT in the map use the generic lowBalanceAccountNames fallback.
 */
function computeRoundSendPlan(sortedAccounts) {
  const plan = new Map();
  const accountNames = sortedAccounts.map((a) => a.name);
  const dist = computeBalanceDistribution(accountNames);

  if (dist.tracked < 2 || dist.deficit.length === 0 || dist.surplus.length === 0) {
    return plan;
  }

  // Surplus senders sorted by highest balance (most to give)
  const surplusSenders = dist.surplus.map((e) => e.name);
  // Deficit recipients sorted by lowest balance (most need)
  const deficitRecipients = dist.deficit.map((e) => e.name);

  // 1:1 assignment: each surplus sender gets one unique deficit recipient
  // Skip pairs that are in reciprocal cooldown
  const assignedRecipients = new Set();

  for (const senderName of surplusSenders) {
    for (const recipientName of deficitRecipients) {
      if (assignedRecipients.has(recipientName)) continue;
      if (senderName === recipientName) continue;
      if (isReciprocalPairInCooldown(senderName, recipientName)) continue;

      plan.set(senderName, [recipientName]);
      assignedRecipients.add(recipientName);
      break;
    }
  }

  // Log the send plan
  if (plan.size > 0) {
    const assignments = [];
    for (const [sender, recipients] of plan.entries()) {
      assignments.push(`${sender}→${recipients[0]}`);
    }
    console.log(
      `[balance-smart] Round plan (${plan.size} pair${plan.size > 1 ? "s" : ""}): ${assignments.join(", ")}`
    );
  }

  return plan;
}

/**
 * Smart recipient picker for continuous scheduler.
 * Strategy: pick account that cannot currently send (balance < own tierMin).
 * Skip self, skip already-claimed recipients, skip reciprocal-pair cooldown.
 * Returns recipient account object or null if none suitable.
 */
function pickSmartRecipient(senderName, sortedAccounts) {
  if (!Array.isArray(sortedAccounts) || sortedAccounts.length === 0) {
    return null;
  }

  const candidates = [];
  for (const account of sortedAccounts) {
    const name = String(account && account.name ? account.name : "").trim();
    if (!name || name === senderName) continue;
    if (!String(account.address || "").trim()) continue;
    // Skip if already targeted this round (no double-inbound)
    if (isRecipientClaimed(name)) continue;
    if (isReciprocalPairInCooldown(senderName, name)) continue;

    const cc = Number(getAccountCcBalance(name));
    if (!Number.isFinite(cc)) continue;

    const tierMin = getAccountTierMinSend(name);
    const minHold = 1; // reserve
    const sendThreshold = tierMin + minHold; // Need this much to send
    const canSend = cc >= sendThreshold;
    const deficit = sendThreshold - cc; // How much CC they need to become active
    const txStats = getPerAccountTxStats(name);
    const txTotal = clampToNonNegativeInt(txStats && txStats.total, 0);
    candidates.push({ account, name, cc, tierMin, deficit, canSend, txTotal });
  }

  if (candidates.length === 0) {
    return null;
  }

  // === CC CONSOLIDATION STRATEGY ===
  // Problem: 500 CC / 26 accounts = ~19 CC avg. Min send = 25 CC.
  // If CC scatters evenly, NO account can send.
  //
  // Strategy: "Activate then Seed"
  //   Phase 1: Send to accounts CLOSEST to threshold (1 send activates them)
  //   Phase 2: When no account is close, "seed" accounts by sending to
  //            the highest-balance needy account (builds them up over 2-3 rounds)
  //
  // This ensures CC circulates AND low-balance accounts gradually grow.

  const needy = candidates.filter(c => !c.canSend && c.deficit > 0);
  const ready = candidates.filter(c => c.canSend);

  if (needy.length > 0) {
    // Split needy into "almost ready" (1 send activates) and "needs seeding" (2+ sends)
    const avgSendAmount = 26; // approximate min send + buffer
    const almostReady = needy.filter(c => c.deficit <= avgSendAmount);
    const needsSeeding = needy.filter(c => c.deficit > avgSendAmount);

    if (almostReady.length > 0) {
      // Phase 1: Activate the closest (cheapest to push over threshold)
      almostReady.sort((a, b) => {
        if (a.deficit !== b.deficit) return a.deficit - b.deficit;
        if (a.txTotal !== b.txTotal) return a.txTotal - b.txTotal;
        return 0;
      });
      return almostReady[0].account;
    }

    // Phase 2: Seed the most promising low-balance account
    // Pick the one with HIGHEST CC (closest to activation even if far)
    // This concentrates multiple sends into ONE account instead of scattering
    needsSeeding.sort((a, b) => {
      // Highest CC first (needs fewest additional sends to activate)
      if (a.cc !== b.cc) return b.cc - a.cc;
      if (a.txTotal !== b.txTotal) return a.txTotal - b.txTotal;
      return 0;
    });
    return needsSeeding[0].account;
  }

  if (ready.length > 0) {
    // Everyone can send — route to lowest TX count (fairness)
    ready.sort((a, b) => {
      if (a.txTotal !== b.txTotal) return a.txTotal - b.txTotal;
      return a.cc - b.cc;
    });
    return ready[0].account;
  }

  return null;
}

const INTERNAL_API_DEFAULTS = {
  baseUrl: "https://bridge.rootsfi.com",
  paths: {
    onboard: "/onboard",
    send: "/send",
    bridge: "/bridge",
    rewards: "/rewards",
    syncAccount: "/api/auth/sync-account",
    authPending: "/api/auth/pending",
    sendOtp: "/api/auth/email/send-otp",
    verifyOtp: "/api/auth/email/verify-otp",
    finalizeReturning: "/api/auth/finalize-returning",
    walletBalances: "/api/wallet/balances",
    sendCcCooldown: "/api/send/cc-cooldown",
    sendResolve: "/api/send/resolve",
    sendTransfer: "/api/send/transfer",
    walletCcOutgoing: "/api/wallet/cc-outgoing",
    sendHistory: "/api/send/history",
    rewardsApi: "/api/rewards",
    rewardsLottery: "/api/rewards/lottery",
    rewardsSendLoyaltyDailyTaper: "/api/rewards/send-loyalty-daily-taper",
    sendLimits: "/api/send/limits",
    recipientPreview: "/api/send/recipient-preview",
    walletOffers: "/api/wallet/offers",
    walletOffersAccept: "/api/wallet/offers/accept",
    marketOtcPythPanel: "/api/market/otc-pyth-panel",
    crossOtcOrders: "/api/cross-otc/orders",
    crossOtcReference: "/api/cross-otc/reference",
    crossOtcStats: "/api/cross-otc/stats",
    accountRewards: "/api/account/rewards"
  },
  headers: {
    userAgent:
      "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.0.0 Safari/537.36",
    acceptLanguage: "en-US,en;q=0.9",
    sendBrowserClientHints: true,
    secChUa: '"Google Chrome";v="147", "Not.A/Brand";v="8", "Chromium";v="147"',
    secChUaMobile: "?0",
    secChUaPlatform: '"macOS"',
    secFetchDest: "empty",
    secFetchMode: "cors",
    secFetchSite: "same-origin",
    priority: "u=1, i"
  },
  http: {
    timeoutMs: 30000,
    maxRetries: 2,
    retryBaseDelayMs: 800
  },
  requestPacing: {
    minDelayMs: 450,
    jitterMs: 250
  },
  send: {
    maxLoopTx: 1,
    minDelayTxSeconds: 120,
    maxDelayTxSeconds: 120,
    delayCycleSeconds: 300,
    sequentialAllRounds: true,
    workers: 1,
    tierAmounts: {
      unranked: { min: "10", max: "25", decimals: 2 },
      newbie: { min: "10", max: "25", decimals: 2 },
      advanced: { min: "25", max: "50", decimals: 2 },
      pro: { min: "50", max: "100", decimals: 2 },
      elite: { min: "100", max: "200", decimals: 2 }
    }
  },
  ui: {
    dashboard: true,
    logLines: 20
  }
};

function getTimeStamp() {
  return new Date().toISOString().slice(11, 19);
}

class PinnedDashboard {
  constructor({ enabled, logLines, accountSnapshots }) {
    this.enabled = Boolean(enabled && process.stdout.isTTY);
    this.logLines = Math.min(
      30,
      Math.max(1, clampToNonNegativeInt(logLines, INTERNAL_API_DEFAULTS.ui.logLines))
    );
    this.logs = [];
    this.accountSnapshots = isObject(accountSnapshots) ? accountSnapshots : {};
    this.state = {
      phase: "init",
      selectedAccount: "-",
      accounts: "-",
      cookie: "-",
      balance: "-",
      send: "-",
      transfer: "-",
      reward: "-",
      rewardsThisWeek: "-",
      rewardsDiff: "-",
      mode: "BALANCE",
      strategy: "balanced_human",
      swapsTotal: 0,
      swapsOk: 0,
      swapsFail: 0,
      targetPerDay: 0,
      cooldown: "0/0"
    };
    this.originalConsole = null;
    this._renderTimer = null;
    this._lastRenderMs = 0;
    this._renderThrottleMs = 1000; // Max 1 render per second
  }

  attach() {
    if (!this.enabled || this.originalConsole) {
      return;
    }

    this.paused = false;

    this.originalConsole = {
      log: console.log,
      warn: console.warn,
      error: console.error
    };

    console.log = (...args) => this.pushLog("INFO", args);
    console.warn = (...args) => this.pushLog("WARN", args);
    console.error = (...args) => this.pushLog("ERROR", args);
    this.render();

    // Periodic refresh for live CD countdown (every 10s)
    this._cdInterval = setInterval(() => {
      if (!this.paused) this._scheduleRender();
    }, 10000);
  }

  detach() {
    if (!this.originalConsole) {
      return;
    }

    console.log = this.originalConsole.log;
    console.warn = this.originalConsole.warn;
    console.error = this.originalConsole.error;
    this.originalConsole = null;
    if (this._cdInterval) { clearInterval(this._cdInterval); this._cdInterval = null; }
    if (this._renderTimer) { clearTimeout(this._renderTimer); this._renderTimer = null; }
    process.stdout.write("\n");
  }

  setState(patch) {
    this.state = { ...this.state, ...patch };
    this.syncSelectedAccountSnapshot();
    if (!this.paused) this._scheduleRender();
  }

  stringifyArg(value) {
    if (typeof value === "string") {
      return value;
    }
    try {
      return JSON.stringify(value);
    } catch {
      return String(value);
    }
  }

  pushLog(level, args) {
    let message = args.map((item) => this.stringifyArg(item)).join(" ").trim();
    let logLevel = level;

    const accountTagMatch = message.match(/^\[(A\d+\/\d+)\]\s*/i);
    if (accountTagMatch) {
      logLevel = String(accountTagMatch[1] || level).toUpperCase();
      message = message.slice(accountTagMatch[0].length).trim();
    }

    // Skip duplicate consecutive messages
    if (this.logs.length > 0) {
      const lastLog = this.logs[this.logs.length - 1];
      if (lastLog.message === message && lastLog.level === logLevel) {
        return; // Don't add duplicate
      }
    }

    this.logs.push({
      time: getTimeStamp(),
      level: logLevel,
      message
    });

    // Keep up to 3x visible log lines in buffer to avoid losing rapid logs
    const maxBuf = this.logLines * 3;
    if (this.logs.length > maxBuf) {
      this.logs.splice(0, this.logs.length - maxBuf);
    }

    if (!this.paused) this._scheduleRender();
  }

  _scheduleRender() {
    if (this._renderTimer) return; // Already scheduled
    const elapsed = Date.now() - this._lastRenderMs;
    if (elapsed >= this._renderThrottleMs) {
      // Enough time passed, render immediately
      this.render();
    } else {
      // Schedule render after remaining throttle time
      this._renderTimer = setTimeout(() => {
        this._renderTimer = null;
        this.render();
      }, this._renderThrottleMs - elapsed);
    }
  }

  pause() {
    this.paused = true;
  }

  resume() {
    this.paused = false;
    this.render();
  }

  clip(text, maxLength) {
    const value = String(text || "");
    if (value.length <= maxLength) {
      return value;
    }
    return `${value.slice(0, Math.max(0, maxLength - 3))}...`;
  }

  formatCell(text, width) {
    const value = this.clip(String(text || "-"), width);
    return value.padEnd(width, " ");
  }

  parseSelectedAccountName() {
    const raw = String(this.state.selectedAccount || "").trim();
    const indexPrefix = raw.match(/^\[\d+\/\d+\]\s*(.+)$/);
    const value = indexPrefix ? indexPrefix[1] : raw;
    const open = value.indexOf(" (");
    if (open > 0) {
      return value.slice(0, open).trim();
    }
    return value;
  }

  mapPhaseToStatus(phase) {
    const key = String(phase || "").toLowerCase();
    const map = {
      init: "IDLE",
      preflight: "SYNC",
      "vercel-refresh": "SECURITY",
      "browser-checkpoint": "SECURITY",
      "session-reuse": "SESSION",
      "otp-send": "OTP-WAIT",
      "otp-verify": "OTP-VERIFY",
      "otp-fallback": "OTP-FALLBACK",
      "sync-onboard": "SYNC",
      "sync-bridge": "SYNC",
      "finalize-returning": "FINALIZE",
      balances: "IDLE",
      send: "SEND",
      cooldown: "COOLDOWN",
      completed: "IDLE",
      "session-reused": "IDLE",
      "dry-run": "DRY-RUN"
    };
    return map[key] || String(phase || "-").toUpperCase();
  }

  parseBalanceFields() {
    const raw = String(this.state.balance || "");
    const matchCc = raw.match(/CC=([^|]+)/i);
    // Extract USDC Base from balance string
    const matchUsdc = raw.match(/USDC=([^|]+)/i);
    return {
      cc: matchCc ? String(matchCc[1]).trim() : "-",
      usdc: matchUsdc ? String(matchUsdc[1]).trim() : "-"
    };
  }

  syncSelectedAccountSnapshot() {
    const selected = this.parseSelectedAccountName();
    if (!selected || selected === "-") {
      return;
    }

    const prev = isObject(this.accountSnapshots[selected]) ? this.accountSnapshots[selected] : {};
    const balances = this.parseBalanceFields();
    const currentSend = String(this.state.send || "-").trim();
    const currentReward = String(this.state.reward || "-").trim();
    const currentRewardsBucket = String(this.state.rewardsBucket || "-").trim();
    const currentRewardsThisWeek = String(this.state.rewardsThisWeek || "-").trim();
    const currentRewardsDiff = String(this.state.rewardsDiff || "-").trim();
    // Use per-account stats for TX Progress column (not global state)
    const accountStats = getPerAccountTxStats(selected);
    const currentProgress = `${accountStats.total} (ok:${accountStats.ok}|fail:${accountStats.fail})`;

    this.accountSnapshots[selected] = {
      status: this.mapPhaseToStatus(this.state.phase),
      cc: balances.cc !== "-" ? balances.cc : String(prev.cc || "-"),
      usdc: balances.usdc !== "-" ? balances.usdc : String(prev.usdc || "-"),
      progress: currentProgress !== "-" ? currentProgress : String(prev.progress || "-"),
      send: currentSend !== "-" ? currentSend : String(prev.send || "-"),
      reward: currentReward !== "-" ? currentReward : String(prev.reward || "-"),
      rewardsBucket: currentRewardsBucket !== "-" ? currentRewardsBucket : String(prev.rewardsBucket || "-"),
      rewardsThisWeek: currentRewardsThisWeek !== "-" ? currentRewardsThisWeek : String(prev.rewardsThisWeek || "-"),
      rewardsDiff: currentRewardsDiff !== "-" ? currentRewardsDiff : String(prev.rewardsDiff || "-")
    };
  }

  formatRewardsThisWeek(accountName, snapshotFallback) {
    const entry = getAccountRewardsThisWeek(accountName);
    if (isObject(entry)) {
      const ccLabel = Number.isFinite(entry.cc) ? entry.cc.toFixed(2) : "?";
      const usdLabel = Number.isFinite(entry.usd) ? entry.usd.toFixed(2) : "?";
      return `${ccLabel} CC ($${usdLabel})`;
    }
    const fallback = String(snapshotFallback || "-");
    return fallback || "-";
  }

  formatRewardsDiff(accountName, snapshotFallback) {
    const diff = getAccountRewardsDiff(accountName);
    if (isObject(diff)) {
      const ccPart = `${diff.cc >= 0 ? "+" : ""}${diff.cc.toFixed(2)} CC`;
      const usdPart = `${diff.usd >= 0 ? "+" : ""}$${diff.usd.toFixed(2)}`;
      return `${ccPart} (${usdPart})`;
    }
    const fallback = String(snapshotFallback || "-");
    return fallback || "-";
  }

  parseAccountRows() {
    const selected = this.parseSelectedAccountName();
    const balances = this.parseBalanceFields();
    const raw = String(this.state.accounts || "").trim();
    const chunks = raw && raw !== "-" ? raw.split("|") : [];
    const rows = [];

    for (const chunk of chunks) {
      const text = chunk.trim();
      if (!text) {
        continue;
      }

      const marked = text.startsWith("*");
      const cleaned = marked ? text.slice(1).trim() : text;
      const match = cleaned.match(/^([^\(]+)\(([^\)]+)\)$/);
      const name = match ? String(match[1]).trim() : cleaned;
      const token = match ? String(match[2]).trim() : "-";
      const isSelected = name === selected || (marked && selected === "-");
      const snapshot = isObject(this.accountSnapshots[name]) ? this.accountSnapshots[name] : {};
      // Use per-account stats for TX Progress column (not global state)
      const accountStats = getPerAccountTxStats(name);
      const currentProgress = `${accountStats.total} (ok:${accountStats.ok}|fail:${accountStats.fail})`;

      rows.push({
        name,
        status: isSelected
          ? this.mapPhaseToStatus(this.state.phase)
          : (snapshot.status || (token && token !== "-" ? String(token).toUpperCase() : "IDLE")),
        token,
        active: isSelected,
        cc: isSelected
          ? (balances.cc !== "-" ? balances.cc : String(snapshot.cc || "-"))
          : String(snapshot.cc || "-"),
        usdc: isSelected
          ? (balances.usdc !== "-" ? balances.usdc : String(snapshot.usdc || "-"))
          : String(snapshot.usdc || "-"),
        progress: isSelected ? currentProgress : String(snapshot.progress || "-"),
        send: isSelected
          ? (String(this.state.send || "-") !== "-" ? String(this.state.send || "-") : String(snapshot.send || "-"))
          : String(snapshot.send || "-"),
        reward: isSelected
          ? (String(this.state.reward || "-") !== "-" ? String(this.state.reward || "-") : String(snapshot.reward || "-"))
          : String(snapshot.reward || "-"),
        rewardsBucket: isSelected
          ? (String(this.state.rewardsBucket || "-") !== "-" ? String(this.state.rewardsBucket || "-") : String(snapshot.rewardsBucket || "-"))
          : String(snapshot.rewardsBucket || "-"),
        rewardsThisWeek: this.formatRewardsThisWeek(name, snapshot.rewardsThisWeek),
        rewardsDiff: this.formatRewardsDiff(name, snapshot.rewardsDiff)
      });
    }

    if (rows.length === 0 && selected && selected !== "-") {
      const snapshot = isObject(this.accountSnapshots[selected]) ? this.accountSnapshots[selected] : {};
      // Use per-account stats for TX Progress column (not global state)
      const accountStats = getPerAccountTxStats(selected);
      const currentProgress = `${accountStats.total} (ok:${accountStats.ok}|fail:${accountStats.fail})`;
      rows.push({
        name: selected,
        status: this.mapPhaseToStatus(this.state.phase),
        token: "-",
        active: true,
        cc: balances.cc !== "-" ? balances.cc : String(snapshot.cc || "-"),
        usdc: balances.usdc !== "-" ? balances.usdc : String(snapshot.usdc || "-"),
        progress: currentProgress,
        send: String(this.state.send || "-") !== "-" ? String(this.state.send || "-") : String(snapshot.send || "-"),
        reward: String(this.state.reward || "-") !== "-" ? String(this.state.reward || "-") : String(snapshot.reward || "-"),
        rewardsBucket: String(this.state.rewardsBucket || "-") !== "-" ? String(this.state.rewardsBucket || "-") : String(snapshot.rewardsBucket || "-"),
        rewardsThisWeek: this.formatRewardsThisWeek(selected, snapshot.rewardsThisWeek),
        rewardsDiff: this.formatRewardsDiff(selected, snapshot.rewardsDiff)
      });
    }

    return rows;
  }

  render() {
    if (!this.enabled) {
      return;
    }
    this._lastRenderMs = Date.now();

    const now = new Date().toLocaleString("id-ID", {
      hour12: false,
      timeZone: "Asia/Jakarta"
    });
    const rows = this.parseAccountRows();
    const W = Math.max(40, Number(process.stdout.columns || 48));
    const modeLabel = String(this.state.mode || "-").toUpperCase();

    // ANSI helpers
    const C = {
      rst: "\x1b[0m", bold: "\x1b[1m", dim: "\x1b[2m",
      cyan: "\x1b[36m", green: "\x1b[32m", yellow: "\x1b[33m",
      red: "\x1b[31m", magenta: "\x1b[35m", white: "\x1b[97m",
      blue: "\x1b[34m",
    };

    // Strip ANSI codes for visible-length calculation
    const stripAnsi = (s) => String(s).replace(/\x1b\[[0-9;]*m/g, "");

    // Fit text to exact visible width, ANSI-aware truncation
    const fitCell = (text, width) => {
      const str = String(text || "");
      const vis = stripAnsi(str);
      if (vis.length <= width) return str + " ".repeat(width - vis.length);
      let result = "", vc = 0, inEsc = false;
      for (let i = 0; i < str.length && vc < width - 1; i++) {
        if (str[i] === "\x1b") { inEsc = true; result += str[i]; }
        else if (inEsc) { result += str[i]; if (str[i] === "m") inEsc = false; }
        else { result += str[i]; vc++; }
      }
      return result + "…" + C.rst;
    };

    // ── Panel widths ──
    const LW = Math.max(24, Math.floor(W * 0.62));
    const RW = W - LW - 1; // 1 char for │ divider

    // ════════════════════════════════════
    // BUILD LEFT PANEL (header + accounts)
    // ════════════════════════════════════
    const L = [];
    const timeStr = (now.split(" ").pop() || now).slice(0, 8);

    L.push(`${C.bold}${C.cyan}RootsFi V15.3${C.rst} ${C.dim}${timeStr}${C.rst}`);
    L.push(`${C.dim}${rows.length} Akun ${modeLabel}${C.rst}`);

    const uptimeLabel = getGlobalUptimeLabel();
    const phColor = {
      send: C.green, cooldown: C.yellow, init: C.dim,
      "browser-checkpoint": C.magenta, "session-reuse": C.cyan
    }[String(this.state.phase || "").toLowerCase()] || C.white;
    L.push(
      `${phColor}▸${String(this.state.phase || "-").toUpperCase().slice(0, 7)}${C.rst}` +
      (uptimeLabel ? ` ${C.dim}${uptimeLabel}${C.rst}` : "")
    );

    if (String(this.state.mode || "").toLowerCase() === "balance-only") {
      const initCc = getTotalInitialCcBalance();
      L.push(`${C.dim}Init ${C.rst}${initCc.toFixed(2)}`);
    }

    L.push(`${C.dim}${"─".repeat(LW)}${C.rst}`);

    // Account rows — 1 line each: marker+name status cc tier Δdiff
    const nameW = Math.min(8, Math.floor(LW * 0.28));
    const stW = 4;

    // Format CC to max 2 decimal places, compact
    const fmtCc = (raw) => {
      const n = Number(raw);
      if (!Number.isFinite(n)) return String(raw || "-");
      if (n >= 1000) return n.toFixed(0);
      if (n >= 100) return n.toFixed(1);
      return n.toFixed(2);
    };

    // Tier abbreviation: UNR, NEW, ADV, PRO, ELI
    const tierAbbr = (name) => {
      const t = String(tierDisplayNameByAccount.get(name) || "?").toLowerCase();
      if (t.startsWith("elite")) return "ELI";
      if (t.startsWith("pro")) return "PRO";
      if (t.startsWith("adv")) return "ADV";
      if (t.startsWith("new")) return "NEW";
      if (t.startsWith("unr")) return "UNR";
      return " ? ";
    };

    // Compact reward diff: "+1.2" or "-0.3" or "-"
    const fmtDiff = (accountName) => {
      const diff = getAccountRewardsDiff(accountName);
      if (!isObject(diff) || !Number.isFinite(diff.cc)) return "  -";
      const v = diff.cc;
      const s = `${v >= 0 ? "+" : ""}${v.toFixed(1)}`;
      return s.padStart(5);
    };

    // Score number + band label from reward string like "85/100 Strong"
    const parseScore = (reward) => {
      const r = String(reward || "-").trim();
      if (r === "-") return { num: " -", band: " - " };
      const numMatch = r.match(/(\d+)/);
      const num = numMatch ? numMatch[1].padStart(2) : " -";
      // Band: extract word after "N/100 " — e.g. Strong, High, Stable, Low
      const bandMatch = r.match(/\d+\/\d+\s+(\w+)/);
      let band = " - ";
      if (bandMatch) {
        const b = bandMatch[1].toLowerCase();
        if (b.startsWith("str")) band = "Str";
        else if (b.startsWith("hi")) band = "Hi ";
        else if (b.startsWith("sta")) band = "Stb";
        else if (b.startsWith("lo")) band = "Lo ";
        else if (b.startsWith("ver")) band = "VLo";
        else band = bandMatch[1].slice(0, 3);
      } else if (r.startsWith("LOW")) {
        band = "Lo ";
      } else if (r.startsWith("SKIP")) {
        band = "Skp";
      }
      return { num, band };
    };

    if (rows.length === 0) {
      L.push(`${C.dim}(no accts)${C.rst}`);
    } else {
      // Column header: Akun | Sts | CC | USDC | ETH | mk | tk | sw | rnd | cd | pts | pen
      const ccW = 6;
      const uxW = 6;
      const ethW = 7;
      const mkW = 3;
      const tkW = 3;
      const swW = 4; // e.g. "5/5 "
      const rndW = 3;
      const cdW = 7; // e.g. "59m30s" / "-"
      const ptsW = 4;
      const penW = 5;

      L.push(
        `${C.dim} ${"Akun".padEnd(nameW)} ` +
        `${"Sts".padEnd(stW)} ` +
        `${"CC".padEnd(ccW)} ` +
        `${"USDC".padEnd(uxW)} ` +
        `${"ETH".padEnd(ethW)} ` +
        `${"mk".padEnd(mkW)} ` +
        `${"tk".padEnd(tkW)} ` +
        `${"sw".padEnd(swW)} ` +
        `${"rnd".padEnd(rndW)} ` +
        `${"cd".padEnd(cdW)} ` +
        `${"pts".padEnd(ptsW)} ` +
        `${"pen".padEnd(penW)}${C.rst}`
      );

      const stMap = {
        IDLE: "IDLE", SEND: "SEND", COOLDOWN: "COOL",
        SECURITY: "SECU", SESSION: "SESS", "OTP-WAIT": "OTP!",
        "OTP-VERIFY": "OTPV", SYNC: "SYNC", "DRY-RUN": "DRY ",
        FINALIZE: "DONE", QUEUE: "QUE ",
        // MT-specific (4-char fits stW=4)
        TAKE: "TAKE", MAKE: "MAKE", WAIT: "WAIT", LOCK: "LOCK",
        CAP: "CAP ", STL: "STL ", OPN: "OPN ", PTK: "PTK ", PMK: "PMK ",
        "PEND-TK": "PTK ", "PEND-MK": "PMK ", "SETTLE": "STL ", "OPEN": "OPN "
      };
      const stColorMap = {
        IDLE: C.dim, SEND: C.green, COOL: C.yellow,
        SECU: C.magenta, SESS: C.cyan, "OTP!": C.red,
        OTPV: C.red, SYNC: C.blue, "QUE ": C.dim,
        "DRY ": C.yellow, DONE: C.green,
        TAKE: C.green, MAKE: C.cyan, WAIT: C.dim, LOCK: C.yellow,
        "CAP ": C.red, "STL ": C.yellow, "OPN ": C.yellow,
        "PTK ": C.magenta, "PMK ": C.magenta
      };

      // Helper untuk pad string visible-width (mengabaikan ANSI escape).
      const padCell = (raw, w) => {
        const s = String(raw == null ? "-" : raw);
        if (s.length >= w) return s.slice(0, w);
        return s + " ".repeat(w - s.length);
      };

      for (const row of rows) {
        const stRaw = stMap[row.status] || String(row.status || "").slice(0, stW);
        const st = padCell(stRaw, stW);
        const stColor = stColorMap[stRaw] || stColorMap[st] || C.white;
        const ccVal = padCell(fmtCc(row.cc), ccW);
        const uxVal = padCell(fmtCc(row.usdc), uxW);
        const marker = row.active ? `${C.bold}>${C.rst}` : " ";

        const snapshot = isObject(this.accountSnapshots[row.name]) ? this.accountSnapshots[row.name] : {};
        const mkRaw = snapshot.mk;
        const tkRaw = snapshot.tk;
        let mkLbl, tkLbl;
        if (mkRaw === undefined && tkRaw === undefined) {
          const txStats = getPerAccountTxStats(row.name);
          mkLbl = padCell(txStats.ok || 0, mkW);
          tkLbl = padCell(txStats.fail || 0, tkW);
        } else {
          mkLbl = padCell(Number(mkRaw) || 0, mkW);
          tkLbl = padCell(Number(tkRaw) || 0, tkW);
        }

        const ethRaw = snapshot.eth;
        const ethLabel = padCell(ethRaw == null || ethRaw === "-" ? "-" : ethRaw, ethW);

        const ptsRaw = snapshot.pts;
        const ptsLabel = padCell(ptsRaw == null || ptsRaw === "-" ? "-" : ptsRaw, ptsW);

        const penRaw = snapshot.pen;
        const penNum = Number(penRaw);
        const penText = Number.isFinite(penNum) ? (penNum > 0 ? `-${penNum}` : "0") : "-";
        const penLabel = padCell(penText, penW);
        const penColor = Number.isFinite(penNum) && penNum > 0 ? C.red : C.dim;

        const swLabel = padCell(snapshot.sw == null ? "-" : snapshot.sw, swW);
        const rndLabel = padCell(snapshot.rnd == null ? "-" : snapshot.rnd, rndW);
        const cdLabel = padCell(snapshot.cd == null ? "-" : snapshot.cd, cdW);

        const nameLbl = padCell(this.clip(row.name, nameW), nameW);

        L.push(
          `${marker}${nameLbl} ` +
          `${stColor}${st}${C.rst} ` +
          `${C.cyan}${ccVal}${C.rst} ` +
          `${C.yellow}${uxVal}${C.rst} ` +
          `${C.blue}${ethLabel}${C.rst} ` +
          `${C.green}${mkLbl}${C.rst} ` +
          `${C.cyan}${tkLbl}${C.rst} ` +
          `${C.green}${swLabel}${C.rst} ` +
          `${C.yellow}${rndLabel}${C.rst} ` +
          `${C.magenta}${cdLabel}${C.rst} ` +
          `${C.magenta}${ptsLabel}${C.rst} ` +
          `${penColor}${penLabel}${C.rst}`
        );
      }
    }

    L.push(`${C.dim}${"─".repeat(LW)}${C.rst}`);
    const capLabel = hourlyCapSource === "server" ? "S" : (hourlyCapSource === "config" ? "C" : "A");
    L.push(
      `${C.dim}${this.state.minDelay || "?"}s-${this.state.maxDelay || "?"}s ` +
      `${HOURLY_MAX_TX_PER_ACCOUNT}/h(${capLabel})${C.rst}`
    );

    // ════════════════════════════════
    // BUILD RIGHT PANEL (logs)
    // ════════════════════════════════
    const R = [];
    R.push(`${C.dim}── Log (${this.logLines}) ──${C.rst}`);
    R.push(`${C.dim}${"─".repeat(RW)}${C.rst}`);

    const logMsgW = Math.max(8, RW - 6);
    if (this.logs.length === 0) {
      R.push(`${C.dim}(empty)${C.rst}`);
    } else {
      // Only show last this.logLines entries (respects config.ui.logLines)
      const visibleLogs = this.logs.slice(-this.logLines);
      for (const log of visibleLogs) {
        const lc = log.level === "ERROR" ? C.red
          : (log.level === "WARN" ? C.yellow : C.dim);
        const ts = log.time.slice(0, 5);
        const msg = String(log.message || "");
        // Wrap long messages to multiple lines instead of truncating
        if (msg.length <= logMsgW) {
          R.push(`${C.dim}${ts}${C.rst}${lc}${msg}${C.rst}`);
        } else {
          // First line with timestamp
          R.push(`${C.dim}${ts}${C.rst}${lc}${msg.slice(0, logMsgW)}${C.rst}`);
          // Continuation lines (indented, no timestamp)
          let pos = logMsgW;
          const contW = RW - 1; // full width minus 1 indent space
          while (pos < msg.length) {
            R.push(`${lc} ${msg.slice(pos, pos + contW)}${C.rst}`);
            pos += contW;
          }
        }
      }
    }

    // ════════════════════════════════
    // MERGE LEFT + RIGHT into output
    // ════════════════════════════════
    const maxH = Math.max(L.length, R.length);
    while (L.length < maxH) L.push("");
    while (R.length < maxH) R.push("");

    const output = [];
    output.push(C.dim + "━".repeat(W) + C.rst);
    for (let i = 0; i < maxH; i++) {
      output.push(
        `${fitCell(L[i], LW)}${C.dim}│${C.rst}${fitCell(R[i], RW)}`
      );
    }
    output.push(C.dim + "━".repeat(W) + C.rst);

    process.stdout.write(`\x1b[2J\x1b[H${output.join("\n")}\n`);
  }
}

function isObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function clampToNonNegativeInt(value, fallback) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed) || parsed < 0) {
    return fallback;
  }
  return Math.floor(parsed);
}

function randomIntInclusive(min, max) {
  const lo = Math.ceil(min);
  const hi = Math.floor(max);
  return Math.floor(Math.random() * (hi - lo + 1)) + lo;
}

// Triangular distribution: most delays cluster near the center of the range,
// with occasional shorter/longer values, mimicking human timing patterns.
function humanLikeDelay(minSec, maxSec) {
  const range = maxSec - minSec;
  if (range <= 0) return Math.round(minSec);
  const r1 = Math.random();
  const r2 = Math.random();
  const centered = (r1 + r2) / 2;
  return Math.round(minSec + (centered * range));
}

function shuffleArray(items) {
  const array = Array.isArray(items) ? [...items] : [];
  for (let i = array.length - 1; i > 0; i -= 1) {
    const j = randomIntInclusive(0, i);
    const temp = array[i];
    array[i] = array[j];
    array[j] = temp;
  }
  return array;
}

function withAccountTag(accountLogTag, message) {
  if (!accountLogTag) {
    return message;
  }
  return `[${accountLogTag}] ${message}`;
}

function maskSecret(value, head = 4, tail = 4) {
  const text = String(value || "");
  if (!text) {
    return "<empty>";
  }
  if (text.length <= head + tail) {
    return "*".repeat(text.length);
  }
  return `${text.slice(0, head)}...${text.slice(-tail)}`;
}

function maskEmail(email) {
  const value = String(email || "").trim();
  if (!value.includes("@")) {
    return maskSecret(value, 2, 2);
  }

  const [local, domain] = value.split("@");
  const localMasked = local.length <= 2 ? `${local[0] || "*"}*` : `${local.slice(0, 2)}***${local.slice(-1)}`;
  return `${localMasked}@${domain}`;
}

function parseArgs(argv) {
  const args = {
    configFile: DEFAULT_CONFIG_FILE,
    accountsFile: DEFAULT_ACCOUNTS_FILE,
    tokensFile: DEFAULT_TOKENS_FILE,
    accountName: null,
    sendCcAmount: null,
    sendTo: null,
    sendIdempotencyKey: null,
    dryRun: false,
    noDashboard: false,
    help: false
  };

  for (let i = 0; i < argv.length; i += 1) {
    const token = argv[i];

    if (token === "-h" || token === "--help") {
      args.help = true;
      continue;
    }

    if (token === "--dry-run") {
      args.dryRun = true;
      continue;
    }

    if (token === "--no-dashboard") {
      args.noDashboard = true;
      continue;
    }

    if (token.startsWith("--config=")) {
      args.configFile = token.slice("--config=".length).trim();
      continue;
    }

    if (token === "--config") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --config");
      }
      args.configFile = argv[i + 1].trim();
      i += 1;
      continue;
    }

    if (token.startsWith("--accounts=")) {
      args.accountsFile = token.slice("--accounts=".length).trim();
      continue;
    }

    if (token === "--accounts") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --accounts");
      }
      args.accountsFile = argv[i + 1].trim();
      i += 1;
      continue;
    }

    if (token.startsWith("--tokens=")) {
      args.tokensFile = token.slice("--tokens=".length).trim();
      continue;
    }

    if (token === "--tokens") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --tokens");
      }
      args.tokensFile = argv[i + 1].trim();
      i += 1;
      continue;
    }

    if (token.startsWith("--account=")) {
      args.accountName = token.slice("--account=".length).trim();
      continue;
    }

    if (token === "--account") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --account");
      }
      args.accountName = argv[i + 1].trim();
      i += 1;
      continue;
    }

    if (token.startsWith("--send-cc=")) {
      args.sendCcAmount = token.slice("--send-cc=".length).trim();
      continue;
    }

    if (token === "--send-cc") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --send-cc");
      }
      args.sendCcAmount = argv[i + 1].trim();
      i += 1;
      continue;
    }

    if (token.startsWith("--send-to=")) {
      args.sendTo = token.slice("--send-to=".length).trim();
      continue;
    }

    if (token === "--send-to") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --send-to");
      }
      args.sendTo = argv[i + 1].trim();
      i += 1;
      continue;
    }

    if (token.startsWith("--send-idempotency-key=")) {
      args.sendIdempotencyKey = token.slice("--send-idempotency-key=".length).trim();
      continue;
    }

    if (token === "--send-idempotency-key") {
      if (!argv[i + 1]) {
        throw new Error("Missing value for --send-idempotency-key");
      }
      args.sendIdempotencyKey = argv[i + 1].trim();
      i += 1;
      continue;
    }

    throw new Error(`Unknown argument: ${token}`);
  }

  return args;
}

function printHelp() {
  console.log(`RootsFi API Login + Balance Bot (API-only)

Usage:
  node index.js [options]

Options:
  --config <path>      Config file (default: config.json)
  --accounts <path>    Accounts file (default: accounts.json)
  --tokens <path>      Generated token storage (default: tokens.json)
  --account <name>     Account name from accounts.json
  --send-cc <amount>   Send CC amount (example: 10.25)
  --send-to <target>   Recipient alias or canton address
  --send-idempotency-key <key>
                       Optional idempotency key for transfer request
  --no-dashboard       Disable pinned dashboard UI
  --dry-run            Validate files and print summary only
  -h, --help           Show this help

Environment overrides:
  ROOTSFI_EMAIL        Override email from accounts.json
  ROOTSFI_NO_DASHBOARD Set to 1 to disable dashboard
  ROOTSFI_SEND_CC      Send CC amount
  ROOTSFI_SEND_TO      Recipient alias or canton address
  ROOTSFI_SEND_IDEMPOTENCY_KEY
                       Transfer idempotency key override
`);
}

async function readJson(filePath, label) {
  let text;
  try {
    text = await fs.readFile(filePath, "utf8");
  } catch (error) {
    if (error && error.code === "ENOENT") {
      throw new Error(`${label} file not found: ${filePath}`);
    }
    throw error;
  }

  try {
    return JSON.parse(text);
  } catch (error) {
    throw new Error(`Invalid JSON in ${label} file ${filePath}: ${error.message}`);
  }
}

async function readOptionalJson(filePath, label) {
  try {
    const text = await fs.readFile(filePath, "utf8");
    return JSON.parse(text);
  } catch (error) {
    if (error && error.code === "ENOENT") {
      return null;
    }
    if (error instanceof SyntaxError) {
      throw new Error(`Invalid JSON in ${label} file ${filePath}: ${error.message}`);
    }
    throw error;
  }
}

function generateBrowserHeaderProfile(deviceId) {
  // ============================================================================
  // DIVERSE FINGERPRINT GENERATOR
  // ============================================================================
  // Creates realistic, unique browser profiles per account to avoid fingerprint
  // correlation between accounts. Uses deviceId as deterministic seed so the
  // same account always gets the same fingerprint across restarts.
  //
  // Diversified:
  //   - Platform (Windows / macOS / Linux)
  //   - Chrome version + full build number
  //   - Accept-Language (varied locales)
  //   - sec-ch-ua / sec-ch-ua-platform (matching platform)
  // ============================================================================

  // Deterministic hash from deviceId for stable per-account randomization
  const hashBytes = crypto.createHash("sha256").update(String(deviceId || "")).digest();
  const seed = (idx) => hashBytes[idx % hashBytes.length];

  // --- Platform ---
  const platforms = [
    {
      platform: "macOS",
      uaPlatform: "(Macintosh; Intel Mac OS X 10_15_7)",
      secChUaPlatform: '"macOS"',
      secChUaMobile: "?0"
    },
    {
      platform: "Windows",
      uaPlatform: "(Windows NT 10.0; Win64; x64)",
      secChUaPlatform: '"Windows"',
      secChUaMobile: "?0"
    },
    {
      platform: "Linux",
      uaPlatform: "(X11; Linux x86_64)",
      secChUaPlatform: '"Linux"',
      secChUaMobile: "?0"
    }
  ];
  const platformIdx = seed(0) % platforms.length;
  const chosenPlatform = platforms[platformIdx];

  // --- Chrome version (realistic major + full build) ---
  const chromeVersions = [
    { major: 131, build: "0.6778.140" },
    { major: 132, build: "0.6834.110" },
    { major: 133, build: "0.6943.127" },
    { major: 134, build: "0.6998.89" },
    { major: 135, build: "0.7049.85" },
    { major: 136, build: "0.7103.114" },
    { major: 137, build: "0.7151.70" },
    { major: 138, build: "0.7204.93" },
    { major: 139, build: "0.7258.68" },
    { major: 140, build: "0.7310.105" },
    { major: 141, build: "0.7365.81" },
    { major: 142, build: "0.7420.97" },
    { major: 143, build: "0.7473.63" },
    { major: 144, build: "0.7528.109" },
    { major: 145, build: "0.7582.72" },
    { major: 146, build: "0.7636.88" }
  ];
  const versionIdx = seed(1) % chromeVersions.length;
  const chosenVersion = chromeVersions[versionIdx];
  const chromeFull = `${chosenVersion.major}.${chosenVersion.build}`;

  // --- Accept-Language (diverse locale pools) ---
  const languages = [
    "en-US,en;q=0.9",
    "en-US,en;q=0.9,id;q=0.8",
    "en-GB,en;q=0.9,en-US;q=0.8",
    "en-US,en;q=0.9,de;q=0.7",
    "en,en-US;q=0.9",
    "en-US,en;q=0.9,fr;q=0.7",
    "en-US,en;q=0.9,ja;q=0.8",
    "en-US,en;q=0.9,es;q=0.8",
    "en-US,en;q=0.8",
    "en-US,en;q=0.9,pt;q=0.7",
    "en-US,en;q=0.9,ko;q=0.7",
    "en-US,en;q=0.9,zh-CN;q=0.7",
    "en-US,en;q=0.9,nl;q=0.8",
    "en-US,en;q=0.9,ru;q=0.7"
  ];
  const langIdx = seed(2) % languages.length;
  const chosenLang = languages[langIdx];

  // --- Not-A.Brand version (varies between Chrome releases) ---
  const brandVersions = [
    { brand: "Not-A.Brand", version: "24" },
    { brand: "Not/A)Brand", version: "8" },
    { brand: "Not_A Brand", version: "99" }
  ];
  const brandIdx = seed(3) % brandVersions.length;
  const chosenBrand = brandVersions[brandIdx];

  const secChUa = `"Chromium";v="${chosenVersion.major}", "${chosenBrand.brand}";v="${chosenBrand.version}", "Google Chrome";v="${chosenVersion.major}"`;

  const userAgent =
    `Mozilla/5.0 ${chosenPlatform.uaPlatform} AppleWebKit/537.36 ` +
    `(KHTML, like Gecko) Chrome/${chromeFull} Safari/537.36`;

  return {
    userAgent,
    acceptLanguage: chosenLang,
    sendBrowserClientHints: true,
    secChUa,
    secChUaMobile: chosenPlatform.secChUaMobile,
    secChUaPlatform: chosenPlatform.secChUaPlatform,
    secFetchDest: "empty",
    secFetchMode: "cors",
    secFetchSite: "same-origin",
    priority: "u=1, i",
    extra: {
      "x-device-id": deviceId
    }
  };
}

function normalizeTokenProfile(rawProfile) {
  const input = isObject(rawProfile) ? rawProfile : {};
  const deviceId = String(input.deviceId || crypto.randomUUID()).trim() || crypto.randomUUID();
  const generatedHeaders = generateBrowserHeaderProfile(deviceId);
  const headersInput = isObject(input.headers) ? input.headers : {};
  const securityInput = isObject(input.security) ? input.security : {};
  const now = new Date().toISOString();

  return {
    cookie: String(input.cookie || "").trim(),
    deviceId,
    headers: {
      // Generated fingerprint headers ALWAYS take priority over persisted.
      // This ensures diverse per-account fingerprints are applied on every startup,
      // even if tokens.json has stale identical headers from a previous version.
      ...headersInput,
      ...generatedHeaders,
      extra: {
        ...(isObject(headersInput.extra) ? headersInput.extra : {}),
        ...generatedHeaders.extra,
        "x-device-id": deviceId
      }
    },
    security: {
      strategy: "browser-challenge-cookie-reuse",
      antiBotNonce: String(securityInput.antiBotNonce || crypto.randomBytes(16).toString("hex")),
      createdAt: String(securityInput.createdAt || now),
      updatedAt: String(securityInput.updatedAt || now),
      lastVercelRefreshAt: String(securityInput.lastVercelRefreshAt || "").trim(),
      hasSecurityCookie: Boolean(securityInput.hasSecurityCookie),
      hasSessionCookie: Boolean(securityInput.hasSessionCookie),
      checkpointRefreshCount: clampToNonNegativeInt(
        securityInput.checkpointRefreshCount,
        0
      )
    }
  };
}

function normalizeTokens(rawTokens, accountsConfig) {
  const raw = isObject(rawTokens) ? rawTokens : {};
  const rawAccounts = isObject(raw.accounts) ? raw.accounts : {};
  const accountMap = {};

  for (const account of accountsConfig.accounts) {
    accountMap[account.name] = normalizeTokenProfile(rawAccounts[account.name]);
  }

  for (const [accountName, profile] of Object.entries(rawAccounts)) {
    if (!Object.prototype.hasOwnProperty.call(accountMap, accountName)) {
      accountMap[accountName] = normalizeTokenProfile(profile);
    }
  }

  const result = {
    version: 1,
    updatedAt: String(raw.updatedAt || new Date().toISOString()),
    accounts: accountMap
  };

  // TX progress no longer persisted; drop any legacy field from older runs.
  if (isObject(raw.dailyProgress)) {
    // intentionally discarded
  }

  return result;
}

function applyTokenProfileToConfig(config, profile) {
  const tokenHeaders = isObject(profile.headers) ? profile.headers : {};

  config.headers = {
    ...config.headers,
    ...tokenHeaders,
    extra: {
      ...(isObject(tokenHeaders.extra) ? tokenHeaders.extra : {}),
      "x-device-id": profile.deviceId
    },
    cookie: String(profile.cookie || "").trim()
  };
}

function applyClientStateToTokenProfile(profile, client, checkpointRefreshCount, lastVercelRefreshAt) {
  const nextProfile = normalizeTokenProfile(profile);
  const now = new Date().toISOString();
  const currentCookie = client.getCookieHeader();

  if (currentCookie) {
    nextProfile.cookie = currentCookie;
  }

  nextProfile.headers.extra = {
    ...(isObject(nextProfile.headers.extra) ? nextProfile.headers.extra : {}),
    "x-device-id": nextProfile.deviceId
  };

  nextProfile.security = {
    ...nextProfile.security,
    updatedAt: now,
    lastVercelRefreshAt:
      String(lastVercelRefreshAt || nextProfile.security.lastVercelRefreshAt || "").trim(),
    hasSecurityCookie: client.hasSecurityCookie(),
    hasSessionCookie: client.hasAccountSessionCookie(),
    checkpointRefreshCount:
      clampToNonNegativeInt(nextProfile.security.checkpointRefreshCount, 0) +
      clampToNonNegativeInt(checkpointRefreshCount, 0)
  };

  return nextProfile;
}

async function saveTokens(tokensPath, tokensState) {
  const payload = {
    ...tokensState,
    version: 1,
    updatedAt: new Date().toISOString()
  };

  await fs.writeFile(tokensPath, JSON.stringify(payload, null, 2), "utf8");
}

let tokensSaveQueue = Promise.resolve();

async function saveTokensSerial(tokensPath, tokensState) {
  tokensSaveQueue = tokensSaveQueue.then(() => saveTokens(tokensPath, tokensState));
  return tokensSaveQueue;
}

// ============================================================================
// Daily TX Progress Persistence
// Tracks completed rounds per UTC date so re-runs continue where they left off.
// ============================================================================

function getTodayUTCDate() {
  return new Date().toISOString().slice(0, 10); // "YYYY-MM-DD"
}

// TX progress persistence removed: bot always starts from TX 0 on re-run.
// Stubs kept so existing call sites do not need to change.
function loadDailyProgress() {
  return { date: getTodayUTCDate(), completedRounds: 0, completedTxTotal: 0, perAccount: {} };
}

function saveDailyProgress(tokensState) {
  if (isObject(tokensState) && "dailyProgress" in tokensState) {
    delete tokensState.dailyProgress;
  }
}

function cloneRuntimeConfig(config) {
  return {
    ...config,
    paths: { ...config.paths },
    headers: {
      ...config.headers,
      extra: {
        ...(isObject(config.headers && config.headers.extra) ? config.headers.extra : {})
      }
    },
    http: { ...config.http },
    requestPacing: { ...config.requestPacing },
    session: { ...config.session },
    send: {
      ...config.send,
      tierAmounts: {
        ...(isObject(config.send && config.send.tierAmounts) ? config.send.tierAmounts : {})
      }
    },
    ui: { ...config.ui }
  };
}

async function loadProxies(relativePath, accountNames) {
  const absolutePath = path.resolve(process.cwd(), relativePath);
  let text;

  try {
    text = await fs.readFile(absolutePath, "utf8");
  } catch (error) {
    if (error && error.code === "ENOENT") {
      console.log(`[init] Proxy file not found: ${absolutePath} — running without proxies`);
      return;
    }
    throw error;
  }

  const lines = text.split(/\r?\n/).map((l) => l.trim()).filter((l) => l && !l.startsWith("#"));
  if (lines.length === 0) {
    console.log("[init] Proxy file is empty — running without proxies");
    return;
  }

  for (let i = 0; i < accountNames.length; i++) {
    let proxyUrl = lines[i % lines.length]; // cycle proxies if fewer than accounts
    // Auto-add http:// prefix if not present (supports user:pass@host:port format)
    if (proxyUrl && !proxyUrl.startsWith("http://") && !proxyUrl.startsWith("https://")) {
      proxyUrl = `http://${proxyUrl}`;
    }
    proxyByAccount.set(accountNames[i], proxyUrl);
  }

  const uniqueProxies = new Set(lines);
  console.log(`[init] Proxies loaded: ${lines.length} lines, ${uniqueProxies.size} unique — assigned to ${accountNames.length} accounts`);
}

async function loadRecipients(relativePath) {
  const absolutePath = path.resolve(process.cwd(), relativePath);
  let text;

  try {
    text = await fs.readFile(absolutePath, "utf8");
  } catch (error) {
    if (error && error.code === "ENOENT") {
      return {
        absolutePath,
        missing: true,
        recipients: [],
        invalidLines: []
      };
    }
    throw error;
  }

  const recipients = [];
  const invalidLines = [];
  const lines = text.split(/\r?\n/);

  for (let index = 0; index < lines.length; index += 1) {
    const raw = lines[index].trim();
    if (!raw || raw.startsWith("#")) {
      continue;
    }

    const sepIndex = raw.indexOf("::");
    if (sepIndex <= 0 || sepIndex >= raw.length - 2) {
      invalidLines.push({ line: index + 1, value: raw });
      continue;
    }

    const alias = raw.slice(0, sepIndex).trim();
    const address = raw.slice(sepIndex + 2).trim();

    if (!alias || !address) {
      invalidLines.push({ line: index + 1, value: raw });
      continue;
    }

    recipients.push({ alias, address, partyId: `${alias}::${address}` });
  }

  return {
    absolutePath,
    missing: false,
    recipients,
    invalidLines
  };
}

function getRandomRecipient(recipients) {
  if (!Array.isArray(recipients) || recipients.length === 0) {
    throw new Error("No recipients available for random selection");
  }
  const index = randomIntInclusive(0, recipients.length - 1);
  return recipients[index];
}

async function promptSendMode() {
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout
  });

  try {
    console.log("\n=== RootsFi Bot - Mode ===");
    console.log("1. Send Internal     (kirim CC antar akun sendiri)");
    console.log("2. OTC Maker         (buat listing — jual CC, terima USDC)");
    console.log("3. OTC Taker         (ambil order orang lain)");
    console.log("4. OTC Maker-Taker   (siklus Maker→429→Taker)");
    console.log("5. Balance Only      (cek saldo saja)");
    console.log("");
    console.log("Mode tambahan (legacy, akses via input langsung):");
    console.log("  e = External (random dari recipient.txt)");
    console.log("  o = OTP (request OTP tiap akun & simpan sesi)");
    console.log("");

    const answer = await rl.question("Pilih mode [1/2/3/4/5]: ");
    const choice = answer.trim().toLowerCase();

    if (choice === "1") return "internal";
    if (choice === "2") return "otc-maker";
    if (choice === "3") return "otc-taker";
    if (choice === "4") return "otc-maker-taker";
    if (choice === "5") return "balance-only";
    if (choice === "e") return "external";
    if (choice === "o") return "otp";
    console.log("[warn] Pilihan tidak valid, default ke balance-only");
    return "balance-only";
  } finally {
    rl.close();
  }
}

async function promptAccountSelection(accounts) {
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout
  });

  try {
    console.log("\n=== Pilih Akun untuk TX ===");
    console.log("0. Semua akun");

    for (let i = 0; i < accounts.length; i++) {
      console.log(`${i + 1}. ${accounts[i].name} (${maskEmail(accounts[i].email)})`);
    }
    console.log("");

    const answer = await rl.question(`Pilih akun [0-${accounts.length}]: `);
    const choice = answer.trim();

    if (choice === "0" || choice === "") {
      return { mode: "all", selectedAccounts: accounts };
    }

    // Check if multiple accounts selected (comma separated)
    if (choice.includes(",")) {
      const indices = choice.split(",").map(s => parseInt(s.trim(), 10));
      const selectedAccounts = [];

      for (const idx of indices) {
        if (idx >= 1 && idx <= accounts.length) {
          selectedAccounts.push(accounts[idx - 1]);
        }
      }

      if (selectedAccounts.length === 0) {
        console.log("[warn] Tidak ada akun valid dipilih, menggunakan semua akun");
        return { mode: "all", selectedAccounts: accounts };
      }

      return { mode: "selected", selectedAccounts };
    }

    // Single account selected
    const idx = parseInt(choice, 10);
    if (idx >= 1 && idx <= accounts.length) {
      return { mode: "single", selectedAccounts: [accounts[idx - 1]] };
    }

    console.log("[warn] Pilihan tidak valid, menggunakan semua akun");
    return { mode: "all", selectedAccounts: accounts };
  } finally {
    rl.close();
  }
}

function normalizeCcAmount(rawAmount) {
  const text = String(rawAmount || "").trim();
  if (!text) {
    throw new Error("CC amount is required");
  }

  if (!/^\d+(\.\d+)?$/.test(text)) {
    throw new Error(`Invalid CC amount format: ${text}`);
  }

  const numeric = Number(text);
  if (!Number.isFinite(numeric) || numeric <= 0) {
    throw new Error(`CC amount must be greater than zero: ${text}`);
  }

  return text;
}

const TIER_KEYS = ["unranked", "newbie", "advanced", "pro", "elite"];

function resolveTierKey(tierDisplayName) {
  const key = String(tierDisplayName || "").trim().toLowerCase();
  if (TIER_KEYS.includes(key)) return key;
  return "unranked";
}

// Track tier displayName per account (from /api/rewards tierProgress.currentTierDisplayName)
const tierDisplayNameByAccount = new Map();
// Track which accounts have had /api/rewards fetched at least once in this run.
// Used to distinguish "tier not yet fetched" vs "fetched but truly unranked".
const tierFetchedByAccount = new Set();

function getAccountTierKey(_accountName) {
  // Tier system dihapus pasca announcement. Semua akun pakai range yang sama
  // (config.send.tierAmounts.unranked sudah hardcoded ke range tunggal).
  return "unranked";
}

function normalizeTierAmountsConfig(rawTierAmounts, pathLabel) {
  const defaults = INTERNAL_API_DEFAULTS.send.tierAmounts;
  const input = isObject(rawTierAmounts) ? rawTierAmounts : {};
  const result = {};
  for (const key of TIER_KEYS) {
    const tierInput = isObject(input[key]) ? input[key] : {};
    const tierDefault = isObject(defaults[key]) ? defaults[key] : defaults.unranked;
    const min = normalizeCcAmount(
      Object.prototype.hasOwnProperty.call(tierInput, "min") ? tierInput.min : tierDefault.min
    );
    const max = normalizeCcAmount(
      Object.prototype.hasOwnProperty.call(tierInput, "max") ? tierInput.max : tierDefault.max
    );
    const decimals = clampToNonNegativeInt(
      tierInput.decimals,
      clampToNonNegativeInt(tierDefault.decimals, 2)
    );
    if (decimals > 8) {
      throw new Error(`${pathLabel}.${key}.decimals must be <= 8`);
    }
    if (Number(min) > Number(max)) {
      throw new Error(`${pathLabel}.${key}.min must be <= ${pathLabel}.${key}.max`);
    }
    result[key] = { min, max, decimals };
  }
  return result;
}

function resolveAmountRangeForTier(sendPolicy, tierKey) {
  const key = resolveTierKey(tierKey);
  const tierAmounts = isObject(sendPolicy && sendPolicy.tierAmounts) ? sendPolicy.tierAmounts : null;
  if (tierAmounts && isObject(tierAmounts[key])) return tierAmounts[key];
  const defaults = INTERNAL_API_DEFAULTS.send.tierAmounts;
  return defaults[key] || defaults.unranked;
}

function generateRandomCcAmount(sendPolicyOrRange, tierKey) {
  // Accept either a sendPolicy (contains tierAmounts) or a direct {min,max,decimals} range.
  const range = (isObject(sendPolicyOrRange) &&
    Object.prototype.hasOwnProperty.call(sendPolicyOrRange, "tierAmounts"))
    ? resolveAmountRangeForTier(sendPolicyOrRange, tierKey)
    : sendPolicyOrRange;

  const decimals = clampToNonNegativeInt(range.decimals, 2);
  const factor = Math.pow(10, decimals);
  const minUnits = Math.ceil(Number(range.min) * factor);
  const maxUnits = Math.floor(Number(range.max) * factor);

  if (minUnits <= 0 || maxUnits <= 0 || minUnits > maxUnits) {
    throw new Error(`Tier amount range invalid (tier=${tierKey || "?"}, min=${range.min}, max=${range.max}). Check config.send.tierAmounts.`);
  }

  const units = randomIntInclusive(minUnits, maxUnits);
  const amount = (units / factor).toFixed(decimals);
  return normalizeCcAmount(amount);
}

function buildSendRequestsWithRandomRecipients(recipients, sendPolicy) {
  const requests = [];
  const txCount = clampToNonNegativeInt(sendPolicy.maxLoopTx || sendPolicy.maxTx, 1);

  const tierKey = resolveTierKey(sendPolicy && sendPolicy.senderTier);
  for (let index = 0; index < txCount; index += 1) {
    const amount = generateRandomCcAmount(sendPolicy, tierKey);
    const target = getRandomRecipient(recipients);

    requests.push({
      amount,
      label: target.alias,
      address: target.partyId,
      source: "external-random"
    });
  }

  return requests;
}

// Build internal recipients from accounts.json (exclude self)
function buildInternalRecipients(accounts, currentAccountName) {
  const recipients = [];

  for (const account of accounts) {
    // Skip self
    if (account.name === currentAccountName) {
      continue;
    }

    // Skip accounts without address
    const address = String(account.address || "").trim();
    if (!address) {
      continue;
    }

    recipients.push({
      alias: account.name,
      address: address,
      partyId: address // For internal, address IS the full cantonPartyId
    });
  }

  return recipients;
}

function buildSendRequests(target, sendPolicy, fixedAmountInput, idempotencySeed) {
  const requests = [];
  const txCount = clampToNonNegativeInt(sendPolicy.maxLoopTx || sendPolicy.maxTx, 1);

  const tierKey = resolveTierKey(sendPolicy && sendPolicy.senderTier);
  for (let index = 0; index < txCount; index += 1) {
    const amount = fixedAmountInput
      ? normalizeCcAmount(fixedAmountInput)
      : generateRandomCcAmount(sendPolicy, tierKey);

    let idempotencyKey = null;
    if (idempotencySeed) {
      idempotencyKey = txCount === 1 ? idempotencySeed : `${idempotencySeed}-${index + 1}`;
    }

    requests.push({
      amount,
      label: target.label,
      address: target.address,
      source: target.source,
      idempotencyKey
    });
  }

  return requests;
}

function shouldRefreshVercelCookie(lastRefreshAt, refreshEveryMinutes) {
  const minutes = clampToNonNegativeInt(refreshEveryMinutes, 0);
  if (minutes <= 0) {
    return false;
  }

  const parsed = Date.parse(String(lastRefreshAt || "").trim());
  if (!Number.isFinite(parsed)) {
    return true;
  }

  const ageMs = Date.now() - parsed;
  return ageMs >= minutes * 60 * 1000;
}

function resolveSendRecipientTarget(input, recipients) {
  const value = String(input || "").trim();
  if (!value) {
    throw new Error("Recipient target is required for send mode");
  }

  if (value.includes("::")) {
    return {
      label: value,
      address: value,
      source: "direct"
    };
  }

  const found = recipients.find((entry) => entry.alias === value);
  if (!found) {
    throw new Error(`Recipient alias '${value}' not found in recipient file`);
  }

  const resolvedPartyId = String(
    found.partyId ||
    (String(found.address || "").includes("::") ? found.address : `${found.alias}::${found.address}`)
  ).trim();

  return {
    label: found.alias,
    address: resolvedPartyId,
    source: "alias"
  };
}

function isVercelCheckpointError(error) {
  const message = String(error && error.message ? error.message : error || "");
  return message.includes("Vercel Security Checkpoint");
}

function isCheckpointOr429Error(error) {
  const status = Number(error && error.status);
  if (status === 429) {
    return true;
  }

  if (isVercelCheckpointError(error)) {
    return true;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    message.includes("http 429") ||
    message.includes("failed preflight get /onboard") ||
    message.includes("fetch failed")
  );
}

function isSessionReuseTimeoutError(error) {
  const status = Number(error && error.status);
  if (Number.isFinite(status)) {
    return false;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    message.includes("timed out") ||
    message.includes("timeout") ||
    message.includes("aborted") ||
    message.includes("fetch failed") ||
    message.includes("network")
  );
}

function isFetchFailedTransientError(error) {
  const status = Number(error && error.status);
  if (Number.isFinite(status)) {
    return false;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    message.includes("fetch failed") ||
    message.includes("socket hang up") ||
    message.includes("econnreset") ||
    message.includes("client network socket disconnected")
  );
}

function isSessionReuseImmediateFetchRestartError(error) {
  if (!error) {
    return false;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    message.includes("trigger immediate client hot-restart") ||
    message.includes("fetch/network failure detected") ||
    message.includes("fetch failed")
  );
}

function isInvalidSessionError(error) {
  const status = Number(error && error.status);
  if (status === 401 || status === 403) {
    return true;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    message.includes("invalid session") ||
    message.includes("session expired") ||
    message.includes("no active session") ||
    message.includes("not authenticated") ||
    message.includes("unauthorized") ||
    message.includes("authentication required")
  );
}

function isTimeoutError(error) {
  if (!error) {
    return false;
  }

  const message = String(
    error && error.message ? error.message : error || ""
  ).toLowerCase();

  return (
    message.includes("timeout") ||
    message.includes("timed out") ||
    message.includes("aborted") ||
    message.includes("etimedout") ||
    message.includes("econnreset") ||
    message.includes("request timed out")
  );
}

function isTransientSendFlowError(error) {
  if (!error) {
    return false;
  }

  if (isSendEligibilityDelayError(error)) {
    return false;
  }

  const status = Number(error && error.status);
  if (status === 429 || (status >= 500 && status < 600)) {
    return true;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    isTimeoutError(error) ||
    message.includes("fetch failed") ||
    message.includes("network") ||
    message.includes("socket") ||
    message.includes("econnreset") ||
    message.includes("eai_again") ||
    message.includes("connection") ||
    message.includes("terminated")
  );
}

function isSendEligibilityDelayError(error) {
  const status = Number(error && error.status);
  if (status === 409 || status === 423) {
    return true;
  }

  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    message.includes("cooldown") ||
    message.includes("retry after") ||
    message.includes("too soon") ||
    message.includes("wait before") ||
    message.includes("temporarily unavailable") ||
    (message.includes("recent") && message.includes("send"))
  );
}

function isBalanceContractFragmentationError(error) {
  const status = Number(error && error.status);
  const message = String(error && error.message ? error.message : error || "").toLowerCase();

  if (status !== 400) {
    return false;
  }

  return (
    message.includes("split across too many contracts") ||
    (message.includes("too many contracts") && message.includes("would be needed")) ||
    (message.includes("contracts") && message.includes("one transaction"))
  );
}

/**
 * Detect HTTP 400 error with hourly send limit message from server.
 * Matches messages like "hourly send limit", "send limit exceeded", etc.
 */
function isHourlySendLimitError(error) {
  const status = Number(error && error.status);
  if (status !== 400) return false;
  const message = String(error && error.message ? error.message : error || "").toLowerCase();
  return (
    (message.includes("hourly") && message.includes("limit")) ||
    (message.includes("send") && message.includes("limit")) ||
    (message.includes("hourly") && message.includes("send")) ||
    message.includes("rate limit") ||
    message.includes("too many send") ||
    message.includes("per hour")
  );
}

/**
 * Parse exact hourly TX limit from server error message.
 * HAR shows: "Hourly send limit reached (2 per hour). Please try again later."
 * Returns the number (e.g. 2) or null if not parseable.
 */
function parseHourlyLimitFromError(error) {
  const msg = String(error && error.message ? error.message : error || "");
  const match = msg.match(/\((\d+)\s+per\s+hour\)/i);
  return match ? parseInt(match[1], 10) : null;
}

function getReducedAmountForFragmentedBalance(currentAmount, sendPolicy) {
  const current = Number(currentAmount);
  if (!Number.isFinite(current) || current <= 0) {
    return null;
  }

  // Use the largest decimals across tierAmounts so reduced amount preserves precision.
  const tierAmounts = isObject(sendPolicy && sendPolicy.tierAmounts) ? sendPolicy.tierAmounts : {};
  let maxDecimals = 3;
  for (const tier of Object.values(tierAmounts)) {
    if (isObject(tier) && Number.isFinite(Number(tier.decimals))) {
      maxDecimals = Math.max(maxDecimals, clampToNonNegativeInt(tier.decimals, 3));
    }
  }
  const decimals = Math.min(8, Math.max(0, maxDecimals));

  const emergencyFloor = 0.1;
  const reducedRaw = current * 0.6;
  const candidate = Math.max(emergencyFloor, reducedRaw);
  if (!(candidate > 0) || candidate >= current) {
    return null;
  }

  const rounded = Number(candidate.toFixed(decimals));
  if (!Number.isFinite(rounded) || rounded <= 0 || rounded >= current) {
    return null;
  }

  return normalizeCcAmount(rounded.toFixed(decimals));
}

function parseRetryAfterSeconds(errorLike, fallbackSeconds = 15) {
  const message = String(errorLike && errorLike.message ? errorLike.message : errorLike || "");
  const normalizedFallback = Math.max(1, clampToNonNegativeInt(fallbackSeconds, 15));

  const parseUnit = (valueRaw, unitRaw) => {
    const value = Number(valueRaw);
    if (!Number.isFinite(value) || value <= 0) {
      return null;
    }

    const unit = String(unitRaw || "s").toLowerCase();
    if (unit.startsWith("ms")) {
      return Math.max(1, Math.ceil(value / 1000));
    }
    if (unit.startsWith("m")) {
      return Math.max(1, Math.ceil(value * 60));
    }
    return Math.max(1, Math.ceil(value));
  };

  const patterns = [
    /retry\s+after\s+(\d+(?:\.\d+)?)\s*(ms|milliseconds?|s|sec|secs|seconds?|m|min|mins|minutes?)?/i,
    /wait\s+(\d+(?:\.\d+)?)\s*(ms|milliseconds?|s|sec|secs|seconds?|m|min|mins|minutes?)?/i,
    /cooldown(?:[^\d]{0,12})(\d+(?:\.\d+)?)\s*(ms|milliseconds?|s|sec|secs|seconds?|m|min|mins|minutes?)?/i
  ];

  for (const pattern of patterns) {
    const match = message.match(pattern);
    if (!match) {
      continue;
    }

    const parsed = parseUnit(match[1], match[2]);
    if (parsed !== null) {
      return parsed;
    }
  }

  return normalizedFallback;
}

function normalizeConfig(rawConfig) {
  if (!isObject(rawConfig)) {
    throw new Error("config.json must be a JSON object");
  }

  const httpInput = isObject(rawConfig.http) ? rawConfig.http : {};
  const http = {
    timeoutMs: clampToNonNegativeInt(httpInput.timeoutMs, INTERNAL_API_DEFAULTS.http.timeoutMs),
    maxRetries: clampToNonNegativeInt(httpInput.maxRetries, INTERNAL_API_DEFAULTS.http.maxRetries),
    retryBaseDelayMs: clampToNonNegativeInt(
      httpInput.retryBaseDelayMs,
      INTERNAL_API_DEFAULTS.http.retryBaseDelayMs
    )
  };

  if (http.timeoutMs < 1000) {
    throw new Error("config.http.timeoutMs must be >= 1000 ms");
  }

  const pacingInput = isObject(rawConfig.requestPacing) ? rawConfig.requestPacing : {};
  const requestPacing = {
    minDelayMs: clampToNonNegativeInt(
      pacingInput.minDelayMs,
      INTERNAL_API_DEFAULTS.requestPacing.minDelayMs
    ),
    jitterMs: clampToNonNegativeInt(
      pacingInput.jitterMs,
      INTERNAL_API_DEFAULTS.requestPacing.jitterMs
    )
  };

  const recipientFile = String(rawConfig.recipientFile || "recipient.txt").trim();
  if (!recipientFile) {
    throw new Error("config.recipientFile must be a non-empty string");
  }

  const sessionInput = isObject(rawConfig.session) ? rawConfig.session : {};
  const session = {
    // Hardcoded: website migrated from Vercel Security Checkpoint to Cloudflare.
    // No _vcrcs cookies needed anymore. Browser challenge is permanently skipped.
    skipVercelChallenge: true,
    preflightOnboard:
      typeof sessionInput.preflightOnboard === "boolean"
        ? sessionInput.preflightOnboard
        : false,
    autoRefreshCheckpoint:
      typeof sessionInput.autoRefreshCheckpoint === "boolean"
        ? sessionInput.autoRefreshCheckpoint
        : true,
    proactiveVercelRefreshMinutes: clampToNonNegativeInt(
      sessionInput.proactiveVercelRefreshMinutes,
      45
    ),
    maxSessionReuseRefreshAttempts: Math.max(
      1,
      clampToNonNegativeInt(sessionInput.maxSessionReuseRefreshAttempts, 3)
    ),
    maxSessionReuseTransientAttempts: Math.max(
      1,
      clampToNonNegativeInt(sessionInput.maxSessionReuseTransientAttempts, 6)
    ),
    maxSessionReuseLightResets: Math.max(
      0,
      clampToNonNegativeInt(sessionInput.maxSessionReuseLightResets, 1)
    ),
    maxSessionReuseTransientBrowserRefreshes: Math.max(
      0,
      clampToNonNegativeInt(sessionInput.maxSessionReuseTransientBrowserRefreshes, 1)
    ),
    transientBrowserRefreshTriggerFailures: Math.max(
      1,
      clampToNonNegativeInt(sessionInput.transientBrowserRefreshTriggerFailures, 2)
    ),
    sessionReuseTransientRetryAfterSeconds: Math.max(
      15,
      clampToNonNegativeInt(sessionInput.sessionReuseTransientRetryAfterSeconds, 45)
    ),
    browserChallengeRetryAfterSeconds: Math.max(
      60,
      clampToNonNegativeInt(sessionInput.browserChallengeRetryAfterSeconds, 120)
    ),
    sessionReuseRetryJitterSeconds: Math.max(
      0,
      clampToNonNegativeInt(sessionInput.sessionReuseRetryJitterSeconds, 12)
    ),
    maxConcurrentSessionReuse: Math.max(
      1,
      clampToNonNegativeInt(sessionInput.maxConcurrentSessionReuse, 1)
    ),
    checkpointSettleDelayMs: Math.max(
      500,
      clampToNonNegativeInt(sessionInput.checkpointSettleDelayMs, 3500)
    ),
    maxOtpRefreshAttempts: Math.max(
      1,
      clampToNonNegativeInt(sessionInput.maxOtpRefreshAttempts, 3)
    ),
    fallbackToOtpOnPersistentCheckpoint:
      typeof sessionInput.fallbackToOtpOnPersistentCheckpoint === "boolean"
        ? sessionInput.fallbackToOtpOnPersistentCheckpoint
        : true
  };

  if (session.maxOtpRefreshAttempts < 1) {
    throw new Error("config.session.maxOtpRefreshAttempts must be >= 1");
  }

  if (session.maxSessionReuseRefreshAttempts < 1) {
    throw new Error("config.session.maxSessionReuseRefreshAttempts must be >= 1");
  }

  const uiInput = isObject(rawConfig.ui) ? rawConfig.ui : {};
  const uiLogLinesInput = Object.prototype.hasOwnProperty.call(uiInput, "logLines")
    ? uiInput.logLines
    : uiInput.maxExecutionLogLines;
  const ui = {
    dashboard:
      typeof uiInput.dashboard === "boolean"
        ? uiInput.dashboard
        : INTERNAL_API_DEFAULTS.ui.dashboard,
    logLines: Math.min(
      20,
      Math.max(
        1,
        clampToNonNegativeInt(uiLogLinesInput, INTERNAL_API_DEFAULTS.ui.logLines)
      )
    )
  };

  const sendInput = isObject(rawConfig.send) ? rawConfig.send : {};
  const maxLoopTx = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(sendInput, "maxLoopTx")
      ? sendInput.maxLoopTx
      : (
        Object.prototype.hasOwnProperty.call(sendInput, "maxTx")
          ? sendInput.maxTx
          : sendInput.maxTxPerAccount
      ),
    INTERNAL_API_DEFAULTS.send.maxLoopTx
  );
  if (maxLoopTx < 1) {
    throw new Error("config.send.maxLoopTx must be >= 1");
  }

  const legacyDelayBetweenTx = isObject(sendInput.delayBetweenTx)
    ? sendInput.delayBetweenTx
    : sendInput.delayBetweenTx;
  const legacyDelayBetweenTxMin = isObject(legacyDelayBetweenTx)
    ? (
      Object.prototype.hasOwnProperty.call(legacyDelayBetweenTx, "min")
        ? legacyDelayBetweenTx.min
        : legacyDelayBetweenTx.max
    )
    : legacyDelayBetweenTx;
  const legacyDelayBetweenTxMax = isObject(legacyDelayBetweenTx)
    ? (
      Object.prototype.hasOwnProperty.call(legacyDelayBetweenTx, "max")
        ? legacyDelayBetweenTx.max
        : legacyDelayBetweenTx.min
    )
    : legacyDelayBetweenTx;

  const minDelayTxSeconds = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(sendInput, "minDelayTxSeconds")
      ? sendInput.minDelayTxSeconds
      : (
        Object.prototype.hasOwnProperty.call(sendInput, "mindelayTxSeconds")
          ? sendInput.mindelayTxSeconds
          : (
            Object.prototype.hasOwnProperty.call(sendInput, "delayTxSeconds")
              ? sendInput.delayTxSeconds
              : legacyDelayBetweenTxMin
          )
      ),
    INTERNAL_API_DEFAULTS.send.minDelayTxSeconds
  );
  const maxDelayTxSeconds = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(sendInput, "maxDelayTxSeconds")
      ? sendInput.maxDelayTxSeconds
      : (
        Object.prototype.hasOwnProperty.call(sendInput, "maxdelayTxSeconds")
          ? sendInput.maxdelayTxSeconds
          : (
            Object.prototype.hasOwnProperty.call(sendInput, "delayTxSeconds")
              ? sendInput.delayTxSeconds
              : legacyDelayBetweenTxMax
          )
      ),
    INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds
  );

  if (maxDelayTxSeconds < minDelayTxSeconds) {
    throw new Error("config.send.maxDelayTxSeconds must be >= config.send.minDelayTxSeconds");
  }

  const delayCycleSeconds = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(sendInput, "delayCycleSeconds")
      ? sendInput.delayCycleSeconds
      : (
        Object.prototype.hasOwnProperty.call(sendInput, "delayBetweenCycles")
          ? sendInput.delayBetweenCycles
          : (
            Object.prototype.hasOwnProperty.call(sendInput, "delayBetweenCycle")
              ? sendInput.delayBetweenCycle
              : sendInput.loopDelaySeconds
          )
      ),
    INTERNAL_API_DEFAULTS.send.delayCycleSeconds
  );

  // Support flat "amount" shorthand: {min, max, decimals} applied to all tiers
  // If "tierAmounts" is explicitly provided, it takes precedence (backward compat)
  let tierAmountsInput = sendInput.tierAmounts;
  if (!isObject(tierAmountsInput) && isObject(sendInput.amount)) {
    // Expand flat amount to all tiers
    tierAmountsInput = {};
    for (const key of TIER_KEYS) {
      tierAmountsInput[key] = { ...sendInput.amount };
    }
  }
  const tierAmounts = normalizeTierAmountsConfig(
    tierAmountsInput,
    "config.send.tierAmounts"
  );

  const sequentialAllRounds =
    typeof sendInput.sequentialAllRounds === "boolean"
      ? sendInput.sequentialAllRounds
      : (
        typeof sendInput.parallelEnabled === "boolean"
          ? !sendInput.parallelEnabled
          : INTERNAL_API_DEFAULTS.send.sequentialAllRounds
      );

  const workers = Math.max(1, clampToNonNegativeInt(
    sendInput.workers,
    INTERNAL_API_DEFAULTS.send.workers
  ));

  // hourlyMaxTx: 0 or absent = adaptive (learn from server 400), >0 = pinned to config value
  const hourlyMaxTx = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(sendInput, "hourlyMaxTx")
      ? sendInput.hourlyMaxTx
      : (
        Object.prototype.hasOwnProperty.call(sendInput, "HourlyMax")
          ? sendInput.HourlyMax
          : sendInput.hourlyMax
      ),
    0
  );

  const send = {
    maxLoopTx,
    minDelayTxSeconds,
    maxDelayTxSeconds,
    delayCycleSeconds,
    sequentialAllRounds,
    workers,
    tierAmounts,
    hourlyMaxTx
  };

  const safetyInput = isObject(rawConfig.safety) ? rawConfig.safety : {};
  const safety = {
    minScoreThreshold: clampToNonNegativeInt(
      safetyInput.minScoreThreshold,
      30
    ),
    minHoldBalanceCc: clampToNonNegativeInt(
      safetyInput.minHoldBalanceCc,
      10
    )
  };

  const profitInput = isObject(rawConfig.profitability) ? rawConfig.profitability : {};
  const rawAllowedModes = Array.isArray(profitInput.allowedModes) ? profitInput.allowedModes : ["amber", "green"];
  const allowedModes = rawAllowedModes
    .map((m) => String(m || "").trim().toLowerCase())
    .filter(Boolean);
  const profitability = {
    allowedModes: allowedModes.length > 0 ? allowedModes : ["amber", "green"],
    retryIntervalSeconds: Math.max(10, clampToNonNegativeInt(profitInput.retryIntervalSeconds, 60))
  };

  const swapInput = isObject(rawConfig.swap) ? rawConfig.swap : {};
  const rawAllowedPairs = Array.isArray(swapInput.allowedPairs) ? swapInput.allowedPairs : [];
  const ringInput = isObject(swapInput.ring) ? swapInput.ring : {};
  // Support flat camouflageEnabled/camouflageProbability as simplified alternative to nested camouflage object
  const camoInput = isObject(ringInput.camouflage) ? ringInput.camouflage : {
    enabled: ringInput.camouflageEnabled,
    probabilityPerLeg: ringInput.camouflageProbability
  };
  const makerInput = isObject(swapInput.maker) ? swapInput.maker : {};
  const takerInput = isObject(swapInput.taker) ? swapInput.taker : {};
  const swap = {
    enabled: swapInput.enabled !== false,
    mode: String(swapInput.mode || "ring-hybrid").toLowerCase(),
    workers: Math.max(1, clampToNonNegativeInt(swapInput.workers, 5)),
    minEdgeBps: Number.isFinite(Number(swapInput.minEdgeBps)) ? Number(swapInput.minEdgeBps) : 25,
    maxOrderSizeUsd: Number.isFinite(Number(swapInput.maxOrderSizeUsd)) ? Number(swapInput.maxOrderSizeUsd) : 10,
    minOrderSizeUsd: Number.isFinite(Number(swapInput.minOrderSizeUsd)) ? Number(swapInput.minOrderSizeUsd) : 1.05,
    minOracleFreshnessSeconds: Math.max(1, clampToNonNegativeInt(swapInput.minOracleFreshnessSeconds, 30)),
    minExpiryBufferSeconds: Math.max(1, clampToNonNegativeInt(swapInput.minExpiryBufferSeconds, 30)),
    minDelaySeconds: Math.max(1, clampToNonNegativeInt(swapInput.minDelaySeconds, 30)),
    maxDelaySeconds: Math.max(1, clampToNonNegativeInt(swapInput.maxDelaySeconds, 90)),
    maxLoopTakes: Math.max(1, clampToNonNegativeInt(swapInput.maxLoopTakes, 100)),
    maxRuntimeMinutes: clampToNonNegativeInt(swapInput.maxRuntimeMinutes, 0),
    allowedPairs: rawAllowedPairs.map((p) => String(p || "").trim().toLowerCase()).filter(Boolean),
    maker: {
      minBps: Number.isFinite(Number(makerInput.minBps)) ? Number(makerInput.minBps) : 10,
      maxBps: Number.isFinite(Number(makerInput.maxBps)) ? Number(makerInput.maxBps) : 100,
      expiresHours: Math.max(1, clampToNonNegativeInt(makerInput.expiresHours, 6)),
      maxOpenOrders: Math.max(1, clampToNonNegativeInt(makerInput.maxOpenOrders, 3)),
      rateLimitCooldownMinutes: Math.max(1, clampToNonNegativeInt(makerInput.rateLimitCooldownMinutes, 60)),
      balanceLockCooldownSeconds: Math.max(10, clampToNonNegativeInt(makerInput.balanceLockCooldownSeconds, 120)),
      takerIdleSecondsBeforeMaker: Math.max(1, clampToNonNegativeInt(makerInput.takerIdleSecondsBeforeMaker, 10)),
      cancelAfterIdleMinutes: Math.max(1, clampToNonNegativeInt(makerInput.cancelAfterIdleMinutes, 5))
    },
    taker: {
      minBps: Number.isFinite(Number(takerInput.minBps)) ? Number(takerInput.minBps) : 25,
      // Hard cap per maker username; resets every Saturday 00:00 UTC (Sat 07:00 WIB).
      // Falls back to the legacy `maxTakesPerCounterpartyPerHour` key if present.
      maxTakesPerCounterpartyPerWeek: Math.max(0, clampToNonNegativeInt(
        takerInput.maxTakesPerCounterpartyPerWeek
        ?? takerInput.maxTakesPerCounterpartyPerHour,
        5
      )),
      balanceLockCooldownSeconds: Math.max(10, clampToNonNegativeInt(takerInput.balanceLockCooldownSeconds, 90)),
      orderBlacklistSeconds: Math.max(10, clampToNonNegativeInt(takerInput.orderBlacklistSeconds, 60)),
      maxDrainPerLoop: Math.max(1, clampToNonNegativeInt(takerInput.maxDrainPerLoop, 10)),
      fastScanIntervalSeconds: Math.max(1, clampToNonNegativeInt(takerInput.fastScanIntervalSeconds, 2))
    },
    ring: {
      enabled: ringInput.enabled !== false,
      selfListEdgeBps: Number.isFinite(Number(ringInput.selfListEdgeBps)) ? Number(ringInput.selfListEdgeBps) : 0,
      baseAmountUsd: Number.isFinite(Number(ringInput.baseAmountUsd)) ? Number(ringInput.baseAmountUsd) : 5,
      amountJitterPercent: Math.max(0, Number(ringInput.amountJitterPercent) || 5),
      legMinJitterSeconds: Math.max(1, clampToNonNegativeInt(ringInput.legMinJitterSeconds, 600)),
      legMaxJitterSeconds: Math.max(1, clampToNonNegativeInt(ringInput.legMaxJitterSeconds, 1800)),
      maxDriftBps: Number.isFinite(Number(ringInput.maxDriftBps)) ? Number(ringInput.maxDriftBps) : 50,
      listingExpiresHours: Math.max(1, clampToNonNegativeInt(ringInput.listingExpiresHours, 1)),
      maxRoundsPerSession: clampToNonNegativeInt(ringInput.maxRoundsPerSession, 0),
      camouflage: {
        enabled: camoInput.enabled !== false,
        probabilityPerLeg: Math.max(0, Math.min(1, Number(camoInput.probabilityPerLeg) || 0.3))
      }
    }
  };

  const captchaInput = isObject(rawConfig.captcha) ? rawConfig.captcha : {};
  const captchaProvider = String(captchaInput.provider || "self-hosted").toLowerCase().trim();
  const validProviders = ["self-hosted", "2captcha", "auto"];

  // solverUrl supports single string or array of strings for load balancing
  let solverUrls;
  if (Array.isArray(captchaInput.solverUrl)) {
    solverUrls = captchaInput.solverUrl
      .map((u) => String(u || "").trim())
      .filter(Boolean);
  } else {
    const single = String(captchaInput.solverUrl || SELFHOSTED_SOLVER_DEFAULT_URL).trim();
    solverUrls = single ? [single] : [SELFHOSTED_SOLVER_DEFAULT_URL];
  }
  if (solverUrls.length === 0) {
    solverUrls = [SELFHOSTED_SOLVER_DEFAULT_URL];
  }

  const captcha = {
    provider: validProviders.includes(captchaProvider) ? captchaProvider : "self-hosted",
    solverUrl: solverUrls.length === 1 ? solverUrls[0] : solverUrls[0],
    solverUrls: solverUrls,
    apiKey: String(captchaInput.apiKey || "").trim()
  };

  const tgInput = isObject(rawConfig.telegram) ? rawConfig.telegram : {};
  const tgAutoReportInput = isObject(tgInput.autoReport) ? tgInput.autoReport : {};
  const allowedChatIdsRaw = Array.isArray(tgInput.allowedChatIds)
    ? tgInput.allowedChatIds
    : (typeof tgInput.allowedChatIds === "string"
      ? tgInput.allowedChatIds.split(",")
      : []);
  const telegram = {
    enabled: tgInput.enabled === false ? false : true,
    botToken: String(tgInput.botToken || tgInput.bot_token || "").trim(),
    allowedChatIds: allowedChatIdsRaw
      .map((v) => String(v).trim())
      .filter(Boolean),
    autoReport: {
      enabled: tgAutoReportInput.enabled === false ? false : true,
      minIntervalMinutes: clampToNonNegativeInt(tgAutoReportInput.minIntervalMinutes || tgAutoReportInput.intervalMinutes, 30) || 30,
      reportAtCycleStart: tgAutoReportInput.reportAtCycleStart === false ? false : true,
      reportOnHourlyCapReached: tgAutoReportInput.reportOnHourlyCapReached === false ? false : true
    }
  };

  return {
    baseUrl: INTERNAL_API_DEFAULTS.baseUrl,
    paths: { ...INTERNAL_API_DEFAULTS.paths },
    headers: {
      ...INTERNAL_API_DEFAULTS.headers,
      extra: {},
      cookie: ""
    },
    http,
    requestPacing,
    recipientFile,
    session,
    send,
    ui,
    safety,
    telegram,
    profitability,
    swap,
    captcha,
    proxyUrl: null
  };
}

function normalizeAccounts(rawAccounts) {
  if (!isObject(rawAccounts)) {
    throw new Error("accounts.json must be a JSON object");
  }

  if (!Array.isArray(rawAccounts.accounts) || rawAccounts.accounts.length === 0) {
    throw new Error("accounts.json must contain a non-empty accounts array");
  }

  const accounts = rawAccounts.accounts.map((entry, index) => {
    if (!isObject(entry)) {
      throw new Error(`accounts[${index}] must be an object`);
    }

    const name = String(entry.name || "").trim();
    const email = String(entry.email || "").trim();
    const address = String(entry.address || entry.cantonPartyId || "").trim();

    if (!name) {
      throw new Error(`accounts[${index}].name is required`);
    }

    if (!email || !email.includes("@")) {
      throw new Error(`accounts[${index}].email is invalid`);
    }

    return {
      name,
      email,
      address
    };
  });

  const names = new Set();
  for (const account of accounts) {
    if (names.has(account.name)) {
      throw new Error(`Duplicate account name in accounts.json: ${account.name}`);
    }
    names.add(account.name);
  }

  const defaultAccount = String(rawAccounts.defaultAccount || accounts[0].name).trim();
  return { defaultAccount, accounts };
}

function extractLegacyAccountCookies(rawAccounts) {
  const cookieMap = new Map();
  if (!isObject(rawAccounts) || !Array.isArray(rawAccounts.accounts)) {
    return cookieMap;
  }

  for (const entry of rawAccounts.accounts) {
    if (!isObject(entry)) {
      continue;
    }

    const name = String(entry.name || "").trim();
    const cookie = String(entry.cookie || "").trim();
    if (name && cookie) {
      cookieMap.set(name, cookie);
    }
  }

  return cookieMap;
}

function selectAccount(accountsConfig, preferredName) {
  const targetName = String(preferredName || accountsConfig.defaultAccount || "").trim();
  const found = accountsConfig.accounts.find((account) => account.name === targetName);
  if (!found) {
    const available = accountsConfig.accounts.map((account) => account.name).join(", ");
    throw new Error(`Account '${targetName}' not found. Available accounts: ${available}`);
  }
  return found;
}

// OTP mutex: serialize OTP prompts so only 1 account reads stdin at a time
let otpMutexPromise = Promise.resolve();
let activeDashboardRef = null; // Set by processAccount to reference the dashboard

function setActiveDashboard(dashboard) {
  activeDashboardRef = dashboard;
}

// Global uptime state (shared across per-account dashboards within one cycle)
let globalUptimeStartMs = 0;
let globalUptimeLabel = "0h 0m 0s";

function setGlobalUptimeStart(ms) {
  globalUptimeStartMs = Number(ms) || 0;
}

function setGlobalUptimeLabel(label) {
  globalUptimeLabel = String(label || "");
}

function getGlobalUptimeLabel() {
  if (!globalUptimeStartMs) return "";
  return globalUptimeLabel;
}

async function promptOtpCode() {
  // Wait for any previous OTP prompt to finish (mutex)
  let release;
  const prev = otpMutexPromise;
  otpMutexPromise = new Promise((resolve) => { release = resolve; });
  await prev;

  try {
    // Pause dashboard rendering to keep the OTP prompt visible
    if (activeDashboardRef && typeof activeDashboardRef.pause === "function") {
      activeDashboardRef.pause();
    }

    const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
    try {
      const code = await rl.question("Enter OTP code: ");
      return String(code || "").trim();
    } finally {
      rl.close();
    }
  } finally {
    // Resume dashboard rendering
    if (activeDashboardRef && typeof activeDashboardRef.resume === "function") {
      activeDashboardRef.resume();
    }
    release();
  }
}

async function acquireBrowserChallengeSlot() {
  if (activeBrowserChallenges < BROWSER_CHALLENGE_MAX_CONCURRENT) {
    activeBrowserChallenges += 1;
    console.log(
      `[browser-queue] Slot acquired (${activeBrowserChallenges}/${BROWSER_CHALLENGE_MAX_CONCURRENT})`
    );
    return;
  }

  const queuePosition = browserChallengeWaitQueue.length + 1;
  const queuedAt = Date.now();
  console.log(
    `[browser-queue] Challenge queued (position ${queuePosition}), ` +
    `active=${activeBrowserChallenges}/${BROWSER_CHALLENGE_MAX_CONCURRENT}`
  );

  await new Promise((resolve) => {
    browserChallengeWaitQueue.push(resolve);
  });

  const waitedSeconds = Math.max(1, Math.round((Date.now() - queuedAt) / 1000));
  console.log(
    `[browser-queue] Slot acquired after waiting ${waitedSeconds}s ` +
    `(${activeBrowserChallenges}/${BROWSER_CHALLENGE_MAX_CONCURRENT})`
  );
}

function applySessionReuseConcurrencyLimit(limitCandidate) {
  const parsed = clampToNonNegativeInt(limitCandidate, SESSION_REUSE_MAX_CONCURRENT);
  SESSION_REUSE_MAX_CONCURRENT = Math.max(1, parsed);
}

async function acquireSessionReuseSlot(accountLogTag = null) {
  const prefix = accountLogTag ? `[${accountLogTag}] ` : "";

  if (activeSessionReuseChallenges < SESSION_REUSE_MAX_CONCURRENT) {
    activeSessionReuseChallenges += 1;
    console.log(
      `${prefix}[session-queue] Slot acquired (${activeSessionReuseChallenges}/${SESSION_REUSE_MAX_CONCURRENT})`
    );
    return;
  }

  const queuePosition = sessionReuseWaitQueue.length + 1;
  const queuedAt = Date.now();
  console.log(
    `${prefix}[session-queue] Session reuse queued (position ${queuePosition}), ` +
    `active=${activeSessionReuseChallenges}/${SESSION_REUSE_MAX_CONCURRENT}`
  );

  await new Promise((resolve) => {
    sessionReuseWaitQueue.push(resolve);
  });

  const waitedSeconds = Math.max(1, Math.round((Date.now() - queuedAt) / 1000));
  console.log(
    `${prefix}[session-queue] Slot acquired after waiting ${waitedSeconds}s ` +
    `(${activeSessionReuseChallenges}/${SESSION_REUSE_MAX_CONCURRENT})`
  );
}

function releaseSessionReuseSlot(accountLogTag = null) {
  const prefix = accountLogTag ? `[${accountLogTag}] ` : "";

  if (activeSessionReuseChallenges > 0) {
    activeSessionReuseChallenges -= 1;
  }

  const next = sessionReuseWaitQueue.shift();
  if (next) {
    activeSessionReuseChallenges += 1;
    next();
  }

  console.log(
    `${prefix}[session-queue] Slot released ` +
    `(active=${activeSessionReuseChallenges}/${SESSION_REUSE_MAX_CONCURRENT}, queue=${sessionReuseWaitQueue.length})`
  );
}

function releaseBrowserChallengeSlot() {
  if (activeBrowserChallenges > 0) {
    activeBrowserChallenges -= 1;
  }

  const next = browserChallengeWaitQueue.shift();
  if (next) {
    activeBrowserChallenges += 1;
    next();
  }

  console.log(
    `[browser-queue] Slot released ` +
    `(active=${activeBrowserChallenges}/${BROWSER_CHALLENGE_MAX_CONCURRENT}, queue=${browserChallengeWaitQueue.length})`
  );
}

function isSecurityCookieName(name) {
  const normalized = String(name || "").trim().toLowerCase();
  return normalized === "_vcrcs" || normalized.startsWith("_vc");
}

function cacheSecurityCookiesFromMap(cookieMap, sourceLabel = "unknown") {
  if (!(cookieMap instanceof Map)) {
    return 0;
  }

  let updated = 0;
  for (const [name, value] of cookieMap.entries()) {
    if (!isSecurityCookieName(name)) {
      continue;
    }

    const key = String(name || "").trim();
    const val = String(value || "").trim();
    if (!key || !val) {
      continue;
    }

    const previousValue = cachedSecurityCookies.get(key);
    if (previousValue !== val) {
      cachedSecurityCookies.set(key, val);
      updated += 1;
    }
  }

  if (updated > 0) {
    console.log(`[cookie-cache] Updated ${updated} security cookie(s) from ${sourceLabel}`);
  }

  return updated;
}

function buildCachedSecurityCookieMap() {
  return new Map(cachedSecurityCookies);
}

async function readAllBrowserCookies(page) {
  const merged = new Map();

  try {
    const pageCookies = await page.cookies();
    for (const cookie of pageCookies) {
      if (cookie && cookie.name) {
        merged.set(cookie.name, cookie.value);
      }
    }
  } catch (error) {
    console.log(`[browser] page.cookies() issue: ${error.message}`);
  }

  try {
    const contextCookies = await page.browserContext().cookies();
    for (const cookie of contextCookies) {
      if (cookie && cookie.name) {
        merged.set(cookie.name, cookie.value);
      }
    }
  } catch (error) {
    console.log(`[browser] browserContext.cookies() issue: ${error.message}`);
  }

  return Array.from(merged.entries()).map(([name, value]) => ({ name, value }));
}

function getBrowserChallengeCooldownRemainingSeconds() {
  if (!Number.isFinite(browserChallengeRateLimitedUntilMs) || browserChallengeRateLimitedUntilMs <= 0) {
    return 0;
  }

  const remainingMs = browserChallengeRateLimitedUntilMs - Date.now();
  if (remainingMs <= 0) {
    browserChallengeRateLimitedUntilMs = 0;
    return 0;
  }

  return Math.max(1, Math.ceil(remainingMs / 1000));
}

function markBrowserChallengeRateLimited(cooldownSeconds = 120) {
  const boundedSeconds = Math.max(30, clampToNonNegativeInt(cooldownSeconds, 120));
  const nextUntilMs = Date.now() + (boundedSeconds * 1000);
  browserChallengeRateLimitedUntilMs = Math.max(browserChallengeRateLimitedUntilMs, nextUntilMs);
  console.log(`[browser] Rate-limit cooldown armed for ${boundedSeconds}s`);
}

async function solveBrowserChallenge(baseUrl, onboardPath, userAgent, headless = true) {
  if (!puppeteer) {
    throw new Error("Puppeteer is not installed. Run: npm install puppeteer-extra puppeteer-extra-plugin-stealth");
  }

  await acquireBrowserChallengeSlot();
  let browser = null;
  let trackedPid = null;
  try {
    console.log("[browser] Launching browser to solve Vercel challenge...");
    console.log("[browser] Mode: " + (headless ? "headless" : "visible"));
    console.log(`[browser] Launch timeout: ${Math.round(BROWSER_LAUNCH_TIMEOUT_MS / 1000)}s`);

    browser = await puppeteer.launch({
      headless: headless,
      timeout: BROWSER_LAUNCH_TIMEOUT_MS,
      args: [
        "--no-sandbox",
        "--disable-setuid-sandbox",
        "--disable-blink-features=AutomationControlled",
        "--disable-infobars",
        "--disable-dev-shm-usage",
        "--window-size=1280,800"
      ],
      defaultViewport: null
    });
    trackedPid = trackBrowserPid(browser);

    const page = await browser.newPage();

    // Keep browser challenge fingerprint close to API requests.
    await page.setUserAgent(String(userAgent || INTERNAL_API_DEFAULTS.headers.userAgent));

    await page.setExtraHTTPHeaders({
      "Accept-Language": "en-US,en;q=0.9"
    });

    const targetUrl = new URL(onboardPath, baseUrl).toString();
    console.log(`[browser] Navigating to ${targetUrl}`);

    let response;
    try {
      response = await page.goto(targetUrl, {
        waitUntil: "domcontentloaded",
        timeout: 30000
      });
    } catch (navError) {
      console.log(`[browser] Navigation issue: ${navError.message}`);
    }

    const status = response ? response.status() : 0;
    console.log(`[browser] Initial response status: ${status}`);
    const probeAttempts = status === 429
      ? BROWSER_CHALLENGE_MAX_ATTEMPTS_ON_429
      : BROWSER_CHALLENGE_MAX_ATTEMPTS;

    if (status === 429) {
      console.log(`[browser] 429 detected, using 429 challenge mode (${probeAttempts} checks).`);
    }

    // If page loaded with 200 and no challenge, cookies may already be available
    // (Cloudflare-proxied sites don't set _vc* cookies anymore)
    if (status === 200) {
      const initialCookies = await page.cookies();
      if (initialCookies.length > 0 || !response) {
        console.log(`[browser] Page loaded with HTTP 200 — no Vercel challenge detected (${initialCookies.length} cookies). Skipping challenge poll.`);
        // Return whatever cookies are available
        const cookieMap = new Map();
        for (const cookie of initialCookies) {
          cookieMap.set(cookie.name, cookie.value);
        }
        cacheSecurityCookiesFromMap(cookieMap, "browser-no-challenge");
        return cookieMap;
      }
    }

    console.log("[browser] Waiting for Vercel challenge to resolve...");

    for (let i = 0; i < probeAttempts; i++) {
      await sleep(2000);
      const currentUrl = page.url();
      const cookies = await page.cookies();

      console.log(`[browser] Attempt ${i + 1}: URL=${currentUrl.slice(0, 60)}..., ${cookies.length} cookies`);

      const hasVercelCookie = cookies.some(c => c.name.startsWith("_vc"));
      if (hasVercelCookie) {
        console.log("[browser] Vercel security cookies obtained!");
        break;
      }

      if (currentUrl.includes("/onboard") && cookies.length > 0) {
        console.log("[browser] Page loaded with cookies");
        break;
      }
    }

    console.log("[browser] Final cookie extraction...");
    await sleep(1000);

    let cookies = await page.cookies();

    if (cookies.length === 0 && status === 429) {
      console.log(
        `[browser] Still no cookies after challenge on HTTP 429. ` +
        `Cooling down ${Math.round(BROWSER_CHALLENGE_RETRY_DELAY_MS / 1000)}s then running quick retry...`
      );
      await sleep(BROWSER_CHALLENGE_RETRY_DELAY_MS);

      try {
        await page.reload({
          waitUntil: "domcontentloaded",
          timeout: 30000
        });
      } catch (reloadError) {
        console.log(`[browser] Reload issue after 429: ${reloadError.message}`);
      }

      for (let i = 0; i < BROWSER_CHALLENGE_RETRY_ATTEMPTS_ON_429; i += 1) {
        await sleep(2000);
        cookies = await page.cookies();
        const hasVercelCookie = cookies.some((cookie) => String(cookie.name || "").startsWith("_vc"));
        console.log(`[browser] Retry attempt ${i + 1}: ${cookies.length} cookies`);
        if (hasVercelCookie || cookies.length > 0) {
          console.log("[browser] Cookies detected after 429 retry.");
          break;
        }
      }
    }

    console.log(`[browser] Extracted ${cookies.length} cookies:`);

    const cookieMap = new Map();
    for (const cookie of cookies) {
      cookieMap.set(cookie.name, cookie.value);
      const valuePreview = cookie.value.length > 40 ? cookie.value.slice(0, 40) + "..." : cookie.value;
      console.log(`[browser]   ${cookie.name}=${valuePreview}`);
    }

    cacheSecurityCookiesFromMap(cookieMap, "browser-challenge");

    return cookieMap;
  } finally {
    if (browser) {
      try {
        await browser.close();
        console.log("[browser] Browser closed");
      } catch (closeError) {
        const closeMessage = String(
          closeError && closeError.message ? closeError.message : closeError || "unknown"
        );
        console.log(`[browser] Browser close warning: ${closeMessage}`);
        // Force kill Chromium if close() failed to prevent zombie
        if (trackedPid) {
          try { process.kill(trackedPid, "SIGKILL"); console.log(`[browser] Force-killed Chromium pid ${trackedPid}`); }
          catch { }
        }
      }
      untrackBrowserPid(trackedPid);
    }
    releaseBrowserChallengeSlot();
  }
}

// ============================================================================
// Profitability / Network Recovery Check
// Cek networkRecovery.mode dari /api/rewards sebelum TX (per akun, pakai client authenticated).
// TX diijinkan HANYA saat mode = "amber" atau "green"; selain itu (red/unknown)
// pause akun sampai mode naik. Pakai mode (bukan %) karena threshold sering diubah dev.
// HTTP 409 "Network is currently congested" = mode drop → wait dulu.
// ============================================================================
function isTrafficCongestionError(error) {
  if (!error) return false;
  const status = Number(error.status);
  const msg = String(error.message || "").toLowerCase();
  return status === 409 && (
    msg.includes("network is currently congested") ||
    msg.includes("acknowledgetrafficwarning")
  );
}

// ============================================================================
// Cloudflare Turnstile challenge (per-transfer anti-bot)
// Backend triggers this when networkRecovery is not "green": /api/send/transfer
// returns HTTP 403 "Network is congested. A challenge must be ..." unless body
// carries { acknowledgeTrafficWarning: true, trafficChallengeToken: <token> }.
//
// Supported providers (config.captcha.provider):
//   "self-hosted" — Turnstile-Solver lokal (GRATIS, default)
//   "2captcha"    — 2Captcha API (berbayar, butuh apiKey)
//   "auto"        — coba self-hosted dulu, fallback ke 2captcha jika gagal
// ============================================================================
const TURNSTILE_SITEKEY = "0x4AAAAAAC-oOGMu5lxFvc7w";
const TURNSTILE_PAGEURL = "https://bridge.rootsfi.com/send";
const TWOCAPTCHA_IN_URL = "https://2captcha.com/in.php";
const TWOCAPTCHA_RES_URL = "https://2captcha.com/res.php";
const TWOCAPTCHA_POLL_INTERVAL_MS = 5000;
const TWOCAPTCHA_POLL_TIMEOUT_MS = 180000;
const TWOCAPTCHA_INITIAL_WAIT_MS = 10000;
const SELFHOSTED_SOLVER_DEFAULT_URL = "http://localhost:8000";
let _solverRoundRobinIndex = 0; // round-robin counter for multi-solver load balancing
const SELFHOSTED_POLL_INTERVAL_MS = 2000;
const SELFHOSTED_POLL_TIMEOUT_MS = 180000;

function isTrafficChallengeRequiredError(error) {
  if (!error) return false;
  const status = Number(error.status);
  const msg = String(error.message || "").toLowerCase();
  if (status !== 403) return false;
  return (
    msg.includes("challenge must be") ||
    msg.includes("challenge token") ||
    msg.includes("traffic challenge") ||
    msg.includes("acknowledgetrafficwarning")
  );
}

async function solveTurnstileVia2Captcha(apiKey, { sitekey = TURNSTILE_SITEKEY, pageurl = TURNSTILE_PAGEURL } = {}) {
  if (!apiKey) {
    throw new Error("2Captcha API key missing (config.captcha.apiKey)");
  }

  const fetchFn = (typeof globalThis.fetch === "function") ? globalThis.fetch.bind(globalThis) : null;
  if (!fetchFn) {
    throw new Error("global fetch is not available in this Node runtime");
  }

  const submitUrl = `${TWOCAPTCHA_IN_URL}?key=${encodeURIComponent(apiKey)}`
    + `&method=turnstile&sitekey=${encodeURIComponent(sitekey)}`
    + `&pageurl=${encodeURIComponent(pageurl)}&json=1`;

  const submitResp = await fetchFn(submitUrl, { method: "GET" });
  const submitText = await submitResp.text();
  let submitJson;
  try {
    submitJson = JSON.parse(submitText);
  } catch {
    throw new Error(`2Captcha in.php returned non-JSON: ${submitText.slice(0, 200)}`);
  }
  if (!submitJson || submitJson.status !== 1) {
    throw new Error(`2Captcha in.php error: ${submitJson && submitJson.request ? submitJson.request : submitText.slice(0, 200)}`);
  }

  const captchaId = String(submitJson.request);
  console.log(`[captcha] 2Captcha task submitted (id=${captchaId}). Waiting for solve...`);
  await sleep(TWOCAPTCHA_INITIAL_WAIT_MS);

  const deadline = Date.now() + TWOCAPTCHA_POLL_TIMEOUT_MS;
  while (Date.now() < deadline) {
    const pollUrl = `${TWOCAPTCHA_RES_URL}?key=${encodeURIComponent(apiKey)}`
      + `&action=get&id=${encodeURIComponent(captchaId)}&json=1`;
    const pollResp = await fetchFn(pollUrl, { method: "GET" });
    const pollText = await pollResp.text();
    let pollJson;
    try {
      pollJson = JSON.parse(pollText);
    } catch {
      console.log(`[captcha] poll parse error: ${pollText.slice(0, 160)}. Retrying...`);
      await sleep(TWOCAPTCHA_POLL_INTERVAL_MS);
      continue;
    }

    if (pollJson.status === 1) {
      const token = String(pollJson.request || "").trim();
      if (!token) {
        throw new Error("2Captcha returned empty token");
      }
      console.log(`[captcha] Turnstile token received (len=${token.length}).`);
      return token;
    }

    if (pollJson.request === "CAPCHA_NOT_READY") {
      await sleep(TWOCAPTCHA_POLL_INTERVAL_MS);
      continue;
    }

    throw new Error(`2Captcha res.php error: ${pollJson.request || pollText.slice(0, 200)}`);
  }

  throw new Error(`2Captcha timed out after ${TWOCAPTCHA_POLL_TIMEOUT_MS / 1000}s waiting for Turnstile token`);
}

/**
 * Solve Cloudflare Turnstile via self-hosted Turnstile-Solver (GRATIS).
 * Solver harus sudah jalan di VPS: python3 api_server.py (default port 8000).
 * Flow: POST /turnstile -> poll GET /result?id=<task_id> sampai success/error.
 */
async function solveTurnstileViaSelfHosted(solverBaseUrl, { sitekey = TURNSTILE_SITEKEY, pageurl = TURNSTILE_PAGEURL } = {}) {
  const baseUrl = String(solverBaseUrl || SELFHOSTED_SOLVER_DEFAULT_URL).replace(/\/+$/, "");

  const fetchFn = (typeof globalThis.fetch === "function") ? globalThis.fetch.bind(globalThis) : null;
  if (!fetchFn) {
    throw new Error("global fetch is not available in this Node runtime");
  }

  // Step 1: Submit task to self-hosted solver
  const submitUrl = `${baseUrl}/turnstile?url=${encodeURIComponent(pageurl)}&sitekey=${encodeURIComponent(sitekey)}`;
  let submitResp;
  try {
    submitResp = await fetchFn(submitUrl, { method: "GET", signal: AbortSignal.timeout(15000) });
  } catch (connError) {
    const connMsg = String(connError && connError.message ? connError.message : connError || "");
    throw new Error(`Self-hosted solver tidak bisa dihubungi di ${baseUrl}: ${connMsg}`);
  }

  if (submitResp.status === 429) {
    throw new Error("Self-hosted solver penuh (429), semua worker sedang sibuk. Coba lagi nanti.");
  }

  const submitText = await submitResp.text();
  let submitJson;
  try {
    submitJson = JSON.parse(submitText);
  } catch {
    throw new Error(`Self-hosted solver returned non-JSON: ${submitText.slice(0, 200)}`);
  }

  if (!submitJson || submitJson.status !== "accepted") {
    const errDetail = submitJson && submitJson.error ? submitJson.error : submitText.slice(0, 200);
    throw new Error(`Self-hosted solver submit error: ${errDetail}`);
  }

  const taskId = String(submitJson.task_id || "").trim();
  if (!taskId) {
    throw new Error("Self-hosted solver returned empty task_id");
  }

  console.log(`[captcha] Self-hosted solver task submitted (id=${taskId.slice(0, 12)}...). Polling...`);

  // Step 2: Poll for result
  const deadline = Date.now() + SELFHOSTED_POLL_TIMEOUT_MS;
  let pollCount = 0;
  while (Date.now() < deadline) {
    await sleep(SELFHOSTED_POLL_INTERVAL_MS);
    pollCount += 1;

    const pollUrl = `${baseUrl}/result?id=${encodeURIComponent(taskId)}`;
    let pollResp;
    try {
      pollResp = await fetchFn(pollUrl, { method: "GET", signal: AbortSignal.timeout(10000) });
    } catch (pollConnError) {
      console.log(`[captcha] Self-hosted solver poll #${pollCount} connection error: ${pollConnError.message}. Retrying...`);
      continue;
    }

    // 404 = task expired or not found
    if (pollResp.status === 404) {
      throw new Error(`Self-hosted solver task ${taskId.slice(0, 12)} expired atau tidak ditemukan (404)`);
    }

    const pollText = await pollResp.text();
    let pollJson;
    try {
      pollJson = JSON.parse(pollText);
    } catch {
      console.log(`[captcha] Self-hosted solver poll #${pollCount} parse error: ${pollText.slice(0, 100)}. Retrying...`);
      continue;
    }

    if (pollJson.status === "success") {
      const token = String(pollJson.value || "").trim();
      if (!token) {
        throw new Error("Self-hosted solver returned empty token");
      }
      console.log(`[captcha] Turnstile token received via self-hosted solver (len=${token.length}, ${pollCount} polls).`);
      return token;
    }

    if (pollJson.status === "error") {
      const errValue = String(pollJson.value || pollJson.message || "unknown");
      throw new Error(`Self-hosted solver error: ${errValue}`);
    }

    // status === "process" -> masih solving, lanjut poll
    if (pollCount % 10 === 0) {
      console.log(`[captcha] Self-hosted solver masih solving... (poll #${pollCount})`);
    }
  }

  throw new Error(`Self-hosted solver timed out after ${SELFHOSTED_POLL_TIMEOUT_MS / 1000}s (${pollCount} polls)`);
}

/**
 * Smart captcha solver wrapper — auto-selects provider based on config.
 * Supports multiple solver URLs with round-robin load balancing.
 * Provider options: "self-hosted" (default, gratis), "2captcha" (berbayar), "auto" (coba self-hosted dulu).
 */
async function solveTurnstile(captchaConfig) {
  const provider = String(captchaConfig && captchaConfig.provider || "self-hosted").toLowerCase().trim();
  const solverUrls = Array.isArray(captchaConfig && captchaConfig.solverUrls) && captchaConfig.solverUrls.length > 0
    ? captchaConfig.solverUrls
    : [String(captchaConfig && captchaConfig.solverUrl || SELFHOSTED_SOLVER_DEFAULT_URL).trim()];
  const apiKey = String(captchaConfig && captchaConfig.apiKey || "").trim();

  if (provider === "2captcha") {
    if (!apiKey) {
      throw new Error("Provider 2captcha dipilih tapi config.captcha.apiKey kosong!");
    }
    console.log("[captcha] Solving Turnstile via 2Captcha (berbayar)...");
    return solveTurnstileVia2Captcha(apiKey);
  }

  if (provider === "self-hosted") {
    // Round-robin across multiple solver URLs
    const errors = [];
    for (let i = 0; i < solverUrls.length; i++) {
      const idx = (_solverRoundRobinIndex + i) % solverUrls.length;
      const url = solverUrls[idx];
      try {
        console.log(`[captcha] Solving via self-hosted solver [${idx + 1}/${solverUrls.length}] (${url})...`);
        const token = await solveTurnstileViaSelfHosted(url);
        _solverRoundRobinIndex = (idx + 1) % solverUrls.length;
        return token;
      } catch (err) {
        console.log(`[captcha] Solver [${idx + 1}] (${url}) gagal: ${err.message}`);
        errors.push({ url, error: err });
      }
    }
    // All solvers failed
    const lastErr = errors.length > 0 ? errors[errors.length - 1].error : new Error("No solver URLs configured");
    throw lastErr;
  }

  if (provider === "auto") {
    // Coba semua self-hosted dulu (round-robin), fallback ke 2captcha
    const errors = [];
    for (let i = 0; i < solverUrls.length; i++) {
      const idx = (_solverRoundRobinIndex + i) % solverUrls.length;
      const url = solverUrls[idx];
      try {
        console.log(`[captcha] [auto] Mencoba solver [${idx + 1}/${solverUrls.length}] (${url})...`);
        const token = await solveTurnstileViaSelfHosted(url);
        _solverRoundRobinIndex = (idx + 1) % solverUrls.length;
        return token;
      } catch (err) {
        console.log(`[captcha] [auto] Solver [${idx + 1}] (${url}) gagal: ${err.message}`);
        errors.push({ url, error: err });
      }
    }
    // All self-hosted failed, try 2captcha fallback
    if (apiKey) {
      console.log("[captcha] [auto] Semua self-hosted gagal. Fallback ke 2Captcha...");
      return solveTurnstileVia2Captcha(apiKey);
    }
    console.log("[captcha] [auto] Semua solver gagal, tidak ada fallback 2Captcha.");
    const lastErr = errors.length > 0 ? errors[errors.length - 1].error : new Error("No solver URLs configured");
    throw lastErr;
  }

  throw new Error(`Provider captcha tidak dikenal: "${provider}". Gunakan: "self-hosted", "2captcha", atau "auto".`);
}

let lastProfitabilityStatus = null;

function parseNetworkRecovery(rewardsData) {
  const nr = isObject(rewardsData.networkRecovery) ? rewardsData.networkRecovery : null;
  if (!nr) return null;
  return {
    mode: String(nr.mode || "unknown"),
    modeLabel: String(nr.modeLabel || nr.mode || "unknown"),
    currentRecovery: Number(nr.currentRecovery) || 0,
    currentRecoveryPercent: Math.round((Number(nr.currentRecovery) || 0) * 100),
    trendRecovery: Number(nr.trendRecovery) || 0,
    trendLabel: String(nr.trendLabel || ""),
    updatedAt: String(nr.updatedHourLabel || ""),
    checkedAt: new Date().toISOString()
  };
}

async function waitForProfitabilityWithClient(_client, _config, _accountLogTag) {
  // Profitability gate dihapus pasca announcement: rewards page & networkRecovery
  // sudah tidak ada. Selalu izinkan TX langsung.
  return null;
}

class RootsFiApiClient {
  constructor(config) {
    this.baseUrl = config.baseUrl;
    this.paths = config.paths;
    this.headers = config.headers;
    this.http = config.http;
    this.requestPacing = config.requestPacing;
    this.proxyUrl = config.proxyUrl || null;
    this._proxyBypassed = false; // Temporarily bypass proxy for Vercel operations
    this.cookieJar = new Map();
    this.initializeCookiesFromConfig();
  }

  // Proxy support disabled — all requests use direct connection.
  getProxyDispatcher() {
    return undefined;
  }

  _getFetchFn() {
    return fetch;
  }

  initializeCookiesFromConfig() {
    const configCookie = this.headers.cookie;
    if (configCookie) {
      this.parseCookieString(configCookie);
    }
  }

  parseCookieString(cookieStr) {
    if (!cookieStr) return;
    const pairs = cookieStr.split(";");
    for (const pair of pairs) {
      const eqIndex = pair.indexOf("=");
      if (eqIndex > 0) {
        const name = pair.slice(0, eqIndex).trim();
        const value = pair.slice(eqIndex + 1).trim();
        if (name) {
          this.cookieJar.set(name, value);
        }
      }
    }
  }

  parseSetCookieHeaders(headers) {
    const setCookieHeaders = [];

    if (typeof headers.getSetCookie === "function") {
      const values = headers.getSetCookie();
      if (Array.isArray(values) && values.length > 0) {
        setCookieHeaders.push(...values);
      }
    }

    if (setCookieHeaders.length === 0) {
      const combined = headers.get("set-cookie");
      if (combined) {
        setCookieHeaders.push(...this.splitCombinedSetCookieHeader(combined));
      }
    }

    for (const setCookie of setCookieHeaders) {
      const parts = setCookie.split(";")[0];
      const eqIndex = parts.indexOf("=");
      if (eqIndex > 0) {
        const name = parts.slice(0, eqIndex).trim();
        const value = parts.slice(eqIndex + 1).trim();
        if (name) {
          this.cookieJar.set(name, value);
        }
      }
    }
  }

  splitCombinedSetCookieHeader(headerValue) {
    if (!headerValue) {
      return [];
    }

    const parts = [];
    let current = "";
    let inExpiresAttr = false;

    for (let i = 0; i < headerValue.length; i += 1) {
      const next8 = headerValue.slice(i, i + 8).toLowerCase();
      if (next8 === "expires=") {
        inExpiresAttr = true;
      }

      const ch = headerValue[i];
      if (ch === "," && !inExpiresAttr) {
        const trimmed = current.trim();
        if (trimmed) {
          parts.push(trimmed);
        }
        current = "";
        continue;
      }

      current += ch;

      if (inExpiresAttr && ch === ";") {
        inExpiresAttr = false;
      }
    }

    const last = current.trim();
    if (last) {
      parts.push(last);
    }

    return parts;
  }

  mergeCookies(cookieMap) {
    for (const [name, value] of cookieMap) {
      this.cookieJar.set(name, value);
    }
  }

  hasValidSession() {
    return this.hasSecurityCookie() || this.hasAccountSessionCookie();
  }

  hasSecurityCookie() {
    return this.cookieJar.has("_vcrcs");
  }

  hasAccountSessionCookie() {
    return this.cookieJar.has("cantonbridge_session");
  }

  logCookieStatus(context) {
    console.log(
      `[info] Cookie status (${context}): _vcrcs=${this.hasSecurityCookie()} cantonbridge_session=${this.hasAccountSessionCookie()} total=${this.cookieJar.size}`
    );
  }

  getCookieStatus() {
    return {
      security: this.hasSecurityCookie(),
      session: this.hasAccountSessionCookie(),
      total: this.cookieJar.size
    };
  }

  getCookieHeader() {
    if (this.cookieJar.size === 0) {
      return "";
    }
    const pairs = [];
    for (const [name, value] of this.cookieJar) {
      pairs.push(`${name}=${value}`);
    }
    return pairs.join("; ");
  }

  buildUrl(endpointPath) {
    return new URL(endpointPath, this.baseUrl).toString();
  }

  buildHeaders(method, refererPath, hasBody, accept = "*/*") {
    const headers = {
      accept,
      "accept-language": this.headers.acceptLanguage,
      referer: this.buildUrl(refererPath),
      "user-agent": this.headers.userAgent
    };

    if (this.headers.sendBrowserClientHints) {
      headers["sec-ch-ua"] = this.headers.secChUa;
      headers["sec-ch-ua-mobile"] = this.headers.secChUaMobile;
      headers["sec-ch-ua-platform"] = this.headers.secChUaPlatform;
      headers["sec-fetch-dest"] = this.headers.secFetchDest;
      headers["sec-fetch-mode"] = this.headers.secFetchMode;
      headers["sec-fetch-site"] = this.headers.secFetchSite;
      headers.priority = this.headers.priority;
    }

    const cookieHeader = this.getCookieHeader();
    if (cookieHeader) {
      headers.cookie = cookieHeader;
    }

    for (const [key, value] of Object.entries(this.headers.extra)) {
      headers[key] = value;
    }

    if (method !== "GET") {
      headers.origin = this.baseUrl;
      if (hasBody) {
        headers["content-type"] = "application/json";
      }
    }

    return headers;
  }

  extractApiError(payload) {
    if (!isObject(payload)) {
      return "unknown API error";
    }

    if (isObject(payload.error)) {
      if (typeof payload.error.message === "string" && payload.error.message.trim()) {
        return payload.error.message;
      }
      if (typeof payload.error.code === "string" && payload.error.code.trim()) {
        return payload.error.code;
      }
    }

    if (typeof payload.error === "string" && payload.error.trim()) {
      return payload.error;
    }
    if (typeof payload.message === "string" && payload.message.trim()) {
      return payload.message;
    }

    if (isObject(payload.data) && typeof payload.data.message === "string" && payload.data.message.trim()) {
      return payload.data.message;
    }

    const compact = JSON.stringify(payload);
    if (compact && compact !== "{}") {
      return compact.slice(0, 240);
    }

    return "unknown API error";
  }

  shouldRetry(error) {
    const status = Number(error && error.status);
    if (status === 429 || (status >= 500 && status < 600)) {
      return true;
    }

    const message = String(error && error.message ? error.message : "").toLowerCase();
    return (
      message.includes("timed out") ||
      message.includes("fetch failed") ||
      message.includes("network") ||
      message.includes("aborted")
    );
  }

  async waitForPacing() {
    const min = this.requestPacing.minDelayMs;
    const jitter = this.requestPacing.jitterMs;
    const delay = min + (jitter > 0 ? randomIntInclusive(0, jitter) : 0);

    if (delay > 0) {
      await sleep(delay);
    }
  }

  async waitForBackoff(attempt) {
    const base = this.http.retryBaseDelayMs;
    if (base <= 0) {
      return;
    }

    const exponential = base * Math.pow(2, attempt - 1);
    const jitter = randomIntInclusive(0, Math.max(1, Math.floor(base / 2)));
    await sleep(exponential + jitter);
  }

  async requestJson(method, endpointPath, options = {}) {
    const body = options.body;
    const refererPath = options.refererPath || this.paths.onboard;
    const accept = options.accept || "*/*";
    const timeoutMs = clampToNonNegativeInt(options.timeoutMs, this.http.timeoutMs);
    const maxAttempts = 1 + this.http.maxRetries;
    // Allow disabling infinite timeout retry for non-critical endpoints
    const skipInfiniteTimeoutRetry = Boolean(options.skipInfiniteTimeoutRetry);

    let lastError = null;
    let attempt = 0;
    let consecutiveTimeouts = 0;

    while (true) {
      attempt += 1;
      const abortController = new AbortController();
      const timeoutId = setTimeout(() => abortController.abort(new Error("Request timed out")), timeoutMs);

      try {
        const fetchOptions = {
          method,
          headers: this.buildHeaders(method, refererPath, body !== undefined, accept),
          body: body === undefined ? undefined : JSON.stringify(body),
          signal: abortController.signal
        };
        const proxyDispatcher = this.getProxyDispatcher();
        if (proxyDispatcher) {
          fetchOptions.dispatcher = proxyDispatcher;
        }
        const fetchFn = this._getFetchFn();
        const response = await fetchFn(this.buildUrl(endpointPath), fetchOptions);

        clearTimeout(timeoutId);

        // Reset consecutive timeout counter on success
        consecutiveTimeouts = 0;

        this.parseSetCookieHeaders(response.headers);

        const contentType = String(response.headers.get("content-type") || "");
        const vercelMitigated = String(response.headers.get("x-vercel-mitigated") || "");
        const vercelRequestId = String(response.headers.get("x-vercel-id") || "");
        const text = await response.text();
        let payload = {};
        if (text) {
          try {
            payload = JSON.parse(text);
          } catch {
            if (text.trim().startsWith("<")) {
              if (vercelMitigated.toLowerCase() === "challenge") {
                const requestRef = vercelRequestId ? ` requestId=${vercelRequestId}` : "";
                throw new Error(
                  `Blocked by Vercel Security Checkpoint at ${endpointPath} (HTTP ${response.status}).` +
                  `${requestRef} Complete browser verification first, then place your session cookie in ` +
                  "tokens.json (selected account token profile) and retry."
                );
              }

              throw new Error(
                `Expected JSON from ${endpointPath}, but received HTML content (HTTP ${response.status}, content-type=${contentType || "unknown"}).`
              );
            }
            throw new Error(`Expected JSON response from ${endpointPath}, got: ${text.slice(0, 200)}`);
          }
        }

        if (!response.ok) {
          const requestError = new Error(
            `HTTP ${response.status} from ${endpointPath}: ${this.extractApiError(payload)}`
          );
          requestError.status = response.status;
          throw requestError;
        }

        if (isObject(payload) && Object.prototype.hasOwnProperty.call(payload, "success") && payload.success === false) {
          throw new Error(`API failure from ${endpointPath}: ${this.extractApiError(payload)}`);
        }

        await this.waitForPacing();
        return payload;
      } catch (error) {
        clearTimeout(timeoutId);
        lastError = error;

        // TIMEOUT errors: retry dengan exponential backoff, tapi limit consecutive timeouts
        // UNLESS skipInfiniteTimeoutRetry is set (for non-critical endpoints)
        if (isTimeoutError(error)) {
          if (skipInfiniteTimeoutRetry) {
            // For non-critical endpoints, just throw timeout error immediately
            throw error;
          }

          consecutiveTimeouts += 1;

          // Check if we've hit max consecutive timeouts - trigger soft restart
          if (consecutiveTimeouts >= TIMEOUT_MAX_CONSECUTIVE) {
            console.log(
              `[timeout-retry] ${method} ${endpointPath} hit ${consecutiveTimeouts} consecutive timeouts. ` +
              `Triggering SOFT RESTART for this account...`
            );
            throw new SoftRestartError(
              `Max consecutive timeouts (${TIMEOUT_MAX_CONSECUTIVE}) reached for ${method} ${endpointPath}`,
              consecutiveTimeouts
            );
          }

          const backoffMs = calculateTimeoutBackoffMs(attempt);
          const backoffSec = Math.round(backoffMs / 1000);
          console.log(
            `[timeout-retry] ${method} ${endpointPath} timed out (attempt ${attempt}, consecutive: ${consecutiveTimeouts}/${TIMEOUT_MAX_CONSECUTIVE}). ` +
            `Retrying in ${backoffSec}s (max: ${TIMEOUT_BACKOFF_MAX_MS / 1000}s)...`
          );
          await sleep(backoffMs);
          continue; // infinite retry untuk timeout
        }

        // Non-timeout errors: gunakan maxAttempts normal
        if (attempt < maxAttempts && this.shouldRetry(error)) {
          await this.waitForBackoff(attempt);
          continue;
        }

        throw error;
      }
    }
  }

  async preflightOnboard() {
    const abortController = new AbortController();
    const timeoutId = setTimeout(() => abortController.abort(new Error("Request timed out")), this.http.timeoutMs);

    try {
      const cookieHeader = this.getCookieHeader();
      const headers = {
        accept: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "accept-language": this.headers.acceptLanguage,
        "user-agent": this.headers.userAgent
      };
      if (cookieHeader) {
        headers.cookie = cookieHeader;
      }

      const fetchOptions = {
        method: "GET",
        headers,
        signal: abortController.signal
      };
      const proxyDispatcher = this.getProxyDispatcher();
      if (proxyDispatcher) {
        fetchOptions.dispatcher = proxyDispatcher;
      }
      const fetchFn = this._getFetchFn();
      const response = await fetchFn(this.buildUrl(this.paths.onboard), fetchOptions);

      this.parseSetCookieHeaders(response.headers);

      if (!response.ok) {
        const err = new Error(`Failed preflight GET ${this.paths.onboard}: HTTP ${response.status}`);
        err.status = response.status;
        throw err;
      }

      // Preflight only needs headers/cookies. Avoid waiting full HTML body to prevent stalls.
      if (response.body && typeof response.body.cancel === "function") {
        try {
          await response.body.cancel();
        } catch {
          // Ignore body cancel errors; cookies have already been captured from headers.
        }
      }
      await this.waitForPacing();
    } finally {
      clearTimeout(timeoutId);
    }
  }

  async syncAccount(refererPath) {
    return this.requestJson("POST", this.paths.syncAccount, { refererPath });
  }

  async getPending(refererPath) {
    return this.requestJson("GET", this.paths.authPending, { refererPath });
  }

  async sendOtp(email) {
    return this.requestJson("POST", this.paths.sendOtp, {
      refererPath: this.paths.onboard,
      body: { email }
    });
  }

  async verifyOtp(payload) {
    return this.requestJson("POST", this.paths.verifyOtp, {
      refererPath: this.paths.onboard,
      body: payload
    });
  }

  async finalizeReturning() {
    return this.requestJson("POST", this.paths.finalizeReturning, {
      refererPath: this.paths.onboard
    });
  }

  async getBalances() {
    return this.requestJson("GET", `${this.paths.walletBalances}?evm=cross-otc`, {
      refererPath: this.paths.bridge
    });
  }

  async checkCcCooldown(recipientIdentifier) {
    // HAR-aligned: recipientType=user, recipient=@username
    // Accepts username (with or without @) or falls back to canton_wallet for bare addresses
    const isUsername = recipientIdentifier && !recipientIdentifier.startsWith("roots");
    return this.requestJson("POST", this.paths.sendCcCooldown, {
      refererPath: this.paths.send,
      body: {
        recipientType: isUsername ? "user" : "canton_wallet",
        recipient: isUsername
          ? (recipientIdentifier.startsWith("@") ? recipientIdentifier : `@${recipientIdentifier}`)
          : recipientIdentifier,
        preferredNetwork: "canton",
        tokenType: "CC",
        instrumentId: "Amulet"
      }
    });
  }

  async resolveSendRecipient(username) {
    // HAR-aligned: API only accepts {username, preferredNetwork} — cantonPartyId returns 400
    return this.requestJson("POST", this.paths.sendResolve, {
      refererPath: this.paths.send,
      body: { username, preferredNetwork: "canton" }
    });
  }

  async sendCcTransfer(recipient, amount, idempotencyKey, trafficChallengeToken = null) {
    const body = {
      recipientType: "canton_wallet",
      recipient,
      amount,
      idempotencyKey,
      preferredNetwork: "canton",
      tokenType: "CC",
      instrumentId: "Amulet"
    };
    if (trafficChallengeToken) {
      body.acknowledgeTrafficWarning = true;
      body.trafficChallengeToken = trafficChallengeToken;
    }
    return this.requestJson("POST", this.paths.sendTransfer, {
      refererPath: this.paths.send,
      timeoutMs: 60000,
      skipInfiniteTimeoutRetry: true,
      body
    });
  }

  async getCcOutgoing() {
    return this.requestJson("GET", this.paths.walletCcOutgoing, {
      refererPath: this.paths.send
    });
  }

  async getSendHistory() {
    return this.requestJson("GET", this.paths.sendHistory, {
      refererPath: this.paths.send,
      skipInfiniteTimeoutRetry: true
    });
  }

  async getWalletOffers() {
    return this.requestJson("GET", this.paths.walletOffers, {
      refererPath: this.paths.bridge
    });
  }

  async acceptAllWalletOffers() {
    // Bulk accept: POST /api/wallet/offers (no body) accepts all pending offers at once.
    // Response: {"success":true,"data":{"offers":[],"accepted":N,"failed":N,"source":"fresh"}}
    return this.requestJson("POST", this.paths.walletOffers, {
      refererPath: this.paths.send,
      timeoutMs: 30000
    });
  }

  async acceptWalletOffer(offerPayload) {
    // Individual accept: POST /api/wallet/offers/accept with full offer object as body.
    return this.requestJson("POST", this.paths.walletOffersAccept, {
      refererPath: this.paths.send,
      timeoutMs: 30000,
      body: offerPayload
    });
  }

  async getSendLimits() {
    return this.requestJson("GET", this.paths.sendLimits, {
      refererPath: this.paths.send
    });
  }

  async recipientPreview(partyId) {
    return this.requestJson("POST", this.paths.recipientPreview, {
      refererPath: this.paths.send,
      body: { partyId }
    });
  }

  async sendCcTransferByUsername(username, amount, idempotencyKey, trafficChallengeToken = null) {
    // HAR-aligned: recipient must be "@username" format
    const normalizedRecipient = username.startsWith("@") ? username : `@${username}`;
    const body = {
      recipientType: "user",
      recipient: normalizedRecipient,
      amount,
      idempotencyKey,
      preferredNetwork: "canton",
      tokenType: "CC",
      instrumentId: "Amulet"
    };
    if (trafficChallengeToken) {
      body.acknowledgeTrafficWarning = true;
      body.trafficChallengeToken = trafficChallengeToken;
    }
    return this.requestJson("POST", this.paths.sendTransfer, {
      refererPath: this.paths.send,
      timeoutMs: 60000,
      skipInfiniteTimeoutRetry: true,
      body
    });
  }

  async sendCcTransferByAddress(address, amount, idempotencyKey, trafficChallengeToken = null) {
    // Fallback: address-based transfer using canton_wallet recipientType
    const body = {
      recipientType: "canton_wallet",
      recipient: address,
      amount,
      idempotencyKey,
      preferredNetwork: "canton",
      tokenType: "CC",
      instrumentId: "Amulet"
    };
    if (trafficChallengeToken) {
      body.acknowledgeTrafficWarning = true;
      body.trafficChallengeToken = trafficChallengeToken;
    }
    return this.requestJson("POST", this.paths.sendTransfer, {
      refererPath: this.paths.send,
      timeoutMs: 60000,
      skipInfiniteTimeoutRetry: true,
      body
    });
  }

  async getRewardsApi() {
    // Rewards page dihapus pasca announcement. Endpoint mungkin 404 — return no-op.
    return { data: {} };
  }

  async getRewardsThisWeek() {
    return { data: {} };
  }

  async getCrossOtcOrders(mineOnly = false) {
    const path = mineOnly
      ? `${this.paths.crossOtcOrders}?mine=1`
      : this.paths.crossOtcOrders;
    return this.requestJson("GET", path, {
      refererPath: "/cross-otc",
      timeoutMs: 20000
    });
  }

  async getCrossOtcReference() {
    return this.requestJson("GET", this.paths.crossOtcReference, {
      refererPath: "/cross-otc",
      timeoutMs: 15000
    });
  }

  async getCrossOtcStats() {
    return this.requestJson("GET", this.paths.crossOtcStats, {
      refererPath: "/cross-otc",
      timeoutMs: 15000
    });
  }

  async getAccountRewards() {
    return this.requestJson("GET", this.paths.accountRewards, {
      refererPath: "/cross-otc",
      timeoutMs: 15000,
      skipInfiniteTimeoutRetry: true
    });
  }

  async reserveOtcOrder(orderId) {
    return this.requestJson("POST", `${this.paths.crossOtcOrders}/${encodeURIComponent(orderId)}/reserve`, {
      refererPath: "/cross-otc",
      timeoutMs: 30000,
      body: {}
    });
  }

  async takeOtcOrder(orderId) {
    return this.requestJson("POST", `${this.paths.crossOtcOrders}/${encodeURIComponent(orderId)}/take`, {
      refererPath: "/cross-otc",
      timeoutMs: 60000,
      body: {}
    });
  }

  async createOtcOrder({ side, srcAmountDecimal, dstAmountDecimal, expiresHours = 1 }) {
    return this.requestJson("POST", this.paths.crossOtcOrders, {
      refererPath: "/cross-otc",
      timeoutMs: 30000,
      body: {
        side,
        srcAmountDecimal: String(srcAmountDecimal),
        dstAmountDecimal: String(dstAmountDecimal),
        expiresHours: Number(expiresHours)
      }
    });
  }

  async cancelOtcOrder(orderId) {
    return this.requestJson("POST", `${this.paths.crossOtcOrders}/${encodeURIComponent(orderId)}/cancel`, {
      refererPath: "/cross-otc",
      timeoutMs: 20000,
      body: {}
    });
  }
}

function printBalanceSummary(data) {
  const balances = isObject(data.balances) ? data.balances : {};
  const wallets = isObject(data.wallets) ? data.wallets : {};

  const ethereum = isObject(balances.ethereum) ? balances.ethereum : {};
  const base = isObject(balances.base) ? balances.base : {};
  const canton = isObject(balances.canton) ? balances.canton : {};

  const holdingsBySymbol = new Map();
  const pushHoldings = (items) => {
    if (!Array.isArray(items)) {
      return;
    }

    for (const holding of items) {
      if (!isObject(holding)) {
        continue;
      }

      const metadata = isObject(holding.metadata) ? holding.metadata : {};
      const rawSymbol = String(metadata.symbol || holding.instrumentId || "UNKNOWN").trim();
      const symbol = rawSymbol.toUpperCase();
      const amount = String(
        holding.amountDecimal ??
        holding.amount ??
        holding.amountBaseUnits ??
        "0"
      ).trim();

      if (!symbol) {
        continue;
      }

      if (!holdingsBySymbol.has(symbol)) {
        holdingsBySymbol.set(symbol, amount || "0");
      }
    }
  };

  // tokenHoldings usually has richer amount fields; use it before otherHoldings.
  pushHoldings(canton.tokenHoldings);
  pushHoldings(canton.otherHoldings);

  const ccBalance = holdingsBySymbol.get("CC") || "0";
  const cbtcBalance = holdingsBySymbol.get("CBTC") || "0";

  console.log("[balance] Base (L2)");
  console.log(`  USDC: ${base.usdc ?? ethereum.usdc ?? "n/a"}`);
  console.log(`  ETH: ${base.eth ?? ethereum.eth ?? "n/a"}`);

  console.log("[balance] Canton");
  console.log(`  USDCx: ${canton.usdcx ?? "n/a"}`);
  console.log(`  CC: ${ccBalance}`);
  console.log(`  Available: ${canton.available ?? "n/a"}`);

  if (holdingsBySymbol.size > 0) {
    console.log("[balance] Canton Holdings");
    for (const [symbol, amount] of holdingsBySymbol.entries()) {
      console.log(`  ${symbol}: ${amount}`);
    }
  }

  console.log("[wallets]");
  console.log(`  ethAddress: ${wallets.ethAddress ?? "n/a"}`);
  console.log(`  cantonPartyId: ${wallets.cantonPartyId ?? "n/a"}`);

  return {
    eth: String(base.eth ?? ethereum.eth ?? "n/a"),
    usdc: String(base.usdc ?? ethereum.usdc ?? "n/a"),
    usdcBase: String(base.usdc ?? "0"),
    usdcx: String(canton.usdcx ?? "n/a"),
    cc: String(ccBalance ?? "0"),
    cbtc: String(cbtcBalance ?? "0"),
    ccNumeric: Number(ccBalance) || 0,
    usdcBaseNumeric: Number(base.usdc) || 0,
    available: canton.available === true || canton.available === "true",
    cantonPartyId: String(wallets.cantonPartyId ?? "n/a")
  };
}

// ============================================================================
// AUTO-ACCEPT PENDING OFFERS
// ============================================================================
// Checks for pending CC transfer offers (inbound) and auto-accepts them.
// This is needed because sending via Canton address now creates a pending
// offer that the recipient must accept, rather than crediting directly.
// Uses bulk accept (POST /api/wallet/offers) which accepts all at once.
// ============================================================================

async function autoAcceptPendingOffers(client, accountLogTag = null) {
  const tagLog = (msg) => console.log(withAccountTag(accountLogTag, msg));
  try {
    const offersResp = await apiCallWithTimeout(
      () => client.getWalletOffers(),
      "Get wallet offers",
      15000
    );
    const offersData = isObject(offersResp.data) ? offersResp.data : {};
    const offers = Array.isArray(offersData.offers) ? offersData.offers : [];

    if (offers.length === 0) {
      return 0;
    }

    tagLog(`[offers] Found ${offers.length} pending offer(s), auto-accepting...`);
    for (const offer of offers) {
      const amount = offer.amountDecimal || "?";
      const from = offer.fromPartyHint || "unknown";
      tagLog(`[offers]   ${amount} CC from ${from}`);
    }

    // Bulk accept all offers at once
    try {
      const acceptResp = await apiCallWithTimeout(
        () => client.acceptAllWalletOffers(),
        "Accept all offers",
        30000
      );
      const acceptData = isObject(acceptResp.data) ? acceptResp.data : {};
      const accepted = acceptData.accepted || 0;
      const failed = acceptData.failed || 0;
      tagLog(`[offers] Bulk accept: ${accepted} accepted, ${failed} failed`);
      return accepted;
    } catch (bulkErr) {
      tagLog(`[offers] Bulk accept failed: ${bulkErr.message}, trying individual accept...`);

      // Fallback: accept individually
      let accepted = 0;
      for (const offer of offers) {
        try {
          await apiCallWithTimeout(
            () => client.acceptWalletOffer(offer),
            `Accept offer ${(offer.contractId || "").slice(0, 16)}...`,
            15000
          );
          accepted += 1;
          tagLog(`[offers] Accepted ${offer.amountDecimal || "?"} CC from ${offer.fromPartyHint || "unknown"}`);
        } catch (err) {
          tagLog(`[offers] Failed: ${err.message}`);
        }
      }
      tagLog(`[offers] Individual accept: ${accepted}/${offers.length}`);
      return accepted;
    }
  } catch (error) {
    tagLog(`[offers] Check failed (non-critical): ${error.message}`);
    return 0;
  }
}

// API call with timeout wrapper
const API_CALL_TIMEOUT_MS = 30000; // 30 seconds
const API_CALL_MAX_RETRIES = 2;

// Timeout infinite backoff settings
const TIMEOUT_BACKOFF_BASE_MS = 5000;       // 5 detik base delay
const TIMEOUT_BACKOFF_MAX_MS = 300000;      // 5 menit max delay
const TIMEOUT_BACKOFF_JITTER_MS = 30000;    // 0-30 detik random jitter
const TIMEOUT_MAX_CONSECUTIVE = 5;          // Max consecutive timeouts before soft restart

// Custom error class for soft restart
class SoftRestartError extends Error {
  constructor(message, consecutiveTimeouts) {
    super(message);
    this.name = "SoftRestartError";
    this.consecutiveTimeouts = consecutiveTimeouts;
    this.isSoftRestart = true;
  }
}

function calculateTimeoutBackoffMs(attempt) {
  // Exponential backoff: 5s, 10s, 20s, 40s, 80s, 160s, 300s (capped)
  const exponential = Math.min(
    TIMEOUT_BACKOFF_BASE_MS * Math.pow(2, attempt - 1),
    TIMEOUT_BACKOFF_MAX_MS
  );
  const jitter = randomIntInclusive(0, TIMEOUT_BACKOFF_JITTER_MS);
  return exponential + jitter;
}

async function apiCallWithTimeout(apiCall, label, timeoutMs = API_CALL_TIMEOUT_MS) {
  const startTime = Date.now();

  const timeoutPromise = new Promise((_, reject) => {
    setTimeout(() => reject(new Error(`${label} timeout after ${timeoutMs}ms`)), timeoutMs);
  });

  const result = await Promise.race([apiCall(), timeoutPromise]);
  const elapsed = Date.now() - startTime;
  console.log(`[info] ${label} completed in ${elapsed}ms`);
  return result;
}

async function apiCallWithRetry(
  apiCall,
  label,
  maxRetries = API_CALL_MAX_RETRIES,
  timeoutMs = API_CALL_TIMEOUT_MS,
  options = {}
) {
  let lastError = null;
  let attempt = 0;
  let consecutiveTimeouts = 0;
  const maxConsecutiveTimeouts = Math.max(
    1,
    clampToNonNegativeInt(options.maxConsecutiveTimeouts, TIMEOUT_MAX_CONSECUTIVE)
  );

  while (true) {
    attempt += 1;

    try {
      const attemptLabel = lastError && isTimeoutError(lastError)
        ? `${label} (timeout retry ${attempt})`
        : `${label} (attempt ${attempt}/${maxRetries})`;

      const result = await apiCallWithTimeout(apiCall, attemptLabel, timeoutMs);

      // Reset consecutive timeout counter on success
      consecutiveTimeouts = 0;
      return result;
    } catch (error) {
      lastError = error;

      // TIMEOUT errors: retry dengan exponential backoff, tapi limit consecutive timeouts
      if (isTimeoutError(error)) {
        consecutiveTimeouts += 1;

        // Check if we've hit max consecutive timeouts - trigger soft restart
        if (consecutiveTimeouts >= maxConsecutiveTimeouts) {
          console.log(
            `[timeout-retry] ${label} hit ${consecutiveTimeouts} consecutive timeouts. ` +
            `Triggering SOFT RESTART for this account...`
          );
          throw new SoftRestartError(
            `Max consecutive timeouts (${maxConsecutiveTimeouts}) reached for ${label}`,
            consecutiveTimeouts
          );
        }

        const backoffMs = calculateTimeoutBackoffMs(attempt);
        const backoffSec = Math.round(backoffMs / 1000);
        console.log(
          `[timeout-retry] ${label} timed out (attempt ${attempt}, consecutive: ${consecutiveTimeouts}/${maxConsecutiveTimeouts}). ` +
          `Retrying in ${backoffSec}s (max: ${TIMEOUT_BACKOFF_MAX_MS / 1000}s)...`
        );
        await sleep(backoffMs);
        continue;
      }

      // Non-timeout errors: gunakan maxRetries normal
      console.log(
        `[warn] ${label} attempt ${attempt}/${maxRetries} failed: ${error.message}`
      );

      if (attempt < maxRetries) {
        const retryDelay = 3000 * attempt; // 3s, 6s, etc
        console.log(`[info] Retrying ${label} in ${retryDelay / 1000}s...`);
        await sleep(retryDelay);
        continue;
      }

      // Max retries reached untuk non-timeout errors
      throw lastError;
    }
  }
}

async function recoverSendFlowByRefresh(
  client,
  config,
  onCheckpointRefresh,
  accountLogTag,
  recoveryAttempt,
  maxRecoveryAttempts,
  options = {}
) {
  const recoveryMode = String(options.mode || "light").toLowerCase();
  const reasonLabel = String(options.reason || "send-flow-transient");
  const withBrowserRefresh = recoveryMode === "full-browser";
  const forceConnectionReset = Boolean(options.forceConnectionReset);
  const runPreflight =
    typeof options.runPreflight === "boolean"
      ? options.runPreflight
      : withBrowserRefresh;
  const taggedLog = (message) => console.log(withAccountTag(accountLogTag, message));
  taggedLog(
    `[send-recovery] ${reasonLabel} ${recoveryAttempt}/${maxRecoveryAttempts}: ` +
    (withBrowserRefresh ? "reset connection + browser refresh" : "light reset (no browser)")
  );

  await resetConnectionPool({ forceReset: forceConnectionReset });

  if (withBrowserRefresh && config.session.autoRefreshCheckpoint === false) {
    taggedLog("[send-recovery] Browser refresh is disabled in config. Using connection reset only.");
  } else if (withBrowserRefresh) {
    try {
      const browserCookies = await solveBrowserChallenge(
        config.baseUrl,
        config.paths.onboard,
        config.headers.userAgent,
        true
      );
      client.mergeCookies(browserCookies);
      if (typeof onCheckpointRefresh === "function") {
        onCheckpointRefresh();
      }
      client.logCookieStatus("after send-recovery browser refresh");
    } catch (error) {
      taggedLog(`[warn] Send recovery browser refresh failed: ${error.message}`);
    }
  }

  if (runPreflight) {
    try {
      await client.preflightOnboard();
      taggedLog("[send-recovery] Preflight check completed");
    } catch (error) {
      taggedLog(`[warn] Send recovery preflight failed: ${error.message}`);
    }
  } else {
    taggedLog("[send-recovery] Skipping preflight in light mode");
  }

  const settleDelayMs = runPreflight
    ? Math.max(
      1000,
      clampToNonNegativeInt(config.session.checkpointSettleDelayMs, 3500)
    )
    : 2000;
  await sleep(settleDelayMs);
}

async function executeCcSendFlow(client, sendRequest, config, onCheckpointRefresh, accountLogTag = null, dashboard = null) {
  const stepLog = (message) => console.log(withAccountTag(accountLogTag, message));

  console.log(`[send] Target (${sendRequest.source}): ${sendRequest.label}`);
  console.log(`[send] Canton recipient: ${sendRequest.address}`);
  console.log(`[send] Amount: ${sendRequest.amount} CC`);

  // Step 1: Cooldown check with retry — prefer username (HAR: recipientType=user)
  stepLog("[step] Send cooldown check");
  const cooldownRecipientId = sendRequest.username || getAccountUsername(sendRequest.label) || sendRequest.address;
  const cooldownResponse = await apiCallWithRetry(
    () => client.checkCcCooldown(cooldownRecipientId),
    "Cooldown check"
  );
  const cooldownData = isObject(cooldownResponse.data) ? cooldownResponse.data : {};

  if (cooldownData.blocked) {
    throw new Error(
      `CC send cooldown is active. Retry after ${cooldownData.retryAfterSeconds ?? "unknown"} seconds.`
    );
  }
  console.log(
    `[info] Cooldown passed (retryAfterSeconds=${cooldownData.retryAfterSeconds ?? 0}, cooldownMinutes=${cooldownData.cooldownMinutes ?? "n/a"})`
  );

  // Step 2a: Recipient preview (matches browser flow)
  stepLog("[step] Recipient preview");
  try {
    await apiCallWithTimeout(
      () => client.recipientPreview(sendRequest.address),
      "Recipient preview",
      10000
    );
  } catch (error) {
    console.log(`[warn] Recipient preview failed (non-critical): ${error.message}`);
  }

  // Step 2b: Validate recipient address for transfer
  // Using address-based transfer (recipientType: canton_wallet) — confirmed working via HAR.
  // Username-based transfers return "Recipient username was not found" for internal accounts.
  if (!sendRequest.address) {
    throw new Error(
      `No canton address for recipient ${sendRequest.label || "?"} — cannot send.`
    );
  }
  stepLog(`[step] Transfer target: ${sendRequest.label} (address-based)`);

  // Step 4: Transfer CC with timeout recovery (web-like refresh + retry)
  if (!sendRequest.idempotencyKey) {
    sendRequest.idempotencyKey = crypto.randomUUID();
  }
  const idempotencyKey = sendRequest.idempotencyKey;

  // Step 3b: Recovery gate already passed (mode amber/green). At this
  // point the backend always requires a Turnstile token on /api/send/transfer
  // regardless of green/amber mode — so pre-solve unconditionally.
  stepLog(`[captcha] Pre-solving Turnstile sebelum transfer...`);
  if (dashboard) {
    dashboard.setState({
      phase: "captcha",
      send: `Pre-solve Turnstile — ${sendRequest.amount} CC -> ${sendRequest.label}`
    });
  }
  let challengeToken = null;
  try {
    challengeToken = await solveTurnstile(config.captcha);
    stepLog(`[captcha] Token siap, lanjut transfer dengan trafficChallengeToken.`);
    if (dashboard) {
      dashboard.setState({
        phase: "send",
        send: `${sendRequest.amount} CC -> ${sendRequest.label} (with captcha token)`
      });
    }
  } catch (error) {
    stepLog(`[captcha] Pre-solve Turnstile gagal: ${error.message}`);
    throw error;
  }

  stepLog(`[step] Transfer CC by address for ${sendRequest.label} (idempotencyKey=${idempotencyKey})`);

  let transferResponse = null;
  const MAX_CHALLENGE_RESOLVES = 3;
  let challengeResolveAttempts = 0;

  // Always use address-based transfer (canton_wallet)
  const runTransferOnce = () =>
    client.sendCcTransferByAddress(sendRequest.address, sendRequest.amount, idempotencyKey, challengeToken);

  while (true) {
    try {
      transferResponse = await apiCallWithTimeout(
        runTransferOnce,
        "Transfer CC",
        75000
      );
      break;
    } catch (error) {
      if (error && error.isSoftRestart) {
        throw error;
      }

      if (isTimeoutError(error)) {
        throw new SoftRestartError(
          `Transfer CC timeout for ${sendRequest.label}. Triggering immediate account restart.`,
          1
        );
      }

      if (isTrafficChallengeRequiredError(error)) {
        challengeResolveAttempts += 1;
        if (challengeResolveAttempts > MAX_CHALLENGE_RESOLVES) {
          stepLog(`[captcha] Sudah ${MAX_CHALLENGE_RESOLVES}x solve Turnstile masih 403. Menyerah untuk TX ini.`);
          throw error;
        }
        stepLog(
          `[captcha] Transfer ditolak 403 (challenge required). ` +
          `Fresh Turnstile token (attempt ${challengeResolveAttempts}/${MAX_CHALLENGE_RESOLVES})...`
        );
        if (dashboard) {
          dashboard.setState({
            phase: "captcha",
            send: `403 Challenge — solving fresh Turnstile #${challengeResolveAttempts} (${sendRequest.amount} CC -> ${sendRequest.label})`
          });
        }
        // Always discard old token; Turnstile tokens are single-use.
        challengeToken = null;
        try {
          challengeToken = await solveTurnstile(config.captcha);
        } catch (solveError) {
          stepLog(`[captcha] Gagal solve Turnstile: ${solveError.message}`);
          throw solveError;
        }
        stepLog(`[captcha] Token fresh siap, retry transfer...`);
        if (dashboard) {
          dashboard.setState({
            phase: "send",
            send: `${sendRequest.amount} CC -> ${sendRequest.label} (retry with fresh token)`
          });
        }
        continue;
      }

      if (isTrafficCongestionError(error)) {
        const allowedLabel = (config.profitability.allowedModes || ["amber", "green"]).join("/");
        stepLog(
          `[profitability] Transfer ditolak 409 (Network congested). ` +
          `Menunggu mode ${allowedLabel}...`
        );
        // Update dashboard to show we're waiting for profitability, not stuck on SEND
        if (dashboard) {
          dashboard.setState({
            phase: "profitability-check",
            send: `409 Congested — waiting mode ${allowedLabel} (${sendRequest.amount} CC -> ${sendRequest.label})`
          });
        }
        await waitForProfitabilityWithClient(client, config, accountLogTag);
        stepLog(`[profitability] Recovery OK, retry transfer...`);
        // Restore dashboard to send phase for retry
        if (dashboard) {
          dashboard.setState({
            phase: "send",
            send: `${sendRequest.amount} CC -> ${sendRequest.label} (retry after 409)`
          });
        }
        continue;
      }

      throw error;
    }
  }

  const transferData = isObject(transferResponse && transferResponse.data) ? transferResponse.data : {};
  const transferId = String(transferData.id || "").trim();
  const transferUpdateId = isObject(transferData.command_result) && isObject(transferData.command_result.transfer)
    ? String(transferData.command_result.transfer.updateId || "").trim()
    : "";

  if (transferId) {
    console.log(
      `[info] Transfer submitted: id=${transferId}${transferUpdateId ? ` updateId=${transferUpdateId}` : ""}`
    );
  }

  // Step 6: Check outgoing (optional, non-fatal)
  try {
    const outgoingResponse = await apiCallWithTimeout(
      () => client.getCcOutgoing(),
      "Get outgoing",
      15000
    );
    const outgoing = isObject(outgoingResponse.data) && Array.isArray(outgoingResponse.data.outgoing)
      ? outgoingResponse.data.outgoing
      : [];
    console.log(`[info] Pending outgoing CC count: ${outgoing.length}`);
  } catch (error) {
    console.log(`[warn] Could not read cc-outgoing: ${error.message}`);
  }

  return {
    transferId,
    status: transferId ? "submitted" : "unknown",
    amount: String(sendRequest.amount),
    recipient: String(sendRequest.label)
  };
}

async function executeCcSendFlowWithCheckpointRecovery(
  client,
  sendRequest,
  config,
  onCheckpointRefresh,
  accountLogTag = null,
  dashboard = null
) {
  const MAX_CHECKPOINT_REFRESH_ATTEMPTS = 1;
  const MAX_TRANSIENT_REFRESH_ATTEMPTS = 2;
  let checkpointRefreshAttempt = 0;
  let transientRefreshAttempt = 0;

  while (true) {
    try {
      return await executeCcSendFlow(client, sendRequest, config, onCheckpointRefresh, accountLogTag, dashboard);
    } catch (error) {
      if (error && error.isSoftRestart) {
        throw error;
      }

      if (isVercelCheckpointError(error)) {
        if (!config.session.autoRefreshCheckpoint) {
          throw new Error(
            "Send flow hit Vercel checkpoint and auto refresh is disabled (config.session.autoRefreshCheckpoint=false)."
          );
        }

        if (checkpointRefreshAttempt >= MAX_CHECKPOINT_REFRESH_ATTEMPTS) {
          throw error;
        }

        checkpointRefreshAttempt += 1;
        console.log("[info] Send flow hit Vercel checkpoint, refreshing browser security cookies...");
        const browserCookies = await solveBrowserChallenge(
          config.baseUrl,
          config.paths.onboard,
          config.headers.userAgent,
          true
        );
        client.mergeCookies(browserCookies);
        if (typeof onCheckpointRefresh === "function") {
          onCheckpointRefresh();
        }
        client.logCookieStatus("after browser refresh for send");
        continue;
      }

      if (isTransientSendFlowError(error) && transientRefreshAttempt < MAX_TRANSIENT_REFRESH_ATTEMPTS) {
        transientRefreshAttempt += 1;
        await recoverSendFlowByRefresh(
          client,
          config,
          onCheckpointRefresh,
          accountLogTag,
          transientRefreshAttempt,
          MAX_TRANSIENT_REFRESH_ATTEMPTS,
          {
            mode: "light",
            reason: "send-flow-transient",
            runPreflight: false,
            forceConnectionReset: transientRefreshAttempt >= MAX_TRANSIENT_REFRESH_ATTEMPTS
          }
        );
        console.log(
          `[info] Retrying full send flow after transient recovery (${transientRefreshAttempt}/${MAX_TRANSIENT_REFRESH_ATTEMPTS})...`
        );
        continue;
      }

      throw error;
    }
  }
}

// Balance check with timeout - returns null if timeout/error (proceed with TX anyway)
const BALANCE_CHECK_TIMEOUT_MS = 10000;
const TX_RETRY_INITIAL_DELAY_SECONDS = 15;
const TX_RETRY_DELAY_STEP_SECONDS = 30;
const SESSION_REUSE_TIMEOUT_BACKOFF_SECONDS = 15;

async function getBalanceWithTimeout(client, timeoutMs = BALANCE_CHECK_TIMEOUT_MS) {
  const startTime = Date.now();

  try {
    const balancePromise = client.getBalances();
    const timeoutPromise = new Promise((_, reject) => {
      setTimeout(() => reject(new Error("Balance check timeout")), timeoutMs);
    });

    const balanceResponse = await Promise.race([balancePromise, timeoutPromise]);
    const elapsed = Date.now() - startTime;
    console.log(`[info] Balance check completed in ${elapsed}ms`);

    const balanceData = balanceResponse && balanceResponse.data ? balanceResponse.data : {};
    return printBalanceSummary(balanceData);
  } catch (error) {
    const elapsed = Date.now() - startTime;
    console.log(`[warn] Balance check failed after ${elapsed}ms: ${error.message}`);
    return null; // Return null to indicate balance check failed/timeout
  }
}

// Track tier minimum qualifying send per account (from /api/rewards tierProgress)
const tierMinSendByAccount = new Map();

function getAccountTierMinSend(accountName) {
  return tierMinSendByAccount.get(accountName) || 25; // default to tier 2 (Advanced) until fetched
}

// Track quality score per account (from /api/rewards weeklyQuality.score)
// Accounts with score < config.safety.minScoreThreshold are QUARANTINED:
//   - The account stops sending
//   - Other accounts stop sending TO this account
// Threshold is configurable via config.json safety.minScoreThreshold (default: 30)
let QUALITY_SCORE_QUARANTINE_THRESHOLD = 30;
let QUALITY_SCORE_WARN_THRESHOLD = 30;
const qualityScoreByAccount = new Map();

// Track initial CC balance per account — captured ONCE at first login, never refreshed
const initialCcBalanceByAccount = new Map();

function recordInitialCcBalance(accountName, ccNumeric) {
  if (!accountName) return;
  if (initialCcBalanceByAccount.has(accountName)) return;
  const value = Number(ccNumeric);
  if (!Number.isFinite(value)) return;
  initialCcBalanceByAccount.set(accountName, value);
}

function getTotalInitialCcBalance() {
  let total = 0;
  for (const value of initialCcBalanceByAccount.values()) {
    if (Number.isFinite(value)) total += value;
  }
  return total;
}

// Track Rewards earned this week per account (from /api/rewards tierProgress.earnedThisWeekCc)
const rewardsThisWeekByAccount = new Map();
// Snapshot of rewards captured at first refresh — used to compute diff earned during this bot session
const rewardsInitialByAccount = new Map();

function getAccountRewardsThisWeek(accountName) {
  const entry = rewardsThisWeekByAccount.get(accountName);
  return isObject(entry) ? entry : null;
}

function getAccountRewardsInitial(accountName) {
  const entry = rewardsInitialByAccount.get(accountName);
  return isObject(entry) ? entry : null;
}

function getAccountRewardsDiff(accountName) {
  const current = getAccountRewardsThisWeek(accountName);
  const initial = getAccountRewardsInitial(accountName);
  if (!isObject(current) || !isObject(initial)) return null;
  const diffCc = Number.isFinite(current.cc) && Number.isFinite(initial.cc) ? current.cc - initial.cc : 0;
  const diffUsd = Number.isFinite(current.usd) && Number.isFinite(initial.usd) ? current.usd - initial.usd : 0;
  return { cc: diffCc, usd: diffUsd };
}

function getTotalRewardsThisWeek() {
  let totalCc = 0;
  let totalUsd = 0;
  for (const entry of rewardsThisWeekByAccount.values()) {
    if (!isObject(entry)) continue;
    if (Number.isFinite(entry.cc)) totalCc += entry.cc;
    if (Number.isFinite(entry.usd)) totalUsd += entry.usd;
  }
  return { cc: totalCc, usd: totalUsd };
}

function getTotalRewardsDiff() {
  let totalCc = 0;
  let totalUsd = 0;
  for (const accountName of rewardsThisWeekByAccount.keys()) {
    const diff = getAccountRewardsDiff(accountName);
    if (!isObject(diff)) continue;
    if (Number.isFinite(diff.cc)) totalCc += diff.cc;
    if (Number.isFinite(diff.usd)) totalUsd += diff.usd;
  }
  return { cc: totalCc, usd: totalUsd };
}

// Quarantine set: accounts with score < threshold
// These accounts are excluded from both sending and receiving
const quarantinedAccounts = new Set();

function getAccountQualityScore(accountName) {
  return qualityScoreByAccount.has(accountName) ? qualityScoreByAccount.get(accountName) : null;
}

function isAccountQuarantined(accountName) {
  return quarantinedAccounts.has(String(accountName || "").trim());
}

function quarantineAccount(accountName, score) {
  const name = String(accountName || "").trim();
  if (!name) return;
  quarantinedAccounts.add(name);
  console.log(`[quarantine] Account '${name}' QUARANTINED (score ${score} < ${QUALITY_SCORE_QUARANTINE_THRESHOLD}) — no send/receive until score recovers`);
}

function unquarantineAccount(accountName) {
  const name = String(accountName || "").trim();
  if (quarantinedAccounts.delete(name)) {
    console.log(`[quarantine] Account '${name}' RELEASED from quarantine — score recovered`);
  }
}

function formatQualityScoreLabel(score) {
  if (score === null || score === undefined) return "-";
  const num = Number(score);
  if (!Number.isFinite(num)) return "-";
  if (num < QUALITY_SCORE_WARN_THRESHOLD) {
    return `LOW ${num}/100`;
  }
  return `${num}/100`;
}

async function refreshThisWeekRewardDashboard(_client, _dashboard, _accountLogTag = null, accountName = null) {
  // Rewards page dihapus pasca announcement. Skip semua call ke /api/rewards.
  // Tetap mark tierFetched supaya guard "tier belum di-fetch" tidak menghalangi send.
  if (accountName) {
    tierFetchedByAccount.add(accountName);
  }
}

async function executeSendBatch(client, sendRequests, config, dashboard, onCheckpointRefresh, accountLogTag = null, senderAccountName = null) {
  if (!Array.isArray(sendRequests) || sendRequests.length === 0) {
    return {
      completedTx: 0,
      skippedTx: 0,
      deferred: false,
      deferReason: null,
      deferRetryAfterSeconds: 0,
      deferRequiredAmount: null,
      deferAvailableAmount: null,
      deferProgress: null,
      deferSendLabel: null,
      sentRecipientLabels: []
    };
  }

  const stepLog = (message) => console.log(withAccountTag(accountLogTag, message));
  const minDelayTxSec = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(config.send, "minDelayTxSeconds")
      ? config.send.minDelayTxSeconds
      : config.send.delayTxSeconds,
    INTERNAL_API_DEFAULTS.send.minDelayTxSeconds
  );
  const maxDelayTxSec = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(config.send, "maxDelayTxSeconds")
      ? config.send.maxDelayTxSeconds
      : config.send.delayTxSeconds,
    INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds
  );
  const delayTxMinSec = Math.min(minDelayTxSec, maxDelayTxSec);
  const delayTxMaxSec = Math.max(minDelayTxSec, maxDelayTxSec);

  let completedTx = 0;
  let skippedTx = 0;
  let deferredState = null;
  const sentRecipientLabels = [];
  const MAX_SEND_FLOW_RETRY_ATTEMPTS = 4;
  const BALANCE_GUARD_RETRY_DELAY_MS = 2000;
  const BALANCE_GUARD_RETRY_TIMEOUT_MS = BALANCE_CHECK_TIMEOUT_MS + 5000;
  const BALANCE_GUARD_MIN_BUFFER_CC = config.safety ? config.safety.minHoldBalanceCc : 10; // TVL reserve from config
  const recipientCandidateMode = sendRequests.every(
    (entry) => isObject(entry) && entry.internalRecipientCandidate === true
  );
  const expectedTxCount = recipientCandidateMode ? 1 : sendRequests.length;

  dashboard.setState({
    swapsTotal: `0/${expectedTxCount}`,
    swapsOk: "0",
    swapsFail: "0"
  });

  for (let index = 0; index < sendRequests.length; index += 1) {
    if (recipientCandidateMode && completedTx > 0) {
      break;
    }

    const sendRequest = sendRequests[index];
    const progress = `${index + 1}/${sendRequests.length}`;
    const progressForDashboard = `${Math.min(index + 1, expectedTxCount)}/${expectedTxCount}`;

    // Check balance before each TX (with timeout fallback)
    stepLog(`[step] Check balance before tx ${progress} (timeout=${BALANCE_CHECK_TIMEOUT_MS}ms)`);
    let currentBalance = await getBalanceWithTimeout(client);

    if (currentBalance === null) {
      stepLog(`[step] Balance guard retry before tx ${progress} (timeout=${BALANCE_GUARD_RETRY_TIMEOUT_MS}ms)`);
      await sleep(BALANCE_GUARD_RETRY_DELAY_MS);
      currentBalance = await getBalanceWithTimeout(client, BALANCE_GUARD_RETRY_TIMEOUT_MS);
    }

    if (currentBalance !== null) {
      dashboard.setState({
        balance: `CC=${currentBalance.cc} | USDC=${currentBalance.usdcBase} | CBTC=${currentBalance.cbtc}`
      });

      console.log(`[info] Current balance: CC=${currentBalance.cc} (${currentBalance.ccNumeric}) | Available=${currentBalance.available}`);
      updateAccountCcBalance(senderAccountName, currentBalance.ccNumeric);
      updateAccountUsdcBalance(senderAccountName, Number(currentBalance.usdcBase) || 0);

      // Check if balance is sufficient (use ccNumeric for comparison)
      const requiredAmount = Number(sendRequest.amount);
      const requiredWithBuffer = requiredAmount + BALANCE_GUARD_MIN_BUFFER_CC;
      const availableAmount = currentBalance.ccNumeric;

      if (currentBalance.available === false) {
        const retryAfterSeconds = TX_RETRY_INITIAL_DELAY_SECONDS;
        console.log(
          `[warn] Deferring tx ${progress} because balance is not available yet ` +
          `(amount=${requiredAmount}, cc=${currentBalance.cc})`
        );
        dashboard.setState({
          phase: "cooldown",
          swapsTotal: progressForDashboard,
          swapsOk: String(completedTx),
          swapsFail: String(skippedTx),
          transfer: `deferred (balance-not-available) (${progress})`,
          cooldown: `${retryAfterSeconds}s`,
          send: `Deferred ${sendRequest.amount} CC -> ${sendRequest.label} (balance unavailable)`
        });

        deferredState = {
          reason: "balance-not-available",
          retryAfterSeconds,
          requiredAmount,
          availableAmount,
          progress,
          sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
        };
        break;
      }

      if (!Number.isFinite(availableAmount) || availableAmount < requiredWithBuffer) {
        // Auto-reduce: send what we can afford instead of deferring.
        // Respect config.min AND tier min — whichever is higher
        const tierMin = senderAccountName ? getAccountTierMinSend(senderAccountName) : 10;
        const senderTierKeyForMin = getAccountTierKey(senderAccountName);
        const senderTierRangeForMin = resolveAmountRangeForTier(config.send, senderTierKeyForMin);
        const configMin = Number(senderTierRangeForMin && senderTierRangeForMin.min) || 0;
        const configMax = Number(senderTierRangeForMin && senderTierRangeForMin.max) || 0;
        const reducedBuffer = BALANCE_GUARD_MIN_BUFFER_CC;
        const maxSendable = Number.isFinite(availableAmount) ? availableAmount - reducedBuffer : 0;
        // Effective min = whichever is higher between tier min and config min
        const effectiveMin = Math.max(tierMin, configMin);

        if (maxSendable >= effectiveMin) {
          const decimals = clampToNonNegativeInt(
            senderTierRangeForMin && senderTierRangeForMin.decimals, 3
          );
          const factor = Math.pow(10, decimals);
          // Clamp max to config.max and what balance allows
          const effectiveMax = Math.min(maxSendable, configMax > 0 ? configMax : maxSendable);
          const maxUnits = Math.floor(effectiveMax * factor);
          const minUnits = Math.ceil(effectiveMin * factor);
          const randomUnits = minUnits < maxUnits
            ? Math.floor(Math.random() * (maxUnits - minUnits + 1)) + minUnits
            : maxUnits;
          const reducedAmount = (randomUnits / factor).toFixed(decimals);
          console.log(
            `[auto-adjust] ${progress} balance=${availableAmount.toFixed(2)} CC, reserve=${reducedBuffer} CC, ` +
            `sendable=${maxSendable.toFixed(2)} CC | ` +
            `range ${effectiveMin}-${(maxUnits / factor).toFixed(decimals)} → ${reducedAmount} CC ` +
            `(was ${requiredAmount} CC)`
          );
          sendRequest.amount = reducedAmount;
          // Continue with adjusted amount — do NOT break/defer
        } else {
          const retryAfterSeconds = TX_RETRY_INITIAL_DELAY_SECONDS;
          console.log(
            `[defer] ${progress} balance=${availableAmount} CC too low: ` +
            `sendable=${maxSendable.toFixed(2)} CC < min=${effectiveMin} CC ` +
            `(need ${effectiveMin + reducedBuffer} CC to send). Retry in ${retryAfterSeconds}s`
          );
          dashboard.setState({
            phase: "cooldown",
            swapsTotal: progressForDashboard,
            swapsOk: String(completedTx),
            swapsFail: String(skippedTx),
            transfer: `deferred (insufficient) (${progress})`,
            cooldown: `${retryAfterSeconds}s`,
            send: `Deferred ${sendRequest.amount} CC -> ${sendRequest.label} (waiting inbound)`
          });

          deferredState = {
            reason: "insufficient-balance",
            retryAfterSeconds,
            requiredAmount,
            availableAmount,
            progress,
            sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
          };
          break;
        }
      }
    } else {
      // Balance check is required to avoid useless transfer timeouts when funds are not ready.
      const retryAfterSeconds = TX_RETRY_INITIAL_DELAY_SECONDS;
      console.log(
        `[warn] Deferring tx ${progress} because balance check is unavailable after retry ` +
        `(retry in ${retryAfterSeconds}s)`
      );
      dashboard.setState({
        phase: "cooldown",
        swapsTotal: progressForDashboard,
        swapsOk: String(completedTx),
        swapsFail: String(skippedTx),
        transfer: `deferred (balance-check-unavailable) (${progress})`,
        cooldown: `${retryAfterSeconds}s`,
        send: `Deferred ${sendRequest.amount} CC -> ${sendRequest.label} (balance check unavailable)`
      });

      deferredState = {
        reason: "balance-check-unavailable",
        retryAfterSeconds,
        requiredAmount: Number(sendRequest.amount),
        availableAmount: null,
        progress,
        sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
      };
      break;
    }

    // Enforce per-account TX delay (config-driven, humanLikeDelay range) +
    // hourly cap (HOURLY_MAX_TX_PER_ACCOUNT, default 10/hour) as safety net.
    if (senderAccountName) {
      const hourlyWaitMs = getHourlyResetWaitMs(senderAccountName);
      if (hourlyWaitMs > 0) {
        const waitSec = Math.ceil(hourlyWaitMs / 1000);
        stepLog(`[hourly] ${senderAccountName} hit ${HOURLY_MAX_TX_PER_ACCOUNT}/hr cap, waiting ${waitSec}s`);
        dashboard.setState({
          phase: "cooldown",
          cooldown: `${waitSec}s (hourly-cap)`,
          send: `Hourly cap ${HOURLY_MAX_TX_PER_ACCOUNT}/hr — waiting ${waitSec}s`
        });
        setAccountCooldownEnd(senderAccountName, Date.now() + hourlyWaitMs);
        await sleep(hourlyWaitMs);
        setAccountCooldownEnd(senderAccountName, 0);
      }

      const lastTxMs = lastTxTimestampByAccount.get(senderAccountName) || 0;
      if (lastTxMs > 0) {
        const minGapSec = clampToNonNegativeInt(
          config.send && config.send.minDelayTxSeconds,
          INTERNAL_API_DEFAULTS.send.minDelayTxSeconds
        );
        const maxGapSec = Math.max(
          minGapSec,
          clampToNonNegativeInt(
            config.send && config.send.maxDelayTxSeconds,
            INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds
          )
        );
        const requiredGapSec = humanLikeDelay(minGapSec, maxGapSec);
        const requiredGapMs = (requiredGapSec * 1000) + PER_ACCOUNT_TX_COOLDOWN_BUFFER_MS;
        const elapsedMs = Date.now() - lastTxMs;
        if (elapsedMs < requiredGapMs) {
          const waitMs = requiredGapMs - elapsedMs;
          const waitSec = Math.ceil(waitMs / 1000);
          stepLog(`[cooldown] ${senderAccountName} per-account TX delay: waiting ${waitSec}s (range ${minGapSec}-${maxGapSec}s)`);
          dashboard.setState({
            phase: "cooldown",
            cooldown: `${waitSec}s (per-account)`,
            send: `Per-account delay ${waitSec}s`
          });
          setAccountCooldownEnd(senderAccountName, Date.now() + waitMs);
          await sleep(waitMs);
          setAccountCooldownEnd(senderAccountName, 0);
        }
      }
    }

    // Track send target for dashboard "To" column
    if (senderAccountName) {
      updateLastSendTarget(senderAccountName, sendRequest.label);
    }

    dashboard.setState({
      phase: "send",
      send: `${sendRequest.amount} CC -> ${sendRequest.label} (${progress})`,
      swapsTotal: progressForDashboard,
      swapsOk: String(completedTx),
      swapsFail: String(skippedTx)
    });

    stepLog(`[step] Send tx ${progress}: ${sendRequest.amount} CC -> ${sendRequest.label}`);

    let sendResult = null;
    let retryAttempt = 0;
    let skipToNextCandidate = false;
    let hardReloginAttempt = 0;
    const MAX_HARD_RELOGIN_ATTEMPTS = 1;
    let fragmentedAmountReductionCount = 0;
    const MAX_FRAGMENTED_BALANCE_REDUCTIONS = 4;
    while (sendResult === null && deferredState === null) {
      try {
        sendResult = await executeCcSendFlowWithCheckpointRecovery(
          client,
          sendRequest,
          config,
          onCheckpointRefresh,
          accountLogTag,
          dashboard
        );
      } catch (error) {
        if (error && error.isSoftRestart) {
          throw error;
        }

        if (isBalanceContractFragmentationError(error)) {
          const errorMessage = String(error && error.message ? error.message : error);

          if (fragmentedAmountReductionCount < MAX_FRAGMENTED_BALANCE_REDUCTIONS) {
            const nextAmount = getReducedAmountForFragmentedBalance(sendRequest.amount, config.send);
            if (nextAmount && Number(nextAmount) < Number(sendRequest.amount)) {
              const previousAmount = sendRequest.amount;
              fragmentedAmountReductionCount += 1;
              sendRequest.amount = nextAmount;

              if (recipientCandidateMode) {
                for (let candidateIndex = index + 1; candidateIndex < sendRequests.length; candidateIndex += 1) {
                  sendRequests[candidateIndex].amount = nextAmount;
                }
              }

              console.warn(
                `[warn] TX ${progress} fragmented balance contracts. ` +
                `Reducing amount ${previousAmount} -> ${nextAmount} ` +
                `(step ${fragmentedAmountReductionCount}/${MAX_FRAGMENTED_BALANCE_REDUCTIONS}) and retrying now. ` +
                `Detail: ${errorMessage}`
              );

              dashboard.setState({
                phase: "cooldown",
                transfer: `reduce-amount (${progress})`,
                send: `Fragmented balance: ${previousAmount} -> ${nextAmount}`,
                cooldown: "0s",
                swapsTotal: progressForDashboard,
                swapsOk: String(completedTx),
                swapsFail: String(skippedTx)
              });
              continue;
            }
          }

          const retryAfterSeconds = 180;
          console.warn(
            `[warn] TX ${progress} fragmented balance still blocking after reductions. ` +
            `Deferring ${retryAfterSeconds}s. Last error: ${errorMessage}`
          );
          dashboard.setState({
            phase: "cooldown",
            transfer: `deferred (fragmented-balance) (${progress})`,
            send: `Deferred ${sendRequest.amount} CC -> ${sendRequest.label} for ${retryAfterSeconds}s`,
            cooldown: `${retryAfterSeconds}s`,
            swapsTotal: progressForDashboard,
            swapsOk: String(completedTx),
            swapsFail: String(skippedTx)
          });
          deferredState = {
            reason: "fragmented-balance",
            retryAfterSeconds,
            requiredAmount: Number(sendRequest.amount),
            availableAmount: null,
            progress,
            sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
          };
          break;
        }

        // ── Adaptive hourly limit: learn from server + smart wait ──
        if (isHourlySendLimitError(error)) {
          // Learn the server's actual cap from this 400 rejection
          if (senderAccountName) {
            learnHourlyCapFromServer(senderAccountName, error);
          }

          // Calculate smart wait: time until oldest TX in the window expires
          const hourlyWaitMs = senderAccountName ? getHourlyResetWaitMs(senderAccountName) : 0;
          const smartWaitSec = hourlyWaitMs > 0
            ? Math.ceil(hourlyWaitMs / 1000)
            : 3600; // Fallback: full hour if no data
          const errorMessage = String(error && error.message ? error.message : error);
          console.warn(
            `[adaptive-cap] TX ${progress} server hourly limit (HTTP 400). ` +
            `Learned cap: ${HOURLY_MAX_TX_PER_ACCOUNT}/hr. Waiting ${smartWaitSec}s. Error: ${errorMessage}`
          );
          dashboard.setState({
            phase: "cooldown",
            status: "COOLDOWN",
            transfer: `hourly-limit (${progress})`,
            send: `Server limit ${HOURLY_MAX_TX_PER_ACCOUNT}/hr — waiting ${smartWaitSec}s`,
            cooldown: `${smartWaitSec}s (server-limit)`,
            swapsTotal: progressForDashboard,
            swapsOk: String(completedTx),
            swapsFail: String(skippedTx)
          });
          deferredState = {
            reason: "server-hourly-limit",
            retryAfterSeconds: smartWaitSec,
            requiredAmount: Number(sendRequest.amount),
            availableAmount: null,
            progress,
            sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
          };
          break;
        }

        if (isSendEligibilityDelayError(error)) {
          // Distinguish general 180s cooldown from reciprocal 10-min cooldown.
          const SEND_COOLDOWN_GENERAL_MIN_SECONDS = 185; // 180s server rule + 5s buffer
          const SEND_COOLDOWN_RECIPROCAL_THRESHOLD_SECONDS = 400;
          const serverRetryAfter = parseRetryAfterSeconds(error, SEND_COOLDOWN_GENERAL_MIN_SECONDS);
          const retryAfterSeconds = serverRetryAfter >= SEND_COOLDOWN_RECIPROCAL_THRESHOLD_SECONDS
            ? serverRetryAfter // Likely reciprocal cooldown, respect full duration
            : Math.max(serverRetryAfter, SEND_COOLDOWN_GENERAL_MIN_SECONDS); // General 180s cooldown
          const errorMessage = String(error && error.message ? error.message : error);

          if (recipientCandidateMode && index < sendRequests.length - 1) {
            console.warn(
              `[warn] Recipient candidate ${sendRequest.label} blocked (${retryAfterSeconds}s). ` +
              `Trying next candidate...`
            );
            dashboard.setState({
              phase: "cooldown",
              transfer: `candidate-blocked (${progress})`,
              send: `Candidate blocked, trying next recipient...`,
              cooldown: `${retryAfterSeconds}s`,
              swapsTotal: progressForDashboard,
              swapsOk: String(completedTx),
              swapsFail: String(skippedTx)
            });
            skipToNextCandidate = true;
            break;
          }

          console.warn(
            `[warn] Deferring tx ${progress} due server send rule. Retry in ${retryAfterSeconds}s: ${errorMessage}`
          );
          dashboard.setState({
            phase: "cooldown",
            transfer: `deferred (server-cooldown) (${progress})`,
            send: `Deferred ${sendRequest.amount} CC -> ${sendRequest.label} for ${retryAfterSeconds}s`,
            cooldown: `${retryAfterSeconds}s`,
            swapsTotal: progressForDashboard,
            swapsOk: String(completedTx),
            swapsFail: String(skippedTx)
          });
          deferredState = {
            reason: "server-cooldown",
            retryAfterSeconds,
            requiredAmount: Number(sendRequest.amount),
            availableAmount: null,
            progress,
            sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
          };
          break;
        }

        retryAttempt += 1;
        const transientSendError = isTransientSendFlowError(error);
        const retryDelaySeconds = transientSendError
          ? Math.min(30, 6 + ((retryAttempt - 1) * 8))
          : TX_RETRY_INITIAL_DELAY_SECONDS + ((retryAttempt - 1) * TX_RETRY_DELAY_STEP_SECONDS);
        const errorMessage = String(error && error.message ? error.message : error);

        if (retryAttempt >= MAX_SEND_FLOW_RETRY_ATTEMPTS) {
          if (transientSendError && hardReloginAttempt < MAX_HARD_RELOGIN_ATTEMPTS) {
            hardReloginAttempt += 1;
            console.warn(
              `[warn] TX ${progress} transient send errors persist. ` +
              `Performing hard relogin recovery ${hardReloginAttempt}/${MAX_HARD_RELOGIN_ATTEMPTS}...`
            );
            dashboard.setState({
              phase: "session-reuse",
              transfer: `hard-relogin (${progress})`,
              send: `Hard relogin ${sendRequest.amount} CC -> ${sendRequest.label}`,
              cooldown: "0s",
              swapsTotal: progressForDashboard,
              swapsOk: String(completedTx),
              swapsFail: String(skippedTx)
            });

            try {
              await recoverSendFlowByRefresh(
                client,
                config,
                onCheckpointRefresh,
                accountLogTag,
                hardReloginAttempt,
                MAX_HARD_RELOGIN_ATTEMPTS,
                {
                  mode: "full-browser",
                  reason: "send-hard-relogin",
                  runPreflight: true,
                  forceConnectionReset: true
                }
              );

              await apiCallWithRetry(
                () => client.syncAccount(config.paths.bridge),
                "Sync account after hard relogin",
                2,
                20000,
                { maxConsecutiveTimeouts: 2 }
              );

              retryAttempt = 0;
              console.log(`[info] Hard relogin recovery completed. Retrying tx ${progress}...`);
              continue;
            } catch (reloginError) {
              const reloginMessage = String(
                reloginError && reloginError.message ? reloginError.message : reloginError
              );
              console.warn(
                `[warn] Hard relogin recovery failed for tx ${progress}: ${reloginMessage}`
              );
            }
          }

          const retryAfterSeconds = transientSendError ? 60 : retryDelaySeconds;
          console.warn(
            `[warn] TX ${progress} reached retry limit (${MAX_SEND_FLOW_RETRY_ATTEMPTS}). ` +
            `Deferring ${retryAfterSeconds}s. Last error: ${errorMessage}`
          );
          dashboard.setState({
            phase: "cooldown",
            transfer: `deferred (retry-limit) (${progress})`,
            send: `Deferred ${sendRequest.amount} CC -> ${sendRequest.label} for ${retryAfterSeconds}s`,
            cooldown: `${retryAfterSeconds}s`,
            swapsTotal: progressForDashboard,
            swapsOk: String(completedTx),
            swapsFail: String(skippedTx)
          });
          deferredState = {
            reason: transientSendError ? "send-flow-transient" : "send-flow-retry-limit",
            retryAfterSeconds,
            requiredAmount: Number(sendRequest.amount),
            availableAmount: null,
            progress,
            sendLabel: `${sendRequest.amount} CC -> ${sendRequest.label}`
          };
          break;
        }

        console.warn(
          `[warn] TX ${progress} failed (attempt ${retryAttempt}) and will retry in ${retryDelaySeconds}s: ${errorMessage}`
        );

        dashboard.setState({
          phase: "cooldown",
          transfer: `retry-${retryAttempt} (${progress})`,
          send: `Retrying ${sendRequest.amount} CC -> ${sendRequest.label} in ${retryDelaySeconds}s`,
          cooldown: `${retryDelaySeconds}s`,
          swapsTotal: progressForDashboard,
          swapsOk: String(completedTx),
          swapsFail: String(skippedTx)
        });

        await sleep(retryDelaySeconds * 1000);
      }
    }

    if (skipToNextCandidate) {
      // Generate fresh amount for next candidate to avoid identical-amount pattern detection
      if (recipientCandidateMode && index < sendRequests.length - 1) {
        const senderTierKey = getAccountTierKey(senderAccountName);
        const freshAmount = generateRandomCcAmount(config.send, senderTierKey);
        for (let ci = index + 1; ci < sendRequests.length; ci += 1) {
          sendRequests[ci].amount = freshAmount;
        }
      }
      continue;
    }

    if (deferredState) {
      break;
    }

    if (!sendResult) {
      skippedTx += 1;
      continue;
    }

    completedTx++;
    if (sendRequest.label) {
      sentRecipientLabels.push(String(sendRequest.label));
    }

    // Record per-account TX timestamp for 60s cooldown enforcement
    if (senderAccountName) {
      lastTxTimestampByAccount.set(senderAccountName, Date.now());
    }

    // Record send pair for internal transfers to avoid reciprocal cooldowns
    if (
      String(sendRequest.source || "").startsWith("internal-") &&
      senderAccountName &&
      sendRequest.label
    ) {
      recordSendPair(senderAccountName, sendRequest.label);
    }

    // Adjust cached balance after successful send (passive, no API call)
    adjustAccountCcBalanceAfterSend(senderAccountName, sendRequest.label, Number(sendRequest.amount));

    dashboard.setState({
      phase: "send",
      send: `${sendRequest.amount} CC -> ${sendRequest.label} (${progress})`,
      transfer: `${sendResult.status} | id=${sendResult.transferId || "n/a"} (${progress})`,
      swapsTotal: `${completedTx}/${expectedTxCount}`,
      swapsOk: String(completedTx),
      swapsFail: String(skippedTx)
    });

    if (recipientCandidateMode && completedTx >= expectedTxCount) {
      console.log(
        `[info] Internal recipient selected via candidate ${index + 1}/${sendRequests.length}: ${sendRequest.label}`
      );
      break;
    }

    // Delay between transactions (skip after last tx) - human-like distribution
    if (index < sendRequests.length - 1 && delayTxMaxSec > 0) {
      const delayTxSec = humanLikeDelay(delayTxMinSec, delayTxMaxSec);
      console.log(`[info] Waiting ${delayTxSec}s before next tx...`);
      dashboard.setState({
        phase: "cooldown",
        cooldown: `${delayTxSec}s`,
        send: `Cooldown ${delayTxSec}s before next tx`
      });
      await sleep(delayTxSec * 1000);
    }
  }

  if (deferredState) {
    console.log(
      `[info] Batch deferred: reason=${deferredState.reason} retryAfter=${deferredState.retryAfterSeconds}s progress=${deferredState.progress}`
    );
    return {
      completedTx,
      skippedTx,
      deferred: true,
      deferReason: deferredState.reason,
      deferRetryAfterSeconds: deferredState.retryAfterSeconds,
      deferRequiredAmount: deferredState.requiredAmount,
      deferAvailableAmount: deferredState.availableAmount,
      deferProgress: deferredState.progress,
      deferSendLabel: deferredState.sendLabel,
      sentRecipientLabels
    };
  }

  // Final balance check (with timeout)
  stepLog(`[step] Refresh balances after send batch (timeout=${BALANCE_CHECK_TIMEOUT_MS}ms)`);
  const postSendBalance = await getBalanceWithTimeout(client);
  if (postSendBalance !== null) {
    dashboard.setState({
      balance: `CC=${postSendBalance.cc} | USDC=${postSendBalance.usdcBase} | CBTC=${postSendBalance.cbtc}`,
      swapsTotal: `${Math.min(expectedTxCount, completedTx + skippedTx)}/${expectedTxCount}`,
      swapsOk: String(completedTx),
      swapsFail: String(skippedTx),
      cooldown: "-"
    });
    console.log(`[info] Final balance: CC=${postSendBalance.cc} | Available=${postSendBalance.available}`);
    updateAccountCcBalance(senderAccountName, postSendBalance.ccNumeric);
    updateAccountUsdcBalance(senderAccountName, Number(postSendBalance.usdcBase) || 0);
  } else {
    console.log(`[warn] Final balance check timeout/failed`);
    dashboard.setState({
      swapsTotal: `${Math.min(expectedTxCount, completedTx + skippedTx)}/${expectedTxCount}`,
      swapsOk: String(completedTx),
      swapsFail: String(skippedTx),
      cooldown: "-"
    });
  }

  console.log(
    `[info] Batch summary: completed=${completedTx}, skipped=${skippedTx}, total=${expectedTxCount}`
  );
  return {
    completedTx,
    skippedTx,
    deferred: false,
    deferReason: null,
    deferRetryAfterSeconds: 0,
    deferRequiredAmount: null,
    deferAvailableAmount: null,
    deferProgress: null,
    deferSendLabel: null,
    sentRecipientLabels
  };
}

async function refreshVercelSecurityCookies(client, config, reasonLabel, onCheckpointRefresh) {
  // Skip browser challenge entirely if website no longer uses Vercel Security Checkpoint
  if (true /* skipVercelChallenge: website migrated to Cloudflare */) {
    console.log(`[info] ${reasonLabel} — SKIPPED (skipVercelChallenge=true, website uses Cloudflare now)`);
    return {
      refreshed: true,
      unavailable: false,
      retryAfterSeconds: 0,
      reason: "skipped-no-vercel-challenge"
    };
  }

  console.log(`[info] ${reasonLabel}`);
  const hadSecurityCookie = client.hasSecurityCookie();
  const hadSessionCookie = client.hasAccountSessionCookie();
  const retryAfterSeconds = Math.max(
    60,
    clampToNonNegativeInt(config.session.browserChallengeRetryAfterSeconds, 120)
  );
  const cooldownRemainingSeconds = getBrowserChallengeCooldownRemainingSeconds();

  if (cooldownRemainingSeconds > 0 && (hadSecurityCookie || hadSessionCookie)) {
    console.log(
      `[warn] Browser challenge cooldown active (${cooldownRemainingSeconds}s). ` +
      "Skipping Puppeteer refresh and deferring."
    );
    return {
      refreshed: false,
      unavailable: true,
      retryAfterSeconds: Math.max(retryAfterSeconds, cooldownRemainingSeconds),
      reason: "browser-rate-limit-cooldown"
    };
  }

  cacheSecurityCookiesFromMap(client.cookieJar, "client-before-refresh");

  const browserCookies = await solveBrowserChallenge(
    config.baseUrl,
    config.paths.onboard,
    config.headers.userAgent,
    true
  );

  if (!browserCookies || browserCookies.size === 0) {
    markBrowserChallengeRateLimited(retryAfterSeconds);
    const cachedSecurityMap = buildCachedSecurityCookieMap();

    if (cachedSecurityMap.size > 0) {
      console.log(
        `[warn] Browser challenge returned no cookies. ` +
        `Applying ${cachedSecurityMap.size} cached security cookie(s) fallback.`
      );

      client.mergeCookies(cachedSecurityMap);
      try {
        await client.preflightOnboard();
        client.logCookieStatus("after cached security cookie fallback");
        return {
          refreshed: false,
          unavailable: false,
          retryAfterSeconds: 0,
          reason: "cached-security-cookie-fallback"
        };
      } catch (cacheError) {
        console.log(`[warn] Cached security cookie fallback failed: ${cacheError.message}`);
      }
    }

    if (hadSecurityCookie || hadSessionCookie) {
      console.log(
        "[warn] Browser challenge returned no cookies (likely rate-limited/429). " +
        "Keeping existing cookies and deferring refresh."
      );
      return {
        refreshed: false,
        unavailable: true,
        retryAfterSeconds,
        reason: "browser-no-cookies"
      };
    }

    const error = new Error("Browser challenge did not return any cookies.");
    error.code = "BROWSER_CHALLENGE_NO_COOKIES";
    error.retryAfterSeconds = retryAfterSeconds;
    throw error;
  }

  cacheSecurityCookiesFromMap(browserCookies, "refresh-browser-challenge");
  client.mergeCookies(browserCookies);
  if (typeof onCheckpointRefresh === "function") {
    onCheckpointRefresh();
  }
  browserChallengeRateLimitedUntilMs = 0;

  // Validate refreshed cookie against the same fetch path used by API client.
  // FULL PROXY MODE: Both browser challenge and preflight use proxy,
  // so _vcrcs cookie IP matches.
  try {
    await client.preflightOnboard();
    client.logCookieStatus("after refresh preflight");
  } catch (error) {
    console.log(`[warn] Refresh preflight still blocked: ${error.message}`);

    if (isCheckpointOr429Error(error)) {
      markBrowserChallengeRateLimited(retryAfterSeconds);
      return {
        refreshed: false,
        unavailable: true,
        retryAfterSeconds,
        reason: "refresh-preflight-blocked"
      };
    }
  }

  return {
    refreshed: true,
    unavailable: false,
    retryAfterSeconds: 0,
    reason: "ok"
  };
}

async function attemptSessionReuse(client, config, onCheckpointRefresh, accountLogTag = null) {
  const logSession = (message) => console.log(withAccountTag(accountLogTag, message));

  const maxCheckpointRefreshAttempts = Math.max(
    1,
    clampToNonNegativeInt(config.session.maxSessionReuseRefreshAttempts, 3)
  );
  const maxTransientAttempts = Math.max(
    1,
    clampToNonNegativeInt(config.session.maxSessionReuseTransientAttempts, 6)
  );
  const maxTransientLightResets = Math.max(
    0,
    clampToNonNegativeInt(config.session.maxSessionReuseLightResets, 1)
  );
  const maxTransientBrowserRefreshes = Math.max(
    0,
    clampToNonNegativeInt(config.session.maxSessionReuseTransientBrowserRefreshes, 1)
  );
  const transientBrowserRefreshTriggerFailures = Math.max(
    1,
    clampToNonNegativeInt(config.session.transientBrowserRefreshTriggerFailures, 2)
  );
  const transientRetryAfterSeconds = Math.max(
    15,
    clampToNonNegativeInt(config.session.sessionReuseTransientRetryAfterSeconds, 45)
  );
  const retryJitterSeconds = Math.max(
    0,
    clampToNonNegativeInt(config.session.sessionReuseRetryJitterSeconds, 12)
  );
  const settleDelayMs = Math.max(
    0,
    clampToNonNegativeInt(config.session.checkpointSettleDelayMs, 3500)
  );
  const browserChallengeRetryAfterSeconds = Math.max(
    60,
    clampToNonNegativeInt(config.session.browserChallengeRetryAfterSeconds, 120)
  );
  const buildTransientDeferral = (message) => {
    const transientLimitError = new Error(message);
    transientLimitError.code = "SESSION_REUSE_TRANSIENT_RETRY_LIMIT";
    transientLimitError.retryAfterSeconds = browserChallengeRetryAfterSeconds;
    return {
      ok: false,
      error: transientLimitError,
      retryAfterSeconds: browserChallengeRetryAfterSeconds
    };
  };

  applySessionReuseConcurrencyLimit(config.session.maxConcurrentSessionReuse);

  let lastError = null;
  let attempt = 0;
  let checkpointRefreshAttempt = 0;
  let transientFailureCount = 0;
  let transientLightResetCount = 0;
  let transientBrowserRefreshCount = 0;

  while (true) {
    attempt += 1;
    try {
      // Step 1: Sync account (this validates session)
      await acquireSessionReuseSlot(accountLogTag);
      const syncStart = Date.now();
      try {
        logSession(`[info] Session reuse attempt ${attempt}: calling sync-account...`);
        await client.syncAccount(config.paths.bridge);
        logSession(`[info] Session reuse attempt ${attempt}: sync-account OK (${Date.now() - syncStart}ms)`);
      } finally {
        releaseSessionReuseSlot(accountLogTag);
      }

      // Step 2: Balance check (optional, timeout OK - session is still valid)
      logSession(`[info] Session reuse attempt ${attempt}: calling balances (timeout=15s)...`);
      const balanceStart = Date.now();

      let balancesData = {};
      try {
        const balancePromise = client.getBalances();
        const timeoutPromise = new Promise((_, reject) => {
          setTimeout(() => reject(new Error("Balance check timeout (15s)")), 15000);
        });

        const balancesResponse = await Promise.race([balancePromise, timeoutPromise]);
        balancesData = balancesResponse && balancesResponse.data ? balancesResponse.data : {};
        logSession(`[info] Session reuse attempt ${attempt}: balances OK (${Date.now() - balanceStart}ms)`);
      } catch (balanceError) {
        // Balance timeout is OK - session is still valid (sync-account passed)
        logSession(`[warn] Balance check failed: ${balanceError.message}`);
        logSession(`[info] Session is still valid (sync-account passed), continuing without balance data...`);
      }

      return {
        ok: true,
        balancesData
      };
    } catch (error) {
      logSession(`[info] Session reuse attempt ${attempt} failed: ${error.message}`);
      lastError = error;

      if (isSessionReuseTimeoutError(error)) {
        const fetchFailedTransient = isFetchFailedTransientError(error);

        // For fetch failures (likely Vercel 429 rate limit at TCP level),
        // do NOT immediately bail — wait with extended backoff and retry.
        // The 429 window typically clears within 30-60s.
        if (fetchFailedTransient) {
          logSession(
            `[warn] Session reuse fetch/network failure detected (possible 429 rate limit). ` +
            `Will retry with extended backoff instead of immediate restart.`
          );
        }

        transientFailureCount += 1;
        let browserRefreshAttemptedThisAttempt = false;

        if (transientLightResetCount < maxTransientLightResets) {
          transientLightResetCount += 1;
          logSession(
            `[info] Session reuse transient recovery (light reset ${transientLightResetCount}/${maxTransientLightResets})`
          );
          await resetConnectionPool({ forceReset: true });
        }

        // For fetch failures (likely 429 rate limit), immediately trigger browser
        // refresh to get fresh Vercel security cookies. The old approach of waiting
        // 3+ failures wasted time — browser refresh gets a new IP/session context
        // which is more effective than just backoff.
        const shouldForceImmediateBrowserRefresh =
          fetchFailedTransient &&
          config.session.autoRefreshCheckpoint &&
          transientBrowserRefreshCount < maxTransientBrowserRefreshes;
        // Browser refresh for ALL transient errors (fetch failures included).
        // Fetch failures = likely 429 → fresh browser cookies help bypass rate limit.
        // Non-fetch transient = timeout/checkpoint → browser refresh also helps.
        const shouldRunTransientBrowserRefresh =
          config.session.autoRefreshCheckpoint &&
          transientBrowserRefreshCount < maxTransientBrowserRefreshes &&
          (transientFailureCount >= transientBrowserRefreshTriggerFailures ||
            shouldForceImmediateBrowserRefresh);

        if (shouldRunTransientBrowserRefresh) {
          transientBrowserRefreshCount += 1;
          browserRefreshAttemptedThisAttempt = true;
          if (
            shouldForceImmediateBrowserRefresh &&
            transientFailureCount < transientBrowserRefreshTriggerFailures
          ) {
            logSession(
              `[info] Session reuse fetch/network failure detected. ` +
              `Escalating to browser refresh immediately (${transientBrowserRefreshCount}/${maxTransientBrowserRefreshes}).`
            );
          }

          let refreshResult = null;
          try {
            refreshResult = await refreshVercelSecurityCookies(
              client,
              config,
              `Session reuse transient failures persist (browser refresh ${transientBrowserRefreshCount}/${maxTransientBrowserRefreshes})`,
              onCheckpointRefresh
            );
          } catch (refreshError) {
            if (refreshError && refreshError.code === "BROWSER_CHALLENGE_NO_COOKIES") {
              logSession(
                `[warn] Browser challenge unavailable during transient recovery. ` +
                `Deferring session reuse ${browserChallengeRetryAfterSeconds}s.`
              );
              return buildTransientDeferral(
                "Session reuse deferred: browser challenge unavailable (no cookies)."
              );
            }
            throw refreshError;
          }

          if (refreshResult && refreshResult.unavailable) {
            logSession(
              `[warn] Browser challenge temporarily unavailable. ` +
              `Deferring session reuse ${browserChallengeRetryAfterSeconds}s.`
            );
            return buildTransientDeferral(
              "Session reuse deferred: browser challenge temporarily unavailable."
            );
          }

          client.logCookieStatus(`after session transient browser refresh ${transientBrowserRefreshCount}`);
          if (settleDelayMs > 0) {
            logSession(`[info] Waiting ${settleDelayMs}ms for token settle before session reuse retry...`);
            await sleep(settleDelayMs);
          }
        }

        const browserRefreshRecoveryExhausted =
          !config.session.autoRefreshCheckpoint ||
          transientBrowserRefreshCount >= maxTransientBrowserRefreshes;
        const lightResetRecoveryExhausted =
          transientLightResetCount >= maxTransientLightResets;
        // For fetch failures (likely 429), don't bail early just because light reset
        // and browser refresh are exhausted. The maxTransientAttempts check below is
        // the proper guard — fetch failures just need time to clear the rate limit.
        if (
          fetchFailedTransient &&
          !browserRefreshAttemptedThisAttempt &&
          lightResetRecoveryExhausted &&
          browserRefreshRecoveryExhausted
        ) {
          logSession(
            `[info] Fetch/network failure after recovery actions exhausted. ` +
            `Continuing retry with backoff (${transientFailureCount}/${maxTransientAttempts})...`
          );
        }

        if (transientFailureCount >= maxTransientAttempts) {
          const transientLimitError = new Error(
            `Session reuse transient retry limit reached (${maxTransientAttempts}) after repeated network failures.`
          );
          transientLimitError.code = "SESSION_REUSE_TRANSIENT_RETRY_LIMIT";
          transientLimitError.retryAfterSeconds = transientRetryAfterSeconds;
          return {
            ok: false,
            error: transientLimitError,
            retryAfterSeconds: transientRetryAfterSeconds
          };
        }

        // For fetch failures (likely 429 rate limit), use significantly longer backoff.
        // Normal timeouts: base ~20s. Fetch failures: base ~45s to let rate limit window clear.
        const fetchFailedExtra = fetchFailedTransient ? 25 : 0;
        const retryBaseSeconds = Math.min(20, transientRetryAfterSeconds) + fetchFailedExtra;
        const retryStepSeconds = Math.min(12, (transientFailureCount - 1) * 3);
        const retryJitterAddSeconds = retryJitterSeconds > 0
          ? randomIntInclusive(0, retryJitterSeconds)
          : 0;
        const retryDelaySeconds = Math.max(
          fetchFailedTransient ? 30 : 5,
          Math.min(
            transientRetryAfterSeconds + retryJitterSeconds + fetchFailedExtra,
            retryBaseSeconds + retryStepSeconds + retryJitterAddSeconds
          )
        );
        logSession(
          `[info] Session reuse ${fetchFailedTransient ? "fetch failure (likely 429)" : "timeout"} detected. ` +
          `Retrying in ${retryDelaySeconds}s... (transient ${transientFailureCount}/${maxTransientAttempts})`
        );
        await sleep(retryDelaySeconds * 1000);
        continue;
      }

      if (
        isVercelCheckpointError(error) &&
        config.session.autoRefreshCheckpoint &&
        checkpointRefreshAttempt < maxCheckpointRefreshAttempts
      ) {
        checkpointRefreshAttempt += 1;
        let refreshResult = null;
        try {
          refreshResult = await refreshVercelSecurityCookies(
            client,
            config,
            `Session reuse blocked by Vercel checkpoint (refresh ${checkpointRefreshAttempt}/${maxCheckpointRefreshAttempts}), refreshing browser security cookies...`,
            onCheckpointRefresh
          );
        } catch (refreshError) {
          if (refreshError && refreshError.code === "BROWSER_CHALLENGE_NO_COOKIES") {
            logSession(
              `[warn] Browser challenge unavailable during checkpoint recovery. ` +
              `Deferring session reuse ${browserChallengeRetryAfterSeconds}s.`
            );
            return buildTransientDeferral(
              "Session reuse deferred: browser challenge unavailable (checkpoint recovery)."
            );
          }
          throw refreshError;
        }

        if (refreshResult && refreshResult.unavailable) {
          logSession(
            `[warn] Browser challenge temporarily unavailable during checkpoint recovery. ` +
            `Deferring session reuse ${browserChallengeRetryAfterSeconds}s.`
          );
          return buildTransientDeferral(
            "Session reuse deferred: browser challenge temporarily unavailable (checkpoint recovery)."
          );
        }

        client.logCookieStatus(`after session refresh attempt ${checkpointRefreshAttempt}`);
        if (settleDelayMs > 0) {
          logSession(`[info] Waiting ${settleDelayMs}ms for Vercel token settle before retry...`);
          await sleep(settleDelayMs);
        }
        continue;
      }

      return {
        ok: false,
        error
      };
    }
  }
}

async function sendOtpWithCheckpointRecovery(client, selectedEmail, config, onCheckpointRefresh) {
  const maxAttempts = Math.max(
    1,
    clampToNonNegativeInt(config.session.maxOtpRefreshAttempts, 3)
  );
  const otpCheckpointRetryAfterSeconds = Math.max(
    60,
    clampToNonNegativeInt(config.session.browserChallengeRetryAfterSeconds, 120)
  );
  const settleDelayMs = Math.max(
    0,
    clampToNonNegativeInt(config.session.checkpointSettleDelayMs, 3500)
  );

  let lastError = null;
  for (let attempt = 1; attempt <= maxAttempts; attempt += 1) {
    try {
      return await client.sendOtp(selectedEmail);
    } catch (error) {
      lastError = error;

      if (error && error.code === "SEND_OTP_CHECKPOINT_DEFER") {
        throw error;
      }

      if (
        !isVercelCheckpointError(error) ||
        !config.session.autoRefreshCheckpoint
      ) {
        throw error;
      }

      if (attempt >= maxAttempts) {
        const deferError = new Error(
          `Send OTP checkpoint persisted after ${maxAttempts} attempts.`
        );
        deferError.code = "SEND_OTP_CHECKPOINT_DEFER";
        deferError.retryAfterSeconds = otpCheckpointRetryAfterSeconds;
        throw deferError;
      }

      let refreshResult = null;
      try {
        refreshResult = await refreshVercelSecurityCookies(
          client,
          config,
          `Send OTP blocked by Vercel checkpoint (attempt ${attempt}/${maxAttempts}), refreshing browser security cookies...`,
          onCheckpointRefresh
        );
      } catch (refreshError) {
        if (refreshError && refreshError.code === "BROWSER_CHALLENGE_NO_COOKIES") {
          const deferError = new Error(
            "Send OTP deferred: browser challenge returned no cookies."
          );
          deferError.code = "SEND_OTP_CHECKPOINT_DEFER";
          deferError.retryAfterSeconds = otpCheckpointRetryAfterSeconds;
          throw deferError;
        }
        throw refreshError;
      }

      if (refreshResult && refreshResult.unavailable) {
        const refreshRetryAfter = Math.max(
          otpCheckpointRetryAfterSeconds,
          clampToNonNegativeInt(refreshResult.retryAfterSeconds, otpCheckpointRetryAfterSeconds)
        );
        const deferError = new Error(
          "Send OTP deferred: browser challenge temporarily unavailable."
        );
        deferError.code = "SEND_OTP_CHECKPOINT_DEFER";
        deferError.retryAfterSeconds = refreshRetryAfter;
        throw deferError;
      }

      client.logCookieStatus(`after refresh before send-otp retry ${attempt}`);
      if (settleDelayMs > 0) {
        console.log(`[info] Waiting ${settleDelayMs}ms for Vercel token settle before send-otp retry...`);
        await sleep(settleDelayMs);
      }
    }
  }

  throw lastError || new Error("Send OTP failed after refresh retries");
}

async function processAccount(context) {
  const {
    account,
    accountToken,
    config,
    tokens,
    tokensPath,
    sendMode,
    recipientsInfo,
    args,
    accountIndex,
    totalAccounts,
    selectedAccounts,
    accountSnapshots,
    loopRound,
    totalLoopRounds,
    maxLoopTxOverride,
    smartFillBlockRecipients,
    resumeFromDeferReason,
    preferRecipientNames
  } = context;
  const safePreferRecipientNames = Array.isArray(preferRecipientNames)
    ? preferRecipientNames.map((n) => String(n || "").trim()).filter(Boolean)
    : [];
  const safeSmartFillBlockRecipients = Array.isArray(smartFillBlockRecipients)
    ? smartFillBlockRecipients
      .map((item) => String(item || "").trim())
      .filter((item) => Boolean(item))
    : [];
  const safeResumeFromDeferReason = String(resumeFromDeferReason || "").trim();

  const selectedEmail = String(process.env.ROOTSFI_EMAIL || account.email).trim();
  if (!selectedEmail || !selectedEmail.includes("@")) {
    throw new Error(`Account ${account.name}: email is invalid`);
  }
  const accountLogTag = `A${accountIndex + 1}/${totalAccounts}`;

  const selectedAccountList =
    Array.isArray(selectedAccounts) && selectedAccounts.length > 0
      ? selectedAccounts
      : [{ name: account.name, email: selectedEmail }];
  const accountRows = selectedAccountList
    .map((entry, idx) => {
      const entryName = String(entry && entry.name ? entry.name : `Account ${idx + 1}`);

      let marker = "queue";
      if (idx < accountIndex) {
        marker = "done";
      } else if (idx === accountIndex) {
        marker = "run";
      }

      return `*${entryName}(${marker})`;
    })
    .join(" | ");
  const accountConfig = cloneRuntimeConfig(config);

  if (safeResumeFromDeferReason) {
    const resumeNeedsCheckpointRefresh =
      safeResumeFromDeferReason === "session-reuse-transient" ||
      safeResumeFromDeferReason === "otp-checkpoint";

    accountConfig.session.maxSessionReuseTransientAttempts = resumeNeedsCheckpointRefresh ? 3 : 2;
    accountConfig.session.maxSessionReuseLightResets = 1;
    accountConfig.session.maxSessionReuseTransientBrowserRefreshes = resumeNeedsCheckpointRefresh
      ? Math.max(
        1,
        clampToNonNegativeInt(accountConfig.session.maxSessionReuseTransientBrowserRefreshes, 1)
      )
      : 0;
    accountConfig.session.transientBrowserRefreshTriggerFailures = resumeNeedsCheckpointRefresh ? 1 : 2;
    accountConfig.session.sessionReuseTransientRetryAfterSeconds = 20;
    console.log(
      `[session] Fast retry mode for deferred account (${safeResumeFromDeferReason}): ` +
      `transient=${accountConfig.session.maxSessionReuseTransientAttempts} ` +
      `lightResets=${accountConfig.session.maxSessionReuseLightResets} ` +
      `browserRefresh=${accountConfig.session.maxSessionReuseTransientBrowserRefreshes}`
    );
  }
  const configuredMaxLoopTx = clampToNonNegativeInt(
    accountConfig.send.maxLoopTx || accountConfig.send.maxTx,
    1
  );
  const effectiveMaxLoopTx = Number.isFinite(Number(maxLoopTxOverride))
    ? Math.max(1, clampToNonNegativeInt(maxLoopTxOverride, 1))
    : configuredMaxLoopTx;
  accountConfig.send.maxLoopTx = effectiveMaxLoopTx;

  const cycleLoopRounds = Math.max(
    1,
    clampToNonNegativeInt(totalLoopRounds, configuredMaxLoopTx)
  );
  const accountTargetPerDay =
    cycleLoopRounds *
    Math.max(1, selectedAccountList.length);
  const defaultMinCooldownSeconds = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(accountConfig.send, "minDelayTxSeconds")
      ? accountConfig.send.minDelayTxSeconds
      : accountConfig.send.delayTxSeconds,
    INTERNAL_API_DEFAULTS.send.minDelayTxSeconds
  );
  const defaultMaxCooldownSeconds = clampToNonNegativeInt(
    Object.prototype.hasOwnProperty.call(accountConfig.send, "maxDelayTxSeconds")
      ? accountConfig.send.maxDelayTxSeconds
      : accountConfig.send.delayTxSeconds,
    INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds
  );
  const cooldownLabel = defaultMaxCooldownSeconds > defaultMinCooldownSeconds
    ? `${defaultMinCooldownSeconds}-${defaultMaxCooldownSeconds}s`
    : `${defaultMinCooldownSeconds}s`;

  // Apply token profile to config for this account
  applyTokenProfileToConfig(accountConfig, accountToken);

  let checkpointRefreshCount = 0;
  let lastVercelRefreshAt = String(accountToken.security.lastVercelRefreshAt || "").trim();
  const markCheckpointRefresh = () => {
    checkpointRefreshCount += 1;
    lastVercelRefreshAt = new Date().toISOString();
  };

  const dashboard = new PinnedDashboard({
    enabled:
      accountConfig.ui.dashboard &&
      !args.noDashboard &&
      process.env.ROOTSFI_NO_DASHBOARD !== "1",
    logLines: accountConfig.ui.logLines,
    accountSnapshots
  });

  const initialDashboardState = {
    phase: "init",
    selectedAccount: `[${accountIndex + 1}/${totalAccounts}] ${account.name} (${maskEmail(selectedEmail)})`,
    accounts: accountRows,
    targetPerDay: String(accountTargetPerDay),
    cooldown: cooldownLabel,
    swapsTotal: "0/0",
    swapsOk: "0",
    swapsFail: "0",
    minDelay: clampToNonNegativeInt(accountConfig.send.minDelayTxSeconds, 60),
    maxDelay: clampToNonNegativeInt(accountConfig.send.maxDelayTxSeconds, 100)
  };
  dashboard.setState(initialDashboardState);
  dashboard.attach();
  setActiveDashboard(dashboard);

  const updateCookieDashboard = (client, phase) => {
    const status = client.getCookieStatus();
    const patch = {
      cookie: `_vcrcs=${status.security} session=${status.session} total=${status.total}`
    };

    if (phase) {
      patch.phase = phase;
    }

    dashboard.setState(patch);
  };

  try {
    const currentRound = Math.max(1, clampToNonNegativeInt(loopRound, 1));
    const roundLabel = totalLoopRounds > 1 ? ` | Round ${currentRound}/${totalLoopRounds}` : "";
    console.log(`\n${"=".repeat(60)}`);
    console.log(`[account ${accountIndex + 1}/${totalAccounts}] Processing: ${account.name} (${maskEmail(selectedEmail)})${roundLabel}`);
    console.log(`${"=".repeat(60)}`);

    console.log(
      `[init] Token profile ready: deviceId=${maskSecret(accountToken.deviceId, 6, 6)} antiBot=${maskSecret(accountToken.security.antiBotNonce, 6, 6)}`
    );

    const sendPolicy = accountConfig.send;

    // Build send requests based on mode.
    // IMPORTANT: this must be called AFTER refreshThisWeekRewardDashboard()
    // so the sender's tier is known before amount is generated.
    let sendRequests = [];
    let buildDeferResult = null;
    const buildSendRequestsNow = () => {
      const senderTierKey = getAccountTierKey(account.name);

      // Guard: defer ONLY if /api/rewards belum pernah berhasil di-fetch untuk akun ini.
      // Kalau sudah fetched tapi tetap unranked (akun baru / belum ada qualifying send),
      // tetap lanjut TX pakai amount range "unranked" dari config.
      if (!tierFetchedByAccount.has(account.name)) {
        console.log(withAccountTag(accountLogTag, `[warn] Tier belum di-fetch, defer send sampai /api/rewards sukses`));
        buildDeferResult = {
          success: true,
          account: account.name,
          mode: "tier-unknown-deferred",
          deferred: true,
          deferReason: "tier-unknown",
          deferRetryAfterSeconds: 30,
          deferRequiredAmount: null,
          deferAvailableAmount: null,
          txCompleted: 0,
          txSkipped: 0
        };
        return;
      }

      const senderTierRange = resolveAmountRangeForTier(sendPolicy, senderTierKey);
      const sendPolicyForSender = { ...sendPolicy, senderTier: senderTierKey };
      sendRequests = [];
      buildDeferResult = null;
      if (sendMode === "external") {
        if (recipientsInfo.missing || recipientsInfo.recipients.length === 0) {
          throw new Error("External mode requires recipient.txt with valid recipients");
        }

        sendRequests = buildSendRequestsWithRandomRecipients(recipientsInfo.recipients, sendPolicyForSender);

        const amountLabel = `${senderTierRange.min}-${senderTierRange.max}`;
        const recipientsList = sendRequests.map(r => r.label).join(", ");
        dashboard.setState({
          send: `${amountLabel} CC x${sendRequests.length} [${senderTierKey}] -> random recipients`,
          mode: "external"
        });
        console.log(`[init] Send plan: ${amountLabel} CC x${sendRequests.length} [${senderTierKey}] -> [${recipientsList}]`);
      } else if (sendMode === "internal") {
        const internalPlan = buildInternalSendRequests(
          selectedAccounts,
          account.name,
          sendPolicy,
          currentRound,
          safeSmartFillBlockRecipients,
          safePreferRecipientNames
        );

        if (safeSmartFillBlockRecipients.length > 0) {
          console.log(
            `[internal] Smart-fill guard for ${account.name}: avoid send-back to [${safeSmartFillBlockRecipients.join(", ")}]`
          );
        }

        if (!internalPlan || internalPlan.requests.length === 0) {
          const retryAfterSeconds = Math.max(
            TX_RETRY_INITIAL_DELAY_SECONDS,
            clampToNonNegativeInt(
              internalPlan && internalPlan.retryAfterSeconds,
              TX_RETRY_INITIAL_DELAY_SECONDS
            )
          );
          const deferReason =
            internalPlan && internalPlan.reason
              ? internalPlan.reason
              : "internal-recipient-unavailable";

          console.log(
            `[internal] ${account.name}: defer send (${deferReason}) for ${retryAfterSeconds}s`
          );
          dashboard.setState({
            phase: "cooldown",
            send: `Deferred internal send for ${retryAfterSeconds}s`,
            transfer: "deferred (internal-recipient)",
            cooldown: `${retryAfterSeconds}s`,
            mode: "internal-rotating"
          });

          buildDeferResult = {
            success: true,
            account: account.name,
            mode: "internal-rotating-deferred",
            deferred: true,
            deferReason,
            deferRetryAfterSeconds: retryAfterSeconds,
            deferRequiredAmount: null,
            deferAvailableAmount: null,
            txCompleted: 0,
            txSkipped: 0
          };
          return;
        }

        sendRequests = internalPlan.requests;
        const primaryRequest = sendRequests[0];
        const fallbackCount = Math.max(0, sendRequests.length - 1);
        const fallbackLabel = fallbackCount > 0 ? ` (+${fallbackCount} fallback)` : "";

        dashboard.setState({
          send: `${primaryRequest.amount} CC -> ${primaryRequest.label}${fallbackLabel}`,
          mode: "internal-rotating"
        });
        console.log(
          `[init] Send plan (internal-rotating): ${primaryRequest.amount} CC -> ${primaryRequest.label}` +
          `${fallbackLabel} | offset=${internalPlan.primaryOffset} | tier=${senderTierKey} (${senderTierRange.min}-${senderTierRange.max})`
        );
      } else {
        dashboard.setState({ mode: "balance-only" });
        console.log("[init] Balance check only mode");
      }
    };

    if (args.dryRun) {
      dashboard.setState({ phase: "dry-run" });
      console.log("[dry-run] Configuration parsed successfully. No API requests were sent.");
      return {
        success: true,
        account: account.name,
        mode: "dry-run",
        deferred: false,
        deferReason: null,
        deferRetryAfterSeconds: 0,
        deferRequiredAmount: null,
        deferAvailableAmount: null,
        txCompleted: 0,
        txSkipped: 0
      };
    }

    let client = new RootsFiApiClient(accountConfig);

    // Inject per-account proxy from proxy.txt
    const accountProxy = proxyByAccount.get(account.name);
    if (accountProxy) {
      accountConfig.proxyUrl = accountProxy;
      client = new RootsFiApiClient(accountConfig);
      console.log(withAccountTag(accountLogTag, `[proxy] Using proxy for ${account.name}`));
    }
    updateCookieDashboard(client, "startup");
    client.logCookieStatus("startup");

    if (accountConfig.session.preflightOnboard) {
      dashboard.setState({ phase: "preflight" });
      console.log(withAccountTag(accountLogTag, "[step] Preflight onboard page"));
      try {
        await client.preflightOnboard();
        console.log(withAccountTag(accountLogTag, "[step] Preflight onboard done"));
      } catch (error) {
        console.log(`[warn] Preflight failed: ${error.message}`);
      }
    }

    // skipVercelChallenge: website migrated to Cloudflare, proactive refresh permanently disabled
    if (false && shouldRefreshVercelCookie(lastVercelRefreshAt, accountConfig.session.proactiveVercelRefreshMinutes)) {
      dashboard.setState({ phase: "vercel-refresh" });
      console.log(
        withAccountTag(
          accountLogTag,
          `[step] Proactive Vercel cookie refresh (interval=${accountConfig.session.proactiveVercelRefreshMinutes}m)`
        )
      );
      try {
        await refreshVercelSecurityCookies(
          client,
          accountConfig,
          "Proactive refresh started",
          markCheckpointRefresh
        );
        client.logCookieStatus("after proactive refresh");
        updateCookieDashboard(client);
      } catch (error) {
        console.log(`[warn] Proactive refresh failed: ${error.message}`);
      }
    }

    if (!client.hasValidSession()) {
      if (true /* skipVercelChallenge: Cloudflare */) {
        // Website no longer uses Vercel checkpoint — skip browser challenge.
        // Session will be established via OTP or session reuse without _vcrcs.
        console.log("[info] No valid session cookies found — Vercel challenge skipped (website uses Cloudflare)");
        console.log("[info] Will proceed to session reuse or OTP flow directly.");
      } else {
        dashboard.setState({ phase: "browser-checkpoint" });
        console.log("[info] No valid session cookies found, launching browser...");
        await refreshVercelSecurityCookies(
          client,
          accountConfig,
          "Initial browser verification required",
          markCheckpointRefresh
        );
        console.log("[info] Browser cookies merged from challenge flow");
        client.logCookieStatus("after browser merge");
        updateCookieDashboard(client);
      }
    } else {
      console.log("[info] Using existing session cookies from tokens.json");
    }

    // Prefer existing authenticated session and only use OTP flow when session is not reusable.
    if (client.hasAccountSessionCookie()) {
      dashboard.setState({ phase: "session-reuse" });
      console.log(withAccountTag(accountLogTag, "[step] Attempt existing session (skip OTP)"));
      let sessionReuse = await attemptSessionReuse(
        client,
        accountConfig,
        markCheckpointRefresh,
        accountLogTag
      );
      updateCookieDashboard(client);

      if (sessionReuse && !sessionReuse.ok && sessionReuse.error && sessionReuse.error.code === "SESSION_REUSE_TRANSIENT_RETRY_LIMIT") {
        const hotRestartCooldownSeconds = 30 + randomIntInclusive(5, 15);
        console.log(
          withAccountTag(
            accountLogTag,
            `[info] Session transient limit reached. Cooling down ${hotRestartCooldownSeconds}s before hot-restart (rerun-like recovery)...`
          )
        );
        await sleep(hotRestartCooldownSeconds * 1000);

        await resetConnectionPool({ forceReset: true });

        const hotRestartConfig = cloneRuntimeConfig(accountConfig);
        const isDeferredResume = Boolean(safeResumeFromDeferReason);
        hotRestartConfig.session.maxSessionReuseTransientAttempts = isDeferredResume
          ? 2
          : Math.max(
            3,
            Math.min(
              6,
              clampToNonNegativeInt(accountConfig.session.maxSessionReuseTransientAttempts, 6)
            )
          );
        hotRestartConfig.session.maxSessionReuseLightResets = isDeferredResume
          ? 1
          : Math.max(
            1,
            Math.min(
              1,
              clampToNonNegativeInt(accountConfig.session.maxSessionReuseLightResets, 1)
            )
          );
        hotRestartConfig.session.maxSessionReuseTransientBrowserRefreshes = Math.max(
          0,
          Math.min(
            1,
            clampToNonNegativeInt(accountConfig.session.maxSessionReuseTransientBrowserRefreshes, 0)
          )
        );
        hotRestartConfig.session.sessionReuseTransientRetryAfterSeconds = isDeferredResume ? 20 : 45;

        const hotRestartClient = new RootsFiApiClient(hotRestartConfig);
        hotRestartClient.parseCookieString(client.getCookieHeader());
        hotRestartClient.logCookieStatus("before session hot-restart attempt");

        const hotRestartReuse = await attemptSessionReuse(
          hotRestartClient,
          hotRestartConfig,
          markCheckpointRefresh,
          accountLogTag
        );

        if (hotRestartReuse.ok) {
          console.log(withAccountTag(accountLogTag, "[info] Session hot-restart succeeded."));
          client = hotRestartClient;
          sessionReuse = hotRestartReuse;
          updateCookieDashboard(client, "session-hot-restart");
        } else {
          const hotRestartError = hotRestartReuse.error;
          console.log(
            withAccountTag(
              accountLogTag,
              `[warn] Session hot-restart did not recover: ${hotRestartError ? hotRestartError.message : "unknown"}`
            )
          );
          client = hotRestartClient;
          sessionReuse = hotRestartReuse;

          if (isSessionReuseImmediateFetchRestartError(hotRestartError)) {
            dashboard.setState({ phase: "session-reuse-cold-rerun" });
            const coldRestartCooldownSeconds = 20 + randomIntInclusive(5, 10);
            console.log(
              withAccountTag(
                accountLogTag,
                `[warn] Fetch/network failure persists after hot-restart. Cooling down ${coldRestartCooldownSeconds}s before cold rerun (no OTP fallback)...`
              )
            );
            await sleep(coldRestartCooldownSeconds * 1000);

            await resetConnectionPool({ forceReset: true });

            const coldRestartConfig = cloneRuntimeConfig(accountConfig);
            applyTokenProfileToConfig(coldRestartConfig, accountToken);
            coldRestartConfig.session.maxSessionReuseTransientAttempts = 2;
            coldRestartConfig.session.maxSessionReuseLightResets = 1;
            coldRestartConfig.session.maxSessionReuseTransientBrowserRefreshes = Math.max(
              1,
              clampToNonNegativeInt(accountConfig.session.maxSessionReuseTransientBrowserRefreshes, 1)
            );
            coldRestartConfig.session.transientBrowserRefreshTriggerFailures = 1;
            coldRestartConfig.session.sessionReuseTransientRetryAfterSeconds = 20;

            const coldRestartClient = new RootsFiApiClient(coldRestartConfig);
            const cachedSecurityMap = buildCachedSecurityCookieMap();
            if (cachedSecurityMap.size > 0) {
              coldRestartClient.mergeCookies(cachedSecurityMap);
            }

            if (coldRestartConfig.session.autoRefreshCheckpoint) {
              try {
                await refreshVercelSecurityCookies(
                  coldRestartClient,
                  coldRestartConfig,
                  "Cold rerun-like browser verification after hot-restart fetch failure",
                  markCheckpointRefresh
                );
                coldRestartClient.logCookieStatus("after cold rerun browser verification");
              } catch (refreshError) {
                console.log(
                  withAccountTag(
                    accountLogTag,
                    `[warn] Cold rerun browser verification failed: ${refreshError.message}`
                  )
                );
              }
            }

            coldRestartClient.logCookieStatus("before cold rerun session attempt");

            const coldRestartReuse = await attemptSessionReuse(
              coldRestartClient,
              coldRestartConfig,
              markCheckpointRefresh,
              accountLogTag
            );

            if (coldRestartReuse.ok) {
              console.log(withAccountTag(accountLogTag, "[info] Cold rerun-like session restart succeeded."));
              client = coldRestartClient;
              sessionReuse = coldRestartReuse;
              updateCookieDashboard(client, "session-cold-rerun");
            } else {
              console.log(
                withAccountTag(
                  accountLogTag,
                  `[warn] Cold rerun-like session restart did not recover: ${coldRestartReuse.error ? coldRestartReuse.error.message : "unknown"}`
                )
              );
              client = coldRestartClient;
              sessionReuse = coldRestartReuse;
            }
          }

          updateCookieDashboard(client);
        }
      }

      if (sessionReuse.ok) {
        const balance = printBalanceSummary(sessionReuse.balancesData);
        dashboard.setState({
          balance: `CC=${balance.cc} | USDC=${balance.usdcBase} | CBTC=${balance.cbtc}`
        });
        updateAccountCcBalance(account.name, balance.ccNumeric);
        updateAccountUsdcBalance(account.name, Number(balance.usdcBase) || 0);
        recordInitialCcBalance(account.name, balance.ccNumeric);

        // Auto-accept pending offers (non-blocking, run before rewards check)
        await autoAcceptPendingOffers(client, accountLogTag);

        // Auto-resolve own username if not yet cached
        if (!getAccountUsername(account.name) && account.address) {
          try {
            const selfResolve = await apiCallWithTimeout(
              () => client.resolveSendRecipient(account.name),
              "Self-resolve username", 10000
            );
            const selfData = isObject(selfResolve.data) ? selfResolve.data : {};
            if (selfData.username) {
              updateAccountUsername(account.name, selfData.username);
              console.log(withAccountTag(accountLogTag, `[info] Resolved own username: ${selfData.username}`));
            }
          } catch (err) {
            console.log(withAccountTag(accountLogTag, `[warn] Self-resolve username failed (non-critical): ${err.message}`));
          }
        }

        await refreshThisWeekRewardDashboard(client, dashboard, accountLogTag, account.name);

        // Profitability gate: wait until network recovery >= threshold before sending
        if (sendMode !== "balance-only") {
          dashboard.setState({ phase: "profitability-check" });
          await waitForProfitabilityWithClient(client, accountConfig, accountLogTag);
        }

        // Tier is now known — safe to build send requests with correct amount range.
        buildSendRequestsNow();
        if (buildDeferResult) {
          return buildDeferResult;
        }

        let sendBatchResult = {
          completedTx: 0,
          skippedTx: 0,
          deferred: false,
          deferReason: null,
          deferRetryAfterSeconds: 0
        };

        if (sendRequests.length > 0) {
          sendBatchResult = await executeSendBatch(
            client,
            sendRequests,
            accountConfig,
            dashboard,
            markCheckpointRefresh,
            accountLogTag,
            account.name // senderAccountName for pair tracking
          );

          // Accumulate global and per-account TX stats
          const batchCompleted = clampToNonNegativeInt(sendBatchResult.completedTx, 0);
          const batchFailed = clampToNonNegativeInt(sendBatchResult.skippedTx, 0);
          addGlobalTxStats(batchCompleted, batchFailed);
          addPerAccountTxStats(account.name, batchCompleted, batchFailed);

          // Persist daily progress immediately after each account TX
          // Use loopRound - 1 as completedRounds: current round is still in progress
          if (!args.dryRun && (batchCompleted > 0 || batchFailed > 0)) {
            saveDailyProgress(tokens, Math.max(0, loopRound - 1), globalSwapsOk + globalSwapsFail, perAccountTxStats);
            await saveTokensSerial(tokensPath, tokens);
          }

          // Update dashboard banner with global totals
          dashboard.setState({
            swapsTotal: globalSwapsTotal,
            swapsOk: globalSwapsOk,
            swapsFail: globalSwapsFail
          });
        }

        client.logCookieStatus("after session reuse");
        updateCookieDashboard(client, "session-reused");
        console.log("[done] Login and balance check completed using existing session.");

        tokens.accounts[account.name] = applyClientStateToTokenProfile(
          accountToken,
          client,
          checkpointRefreshCount,
          lastVercelRefreshAt
        );
        await saveTokensSerial(tokensPath, tokens);
        console.log("[info] Session/header/device/security saved to tokens.json");
        return {
          success: true,
          account: account.name,
          mode: "session-reuse",
          deferred: Boolean(sendBatchResult.deferred),
          deferReason: sendBatchResult.deferReason || null,
          deferRetryAfterSeconds: clampToNonNegativeInt(
            sendBatchResult.deferRetryAfterSeconds,
            TX_RETRY_INITIAL_DELAY_SECONDS
          ),
          deferRequiredAmount: sendBatchResult.deferRequiredAmount,
          deferAvailableAmount: sendBatchResult.deferAvailableAmount,
          sentRecipientLabels: Array.isArray(sendBatchResult.sentRecipientLabels)
            ? sendBatchResult.sentRecipientLabels
            : [],
          txCompleted: clampToNonNegativeInt(sendBatchResult.completedTx, 0),
          txSkipped: clampToNonNegativeInt(sendBatchResult.skippedTx, 0)
        };
      }

      const sessionError = sessionReuse.error;
      if (sessionError && sessionError.code === "SESSION_REUSE_TRANSIENT_RETRY_LIMIT") {
        const retryAfterSeconds = Math.max(
          TX_RETRY_INITIAL_DELAY_SECONDS,
          clampToNonNegativeInt(
            sessionReuse.retryAfterSeconds,
            clampToNonNegativeInt(sessionError.retryAfterSeconds, 90)
          )
        );

        dashboard.setState({
          phase: "cooldown",
          transfer: "deferred (session-reuse-transient)",
          send: `Session reuse unstable. Deferred ${retryAfterSeconds}s`,
          cooldown: `${retryAfterSeconds}s`
        });
        console.log(
          withAccountTag(
            accountLogTag,
            `[warn] Session reuse deferred after transient retry limit. Retry in ${retryAfterSeconds}s.`
          )
        );

        tokens.accounts[account.name] = applyClientStateToTokenProfile(
          accountToken,
          client,
          checkpointRefreshCount,
          lastVercelRefreshAt
        );
        await saveTokensSerial(tokensPath, tokens);

        return {
          success: true,
          account: account.name,
          mode: "session-reuse-deferred",
          deferred: true,
          deferReason: "session-reuse-transient",
          deferRetryAfterSeconds: retryAfterSeconds,
          deferRequiredAmount: null,
          deferAvailableAmount: null,
          sentRecipientLabels: [],
          txCompleted: 0,
          txSkipped: 0
        };
      }

      if (isVercelCheckpointError(sessionError)) {
        tokens.accounts[account.name] = applyClientStateToTokenProfile(
          accountToken,
          client,
          checkpointRefreshCount,
          lastVercelRefreshAt
        );
        await saveTokensSerial(tokensPath, tokens);
        console.log("[info] Latest refreshed security cookies saved to tokens.json");

        if (!accountConfig.session.fallbackToOtpOnPersistentCheckpoint) {
          throw new Error(
            "Existing session still blocked by Vercel Security Checkpoint after refresh attempts. " +
            "Fallback to OTP is disabled by config.session.fallbackToOtpOnPersistentCheckpoint=false."
          );
        }

        dashboard.setState({ phase: "otp-fallback" });
        console.log(
          "[warn] Existing session still blocked by Vercel checkpoint after refresh attempts. Falling back to OTP flow as last resort."
        );

        // Force fresh browser challenge before OTP fallback to get valid security cookies
        console.log(withAccountTag(accountLogTag, "[step] Force fresh browser challenge before OTP fallback..."));
        await refreshVercelSecurityCookies(
          client,
          accountConfig,
          "Fresh browser verification for OTP fallback",
          markCheckpointRefresh
        );
        client.logCookieStatus("after fresh browser for OTP fallback");
        updateCookieDashboard(client);

        const settleDelayMs = Math.max(
          0,
          clampToNonNegativeInt(accountConfig.session.checkpointSettleDelayMs, 3500)
        );
        if (settleDelayMs > 0) {
          console.log(`[info] Waiting ${settleDelayMs}ms before OTP fallback...`);
          await sleep(settleDelayMs);
        }
      } else {
        if (isInvalidSessionError(sessionError)) {
          console.log(`[info] Existing session is invalid: ${sessionError.message}`);
          console.log("[info] Falling back to OTP login flow.");
        } else {
          throw new Error(
            `Existing session is not reusable but not marked invalid-session: ${sessionError.message}`
          );
        }
      }
    }

    // FULL PROXY MODE: All API calls go through proxy.
    // No bypass needed — browser challenge obtained _vcrcs through same proxy IP.

    dashboard.setState({ phase: "otp-send" });
    console.log(withAccountTag(accountLogTag, "[step] Send OTP"));
    let sendOtpResponse = null;
    try {
      sendOtpResponse = await sendOtpWithCheckpointRecovery(
        client,
        selectedEmail,
        accountConfig,
        markCheckpointRefresh
      );
    } catch (error) {
      const otpCheckpointDefer = error && error.code === "SEND_OTP_CHECKPOINT_DEFER";
      if (otpCheckpointDefer || isCheckpointOr429Error(error)) {
        const fallbackRetryAfterSeconds = Math.max(
          60,
          clampToNonNegativeInt(accountConfig.session.browserChallengeRetryAfterSeconds, 120)
        );
        const retryAfterSeconds = Math.max(
          30,
          clampToNonNegativeInt(
            error && error.retryAfterSeconds,
            fallbackRetryAfterSeconds
          )
        );
        const errorMessage = String(error && error.message ? error.message : error || "unknown");

        dashboard.setState({
          phase: "cooldown",
          transfer: "deferred (otp-checkpoint)",
          send: `OTP checkpoint deferred ${retryAfterSeconds}s`,
          cooldown: `${retryAfterSeconds}s`
        });
        console.log(
          withAccountTag(
            accountLogTag,
            `[warn] OTP flow blocked by checkpoint. Defer ${retryAfterSeconds}s. Detail: ${errorMessage}`
          )
        );

        tokens.accounts[account.name] = applyClientStateToTokenProfile(
          accountToken,
          client,
          checkpointRefreshCount,
          lastVercelRefreshAt
        );
        await saveTokensSerial(tokensPath, tokens);

        return {
          success: true,
          account: account.name,
          mode: "otp-checkpoint-deferred",
          deferred: true,
          deferReason: "otp-checkpoint",
          deferRetryAfterSeconds: retryAfterSeconds,
          deferRequiredAmount: null,
          deferAvailableAmount: null,
          sentRecipientLabels: [],
          txCompleted: 0,
          txSkipped: 0
        };
      }

      throw error;
    }
    updateCookieDashboard(client);
    const otpId = sendOtpResponse && sendOtpResponse.data ? sendOtpResponse.data.otpId : null;

    if (!otpId) {
      throw new Error("send-otp did not return otpId");
    }

    console.log(`[info] OTP sent to ${maskEmail(selectedEmail)} | otpId=${maskSecret(otpId, 8, 6)}`);

    const otpCode = await promptOtpCode();

    if (!/^\d{4,8}$/.test(otpCode)) {
      throw new Error("OTP format must be numeric (4 to 8 digits)");
    }

    dashboard.setState({ phase: "otp-verify" });
    console.log(withAccountTag(accountLogTag, "[step] Verify OTP"));
    const verifyResponse = await client.verifyOtp({
      email: selectedEmail,
      otpId,
      otpCode
    });

    const nextStep = verifyResponse && verifyResponse.data ? verifyResponse.data.nextStep : null;
    console.log(`[info] verify-otp nextStep: ${nextStep || "unknown"}`);

    dashboard.setState({ phase: "sync-onboard" });
    console.log(withAccountTag(accountLogTag, "[step] Sync account (onboard referer)"));
    await client.syncAccount(accountConfig.paths.onboard);

    const pendingAfterVerify = await client.getPending(accountConfig.paths.onboard);
    const pendingData = pendingAfterVerify && pendingAfterVerify.data ? pendingAfterVerify.data : {};
    console.log(`[info] Pending after verify: ${Boolean(pendingData.pending)}`);

    if (pendingData.pending) {
      if (pendingData.alreadyActive === true) {
        dashboard.setState({ phase: "finalize-returning" });
        console.log(withAccountTag(accountLogTag, "[step] Finalize returning account"));
        const finalizeResponse = await client.finalizeReturning();
        const username = finalizeResponse && finalizeResponse.data ? finalizeResponse.data.username : pendingData.existingUsername;
        console.log(`[info] Finalized returning user: ${username || "unknown"}`);
        if (username) {
          updateAccountUsername(account.name, username);
          console.log(withAccountTag(accountLogTag, `[info] Cached username: ${username}`));
        }
      } else {
        throw new Error(
          "Account still in pending state and not marked alreadyActive. This script currently handles returning-account flow."
        );
      }
    }

    dashboard.setState({ phase: "sync-bridge" });
    console.log(withAccountTag(accountLogTag, "[step] Sync account (bridge referer)"));
    await client.syncAccount(accountConfig.paths.bridge);

    dashboard.setState({ phase: "balances" });
    console.log(withAccountTag(accountLogTag, "[step] Get balances"));
    const balancesResponse = await client.getBalances();
    const balance = printBalanceSummary(balancesResponse && balancesResponse.data ? balancesResponse.data : {});
    dashboard.setState({
      balance: `CC=${balance.cc} | USDC=${balance.usdcBase} | CBTC=${balance.cbtc}`
    });
    updateAccountCcBalance(account.name, balance.ccNumeric);
    updateAccountUsdcBalance(account.name, Number(balance.usdcBase) || 0);
    recordInitialCcBalance(account.name, balance.ccNumeric);

    // Auto-accept pending offers (non-blocking, run before rewards check)
    await autoAcceptPendingOffers(client, accountLogTag);

    // Auto-resolve own username if not yet cached
    if (!getAccountUsername(account.name) && account.address) {
      try {
        const selfResolve = await apiCallWithTimeout(
          () => client.resolveSendRecipient(account.name),
          "Self-resolve username", 10000
        );
        const selfData = isObject(selfResolve.data) ? selfResolve.data : {};
        if (selfData.username) {
          updateAccountUsername(account.name, selfData.username);
          console.log(withAccountTag(accountLogTag, `[info] Resolved own username: ${selfData.username}`));
        }
      } catch (err) {
        console.log(withAccountTag(accountLogTag, `[warn] Self-resolve username failed (non-critical): ${err.message}`));
      }
    }

    await refreshThisWeekRewardDashboard(client, dashboard, accountLogTag, account.name);

    // Profitability gate: wait until network recovery >= threshold before sending
    if (sendMode !== "balance-only") {
      dashboard.setState({ phase: "profitability-check" });
      await waitForProfitabilityWithClient(client, accountConfig, accountLogTag);
    }

    // Tier is now known — safe to build send requests with correct amount range.
    buildSendRequestsNow();
    if (buildDeferResult) {
      return buildDeferResult;
    }

    let sendBatchResult = {
      completedTx: 0,
      skippedTx: 0,
      deferred: false,
      deferReason: null,
      deferRetryAfterSeconds: 0
    };

    if (sendRequests.length > 0) {
      sendBatchResult = await executeSendBatch(
        client,
        sendRequests,
        accountConfig,
        dashboard,
        markCheckpointRefresh,
        accountLogTag,
        account.name // senderAccountName for pair tracking
      );

      // Accumulate global and per-account TX stats
      const batchCompleted = clampToNonNegativeInt(sendBatchResult.completedTx, 0);
      const batchFailed = clampToNonNegativeInt(sendBatchResult.skippedTx, 0);
      addGlobalTxStats(batchCompleted, batchFailed);
      addPerAccountTxStats(account.name, batchCompleted, batchFailed);

      // Persist daily progress immediately after each account TX
      // Use loopRound - 1 as completedRounds: current round is still in progress
      if (!args.dryRun && (batchCompleted > 0 || batchFailed > 0)) {
        saveDailyProgress(tokens, Math.max(0, loopRound - 1), globalSwapsOk + globalSwapsFail, perAccountTxStats);
        await saveTokensSerial(tokensPath, tokens);
      }

      // Update dashboard banner with global totals
      dashboard.setState({
        swapsTotal: globalSwapsTotal,
        swapsOk: globalSwapsOk,
        swapsFail: globalSwapsFail
      });
    }

    client.logCookieStatus("after login flow");
    updateCookieDashboard(client, "completed");
    if (!client.hasAccountSessionCookie()) {
      console.log(
        "[warn] cantonbridge_session is not present in cookie jar yet. This can happen if runtime does not expose set-cookie headers."
      );
    }

    console.log("[done] Login and balance check completed.");

    tokens.accounts[account.name] = applyClientStateToTokenProfile(
      accountToken,
      client,
      checkpointRefreshCount,
      lastVercelRefreshAt
    );
    await saveTokensSerial(tokensPath, tokens);
    console.log("[info] Session/header/device/security saved to tokens.json");

    return {
      success: true,
      account: account.name,
      mode: "otp-login",
      deferred: Boolean(sendBatchResult.deferred),
      deferReason: sendBatchResult.deferReason || null,
      deferRetryAfterSeconds: clampToNonNegativeInt(
        sendBatchResult.deferRetryAfterSeconds,
        TX_RETRY_INITIAL_DELAY_SECONDS
      ),
      deferRequiredAmount: sendBatchResult.deferRequiredAmount,
      deferAvailableAmount: sendBatchResult.deferAvailableAmount,
      sentRecipientLabels: Array.isArray(sendBatchResult.sentRecipientLabels)
        ? sendBatchResult.sentRecipientLabels
        : [],
      txCompleted: clampToNonNegativeInt(sendBatchResult.completedTx, 0),
      txSkipped: clampToNonNegativeInt(sendBatchResult.skippedTx, 0)
    };
  } finally {
    dashboard.detach();
  }
}

function getNextMidnightUTC() {
  const now = new Date();
  const tomorrow = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate() + 1,
    0, 0, 0, 0
  ));
  return tomorrow;
}

function formatDuration(ms) {
  const totalSeconds = Math.floor(ms / 1000);
  const hours = Math.floor(totalSeconds / 3600);
  const minutes = Math.floor((totalSeconds % 3600) / 60);
  const seconds = totalSeconds % 60;
  return `${hours}h ${minutes}m ${seconds}s`;
}

function formatUTCTime(date) {
  return date.toISOString().replace("T", " ").slice(0, 19) + " UTC";
}

// ============================================================================
// TELEGRAM AUTO-REPORT
// ============================================================================
// Sends a reward snapshot to Telegram at two triggers:
//   1. Cycle start (baseline).
//   2. When every account has reached the hourly TX cap (batch complete).
// Before collecting, scheduler pauses (reportingInProgress=true) and waits
// until inFlight is empty — guarantees no TX running while we read state.
// ============================================================================

let reportingInProgress = false;
let lastAutoReportAtMs = 0;

function isReportingInProgress() {
  return reportingInProgress;
}

function nowJakartaLabel() {
  return new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" }) + " WIB";
}

async function sendTelegramMessage(telegramConfig, text) {
  if (!telegramConfig || !telegramConfig.enabled) return false;
  const token = String(telegramConfig.botToken || "").trim();
  const chatIds = Array.isArray(telegramConfig.allowedChatIds)
    ? telegramConfig.allowedChatIds
    : [];
  if (!token || chatIds.length === 0) return false;

  const maxLen = 3800;
  const chunks = [];
  let rest = String(text || "");
  while (rest.length > maxLen) {
    let cut = rest.lastIndexOf("\n", maxLen);
    if (cut < maxLen * 0.5) cut = maxLen;
    chunks.push(rest.slice(0, cut));
    rest = rest.slice(cut).replace(/^\n+/, "");
  }
  if (rest) chunks.push(rest);

  const url = `https://api.telegram.org/bot${token}/sendMessage`;
  let sentAny = false;
  for (const chatId of chatIds) {
    for (const chunk of chunks) {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(new Error("telegram timeout")), 20000);
      try {
        const res = await fetch(url, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({
            chat_id: chatId,
            text: chunk,
            disable_web_page_preview: true
          }),
          signal: controller.signal
        });
        if (!res.ok) {
          const body = await res.text();
          console.warn(`[telegram] sendMessage HTTP ${res.status}: ${body.slice(0, 160)}`);
        } else {
          sentAny = true;
        }
      } catch (err) {
        console.warn(`[telegram] sendMessage error: ${err.message}`);
      } finally {
        clearTimeout(timer);
      }
    }
  }
  return sentAny;
}

function buildAutoReportMessage(trigger, sortedAccounts) {
  const lines = [];
  lines.push("🏆 RootsFi Auto Reward Report");
  lines.push(`🕐 ${nowJakartaLabel()}`);
  lines.push(`📌 Trigger: ${trigger}`);
  lines.push("━━━━━━━━━━━━━━━━━━━━━");

  let totalWeekCc = 0;
  let totalWeekUsd = 0;
  let totalDiffCc = 0;
  let totalDiffUsd = 0;
  let totalTx = 0;
  let totalOk = 0;
  let totalFail = 0;
  let totalCcBalance = 0;
  const scores = [];

  for (const acc of sortedAccounts) {
    const name = acc.name;
    const week = getAccountRewardsThisWeek(name);
    const diff = getAccountRewardsDiff(name);
    const tier = tierDisplayNameByAccount.get(name) || "?";
    const score = getAccountQualityScore(name);
    const txStats = getPerAccountTxStats(name);
    const cc = getAccountCcBalance(name);
    const hourlyCount = getHourlyTxCount(name);

    const weekCcN = isObject(week) && Number.isFinite(week.cc) ? week.cc : 0;
    const weekUsdN = isObject(week) && Number.isFinite(week.usd) ? week.usd : 0;
    const diffCcN = isObject(diff) && Number.isFinite(diff.cc) ? diff.cc : 0;
    const diffUsdN = isObject(diff) && Number.isFinite(diff.usd) ? diff.usd : 0;

    totalWeekCc += weekCcN;
    totalWeekUsd += weekUsdN;
    totalDiffCc += diffCcN;
    totalDiffUsd += diffUsdN;
    totalTx += txStats.total;
    totalOk += txStats.ok;
    totalFail += txStats.fail;
    if (Number.isFinite(cc)) totalCcBalance += cc;
    if (Number.isFinite(score)) scores.push(score);

    const scoreLabel = Number.isFinite(score) ? `${score}/100` : "-";
    const ccLabel = Number.isFinite(cc) ? `${cc.toFixed(2)} CC` : "-";
    const weekLabel = isObject(week)
      ? `${weekCcN.toFixed(2)} CC ($${weekUsdN.toFixed(2)})`
      : "-";
    const diffLabel = isObject(diff)
      ? `${diffCcN >= 0 ? "+" : ""}${diffCcN.toFixed(2)} CC (${diffUsdN >= 0 ? "+" : ""}$${diffUsdN.toFixed(2)})`
      : "-";

    lines.push(`🏦 ${name}`);
    lines.push(`   Tier: ${tier} | Score: ${scoreLabel}`);
    lines.push(`   CC: ${ccLabel} | TX: ${txStats.total} (ok:${txStats.ok}|fail:${txStats.fail}) | hr:${hourlyCount}/${HOURLY_MAX_TX_PER_ACCOUNT}`);
    lines.push(`   Week: ${weekLabel}`);
    lines.push(`   Session diff: ${diffLabel}`);
  }

  const avgScore = scores.length > 0
    ? (scores.reduce((s, v) => s + v, 0) / scores.length).toFixed(1)
    : "-";

  lines.push("━━━━━━━━━━━━━━━━━━━━━");
  lines.push(`📊 TX total: ${totalTx} (ok:${totalOk} | fail:${totalFail})`);
  lines.push(`💰 Total CC balance: ${totalCcBalance.toFixed(4)} CC`);
  lines.push(`📅 Rewards this week: ${totalWeekCc.toFixed(2)} CC | $${totalWeekUsd.toFixed(2)}`);
  lines.push(`🚀 Session earnings: ${totalDiffCc >= 0 ? "+" : ""}${totalDiffCc.toFixed(2)} CC | ${totalDiffUsd >= 0 ? "+" : ""}$${totalDiffUsd.toFixed(2)}`);
  lines.push(`🎯 Avg Score: ${avgScore}${scores.length > 0 ? "/100" : ""}`);

  return lines.join("\n");
}

/**
 * Wait until there are no in-flight TX jobs, then send a report.
 * Sets reportingInProgress=true so the scheduler defers new assignments.
 * Respects minIntervalMinutes cooldown to prevent spam.
 */
async function triggerAutoReport(config, sortedAccounts, inFlight, trigger, options = {}) {
  const telegramConfig = config.telegram;
  if (!telegramConfig || !telegramConfig.enabled) return false;
  if (!telegramConfig.autoReport || !telegramConfig.autoReport.enabled) return false;

  const token = String(telegramConfig.botToken || "").trim();
  const chatIds = Array.isArray(telegramConfig.allowedChatIds) ? telegramConfig.allowedChatIds : [];
  if (!token || chatIds.length === 0) {
    console.log("[telegram] Auto-report skipped: missing botToken or allowedChatIds");
    return false;
  }

  const force = Boolean(options.force);
  const minIntervalMs = Math.max(0, Number(telegramConfig.autoReport.minIntervalMinutes || 0) * 60 * 1000);
  if (!force && lastAutoReportAtMs > 0 && (Date.now() - lastAutoReportAtMs) < minIntervalMs) {
    return false;
  }

  if (reportingInProgress) return false;
  reportingInProgress = true;

  try {
    if (inFlight && inFlight.size > 0) {
      console.log(`[telegram] Waiting for ${inFlight.size} in-flight TX to finish before collecting report...`);
      const waitStart = Date.now();
      while (inFlight.size > 0 && (Date.now() - waitStart) < 5 * 60 * 1000) {
        await sleep(1500);
      }
      if (inFlight.size > 0) {
        console.warn(`[telegram] ${inFlight.size} TX still in-flight after 5min wait — aborting report collection to avoid stale data`);
        return false;
      }
    }

    const message = buildAutoReportMessage(trigger, sortedAccounts);
    const sent = await sendTelegramMessage(telegramConfig, message);
    if (sent) {
      lastAutoReportAtMs = Date.now();
      console.log(`[telegram] Auto-report sent (trigger=${trigger})`);
    }
    return sent;
  } finally {
    reportingInProgress = false;
  }
}

async function runDailyCycle(context) {
  const {
    config,
    accounts,
    tokens,
    tokensPath,
    sendMode,
    recipientsInfo,
    args
  } = context;

  const cycleStartTime = new Date();

  resetGlobalTxStats();
  cleanupExpiredSendPairs();
  nextAvailableAtByAccount.clear();
  claimedRecipients.clear();

  const sortedAccounts = [...accounts.accounts].sort((a, b) =>
    a.name.localeCompare(b.name)
  );

  // Resume-aware daily progress (UTC day)
  const dailyProgress = sendMode === "balance-only"
    ? { completedRounds: 0, completedTxTotal: 0, perAccount: {} }
    : loadDailyProgress(tokens);
  if (dailyProgress.completedTxTotal > 0 && isObject(dailyProgress.perAccount)) {
    for (const [name, stats] of Object.entries(dailyProgress.perAccount)) {
      if (isObject(stats)) {
        addPerAccountTxStats(
          name,
          clampToNonNegativeInt(stats.ok, 0),
          clampToNonNegativeInt(stats.fail, 0)
        );
        addGlobalTxStats(
          clampToNonNegativeInt(stats.ok, 0),
          clampToNonNegativeInt(stats.fail, 0)
        );
      }
    }
  }

  const totalAccounts = sortedAccounts.length;
  const targetTxPerAccount = Math.max(
    1,
    clampToNonNegativeInt(config.send.maxLoopTx || config.send.maxTx, 25)
  );

  console.log(`\n${"#".repeat(70)}`);
  console.log(`[cycle] Continuous scheduler started at ${formatUTCTime(cycleStartTime)}`);
  console.log(`[cycle] Mode: ${sendMode} | Accounts: ${totalAccounts} | Target/account: ${targetTxPerAccount} TX`);
  {
    const minDelay = clampToNonNegativeInt(config.send.minDelayTxSeconds, INTERNAL_API_DEFAULTS.send.minDelayTxSeconds);
    const maxDelay = clampToNonNegativeInt(config.send.maxDelayTxSeconds, INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds);
    console.log(`[cycle] Per-account TX delay: ${minDelay}-${maxDelay}s | Hourly cap: ${HOURLY_MAX_TX_PER_ACCOUNT}/hr (${hourlyCapSource}) | Reciprocal pair cooldown: ${Math.round(SEND_PAIR_COOLDOWN_MS / 1000)}s`);
  }
  console.log(`${"#".repeat(70)}\n`);

  // Balance-only fast path: login + print balance per account, no scheduler/TX.
  if (sendMode === "balance-only") {
    const boResults = [];
    const boSnapshots = {};
    for (let i = 0; i < sortedAccounts.length; i++) {
      const account = sortedAccounts[i];
      const accountToken = tokens.accounts[account.name] || normalizeTokenProfile({});
      tokens.accounts[account.name] = accountToken;
      try {
        const result = await processAccount({
          account,
          accountToken,
          config,
          tokens,
          tokensPath,
          sendMode,
          recipientsInfo,
          args,
          accountIndex: i,
          totalAccounts: sortedAccounts.length,
          selectedAccounts: sortedAccounts,
          accountSnapshots: boSnapshots,
          loopRound: 1,
          totalLoopRounds: 1,
          maxLoopTxOverride: 0,
          smartFillBlockRecipients: [],
          resumeFromDeferReason: "",
          preferRecipientNames: []
        });
        boResults.push(result);
      } catch (error) {
        console.error(`[error] ${account.name}: ${error.message}`);
        boResults.push({ success: false, account: account.name, error: error.message });
      }
    }
    if (!args.dryRun) {
      try { await saveTokensSerial(tokensPath, tokens); } catch (err) {
        console.warn(`[warn] Failed to persist tokens: ${err.message}`);
      }
    }
    const cycleEndTime = new Date();
    return {
      results: boResults,
      successful: boResults.filter((r) => r && r.success && !r.deferred),
      failed: boResults.filter((r) => r && !r.success),
      cycleDuration: cycleEndTime - cycleStartTime
    };
  }

  const results = [];
  const accountSnapshots = {};
  const inFlight = new Set();
  const completedByAccount = new Map();
  const skipLoggedAt = new Map();
  const noRecipientLoggedAt = new Map();
  const accountIndexByName = new Map();
  sortedAccounts.forEach((acc, idx) => accountIndexByName.set(acc.name, idx));

  // Seed completed counts from resumed progress (per-account)
  for (const acc of sortedAccounts) {
    const stats = getPerAccountTxStats(acc.name);
    completedByAccount.set(acc.name, clampToNonNegativeInt(stats.ok, 0));
  }

  const minDelaySec = clampToNonNegativeInt(
    config.send.minDelayTxSeconds,
    INTERNAL_API_DEFAULTS.send.minDelayTxSeconds
  );
  const maxDelaySec = clampToNonNegativeInt(
    config.send.maxDelayTxSeconds,
    INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds
  );
  const startJitterMin = Math.min(minDelaySec, maxDelaySec);
  const startJitterMax = Math.max(minDelaySec, maxDelaySec);

  const workerCap = Math.max(
    1,
    clampToNonNegativeInt(config.send.workers, totalAccounts)
  );

  // Global dashboard uptime ticker (writes to whichever dashboard is active)
  setGlobalUptimeStart(cycleStartTime.getTime());
  const uptimeTicker = setInterval(() => {
    const elapsedMs = Date.now() - cycleStartTime.getTime();
    setGlobalUptimeLabel(formatDuration(elapsedMs));
    if (activeDashboardRef && typeof activeDashboardRef.setState === "function") {
      activeDashboardRef.setState({ uptime: formatDuration(elapsedMs) });
    }
  }, 1000);

  // Periodic Telegram auto-report: fire every minIntervalMinutes regardless
  // of TX events (cycle-start / hourly-cap). Skip if disabled.
  let periodicReportTicker = null;
  if (
    config.telegram && config.telegram.enabled &&
    config.telegram.autoReport && config.telegram.autoReport.enabled
  ) {
    const intervalMs = Math.max(1, Number(config.telegram.autoReport.minIntervalMinutes || 30)) * 60 * 1000;
    periodicReportTicker = setInterval(() => {
      triggerAutoReport(config, sortedAccounts, inFlight, "periodic").catch((err) => {
        console.warn(`[telegram] Periodic auto-report failed: ${err.message}`);
      });
    }, intervalMs);
    if (typeof periodicReportTicker.unref === "function") periodicReportTicker.unref();
    console.log(`[telegram] Periodic auto-report scheduled every ${config.telegram.autoReport.minIntervalMinutes} minute(s)`);
  }

  const updateGlobalDashboard = () => {
    if (!activeDashboardRef || typeof activeDashboardRef.setState !== "function") return;
    const totalTargetTx = totalAccounts * targetTxPerAccount;
    const doneTx = globalSwapsOk + globalSwapsFail;
    activeDashboardRef.setState({
      swapsTotal: `${doneTx}/${totalTargetTx}`,
      swapsOk: String(globalSwapsOk),
      swapsFail: String(globalSwapsFail)
    });
  };

  // Apply small random first-run jitter so the 17 accounts don't fire exactly together
  {
    const nowMs = Date.now();
    for (const acc of sortedAccounts) {
      const jitter = randomIntInclusive(0, Math.max(0, startJitterMax));
      nextAvailableAtByAccount.set(acc.name, nowMs + (jitter * 1000));
    }
  }

  const isAccountDone = (name) => {
    const done = completedByAccount.get(name) || 0;
    return done >= targetTxPerAccount;
  };

  const allAccountsDone = () => {
    for (const acc of sortedAccounts) {
      if (!isAccountDone(acc.name)) return false;
    }
    return true;
  };

  const runOne = async (account) => {
    const accountName = account.name;
    inFlight.add(accountName);
    const accountIdx = accountIndexByName.get(accountName) || 0;
    const accountToken = tokens.accounts[accountName] || normalizeTokenProfile({});
    tokens.accounts[accountName] = accountToken;

    // Pre-check sender balance: must cover tierMin + safety buffer.
    // If not, skip without retry — this account will become recipient priority
    // until someone else fills it.
    const senderCc = Number(getAccountCcBalance(accountName));
    const tierMinSender = getAccountTierMinSend(accountName);
    const buffer = clampToNonNegativeInt(
      config.safety && config.safety.minHoldBalanceCc,
      2
    );
    if (Number.isFinite(senderCc) && senderCc > 0 && senderCc < (tierMinSender + buffer)) {
      const lastLogged = skipLoggedAt.get(accountName) || 0;
      if (Date.now() - lastLogged > 30 * 1000) {
        console.log(
          `[skip] ${accountName} insufficient balance for tier min: ` +
          `cc=${senderCc.toFixed(2)} need>=${tierMinSender + buffer} (tierMin=${tierMinSender}+buffer=${buffer}). ` +
          `Waiting inbound.`
        );
        skipLoggedAt.set(accountName, Date.now());
      }
      // Re-check in 30s — may have received inbound
      nextAvailableAtByAccount.set(accountName, Date.now() + 30 * 1000);
      setAccountCooldownEnd(accountName, Date.now() + 30 * 1000);
      inFlight.delete(accountName);
      return;
    }

    // Pick recipient: lowest TX progress first, then neediest, no double-inbound, no reciprocal cooldown
    const recipient = pickSmartRecipient(accountName, sortedAccounts);
    if (!recipient) {
      const lastLogged = noRecipientLoggedAt.get(accountName) || 0;
      if (Date.now() - lastLogged > 30 * 1000) {
        console.log(`[skip] ${accountName} no eligible recipient (all claimed/cooldown). Retry in 15s.`);
        noRecipientLoggedAt.set(accountName, Date.now());
      }
      nextAvailableAtByAccount.set(accountName, Date.now() + 15 * 1000);
      setAccountCooldownEnd(accountName, Date.now() + 15 * 1000);
      inFlight.delete(accountName);
      return;
    }

    if (!claimRecipient(recipient.name)) {
      // Race: lost claim; retry quickly
      nextAvailableAtByAccount.set(accountName, Date.now() + 5 * 1000);
      inFlight.delete(accountName);
      return;
    }

    let resultRecord = null;
    let success = false;
    try {
      console.log(`[schedule] ${accountName} -> ${recipient.name} | cc=${senderCc.toFixed(2)} (tierMin=${tierMinSender})`);
      updateLastSendTarget(accountName, recipient.name);
      const result = await processAccount({
        account,
        accountToken,
        config,
        tokens,
        tokensPath,
        sendMode,
        recipientsInfo,
        args,
        accountIndex: accountIdx,
        totalAccounts,
        selectedAccounts: sortedAccounts,
        accountSnapshots,
        loopRound: (completedByAccount.get(accountName) || 0) + 1,
        totalLoopRounds: targetTxPerAccount,
        maxLoopTxOverride: 1,
        smartFillBlockRecipients: [],
        resumeFromDeferReason: "",
        preferRecipientNames: [recipient.name]
      });

      resultRecord = { ...result };
      success = Boolean(result && result.success && !result.deferred);
    } catch (error) {
      console.error(`[error] ${accountName}: ${error.message}`);
      resultRecord = { success: false, account: accountName, error: error.message };
    } finally {
      releaseRecipient(recipient.name);
    }

    results.push(resultRecord);

    if (success) {
      completedByAccount.set(
        accountName,
        (completedByAccount.get(accountName) || 0) + 1
      );
      recordTxTimestamp(accountName);
      maybeProbeHigherCap();

      // Next-available: humanLikeDelay window + safety buffer.
      // If hourly cap reached, push to oldest+1h (clamp by hourly waiter).
      const minDelaySec = clampToNonNegativeInt(
        config.send.minDelayTxSeconds,
        INTERNAL_API_DEFAULTS.send.minDelayTxSeconds
      );
      const maxDelaySec = Math.max(
        minDelaySec,
        clampToNonNegativeInt(
          config.send.maxDelayTxSeconds,
          INTERNAL_API_DEFAULTS.send.maxDelayTxSeconds
        )
      );
      const gapSec = humanLikeDelay(minDelaySec, maxDelaySec);
      const baseNextAvailable = Date.now() + (gapSec * 1000) + PER_ACCOUNT_TX_COOLDOWN_BUFFER_MS;
      const hourlyWaitMs = getHourlyResetWaitMs(accountName);
      const hourlyNextAvailable = hourlyWaitMs > 0 ? Date.now() + hourlyWaitMs : 0;
      const nextAt = Math.max(baseNextAvailable, hourlyNextAvailable);
      nextAvailableAtByAccount.set(accountName, nextAt);
      setAccountCooldownEnd(accountName, nextAt);

      if (hourlyWaitMs > 0) {
        console.log(
          `[hourly] ${accountName} reached ${HOURLY_MAX_TX_PER_ACCOUNT}/hr cap, ` +
          `next attempt in ${Math.ceil(hourlyWaitMs / 1000)}s`
        );
      }
    } else if (resultRecord && resultRecord.deferred) {
      // Per requirement: deferred account does NOT keep retrying with the same amount.
      // Back off long enough to let inbound CC accumulate before re-evaluating.
      const reason = String(resultRecord.deferReason || "");
      const defaultWaitByReason = reason === "insufficient-balance" ? 120 : 30;
      const waitSec = Math.max(
        defaultWaitByReason,
        clampToNonNegativeInt(resultRecord.deferRetryAfterSeconds, defaultWaitByReason)
      );
      const nextAt = Date.now() + (waitSec * 1000);
      nextAvailableAtByAccount.set(accountName, nextAt);
      setAccountCooldownEnd(accountName, nextAt);
    } else {
      // Transient failure: short retry
      const nextAt = Date.now() + 20 * 1000;
      nextAvailableAtByAccount.set(accountName, nextAt);
      setAccountCooldownEnd(accountName, nextAt);
    }

    updateGlobalDashboard();

    // Persist progress
    if (!args.dryRun) {
      try {
        saveDailyProgress(
          tokens,
          0,
          globalSwapsOk + globalSwapsFail,
          perAccountTxStats
        );
        await saveTokensSerial(tokensPath, tokens);
      } catch (err) {
        console.warn(`[warn] Failed to persist progress: ${err.message}`);
      }
    }

    inFlight.delete(accountName);
  };

  // Trigger 1: baseline report at cycle start.
  if (config.telegram && config.telegram.autoReport && config.telegram.autoReport.reportAtCycleStart) {
    try {
      await triggerAutoReport(config, sortedAccounts, inFlight, "cycle-start", { force: true });
    } catch (err) {
      console.warn(`[telegram] cycle-start report failed: ${err.message}`);
    }
  }

  // Helper: are all accounts currently at-or-above the hourly cap?
  const allAccountsAtHourlyCap = () => {
    for (const acc of sortedAccounts) {
      if (isAccountDone(acc.name)) continue; // excluded from requirement
      if (getHourlyTxCount(acc.name) < HOURLY_MAX_TX_PER_ACCOUNT) return false;
    }
    return true;
  };

  // Main scheduler loop
  const TICK_MS = 500;
  let consecutiveAllIdle = 0;

  while (!allAccountsDone()) {
    const nowMs = Date.now();

    // Pause launching new TX while an auto-report is being collected.
    if (isReportingInProgress()) {
      await sleep(TICK_MS);
      continue;
    }

    // Trigger 2: every account reached hourly cap → collect report.
    // triggerAutoReport enforces its own minInterval cooldown.
    if (
      config.telegram && config.telegram.autoReport &&
      config.telegram.autoReport.reportOnHourlyCapReached &&
      allAccountsAtHourlyCap()
    ) {
      // Fire-and-forget: it will flip reportingInProgress and wait for inFlight.
      triggerAutoReport(config, sortedAccounts, inFlight, "all-hourly-cap").catch((err) => {
        console.warn(`[telegram] hourly-cap report failed: ${err.message}`);
      });
    }

    // Collect ready accounts
    const readyAccounts = [];
    for (const acc of sortedAccounts) {
      if (isAccountDone(acc.name)) continue;
      if (inFlight.has(acc.name)) continue;
      const readyAt = nextAvailableAtByAccount.get(acc.name) || 0;
      if (readyAt <= nowMs) {
        readyAccounts.push(acc);
      }
    }

    // Respect worker cap
    const freeWorkers = Math.max(0, workerCap - inFlight.size);
    const toLaunch = readyAccounts.slice(0, freeWorkers);

    for (const acc of toLaunch) {
      runOne(acc); // fire and forget — tracked via inFlight + nextAvailableAt
    }

    // Deadlock detection: if every remaining account is skipping due to low
    // balance AND no one is in-flight, we might be stuck. Log a warning every
    // ~60s but keep trying (inbound may resolve it).
    if (inFlight.size === 0 && toLaunch.length === 0) {
      consecutiveAllIdle += 1;
      if (consecutiveAllIdle % 120 === 0) {
        console.log(
          "[schedule] All accounts idle (waiting cooldown/balance). " +
          "If this persists, check tier amounts vs balances."
        );
      }
    } else {
      consecutiveAllIdle = 0;
    }

    await sleep(TICK_MS);
  }

  clearInterval(uptimeTicker);
  if (periodicReportTicker) clearInterval(periodicReportTicker);

  if (!args.dryRun) {
    saveDailyProgress(tokens, 0, globalSwapsOk + globalSwapsFail, perAccountTxStats);
    await saveTokensSerial(tokensPath, tokens);
  }

  const cycleEndTime = new Date();
  const cycleDuration = cycleEndTime - cycleStartTime;

  const successful = results.filter((r) => r && r.success && !r.deferred);
  const failed = results.filter((r) => r && !r.success);

  return { results, successful, failed, cycleDuration };
}

// =============================================================================
// OTC Trading (Cross-OTC) — take-only profit-seeking flow.
// =============================================================================

const OTC_USD_STABLES = new Set(["USDC", "USDCX"]);

function otcAssetToUsd(asset, amount, mids) {
  const sym = String(asset || "").toUpperCase();
  const num = Number(amount);
  if (!Number.isFinite(num) || num <= 0) return null;
  if (OTC_USD_STABLES.has(sym)) return num;
  if (!isObject(mids)) return null;
  if (sym === "CC") {
    const p = Number(mids.cc_usdcx);
    return Number.isFinite(p) && p > 0 ? num * p : null;
  }
  if (sym === "ETH") {
    const p = Number(mids.eth_usdcx);
    return Number.isFinite(p) && p > 0 ? num * p : null;
  }
  return null;
}

function otcAssetBalanceUsd(asset, amount, mids) {
  const usd = otcAssetToUsd(asset, amount, mids);
  return usd === null ? 0 : usd;
}

function otcGetAccountBalance(asset, balanceData) {
  // Struktur asli (lihat printBalanceSummary):
  //   balances.canton.usdcx (number)
  //   balances.canton.tokenHoldings[] / otherHoldings[] dengan metadata.symbol + amountDecimal
  //   balances.ethereum.usdc / .eth
  if (!isObject(balanceData)) return 0;
  const sym = String(asset || "").toUpperCase();
  const balances = isObject(balanceData.balances) ? balanceData.balances : {};
  const canton = isObject(balances.canton) ? balances.canton : {};
  const base = isObject(balances.base) ? balances.base : {};
  const ethereum = isObject(balances.ethereum) ? balances.ethereum : {};

  if (sym === "USDCX") return Number(canton.usdcx) || 0;
  if (sym === "USDC") return Number(base.usdc) || Number(ethereum.usdc) || 0;
  if (sym === "ETH") return Number(base.eth) || Number(ethereum.eth) || 0;

  // For CC + tokens lain, walk Canton tokenHoldings + otherHoldings
  const lists = [];
  if (Array.isArray(canton.tokenHoldings)) lists.push(...canton.tokenHoldings);
  if (Array.isArray(canton.otherHoldings)) lists.push(...canton.otherHoldings);
  if (Array.isArray(ethereum.tokenHoldings)) lists.push(...ethereum.tokenHoldings);
  for (const h of lists) {
    if (!isObject(h)) continue;
    const meta = isObject(h.metadata) ? h.metadata : {};
    const rawSymbol = String(meta.symbol || h.instrumentId || h.symbol || "").trim().toUpperCase();
    if (rawSymbol === sym) {
      const raw = h.amountDecimal ?? h.amount ?? h.amountBaseUnits ?? 0;
      const num = Number(raw);
      return Number.isFinite(num) ? num : 0;
    }
  }
  return 0;
}

function computeOtcOrderEdge(order, mids) {
  if (!isObject(order) || !isObject(mids)) return null;
  const takerPaysUsd = otcAssetToUsd(order.dstAsset, order.dstAmountDecimal, mids);
  const takerRecvUsd = otcAssetToUsd(order.srcAsset, order.srcAmountDecimal, mids);
  if (takerPaysUsd === null || takerRecvUsd === null || takerPaysUsd <= 0) return null;
  const edgeBps = (takerRecvUsd / takerPaysUsd - 1) * 10000;
  return {
    takerPaysUsd,
    takerRecvUsd,
    edgeBps,
    estProfitUsd: takerRecvUsd - takerPaysUsd
  };
}

function isOtcOrderProfitable(order, mids, balanceData, selfProfileId, swapCfg, nowMs, ctx) {
  if (!isObject(order)) return { ok: false, reason: "no-order" };

  // Skip orders that just returned 409 (already reserved/closed)
  if (order.id && isOtcOrderBlacklisted(order.id)) {
    return { ok: false, reason: "blacklisted" };
  }

  // Skip own orders (anti-circular)
  const makerId = String(order.makerProfileId || "");
  if (selfProfileId && makerId && makerId === String(selfProfileId)) {
    return { ok: false, reason: "self-order" };
  }

  // Skip own orders by username (public listing now exposes makerUsername)
  const makerUsername = normalizeOtcUsername(order.makerUsername);
  const ownUsernames = isObject(ctx) && ctx.ownUsernames instanceof Set ? ctx.ownUsernames : null;
  if (makerUsername && ownUsernames && ownUsernames.has(makerUsername)) {
    return { ok: false, reason: "self-username" };
  }

  // Per-counterparty take limit. Resets every Saturday 00:00 UTC (Sat 07:00 WIB),
  // aligned with Roots' rewards weekly snapshot to avoid the "repetitive_otc_swaps" penalty.
  const takerCfg = isObject(swapCfg.taker) ? swapCfg.taker : {};
  const maxPerCounterparty = Number(takerCfg.maxTakesPerCounterpartyPerWeek)
    || Number(takerCfg.maxTakesPerCounterpartyPerHour) || 0;
  if (makerUsername && maxPerCounterparty > 0) {
    const recent = pruneOtcCounterpartyHistory(makerUsername, nowMs);
    if (recent.length >= maxPerCounterparty) {
      const resetMs = getNextCounterpartyResetMs(nowMs);
      const hoursToReset = Math.max(0, (resetMs - nowMs) / 3_600_000);
      return {
        ok: false,
        reason: `counterparty-limit (${recent.length}/${maxPerCounterparty} from ${makerUsername}, resets in ${hoursToReset.toFixed(1)}h)`
      };
    }
  }

  // Skip reserved
  if (order.reservedByProfileId) {
    return { ok: false, reason: "reserved" };
  }

  // Status must be open / awaiting_taker
  if (order.status && order.status !== "open") {
    return { ok: false, reason: `status=${order.status}` };
  }

  // Expiry buffer
  const expiresAt = Date.parse(order.expiresAt || "");
  if (Number.isFinite(expiresAt)) {
    const bufferMs = (swapCfg.minExpiryBufferSeconds || 30) * 1000;
    if (expiresAt - nowMs < bufferMs) {
      return { ok: false, reason: "expiring-soon" };
    }
  }

  // Allowed pair filter (if configured)
  if (Array.isArray(swapCfg.allowedPairs) && swapCfg.allowedPairs.length > 0) {
    if (!swapCfg.allowedPairs.includes(String(order.pair || "").toLowerCase())) {
      return { ok: false, reason: "pair-not-allowed" };
    }
  }

  const edge = computeOtcOrderEdge(order, mids);
  if (!edge) return { ok: false, reason: "edge-uncomputable" };

  // Order size limits
  const maxUsd = Number(swapCfg.maxOrderSizeUsd) || 0;
  const minUsd = Number(swapCfg.minOrderSizeUsd) || 0;
  if (maxUsd > 0 && edge.takerPaysUsd > maxUsd) {
    return { ok: false, reason: `too-large (${edge.takerPaysUsd.toFixed(2)} > ${maxUsd})`, edge };
  }
  if (minUsd > 0 && edge.takerPaysUsd < minUsd) {
    return { ok: false, reason: `too-small (${edge.takerPaysUsd.toFixed(2)} < ${minUsd})`, edge };
  }

  // Min edge
  const minEdgeBps = Number(swapCfg.minEdgeBps);
  if (Number.isFinite(minEdgeBps) && edge.edgeBps < minEdgeBps) {
    return { ok: false, reason: `edge-too-low (${edge.edgeBps.toFixed(1)} < ${minEdgeBps})`, edge };
  }

  // Sufficient balance for what taker pays
  const accountBalance = otcGetAccountBalance(order.dstAsset, balanceData);
  const required = Number(order.dstAmountDecimal) || 0;
  if (accountBalance < required) {
    return { ok: false, reason: `insufficient-balance (${accountBalance} < ${required} ${order.dstAsset})`, edge };
  }

  return { ok: true, reason: "profitable", edge };
}

function pickBestOtcOrder(orders, mids, balanceData, selfProfileId, swapCfg, ctx) {
  if (!Array.isArray(orders) || orders.length === 0) return null;
  const nowMs = Date.now();
  const candidates = [];
  for (const order of orders) {
    const verdict = isOtcOrderProfitable(order, mids, balanceData, selfProfileId, swapCfg, nowMs, ctx);
    if (verdict.ok) {
      candidates.push({ order, edge: verdict.edge });
    }
  }
  if (candidates.length === 0) return null;
  // Sort by edgeBps descending, break ties by larger profitUsd
  candidates.sort((a, b) => {
    const dEdge = b.edge.edgeBps - a.edge.edgeBps;
    if (Math.abs(dEdge) > 0.01) return dEdge;
    return b.edge.estProfitUsd - a.edge.estProfitUsd;
  });
  return candidates[0];
}

function getSelfProfileIdFromBalance(balanceData) {
  if (!isObject(balanceData)) return null;
  const wallets = isObject(balanceData.wallets) ? balanceData.wallets : {};
  for (const w of Object.values(wallets)) {
    if (isObject(w) && w.profileId) return String(w.profileId);
  }
  return null;
}

// =============================================================================
// OTC Dashboard wrapper — match the Send-mode pinned dashboard UI for OTC flows
// =============================================================================

function attachOtcDashboard(context, modeLabel) {
  const config = context.config || {};
  const args = context.args || {};
  const accountList = (context.accounts && Array.isArray(context.accounts.accounts))
    ? context.accounts.accounts
    : [];
  const uiCfg = isObject(config.ui) ? config.ui : {};
  const swapCfg = isObject(config.swap) ? config.swap : {};

  const accountSnapshots = {};
  for (const acc of accountList) {
    accountSnapshots[acc.name] = { status: "QUEUE", cc: "-", usdc: "-", eth: "-", mk: 0, tk: 0, pts: "-", pen: 0 };
  }

  const dashboard = new PinnedDashboard({
    enabled:
      uiCfg.dashboard !== false &&
      !args.noDashboard &&
      process.env.ROOTSFI_NO_DASHBOARD !== "1",
    logLines: uiCfg.logLines,
    accountSnapshots
  });

  const accountsState = accountList
    .map((acc, idx) => `${idx === 0 ? "*" : ""}${acc.name}(QUEUE)`)
    .join(" | ");

  dashboard.setState({
    phase: "init",
    mode: String(modeLabel || "OTC").toUpperCase(),
    selectedAccount: accountList.length > 0
      ? `[1/${accountList.length}] ${accountList[0].name} (${maskEmail(accountList[0].email)})`
      : "-",
    accounts: accountsState,
    minDelay: clampToNonNegativeInt(swapCfg.minDelaySeconds, 5),
    maxDelay: clampToNonNegativeInt(swapCfg.maxDelaySeconds, 90)
  });
  dashboard.attach();
  setActiveDashboard(dashboard);
  return dashboard;
}

function updateOtcAccountSnapshot(dashboard, accountName, patch) {
  if (!dashboard || !accountName || !isObject(dashboard.accountSnapshots)) return;
  const prev = isObject(dashboard.accountSnapshots[accountName])
    ? dashboard.accountSnapshots[accountName]
    : {};
  dashboard.accountSnapshots[accountName] = { ...prev, ...patch };
  if (typeof dashboard._scheduleRender === "function") {
    dashboard._scheduleRender();
  }
}

function detachOtcDashboard(dashboard) {
  if (!dashboard) return;
  try { require("./web-bridge").detach(dashboard); } catch (_) { }
  try { if (typeof dashboard.detach === "function") dashboard.detach(); } catch (_) { }
  try { setActiveDashboard(null); } catch (_) { }
}

// Thin shim that delegates web dashboard snapshot logic to ./web-bridge.js.
// Keeps this file's footprint minimal so frequent `indexm.js` updates don't
// break the web dashboard, and vice versa.
function startOtcWebSnapshotLoop(dashboard, modeLabel, context) {
  if (!dashboard || !context) return;
  // Inject deps the bridge needs without exporting them publicly.
  context._counterpartyHistory = otcCounterpartyTakeHistory;
  try { require("./web-bridge").attach(dashboard, modeLabel, context); } catch (_) { }
}


async function refreshOtcAccountPoints(client, dashboard, accountName, tag) {
  try {
    const resp = await client.getAccountRewards();
    const data = isObject(resp && resp.data) ? resp.data : {};
    const totalPoints = Number(data.totalPoints);
    const penalties = Array.isArray(data.penalties) ? data.penalties : [];
    const totalPen = penalties.reduce((sum, p) => sum + (Number(p && p.penalty) || 0), 0);
    if (Number.isFinite(totalPoints)) {
      updateOtcAccountSnapshot(dashboard, accountName, { pts: totalPoints, pen: totalPen });
      const earned = Number(data.earnedPoints);
      console.log(`${tag} [pts] totalPoints=${totalPoints}${Number.isFinite(earned) ? ` earned=${earned}` : ""}${totalPen > 0 ? ` penalties=-${totalPen}` : ""}`);
    } else {
      // No totalPoints field — still update penalty snapshot if available
      updateOtcAccountSnapshot(dashboard, accountName, { pen: totalPen });
    }
  } catch (error) {
    // non-fatal — endpoint may 404 or rate-limit
  }
}

function formatOtcCcUsdc(balanceData) {
  const cc = otcGetAccountBalance("CC", balanceData);
  const usdc = otcGetAccountBalance("USDC", balanceData);
  const eth = otcGetAccountBalance("ETH", balanceData);
  const fmt = (n) => {
    const v = Number(n) || 0;
    if (v >= 1000) return v.toFixed(0);
    if (v >= 100) return v.toFixed(1);
    return v.toFixed(2);
  };
  const fmtEth = (n) => {
    const v = Number(n) || 0;
    if (v >= 1) return v.toFixed(3);
    if (v >= 0.001) return v.toFixed(4);
    if (v > 0) return v.toFixed(5);
    return "0";
  };
  return { cc: fmt(cc), usdc: fmt(usdc), eth: fmtEth(eth) };
}

async function runOtcAccountWorker(account, context, statsBucket) {
  const { config, tokens, accounts, dashboard } = context;
  const accountToken = tokens.accounts[account.name] || normalizeTokenProfile({});
  tokens.accounts[account.name] = accountToken;
  const accountConfig = cloneRuntimeConfig(config);
  applyTokenProfileToConfig(accountConfig, accountToken);
  const accountLogTag = `[${account.name}]`;
  const swapCfg = config.swap;
  const ownUsernames = new Set(
    (Array.isArray(accounts && accounts.accounts) ? accounts.accounts : [])
      .map((a) => normalizeOtcUsername(a && a.name))
      .filter(Boolean)
  );
  const pickerCtx = { ownUsernames };

  updateOtcAccountSnapshot(dashboard, account.name, { status: "SESS" });
  const client = new RootsFiApiClient(accountConfig);

  // Session reuse (OTC mode requires existing session; OTP login not handled here)
  if (!client.hasAccountSessionCookie()) {
    console.log(`${accountLogTag} [otc] No session cookie — run OTP mode first`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "NOSESS" });
    return { account: account.name, ok: false, error: "no-session" };
  }
  let sessionReuse = null;
  try {
    sessionReuse = await attemptSessionReuse(client, accountConfig, () => { }, accountLogTag);
  } catch (error) {
    console.log(`${accountLogTag} [otc] Session reuse threw: ${error.message}`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "ERR" });
    return { account: account.name, ok: false, error: error.message };
  }
  if (!sessionReuse || !sessionReuse.ok) {
    const reason = sessionReuse && sessionReuse.error ? sessionReuse.error.message : "unknown";
    console.log(`${accountLogTag} [otc] Session not reusable: ${reason}`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "ERR" });
    return { account: account.name, ok: false, error: "session-not-ok" };
  }

  let balanceData = sessionReuse.balancesData;
  const selfProfileId = getSelfProfileIdFromBalance(balanceData);
  const initBal = formatOtcCcUsdc(balanceData);
  updateOtcAccountSnapshot(dashboard, account.name, { status: "IDLE", cc: initBal.cc, usdc: initBal.usdc, eth: initBal.eth, mk: 0, tk: 0 });
  maybeRefillEth(account.name, balanceData);
  await refreshOtcAccountPoints(client, dashboard, account.name, accountLogTag);
  console.log(`${accountLogTag} [otc] Profile=${selfProfileId || "?"} — start scanning orders`);

  const maxLoop = Number(swapCfg.maxLoopTakes) || 100;
  const maxRuntimeMs = (Number(swapCfg.maxRuntimeMinutes) || 0) * 60 * 1000;
  const startMs = Date.now();
  let takesOk = 0;
  let takesFail = 0;
  let scans = 0;
  let takerBalanceLockUntil = 0;
  let localTakeCount = 0;
  const pointsRefreshEvery = 5; // refresh pts every N successful takes

  while (takesOk < maxLoop) {
    if (maxRuntimeMs > 0 && Date.now() - startMs > maxRuntimeMs) {
      console.log(`${accountLogTag} [otc] Max runtime reached, stop`);
      break;
    }

    // Honor balance-lock cooldown (server says pending sends/open swaps eat available balance)
    if (Date.now() < takerBalanceLockUntil) {
      const remainSec = Math.ceil((takerBalanceLockUntil - Date.now()) / 1000);
      if (scans % 5 === 0) {
        console.log(`${accountLogTag} [otc] Balance-lock cooldown ${remainSec}s (waiting for pending settlement)`);
      }
      updateOtcAccountSnapshot(dashboard, account.name, { status: "LOCK" });
      await sleep(Math.min(15000, remainSec * 1000));
      scans += 1;
      continue;
    }

    pruneOtcOrderBlacklist();
    scans += 1;

    // Rolling hourly swap cap
    const hourlySwapCap = Math.max(1, Number(swapCfg.hourlyMaxSwaps) || 5);
    const hrCnt = getOtcAccountSwapCount(account.name);
    const roundNumber = getOtcAccountSwapRound(account.name);
    const waitMs = getOtcAccountSwapResetMs(account.name);
    // Always update dashboard columns: sw, rnd, cd
    updateOtcAccountSnapshot(dashboard, account.name, {
      sw: `${hrCnt}/${hourlySwapCap}`,
      rnd: roundNumber,
      cd: waitMs > 0 ? `${Math.floor(waitMs / 60000)}m${Math.floor((waitMs % 60000) / 1000)}s` : "-"
    });
    const windowExpired = isOtcAccountSwapWindowExpired(account.name);

    if (hrCnt >= hourlySwapCap) {
      if (windowExpired || waitMs <= 0) {
        // Countdown habis + cap tercapai → round selesai! Naik ke round berikutnya.
        const completed = completeOtcAccountSwapRound(account.name);
        console.log(`${accountLogTag} [otc] ✓ Round ${roundNumber} complete (${hrCnt}/${hourlySwapCap}) → starting round ${completed.roundNumber}`);
        updateOtcAccountSnapshot(dashboard, account.name, {
          rnd: completed.roundNumber,
          sw: `0/${hourlySwapCap}`,
          cd: "-",
          status: "IDLE"
        });
        await sleep(5000);
        continue;
      }
      // Countdown masih jalan — tunggu.
      const waitSec = Math.ceil(waitMs / 1000);
      updateOtcAccountSnapshot(dashboard, account.name, { status: "CAP" });
      if (scans % 5 === 0) {
        console.log(`${accountLogTag} [otc] Round ${roundNumber} cap reached (${hrCnt}/${hourlySwapCap}) — cooldown ${Math.floor(waitMs / 60000)}m${Math.floor((waitMs % 60000) / 1000)}s`);
      }
      await sleep(Math.min(waitMs, 30000) || 15000);
      continue;
    }

    // Window expired tapi cap belum tercapai → reset window, tetap round sama.
    // PENTING: ini HARUS setelah cap check di atas.
    if (windowExpired && hrCnt < hourlySwapCap && hrCnt > 0) {
      console.log(`${accountLogTag} [otc] Window expired with ${hrCnt}/${hourlySwapCap} — resetting timer (still round ${roundNumber})`);
      resetOtcAccountSwapWindow(account.name);
      updateOtcAccountSnapshot(dashboard, account.name, {
        sw: `0/${hourlySwapCap}`,
        cd: "-"
      });
    }

    let orders = [];
    let mids = {};
    let oracleStaleSec = 0;
    try {
      const [ordersRes, refRes] = await Promise.all([
        client.getCrossOtcOrders(false),
        client.getCrossOtcReference()
      ]);
      orders = Array.isArray(ordersRes && ordersRes.data && ordersRes.data.orders)
        ? ordersRes.data.orders
        : (Array.isArray(ordersRes && ordersRes.data) ? ordersRes.data : []);
      const refData = isObject(refRes && refRes.data) ? refRes.data : {};
      mids = isObject(refData.mids) ? refData.mids : {};
      const capturedAtMs = Number(refData.capturedAtMs) || 0;
      if (capturedAtMs > 0) {
        oracleStaleSec = (Date.now() - capturedAtMs) / 1000;
      }
    } catch (error) {
      console.log(`${accountLogTag} [otc] Fetch failed: ${error.message}`);
      await sleep(15000);
      continue;
    }

    const minFresh = Number(swapCfg.minOracleFreshnessSeconds) || 30;
    if (oracleStaleSec > minFresh) {
      console.log(`${accountLogTag} [otc] Oracle stale (${oracleStaleSec.toFixed(1)}s), retry`);
      await sleep(5000);
      continue;
    }

    const takerCfg = isObject(swapCfg.taker) ? swapCfg.taker : {};
    const takerSwapCfg = { ...swapCfg, minEdgeBps: Number(takerCfg.minBps) ?? 25 };
    const blacklistTtlMs = (Number(takerCfg.orderBlacklistSeconds) || 60) * 1000;
    const maxDrainPerLoop = Math.max(1, clampToNonNegativeInt(takerCfg.maxDrainPerLoop, 10));

    // ═══════════════════════════════════════════════════
    // DRAIN — keep taking while balance allows.
    //   Counterparty per-hour limit + self-username skip are enforced
    //   inside isOtcOrderProfitable (preserved automatically).
    // ═══════════════════════════════════════════════════
    let drainCount = 0;
    let breakDrain = false;

    while (takesOk < maxLoop && drainCount < maxDrainPerLoop && !breakDrain) {
      const pick = pickBestOtcOrder(orders, mids, balanceData, selfProfileId, takerSwapCfg, pickerCtx);
      if (!pick) break;

      const { order, edge } = pick;
      updateOtcAccountSnapshot(dashboard, account.name, { status: "TAKE" });
      console.log(
        `${accountLogTag} [otc] PICK ${order.id.slice(0, 8)} ${order.side} ` +
        `pays=${order.dstAmountDecimal} ${order.dstAsset} recv=${order.srcAmountDecimal} ${order.srcAsset} ` +
        `edge=${edge.edgeBps.toFixed(1)}bps (~$${edge.estProfitUsd.toFixed(4)}) ` +
        `[drain ${drainCount + 1}/${maxDrainPerLoop}]`
      );

      // Reserve
      let reserveOk = false;
      try {
        await client.reserveOtcOrder(order.id);
        reserveOk = true;
      } catch (error) {
        const errMsg = String(error.message || "");
        if (isOtcOrderClosedError(errMsg)) {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${accountLogTag} [otc] Reserve race ${order.id.slice(0, 8)} (409) — blacklist, try next`);
        } else if (isOtcMakerSettlementInProgressError(errMsg)) {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${accountLogTag} [otc] Reserve skip ${order.id.slice(0, 8)} (maker settling) — blacklist, try next`);
        } else {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${accountLogTag} [otc] Reserve failed for ${order.id.slice(0, 8)}: ${errMsg}`);
        }
        takesFail += 1;
        statsBucket.reserveFail += 1;
      }

      if (!reserveOk) {
        drainCount++;
        continue;
      }

      // Take
      let takeOk = false;
      try {
        const takeResult = await client.takeOtcOrder(order.id);
        const filled = isObject(takeResult && takeResult.data && takeResult.data.order)
          ? takeResult.data.order
          : null;
        let status = String((filled && filled.status) || "").toLowerCase();
        const makerUsername = normalizeOtcUsername(order.makerUsername);

        // VERIFIKASI: kalau status belum terminal, poll sampai resolve sebelum
        // cek cap. Hindari race condition over-cap.
        const isImmediateTerminal = isOtcTerminalStatus(status);
        if (!isImmediateTerminal) {
          await sleep(1500);
          const verifyTimeoutMs = Math.max(5000, Number(takerCfg.takeVerifyTimeoutMs) || 20000);
          const resolution = await waitForOtcOrderResolution(client, order.id, { timeoutMs: verifyTimeoutMs, pollIntervalMs: 2000 });
          if (resolution.resolved && resolution.status && resolution.status !== "missing") {
            status = String(resolution.status).toLowerCase();
            console.log(`${accountLogTag} [otc] verify ${order.id.slice(0, 8)} → status=${status}`);
          } else {
            console.log(`${accountLogTag} [otc] verify ${order.id.slice(0, 8)} unresolved (last=${resolution.status || "?"}) — assume settled`);
            // Default: treat as filled untuk consistency dengan perilaku lama.
            status = "filled";
          }
        }

        const countsAsSwap = isOtcSwapCountedStatus(status); // filled atau failed
        const isCancelledLike = !countsAsSwap && (
          status === "cancelled" || status === "canceled" || status === "expired" || status === "rejected"
        );

        if (makerUsername) {
          recordOtcCounterpartyTake(makerUsername);
          const cnt = pruneOtcCounterpartyHistory(makerUsername, Date.now()).length;
          const limit = Number(takerCfg.maxTakesPerCounterpartyPerWeek)
            || Number(takerCfg.maxTakesPerCounterpartyPerHour) || 0;
          console.log(
            `${accountLogTag} [otc] TAKE ${countsAsSwap ? (status === "filled" ? "OK" : "FAIL") : (isCancelledLike ? "CXL" : "?")} ${order.id.slice(0, 8)} status=${status} ` +
            `maker=${order.makerUsername} (${cnt}${limit > 0 ? `/${limit}` : ""}/wk)`
          );
        } else {
          console.log(`${accountLogTag} [otc] TAKE ${countsAsSwap ? (status === "filled" ? "OK" : "FAIL") : (isCancelledLike ? "CXL" : "?")} ${order.id.slice(0, 8)} status=${status}`);
        }

        if (countsAsSwap) {
          if (status === "filled") {
            takesOk += 1;
            statsBucket.takeOk += 1;
            statsBucket.profitUsd += edge.estProfitUsd;
            statsBucket.volumeUsd += edge.takerPaysUsd;
            takeOk = true;
          } else {
            // failed
            statsBucket.takeFail += 1;
          }
          blacklistOtcOrder(order.id, blacklistTtlMs); // skip di cached `orders` array
          localTakeCount += 1;
          recordOtcAccountSwap(account.name);
          updateOtcAccountSnapshot(dashboard, account.name, { tk: takesOk });
          if (localTakeCount % pointsRefreshEvery === 0) {
            await refreshOtcAccountPoints(client, dashboard, account.name, accountLogTag);
          }
          if (getOtcAccountSwapCount(account.name) >= hourlySwapCap) {
            console.log(`${accountLogTag} [otc] hourly swap cap ${hourlySwapCap}/hr — end drain`);
            breakDrain = true;
          }
        } else {
          // Cancelled / canceled / expired / rejected — TIDAK dihitung swap.
          blacklistOtcOrder(order.id, blacklistTtlMs);
          statsBucket.takeFail += 1;
        }
      } catch (error) {
        const errMsg = String(error.message || "");
        if (isOtcOrderClosedError(errMsg)) {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${accountLogTag} [otc] Take race ${order.id.slice(0, 8)} (409) — blacklist, try next`);
        } else if (isOtcBalanceLockError(errMsg)) {
          const lockSec = Number(takerCfg.balanceLockCooldownSeconds) || 90;
          takerBalanceLockUntil = Date.now() + lockSec * 1000;
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${accountLogTag} [otc] Balance lock on take ${order.id.slice(0, 8)} — pause ${lockSec}s, end drain`);
          breakDrain = true;
        } else {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${accountLogTag} [otc] Take failed for ${order.id.slice(0, 8)}: ${errMsg}`);
        }
        takesFail += 1;
        statsBucket.takeFail += 1;
      }

      drainCount++;

      if (takeOk) {
        // Refresh balance immediately so next pick filters by post-take saldo
        try {
          const balResp = await client.getBalances();
          if (isObject(balResp && balResp.data)) {
            balanceData = balResp.data;
            const bal = formatOtcCcUsdc(balanceData);
            updateOtcAccountSnapshot(dashboard, account.name, { cc: bal.cc, usdc: bal.usdc, eth: bal.eth });
            maybeRefillEth(account.name, balanceData);
          }
        } catch (_) { }
      }
    }

    if (drainCount === 0) {
      // No profitable order — fast re-scan to honor "wajib ambil" rule on new orders
      const idleSec = Math.max(1, Number(takerCfg.fastScanIntervalSeconds) || 2);
      if (scans % 10 === 1) {
        console.log(`${accountLogTag} [otc] No profitable order (scanned ${orders.length}, fast-scan ${idleSec}s)`);
      }
      updateOtcAccountSnapshot(dashboard, account.name, { status: "IDLE" });
      await sleep(idleSec * 1000);
      continue;
    }

    if (drainCount > 1) {
      console.log(`${accountLogTag} [otc] drain complete: ${drainCount} attempts this loop`);
    }

    const cooldown = humanLikeDelay(
      clampToNonNegativeInt(swapCfg.minDelaySeconds, 30),
      clampToNonNegativeInt(swapCfg.maxDelaySeconds, 90)
    );
    updateOtcAccountSnapshot(dashboard, account.name, { status: "COOL" });
    console.log(`${accountLogTag} [otc] cooldown ${cooldown}s before next scan`);
    await sleep(cooldown * 1000);
  }

  updateOtcAccountSnapshot(dashboard, account.name, { status: "DONE" });
  return { account: account.name, ok: true, takesOk, takesFail, scans };
}

async function runOtcTradingFlow(context) {
  const { config, accounts, args } = context;
  const swapCfg = isObject(config.swap) ? config.swap : {};
  if (!swapCfg.enabled) {
    console.log("[otc] config.swap.enabled = false. Aktifkan dulu di config.json.");
    return;
  }

  const selectedAccounts = accounts.accounts;
  if (selectedAccounts.length === 0) {
    console.log("[otc] Tidak ada akun terpilih.");
    return;
  }

  const takerBpsBanner = isObject(swapCfg.taker) ? (Number(swapCfg.taker.minBps) || 25) : 25;
  const dashboard = attachOtcDashboard(context, "OTC-TAKER");
  context.dashboard = dashboard;

  console.log(`\n${"#".repeat(70)}`);
  console.log(`[otc] Taker-only OTC trading — take orders at ≥${takerBpsBanner}bps`);
  console.log(`[otc] Accounts=${selectedAccounts.length} | minEdge=${takerBpsBanner}bps | maxOrder=$${swapCfg.maxOrderSizeUsd}`);
  console.log(`[otc] Workers=${swapCfg.workers} | maxTakes/akun=${swapCfg.maxLoopTakes}`);
  console.log(`${"#".repeat(70)}\n`);

  const statsBucket = { takeOk: 0, takeFail: 0, reserveFail: 0, profitUsd: 0, volumeUsd: 0 };
  context.statsBucket = statsBucket;
  startOtcWebSnapshotLoop(dashboard, "OTC-TAKER", context);
  const workers = Math.max(1, Number(swapCfg.workers) || 5);

  // Run accounts in parallel batches
  const queue = [...selectedAccounts];
  const inFlight = [];
  const results = [];

  const launchNext = () => {
    while (inFlight.length < workers && queue.length > 0) {
      const acc = queue.shift();
      const p = runOtcAccountWorker(acc, context, statsBucket)
        .then((r) => { results.push(r); })
        .catch((err) => { results.push({ account: acc.name, ok: false, error: err.message }); })
        .finally(() => {
          const idx = inFlight.indexOf(p);
          if (idx >= 0) inFlight.splice(idx, 1);
        });
      inFlight.push(p);
    }
  };

  try {
    launchNext();
    while (inFlight.length > 0) {
      await Promise.race(inFlight);
      launchNext();
    }

    console.log(`\n${"#".repeat(70)}`);
    console.log(`[otc] Done — takes ok=${statsBucket.takeOk} fail=${statsBucket.takeFail} | volume=$${statsBucket.volumeUsd.toFixed(2)} | est profit=$${statsBucket.profitUsd.toFixed(4)}`);
    console.log(`${"#".repeat(70)}\n`);
  } finally {
    detachOtcDashboard(dashboard);
    context.dashboard = null;
  }
}

// =============================================================================
// OTC Maker Flow — create listings (sell CC for USDC)
// =============================================================================

async function runOtcMakerAccountWorker(account, context, statsBucket) {
  const { config, tokens, dashboard } = context;
  const accountToken = tokens.accounts[account.name] || normalizeTokenProfile({});
  tokens.accounts[account.name] = accountToken;
  const accountConfig = cloneRuntimeConfig(config);
  applyTokenProfileToConfig(accountConfig, accountToken);
  const tag = `[${account.name}]`;
  const swapCfg = isObject(config.swap) ? config.swap : {};
  const makerCfg = isObject(swapCfg.maker) ? swapCfg.maker : {};

  updateOtcAccountSnapshot(dashboard, account.name, { status: "SESS" });
  const client = new RootsFiApiClient(accountConfig);

  if (!client.hasAccountSessionCookie()) {
    console.log(`${tag} [maker] No session cookie — run OTP mode first`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "NOSESS" });
    return { account: account.name, ok: false, error: "no-session" };
  }

  let sessionReuse = null;
  try {
    sessionReuse = await attemptSessionReuse(client, accountConfig, () => { }, tag);
  } catch (error) {
    console.log(`${tag} [maker] Session reuse failed: ${error.message}`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "ERR" });
    return { account: account.name, ok: false, error: error.message };
  }
  if (!sessionReuse || !sessionReuse.ok) {
    console.log(`${tag} [maker] Session not reusable`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "ERR" });
    return { account: account.name, ok: false, error: "session-not-ok" };
  }

  let balanceData = sessionReuse.balancesData;
  const selfProfileId = getSelfProfileIdFromBalance(balanceData);
  const initBal = formatOtcCcUsdc(balanceData);
  updateOtcAccountSnapshot(dashboard, account.name, { status: "IDLE", cc: initBal.cc, usdc: initBal.usdc, eth: initBal.eth, mk: 0, tk: 0 });
  maybeRefillEth(account.name, balanceData);
  await refreshOtcAccountPoints(client, dashboard, account.name, tag);
  console.log(`${tag} [maker] Profile=${selfProfileId || "?"} — start creating listings`);

  const minBps = Number.isFinite(makerCfg.minBps) ? makerCfg.minBps : 10;
  const maxBps = Number.isFinite(makerCfg.maxBps) ? makerCfg.maxBps : 100;
  const expiresHours = Number(makerCfg.expiresHours) || 6;
  const maxOpenOrders = Number(makerCfg.maxOpenOrders) || 3;
  const rateLimitCooldownMs = (Number(makerCfg.rateLimitCooldownMinutes) || 60) * 60 * 1000;
  const maxLoop = Number(swapCfg.maxLoopTakes) || 100;
  let ordersCreated = 0;
  let makerCooldownUntil = 0; // timestamp when maker can resume
  let makerBalanceLockUntil = 0; // pause when create returns "balance below listed amount"

  for (let loop = 0; loop < maxLoop; loop++) {
    // Check if in maker cooldown (rate limited)
    if (Date.now() < makerCooldownUntil) {
      const remainMin = Math.ceil((makerCooldownUntil - Date.now()) / 60000);
      if (loop % 10 === 0) {
        console.log(`${tag} [maker] Rate limit cooldown — ${remainMin}min remaining`);
      }
      await sleep(30000);
      continue;
    }

    // Balance-lock cooldown — wait for pending settlement
    if (Date.now() < makerBalanceLockUntil) {
      const remainSec = Math.ceil((makerBalanceLockUntil - Date.now()) / 1000);
      if (loop % 5 === 0) {
        console.log(`${tag} [maker] Balance-lock cooldown ${remainSec}s (waiting settlement)`);
      }
      updateOtcAccountSnapshot(dashboard, account.name, { status: "LOCK" });
      await sleep(Math.min(15000, remainSec * 1000));
      continue;
    }

    // Check how many open orders we have
    let myOrders = [];
    let mids = {};
    try {
      const [ordersRes, mineRes, refRes] = await Promise.all([
        client.getCrossOtcOrders(false),
        client.getCrossOtcOrders(true),
        client.getCrossOtcReference()
      ]);
      myOrders = Array.isArray(mineRes && mineRes.data && mineRes.data.orders)
        ? mineRes.data.orders
        : (Array.isArray(mineRes && mineRes.data) ? mineRes.data : []);
      const refData = isObject(refRes && refRes.data) ? refRes.data : {};
      mids = isObject(refData.mids) ? refData.mids : {};
    } catch (error) {
      console.log(`${tag} [maker] Fetch failed: ${error.message}`);
      await sleep(15000);
      continue;
    }

    // Count open orders and calculate locked balance per asset
    let openOrders = myOrders.filter(o => o.status === "open");

    // Cancel listings that have been waiting for taker too long
    {
      const nowMs = Date.now();
      const cancelAfterIdleMs = Math.max(60_000, (Number(makerCfg.cancelAfterIdleMinutes) || 5) * 60_000);
      const survivors = [];
      for (const myOrder of openOrders) {
        if (myOrder.reservedByProfileId) {
          // Currently reserved — let settlement proceed
          survivors.push(myOrder);
          continue;
        }
        const createdMs = Date.parse(myOrder.createdAt || "");
        if (!Number.isFinite(createdMs)) {
          survivors.push(myOrder);
          continue;
        }
        const elapsedMs = nowMs - createdMs;
        if (elapsedMs >= cancelAfterIdleMs) {
          try {
            await client.cancelOtcOrder(myOrder.id);
            console.log(`${tag} [maker] Cancelled ${myOrder.id.slice(0, 8)} (idle ${(elapsedMs / 60000).toFixed(1)}min ≥ ${(cancelAfterIdleMs / 60000).toFixed(0)}min threshold)`);
            statsBucket.ordersCancelled = (statsBucket.ordersCancelled || 0) + 1;
            continue; // exclude from survivors
          } catch (_) {
            survivors.push(myOrder); // failed to cancel — keep
          }
        } else {
          survivors.push(myOrder);
        }
      }
      openOrders = survivors;
    }

    let lockedCc = 0;
    let lockedUsdc = 0;
    for (const o of openOrders) {
      const src = Number(o.srcAmountDecimal) || 0;
      const srcAsset = String(o.srcAsset || "").toUpperCase();
      if (srcAsset === "CC") lockedCc += src;
      else if (srcAsset === "USDC") lockedUsdc += src;
    }

    if (openOrders.length >= maxOpenOrders) {
      const idleSec = humanLikeDelay(
        clampToNonNegativeInt(swapCfg.minDelaySeconds, 30),
        clampToNonNegativeInt(swapCfg.maxDelaySeconds, 90)
      );
      if (loop % 3 === 0) {
        console.log(`${tag} [maker] ${openOrders.length}/${maxOpenOrders} open (locked CC=${lockedCc.toFixed(2)} USDC=${lockedUsdc.toFixed(2)}), wait ${idleSec}s`);
      }
      await sleep(idleSec * 1000);
      continue;
    }

    // Available = total balance - locked in open orders
    const ccBalance = otcGetAccountBalance("CC", balanceData);
    const usdcBalance = otcGetAccountBalance("USDC", balanceData);
    const availCc = Math.max(0, ccBalance - lockedCc);
    const availUsdc = Math.max(0, usdcBalance - lockedUsdc);
    const minUsd = Number(swapCfg.minOrderSizeUsd) || 1.05;
    const maxUsd = Number(swapCfg.maxOrderSizeUsd) || 10;
    const ccPriceUsd = Number(mids.cc_usdcx) || Number(mids.usdc_cc) || 0;

    if (ccPriceUsd <= 0) {
      console.log(`${tag} [maker] No price data, retry in 10s`);
      await sleep(10000);
      continue;
    }

    // Check if available balance meets minimum order size
    const availCcValueUsd = availCc * ccPriceUsd;
    const canSellCc = availCcValueUsd >= minUsd;
    const canSellUsdc = availUsdc >= minUsd;

    if (!canSellCc && !canSellUsdc) {
      console.log(
        `${tag} [maker] Low available: CC=${availCc.toFixed(2)}/${ccBalance.toFixed(2)} ($${availCcValueUsd.toFixed(2)}) ` +
        `USDC=${availUsdc.toFixed(2)}/${usdcBalance.toFixed(2)} — need >$${minUsd}`
      );
      const waitSec = humanLikeDelay(60, 120);
      await sleep(waitSec * 1000);
      continue;
    }

    // Pick direction: weighted random towards asset with more available value
    let sellDirection;
    if (canSellCc && canSellUsdc) {
      const ccWeight = availCcValueUsd / (availCcValueUsd + availUsdc);
      sellDirection = Math.random() < ccWeight ? "cc" : "usdc";
    } else {
      sellDirection = canSellCc ? "cc" : "usdc";
    }

    // Random edge between minBps and maxBps
    const edgeBps = minBps + Math.random() * (maxBps - minBps);
    const edgeFactor = 1 - edgeBps / 10000;

    let side, srcAmount, dstAmount, srcLabel, dstLabel;

    if (sellDirection === "cc") {
      // Sell CC → Get USDC
      const maxCcForOrder = Math.min(availCc, maxUsd / ccPriceUsd);
      const minCcForOrder = minUsd / ccPriceUsd;
      const actualCc = Number((minCcForOrder + Math.random() * Math.max(0, maxCcForOrder - minCcForOrder)).toFixed(6));
      const askUsdc = Number((actualCc * ccPriceUsd * edgeFactor).toFixed(6));

      side = "canton_sell_cc_for_usdc";
      srcAmount = actualCc.toFixed(9).replace(/\.?0+$/, "");
      dstAmount = askUsdc.toFixed(6).replace(/\.?0+$/, "");
      srcLabel = `${actualCc.toFixed(4)} CC`;
      dstLabel = `${askUsdc.toFixed(6)} USDC`;
    } else {
      // Sell USDC → Get CC
      const maxUsdcForOrder = Math.min(availUsdc, maxUsd);
      const minUsdcForOrder = minUsd;
      const actualUsdc = Number((minUsdcForOrder + Math.random() * Math.max(0, maxUsdcForOrder - minUsdcForOrder)).toFixed(6));
      const askCc = Number((actualUsdc / ccPriceUsd * edgeFactor).toFixed(6));

      side = "eth_sell_usdc_for_cc";
      srcAmount = actualUsdc.toFixed(6).replace(/\.?0+$/, "");
      dstAmount = askCc.toFixed(9).replace(/\.?0+$/, "");
      srcLabel = `${actualUsdc.toFixed(4)} USDC`;
      dstLabel = `${askCc.toFixed(4)} CC`;
    }

    updateOtcAccountSnapshot(dashboard, account.name, { status: "MAKE" });
    console.log(`${tag} [maker] Creating: sell ${srcLabel} → ${dstLabel} (edge=${edgeBps.toFixed(0)}bps) [${openOrders.length + 1}/${maxOpenOrders}]`);

    try {
      const result = await client.createOtcOrder({
        side,
        srcAmountDecimal: srcAmount,
        dstAmountDecimal: dstAmount,
        expiresHours
      });
      const order = isObject(result && result.data && result.data.order) ? result.data.order : {};
      console.log(`${tag} [maker] Order ${(order.id || "?").slice(0, 8)} status=${order.status || "?"}`);
      ordersCreated++;
      statsBucket.ordersCreated = (statsBucket.ordersCreated || 0) + 1;
      updateOtcAccountSnapshot(dashboard, account.name, { mk: ordersCreated });
    } catch (error) {
      const errMsg = String(error.message || "");
      if (errMsg.includes("429") || errMsg.toLowerCase().includes("too many")) {
        const cooldownMin = Math.ceil(rateLimitCooldownMs / 60000);
        makerCooldownUntil = Date.now() + rateLimitCooldownMs;
        console.log(`${tag} [maker] Rate limited! Cooling down for ${cooldownMin}min`);
        statsBucket.rateLimits = (statsBucket.rateLimits || 0) + 1;
        continue;
      }
      if (isOtcBalanceLockError(errMsg)) {
        const lockSec = Number(makerCfg.balanceLockCooldownSeconds) || 120;
        makerBalanceLockUntil = Date.now() + lockSec * 1000;
        console.log(`${tag} [maker] Balance lock on create — pause maker ${lockSec}s for settlement`);
        statsBucket.balanceLocks = (statsBucket.balanceLocks || 0) + 1;
        continue;
      }
      console.log(`${tag} [maker] Create failed: ${errMsg}`);
      statsBucket.ordersFail = (statsBucket.ordersFail || 0) + 1;
    }

    // Refresh balance
    try {
      const balResp = await client.getBalances();
      if (isObject(balResp && balResp.data)) {
        balanceData = balResp.data;
        const bal = formatOtcCcUsdc(balanceData);
        updateOtcAccountSnapshot(dashboard, account.name, { cc: bal.cc, usdc: bal.usdc, eth: bal.eth });
        maybeRefillEth(account.name, balanceData);
      }
    } catch (_) { }

    const cooldown = humanLikeDelay(
      clampToNonNegativeInt(swapCfg.minDelaySeconds, 30),
      clampToNonNegativeInt(swapCfg.maxDelaySeconds, 90)
    );
    updateOtcAccountSnapshot(dashboard, account.name, { status: "COOL" });
    console.log(`${tag} [maker] cooldown ${cooldown}s`);
    await sleep(cooldown * 1000);
  }

  updateOtcAccountSnapshot(dashboard, account.name, { status: "DONE" });
  return { account: account.name, ok: true, ordersCreated };
}

async function runOtcMakerFlow(context) {
  const { config, accounts } = context;
  const swapCfg = isObject(config.swap) ? config.swap : {};
  if (!swapCfg.enabled) {
    console.log("[otc-maker] config.swap.enabled = false. Aktifkan dulu.");
    return;
  }

  const selectedAccounts = accounts.accounts;
  if (selectedAccounts.length === 0) {
    console.log("[otc-maker] Tidak ada akun terpilih.");
    return;
  }

  const makerCfg = isObject(swapCfg.maker) ? swapCfg.maker : {};
  const dashboard = attachOtcDashboard(context, "OTC-MAKER");
  context.dashboard = dashboard;

  console.log(`\n${"#".repeat(70)}`);
  console.log(`[otc-maker] Maker mode — create CC↔USDC listings (bidirectional)`);
  console.log(`[otc-maker] Accounts=${selectedAccounts.length} | BPS=${makerCfg.minBps}-${makerCfg.maxBps} | expires=${makerCfg.expiresHours || 6}h | maxOpen=${makerCfg.maxOpenOrders}/akun`);
  console.log(`${"#".repeat(70)}\n`);

  const statsBucket = { ordersCreated: 0, ordersFail: 0 };
  context.statsBucket = statsBucket;
  startOtcWebSnapshotLoop(dashboard, "OTC-MAKER", context);
  const workers = Math.max(1, Number(swapCfg.workers) || 5);
  const queue = [...selectedAccounts];
  const inFlight = [];
  const results = [];

  const launchNext = () => {
    while (inFlight.length < workers && queue.length > 0) {
      const acc = queue.shift();
      const p = runOtcMakerAccountWorker(acc, context, statsBucket)
        .then((r) => { results.push(r); })
        .catch((err) => { results.push({ account: acc.name, ok: false, error: err.message }); })
        .finally(() => {
          const idx = inFlight.indexOf(p);
          if (idx >= 0) inFlight.splice(idx, 1);
        });
      inFlight.push(p);
    }
  };

  try {
    launchNext();
    while (inFlight.length > 0) {
      await Promise.race(inFlight);
      launchNext();
    }
    console.log(`\n${"#".repeat(70)}`);
    console.log(`[otc-maker] Done — created=${statsBucket.ordersCreated} fail=${statsBucket.ordersFail}`);
    console.log(`${"#".repeat(70)}\n`);
  } finally {
    detachOtcDashboard(dashboard);
    context.dashboard = null;
  }
}

// =============================================================================
// OTC Maker-Taker Flow — "Taker First, Maker Fill" strategy
//
// STRATEGY: The optimal Maker-Taker approach for 26 accounts:
//
// 1. TAKER FIRST: Every loop, scan for external orders at ≥25bps edge.
//    Taking = instant volume, highest priority. If found, take immediately.
//
// 2. MAKER FILL: If no take opportunity, create a listing from whatever
//    asset the account holds (CC→USDC or USDC→CC). Bidirectional flow
//    creates a natural "market maker" pattern across accounts.
//
// 3. STALE CLEANUP: Cancel own orders that sat untaken past 50% of expiry.
//    This frees locked balance for new listings at fresher prices.
//
// 4. CROSS-ACCOUNT SYNERGY: Account A lists sell CC→USDC,
//    Account B (with USDC) can take it externally if edge is ≥25bps.
//    CC flows A→B via OTC, USDC flows B→A. Volume for both.
//
// This creates maximum activity with minimum capital waste.
// =============================================================================

async function runOtcMakerTakerAccountWorker(account, context, statsBucket) {
  const { config, tokens, accounts, dashboard } = context;
  const accountToken = tokens.accounts[account.name] || normalizeTokenProfile({});
  tokens.accounts[account.name] = accountToken;
  const accountConfig = cloneRuntimeConfig(config);
  applyTokenProfileToConfig(accountConfig, accountToken);
  const tag = `[${account.name}]`;
  const swapCfg = isObject(config.swap) ? config.swap : {};
  const makerCfg = isObject(swapCfg.maker) ? swapCfg.maker : {};
  const takerCfg = isObject(swapCfg.taker) ? swapCfg.taker : {};
  const ownUsernames = new Set(
    (Array.isArray(accounts && accounts.accounts) ? accounts.accounts : [])
      .map((a) => normalizeOtcUsername(a && a.name))
      .filter(Boolean)
  );
  const pickerCtx = { ownUsernames };
  updateOtcAccountSnapshot(dashboard, account.name, { status: "SESS" });

  const client = new RootsFiApiClient(accountConfig);

  if (!client.hasAccountSessionCookie()) {
    console.log(`${tag} [mt] No session cookie — run OTP mode first`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "NOSESS" });
    return { account: account.name, ok: false, error: "no-session" };
  }

  let sessionReuse = null;
  try {
    sessionReuse = await attemptSessionReuse(client, accountConfig, () => { }, tag);
  } catch (error) {
    console.log(`${tag} [mt] Session reuse failed: ${error.message}`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "ERR" });
    return { account: account.name, ok: false, error: error.message };
  }
  if (!sessionReuse || !sessionReuse.ok) {
    console.log(`${tag} [mt] Session not reusable`);
    updateOtcAccountSnapshot(dashboard, account.name, { status: "ERR" });
    return { account: account.name, ok: false, error: "session-not-ok" };
  }

  let balanceData = sessionReuse.balancesData;
  const selfProfileId = getSelfProfileIdFromBalance(balanceData);
  const initBal = formatOtcCcUsdc(balanceData);
  updateOtcAccountSnapshot(dashboard, account.name, { status: "IDLE", cc: initBal.cc, usdc: initBal.usdc, eth: initBal.eth, mk: 0, tk: 0 });
  maybeRefillEth(account.name, balanceData);
  await refreshOtcAccountPoints(client, dashboard, account.name, tag);
  console.log(`${tag} [mt] Profile=${selfProfileId || "?"} — start (Maker→429→Taker cycle)`);

  const minBps = Number.isFinite(makerCfg.minBps) ? makerCfg.minBps : 10;
  const maxBps = Number.isFinite(makerCfg.maxBps) ? makerCfg.maxBps : 100;
  const expiresHours = Number(makerCfg.expiresHours) || 6;
  const maxOpenOrders = Number(makerCfg.maxOpenOrders) || 3;
  const rateLimitCooldownMs = (Number(makerCfg.rateLimitCooldownMinutes) || 60) * 60 * 1000;
  const takerMinBps = Number.isFinite(takerCfg.minBps) ? takerCfg.minBps : 25;
  const idleThresholdMs = Math.max(1, Number(makerCfg.takerIdleSecondsBeforeMaker) || 10) * 1000;
  const maxLoop = Number(swapCfg.maxLoopTakes) || 100;
  let takesOk = 0;       // taker swaps sukses (langsung settled + pending→filled)
  let makerFillsOk = 0;  // maker fills sukses (bukan creates)
  let ordersCreated = 0;  // maker orders created (untuk stats saja)
  let ordersCancelled = 0;
  let makerCooldownUntil = 0; // when 429 hit, maker pauses but taker continues
  let makerBalanceLockUntil = 0; // when create returns "balance below listed amount" — wait pending settlement
  let takerBalanceLockUntil = 0; // when take returns "balance below required amount"
  let lastProfitableHitAt = Date.now(); // updated when scan finds a takeable order
  let mtActivityCount = 0;
  const mtPointsRefreshEvery = 5;

  // Hourly swap cap. Timer 60min dimulai saat swap pertama (record).
  const hourlySwapCap = Math.max(1, Number(swapCfg.hourlyMaxSwaps) || 5);
  // Reset window untuk akun ini — semua data start dari nol.
  otcAccountSwapWindow.delete(account.name);
  // Track take IDs yang SUDAH di-record swap-nya agar tidak double-count.
  const recordedSwapTakeIds = new Set();
  // Track maker fill IDs yang SUDAH di-record swap-nya agar tidak double-count.
  const recordedMakerFillIds = new Set();
  // Persistent in-flight take tracker: ID order yang sudah kita take tapi
  // belum terkonfirmasi resolve di server. Drop saat order muncul sebagai
  // filled/failed/expired/cancelled di /orders endpoint.
  const inFlightTakeIds = new Set();
  // Persistent in-flight maker tracker: ID listing yang baru kita create.
  // Drop saat status final di server.
  const inFlightMakerIds = new Set();
  // Listings we are watching for a settlement signal. We add an ID to this
  // set when we observe it reserved. When it disappears from myOrders we
  // count it once (if not self-cancelled) and remove it from the set.
  const watchedReservedIds = new Set();
  // Skip maker-fill detection until we've established a baseline (otherwise
  // pre-existing reserved listings from a prior run inflate the counter).
  let makerFillBaselineSet = false;
  // IDs we cancelled ourselves — never count those as maker fills.
  const selfCancelledIds = new Set();

  // Cancel-all on start: bersihkan listing apapun dari run sebelumnya supaya
  // baseline maker-fill detection bersih.
  try {
    const mineRes = await client.getCrossOtcOrders(true);
    const startMyOrders = Array.isArray(mineRes && mineRes.data && mineRes.data.orders)
      ? mineRes.data.orders
      : (Array.isArray(mineRes && mineRes.data) ? mineRes.data : []);
    const toCancel = startMyOrders.filter(o => o.status === "open" && !o.reservedByProfileId);
    if (toCancel.length > 0) {
      console.log(`${tag} [mt] start: cancelling ${toCancel.length} pre-existing open listing(s)`);
      for (const o of toCancel) {
        try {
          await client.cancelOtcOrder(o.id);
          selfCancelledIds.add(String(o.id));
        } catch (err) {
          console.log(`${tag} [mt] start-cancel ${o.id.slice(0, 8)} failed: ${err.message}`);
        }
      }
    }
    // Listing reserved saat start = bukan tanggung jawab bot ini.
    // Treat them as already-cancelled-by-self supaya tidak ke-record kalau
    // settled di iterasi berikut.
    for (const o of startMyOrders) {
      if (o.reservedByProfileId) selfCancelledIds.add(String(o.id));
    }
    // Pre-populate recorded IDs: semua order filled/failed saat start BUKAN dari bot ini.
    // Jangan hitung sebagai swap baru.
    for (const o of startMyOrders) {
      const st = String(o.status || "").toLowerCase();
      if (isOtcSwapCountedStatus(st)) {
        const id = String(o.id || "");
        if (o.isMaker) recordedMakerFillIds.add(id);
        else recordedSwapTakeIds.add(id);
      }
    }
    // Counting 100% lokal — mulai dari 0.
    // Server history TIDAK dipakai untuk count agar predictable.
    const preFilledCount = recordedMakerFillIds.size + recordedSwapTakeIds.size;
    console.log(`${tag} [mt] start: clean state — swap 0/${hourlySwapCap}, round 1 (${preFilledCount} pre-existing fills excluded)`);
    makerFillBaselineSet = true;
  } catch (err) {
    console.log(`${tag} [mt] start-fetch myOrders failed: ${err.message}`);
  }

  for (let loop = 0; loop < maxLoop; loop++) {
    pruneOtcOrderBlacklist();
    let orders = [];
    let myOrders = [];
    let mids = {};
    try {
      const [allRes, mineRes, refRes] = await Promise.all([
        client.getCrossOtcOrders(false),
        client.getCrossOtcOrders(true),
        client.getCrossOtcReference()
      ]);
      orders = Array.isArray(allRes && allRes.data && allRes.data.orders)
        ? allRes.data.orders
        : (Array.isArray(allRes && allRes.data) ? allRes.data : []);
      myOrders = Array.isArray(mineRes && mineRes.data && mineRes.data.orders)
        ? mineRes.data.orders
        : (Array.isArray(mineRes && mineRes.data) ? mineRes.data : []);
      const refData = isObject(refRes && refRes.data) ? refRes.data : {};
      mids = isObject(refData.mids) ? refData.mids : {};
    } catch (error) {
      console.log(`${tag} [mt] Fetch failed: ${error.message}`);
      await sleep(15000);
      continue;
    }

    const ccPriceUsd = Number(mids.cc_usdcx) || Number(mids.usdc_cc) || 0;
    if (ccPriceUsd <= 0) {
      console.log(`${tag} [mt] No price data, retry in 10s`);
      await sleep(10000);
      continue;
    }

    // Update dashboard dari local count (100% lokal, tidak ada server sync).
    {
      const localCount = getOtcAccountSwapCount(account.name);
      const roundNumber = getOtcAccountSwapRound(account.name);
      updateOtcAccountSnapshot(dashboard, account.name, { sw: `${localCount}/${hourlySwapCap}` });
    }

    // Prune in-flight trackers: kalau ID-nya muncul di myOrders dengan status
    // final (filled/failed/expired/cancelled), atau hilang sama sekali dari
    // orderbook publik (taker side), drop dari tracker.
    let swapJustRecordedInPrune = false;
    {
      const myOrderById = new Map(myOrders.map(o => [String(o.id), o]));
      const publicOrderIds = new Set(orders.map(o => String(o.id)));
      for (const id of Array.from(inFlightTakeIds)) {
        const o = myOrderById.get(id);
        if (o) {
          const st = String(o.status || "").toLowerCase();
          if (isOtcTerminalStatus(st)) {
            inFlightTakeIds.delete(id);
            // Hitung sebagai swap kalau status = filled ATAU failed.
            // Cancelled / canceled / expired / rejected TIDAK dihitung.
            if (isOtcSwapCountedStatus(st) && !recordedSwapTakeIds.has(id)) {
              recordOtcAccountSwap(account.name);
              recordedSwapTakeIds.add(id);
              if (st === "filled") takesOk++;
              updateOtcAccountSnapshot(dashboard, account.name, { tk: takesOk });
              const lc = getOtcAccountSwapCount(account.name);
              const stLabel = st === "filled" ? "FILLED" : "FAILED";
              console.log(`${tag} [mt] take ${id.slice(0, 8)} ${stLabel} → swap ${lc}/${hourlySwapCap}`);
              swapJustRecordedInPrune = true;
            } else {
              console.log(`${tag} [mt] take ${id.slice(0, 8)} resolved (status=${st}, not counted)`);
            }
          }
        } else if (!publicOrderIds.has(id)) {
          // Hilang dari publik & tidak ada di mine — biarkan, masih unresolved
        }
      }
      for (const id of Array.from(inFlightMakerIds)) {
        const o = myOrderById.get(id);
        if (!o) {
          // Listing hilang dari mine — clean up tracking.
          inFlightMakerIds.delete(id);
          continue;
        }
        const st = String(o.status || "").toLowerCase();
        if (st === "filled" || st === "failed" || st === "expired" || st === "cancelled" || st === "canceled") {
          inFlightMakerIds.delete(id);
        }
      }
    }

    // ═══════════════════════════════════════════════════════════════
    // MAKER FILL SCAN — sumber satu-satunya untuk record swap maker.
    // Scan SEMUA myOrders setiap iterasi. Kalau ada order kita yang:
    //   - status = "filled" ATAU "failed" DAN isMaker = true
    //   - belum pernah di-record (tidak ada di recordedMakerFillIds)
    //   - bukan self-cancelled
    // → recordOtcAccountSwap() langsung.
    // Cancelled/canceled/expired TIDAK dihitung.
    // ═══════════════════════════════════════════════════════════════
    if (makerFillBaselineSet) {
      for (const o of myOrders) {
        const id = String(o.id || "");
        if (!id) continue;
        const st = String(o.status || "").toLowerCase();
        if (!isOtcSwapCountedStatus(st)) continue;
        if (!o.isMaker) continue;
        if (recordedMakerFillIds.has(id)) continue;
        if (selfCancelledIds.has(id)) {
          selfCancelledIds.delete(id);
          recordedMakerFillIds.add(id); // mark agar tidak cek ulang
          continue;
        }
        // ✓ Maker fill/failed baru terdeteksi → record swap lokal.
        recordOtcAccountSwap(account.name);
        recordedMakerFillIds.add(id);
        watchedReservedIds.delete(id);
        if (st === "filled") makerFillsOk++;
        updateOtcAccountSnapshot(dashboard, account.name, { mk: makerFillsOk });
        const localCount = getOtcAccountSwapCount(account.name);
        const stLabel = st === "filled" ? "FILLED" : "FAILED";
        console.log(`${tag} [maker-scan] ${id.slice(0, 8)} ${stLabel} → swap ${localCount}/${hourlySwapCap}`);
        swapJustRecordedInPrune = true;
      }
      // Track settling orders (untuk serial gate display saja).
      watchedReservedIds.clear();
      for (const o of myOrders) {
        if (o.status === "open" && o.reservedByProfileId) {
          watchedReservedIds.add(String(o.id));
        }
      }
    }

    // Cooldown setelah swap baru terdeteksi di prune/scan.
    // Tunggu 10 detik agar counting settle sebelum open posisi baru.
    if (swapJustRecordedInPrune) {
      const lc = getOtcAccountSwapCount(account.name);
      updateOtcAccountSnapshot(dashboard, account.name, {
        sw: `${lc}/${hourlySwapCap}`,
        status: "COOL"
      });
      console.log(`${tag} [mt] Swap recorded in prune — cooling 10s before next action (${lc}/${hourlySwapCap})`);
      makerFillBaselineSet = true;
      await sleep(10000);
      continue;
    }


    let pendingTakerReserves = 0;
    const getCommitment = () => {
      const done = getOtcAccountSwapCount(account.name);
      return { done, slotsLeft: Math.max(0, hourlySwapCap - done) };
    };

    // Round N: kumpulkan 5 swap sukses. Countdown 60min dimulai dari swap pertama.
    // Saat cap (5/5) DAN countdown expired → round naik, sw reset ke 0.
    const swapCountNow = getOtcAccountSwapCount(account.name);
    const waitMs = getOtcAccountSwapResetMs(account.name);
    const windowExpired = isOtcAccountSwapWindowExpired(account.name);
    const roundNumber = getOtcAccountSwapRound(account.name);
    updateOtcAccountSnapshot(dashboard, account.name, { rnd: roundNumber });

    // Helper: cek listing kita yang sedang settling (open + reservedByProfileId).
    const getSettlingListings = () => myOrders.filter(o =>
      o.status === "open" && o.reservedByProfileId && o.isMaker
    );

    // Format countdown untuk dashboard cd column — selalu update setiap iterasi.
    const cdDisplay = waitMs > 0
      ? `${Math.floor(waitMs / 60000)}m${Math.floor((waitMs % 60000) / 1000)}s`
      : "-";
    updateOtcAccountSnapshot(dashboard, account.name, { cd: cdDisplay });

    if (swapCountNow >= hourlySwapCap) {
      const settling = getSettlingListings();

      // Kalau masih ada listing settling, JANGAN declare round done dulu.
      if (settling.length > 0) {
        updateOtcAccountSnapshot(dashboard, account.name, { status: "STL", rnd: roundNumber });
        if (loop % 5 === 0) {
          const ids = settling.map(o => o.id.slice(0, 8)).join(",");
          console.log(`${tag} [mt] Cap reached (${swapCountNow}/${hourlySwapCap}) but ${settling.length} listing(s) settling: ${ids}`);
        }
        const openToCancel = myOrders.filter(o => o.status === "open" && !o.reservedByProfileId);
        for (const myOrder of openToCancel) {
          try {
            await client.cancelOtcOrder(myOrder.id);
            selfCancelledIds.add(String(myOrder.id));
            inFlightMakerIds.delete(String(myOrder.id));
            statsBucket.ordersCancelled = (statsBucket.ordersCancelled || 0) + 1;
          } catch (_) { }
        }
        makerFillBaselineSet = true;
        await sleep(10000);
        continue;
      }

      // Cap reached + no settling.
      if (windowExpired || waitMs <= 0) {
        // Countdown habis → round selesai! Naik ke round berikutnya.
        const completed = completeOtcAccountSwapRound(account.name);
        console.log(`${tag} [mt] ✓ Round ${roundNumber} complete (${swapCountNow}/${hourlySwapCap}) → starting round ${completed.roundNumber}`);
        updateOtcAccountSnapshot(dashboard, account.name, {
          rnd: completed.roundNumber,
          sw: `0/${hourlySwapCap}`,
          cd: "-",
          status: "IDLE"
        });
        // Cancel open orders sebelum mulai round baru
        const openToCancel = myOrders.filter(o => o.status === "open" && !o.reservedByProfileId);
        for (const myOrder of openToCancel) {
          try {
            await client.cancelOtcOrder(myOrder.id);
            selfCancelledIds.add(String(myOrder.id));
            inFlightMakerIds.delete(String(myOrder.id));
            statsBucket.ordersCancelled = (statsBucket.ordersCancelled || 0) + 1;
          } catch (_) { }
        }
        makerFillBaselineSet = true;
        await sleep(5000);
        continue;
      }

      // Countdown masih jalan — tunggu.
      updateOtcAccountSnapshot(dashboard, account.name, { status: "CAP", rnd: roundNumber });
      const waitMin = Math.floor(waitMs / 60000);
      const waitSec = Math.floor((waitMs % 60000) / 1000);
      if (loop % 5 === 0) {
        console.log(`${tag} [mt] Round ${roundNumber} done (${swapCountNow}/${hourlySwapCap}) — cooldown ${waitMin}m${waitSec}s`);
      }
      // Cancel open orders saat menunggu cooldown
      const openToCancel = myOrders.filter(o => o.status === "open" && !o.reservedByProfileId);
      for (const myOrder of openToCancel) {
        try {
          await client.cancelOtcOrder(myOrder.id);
          selfCancelledIds.add(String(myOrder.id));
          inFlightMakerIds.delete(String(myOrder.id));
          statsBucket.ordersCancelled = (statsBucket.ordersCancelled || 0) + 1;
        } catch (_) { }
      }
      makerFillBaselineSet = true;
      await sleep(Math.min(waitMs, 30000));
      continue;
    }

    // Window expired tapi cap belum tercapai → reset window, tetap round sama.
    // PENTING: ini HARUS setelah cap check di atas.
    // Kalau ditaruh sebelum cap check, count di-reset ke 0 sebelum cap check melihatnya
    // → cap check skip → round tidak pernah advance.
    if (windowExpired && swapCountNow < hourlySwapCap) {
      console.log(`${tag} [mt] Window expired with ${swapCountNow}/${hourlySwapCap} — resetting timer (still round ${roundNumber})`);
      resetOtcAccountSwapWindow(account.name);
      updateOtcAccountSnapshot(dashboard, account.name, {
        sw: `0/${hourlySwapCap}`,
        cd: "-"
      });
      // Lanjut ke taker/maker — tidak skip
    }

    const isMakerCooldown = Date.now() < makerCooldownUntil;
    const isMakerBalanceLock = Date.now() < makerBalanceLockUntil;
    const isTakerBalanceLock = Date.now() < takerBalanceLockUntil;

    // STRICT SERIAL GATE: kalau ada in-flight apapun (settling/pending),
    // skip seluruh phase taker & maker. Tunggu sampai semua resolve.
    // TAPI: cancel order idle yg sudah lewat cancelAfterIdleMinutes
    // agar akun tidak stuck di OPN selamanya.
    // NOTE: order settling (reservedByProfileId) TIDAK BISA dicancel.
    {
      const settling = getSettlingListings();
      const openOrders = myOrders.filter(o => o.status === "open");
      const openAny = openOrders.length;
      const hasInFlight = settling.length > 0 || openAny > 0 || inFlightTakeIds.size > 0 || inFlightMakerIds.size > 0;
      if (hasInFlight) {
        // SMART IDLE-CANCEL: cancel order yang sudah terlalu lama idle.
        // Hanya cancel order yang BELUM reserved (settling = tidak bisa dicancel).
        const cancelAfterIdleMs = Math.max(60_000, (Number(makerCfg.cancelAfterIdleMinutes) || 5) * 60_000);
        const nowGate = Date.now();
        let cancelledInGate = 0;
        for (const myOrder of openOrders) {
          const createdMs = Date.parse(myOrder.createdAt || "");
          if (!Number.isFinite(createdMs)) continue;
          const elapsedMs = nowGate - createdMs;
          if (elapsedMs < cancelAfterIdleMs) continue;
          // Order sudah idle >= threshold → coba cancel.
          // Kalau reservedByProfileId set tapi ternyata ghost/stale reserve,
          // cancel akan sukses. Kalau benar settling, API return 409 → kita skip.
          try {
            await client.cancelOtcOrder(myOrder.id);
            selfCancelledIds.add(String(myOrder.id));
            inFlightMakerIds.delete(String(myOrder.id));
            cancelledInGate++;
            statsBucket.ordersCancelled = (statsBucket.ordersCancelled || 0) + 1;
            const reserveNote = myOrder.reservedByProfileId ? " (was ghost-reserved)" : "";
            console.log(
              `${tag} [gate] Cancelled idle ${myOrder.id.slice(0, 8)} ` +
              `(${(elapsedMs / 60000).toFixed(1)}min ≥ ${(cancelAfterIdleMs / 60000).toFixed(0)}min threshold)${reserveNote}`
            );
          } catch (cancelErr) {
            const errMsg = String(cancelErr.message || "").toLowerCase();
            if (errMsg.includes("settlement") || errMsg.includes("reserved") || errMsg.includes("409")) {
              // Benar-benar settling — tidak bisa dicancel, tunggu resolve.
              console.log(`${tag} [gate] Cancel skip ${myOrder.id.slice(0, 8)} (truly settling — API rejected)`);
            } else {
              console.log(`${tag} [gate] Cancel failed ${myOrder.id.slice(0, 8)}: ${cancelErr.message}`);
            }
          }
        }
        // Jika berhasil cancel order, langsung re-loop (jangan sleep 8s)
        // supaya data myOrders ter-refresh dan gate re-evaluate.
        if (cancelledInGate > 0) {
          console.log(`${tag} [gate] Cancelled ${cancelledInGate} idle order(s) — re-evaluating`);
          makerFillBaselineSet = true;
          await sleep(2000); // brief pause before re-fetch
          continue;
        }

        const label = settling.length > 0 ? "SETTLE" :
          (inFlightTakeIds.size > 0 ? "PEND-TK" :
            (openAny > 0 ? "OPEN" : "PEND-MK"));
        updateOtcAccountSnapshot(dashboard, account.name, { status: label, rnd: roundNumber });
        if (loop % 5 === 0) {
          const settlingIds = settling.map(o => o.id.slice(0, 8)).join(",") || "-";
          const takeIds = Array.from(inFlightTakeIds).map(s => s.slice(0, 8)).join(",") || "-";
          const makerIds = Array.from(inFlightMakerIds).map(s => s.slice(0, 8)).join(",") || "-";
          console.log(`${tag} [mt] WAIT in-flight (open=${openAny} settling=${settling.length} take=${inFlightTakeIds.size} maker=${inFlightMakerIds.size}) — settling=${settlingIds} take=${takeIds} maker=${makerIds}`);
        }
        await sleep(8000);
        continue;
      }
    }

    // ═══════════════════════════════════════════════════
    // PHASE 1: TAKER (drain) — keep taking while balance allows.
    //   Maker only runs if zero successful takes this iteration.
    //   Balance-aware: pickBestOtcOrder filters orders we cannot afford,
    //   and we refresh balance after each take so next pick is accurate.
    // ═══════════════════════════════════════════════════
    const takerSwapCfg = { ...swapCfg, minEdgeBps: takerMinBps };
    let didTake = false;
    let drainCount = 0;
    let settlingSkipCount = 0;
    const maxSettlingSkips = 5;
    const maxDrainPerLoop = Math.max(1, clampToNonNegativeInt(takerCfg.maxDrainPerLoop, 10));

    if (isTakerBalanceLock && loop % 5 === 0) {
      const remainSec = Math.ceil((takerBalanceLockUntil - Date.now()) / 1000);
      console.log(`${tag} [taker] Balance-lock cooldown ${remainSec}s (waiting pending settlement)`);
    }

    while (!isTakerBalanceLock && drainCount < maxDrainPerLoop) {
      // SERIAL gate: tidak boleh take kalau:
      //   1. Sudah ada listing maker kita yang open (reserved/belum) — biar resolve dulu
      //   2. Sudah ada 1 taker reserve in-flight (pendingTakerReserves > 0)
      //   3. Proyeksi (done + this take) bakal melebihi cap
      {
        const c = getCommitment();
        const openAny = myOrders.filter(o => o.status === "open").length;
        const projected = c.done + openAny + pendingTakerReserves + 1;
        if (projected > hourlySwapCap) break;
        if (openAny > 0) break; // tunggu listing maker resolve
        if (pendingTakerReserves > 0) break; // sudah ada reserve in-flight
      }

      const pick = pickBestOtcOrder(orders, mids, balanceData, selfProfileId, takerSwapCfg, pickerCtx);
      if (!pick) break;

      // Mark "the orderbook had something profitable I could attempt" — even if take fails later
      lastProfitableHitAt = Date.now();

      const { order, edge } = pick;
      updateOtcAccountSnapshot(dashboard, account.name, { status: "TAKE" });
      console.log(
        `${tag} [taker] PICK ${order.id.slice(0, 8)} ` +
        `${order.srcAsset}→${order.dstAsset} edge=${edge.edgeBps.toFixed(1)}bps ` +
        `(drain ${drainCount + 1}/${maxDrainPerLoop})`
      );
      const blacklistTtlMs = (Number(takerCfg.orderBlacklistSeconds) || 60) * 1000;

      // Reserve
      let reserveOk = false;
      try {
        await client.reserveOtcOrder(order.id);
        reserveOk = true;
        pendingTakerReserves += 1;
      } catch (error) {
        const errMsg = String(error.message || "");
        if (isOtcOrderClosedError(errMsg)) {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${tag} [taker] Reserve race ${order.id.slice(0, 8)} (409) — blacklist, try next`);
        } else if (isOtcMakerSettlementInProgressError(errMsg)) {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          settlingSkipCount += 1;
          console.log(`${tag} [taker] Reserve skip ${order.id.slice(0, 8)} (maker settling ${settlingSkipCount}/${maxSettlingSkips}) — blacklist, try next`);
        } else {
          console.log(`${tag} [taker] Reserve failed: ${errMsg}`);
          blacklistOtcOrder(order.id, blacklistTtlMs);
        }
        statsBucket.takeFail = (statsBucket.takeFail || 0) + 1;
      }

      if (!reserveOk) {
        if (settlingSkipCount >= maxSettlingSkips) {
          // Force switch to maker phase (skips idle-threshold wait, handled below)
          break;
        }
        // Try the next-best order in this same drain iteration
        continue;
      }

      // Take
      let takeOk = false;
      let breakAfterThis = false;
      try {
        const takeResult = await client.takeOtcOrder(order.id);
        const filled = isObject(takeResult && takeResult.data && takeResult.data.order) ? takeResult.data.order : {};
        let filledStatus = String(filled.status || "").toLowerCase();
        const isSettledImmediate = filledStatus === "settled" || filledStatus === "completed" || filledStatus === "filled";
        const isFailedImmediate = filledStatus === "failed" || filledStatus === "rejected";
        const isCancelledImmediate = filledStatus === "cancelled" || filledStatus === "canceled" || filledStatus === "expired";
        const isPendingImmediate = !isSettledImmediate && !isFailedImmediate && !isCancelledImmediate;
        const makerUsername = normalizeOtcUsername(order.makerUsername);

        // VERIFIKASI: setelah take, kalau status belum terminal, poll sampai
        // server confirm sebelum kita keputusan cap. Ini ngehindarin race
        // condition di mana kita over-create maker karena status belum sempat
        // ke-record di local counter.
        let finalStatus = filledStatus;
        let verified = isSettledImmediate || isFailedImmediate || isCancelledImmediate;
        if (isPendingImmediate) {
          // Brief delay supaya server sempat propagate state.
          await sleep(1500);
          const verifyTimeoutMs = Math.max(5000, Number(takerCfg.takeVerifyTimeoutMs) || 20000);
          const resolution = await waitForOtcOrderResolution(client, order.id, { timeoutMs: verifyTimeoutMs, pollIntervalMs: 2000 });
          if (resolution.resolved && resolution.status !== "missing") {
            finalStatus = String(resolution.status || "").toLowerCase();
            verified = true;
            console.log(`${tag} [taker] verify ${order.id.slice(0, 8)} → status=${finalStatus}`);
          } else if (resolution.resolved && resolution.status === "missing") {
            console.log(`${tag} [taker] verify ${order.id.slice(0, 8)} → missing from /orders (assume settled remotely)`);
            // Treat missing as filled-equivalent? Aman: TIDAK record, biarin
            // prune di iterasi berikutnya yang menentukan.
          } else {
            console.log(`${tag} [taker] verify ${order.id.slice(0, 8)} timeout (last=${resolution.status || "?"}) — leave as in-flight`);
          }
        }

        const isFinalSettled = finalStatus === "settled" || finalStatus === "completed" || finalStatus === "filled";
        const isFinalFailed = finalStatus === "failed" || finalStatus === "rejected";
        const isFinalCancelled = finalStatus === "cancelled" || finalStatus === "canceled" || finalStatus === "expired";

        const mark = isFinalSettled ? "OK" : (isFinalFailed ? "FAIL" : (isFinalCancelled ? "CXL" : "PEND"));
        if (makerUsername) {
          recordOtcCounterpartyTake(makerUsername);
          const cnt = pruneOtcCounterpartyHistory(makerUsername, Date.now()).length;
          const limit = Number(takerCfg.maxTakesPerCounterpartyPerWeek)
            || Number(takerCfg.maxTakesPerCounterpartyPerHour) || 0;
          console.log(
            `${tag} [taker] ${mark} TOOK ${order.id.slice(0, 8)} status=${finalStatus || "?"} ` +
            `maker=${order.makerUsername} (${cnt}${limit > 0 ? `/${limit}` : ""}/wk)`
          );
        } else {
          console.log(`${tag} [taker] ${mark} TOOK ${order.id.slice(0, 8)} status=${finalStatus || "?"}`);
        }

        if (verified && (isFinalSettled || isFinalFailed)) {
          // ✓ Hitung sebagai swap: filled atau failed.
          if (isFinalSettled) {
            takesOk++;
            statsBucket.takeOk = (statsBucket.takeOk || 0) + 1;
            didTake = true;
            takeOk = true;
          } else {
            statsBucket.takeFail = (statsBucket.takeFail || 0) + 1;
          }
          if (!recordedSwapTakeIds.has(String(order.id))) {
            recordOtcAccountSwap(account.name);
            recordedSwapTakeIds.add(String(order.id));
          }
          inFlightTakeIds.delete(String(order.id));
          breakAfterThis = true;
        } else if (verified && isFinalCancelled) {
          // Cancelled/expired: TIDAK dihitung sebagai swap.
          blacklistOtcOrder(order.id, blacklistTtlMs);
          statsBucket.takeFail = (statsBucket.takeFail || 0) + 1;
          inFlightTakeIds.delete(String(order.id));
        } else {
          // Belum ter-verifikasi (pending atau timeout): HOLD slot, biarin
          // prune iterasi berikutnya yang resolve.
          inFlightTakeIds.add(String(order.id));
          blacklistOtcOrder(order.id, blacklistTtlMs);
          breakAfterThis = true;
        }

        const hrCnt = getOtcAccountSwapCount(account.name);
        // Skip this order on next pick (cached `orders` array still has it as "open")
        blacklistOtcOrder(order.id, blacklistTtlMs);
        updateOtcAccountSnapshot(dashboard, account.name, { tk: takesOk, sw: `${hrCnt}/${hourlySwapCap}` });
        mtActivityCount += 1;
        if (mtActivityCount % mtPointsRefreshEvery === 0) {
          await refreshOtcAccountPoints(client, dashboard, account.name, tag);
        }
        if (hrCnt >= hourlySwapCap) {
          console.log(`${tag} [taker] hourly swap cap ${hrCnt}/${hourlySwapCap} — end drain`);
          breakAfterThis = true;
        }
      } catch (error) {
        const errMsg = String(error.message || "");
        if (isOtcOrderClosedError(errMsg)) {
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${tag} [taker] Take race ${order.id.slice(0, 8)} (409) — blacklist, try next`);
        } else if (isOtcBalanceLockError(errMsg)) {
          const lockSec = Number(takerCfg.balanceLockCooldownSeconds) || 90;
          takerBalanceLockUntil = Date.now() + lockSec * 1000;
          blacklistOtcOrder(order.id, blacklistTtlMs);
          console.log(`${tag} [taker] Balance lock on take ${order.id.slice(0, 8)} — pause taker ${lockSec}s, end drain`);
          breakAfterThis = true;
        } else {
          console.log(`${tag} [taker] Take failed: ${errMsg}`);
          blacklistOtcOrder(order.id, blacklistTtlMs);
        }
        statsBucket.takeFail = (statsBucket.takeFail || 0) + 1;
      }
      // Reserve→take cycle selesai (sukses atau fail) → lepas pending counter.
      // Kalau sukses, swap sudah tercatat via recordOtcAccountSwap (done naik).
      pendingTakerReserves = Math.max(0, pendingTakerReserves - 1);

      drainCount++;

      if (breakAfterThis) break;

      if (takeOk) {
        // Refresh balance immediately so next pick filters by post-take balance
        try {
          const balResp = await client.getBalances();
          if (isObject(balResp && balResp.data)) {
            balanceData = balResp.data;
            const bal = formatOtcCcUsdc(balanceData);
            updateOtcAccountSnapshot(dashboard, account.name, { cc: bal.cc, usdc: bal.usdc, eth: bal.eth });
            maybeRefillEth(account.name, balanceData);
          }
        } catch (_) { }
      }
    }

    if (didTake && drainCount > 1) {
      console.log(`${tag} [taker] drain complete: ${drainCount} attempts this loop`);
    }

    // ── CAP VERIFY ── setelah drain selesai, cek ulang cap.
    // Kalau sudah tercapai → skip cleanup & maker, langsung ke cap check di atas.
    {
      const postDrainCount = getOtcAccountSwapCount(account.name);
      if (postDrainCount >= hourlySwapCap) {
        console.log(`${tag} [cap-verify] Post-drain: ${postDrainCount}/${hourlySwapCap} — cap reached, skipping maker`);
        updateOtcAccountSnapshot(dashboard, account.name, {
          sw: `${postDrainCount}/${hourlySwapCap}`,
          status: "CAP"
        });
        makerFillBaselineSet = true;
        await sleep(5000);
        continue;
      }
    }

    // ═══════════════════════════════════════════════════
    const openOrders = myOrders.filter(o => o.status === "open");
    let lockedCc = 0;
    let lockedUsdc = 0;
    for (const o of openOrders) {
      const src = Number(o.srcAmountDecimal) || 0;
      const srcAsset = String(o.srcAsset || "").toUpperCase();
      if (srcAsset === "CC") lockedCc += src;
      else if (srcAsset === "USDC") lockedUsdc += src;
    }

    const now = Date.now();
    const cancelAfterIdleMs = Math.max(60_000, (Number(makerCfg.cancelAfterIdleMinutes) || 5) * 60_000);
    let cancelledThisLoop = 0;
    for (const myOrder of openOrders) {
      // PENTING: order settling (reservedByProfileId) TIDAK BISA dicancel
      if (myOrder.reservedByProfileId) continue;

      const createdMs = Date.parse(myOrder.createdAt || "");
      const expiresMs = Date.parse(myOrder.expiresAt || "");
      if (!Number.isFinite(createdMs) || !Number.isFinite(expiresMs)) continue;
      const totalLifeMs = expiresMs - createdMs;
      const elapsedMs = now - createdMs;

      const idleTooLong = elapsedMs >= cancelAfterIdleMs;
      const pastHalfLife = totalLifeMs > 0 && elapsedMs > totalLifeMs * 0.5;
      if (!idleTooLong && !pastHalfLife) continue;

      const cancelReason = idleTooLong
        ? `idle ${(elapsedMs / 60000).toFixed(1)}min ≥ ${(cancelAfterIdleMs / 60000).toFixed(0)}min threshold`
        : `past half-life`;
      try {
        await client.cancelOtcOrder(myOrder.id);
        selfCancelledIds.add(String(myOrder.id));
        inFlightMakerIds.delete(String(myOrder.id));
        // Free locked balance
        const cancelledSrc = Number(myOrder.srcAmountDecimal) || 0;
        if (String(myOrder.srcAsset || "").toUpperCase() === "CC") lockedCc -= cancelledSrc;
        else if (String(myOrder.srcAsset || "").toUpperCase() === "USDC") lockedUsdc -= cancelledSrc;
        console.log(`${tag} [maker] Cancelled ${myOrder.id.slice(0, 8)} (${cancelReason})`);
        ordersCancelled++;
        cancelledThisLoop++;
        statsBucket.ordersCancelled = (statsBucket.ordersCancelled || 0) + 1;
      } catch (cancelErr) {
        const errMsg = String(cancelErr.message || "").toLowerCase();
        if (errMsg.includes("settlement") || errMsg.includes("reserved") || errMsg.includes("409")) {
          // Order sedang settling — tidak bisa dicancel, skip
          console.log(`${tag} [maker] Cancel skip ${myOrder.id.slice(0, 8)} (settling — not cancellable)`);
        } else {
          console.log(`${tag} [maker] Cancel failed ${myOrder.id.slice(0, 8)}: ${cancelErr.message}`);
        }
      }
    }

    // ═══════════════════════════════════════════════════
    // PHASE 3: MAKER — create listing only when orderbook is idle
    //   Trigger: no profitable take seen for `takerIdleSecondsBeforeMaker`.
    //   (SKIPPED during maker cooldown / balance lock / in-flight takes)
    // ═══════════════════════════════════════════════════
    const currentOpenCount = openOrders.length - cancelledThisLoop;
    const msSinceProfitable = Date.now() - lastProfitableHitAt;
    const settlingForcedMaker = settlingSkipCount >= maxSettlingSkips;
    const idleEnoughForMaker = settlingForcedMaker || msSinceProfitable >= idleThresholdMs;
    // HARD BLOCK: in-flight = tidak boleh open apapun.
    const hasInFlightActivity = inFlightTakeIds.size > 0 || inFlightMakerIds.size > 0;
    if (settlingForcedMaker && !hasInFlightActivity) {
      console.log(`${tag} [mt] ${settlingSkipCount} maker-settling skips — force switch to maker phase`);
    }

    // SERIAL MODE: hanya boleh 1 listing terbuka pada satu waktu.
    const commitNow = getCommitment();
    const settlingCount = getSettlingListings().length;
    const openAnyCount = openOrders.length - cancelledThisLoop;
    const projectedSlots = Math.max(0, hourlySwapCap - commitNow.done - openAnyCount);
    const SERIAL_MAX_OPEN = 1;
    const effectiveMaxOpen = openAnyCount === 0 && projectedSlots > 0 && !hasInFlightActivity ? SERIAL_MAX_OPEN : 0;

    if (hasInFlightActivity) {
      updateOtcAccountSnapshot(dashboard, account.name, { status: "PEND" });
    } else if (isMakerCooldown) {
      if (loop % 10 === 0) {
        const remainMin = Math.ceil((makerCooldownUntil - Date.now()) / 60000);
        console.log(`${tag} [mt] Maker cooldown — ${remainMin}min left — taker-only mode`);
      }
    } else if (isMakerBalanceLock) {
      updateOtcAccountSnapshot(dashboard, account.name, { status: "LOCK" });
      if (loop % 5 === 0) {
        const remainSec = Math.ceil((makerBalanceLockUntil - Date.now()) / 1000);
        console.log(`${tag} [maker] Balance-lock cooldown ${remainSec}s (locked CC=${lockedCc.toFixed(2)} USDC=${lockedUsdc.toFixed(2)} — waiting settlement)`);
      }
    } else if (!didTake && !idleEnoughForMaker) {
      updateOtcAccountSnapshot(dashboard, account.name, { status: "WAIT" });
    } else if (!didTake && idleEnoughForMaker && effectiveMaxOpen > 0 && currentOpenCount < maxOpenOrders) {
      // ── PRE-MAKER VERIFY ── verifikasi terakhir sebelum open maker.
      // Re-fetch myOrders + jalankan ulang scan untuk catch fill/failed
      // yang terjadi barusan, biar cap check di sini valid.
      try {
        const verifyRes = await client.getCrossOtcOrders(true);
        const verifyOrders = Array.isArray(verifyRes && verifyRes.data && verifyRes.data.orders)
          ? verifyRes.data.orders
          : (Array.isArray(verifyRes && verifyRes.data) ? verifyRes.data : []);
        // Re-scan filled+failed sebelum cap check.
        for (const o of verifyOrders) {
          const oid = String(o.id || "");
          if (!oid) continue;
          const stv = String(o.status || "").toLowerCase();
          if (!isOtcSwapCountedStatus(stv)) continue;
          if (recordedMakerFillIds.has(oid) || recordedSwapTakeIds.has(oid)) continue;
          if (selfCancelledIds.has(oid)) {
            selfCancelledIds.delete(oid);
            if (o.isMaker) recordedMakerFillIds.add(oid);
            else recordedSwapTakeIds.add(oid);
            continue;
          }
          recordOtcAccountSwap(account.name);
          if (o.isMaker) recordedMakerFillIds.add(oid);
          else recordedSwapTakeIds.add(oid);
          const lc = getOtcAccountSwapCount(account.name);
          const stLabel = stv === "filled" ? "FILLED" : "FAILED";
          console.log(`${tag} [pre-maker-verify] ${oid.slice(0, 8)} ${stLabel} → swap ${lc}/${hourlySwapCap}`);
        }
        // Cek ulang cap setelah verify.
        const postVerifyCount = getOtcAccountSwapCount(account.name);
        if (postVerifyCount >= hourlySwapCap) {
          console.log(`${tag} [pre-maker-verify] cap reached ${postVerifyCount}/${hourlySwapCap} — abort maker create`);
          updateOtcAccountSnapshot(dashboard, account.name, {
            sw: `${postVerifyCount}/${hourlySwapCap}`,
            status: "CAP"
          });
          makerFillBaselineSet = true;
          await sleep(5000);
          continue;
        }
        // Cek ulang in-flight: ada order baru yang masih open?
        const stillOpenAny = verifyOrders.some(o => String(o.status || "").toLowerCase() === "open");
        if (stillOpenAny) {
          console.log(`${tag} [pre-maker-verify] open order detected — defer maker, wait next iter`);
          await sleep(5000);
          continue;
        }
      } catch (verifyErr) {
        console.log(`${tag} [pre-maker-verify] fetch failed: ${verifyErr.message} — defer maker`);
        await sleep(5000);
        continue;
      }

      // Refresh balance before maker create
      try {
        const balResp = await client.getBalances();
        if (isObject(balResp && balResp.data)) {
          balanceData = balResp.data;
          const bal = formatOtcCcUsdc(balanceData);
          updateOtcAccountSnapshot(dashboard, account.name, { cc: bal.cc, usdc: bal.usdc, eth: bal.eth });
          maybeRefillEth(account.name, balanceData);
        }
      } catch (_) { }

      const ccBalance = otcGetAccountBalance("CC", balanceData);
      const usdcBalance = otcGetAccountBalance("USDC", balanceData);
      const availCc = Math.max(0, ccBalance - Math.max(0, lockedCc));
      const availUsdc = Math.max(0, usdcBalance - Math.max(0, lockedUsdc));
      const minUsd = Number(swapCfg.minOrderSizeUsd) || 1.05;
      const maxUsd = Number(swapCfg.maxOrderSizeUsd) || 10;

      const availCcValueUsd = availCc * ccPriceUsd;
      const canSellCc = availCcValueUsd >= minUsd;
      const canSellUsdc = availUsdc >= minUsd;

      if (canSellCc || canSellUsdc) {
        let sellDirection;
        if (canSellCc && canSellUsdc) {
          const ccWeight = availCcValueUsd / (availCcValueUsd + availUsdc);
          sellDirection = Math.random() < ccWeight ? "cc" : "usdc";
        } else {
          sellDirection = canSellCc ? "cc" : "usdc";
        }

        const edgeBps = minBps + Math.random() * (maxBps - minBps);
        const edgeFactor = 1 - edgeBps / 10000;

        let side, srcAmount, dstAmount, srcLabel, dstLabel;

        if (sellDirection === "cc") {
          const maxCcForOrder = Math.min(availCc, maxUsd / ccPriceUsd);
          const minCcForOrder = minUsd / ccPriceUsd;
          const actualCc = Number((minCcForOrder + Math.random() * Math.max(0, maxCcForOrder - minCcForOrder)).toFixed(6));
          const askUsdc = Number((actualCc * ccPriceUsd * edgeFactor).toFixed(6));
          side = "canton_sell_cc_for_usdc";
          srcAmount = actualCc.toFixed(9).replace(/\.?0+$/, "");
          dstAmount = askUsdc.toFixed(6).replace(/\.?0+$/, "");
          srcLabel = `${actualCc.toFixed(4)} CC`;
          dstLabel = `${askUsdc.toFixed(6)} USDC`;
        } else {
          const maxUsdcForOrder = Math.min(availUsdc, maxUsd);
          const minUsdcForOrder = minUsd;
          const actualUsdc = Number((minUsdcForOrder + Math.random() * Math.max(0, maxUsdcForOrder - minUsdcForOrder)).toFixed(6));
          const askCc = Number((actualUsdc / ccPriceUsd * edgeFactor).toFixed(6));
          side = "eth_sell_usdc_for_cc";
          srcAmount = actualUsdc.toFixed(6).replace(/\.?0+$/, "");
          dstAmount = askCc.toFixed(9).replace(/\.?0+$/, "");
          srcLabel = `${actualUsdc.toFixed(4)} USDC`;
          dstLabel = `${askCc.toFixed(4)} CC`;
        }

        updateOtcAccountSnapshot(dashboard, account.name, { status: "MAKE" });
        console.log(`${tag} [maker] Creating: sell ${srcLabel} → ${dstLabel} (edge=${edgeBps.toFixed(0)}bps) [${currentOpenCount + 1}/${maxOpenOrders}]`);
        try {
          const createResult = await client.createOtcOrder({ side, srcAmountDecimal: srcAmount, dstAmountDecimal: dstAmount, expiresHours });
          const createdOrder = isObject(createResult && createResult.data && createResult.data.order)
            ? createResult.data.order : null;
          if (createdOrder && createdOrder.id) {
            inFlightMakerIds.add(String(createdOrder.id));
          }
          ordersCreated++;
          statsBucket.ordersCreated = (statsBucket.ordersCreated || 0) + 1;
          updateOtcAccountSnapshot(dashboard, account.name, { mk: ordersCreated });
          mtActivityCount += 1;
          if (mtActivityCount % mtPointsRefreshEvery === 0) {
            await refreshOtcAccountPoints(client, dashboard, account.name, tag);
          }
          // POST-CREATE VERIFY — wait until server confirms listing visible
          // di /orders mine. Mencegah race condition di mana iterasi berikutnya
          // belum lihat order ini & open maker lagi.
          if (createdOrder && createdOrder.id) {
            await sleep(2000); // brief delay supaya server sync
            const verifyTimeoutMs = Math.max(3000, Number(makerCfg.createVerifyTimeoutMs) || 12000);
            const verifyDeadline = Date.now() + verifyTimeoutMs;
            let seenOnServer = false;
            while (Date.now() < verifyDeadline) {
              try {
                const checkRes = await client.getCrossOtcOrders(true);
                const checkOrders = Array.isArray(checkRes && checkRes.data && checkRes.data.orders)
                  ? checkRes.data.orders
                  : (Array.isArray(checkRes && checkRes.data) ? checkRes.data : []);
                if (checkOrders.some(o => String(o.id) === String(createdOrder.id))) {
                  seenOnServer = true;
                  break;
                }
              } catch (_) { /* retry */ }
              await sleep(1500);
            }
            if (seenOnServer) {
              console.log(`${tag} [maker] verify ${createdOrder.id.slice(0, 8)} visible on server`);
            } else {
              console.log(`${tag} [maker] verify ${createdOrder.id.slice(0, 8)} NOT visible after ${verifyTimeoutMs}ms — leave as in-flight`);
            }
          }
        } catch (error) {
          const errMsg = String(error.message || "");
          if (errMsg.includes("429") || errMsg.toLowerCase().includes("too many")) {
            const cooldownMin = Math.ceil(rateLimitCooldownMs / 60000);
            makerCooldownUntil = Date.now() + rateLimitCooldownMs;
            console.log(`${tag} [maker] Rate limited! Switching to taker-only for ${cooldownMin}min`);
            statsBucket.rateLimits = (statsBucket.rateLimits || 0) + 1;
          } else if (isOtcBalanceLockError(errMsg)) {
            const lockSec = Number(makerCfg.balanceLockCooldownSeconds) || 120;
            makerBalanceLockUntil = Date.now() + lockSec * 1000;
            console.log(`${tag} [maker] Balance lock on create — pause maker ${lockSec}s for settlement (locked CC=${lockedCc.toFixed(2)} USDC=${lockedUsdc.toFixed(2)})`);
            statsBucket.balanceLocks = (statsBucket.balanceLocks || 0) + 1;
          } else {
            console.log(`${tag} [maker] Create failed: ${errMsg}`);
            statsBucket.ordersFail = (statsBucket.ordersFail || 0) + 1;
          }
        }
      } else {
        if (loop % 5 === 0) {
          console.log(`${tag} [maker] Low avail: CC=${availCc.toFixed(2)}/${ccBalance.toFixed(2)} USDC=${availUsdc.toFixed(2)}/${usdcBalance.toFixed(2)}`);
        }
      }
    }

    try {
      const balResp = await client.getBalances();
      if (isObject(balResp && balResp.data)) {
        balanceData = balResp.data;
        const bal = formatOtcCcUsdc(balanceData);
        updateOtcAccountSnapshot(dashboard, account.name, { cc: bal.cc, usdc: bal.usdc, eth: bal.eth });
        maybeRefillEth(account.name, balanceData);
      }
    } catch (_) { }

    // Cooldown:
    //   - fully stalled (maker cooldown + taker balance lock) → 15s+
    //   - WAIT mode (no take, no make this iter, idle<threshold, no locks) → fast scan
    //     (honors "wajib ambil" rule: re-scan orderbook ASAP for new takeable orders)
    //   - otherwise (took or made or in lock) → human-like 5-10s
    const fullyStalled = (isMakerCooldown || isMakerBalanceLock) && isTakerBalanceLock;
    const inWaitMode = !didTake
      && !idleEnoughForMaker
      && !isMakerCooldown
      && !isMakerBalanceLock
      && !isTakerBalanceLock;
    let cooldown;
    if (fullyStalled) {
      cooldown = Math.max(15, clampToNonNegativeInt(swapCfg.minDelaySeconds, 30));
    } else if (inWaitMode) {
      cooldown = Math.max(1, Number(takerCfg.fastScanIntervalSeconds) || 2);
    } else {
      cooldown = humanLikeDelay(
        clampToNonNegativeInt(swapCfg.minDelaySeconds, 30),
        clampToNonNegativeInt(swapCfg.maxDelaySeconds, 90)
      );
    }
    if (!isMakerBalanceLock && !isTakerBalanceLock && !isMakerCooldown && !inWaitMode) {
      updateOtcAccountSnapshot(dashboard, account.name, { status: "COOL" });
    }
    makerFillBaselineSet = true;
    await sleep(cooldown * 1000);
  }

  updateOtcAccountSnapshot(dashboard, account.name, { status: "DONE" });
  return { account: account.name, ok: true, takesOk, ordersCreated, ordersCancelled };
}

async function runOtcMakerTakerFlow(context) {
  const { config, accounts } = context;
  const swapCfg = isObject(config.swap) ? config.swap : {};
  if (!swapCfg.enabled) {
    console.log("[otc-mt] config.swap.enabled = false. Aktifkan dulu.");
    return;
  }

  const selectedAccounts = accounts.accounts;
  if (selectedAccounts.length === 0) {
    console.log("[otc-mt] Tidak ada akun terpilih.");
    return;
  }

  const makerCfg = isObject(swapCfg.maker) ? swapCfg.maker : {};
  const takerCfg = isObject(swapCfg.taker) ? swapCfg.taker : {};
  const dashboard = attachOtcDashboard(context, "OTC-MAKER-TAKER");
  context.dashboard = dashboard;

  console.log(`\n${"#".repeat(70)}`);
  console.log(`[otc-mt] Maker-Taker — "Maker→429→Taker" cycle strategy`);
  console.log(`[otc-mt] Accounts=${selectedAccounts.length} | MakerBPS=${makerCfg.minBps}-${makerCfg.maxBps} | TakerMinBPS=${takerCfg.minBps} | maxOpen=${makerCfg.maxOpenOrders}/akun`);
  console.log(`[otc-mt] Pair: CC(Canton) ↔ USDC(Base) | Cooldown=${makerCfg.rateLimitCooldownMinutes}min`);
  console.log(`${"#".repeat(70)}\n`);

  const statsBucket = { ordersCreated: 0, ordersFail: 0, ordersCancelled: 0, takeOk: 0, takeFail: 0 };
  context.statsBucket = statsBucket;
  startOtcWebSnapshotLoop(dashboard, "OTC-MAKER-TAKER", context);
  const workers = Math.max(1, Number(swapCfg.workers) || 5);
  const queue = [...selectedAccounts];
  const inFlight = [];
  const results = [];

  const launchNext = () => {
    while (inFlight.length < workers && queue.length > 0) {
      const acc = queue.shift();
      const p = runOtcMakerTakerAccountWorker(acc, context, statsBucket)
        .then((r) => { results.push(r); })
        .catch((err) => { results.push({ account: acc.name, ok: false, error: err.message }); })
        .finally(() => {
          const idx = inFlight.indexOf(p);
          if (idx >= 0) inFlight.splice(idx, 1);
        });
      inFlight.push(p);
    }
  };

  try {
    launchNext();
    while (inFlight.length > 0) {
      await Promise.race(inFlight);
      launchNext();
    }
    console.log(`\n${"#".repeat(70)}`);
    console.log(`[otc-mt] Done — listings=${statsBucket.ordersCreated} takes=${statsBucket.takeOk} cancelled=${statsBucket.ordersCancelled} fail=${statsBucket.takeFail + statsBucket.ordersFail}`);
    console.log(`${"#".repeat(70)}\n`);
  } finally {
    detachOtcDashboard(dashboard);
    context.dashboard = null;
  }
}

// =============================================================================
// OTC Ring-Hybrid (legacy — self-listing antar akun + camouflage external take)
// =============================================================================

const OTC_PAIR_SIDES = {
  cc_usdcx: { sellBaseSide: "canton_sell_cc_for_usdcx", sellQuoteSide: "canton_sell_usdcx_for_cc", baseAsset: "CC", quoteAsset: "USDCx" },
  usdc_cc: { sellBaseSide: "canton_sell_usdc_for_cc", sellQuoteSide: "canton_sell_cc_for_usdc", baseAsset: "USDC", quoteAsset: "CC" },
  usdc_usdcx: { sellBaseSide: "canton_sell_usdc_for_usdcx", sellQuoteSide: "canton_sell_usdcx_for_usdc", baseAsset: "USDC", quoteAsset: "USDCx" }
};

function shuffleArray(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = randomIntInclusive(0, i);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function selectRingPair(swapCfg, lastPair) {
  const pairs = Array.isArray(swapCfg.allowedPairs) && swapCfg.allowedPairs.length > 0
    ? swapCfg.allowedPairs.filter((p) => OTC_PAIR_SIDES[p])
    : Object.keys(OTC_PAIR_SIDES);
  if (pairs.length === 0) return null;
  if (pairs.length === 1) return pairs[0];
  // Avoid repeating the last pair if possible
  const candidates = lastPair ? pairs.filter((p) => p !== lastPair) : pairs;
  return candidates[randomIntInclusive(0, candidates.length - 1)];
}

function buildSelfListingPayload(pair, oracleMids, baseAmount, edgeBps, sellDirection) {
  // sellDirection: "base" → maker sells baseAsset, wants quoteAsset
  //                "quote" → maker sells quoteAsset, wants baseAsset
  const meta = OTC_PAIR_SIDES[pair];
  if (!meta) return null;
  const oraclePrice = Number(oracleMids[pair]);  // quote per base
  if (!Number.isFinite(oraclePrice) || oraclePrice <= 0) return null;

  const edgeFactor = 1 + (Number(edgeBps) || 0) / 10000;
  // edgeBps positif = taker discount (maker kasih lebih ke taker)
  // Untuk direction "base": maker sell base, dst quote; taker pays quote, gets base.
  //   Taker rate (base per quote) = srcBase / dstQuote.
  //   Untuk edge taker = +X bps, taker dapat lebih banyak base per quote → naikkan srcBase atau turunkan dstQuote.
  //   Kita pilih: turunkan dstQuote (maker minta quote lebih sedikit dari fair).

  if (sellDirection === "base") {
    const srcAmount = Number(baseAmount);  // base
    const fairDst = srcAmount * oraclePrice;  // quote
    const dstAmount = fairDst / edgeFactor;   // taker untung kalau edgeBps>0
    return {
      side: meta.sellBaseSide,
      srcAmountDecimal: srcAmount.toFixed(6).replace(/\.?0+$/, ""),
      dstAmountDecimal: dstAmount.toFixed(6).replace(/\.?0+$/, ""),
      srcAsset: meta.baseAsset,
      dstAsset: meta.quoteAsset,
      pair,
      oraclePrice,
      notionalUsdQuote: otcAssetToUsd(meta.quoteAsset, dstAmount, oracleMids) || 0
    };
  } else {
    // sell quote, get base
    const srcAmount = Number(baseAmount) * oraclePrice;  // quote (sama notional)
    const fairDst = srcAmount / oraclePrice;             // base = baseAmount
    const dstAmount = fairDst / edgeFactor;
    return {
      side: meta.sellQuoteSide,
      srcAmountDecimal: srcAmount.toFixed(6).replace(/\.?0+$/, ""),
      dstAmountDecimal: dstAmount.toFixed(6).replace(/\.?0+$/, ""),
      srcAsset: meta.quoteAsset,
      dstAsset: meta.baseAsset,
      pair,
      oraclePrice,
      notionalUsdQuote: otcAssetToUsd(meta.quoteAsset, srcAmount, oracleMids) || 0
    };
  }
}

function oracleDriftBps(listingPayload, freshMids) {
  const fresh = Number(freshMids[listingPayload.pair]);
  if (!Number.isFinite(fresh) || fresh <= 0) return 0;
  const orig = Number(listingPayload.oraclePrice);
  if (!Number.isFinite(orig) || orig <= 0) return 0;
  return Math.abs((fresh / orig - 1) * 10000);
}

async function refreshOtcWorkerBalance(worker, accountLogTag) {
  try {
    const balResp = await worker.client.getBalances();
    if (isObject(balResp && balResp.data)) {
      worker.balance = balResp.data;
      return true;
    }
  } catch (error) {
    console.log(`${accountLogTag} [otc-ring] Balance refresh failed: ${error.message}`);
  }
  return false;
}

async function setupOtcRingWorker(account, config, tokens) {
  const accountToken = tokens.accounts[account.name] || normalizeTokenProfile({});
  tokens.accounts[account.name] = accountToken;
  const accountConfig = cloneRuntimeConfig(config);
  applyTokenProfileToConfig(accountConfig, accountToken);
  const client = new RootsFiApiClient(accountConfig);
  const tag = `[${account.name}]`;

  if (!client.hasAccountSessionCookie()) {
    console.log(`${tag} [otc-ring] No session cookie — run OTP mode first, skip akun ini`);
    return null;
  }

  let sessionReuse;
  try {
    sessionReuse = await attemptSessionReuse(client, accountConfig, () => { }, tag);
  } catch (error) {
    console.log(`${tag} [otc-ring] Session reuse threw: ${error.message}`);
    return null;
  }
  if (!sessionReuse || !sessionReuse.ok) {
    console.log(`${tag} [otc-ring] Session not reusable, skip`);
    return null;
  }

  const balance = sessionReuse.balancesData;
  const profileId = getSelfProfileIdFromBalance(balance);
  return {
    account,
    client,
    balance,
    profileId,
    tag
  };
}

async function maybeCamouflageExternalTake(worker, swapCfg, openListings, statsBucket) {
  const camo = isObject(swapCfg.ring && swapCfg.ring.camouflage) ? swapCfg.ring.camouflage : {};
  if (!camo.enabled) return;
  const prob = Number(camo.probabilityPerLeg);
  if (!Number.isFinite(prob) || prob <= 0) return;
  if (Math.random() >= prob) return;

  let orders = [];
  let mids = {};
  try {
    const [ordersRes, refRes] = await Promise.all([
      worker.client.getCrossOtcOrders(false),
      worker.client.getCrossOtcReference()
    ]);
    orders = Array.isArray(ordersRes && ordersRes.data && ordersRes.data.orders)
      ? ordersRes.data.orders
      : (Array.isArray(ordersRes && ordersRes.data) ? ordersRes.data : []);
    mids = isObject(refRes && refRes.data && refRes.data.mids) ? refRes.data.mids : {};
  } catch (error) {
    return;
  }

  // Filter out our own listings (anti-flag): exclude maker == any worker we manage
  const ourProfileIds = new Set(openListings ? [...openListings.values()].map((v) => v.makerProfileId).filter(Boolean) : []);
  ourProfileIds.add(worker.profileId);
  const filtered = orders.filter((o) => !ourProfileIds.has(String(o.makerProfileId || "")));

  const pick = pickBestOtcOrder(filtered, mids, worker.balance, worker.profileId, swapCfg);
  if (!pick) return;

  const { order, edge } = pick;
  console.log(`${worker.tag} [otc-camo] take external ${order.id.slice(0, 8)} edge=${edge.edgeBps.toFixed(1)}bps`);
  try {
    await worker.client.reserveOtcOrder(order.id);
    await worker.client.takeOtcOrder(order.id);
    statsBucket.camoTakeOk += 1;
    statsBucket.camoVolumeUsd += edge.takerPaysUsd;
    await refreshOtcWorkerBalance(worker, worker.tag);
  } catch (error) {
    const errMsg = String(error.message || "");
    if (isOtcMakerSettlementInProgressError(errMsg)) {
      blacklistOtcOrder(order.id, 60000);
      console.log(`${worker.tag} [otc-camo] reserve skip ${order.id.slice(0, 8)} (maker settling)`);
    } else {
      console.log(`${worker.tag} [otc-camo] take failed: ${errMsg}`);
    }
    statsBucket.camoTakeFail += 1;
  }
}

async function runOtcRingHybridFlow(context) {
  const { config, accounts, tokens } = context;
  const swapCfg = isObject(config.swap) ? config.swap : {};
  const ringCfg = isObject(swapCfg.ring) ? swapCfg.ring : {};
  if (!swapCfg.enabled) {
    console.log("[otc-ring] config.swap.enabled = false");
    return;
  }
  const selectedAccounts = accounts.accounts;
  if (selectedAccounts.length < 2) {
    console.log(`[otc-ring] Butuh minimal 2 akun (terpilih: ${selectedAccounts.length}).`);
    return;
  }

  // Small-ring auto-boost: kalau <4 akun, naikkan camouflage probability untuk
  // kompensasi pattern (maker, taker) yang lebih obvious. 2 akun = pair statis,
  // 3 akun = 3-cycle yang masih reciprocal-ish, jadi camouflage minimal 50%.
  const smallRing = selectedAccounts.length < 4;
  const baseProb = ringCfg.camouflage && Number.isFinite(Number(ringCfg.camouflage.probabilityPerLeg))
    ? Number(ringCfg.camouflage.probabilityPerLeg)
    : 0.3;
  const effectiveCamoProb = smallRing ? Math.max(baseProb, 0.5) : baseProb;

  console.log(`\n${"#".repeat(70)}`);
  console.log(`[otc-ring] Ring-Hybrid OTC start${smallRing ? " (small-ring mode, anti-detect boost)" : ""}`);
  console.log(`[otc-ring] Accounts=${selectedAccounts.length} | edge=${ringCfg.selfListEdgeBps}bps | baseUsd=$${ringCfg.baseAmountUsd}`);
  console.log(`[otc-ring] Jitter=${ringCfg.legMinJitterSeconds}-${ringCfg.legMaxJitterSeconds}s | maxDrift=${ringCfg.maxDriftBps}bps | listingExpiresHours=${ringCfg.listingExpiresHours}`);
  console.log(`[otc-ring] Camouflage=${ringCfg.camouflage && ringCfg.camouflage.enabled ? `${(effectiveCamoProb * 100).toFixed(0)}%${smallRing && effectiveCamoProb > baseProb ? ` (boosted from ${(baseProb * 100).toFixed(0)}%)` : ""}` : "off"}`);
  if (smallRing) {
    console.log(`[otc-ring] WARN: ${selectedAccounts.length} akun = pair pattern lebih mudah dideteksi. Pertimbangkan tambah akun.`);
  }
  console.log(`${"#".repeat(70)}\n`);

  // Apply boosted probability to swapCfg snapshot used by maybeCamouflageExternalTake
  const effectiveSwapCfg = {
    ...swapCfg,
    ring: {
      ...ringCfg,
      camouflage: {
        ...(ringCfg.camouflage || {}),
        probabilityPerLeg: effectiveCamoProb
      }
    }
  };

  // Setup workers (login + session reuse parallel)
  console.log(`[otc-ring] Setting up ${selectedAccounts.length} workers...`);
  const setupResults = await Promise.all(
    selectedAccounts.map((acc) => setupOtcRingWorker(acc, config, tokens))
  );
  const workers = setupResults.filter(Boolean);
  if (workers.length < 2) {
    console.log(`[otc-ring] Only ${workers.length} worker(s) ready (<2). Abort.`);
    return;
  }
  console.log(`[otc-ring] ${workers.length} workers ready.\n`);

  // Open listings registry + SIGINT cleanup
  const openListings = new Map();  // orderId -> { client, account, makerProfileId, createdAtMs }
  let shuttingDown = false;
  const cleanup = async () => {
    if (shuttingDown) return;
    shuttingDown = true;
    console.log(`\n[otc-ring] SIGINT received, canceling ${openListings.size} open listings...`);
    await Promise.allSettled(
      [...openListings.entries()].map(([id, info]) =>
        info.client.cancelOtcOrder(id).catch((err) =>
          console.log(`[otc-ring] cancel ${id.slice(0, 8)} failed: ${err.message}`)
        )
      )
    );
    console.log("[otc-ring] cleanup done, exit.");
    process.exit(0);
  };
  process.on("SIGINT", cleanup);
  process.on("SIGTERM", cleanup);

  const statsBucket = {
    legsAttempted: 0,
    legsOk: 0,
    legsSkipped: 0,
    legsFailed: 0,
    listingsCanceled: 0,
    volumeUsd: 0,
    camoTakeOk: 0,
    camoTakeFail: 0,
    camoVolumeUsd: 0
  };

  const maxRounds = Math.max(0, clampToNonNegativeInt(ringCfg.maxRoundsPerSession, 0));
  let lastPair = null;
  let round = 0;

  while (!shuttingDown) {
    round += 1;
    if (maxRounds > 0 && round > maxRounds) {
      console.log(`[otc-ring] Reached maxRoundsPerSession=${maxRounds}, stop.`);
      break;
    }

    const ringOrder = shuffleArray(workers);
    const baseAmountUsd = Number(ringCfg.baseAmountUsd) || 5;
    const jitterPct = Math.max(0, Number(ringCfg.amountJitterPercent) || 0) / 100;
    const minOrderUsd = Number(swapCfg.minOrderSizeUsd) || 1.05;
    const reserveFraction = 0.95;

    // Refresh balance + oracle untuk semua worker, scan pair yang viable
    let mids = {};
    try {
      const refRes = await ringOrder[0].client.getCrossOtcReference();
      mids = isObject(refRes && refRes.data && refRes.data.mids) ? refRes.data.mids : {};
    } catch (error) {
      console.log(`[otc-ring] reference failed: ${error.message}, sleep 30s`);
      await sleep(30000);
      continue;
    }
    await Promise.all(ringOrder.map((w) => refreshOtcWorkerBalance(w, w.tag)));

    // Untuk tiap pair di allowedPairs: cek apakah ADA pasangan (maker, taker)
    // dimana min(makerSrc, takerDst) × usd ≥ minOrderUsd di salah satu direction.
    const allowedPairs = (Array.isArray(swapCfg.allowedPairs) && swapCfg.allowedPairs.length > 0
      ? swapCfg.allowedPairs.filter((p) => OTC_PAIR_SIDES[p])
      : Object.keys(OTC_PAIR_SIDES));
    const viablePairs = [];
    for (const candPair of allowedPairs) {
      const cmeta = OTC_PAIR_SIDES[candPair];
      const baseUsd = otcAssetToUsd(cmeta.baseAsset, 1, mids) || 1;
      const quoteUsd = otcAssetToUsd(cmeta.quoteAsset, 1, mids) || 1;
      let bestCapUsd = 0;
      for (let i = 0; i < ringOrder.length; i++) {
        const m = ringOrder[i];
        const t = ringOrder[(i + 1) % ringOrder.length];
        // direction "base": maker sells base, taker pays quote
        const cap1 = Math.min(
          otcGetAccountBalance(cmeta.baseAsset, m.balance) * baseUsd,
          otcGetAccountBalance(cmeta.quoteAsset, t.balance) * quoteUsd
        ) * reserveFraction;
        // direction "quote": maker sells quote, taker pays base
        const cap2 = Math.min(
          otcGetAccountBalance(cmeta.quoteAsset, m.balance) * quoteUsd,
          otcGetAccountBalance(cmeta.baseAsset, t.balance) * baseUsd
        ) * reserveFraction;
        bestCapUsd = Math.max(bestCapUsd, cap1, cap2);
      }
      if (bestCapUsd >= minOrderUsd) {
        viablePairs.push({ pair: candPair, capUsd: bestCapUsd });
      }
    }

    if (viablePairs.length === 0) {
      const balanceSummary = ringOrder.map((w) => {
        const cc = otcGetAccountBalance("CC", w.balance).toFixed(2);
        const usdcx = otcGetAccountBalance("USDCx", w.balance).toFixed(2);
        const usdc = otcGetAccountBalance("USDC", w.balance).toFixed(2);
        return `${w.tag} CC=${cc} USDCx=${usdcx} USDC=${usdc}`;
      }).join(" | ");
      console.log(`\n[otc-ring] Round ${round} ABORT: tidak ada pair viable (≥$${minOrderUsd}). ${balanceSummary}`);
      console.log(`[otc-ring] Saldo akun terlalu kecil/timpang. Top-up salah satu akun lalu retry. Sleep 5 menit...`);
      await sleep(5 * 60 * 1000);
      continue;
    }

    // Pilih pair: hindari yang baru dipakai kalau ada alternatif viable
    let pair;
    if (viablePairs.length > 1 && lastPair) {
      const filtered = viablePairs.filter((v) => v.pair !== lastPair);
      const pool = filtered.length > 0 ? filtered : viablePairs;
      pair = pool[randomIntInclusive(0, pool.length - 1)].pair;
    } else {
      pair = viablePairs[randomIntInclusive(0, viablePairs.length - 1)].pair;
    }
    lastPair = pair;
    const meta = OTC_PAIR_SIDES[pair];

    const viableLabels = viablePairs.map((v) => `${v.pair}=$${v.capUsd.toFixed(2)}`).join(", ");
    console.log(`\n[otc-ring] Round ${round}/${maxRounds || "∞"} | pair=${pair} (chosen) | viable: ${viableLabels} | ringSize=${ringOrder.length}`);

    for (let i = 0; i < ringOrder.length && !shuttingDown; i++) {
      const maker = ringOrder[i];
      const taker = ringOrder[(i + 1) % ringOrder.length];
      statsBucket.legsAttempted += 1;

      // Refresh oracle for amount calc (per-leg fresh; round-level mids dipakai
      // sebagai fallback kalau fetch gagal)
      let legMids = mids;
      try {
        const refRes = await maker.client.getCrossOtcReference();
        const fresh = isObject(refRes && refRes.data && refRes.data.mids) ? refRes.data.mids : null;
        if (fresh) legMids = fresh;
      } catch (error) {
        console.log(`${maker.tag} [otc-ring] reference fetch failed (use round mids): ${error.message}`);
      }

      const oraclePrice = Number(legMids[pair]);
      if (!Number.isFinite(oraclePrice) || oraclePrice <= 0) {
        console.log(`[otc-ring] No oracle for pair=${pair}, skip leg`);
        statsBucket.legsSkipped += 1;
        continue;
      }

      // Pilih direction berdasarkan saldo: cari kombinasi (sellDir, srcAsset, dstAsset)
      // dimana maker punya srcAsset DAN taker punya dstAsset. Auto-fit amount ke
      // saldo terkecil (dengan reserve buffer) supaya tidak skip karena saldo kecil.
      const baseAssetUsdPrice = otcAssetToUsd(meta.baseAsset, 1, legMids) || 1;
      const quoteAssetUsdPrice = otcAssetToUsd(meta.quoteAsset, 1, legMids) || 1;

      const candidates = [
        { sellDir: "base", srcAsset: meta.baseAsset, dstAsset: meta.quoteAsset, srcUsd: baseAssetUsdPrice, dstUsd: quoteAssetUsdPrice },
        { sellDir: "quote", srcAsset: meta.quoteAsset, dstAsset: meta.baseAsset, srcUsd: quoteAssetUsdPrice, dstUsd: baseAssetUsdPrice }
      ];

      let bestCandidate = null;
      for (const cand of candidates) {
        const makerSrc = otcGetAccountBalance(cand.srcAsset, maker.balance);
        const takerDst = otcGetAccountBalance(cand.dstAsset, taker.balance);
        const makerCapUsd = makerSrc * cand.srcUsd * reserveFraction;
        const takerCapUsd = takerDst * cand.dstUsd * reserveFraction;
        const capUsd = Math.min(makerCapUsd, takerCapUsd);
        if (capUsd <= 0) continue;
        if (!bestCandidate || capUsd > bestCandidate.capUsd) {
          bestCandidate = { ...cand, capUsd, makerSrc, takerDst };
        }
      }

      if (!bestCandidate) {
        console.log(`[otc-ring] skip leg: tidak ada kombinasi saldo yang muat (maker=${maker.tag}, taker=${taker.tag}, pair=${pair})`);
        statsBucket.legsSkipped += 1;
        continue;
      }

      const jitterMul = 1 + ((Math.random() * 2 - 1) * jitterPct);
      const desiredNotionalUsd = baseAmountUsd * jitterMul;
      const maxOrderUsd = Number(swapCfg.maxOrderSizeUsd) || 0;
      let notionalUsd = Math.min(desiredNotionalUsd, bestCandidate.capUsd);
      if (maxOrderUsd > 0) notionalUsd = Math.min(notionalUsd, maxOrderUsd);
      if (notionalUsd < minOrderUsd) {
        console.log(`[otc-ring] skip leg: notional capacity $${notionalUsd.toFixed(4)} < min $${minOrderUsd} (maker=${maker.tag} ${bestCandidate.srcAsset}, taker=${taker.tag} ${bestCandidate.dstAsset})`);
        statsBucket.legsSkipped += 1;
        continue;
      }

      const baseAmount = notionalUsd / baseAssetUsdPrice;
      const sellDir = bestCandidate.sellDir;

      const payload = buildSelfListingPayload(pair, legMids, baseAmount, ringCfg.selfListEdgeBps, sellDir);
      if (!payload) {
        console.log(`[otc-ring] Failed to build payload, skip leg`);
        statsBucket.legsSkipped += 1;
        continue;
      }

      // Final safety check (defensive — bestCandidate sudah seharusnya menjamin ini)
      const srcReq = Number(payload.srcAmountDecimal);
      const dstReq = Number(payload.dstAmountDecimal);
      if (bestCandidate.makerSrc < srcReq || bestCandidate.takerDst < dstReq) {
        console.log(`[otc-ring] skip leg (rounding mismatch): need src=${srcReq} ${payload.srcAsset} have=${bestCandidate.makerSrc.toFixed(4)} | need dst=${dstReq} ${payload.dstAsset} have=${bestCandidate.takerDst.toFixed(4)}`);
        statsBucket.legsSkipped += 1;
        continue;
      }

      console.log(
        `[otc-ring] LEG ${i + 1}/${ringOrder.length}: ${maker.tag} list ${payload.srcAmountDecimal} ${payload.srcAsset} → ${payload.dstAmountDecimal} ${payload.dstAsset} | taker=${taker.tag}`
      );

      // Create listing
      let listing = null;
      try {
        const listResp = await maker.client.createOtcOrder({
          side: payload.side,
          srcAmountDecimal: payload.srcAmountDecimal,
          dstAmountDecimal: payload.dstAmountDecimal,
          expiresHours: clampToNonNegativeInt(ringCfg.listingExpiresHours, 1) || 1
        });
        listing = isObject(listResp && listResp.data && listResp.data.order) ? listResp.data.order : null;
      } catch (error) {
        console.log(`${maker.tag} [otc-ring] createOrder failed: ${error.message}`);
        statsBucket.legsFailed += 1;
        continue;
      }
      if (!listing || !listing.id) {
        console.log(`${maker.tag} [otc-ring] createOrder returned no order id`);
        statsBucket.legsFailed += 1;
        continue;
      }
      openListings.set(listing.id, {
        client: maker.client,
        account: maker.account.name,
        makerProfileId: maker.profileId,
        createdAtMs: Date.now()
      });

      // Jitter delay (split half before/after camouflage attempts)
      const jitterTotalSec = randomIntInclusive(
        Math.max(1, clampToNonNegativeInt(ringCfg.legMinJitterSeconds, 600)),
        Math.max(1, clampToNonNegativeInt(ringCfg.legMaxJitterSeconds, 1800))
      );
      const half = Math.floor(jitterTotalSec / 2);
      console.log(`[otc-ring] wait ${jitterTotalSec}s with camouflage attempts...`);
      await sleep(half * 1000);
      if (shuttingDown) break;

      // Camouflage external takes for both maker and taker
      await maybeCamouflageExternalTake(maker, effectiveSwapCfg, openListings, statsBucket);
      if (shuttingDown) break;
      await maybeCamouflageExternalTake(taker, effectiveSwapCfg, openListings, statsBucket);
      if (shuttingDown) break;

      await sleep((jitterTotalSec - half) * 1000);
      if (shuttingDown) break;

      // Drift check
      let freshMids = {};
      try {
        const refRes = await maker.client.getCrossOtcReference();
        freshMids = isObject(refRes && refRes.data && refRes.data.mids) ? refRes.data.mids : {};
      } catch (error) {
        // tolerate, fallback to no drift check
        freshMids = mids;
      }
      const driftBps = oracleDriftBps(payload, freshMids);
      const maxDrift = Number(ringCfg.maxDriftBps) || 50;
      if (driftBps > maxDrift) {
        console.log(`[otc-ring] DRIFT ${driftBps.toFixed(1)}bps > ${maxDrift}, cancel listing ${listing.id.slice(0, 8)}`);
        try {
          await maker.client.cancelOtcOrder(listing.id);
          statsBucket.listingsCanceled += 1;
        } catch (error) {
          console.log(`${maker.tag} [otc-ring] cancel failed: ${error.message}`);
        }
        openListings.delete(listing.id);
        statsBucket.legsSkipped += 1;
        continue;
      }

      // Taker reserve + take
      try {
        await taker.client.reserveOtcOrder(listing.id);
        await taker.client.takeOtcOrder(listing.id);
        openListings.delete(listing.id);
        statsBucket.legsOk += 1;
        statsBucket.volumeUsd += payload.notionalUsdQuote;
        console.log(`[otc-ring] LEG ok | volume +$${payload.notionalUsdQuote.toFixed(2)}`);
        // Refresh both balances for next leg accuracy
        await Promise.all([
          refreshOtcWorkerBalance(maker, maker.tag),
          refreshOtcWorkerBalance(taker, taker.tag)
        ]);
      } catch (error) {
        const errMsg = String(error.message || "");
        if (isOtcMakerSettlementInProgressError(errMsg)) {
          // Maker wallet sedang settle — skip leg ini. Listing tidak di-cancel
          // (cancel butuh wallet yang sama yang sedang busy).
          console.log(`${taker.tag} [otc-ring] reserve skip ${listing.id.slice(0, 8)} (maker settling)`);
          statsBucket.legsSkipped += 1;
        } else {
          console.log(`${taker.tag} [otc-ring] take failed: ${errMsg}, attempting cancel`);
          try {
            await maker.client.cancelOtcOrder(listing.id);
            statsBucket.listingsCanceled += 1;
          } catch (cancelErr) {
            console.log(`${maker.tag} [otc-ring] cancel after take-fail also failed: ${cancelErr.message}`);
          }
          openListings.delete(listing.id);
          statsBucket.legsFailed += 1;
        }
      }
    }

    console.log(`[otc-ring] Round ${round} done | ok=${statsBucket.legsOk} skip=${statsBucket.legsSkipped} fail=${statsBucket.legsFailed} | volume=$${statsBucket.volumeUsd.toFixed(2)}`);
  }

  process.removeListener("SIGINT", cleanup);
  process.removeListener("SIGTERM", cleanup);

  console.log(`\n${"#".repeat(70)}`);
  console.log(`[otc-ring] Done | rounds=${round} | legsOk=${statsBucket.legsOk}/${statsBucket.legsAttempted} | volume=$${statsBucket.volumeUsd.toFixed(2)}`);
  console.log(`[otc-ring] Camouflage: takeOk=${statsBucket.camoTakeOk} fail=${statsBucket.camoTakeFail} | volume=$${statsBucket.camoVolumeUsd.toFixed(2)}`);
  console.log(`[otc-ring] Listings canceled (drift/fail): ${statsBucket.listingsCanceled}`);
  console.log(`${"#".repeat(70)}\n`);
}

async function runOtpOnlyFlow(context) {
  const { config, accounts, tokens, tokensPath } = context;
  const accountList = accounts.accounts;
  console.log(`\n${"=".repeat(70)}`);
  console.log(`[otp-mode] Request OTP untuk ${accountList.length} akun, hasil tersimpan ke tokens.json`);
  console.log(`${"=".repeat(70)}\n`);

  const summary = { ok: [], failed: [] };

  for (let i = 0; i < accountList.length; i++) {
    const account = accountList[i];
    const tag = `[${i + 1}/${accountList.length}] ${account.name}`;
    const selectedEmail = String(account.email || "").trim();

    console.log(`\n${"-".repeat(70)}`);
    console.log(`${tag} | ${maskEmail(selectedEmail)}`);
    console.log(`${"-".repeat(70)}`);

    if (!selectedEmail || !selectedEmail.includes("@")) {
      console.log(`[error] ${tag}: email invalid, skip`);
      summary.failed.push({ name: account.name, reason: "invalid-email" });
      continue;
    }

    const accountToken = tokens.accounts[account.name] || normalizeTokenProfile({});
    tokens.accounts[account.name] = accountToken;

    const accountConfig = cloneRuntimeConfig(config);
    applyTokenProfileToConfig(accountConfig, accountToken);

    let checkpointRefreshCount = 0;
    let lastVercelRefreshAt = String(accountToken.security.lastVercelRefreshAt || "").trim();
    const markCheckpointRefresh = () => {
      checkpointRefreshCount += 1;
      lastVercelRefreshAt = new Date().toISOString();
    };

    const client = new RootsFiApiClient(accountConfig);

    try {
      if (true /* skipVercelChallenge: Cloudflare */) {
        console.log(`[step] ${tag}: Browser challenge skipped (website uses Cloudflare)`);
      } else {
        console.log(`[step] ${tag}: Browser challenge (ambil _vcrcs)`);
        await refreshVercelSecurityCookies(
          client,
          accountConfig,
          `OTP-mode fresh browser challenge (${account.name})`,
          markCheckpointRefresh
        );
      }

      console.log(`[step] ${tag}: Send OTP ke ${maskEmail(selectedEmail)}`);
      const sendOtpResponse = await sendOtpWithCheckpointRecovery(
        client,
        selectedEmail,
        accountConfig,
        markCheckpointRefresh
      );
      const otpId = sendOtpResponse && sendOtpResponse.data ? sendOtpResponse.data.otpId : null;
      if (!otpId) {
        throw new Error("send-otp tidak return otpId");
      }
      console.log(`[info] ${tag}: OTP terkirim | otpId=${maskSecret(otpId, 8, 6)}`);

      const otpCode = await promptOtpCode();
      if (!/^\d{4,8}$/.test(otpCode)) {
        throw new Error("OTP harus 4-8 digit angka");
      }

      console.log(`[step] ${tag}: Verify OTP`);
      const verifyResponse = await client.verifyOtp({
        email: selectedEmail,
        otpId,
        otpCode
      });
      const nextStep = verifyResponse && verifyResponse.data ? verifyResponse.data.nextStep : null;
      console.log(`[info] ${tag}: verify-otp nextStep=${nextStep || "unknown"}`);

      console.log(`[step] ${tag}: Sync onboard`);
      await client.syncAccount(accountConfig.paths.onboard);

      const pendingResp = await client.getPending(accountConfig.paths.onboard);
      const pendingData = pendingResp && pendingResp.data ? pendingResp.data : {};
      if (pendingData.pending) {
        if (pendingData.alreadyActive === true) {
          console.log(`[step] ${tag}: Finalize returning account`);
          await client.finalizeReturning();
        } else {
          console.log(`[warn] ${tag}: Akun masih pending & belum alreadyActive (skip finalize)`);
        }
      }

      console.log(`[step] ${tag}: Sync bridge`);
      await client.syncAccount(accountConfig.paths.bridge);

      tokens.accounts[account.name] = applyClientStateToTokenProfile(
        accountToken,
        client,
        checkpointRefreshCount,
        lastVercelRefreshAt
      );
      await saveTokensSerial(tokensPath, tokens);
      console.log(`[done] ${tag}: Sesi tersimpan ke tokens.json`);
      summary.ok.push(account.name);
    } catch (error) {
      const msg = error && error.message ? error.message : String(error);
      console.log(`[error] ${tag}: ${msg}`);
      summary.failed.push({ name: account.name, reason: msg });
      try {
        tokens.accounts[account.name] = applyClientStateToTokenProfile(
          accountToken,
          client,
          checkpointRefreshCount,
          lastVercelRefreshAt
        );
        await saveTokensSerial(tokensPath, tokens);
      } catch (saveError) {
        console.log(`[warn] ${tag}: gagal save tokens.json (${saveError.message})`);
      }
    }
  }

  console.log(`\n${"=".repeat(70)}`);
  console.log(`[otp-mode] Selesai | OK=${summary.ok.length} | Failed=${summary.failed.length}`);
  if (summary.ok.length > 0) console.log(`  OK: ${summary.ok.join(", ")}`);
  if (summary.failed.length > 0) {
    for (const f of summary.failed) console.log(`  FAIL ${f.name}: ${f.reason}`);
  }
  console.log(`${"=".repeat(70)}\n`);
  return summary;
}

async function run() {
  if (typeof fetch !== "function") {
    throw new Error("Global fetch is not available. Use Node.js 18+.");
  }

  const args = parseArgs(process.argv.slice(2));
  if (args.help) {
    printHelp();
    return;
  }

  const configPath = path.resolve(process.cwd(), args.configFile);
  const accountsPath = path.resolve(process.cwd(), args.accountsFile);
  const tokensPath = path.resolve(process.cwd(), args.tokensFile);

  const [rawConfig, rawAccounts, rawTokens] = await Promise.all([
    readJson(configPath, "config"),
    readJson(accountsPath, "accounts"),
    readOptionalJson(tokensPath, "tokens")
  ]);

  const config = normalizeConfig(rawConfig);

  setHourlyMaxTx(config.send.hourlyMaxTx);
  console.log(
    `[init] Safety: minHoldBalanceCc=${config.safety.minHoldBalanceCc}, ` +
    `hourlyMaxTx=${HOURLY_MAX_TX_PER_ACCOUNT}/hr per account (${hourlyCapSource})`
  );
  console.log(
    `[init] HourlyCap: mode=${hourlyCapSource === "config" ? "pinned" : "adaptive"} | ` +
    `auto-learn from server HTTP 400, auto-wait until window resets`
  );

  {
    const tg = config.telegram || {};
    const tgEnabled = tg.enabled && tg.botToken && Array.isArray(tg.allowedChatIds) && tg.allowedChatIds.length > 0;
    const autoEnabled = tgEnabled && tg.autoReport && tg.autoReport.enabled;
    console.log(
      `[init] Telegram: enabled=${Boolean(tgEnabled)} | autoReport=${Boolean(autoEnabled)} ` +
      `(minInterval=${tg.autoReport ? tg.autoReport.minIntervalMinutes : 0}m, ` +
      `cycleStart=${tg.autoReport ? tg.autoReport.reportAtCycleStart : false}, ` +
      `hourlyCap=${tg.autoReport ? tg.autoReport.reportOnHourlyCapReached : false})`
    );
  }

  const accounts = normalizeAccounts(rawAccounts);
  const legacyCookies = extractLegacyAccountCookies(rawAccounts);
  const tokens = normalizeTokens(rawTokens, accounts);

  for (const accountEntry of accounts.accounts) {
    const profile = tokens.accounts[accountEntry.name] || normalizeTokenProfile({});
    if (!String(profile.cookie || "").trim() && legacyCookies.has(accountEntry.name)) {
      profile.cookie = legacyCookies.get(accountEntry.name);
    }
    tokens.accounts[accountEntry.name] = profile;
  }

  // Keep generated token file in sync with current accounts and token schema.
  await saveTokensSerial(tokensPath, tokens);

  // Load recipients
  const recipientsInfo = await loadRecipients(config.recipientFile);
  if (recipientsInfo.missing) {
    console.log(`[warn] Recipient file not found: ${recipientsInfo.absolutePath}`);
  } else {
    console.log(`[init] Recipients loaded: ${recipientsInfo.recipients.length}`);
    if (recipientsInfo.invalidLines.length > 0) {
      console.log(`[warn] Invalid recipient rows: ${recipientsInfo.invalidLines.length}`);
    }
  }

  // Show accounts summary
  console.log(`[init] Total accounts: ${accounts.accounts.length}`);
  for (const acc of accounts.accounts) {
    const tokenProfile = tokens.accounts[acc.name];
    const hasToken = tokenProfile && String(tokenProfile.cookie || "").trim();
    console.log(`  - ${acc.name} (${maskEmail(acc.email)}) [${hasToken ? "has-token" : "no-token"}]`);
  }

  // Proxy support disabled — direct connection only\n  // const accountNamesForProxy = accounts.accounts.map((a) => a.name);\n  // await loadProxies(DEFAULT_PROXY_FILE, accountNamesForProxy);

  // Prompt for send mode
  const sendMode = await promptSendMode();
  console.log(`\n[init] Selected mode: ${sendMode}`);

  if (sendMode === "otp") {
    const otpSelection = await promptAccountSelection(accounts.accounts);
    const otpAccounts = otpSelection.selectedAccounts;
    console.log(`\n[init] OTP mode - akun terpilih: ${otpAccounts.length}`);
    await runOtpOnlyFlow({
      config,
      accounts: { ...accounts, accounts: otpAccounts },
      tokens,
      tokensPath,
      args
    });
    return;
  }

  if (sendMode === "otc-maker" || sendMode === "otc-taker" || sendMode === "otc-maker-taker") {
    // Initialize ETH auto-fill from master wallet (continuous monitoring)
    initEthAutoFill(rawAccounts.masterWalletPrivateKey);

    const otcAccounts = accounts.accounts;
    console.log(`\n[init] OTC mode=${sendMode} - using all ${otcAccounts.length} accounts`);
    const otcContext = {
      config,
      accounts: { ...accounts, accounts: otcAccounts },
      tokens,
      tokensPath,
      args,
      otcMode: sendMode
    };
    if (sendMode === "otc-taker") {
      await runOtcTradingFlow(otcContext);
    } else if (sendMode === "otc-maker") {
      await runOtcMakerFlow(otcContext);
    } else {
      await runOtcMakerTakerFlow(otcContext);
    }
    return;
  }

  if (sendMode === "external" && (recipientsInfo.missing || recipientsInfo.recipients.length === 0)) {
    throw new Error("External mode requires recipient.txt with valid recipients");
  }

  // Validate internal mode - check accounts have addresses
  if (sendMode === "internal") {
    const accountsWithAddress = accounts.accounts.filter(acc => String(acc.address || "").trim());
    if (accountsWithAddress.length < 2) {
      throw new Error("Internal mode requires at least 2 accounts with 'address' field in accounts.json. Please fill in the cantonPartyId for each account.");
    }
    console.log(`[init] Accounts with address: ${accountsWithAddress.length}/${accounts.accounts.length}`);

    const missingAddress = accounts.accounts.filter(acc => !String(acc.address || "").trim());
    if (missingAddress.length > 0) {
      console.log(`[warn] Accounts without address (will be skipped): ${missingAddress.map(a => a.name).join(", ")}`);
    }
  }

  // Prompt for account selection (for external and balance-only modes)
  // For internal mode, use all accounts with valid addresses
  let selectedAccounts = accounts.accounts;
  if (sendMode === "external" || sendMode === "balance-only") {
    const accountSelection = await promptAccountSelection(accounts.accounts);
    selectedAccounts = accountSelection.selectedAccounts;

    const accountNames = selectedAccounts.map(a => a.name).join(", ");
    console.log(`\n[init] Selected accounts (${selectedAccounts.length}): ${accountNames}`);
  } else if (sendMode === "internal") {
    // For internal mode, use all accounts with valid addresses
    selectedAccounts = accounts.accounts.filter(acc => String(acc.address || "").trim());
    console.log(`\n[init] Internal mode - using all ${selectedAccounts.length} accounts with addresses (sequential cross-send)`);
  }

  const cycleContext = {
    config,
    accounts: { ...accounts, accounts: selectedAccounts },
    tokens,
    tokensPath,
    sendMode,
    recipientsInfo,
    args,
    legacyCookies
  };

  // Daily loop
  let cycleCount = 0;
  const maxConsecutiveErrors = 3;
  let consecutiveErrors = 0;

  while (true) {
    cycleCount++;

    try {
      // Reload tokens before each cycle (in case manually edited)
      const freshTokens = await readOptionalJson(tokensPath, "tokens");
      const reloadedTokens = normalizeTokens(freshTokens, cycleContext.accounts);

      for (const accountEntry of cycleContext.accounts.accounts) {
        const profile = reloadedTokens.accounts[accountEntry.name] || normalizeTokenProfile({});
        if (!String(profile.cookie || "").trim() && cycleContext.legacyCookies.has(accountEntry.name)) {
          profile.cookie = cycleContext.legacyCookies.get(accountEntry.name);
        }
        cycleContext.tokens.accounts[accountEntry.name] = profile;
      }

      // Run the daily cycle
      const cycleResult = await runDailyCycle(cycleContext);

      // Reset consecutive errors on success
      consecutiveErrors = 0;

      // Balance-only mode: exit after checking all accounts (no daily loop)
      if (sendMode === "balance-only") {
        console.log(`\n${"=".repeat(70)}`);
        console.log(`[cycle] Balance check completed!`);
        console.log(`[cycle] Results: ${cycleResult.successful.length} successful, ${cycleResult.failed.length} failed`);
        console.log(`[cycle] Duration: ${formatDuration(cycleResult.cycleDuration)}`);
        console.log(`${"=".repeat(70)}\n`);
        break; // Exit the while loop — done
      }

      // Calculate time until next cycle (next midnight UTC)
      const now = new Date();
      const nextCycleTime = getNextMidnightUTC();
      const waitMs = Math.max(0, nextCycleTime - now);

      if (waitMs > 0 && !args.dryRun) {
        console.log(`\n${"=".repeat(70)}`);
        console.log(`[cycle] Daily cycle #${cycleCount} completed!`);
        console.log(`[cycle] Results: ${cycleResult.successful.length} successful, ${cycleResult.failed.length} failed`);
        console.log(`[cycle] Duration: ${formatDuration(cycleResult.cycleDuration)}`);
        console.log(`[cycle] Next cycle at: ${formatUTCTime(nextCycleTime)}`);
        console.log(`[cycle] Waiting: ${formatDuration(waitMs)}`);
        console.log(`${"=".repeat(70)}\n`);

        await sleep(waitMs);
      }

    } catch (error) {
      consecutiveErrors++;
      console.error(`\n[error] Cycle #${cycleCount} failed: ${error.message}`);

      if (consecutiveErrors >= maxConsecutiveErrors) {
        console.error(`[fatal] ${maxConsecutiveErrors} consecutive errors. Stopping bot.`);
        throw error;
      }

      // Wait 5 minutes before retrying on error
      const retryDelayMs = 5 * 60 * 1000;
      console.log(`[loop] Retrying in ${formatDuration(retryDelayMs)}... (${consecutiveErrors}/${maxConsecutiveErrors} errors)`);
      await sleep(retryDelayMs);
    }
  }
}

run().catch((error) => {
  console.error(`[error] ${error && error.message ? error.message : String(error)}`);
  process.exitCode = 1;
});
