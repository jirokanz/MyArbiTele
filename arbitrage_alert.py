#!/usr/bin/env python3
"""
STANDALONE LIVE ARBITRAGE REPORTER
- Exchange order: Binance → Pionex → Luno → Hata → Sinegy → KDX → MX
- Public WebSocket for Binance, Pionex, Luno, Hata, Sinegy
- REST fetch for KDX and MX (Sinegy has REST fallback)
- No API keys required for market data
- Reads TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID from api.txt
- Duplicate prevention: time-based cooldown (10 minutes) per (pair, buy_exchange, sell_exchange)
- Shows REAL fillable volume from order books
- USDT/MYR rate fetched once every 60s in background, shared across all pairs
- Binance/Luno/Hata/Sinegy REST fallbacks used on-demand (cache miss only)
- KDX and MX have no WS; fetched fresh via _fetch_all_depths() at the start of
  each 10-minute monitor() scan cycle (no background poller)
"""

import os
import sys
import json
import time
import ssl
import certifi
import threading
import logging
import random
import queue
import math
from decimal import Decimal
from typing import Dict, List, Optional, Tuple, Any

import requests

# ----------------------------------------------------------------------
# Optional dependencies
# ----------------------------------------------------------------------
try:
    import websocket
    WEBSOCKET_AVAILABLE = True
except ImportError:
    WEBSOCKET_AVAILABLE = False
    print("⚠️ websocket-client not installed. Install with: pip install websocket-client")

try:
    from curl_cffi import requests as curl_requests
    CURL_CFI_AVAILABLE = True
except ImportError:
    CURL_CFI_AVAILABLE = False
    print("⚠️ curl_cffi not installed. Hata WS disabled. Install with: pip install curl_cffi")

# ----------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------
CONFIG_FILE = "api.txt"

def load_config() -> dict:
    config = {}
    if not os.path.exists(CONFIG_FILE):
        print(f"⚠️ {CONFIG_FILE} not found. Only Telegram will work if tokens are set elsewhere.")
        return config
    with open(CONFIG_FILE, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            if '=' not in line:
                continue
            key, val = line.split('=', 1)
            key = key.strip().upper()
            val = val.strip().strip('"').strip("'")
            config[key] = val
    return config

CONFIG = load_config()

TELEGRAM_TOKEN = CONFIG.get('TELEGRAM_BOT_TOKEN')
TELEGRAM_CHAT_ID = CONFIG.get('TELEGRAM_CHAT_ID')
MIN_PROFIT_PCT = Decimal(CONFIG.get('PROFIT_PERCENTAGE', '0.5'))

# ----------------------------------------------------------------------
# Logging
# ----------------------------------------------------------------------
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger("StandaloneReporter")

class WebSocketFilter(logging.Filter):
    def filter(self, record):
        msg = record.getMessage()
        if ("opcode=8" in msg
                or "object has no attribute 'sock'" in msg
                or "502 Bad Gateway" in msg
                or "503 Service Unavailable" in msg):
            return False
        return True
logging.getLogger("websocket").addFilter(WebSocketFilter())
# Fully silenced (was ERROR): every WS manager's own on_error/except handler
# now logs the same connection failures itself, tagged with the exchange
# name (e.g. "Binance WS error: ..."), so the library's untagged internal
# "<error> - goodbye" messages would just be a duplicate, less useful copy.
logging.getLogger("websocket").setLevel(logging.CRITICAL)

# ----------------------------------------------------------------------
# Fee constants & Exchange order (hierarchy)
# ----------------------------------------------------------------------
TAKER_FEES = {
    'binance': Decimal('0.001'),   # 0.1%
    'pionex': Decimal('0.0005'),   # 0.05%
    'luno': Decimal('0.006'),      # 0.6%
    'hata': Decimal('0.004'),      # 0.4%
    'sinegy': Decimal('0.0025'),   # 0.25%
    'kdx': Decimal('0.006'),       # 0.6%
    'mx': Decimal('0.005'),        # 0.5%
}

EXCHANGE_ORDER = ['binance', 'pionex', 'luno', 'hata', 'sinegy', 'kdx', 'mx']
USDT_EXCHANGES = {'binance', 'pionex'}  # exchanges that trade in USDT, not MYR

# ----------------------------------------------------------------------
# Live toggles — controlled via keypress while the bot runs (see
# Reporter._start_keypress_listener). Read from get_prices()/should_alert()
# on every scan, so a toggle takes effect on the very next update.
# ----------------------------------------------------------------------
ENABLED_EXCHANGES = set(EXCHANGE_ORDER)  # all exchanges on by default
REVERSE_ONLY_MODE = False                # when True: only 'reverse' and 'myr' arb_types alert
_exchange_state_lock = threading.Lock()

EXCHANGE_TOGGLE_KEYS = {
    'b': 'binance',
    'p': 'pionex',
    'l': 'luno',
    'h': 'hata',
    's': 'sinegy',
    'k': 'kdx',
    'm': 'mx',
}

def should_alert(opp: Dict) -> bool:
    """Central filter applied before every alert — profit threshold plus
    the live reverse-only-mode toggle. myr-to-myr opportunities always pass
    the reverse-only filter regardless of the toggle state."""
    if opp['profit_pct'] < MIN_PROFIT_PCT:
        return False
    if REVERSE_ONLY_MODE and opp['arb_type'] not in ('reverse', 'myr'):
        return False
    return True

# ----------------------------------------------------------------------
# Referral links – sent periodically alongside arbitrage alerts
# ----------------------------------------------------------------------
REFERRAL_LINKS = {
    'Luno': 'https://www.luno.com/wallet/rewards/enter_code?code=AXKAG',
    'Hata': 'https://hata.io/signup?ref=AF01X2KFAA',
    'Sinegy': 'https://exchange.sinegy.com/signup?ref=4f099',
    'MX': 'https://app.mx.exchange/sign-up?elink=lukman',
    'KDX': 'https://kdx.com.my/register?invite_code=8hF1P',
    'Binance': 'https://www.binance.com/register?ref=ZBK9WIK9',
    'Pionex': 'https://accounts.pionex.com/en/signUp?r=xYlRQCZj',
}
REFERRAL_INTERVAL = 600  # 10 minutes in seconds (kept for reference)
REFERRAL_EVERY_N_ALERTS = 10  # fire referral message every N arb alerts
_alert_count = 0               # global arb alert counter
_alert_count_lock = threading.Lock()

# ----------------------------------------------------------------------
# Shared, thread-safe Telegram sender
# Enforces a global minimum spacing between ANY two sends (arb alerts and
# referral broadcasts share one chat, so they must not be sent concurrently
# or back-to-back faster than Telegram's ~1 msg/sec per-chat limit).
# ----------------------------------------------------------------------
_last_telegram_send_time = 0.0
TELEGRAM_MIN_INTERVAL = 3.5  # seconds; channels/groups are limited to ~20 msgs/min (1 per 3s), with margin

# ----------------------------------------------------------------------
# Send queue — a single dedicated thread drains this one message at a time.
# Callers (monitor loop, referral broadcaster) just enqueue and move on
# immediately; they never block on a slow send, a 429 backoff, or a
# connection-reset retry. Bounded so a prolonged Telegram outage can't
# grow this without limit.
# ----------------------------------------------------------------------
_telegram_queue: "queue.Queue" = queue.Queue(maxsize=200)

def _telegram_sender_worker():
    """Drains _telegram_queue one message at a time, forever."""
    while True:
        payload, context = _telegram_queue.get()
        try:
            _telegram_post(payload, context)
        finally:
            _telegram_queue.task_done()

def _telegram_post(payload: dict, context: str) -> bool:
    """Send with rate-limiting and retry-with-backoff. Only ever called from
    the single _telegram_sender_worker thread, so no lock is needed here —
    serialization comes from there being just one caller, not from mutual
    exclusion.
    Returns True if sent successfully, False if it permanently failed."""
    global _last_telegram_send_time
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    max_attempts = 3
    for attempt in range(1, max_attempts + 1):
        resp = None
        err = None
        wait = TELEGRAM_MIN_INTERVAL - (time.time() - _last_telegram_send_time)
        if wait > 0:
            time.sleep(wait)
        try:
            resp = requests.post(url, data=payload, timeout=10)
        except (requests.exceptions.ConnectionError, requests.exceptions.Timeout) as e:
            err = e
        except Exception as e:
            err = e
        finally:
            _last_telegram_send_time = time.time()

        if resp is not None and resp.ok:
            return True

        retry_after = None
        if resp is not None:
            if resp.status_code == 429:
                try:
                    retry_after = resp.json().get('parameters', {}).get('retry_after')
                except Exception:
                    retry_after = None
                logger.warning(f"{context} rate-limited by Telegram (attempt {attempt}/{max_attempts}): "
                                f"retry after {retry_after}s")
            else:
                logger.warning(f"{context} send failed (attempt {attempt}/{max_attempts}): "
                                f"HTTP {resp.status_code} - {resp.text[:200]}")
        elif err is not None:
            logger.warning(f"{context} send failed (attempt {attempt}/{max_attempts}): {err}")

        if attempt < max_attempts:
            backoff = retry_after if retry_after else 2 * attempt
            _last_telegram_send_time = time.time() + backoff - TELEGRAM_MIN_INTERVAL
            time.sleep(backoff)
    logger.warning(f"{context} send permanently failed after {max_attempts} attempts.")
    return False

def _enqueue_telegram(payload: dict, context: str) -> bool:
    """Queue a message for the sender thread, tolerating a full queue.
    Returns True if it was enqueued."""
    try:
        _telegram_queue.put_nowait((payload, context))
        return True
    except queue.Full:
        logger.warning(f"Telegram send queue full — dropping {context}.")
        return False


def _enqueue_alert(payload: dict, context: str, cooldown_dict: dict, key, now: float) -> bool:
    """_enqueue_telegram, plus starting the cooldown for this key once the
    alert is actually queued for delivery — shared by send_telegram_alert
    and send_triangle_alert so both cooldown dicts stay in sync with what
    was really sent (not just computed).

    The cooldown write is done under _cooldown_lock *before* enqueueing so
    that a concurrent caller (e.g. _on_price_update WS thread racing with
    monitor()) that reads the dict between our check and our write cannot
    slip through and send a duplicate."""
    with _cooldown_lock:
        # Re-check under the lock — another thread may have written the key
        # between our caller's check and now.
        if now - cooldown_dict.get(key, 0) < ALERT_COOLDOWN:
            return False
        cooldown_dict[key] = now
    if _enqueue_telegram(payload, context):
        _increment_alert_count()
        return True
    # Enqueue failed (queue full) — clear the timestamp so the next attempt
    # isn't silently suppressed by a cooldown that never actually sent.
    with _cooldown_lock:
        cooldown_dict.pop(key, None)
    return False


def send_referral_message():
    """Send the referral/signup links message via Telegram in 2-column layout."""
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    items = list(REFERRAL_LINKS.items())
    rows = []
    for i in range(0, len(items), 2):
        left_name, left_url = items[i]
        if i + 1 < len(items):
            right_name, right_url = items[i + 1]
            rows.append(f"• [{left_name}]({left_url})   • [{right_name}]({right_url})")
        else:
            rows.append(f"• [{left_name}]({left_url})")
    msg = "🚀 Don't just watch. Sign up and execute:\n\n" + "\n".join(rows)
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": msg,
        "parse_mode": "Markdown",
        "disable_web_page_preview": True,
    }
    _enqueue_telegram(payload, "Referral message")


def _increment_alert_count():
    """Increment arb alert counter and fire referral message every N alerts."""
    global _alert_count
    with _alert_count_lock:
        _alert_count += 1
        should_send = (_alert_count % REFERRAL_EVERY_N_ALERTS == 0)
    if should_send:
        send_referral_message()

def sort_exchanges(exchanges: List[str]) -> List[str]:
    return sorted(exchanges, key=lambda x: EXCHANGE_ORDER.index(x) if x in EXCHANGE_ORDER else len(EXCHANGE_ORDER))

# ----------------------------------------------------------------------
# Price Cache
# ----------------------------------------------------------------------
class PriceDepthCache:
    def __init__(self):
        self._depth = {}
        self._lock = threading.Lock()
        self._usdt_myr = None          # latest rate (could be None if not yet fetched)
        self._usdt_myr_time = 0
        self._on_update = None         # optional callback(exchange, symbol), fired on every update_depth

    def set_on_update(self, callback):
        """Register a callback(exchange, symbol) fired right after every update_depth call,
        so callers can react to a fresh price the instant it arrives instead of waiting
        for the next periodic scan."""
        self._on_update = callback

    def update_depth(self, exchange: str, symbol: str, bids: list, asks: list):
        key = (exchange, symbol)
        with self._lock:
            self._depth[key] = {
                'bids': [(Decimal(str(p)), Decimal(str(q))) for p, q in bids[:10]],
                'asks': [(Decimal(str(p)), Decimal(str(q))) for p, q in asks[:10]],
                'time': time.time()
            }
        # Fire outside the lock so a slow/buggy callback can't block other cache writers.
        if self._on_update:
            try:
                self._on_update(exchange, symbol)
            except Exception as e:
                logger.warning(f"on_update callback failed for {exchange}/{symbol}: {e}")

    def get_depth(self, exchange: str, symbol: str, max_age: float = 10.0) -> Optional[dict]:
        key = (exchange, symbol)
        with self._lock:
            entry = self._depth.get(key)
            if entry and (time.time() - entry['time']) < max_age:
                return {
                    'bids': entry['bids'][:],
                    'asks': entry['asks'][:],
                    'time': entry['time']
                }
        return None

    def set_usdt_myr(self, rate: Optional[float]):
        """Store the latest rate (could be None if fetch failed)."""
        with self._lock:
            self._usdt_myr = rate
            self._usdt_myr_time = time.time()

    def get_usdt_myr(self) -> Optional[float]:
        """Return the latest cached rate (no expiry – updater thread refreshes every 60s)."""
        with self._lock:
            return self._usdt_myr

# ----------------------------------------------------------------------
# USDT/MYR rate – now fetched only by the background updater
# ----------------------------------------------------------------------
def get_usdt_myr_rate() -> Optional[float]:
    """Attempt to fetch USDT/MYR from CoinGecko; fallback to yfinance (quiet)."""
    # Primary: CoinGecko
    try:
        resp = requests.get(
            "https://api.coingecko.com/api/v3/simple/price",
            params={"ids": "tether", "vs_currencies": "myr"},
            timeout=10
        )
        if resp.ok:
            data = resp.json()
            rate = data.get("tether", {}).get("myr")
            if rate and rate > 0:
                return float(rate)
    except Exception:
        pass

    # Fallback: yfinance (silent)
    try:
        import yfinance as yf
        import io, contextlib
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            ticker = yf.Ticker("MYR=X")
            hist = ticker.history(period="1d", interval="1m")
        if not hist.empty:
            rate = hist['Close'].iloc[-1]
            if rate and rate > 0:
                return float(rate)
    except Exception:
        pass
    return None

# ----------------------------------------------------------------------
# REST fallbacks for exchanges that use them (Binance, Luno, Hata, KDX, MX)
# (Pionex and Sinegy are WS‑only, no REST fallback for order books)
# ----------------------------------------------------------------------
def _safe_get_json(url: str, params: dict = None, timeout: float = 5, headers: dict = None) -> Optional[dict]:
    """Shared GET-and-parse-JSON boilerplate for REST fallbacks: issues the
    request and returns the parsed JSON body on HTTP 200. Returns None on
    any non-200 status, network error, or unparseable body — callers just
    treat None as "no data this attempt" the same way they already did.
    A caller that needs to react to a specific non-200 status (e.g. Pionex's
    429 rate-limit logging) should call requests.get directly instead."""
    try:
        resp = requests.get(url, params=params, timeout=timeout, headers=headers)
        if resp.status_code == 200:
            return resp.json()
    except Exception:
        pass
    return None


def rest_fetch_binance_orderbook(symbol: str) -> Optional[dict]:
    data = _safe_get_json("https://api.binance.com/api/v3/depth", params={'symbol': symbol, 'limit': 10})
    if data and data.get('bids') and data.get('asks'):
        bids = [(float(b[0]), float(b[1])) for b in data['bids']]
        asks = [(float(a[0]), float(a[1])) for a in data['asks']]
        return {'bids': bids, 'asks': asks}
    return None

def rest_fetch_luno_orderbook(pair: str) -> Optional[dict]:
    data = _safe_get_json("https://api.luno.com/api/1/orderbook", params={"pair": pair})
    if data and data.get('bids') and data.get('asks'):
        bids = [(float(b['price']), float(b['volume'])) for b in data['bids']]
        asks = [(float(a['price']), float(a['volume'])) for a in data['asks']]
        return {'bids': bids, 'asks': asks}
    return None

def rest_fetch_hata_orderbook(pair: str) -> Optional[dict]:
    data = _safe_get_json("https://my-api.hata.io/orderbook/api/orderbook", params={"pair_name": pair})
    if not data:
        return None
    if 'data' in data:
        data = data['data']
    bids = data.get('bids', [])
    asks = data.get('asks', [])
    if bids and asks:
        def vol(level):
            return level.get('qty', level.get('volume'))
        bid_depth = [(float(b['price']), float(vol(b))) for b in bids[:10] if vol(b) is not None]
        ask_depth = [(float(a['price']), float(vol(a))) for a in asks[:10] if vol(a) is not None]
        if bid_depth and ask_depth:
            return {'bids': bid_depth, 'asks': ask_depth}
    return None

def rest_fetch_kdx_ticker(pair: str) -> Optional[dict]:
    """Fetch real order book depth from KDX /market/orderbook (buy/sell keys)."""
    base = pair[:-3]
    market = f"MYR-{base}"
    data = _safe_get_json("https://api.kdx.com.my/public/v1/market/orderbook", params={"market": market})
    if not data:
        return None
    book = data.get('data', {})
    bids_raw = book.get('buy', [])
    asks_raw = book.get('sell', [])
    if bids_raw and asks_raw:
        bids = [(float(b['rate']), float(b['quantity'])) for b in bids_raw[:10]]
        asks = [(float(a['rate']), float(a['quantity'])) for a in asks_raw[:10]]
        if bids and asks:
            return {'bids': bids, 'asks': asks}
    return None

def rest_fetch_mx_orderbook(pair: str) -> Optional[dict]:
    data = _safe_get_json("https://openapi.mx.exchange/api/1/orderbooks", params={"pair": pair})
    if not data:
        return None
    bids = data.get('bids', [])
    asks = data.get('asks', [])
    if bids and asks:
        bid_depth = [(float(b['price']), float(b.get('volume', b.get('amount', 0)))) for b in bids]
        ask_depth = [(float(a['price']), float(a.get('volume', a.get('amount', 0)))) for a in asks]
        return {'bids': bid_depth, 'asks': ask_depth}
    return None

def rest_fetch_sinegy_orderbook(pair: str) -> Optional[dict]:
    """Fetch real order book depth from Sinegy /market/depth.
    pair format: BTCMYR → symbol MYR_BTC
    Response: bids/asks are [price, qty, []] arrays.
    """
    asset = pair[:-3]
    symbol = f"MYR_{asset}"
    data = _safe_get_json("https://exchange-api.sinegy.com/market/depth", params={"symbol": symbol, "limit": 10})
    if not data or data.get('status') != 'Success':
        return None
    book = data.get('data', {})
    bids_raw = book.get('bids', [])
    asks_raw = book.get('asks', [])
    if bids_raw and asks_raw:
        bids = [(float(b[0]), float(b[1])) for b in bids_raw if len(b) >= 2]
        asks = [(float(a[0]), float(a[1])) for a in asks_raw if len(a) >= 2]
        if bids and asks:
            return {'bids': bids, 'asks': asks}
    return None

# ----------------------------------------------------------------------
# WebSocket Managers (ordered: Binance, Pionex, Luno, Hata, Sinegy)
# ----------------------------------------------------------------------
class ReconnectBackoff:
    """Shared exponential-backoff-with-jitter helper for WS reconnect loops.
    Each manager owns its own instance so caps can differ per exchange, but
    the arithmetic lives in one place instead of being copy-pasted five times.

    reset() on a clean connect/disconnect cycle; next_delay() before sleeping
    ahead of a reconnect attempt — it also advances the internal backoff.
    """
    def __init__(self, base: float = 5.0, cap: float = 60.0):
        self.base = base
        self.cap = cap
        self._current = base

    def reset(self):
        self._current = self.base

    def next_delay(self) -> float:
        delay = self._current + random.uniform(0, self._current * 0.25)
        self._current = min(self._current * 2, self.cap)
        return delay


class BinancePublicWSManager:
    WS_BASE = "wss://stream.binance.com:9443"
    def __init__(self, symbols: List[str], cache: PriceDepthCache):
        self.symbols = symbols
        self.cache = cache
        self._running = False
        self._ws = None
        self._thread = None

    def _connect(self):
        if not self.symbols:
            return
        streams = '/'.join([f"{s.lower()}@depth10@100ms" for s in self.symbols])
        url = f"{self.WS_BASE}/stream?streams={streams}"
        def on_message(ws, msg):
            try:
                data = json.loads(msg)
                stream = data.get('stream')
                if stream and stream.endswith('@depth10@100ms'):
                    symbol = stream.replace('@depth10@100ms', '').upper()
                    depth = data.get('data', {})
                    asks = [(float(a[0]), float(a[1])) for a in depth.get('asks', [])]
                    bids = [(float(b[0]), float(b[1])) for b in depth.get('bids', [])]
                    if bids and asks:
                        self.cache.update_depth('binance', symbol, bids, asks)
            except Exception:
                pass
        def on_error(ws, error):
            logger.warning(f"Binance WS error: {error}")
        backoff = ReconnectBackoff(base=5, cap=120)
        while self._running:
            try:
                self._ws = websocket.WebSocketApp(url, on_message=on_message, on_error=on_error)
                self._ws.run_forever(sslopt={"ca_certs": certifi.where()}, ping_interval=30, ping_timeout=10)
                backoff.reset()  # reset on clean exit
            except Exception as e:
                logger.warning(f"Binance WS exception: {e}")
            if self._running:
                sleep_for = backoff.next_delay()
                logger.debug(f"Binance WS reconnecting in {sleep_for:.1f}s")
                time.sleep(sleep_for)

    def start(self):
        if not WEBSOCKET_AVAILABLE or not self.symbols:
            return
        self._running = True
        self._thread = threading.Thread(target=self._connect, daemon=True)
        self._thread.start()
        logger.info(f"Binance WS: connecting to {len(self.symbols)} symbols")

    def stop(self):
        self._running = False
        if self._ws:
            try:
                self._ws.close()
            except:
                pass

# ================================================================
# FIXED PIONEX WEBSOCKET MANAGER (correct protocol)
# ================================================================
class TokenBucket:
    """Thread-safe token bucket for rate limiting REST calls.

    capacity  – max burst size (tokens)
    rate      – tokens refilled per second
    """
    def __init__(self, capacity: float, rate: float):
        self._capacity = capacity
        self._rate = rate
        self._tokens = float(capacity)
        self._last_refill = time.monotonic()
        self._lock = threading.Lock()

    def acquire(self, block: bool = True) -> bool:
        """Consume one token. If block=True, sleep until a token is available.
        Returns True if acquired, False if not available (only when block=False)."""
        while True:
            with self._lock:
                now = time.monotonic()
                elapsed = now - self._last_refill
                self._tokens = min(self._capacity, self._tokens + elapsed * self._rate)
                self._last_refill = now
                if self._tokens >= 1.0:
                    self._tokens -= 1.0
                    return True
                wait_for = (1.0 - self._tokens) / self._rate
            if not block:
                return False
            time.sleep(wait_for)


# Pionex rate limit: 10 requests/second across REST calls AND WS subscriptions.
# Burst of 10 (one full second's worth), refill at 10/s.
# Both rest_fetch_pionex_orderbook() and _on_open() acquire from this shared bucket
# so the two paths can never jointly exceed the server limit.
_pionex_bucket = TokenBucket(capacity=10, rate=10)


def rest_fetch_pionex_orderbook(symbol: str) -> Optional[dict]:
    """REST fallback for Pionex depth. symbol format: BTC_USDT.
    Blocks until the shared TokenBucket allows the call (max 10 req/s)."""
    _pionex_bucket.acquire()   # blocks if burst is exhausted; never drops the call
    try:
        resp = requests.get(
            "https://api.pionex.com/api/v1/market/depth",
            params={"symbol": symbol, "limit": 10},
            headers={"User-Agent": "Mozilla/5.0"},
            timeout=5,
        )
        if resp.status_code == 200:
            data = resp.json()
            # Response: {"result": true, "data": {"bids": [["price","qty"],...], "asks": [...]}}
            depth = data.get("data", data)
            bids_raw = depth.get("bids", [])
            asks_raw = depth.get("asks", [])
            if bids_raw and asks_raw:
                bids = [(float(b[0]), float(b[1])) for b in bids_raw]
                asks = [(float(a[0]), float(a[1])) for a in asks_raw]
                if bids and asks:
                    return {"bids": bids, "asks": asks}
        elif resp.status_code == 429:
            logger.warning("Pionex REST rate-limited (429) – bucket may need tuning")
    except Exception:
        pass
    return None


class _PionexShardWSManager:
    """Single WS connection handling up to SHARD_SIZE symbols."""
    WS_URL = "wss://ws.pionex.com/wsPub"
    SHARD_SIZE = 10

    def __init__(self, shard_id: int, symbols: List[str], cache: PriceDepthCache, running_ref: list):
        self.shard_id = shard_id
        self.symbols = symbols
        self.cache = cache
        self._running_ref = running_ref  # shared [bool] so parent can stop all shards
        self._ws = None

    def _on_open(self, ws):
        logger.info(f"Pionex shard-{self.shard_id} connected ({len(self.symbols)} symbols)")
        for sym in self.symbols:
            if not self._running_ref[0]:
                break
            msg = {"op": "SUBSCRIBE", "topic": "DEPTH", "symbol": sym, "limit": 10}
            try:
                _pionex_bucket.acquire()  # shared rate-limit with REST calls
                ws.send(json.dumps(msg))
            except Exception as e:
                logger.warning(f"Pionex shard-{self.shard_id} subscribe failed for {sym}: {e}")
                break
        logger.info(f"Pionex shard-{self.shard_id} subscriptions sent")

    def _on_message(self, ws, message):
        try:
            data = json.loads(message)
        except Exception:
            return

        op = data.get('op')
        topic = data.get('topic', '')

        if op == 'PING':
            timestamp = data.get('timestamp')
            if timestamp is not None:
                try:
                    ws.send(json.dumps({"op": "PONG", "timestamp": timestamp}))
                except Exception:
                    pass
            return

        if topic.upper() == 'DEPTH':
            symbol = data.get('symbol')
            if not symbol:
                return
            depth_data = data.get('data', {})
            bids_raw = depth_data.get('bids', [])
            asks_raw = depth_data.get('asks', [])
            if bids_raw and asks_raw:
                bids = [(float(b[0]), float(b[1])) for b in bids_raw]
                asks = [(float(a[0]), float(a[1])) for a in asks_raw]
                if bids and asks:
                    self.cache.update_depth('pionex', symbol, bids, asks)
            else:
                logger.debug(f"Pionex shard-{self.shard_id} DEPTH empty book for {symbol}")
            return

        logger.debug(f"Pionex shard-{self.shard_id} unhandled: {json.dumps(data)[:200]}")

    def _on_error(self, ws, error):
        logger.warning(f"Pionex shard-{self.shard_id} error: {error}")

    def _on_close(self, ws, close_status_code, close_msg):
        logger.debug(f"Pionex shard-{self.shard_id} closed: status={close_status_code}")

    def run(self):
        """Blocking reconnect loop — run in its own daemon thread."""
        backoff = ReconnectBackoff(base=5, cap=120)
        while self._running_ref[0]:
            try:
                self._ws = websocket.WebSocketApp(
                    self.WS_URL,
                    on_open=self._on_open,
                    on_message=self._on_message,
                    on_error=self._on_error,
                    on_close=self._on_close,
                )
                self._ws.run_forever(
                    sslopt={"ca_certs": certifi.where()},
                    ping_interval=20,
                    ping_timeout=10,
                )
                backoff.reset()  # reset on clean exit
            except Exception as e:
                logger.warning(f"Pionex shard-{self.shard_id} exception: {e}")
            if self._running_ref[0]:
                sleep_for = backoff.next_delay()
                logger.debug(f"Pionex shard-{self.shard_id} reconnecting in {sleep_for:.1f}s")
                time.sleep(sleep_for)

    def stop(self):
        if self._ws:
            try:
                self._ws.close()
            except Exception:
                pass


class PionexPublicWSManager:
    """Splits symbols across multiple WS connections (≤10 symbols each) to
    avoid Pionex's per-connection subscription cap."""

    SHARD_SIZE = 10

    def __init__(self, symbols: List[str], cache: PriceDepthCache):
        self.symbols = symbols
        self.cache = cache
        self._running = [False]  # mutable so shards share the flag
        self._shards: List[_PionexShardWSManager] = []
        self._threads: List[threading.Thread] = []

    def start(self):
        if not WEBSOCKET_AVAILABLE or not self.symbols:
            return
        self._running[0] = True

        chunks = [
            self.symbols[i: i + self.SHARD_SIZE]
            for i in range(0, len(self.symbols), self.SHARD_SIZE)
        ]
        logger.info(
            f"Pionex WS: {len(self.symbols)} symbols → "
            f"{len(chunks)} shard(s) of ≤{self.SHARD_SIZE}"
        )

        for idx, chunk in enumerate(chunks):
            shard = _PionexShardWSManager(idx, chunk, self.cache, self._running)
            self._shards.append(shard)
            t = threading.Thread(target=shard.run, daemon=True, name=f"pionex-shard-{idx}")
            self._threads.append(t)
            t.start()
            # Stagger shard startups slightly so they don't all hit the server at once
            time.sleep(1)

    def stop(self):
        self._running[0] = False
        for shard in self._shards:
            shard.stop()

class LunoPublicWSManager:
    WS_BASE = "wss://ws.luno.com/api/1/stream"
    def __init__(self, pairs: List[str], cache: PriceDepthCache):
        self.pairs = pairs
        self.cache = cache
        self._running = False
        self._wss = {}

    def _run_pair(self, pair: str):
        backoff = ReconnectBackoff(base=5, cap=60)
        while self._running:
            try:
                def on_message(ws, msg, p=pair):
                    try:
                        data = json.loads(msg)
                        bids = data.get("bids", [])
                        asks = data.get("asks", [])
                        if bids and asks and 'price' in bids[0]:
                            bid_depth = [(float(b['price']), float(b['volume'])) for b in bids]
                            ask_depth = [(float(a['price']), float(a['volume'])) for a in asks]
                            self.cache.update_depth('luno', p, bid_depth, ask_depth)
                    except Exception:
                        pass
                def on_error(ws, error, p=pair):
                    logger.warning(f"Luno WS {p} error: {error}")
                ws = websocket.WebSocketApp(
                    f"{self.WS_BASE}/{pair}",
                    on_message=on_message,
                    on_error=on_error,
                )
                self._wss[pair] = ws
                ws.run_forever(sslopt={"ca_certs": certifi.where()}, ping_interval=30, ping_timeout=10)
                backoff.reset()  # reset on clean disconnect
            except Exception as e:
                if self._running:
                    logger.warning(f"Luno WS {pair} exception: {e}")
            if self._running:
                time.sleep(backoff.next_delay())

    def start(self):
        if not WEBSOCKET_AVAILABLE:
            return
        self._running = True
        logger.info(f"Luno WS: starting {len(self.pairs)} pair connections")
        for i, pair in enumerate(self.pairs):
            t = threading.Thread(target=self._run_pair, args=(pair,), daemon=True)
            t.start()
            if i < len(self.pairs) - 1:
                time.sleep(0.3)  # stagger to avoid Cloudflare burst-detection

    def stop(self):
        self._running = False
        for ws in self._wss.values():
            try:
                ws.close()
            except:
                pass

class HataPublicWSManager:
    API_BASE = "https://my-api.hata.io"
    WS_URL = "wss://websocket-my.hata.io/sapi/connection/websocket"

    def __init__(self, pairs: List[str], cache: PriceDepthCache):
        self.pairs = pairs
        self.cache = cache
        self.running = False
        self.ws = None
        self._buffer = ""

    def _get_stream_key(self):
        try:
            with curl_requests.Session(impersonate="chrome130") as session:
                r = session.post(f"{self.API_BASE}/auth/api/v2/my/user-stream-key", timeout=10)
                if r.status_code == 200:
                    data = r.json().get('data', r.json())
                    return data.get('token')
        except Exception:
            pass
        return None

    def _extract_json_objects(self, raw: str) -> List[str]:
        objects = []
        self._buffer += raw
        i = 0
        while i < len(self._buffer):
            start = self._buffer.find('{', i)
            if start == -1:
                break
            depth = 0
            j = start
            while j < len(self._buffer):
                ch = self._buffer[j]
                if ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0:
                        objects.append(self._buffer[start:j+1])
                        i = j + 1
                        break
                j += 1
            else:
                self._buffer = self._buffer[start:]
                break
        else:
            self._buffer = ""
        return objects

    def _dispatch_message(self, ws, message):
        for part in self._extract_json_objects(message):
            try:
                data = json.loads(part)
            except:
                continue
            try:
                if data == {}:
                    ws.send("{}")
                    continue
                push = data.get('push')
                if not push:
                    continue
                pub = push.get('pub', {})
                event_name = pub.get('data', {}).get('event_name', '')
                event_data = pub.get('data', {}).get('data', {})
                if '@depth' in str(event_name):
                    sym = event_name.replace('@depth', '')
                    bids = event_data.get('bids', [])
                    asks = event_data.get('asks', [])
                    if bids and asks:
                        bid_depth = [(float(b['price']), float(b['qty'])) for b in bids]
                        ask_depth = [(float(a['price']), float(a['qty'])) for a in asks]
                        self.cache.update_depth('hata', sym, bid_depth, ask_depth)
            except Exception:
                pass

    def _run_forever(self):
        backoff = ReconnectBackoff(base=5, cap=60)
        while self.running:
            try:
                token = self._get_stream_key()
                if not token:
                    time.sleep(30)
                    continue
                with curl_requests.Session(impersonate="chrome130") as session:
                    def on_open(ws):
                        ws.send(json.dumps({"id": 1, "connect": {"token": token}}))
                        for i, sym in enumerate(self.pairs, start=10):
                            try:
                                ws.send(json.dumps({
                                    "id": i,
                                    "subscribe": {"channel": f"public:{sym}@depth"}
                                }))
                            except:
                                pass
                    def on_message(ws, msg):
                        if isinstance(msg, bytes):
                            msg = msg.decode("utf-8")
                        self._dispatch_message(ws, msg)
                    ws = session.ws_connect(
                        self.WS_URL,
                        on_open=on_open,
                        on_message=on_message,
                    )
                    self.ws = ws
                    ws.run_forever()
                backoff.reset()  # reset on clean exit
                if self.running:
                    time.sleep(5)
            except Exception as e:
                if self.running:
                    sleep_for = backoff.next_delay()
                    logger.warning(f"Hata WS reconnecting in {sleep_for:.1f}s: {e}")
                    time.sleep(sleep_for)

    def start(self):
        if not CURL_CFI_AVAILABLE:
            return
        self.running = True
        logger.info(f"Hata WS: connecting to {len(self.pairs)} pairs")
        threading.Thread(target=self._run_forever, daemon=True).start()

    def stop(self):
        self.running = False
        if self.ws:
            try:
                self.ws.close()
            except:
                pass

class SinegyPublicWSManager:
    WS_URL = "wss://exchange-api.sinegy.com/ws"

    def __init__(self, pairs: List[str], cache: PriceDepthCache):
        self.pairs = pairs
        self.cache = cache
        self._running = False
        self._ws = None
        self._thread = None
        self._subscribed = False

    def _connect(self):
        backoff = ReconnectBackoff(base=5, cap=60)
        while self._running:
            try:
                self._ws = websocket.WebSocketApp(
                    self.WS_URL,
                    on_open=self._on_open,
                    on_message=self._on_message,
                    on_error=self._on_error,
                    on_close=self._on_close,
                )
                self._ws.run_forever(sslopt={"ca_certs": certifi.where()})
                backoff.reset()  # reset on clean exit
            except Exception as e:
                logger.warning(f"Sinegy WS error: {e}")
            if self._running:
                sleep_for = backoff.next_delay()
                logger.warning(f"Sinegy WS reconnecting in {sleep_for:.1f}s")
                time.sleep(sleep_for)

    def _on_open(self, ws):
        logger.info(f"Sinegy WS connected, subscribing to {len(self.pairs)} pairs")
        events = []
        for pair in self.pairs:
            base = pair[:-3]
            quote = pair[-3:]
            events.append(f"OB.{base}_{quote}")
        subscribe_msg = {"method": "subscribe", "events": events}
        try:
            ws.send(json.dumps(subscribe_msg))
            self._subscribed = True
            logger.info(f"Sinegy subscribed to {len(events)} order books")
        except Exception as e:
            logger.warning(f"Sinegy subscribe failed: {e}")

    def _on_message(self, ws, message):
        try:
            data = json.loads(message)
        except:
            return
        method = data.get("method")
        event = data.get("event")
        if method == "subscribe":
            return
        # Reply to server-side heartbeat pings
        if method in ("ping", "heartbeat") or data.get("type") in ("ping", "heartbeat"):
            try:
                ws.send(json.dumps({"method": "pong"}))
            except:
                pass
            return
        if method == "stream" and event and event.startswith("OB."):
            symbol = event.replace("OB.", "").replace("_", "")
            stream_data = data.get("data", {})
            bids_raw = stream_data.get("bids", [])
            asks_raw = stream_data.get("asks", [])
            if bids_raw and asks_raw:
                bids = [(float(b[0]), float(b[1])) for b in bids_raw if len(b) >= 2]
                asks = [(float(a[0]), float(a[1])) for a in asks_raw if len(a) >= 2]
                if bids and asks:
                    self.cache.update_depth("sinegy", symbol, bids, asks)

    def _on_error(self, ws, error):
        logger.warning(f"Sinegy WS error: {error}")

    def _on_close(self, ws, close_status_code, close_msg):
        logger.debug("Sinegy WS closed")
        self._subscribed = False

    def start(self):
        if not WEBSOCKET_AVAILABLE or not self.pairs:
            return
        self._running = True
        self._thread = threading.Thread(target=self._connect, daemon=True)
        self._thread.start()
        time.sleep(1)

    def stop(self):
        self._running = False
        if self._ws:
            try:
                self._ws.close()
            except:
                pass


# ----------------------------------------------------------------------
# Pollers for KDX and MX (REST only) – fixed 60-second interval
# ----------------------------------------------------------------------

# ----------------------------------------------------------------------
# Market discovery (with retry for MX, fixed Pionex, correct Sinegy)
# ----------------------------------------------------------------------
def _discover_get_json(exchange_label: str, url: str, params: dict = None, timeout: float = 10) -> Optional[dict]:
    """Shared GET-and-log boilerplate for discover_pairs()/discover_pionex_triangles().
    Returns parsed JSON on HTTP 200; otherwise logs why (status code,
    unparseable body, or exception) and returns None. Each exchange's own
    symbol-parsing/counting logic stays in its own block since the response
    shapes genuinely differ — this only removes the repeated try/except/
    status-check wrapper around it."""
    try:
        resp = requests.get(url, params=params, timeout=timeout)
        if resp.status_code == 200:
            try:
                return resp.json()
            except ValueError:
                logger.info(f"   {exchange_label}: response not JSON (status {resp.status_code})")
                return None
        logger.info(f"   {exchange_label}: HTTP {resp.status_code}")
    except Exception as e:
        logger.info(f"   {exchange_label}: exception – {e}")
    return None


def discover_pairs() -> List[Dict]:
    logger.info("🔍 Discovering market pairs...")
    all_pairs = {}

    # Luno
    data = _discover_get_json("Luno", "https://api.luno.com/api/exchange/1/markets")
    if data is not None:
        count = 0
        for m in data.get('markets', []):
            if m['market_id'].endswith('MYR'):
                asset = m['market_id'][:-3].replace('XBT', 'BTC')
                all_pairs.setdefault(asset, {})['luno'] = m['market_id']
                count += 1
        logger.info(f"   Luno: {count} MYR pairs")

    # Hata
    data = _discover_get_json("Hata", "https://my-api.hata.io/orderbook/api/v2/exchange-info")
    if data is not None:
        count = 0
        symbols = []
        if isinstance(data, list):
            symbols = data
        elif isinstance(data, dict):
            if 'data' in data and isinstance(data['data'], list):
                symbols = data['data']
            elif 'data' in data and isinstance(data['data'], dict) and 'symbols' in data['data']:
                symbols = data['data']['symbols']
            elif 'symbols' in data:
                symbols = data['symbols']
        for sym in symbols:
            if isinstance(sym, dict) and sym.get('quote') == 'MYR' and sym.get('status') != 'inactive':
                asset = sym.get('base')
                if asset:
                    all_pairs.setdefault(asset, {})['hata'] = f"{asset}MYR"
                    count += 1
        logger.info(f"   Hata: {count} MYR pairs")

    # KDX
    data = _discover_get_json("KDX", "https://api.kdx.com.my/public/v1/market/get-markets")
    if data is not None:
        count = 0
        if data.get('status') == 'success':
            for section in data.get('data', []):
                if section.get('title') == 'MYR':
                    for market in section.get('list', []):
                        if market.get('status') != 'active':
                            continue
                        name = market.get('marketName', '')
                        if name.startswith('MYR-'):
                            asset = name.split('-', 1)[1]
                            all_pairs.setdefault(asset, {})['kdx'] = f"{asset}MYR"
                            count += 1
            logger.info(f"   KDX: {count} MYR pairs")
        else:
            logger.info(f"   KDX: API error – {data.get('message', 'unknown')}")

    # MX – retry on rate limit (own loop; _discover_get_json doesn't special-case 429)
    mx_retries = 3
    for attempt in range(mx_retries):
        try:
            resp = requests.get("https://openapi.mx.exchange/api/1/marketpair", timeout=10)
            if resp.status_code == 200:
                count = 0
                for p in resp.json().get('marketPair', []):
                    if p.upper().endswith('MYR'):
                        asset = p[:-3]
                        all_pairs.setdefault(asset, {})['mx'] = p.upper()
                        count += 1
                logger.info(f"   MX: {count} MYR pairs")
                break
            elif resp.status_code == 429:
                logger.info(f"   MX: rate limited (429), retrying in {2 ** attempt}s...")
                time.sleep(2 ** attempt)
            else:
                logger.info(f"   MX: HTTP {resp.status_code}")
                break
        except Exception as e:
            logger.info(f"   MX: exception – {e}")
            break

    # Pionex – fixed parsing
    pionex_count = 0
    data = _discover_get_json("Pionex", "https://api.pionex.com/api/v1/common/symbols")
    if data is not None:
        symbols = []
        if data.get('result') and 'data' in data and isinstance(data['data'], dict):
            symbols = data['data'].get('symbols', [])
        elif isinstance(data, dict):
            if 'symbols' in data:
                symbols = data['symbols']
            elif 'data' in data and isinstance(data['data'], list):
                symbols = data['data']
            elif 'data' in data and isinstance(data['data'], dict) and 'symbols' in data['data']:
                symbols = data['data']['symbols']
        elif isinstance(data, list):
            symbols = data
        for sym in symbols:
            if isinstance(sym, dict) and sym.get('quoteCurrency') == 'USDT' and sym.get('enable') is not False:
                asset = sym.get('baseCurrency')
                if asset:
                    all_pairs.setdefault(asset, {})['pionex'] = sym.get('symbol')
                    pionex_count += 1
    logger.info(f"   Pionex: {pionex_count} USDT pairs")

    # Sinegy – using correct /market/get-market-summary
    sinegy_count = 0
    data = _discover_get_json("Sinegy", "https://exchange-api.sinegy.com/market/get-market-summary")
    if data is not None and data.get('status') == 'Success' and 'data' in data:
        market_data = data['data']
        for pair_key in market_data.keys():
            if pair_key.startswith('MYR_'):
                asset = pair_key.split('_')[1]
                all_pairs.setdefault(asset, {})['sinegy'] = f"{asset}MYR"
                sinegy_count += 1
    logger.info(f"   Sinegy: {sinegy_count} MYR pairs")

    # Binance
    data = _discover_get_json("Binance", "https://api.binance.com/api/v3/exchangeInfo")
    if data is not None:
        count = 0
        for sym in data.get('symbols', []):
            if sym.get('status') != 'TRADING':
                continue
            if sym.get('quoteAsset') == 'USDT':
                asset = sym.get('baseAsset')
                if asset:
                    all_pairs.setdefault(asset, {})['binance'] = sym.get('symbol')
                    count += 1
        logger.info(f"   Binance: {count} USDT pairs")

    # Build final pairs — must have at least one MYR exchange so Binance/Pionex
    # USDT pairs are only subscribed when there is a Malaysian market to arb against
    MYR_EXCHANGES = {'luno', 'hata', 'kdx', 'mx', 'sinegy'}
    pairs = []
    for asset, ex_dict in all_pairs.items():
        has_myr = any(ex in ex_dict for ex in MYR_EXCHANGES)
        if has_myr and len(ex_dict) >= 2:
            pair = {'name': f"{asset}MYR"}
            pair.update(ex_dict)
            pairs.append(pair)

    logger.info(f"✅ Total arbitrage pairs (assets with >=2 exchanges, at least 1 MYR): {len(pairs)}")
    return pairs

# ----------------------------------------------------------------------
# Pionex triangular arbitrage — USDT-anchored only (USDT -> X -> Y -> USDT)
# ----------------------------------------------------------------------
def discover_exchange_triangles(exchange: str, symbols: List[dict],
                                 base_key: str, quote_key: str, symbol_key: str,
                                 max_triangles: Optional[int] = None) -> List[Dict]:
    """Find every USDT-anchored triangle on a single exchange from its already-
    fetched symbol list: two assets X and Y that both have a direct USDT
    market, plus a direct market between X and Y (in either base/quote
    orientation). Shared by Pionex and Binance discovery — only the field
    names differ between their exchangeInfo-style responses.

    max_triangles caps the result (largest exchanges by USDT-pair count) —
    important for exchanges whose WS manager isn't sharded like Pionex's is;
    an unbounded triangle count there could push far too many symbols into
    one WS connection.
    """
    market_by_pair: Dict[Tuple[str, str], str] = {}
    usdt_assets: Dict[str, str] = {}
    for sym in symbols:
        base = sym.get(base_key)
        quote = sym.get(quote_key)
        symbol_str = sym.get(symbol_key)
        if not base or not quote or not symbol_str:
            continue
        market_by_pair[(base, quote)] = symbol_str
        if quote == 'USDT':
            usdt_assets[base] = symbol_str

    triangles = []
    assets = sorted(usdt_assets.keys())
    for i, x in enumerate(assets):
        for y in assets[i + 1:]:
            cross_symbol = None
            cross_base, cross_quote = None, None
            if (x, y) in market_by_pair:
                cross_symbol = market_by_pair[(x, y)]
                cross_base, cross_quote = x, y
            elif (y, x) in market_by_pair:
                cross_symbol = market_by_pair[(y, x)]
                cross_base, cross_quote = y, x
            if cross_symbol:
                triangles.append({
                    'exchange': exchange,
                    'asset_x': x,
                    'asset_y': y,
                    'x_usdt_symbol': usdt_assets[x],
                    'y_usdt_symbol': usdt_assets[y],
                    'cross_symbol': cross_symbol,
                    'cross_base': cross_base,
                    'cross_quote': cross_quote,
                })
    if max_triangles is not None and len(triangles) > max_triangles:
        logger.info(f"   {exchange}: {len(triangles)} triangles found, capping to top {max_triangles}")
        triangles = triangles[:max_triangles]
    return triangles


def discover_pionex_triangles() -> List[Dict]:
    """Find every valid USDT-anchored triangle on Pionex."""
    triangles = []
    data = _discover_get_json("Pionex triangles", "https://api.pionex.com/api/v1/common/symbols")
    if data is not None:
        symbols = []
        if data.get('result') and 'data' in data and isinstance(data['data'], dict):
            symbols = data['data'].get('symbols', [])
        elif isinstance(data, dict) and 'symbols' in data:
            symbols = data['symbols']
        enabled = [s for s in symbols if isinstance(s, dict) and s.get('enable') is not False]
        triangles = discover_exchange_triangles(
            'pionex', enabled, base_key='baseCurrency', quote_key='quoteCurrency', symbol_key='symbol')
    logger.info(f"✅ Pionex USDT-anchored triangles discovered: {len(triangles)}")
    return triangles


def discover_binance_triangles(max_triangles: int = 300) -> List[Dict]:
    """Find valid USDT-anchored triangles on Binance. Binance has far more
    USDT pairs than Pionex, so this is capped (max_triangles) — Binance's WS
    manager is a single connection, not sharded like Pionex's, so an
    unbounded triangle count risks pushing too many symbols into one stream
    URL/connection."""
    triangles = []
    data = _discover_get_json("Binance triangles", "https://api.binance.com/api/v3/exchangeInfo")
    if data is not None:
        enabled = [s for s in data.get('symbols', []) if isinstance(s, dict) and s.get('status') == 'TRADING']
        triangles = discover_exchange_triangles(
            'binance', enabled, base_key='baseAsset', quote_key='quoteAsset', symbol_key='symbol',
            max_triangles=max_triangles)
    logger.info(f"✅ Binance USDT-anchored triangles discovered: {len(triangles)}")
    return triangles

# ----------------------------------------------------------------------
# Weighted fill & max fillable volume
# ----------------------------------------------------------------------
def calculate_max_fillable(buy_asks, sell_bids, buy_fee_rate: Decimal, sell_fee_rate: Decimal,
                            min_profit_pct: Decimal = Decimal('0')) -> Tuple[Decimal, Decimal, Decimal]:
    """Walk the crossed order book level-by-level and return the REAL tradeable size.

    Returns (total_volume, avg_buy_price, avg_sell_price):
      - total_volume: the actual size available at profitable prices (not an assumption)
      - avg_buy_price / avg_sell_price: the true volume-weighted (pre-fee) prices across
        every level actually crossed to fill total_volume

    Stops walking as soon as a level's fee-inclusive marginal profit drops below
    min_profit_pct, so every level included is itself profitable.
    """
    if not buy_asks or not sell_bids:
        return Decimal('0'), Decimal('0'), Decimal('0')
    def _dec(x):
        # Inputs from PriceDepthCache are already Decimal; avoid a redundant
        # str-roundtrip conversion in this hot path (called on every scan,
        # every exchange-pair direction, every price level).
        return x if isinstance(x, Decimal) else Decimal(str(x))
    asks = sorted([(_dec(p), _dec(v)) for p, v in buy_asks if v > 0], key=lambda x: x[0])
    bids = sorted([(_dec(p), _dec(v)) for p, v in sell_bids if v > 0], key=lambda x: x[0], reverse=True)
    if not asks or not bids:
        return Decimal('0'), Decimal('0'), Decimal('0')
    ai = bi = 0
    total_volume = Decimal('0')
    total_buy_cost = Decimal('0')      # sum of raw ask_price * volume (pre-fee)
    total_sell_revenue = Decimal('0')  # sum of raw bid_price * volume (pre-fee)
    while ai < len(asks) and bi < len(bids):
        ask_price, ask_vol = asks[ai]
        bid_price, bid_vol = bids[bi]
        buy_cost = ask_price * (1 + buy_fee_rate)
        sell_revenue = bid_price * (1 - sell_fee_rate)
        if sell_revenue <= buy_cost:
            break
        marginal_profit_pct = (sell_revenue - buy_cost) / buy_cost * 100
        if marginal_profit_pct < min_profit_pct:
            break
        step_vol = min(ask_vol, bid_vol)
        total_volume += step_vol
        total_buy_cost += ask_price * step_vol
        total_sell_revenue += bid_price * step_vol
        asks[ai] = (ask_price, ask_vol - step_vol)
        bids[bi] = (bid_price, bid_vol - step_vol)
        if asks[ai][1] <= 0:
            ai += 1
        if bids[bi][1] <= 0:
            bi += 1
    if total_volume == 0:
        return Decimal('0'), Decimal('0'), Decimal('0')
    avg_buy_price = total_buy_cost / total_volume
    avg_sell_price = total_sell_revenue / total_volume
    return total_volume, avg_buy_price, avg_sell_price

# ----------------------------------------------------------------------
# Arbitrage calculation
# ----------------------------------------------------------------------
def compute_profit(buy_avg: Decimal, sell_avg: Decimal, fee_buy: Decimal, fee_sell: Decimal) -> Tuple[Decimal, Decimal, Decimal]:
    """Shared fee-inclusive profit math used by every arbitrage branch.

    Returns (cost, profit_per_unit, profit_pct) where cost is the fee-inclusive
    buy price and profit_pct is net-of-fees profit relative to cost.
    """
    cost = buy_avg * (1 + fee_buy)
    revenue = sell_avg * (1 - fee_sell)
    profit_per_unit = revenue - cost
    profit_pct = (profit_per_unit / cost) * 100 if cost > 0 else Decimal('0')
    return cost, profit_per_unit, profit_pct

def calculate_triangle_opportunity(cache: 'PriceDepthCache', triangle: Dict, fee: Decimal,
                                    min_profit_pct: Decimal) -> Optional[Dict]:
    """Check a single USDT-anchored triangle for profit, in both directions
    (USDT->X->Y->USDT and USDT->Y->X->USDT). Works for any exchange whose
    triangle dict carries an 'exchange' key matching how its WS manager
    writes into the cache (currently Pionex and Binance).

    NOTE — top-of-book only: unlike calculate_max_fillable (which walks the
    full order book for 2-leg cross-exchange arb), this only looks at the
    best bid/ask on each of the 3 legs. Walking full depth across 3 chained
    legs is substantially more complex (each leg's available depth depends
    on how much of the previous leg's output you actually got), so this
    trades some precision for simplicity. 'max_volume' is a rough estimate
    capped by the smallest top-of-book size among the 3 legs, in USDT terms
    — treat it as a ceiling, not a guarantee of exact fillable size.
    """
    exchange = triangle['exchange']
    x_usdt = cache.get_depth(exchange, triangle['x_usdt_symbol'], max_age=10.0)
    y_usdt = cache.get_depth(exchange, triangle['y_usdt_symbol'], max_age=10.0)
    cross = cache.get_depth(exchange, triangle['cross_symbol'], max_age=10.0)
    if not x_usdt or not y_usdt or not cross:
        return None
    if not (x_usdt['bids'] and x_usdt['asks'] and y_usdt['bids'] and y_usdt['asks']
            and cross['bids'] and cross['asks']):
        return None

    x_ask, x_ask_vol = x_usdt['asks'][0]
    x_bid, x_bid_vol = x_usdt['bids'][0]
    y_ask, y_ask_vol = y_usdt['asks'][0]
    y_bid, y_bid_vol = y_usdt['bids'][0]
    cross_ask, cross_ask_vol = cross['asks'][0]
    cross_bid, cross_bid_vol = cross['bids'][0]
    if min(x_ask, x_bid, y_ask, y_bid, cross_ask, cross_bid) <= 0:
        return None

    fee_mult = Decimal('1') - fee

    # Rate to convert 1 unit of X -> Y, and 1 unit of Y -> X, via the cross market,
    # whichever orientation it's actually listed in.
    if triangle['cross_base'] == triangle['asset_x']:
        # cross symbol is X/Y: sell X for Y at cross_bid; buy X with Y at cross_ask
        x_to_y_rate = cross_bid
        y_to_x_rate = Decimal('1') / cross_ask
    else:
        # cross symbol is Y/X: sell Y for X at cross_bid; buy Y with X at cross_ask
        x_to_y_rate = Decimal('1') / cross_ask
        y_to_x_rate = cross_bid

    results = []

    # Direction A: USDT -> X -> Y -> USDT
    x_from_usdt = (Decimal('1') / x_ask) * fee_mult
    y_from_x = x_from_usdt * x_to_y_rate * fee_mult
    usdt_from_y = y_from_x * y_bid * fee_mult
    profit_pct_a = (usdt_from_y - Decimal('1')) * 100
    results.append(('USDT->%s->%s->USDT' % (triangle['asset_x'], triangle['asset_y']), profit_pct_a))

    # Direction B: USDT -> Y -> X -> USDT
    y_from_usdt = (Decimal('1') / y_ask) * fee_mult
    x_from_y = y_from_usdt * y_to_x_rate * fee_mult
    usdt_from_x = x_from_y * x_bid * fee_mult
    profit_pct_b = (usdt_from_x - Decimal('1')) * 100
    results.append(('USDT->%s->%s->USDT' % (triangle['asset_y'], triangle['asset_x']), profit_pct_b))

    direction, profit_pct = max(results, key=lambda r: r[1])
    if profit_pct < min_profit_pct:
        return None

    # Rough fillable ceiling in USDT terms, using just the two direct USDT
    # legs' top-of-book size (the simpler and less bug-prone of the three
    # legs to convert to a common USDT basis). The cross-leg's own depth
    # could theoretically be the tighter constraint, but is left out here —
    # this is a rough ceiling for display, not a guarantee.
    if direction.startswith(f"USDT->{triangle['asset_x']}"):
        leg1_usdt = x_ask_vol * x_ask
        leg3_usdt = y_bid_vol * y_bid
    else:
        leg1_usdt = y_ask_vol * y_ask
        leg3_usdt = x_bid_vol * x_bid
    max_volume_usdt = min(leg1_usdt, leg3_usdt)
    if max_volume_usdt * profit_pct / 100 < Decimal('1'):  # skip if profit on the fillable size is under $1
        return None

    return {
        'triangle': triangle,
        'direction': direction,
        'profit_pct': profit_pct,
        'max_volume_usdt': max_volume_usdt,
        'estimated_profit_usdt': max_volume_usdt * profit_pct / 100,
    }

def calculate_opportunities(prices: Dict, min_profit_pct: Decimal) -> List[Dict]:
    opportunities = []
    exchanges = sort_exchanges(list(prices.keys()))

    for i, buy_ex in enumerate(exchanges):
        for sell_ex in exchanges[i+1:]:
            for buy, sell in [(buy_ex, sell_ex), (sell_ex, buy_ex)]:
                if buy not in prices or sell not in prices:
                    continue
                if 'ask' not in prices[buy] or 'bid' not in prices[sell]:
                    continue

                buy_is_usdt = buy in USDT_EXCHANGES
                sell_is_usdt = sell in USDT_EXCHANGES

                # ── USDT-to-USDT (e.g. Binance ↔ Pionex) ──────────────────
                if buy_is_usdt and sell_is_usdt:
                    buy_asks = prices[buy].get('asks_usdt', [])
                    sell_bids = prices[sell].get('bids_usdt', [])
                    if not buy_asks or not sell_bids:
                        continue
                    usdt_myr = prices[buy].get('usdt_myr')
                    if usdt_myr is None:
                        continue  # shouldn't happen — get_prices() only sets this when the rate is known
                    fee_buy = TAKER_FEES.get(buy, Decimal('0.001'))
                    fee_sell = TAKER_FEES.get(sell, Decimal('0.001'))
                    max_volume, buy_avg, sell_avg = calculate_max_fillable(
                        buy_asks, sell_bids, fee_buy, fee_sell, min_profit_pct)
                    if max_volume <= 0:
                        continue
                    cost, profit_per_unit, profit_pct = compute_profit(buy_avg, sell_avg, fee_buy, fee_sell)
                    if profit_pct < min_profit_pct:
                        continue
                    if max_volume * buy_avg * usdt_myr < Decimal('10'):
                        continue
                    opportunities.append({
                        'arb_type': 'usdt',
                        'direction': f"{buy}->{sell}",
                        'profit_pct': profit_pct,
                        'profit_per_unit': profit_per_unit,
                        'max_volume': max_volume,
                        'buy_exchange': buy,
                        'sell_exchange': sell,
                        'buy_price': buy_avg,       # in USDT
                        'sell_price': sell_avg,     # in USDT
                        'usdt_myr': usdt_myr,
                        'total_profit': profit_per_unit * max_volume,  # in USDT
                    })
                    continue

                # ── REVERSE arb: MYR exchange → USDT exchange ───────────────
                if not buy_is_usdt and sell_is_usdt:
                    buy_asks = prices[buy].get('asks', [])
                    sell_bids_usdt = prices[sell].get('bids_usdt', [])
                    if not buy_asks or not sell_bids_usdt:
                        continue
                    usdt_myr = prices[sell].get('usdt_myr')
                    if usdt_myr is None:
                        continue  # shouldn't happen — get_prices() only sets this when the rate is known
                    fee_buy = TAKER_FEES.get(buy, Decimal('0.004'))
                    fee_sell = TAKER_FEES.get(sell, Decimal('0.001'))
                    # max fillable using MYR asks vs USDT bids converted to MYR
                    sell_bids_myr = [(p * usdt_myr, q) for p, q in sell_bids_usdt]
                    max_volume, buy_avg, sell_avg_myr = calculate_max_fillable(
                        buy_asks, sell_bids_myr, fee_buy, fee_sell, min_profit_pct)
                    if max_volume <= 0:
                        continue
                    cost_myr, profit_per_unit, profit_pct = compute_profit(buy_avg, sell_avg_myr, fee_buy, fee_sell)
                    if profit_pct < min_profit_pct:
                        continue
                    if max_volume * cost_myr < Decimal('10'):
                        continue
                    sell_avg_usdt = sell_avg_myr / usdt_myr
                    # Both buy_avg (native MYR ask, buy exchange) and
                    # sell_avg_usdt (native USDT bid, sell exchange — exactly
                    # recovered above since sell_bids_myr was sell_bids_usdt
                    # scaled by the constant usdt_myr) come from two entirely
                    # separate exchanges. Their ratio is the USDT/MYR rate
                    # implied by what this trade would actually realize —
                    # independent of the CoinGecko/yfinance benchmark, unlike
                    # usdt_myr itself.
                    effective_rate = buy_avg / sell_avg_usdt if sell_avg_usdt > 0 else None
                    opportunities.append({
                        'arb_type': 'reverse',
                        'direction': f"{buy}->{sell}",
                        'profit_pct': profit_pct,
                        'profit_per_unit': profit_per_unit,
                        'max_volume': max_volume,
                        'buy_exchange': buy,
                        'sell_exchange': sell,
                        'buy_price': buy_avg,           # in MYR
                        'sell_price': sell_avg_usdt,    # in USDT
                        'usdt_myr': usdt_myr,
                        'effective_rate': effective_rate,
                        'total_profit': profit_per_unit * max_volume,  # in MYR
                    })
                    continue

                # ── FORWARD arb: USDT exchange → MYR exchange ───────────────
                if buy_is_usdt and not sell_is_usdt:
                    buy_asks_myr = prices[buy].get('asks', [])
                    sell_bids_myr = prices[sell].get('bids', [])
                    if not buy_asks_myr or not sell_bids_myr:
                        continue
                    fee_buy = TAKER_FEES.get(buy, Decimal('0.001'))
                    fee_sell = TAKER_FEES.get(sell, Decimal('0.004'))
                    max_volume, buy_avg, sell_avg = calculate_max_fillable(
                        buy_asks_myr, sell_bids_myr, fee_buy, fee_sell, min_profit_pct)
                    if max_volume <= 0:
                        continue
                    cost, profit_per_unit, profit_pct = compute_profit(buy_avg, sell_avg, fee_buy, fee_sell)
                    if profit_pct < min_profit_pct:
                        continue
                    if max_volume * buy_avg < Decimal('10'):
                        continue
                    usdt_myr = prices[buy].get('usdt_myr')
                    if usdt_myr is None:
                        continue  # shouldn't happen — get_prices() only sets this when the rate is known
                    # buy_avg was computed by walking buy_asks_myr, which is
                    # asks_usdt scaled by the constant usdt_myr — so dividing
                    # back out recovers the exact native USDT average fill
                    # price. sell_avg is already native MYR (sell is a MYR
                    # exchange, never converted). Their ratio is this trade's
                    # own implied USDT/MYR rate, independent of usdt_myr.
                    buy_avg_usdt = buy_avg / usdt_myr
                    effective_rate = sell_avg / buy_avg_usdt if buy_avg_usdt > 0 else None
                    opportunities.append({
                        'arb_type': 'forward',
                        'direction': f"{buy}->{sell}",
                        'profit_pct': profit_pct,
                        'profit_per_unit': profit_per_unit,
                        'max_volume': max_volume,
                        'buy_exchange': buy,
                        'sell_exchange': sell,
                        'buy_price': buy_avg,       # in MYR equivalent
                        'sell_price': sell_avg,     # in MYR
                        'usdt_myr': usdt_myr,
                        'effective_rate': effective_rate,
                        'total_profit': profit_per_unit * max_volume,
                    })
                    continue

                # ── MYR-to-MYR (e.g. Luno ↔ Hata) ─────────────────────────
                buy_asks = prices[buy].get('asks', [])
                sell_bids = prices[sell].get('bids', [])
                if not buy_asks or not sell_bids:
                    continue
                fee_buy = TAKER_FEES.get(buy, Decimal('0.004'))
                fee_sell = TAKER_FEES.get(sell, Decimal('0.004'))
                max_volume, buy_avg, sell_avg = calculate_max_fillable(
                    buy_asks, sell_bids, fee_buy, fee_sell, min_profit_pct)
                if max_volume <= 0:
                    continue
                cost, profit_per_unit, profit_pct = compute_profit(buy_avg, sell_avg, fee_buy, fee_sell)
                if profit_pct < min_profit_pct:
                    continue
                if max_volume * buy_avg < Decimal('10'):
                    continue
                opportunities.append({
                    'arb_type': 'myr',
                    'direction': f"{buy}->{sell}",
                    'profit_pct': profit_pct,
                    'profit_per_unit': profit_per_unit,
                    'max_volume': max_volume,
                    'buy_exchange': buy,
                    'sell_exchange': sell,
                    'buy_price': buy_avg,
                    'sell_price': sell_avg,
                    'total_profit': profit_per_unit * max_volume,
                })

    return sorted(opportunities, key=lambda x: x['profit_pct'], reverse=True)

# ----------------------------------------------------------------------
# Telegram sender (with 10‑minute cooldown per direction)
# ----------------------------------------------------------------------
# Time‑based deduplication: store last send timestamp for each (pair, buy_exchange, sell_exchange)
_last_sent_time = {}
ALERT_COOLDOWN = 600  # 10 minutes in seconds
_last_prune_time = [0.0]
PRUNE_INTERVAL = 3600  # sweep stale cooldown keys at most once an hour
# Single lock shared by all cooldown dicts so the check-and-set is atomic
# across concurrent callers (_on_price_update WS thread vs monitor() thread).
_cooldown_lock = threading.Lock()

def _prune_cooldown_dict(d: dict, now: float, last_prune_holder: list, cooldown: float):
    """Drop cooldown entries that expired long ago from any (key -> timestamp)
    dict. last_prune_holder is a 1-element list used as a mutable timestamp
    (avoids a separate global per caller). If the underlying set of keys
    changes over a long-running process (e.g. discover_pairs() adds/drops
    pairs), stale entries would otherwise sit here forever."""
    if now - last_prune_holder[0] < PRUNE_INTERVAL:
        return
    last_prune_holder[0] = now
    stale = [k for k, t in d.items() if now - t > cooldown * 2]
    for k in stale:
        del d[k]
    if stale:
        logger.debug(f"Pruned {len(stale)} stale cooldown entries")

def price_decimals(value: float, sig_figs: int = 4) -> int:
    """Pick a decimal-place count that shows ~sig_figs significant figures.

    We don't have each exchange's actual tick size on hand (that'd need an
    extra API call per exchange), so this approximates it: high-value assets
    get fewer decimals (e.g. RM180 -> 2dp), low-value assets get more
    (e.g. $0.74 -> 4dp) — matching how exchanges typically display prices,
    rather than always showing a fixed number of decimals regardless of
    magnitude.
    """
    if value == 0:
        return 2
    magnitude = math.floor(math.log10(abs(value)))
    decimals = sig_figs - magnitude - 1
    return max(2, min(decimals, 8))

def fmt_price(value: float, sig_figs: int = 4) -> str:
    """Format a native (directly-quoted) price using magnitude-based precision."""
    return fmt(value, price_decimals(value, sig_figs))

def fmt_converted(value: float, decimals: int) -> str:
    """Format a currency-converted price using the SAME decimal count as the
    original price it was converted from, rather than inventing its own
    precision."""
    return fmt(value, decimals)

def fmt_fixed(value: float, decimals: int) -> str:
    """Format a float to a fixed number of decimal places (no trailing-zero strip).
    Used for paired price display so both sides always share the same decimal count."""
    return f"{value:.{decimals}f}"

def fmt(value: float, max_decimals: int = 6) -> str:
    """Format a float stripping trailing zeros, up to max_decimals places.
    Note: buy/sell prices in alerts are volume-weighted averages across
    multiple order-book levels (see calculate_max_fillable), not a single
    exchange quote — so they can carry more raw precision than the
    exchange's own tick size. Capped at 6 decimals here for readability."""
    formatted = f"{value:.{max_decimals}f}".rstrip('0').rstrip('.')
    return formatted

def send_telegram_alert(opp: Dict, pair_info: Dict):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return

    buy_ex = opp['buy_exchange']
    sell_ex = opp['sell_exchange']
    pair = pair_info['name']
    arb_type = opp.get('arb_type', 'myr')
    key = (pair, buy_ex, sell_ex, arb_type)

    now = time.time()
    _prune_cooldown_dict(_last_sent_time, now, _last_prune_time, ALERT_COOLDOWN)
    last = _last_sent_time.get(key, 0)
    if now - last < ALERT_COOLDOWN:
        return

    profit_pct = float(opp['profit_pct'])
    fill_volume = opp.get('max_volume', Decimal('0'))
    if fill_volume <= 0:
        return

    base_asset = pair[:-3]
    total_profit = Decimal(str(opp.get('total_profit', Decimal('0'))))
    buy_price = opp['buy_price']
    sell_price = opp['sell_price']

    if arb_type in ('usdt', 'reverse', 'forward') and opp.get('usdt_myr') is None:
        # Shouldn't happen — calculate_opportunities() only builds these arb
        # types when a live USDT/MYR rate was available. Bail rather than
        # alert on a stale/guessed rate.
        logger.warning(f"Dropping alert for {pair} {buy_ex}->{sell_ex}: missing usdt_myr rate.")
        return

    if arb_type == 'usdt':
        # Both sides USDT — Binance ↔ Pionex
        usdt_myr = opp['usdt_myr']
        fill_usdt = fill_volume * Decimal(str(buy_price))
        fill_myr = fill_usdt * usdt_myr
        profit_usdt = total_profit
        profit_myr = profit_usdt * usdt_myr
        buy_dp = price_decimals(float(buy_price))
        sell_dp = price_decimals(float(sell_price))
        dp = max(buy_dp, sell_dp)
        msg = (
            f"⚡{base_asset} +{fmt_fixed(float(profit_pct), 2)}%⚡\n"
            f"🟢 Buy  {buy_ex.upper()}  ${fmt_fixed(float(buy_price), dp)}\n"
            f"🔴 Sell {sell_ex.upper()}  ${fmt_fixed(float(sell_price), dp)}\n"
            f"💰 Profit ≈ ${fmt_fixed(float(profit_usdt), 2)} (≈RM{fmt_fixed(float(profit_myr), 2)})\n"
            f"🪙 Size {fmt(float(fill_volume))} {base_asset} (≈RM{fmt_fixed(float(fill_myr), 2)})\n"
        )

    elif arb_type == 'reverse':
        # MYR exchange → USDT exchange
        usdt_myr = opp['usdt_myr']
        effective_rate = opp.get('effective_rate')
        sell_price_myr = Decimal(str(sell_price)) * usdt_myr
        fill_myr = fill_volume * Decimal(str(buy_price))
        profit_myr = total_profit
        dp = max(price_decimals(float(buy_price)), price_decimals(float(sell_price_myr)))
        eff_rate_val = float(effective_rate) if effective_rate else float(usdt_myr)
        msg = (
            f"⚡{base_asset} +{fmt_fixed(float(profit_pct), 2)}%⚡\n"
            f"🟢 Buy  {buy_ex.upper()}  RM{fmt_fixed(float(buy_price), dp)}\n"
            f"🔴 Sell {sell_ex.upper()}  RM{fmt_fixed(float(sell_price_myr), dp)}\n"
            f"💰 Profit ≈ RM{fmt_fixed(float(profit_myr), 2)}\n"
            f"🪙 Size {fmt(float(fill_volume))} {base_asset} (≈RM{fmt_fixed(float(fill_myr), 2)})\n"
            f"💱 Rate RM{fmt_fixed(eff_rate_val, 2)} effective | RM{fmt_fixed(float(usdt_myr), 2)} current\n"
        )

    elif arb_type == 'forward':
        # USDT exchange → MYR exchange
        usdt_myr = opp['usdt_myr']
        effective_rate = opp.get('effective_rate')
        buy_price_usdt = Decimal(str(buy_price)) / usdt_myr
        fill_myr = fill_volume * Decimal(str(buy_price))
        profit_myr = total_profit
        dp = max(price_decimals(float(buy_price)), price_decimals(float(sell_price)))
        eff_rate_val = float(effective_rate) if effective_rate else float(usdt_myr)
        msg = (
            f"⚡{base_asset} +{fmt_fixed(float(profit_pct), 2)}%⚡\n"
            f"🟢 Buy  {buy_ex.upper()}  RM{fmt_fixed(float(buy_price), dp)}\n"
            f"🔴 Sell {sell_ex.upper()}  RM{fmt_fixed(float(sell_price), dp)}\n"
            f"💰 Profit ≈ RM{fmt_fixed(float(profit_myr), 2)}\n"
            f"🪙 Size {fmt(float(fill_volume))} {base_asset} (≈RM{fmt_fixed(float(fill_myr), 2)})\n"
            f"💱 Rate RM{fmt_fixed(eff_rate_val, 2)} effective | RM{fmt_fixed(float(usdt_myr), 2)} current\n"
        )

    else:
        # MYR-to-MYR
        fill_myr = fill_volume * Decimal(str(buy_price))
        profit_myr = total_profit
        dp = max(price_decimals(float(buy_price)), price_decimals(float(sell_price)))
        msg = (
            f"⚡{base_asset} +{fmt_fixed(float(profit_pct), 2)}%⚡\n"
            f"🟢 Buy  {buy_ex.upper()}  RM{fmt_fixed(float(buy_price), dp)}\n"
            f"🔴 Sell {sell_ex.upper()}  RM{fmt_fixed(float(sell_price), dp)}\n"
            f"💰 Profit ≈ RM{fmt_fixed(float(profit_myr), 2)}\n"
            f"🪙 Size {fmt(float(fill_volume))} {base_asset} (≈RM{fmt_fixed(float(fill_myr), 2)})\n"
        )

    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": msg,
        "parse_mode": "Markdown",
        "disable_web_page_preview": True,
    }
    # Cooldown starts once the alert is queued for delivery — the dedicated
    # sender thread will retry on transient failures, so this is as good as
    # "sent" from the monitor loop's point of view, and it avoids blocking
    # the scan loop on a slow/rate-limited send.
    _enqueue_alert(payload, f"Alert [{pair} {buy_ex}->{sell_ex}]", _last_sent_time, key, now)

# ----------------------------------------------------------------------
# Triangular arbitrage alert (Pionex, Binance — any USDT-anchored exchange in
# self.triangles) — its own cooldown, keyed by (exchange, x_usdt_symbol,
# y_usdt_symbol, cross_symbol, direction).
# ----------------------------------------------------------------------
_last_triangle_sent_time = {}
_last_triangle_prune_time = [0.0]

def send_triangle_alert(result: Dict):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    triangle = result['triangle']
    direction = result['direction']
    key = (triangle['exchange'], triangle['x_usdt_symbol'], triangle['y_usdt_symbol'], triangle['cross_symbol'], direction)

    now = time.time()
    _prune_cooldown_dict(_last_triangle_sent_time, now, _last_triangle_prune_time, ALERT_COOLDOWN)
    last = _last_triangle_sent_time.get(key, 0)
    if now - last < ALERT_COOLDOWN:
        return

    profit_pct = float(result['profit_pct'])
    max_volume_usdt = float(result['max_volume_usdt'])
    est_profit_usdt = float(result['estimated_profit_usdt'])

    msg = (
        f"🔄TRIANGLE +{fmt_fixed(profit_pct, 2)}%🔄\n"
        f"Exchange: {triangle['exchange'].upper()}\n"
        f"Route: {direction}\n"
        f"💰 Profit ≈ ${fmt_fixed(est_profit_usdt, 2)}\n"
        f"🪙 Size ${fmt_fixed(max_volume_usdt, 2)} USDT (est.)\n"
    )
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": msg,
        "parse_mode": "Markdown",
        "disable_web_page_preview": True,
    }
    _enqueue_alert(payload, f"Triangle [{direction}]", _last_triangle_sent_time, key, now)

# ----------------------------------------------------------------------
# Reporter
# ----------------------------------------------------------------------
# Exchanges quoted in USDT: fetched book gets converted to MYR using the live rate.
USDT_QUOTED_FETCHERS = {
    'binance': rest_fetch_binance_orderbook,
    'pionex': rest_fetch_pionex_orderbook,
}
# Exchanges quoted directly in MYR: no conversion needed.
MYR_QUOTED_FETCHERS = {
    'luno': rest_fetch_luno_orderbook,
    'hata': rest_fetch_hata_orderbook,
    'sinegy': rest_fetch_sinegy_orderbook,
    'kdx': rest_fetch_kdx_ticker,
    'mx': rest_fetch_mx_orderbook,
}

class Reporter:
    def __init__(self):
        self.cache = PriceDepthCache()
        self.pairs = discover_pairs()
        self.triangles = discover_pionex_triangles() + discover_binance_triangles()
        # Reverse index: (exchange, symbol) -> pair_info, so a WS price update
        # can look up which unified pair it belongs to in O(1) instead of
        # scanning all pairs.
        self._symbol_to_pair: Dict[Tuple[str, str], Dict] = {}
        for pair_info in self.pairs:
            for ex in EXCHANGE_ORDER:
                if ex in pair_info:
                    self._symbol_to_pair[(ex, pair_info[ex])] = pair_info
        # Reverse index: (exchange, symbol) -> list of triangles that use it in
        # any of their 3 legs, so a single price update can trigger checks
        # on every triangle it's part of.
        self._symbol_to_triangles: Dict[Tuple[str, str], List[Dict]] = {}
        for tri in self.triangles:
            for sym in (tri['x_usdt_symbol'], tri['y_usdt_symbol'], tri['cross_symbol']):
                self._symbol_to_triangles.setdefault((tri['exchange'], sym), []).append(tri)
        self.cache.set_on_update(self._on_price_update)
        self.binance_ws = None
        self.pionex_ws = None
        self.luno_ws = None
        self.hata_ws = None
        self.sinegy_ws = None
        self._start_websockets()
        self._start_rate_updater()
        self._start_referral_broadcaster()
        self._start_telegram_sender()
        self._start_keypress_listener()

    def _on_price_update(self, exchange: str, symbol: str):
        """Fired the instant any exchange's cached depth changes (WS push or
        REST poll). Recomputes just this one pair and alerts immediately,
        instead of waiting for the next periodic scan. Reads cache-only
        (use_rest_fallback=False) so this never blocks a WS thread on a
        network call — the periodic monitor() loop still covers filling
        any gaps every _FETCH_SCAN_INTERVAL (10 minutes)."""
        pair_info = self._symbol_to_pair.get((exchange, symbol))
        if pair_info:
            usdt_myr = self.cache.get_usdt_myr()
            prices = self.get_prices(pair_info, usdt_myr=usdt_myr, use_rest_fallback=False)
            if prices:
                opportunities = calculate_opportunities(prices, MIN_PROFIT_PCT)
                for opp in opportunities:
                    if not should_alert(opp):
                        continue
                    send_telegram_alert(opp, pair_info)

        for tri in self._symbol_to_triangles.get((exchange, symbol), []):
            fee = TAKER_FEES.get(exchange, Decimal('0.001'))
            result = calculate_triangle_opportunity(self.cache, tri, fee, MIN_PROFIT_PCT)
            if result:
                send_triangle_alert(result)

    def _start_telegram_sender(self):
        """Single dedicated thread that drains the Telegram send queue."""
        t = threading.Thread(target=_telegram_sender_worker, daemon=True)
        t.start()

    def _start_keypress_listener(self):
        """Background thread: press a letter to toggle an exchange on/off,
        or 'r' to toggle reverse-only mode (only 'reverse' and 'myr'-type
        opportunities alert; myr-to-myr always still shows regardless).
        Press '?' anytime to print the key list. No-ops if stdin isn't an
        interactive terminal (e.g. running under launchd/nohup)."""
        if not sys.stdin.isatty():
            logger.info("Keypress listener skipped (no interactive terminal).")
            return
        try:
            import termios
            import tty
        except ImportError:
            logger.info("Keypress listener skipped (termios/tty unavailable on this platform).")
            return

        def print_help():
            keys = ", ".join(f"{k}={v}" for k, v in EXCHANGE_TOGGLE_KEYS.items())
            print(f"\nℹ️  Toggle keys: {keys}, r=reverse-only mode, ?=this help")

        def listener():
            global REVERSE_ONLY_MODE
            fd = sys.stdin.fileno()
            old_settings = termios.tcgetattr(fd)
            try:
                tty.setcbreak(fd)
                print_help()
                while True:
                    ch = sys.stdin.read(1)
                    if not ch:
                        continue
                    ch = ch.lower()
                    if ch == 'r':
                        with _exchange_state_lock:
                            REVERSE_ONLY_MODE = not REVERSE_ONLY_MODE
                        state = "ON (only reverse + myr-myr alerts)" if REVERSE_ONLY_MODE else "OFF (all types)"
                        print(f"\n🔀 Reverse-only mode: {state}")
                    elif ch in EXCHANGE_TOGGLE_KEYS:
                        ex = EXCHANGE_TOGGLE_KEYS[ch]
                        with _exchange_state_lock:
                            if ex in ENABLED_EXCHANGES:
                                ENABLED_EXCHANGES.discard(ex)
                                state = "OFF"
                            else:
                                ENABLED_EXCHANGES.add(ex)
                                state = "ON"
                        print(f"\n🔁 {ex.upper()}: {state}")
                    elif ch == '?':
                        print_help()
            except Exception as e:
                logger.warning(f"Keypress listener stopped: {e}")
            finally:
                termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

        t = threading.Thread(target=listener, daemon=True)
        t.start()

    def _start_referral_broadcaster(self):
        """Referral messages now fire every REFERRAL_EVERY_N_ALERTS arb alerts
        via _increment_alert_count() — no background thread needed."""
        logger.info(f"Referral broadcaster: will fire every {REFERRAL_EVERY_N_ALERTS} arb alerts.")

    def _start_rate_updater(self):
        """Background thread to fetch USDT/MYR every 60 seconds."""
        def updater():
            logger.info("Starting USDT/MYR rate updater (every 60s)...")
            while True:
                rate = get_usdt_myr_rate()
                if rate is not None:
                    self.cache.set_usdt_myr(rate)
                else:
                    # Keep the last known-good rate rather than wiping the cache —
                    # overwriting with None here would silently disable every
                    # USDT-quoted arb leg until the next successful fetch.
                    logger.debug("USDT/MYR fetch failed, keeping last known rate, will retry in 60s")
                time.sleep(60)
        t = threading.Thread(target=updater, daemon=True)
        t.start()

    def _start_websockets(self):
        # Binance
        # Include triangle-leg symbols alongside the existing cross-exchange
        # USDT pairs, deduplicated, so one WS feed covers both use cases —
        # same pattern as Pionex below. NOTE: unlike Pionex, this manager is
        # a single WS connection (not sharded), so discover_binance_triangles()
        # caps the triangle count to keep the combined symbol list bounded.
        binance_symbols = {p['binance'] for p in self.pairs if 'binance' in p}
        binance_cross_count = len(binance_symbols)
        for tri in self.triangles:
            if tri['exchange'] == 'binance':
                binance_symbols.add(tri['x_usdt_symbol'])
                binance_symbols.add(tri['y_usdt_symbol'])
                binance_symbols.add(tri['cross_symbol'])
        binance_symbols = list(binance_symbols)
        logger.info(f"Binance WS: {binance_cross_count} cross-exchange symbols + "
                    f"{len(binance_symbols) - binance_cross_count} additional triangle-only symbols "
                    f"= {len(binance_symbols)} total")
        if binance_symbols and WEBSOCKET_AVAILABLE:
            self.binance_ws = BinancePublicWSManager(binance_symbols, self.cache)
            self.binance_ws.start()
        else:
            logger.info("Binance WS: no symbols or WS not available")

        # Pionex (WS only – no REST)
        # Include triangle-leg symbols (x_usdt, y_usdt, cross) alongside the
        # existing cross-exchange USDT pairs, deduplicated, so one WS feed
        # covers both use cases.
        pionex_symbols = {p['pionex'] for p in self.pairs if 'pionex' in p}
        triangle_symbol_count_before = len(pionex_symbols)
        for tri in self.triangles:
            if tri['exchange'] == 'pionex':
                pionex_symbols.add(tri['x_usdt_symbol'])
                pionex_symbols.add(tri['y_usdt_symbol'])
                pionex_symbols.add(tri['cross_symbol'])
        pionex_symbols = list(pionex_symbols)
        logger.info(f"Pionex WS: {triangle_symbol_count_before} cross-exchange symbols + "
                    f"{len(pionex_symbols) - triangle_symbol_count_before} additional triangle-only symbols "
                    f"= {len(pionex_symbols)} total")
        if pionex_symbols and WEBSOCKET_AVAILABLE:
            self.pionex_ws = PionexPublicWSManager(pionex_symbols, self.cache)
            self.pionex_ws.start()
        else:
            logger.info("Pionex WS: no symbols or WS not available")

        # Luno
        luno_pairs = [p['luno'] for p in self.pairs if 'luno' in p]
        if luno_pairs and WEBSOCKET_AVAILABLE:
            self.luno_ws = LunoPublicWSManager(luno_pairs, self.cache)
            self.luno_ws.start()
        else:
            logger.info("Luno WS: no pairs or WS not available")

        # Hata
        hata_pairs = [p['hata'] for p in self.pairs if 'hata' in p]
        if hata_pairs and CURL_CFI_AVAILABLE:
            self.hata_ws = HataPublicWSManager(hata_pairs, self.cache)
            self.hata_ws.start()
        else:
            logger.info("Hata WS: no pairs, curl_cffi missing, or WS not available")

        # Sinegy — WS primary, REST fallback handled on-demand in get_prices
        sinegy_pairs = [p['sinegy'] for p in self.pairs if 'sinegy' in p]
        if sinegy_pairs and WEBSOCKET_AVAILABLE:
            self.sinegy_ws = SinegyPublicWSManager(sinegy_pairs, self.cache)
            self.sinegy_ws.start()
        else:
            logger.info("Sinegy WS: no pairs or WS not available")

        # KDX and MX have no WS — depth is fetched in _fetch_all_depths() at
        # the start of every monitor() scan cycle instead of a background poller.

    def stop(self):
        if self.binance_ws: self.binance_ws.stop()
        if self.pionex_ws: self.pionex_ws.stop()
        if self.luno_ws: self.luno_ws.stop()
        if self.hata_ws: self.hata_ws.stop()
        if self.sinegy_ws: self.sinegy_ws.stop()

    def get_prices(self, pair_info: Dict, usdt_myr: Optional[float] = None, use_rest_fallback: bool = True) -> Optional[Dict]:
        prices = {}
        if usdt_myr is None:
            usdt_myr = self.cache.get_usdt_myr()  # fallback if not passed in

        # USDT-quoted exchanges (Binance, Pionex): WS primary, REST fallback,
        # then convert to MYR using the live rate.
        for ex, fetch_fn in USDT_QUOTED_FETCHERS.items():
            if ex not in pair_info or usdt_myr is None or ex not in ENABLED_EXCHANGES:
                continue
            depth = self.cache.get_depth(ex, pair_info[ex], max_age=60.0)
            if not depth and use_rest_fallback:
                raw = fetch_fn(pair_info[ex])
                if raw:
                    self.cache.update_depth(ex, pair_info[ex], raw['bids'], raw['asks'])
                    depth = self.cache.get_depth(ex, pair_info[ex], max_age=60.0)
            if depth:
                usdt_myr_decimal = Decimal(str(usdt_myr))
                bids_myr = [(p * usdt_myr_decimal, q) for p, q in depth['bids']]
                asks_myr = [(p * usdt_myr_decimal, q) for p, q in depth['asks']]
                prices[ex] = {
                    'bid': bids_myr[0][0],
                    'ask': asks_myr[0][0],
                    'bids': bids_myr,
                    'asks': asks_myr,
                    'bids_usdt': depth['bids'],
                    'asks_usdt': depth['asks'],
                    'usdt_myr': usdt_myr_decimal,
                }

        # MYR-quoted exchanges (Luno, Hata, Sinegy, KDX, MX): WS/poller primary,
        # REST fallback, max_age=60 — no currency conversion needed.
        for ex, fetch_fn in MYR_QUOTED_FETCHERS.items():
            if ex not in pair_info or ex not in ENABLED_EXCHANGES:
                continue
            depth = self.cache.get_depth(ex, pair_info[ex], max_age=60.0)
            if not depth and use_rest_fallback:
                depth = fetch_fn(pair_info[ex])
                if depth:
                    self.cache.update_depth(ex, pair_info[ex], depth['bids'], depth['asks'])
                    depth = self.cache.get_depth(ex, pair_info[ex], max_age=60.0)
            if depth:
                prices[ex] = {
                    'bid': depth['bids'][0][0],
                    'ask': depth['asks'][0][0],
                    'bids': depth['bids'],
                    'asks': depth['asks'],
                }

        if len(prices) >= 2:
            ordered = {ex: prices[ex] for ex in EXCHANGE_ORDER if ex in prices}
            return ordered
        return None

    _FETCH_SCAN_INTERVAL = 600.0  # 10 minutes: fetch fresh depth + full scan

    def _fetch_all_depths(self):
        """
        Proactively fetch orderbook depth for REST-only exchanges (KDX, MX)
        in parallel, writing results into self.cache.

        WS exchanges (Binance, Pionex, Luno, Hata, Sinegy) stay live via
        their background managers and are not touched here.
        """
        from concurrent.futures import ThreadPoolExecutor, as_completed

        fetch_map = {
            'kdx': rest_fetch_kdx_ticker,
            'mx':  rest_fetch_mx_orderbook,
        }

        tasks = []
        for pair in self.pairs:
            for ex, fetch_fn in fetch_map.items():
                sym = pair.get(ex)
                if sym:
                    tasks.append((ex, sym, fetch_fn))

        if not tasks:
            return

        def _fetch(ex, sym, fn):
            try:
                raw = fn(sym)
                if raw and raw.get('bids') and raw.get('asks'):
                    self.cache.update_depth(ex, sym, raw['bids'], raw['asks'])
            except Exception as e:
                logger.debug(f"_fetch_all_depths {ex}/{sym}: {e}")

        with ThreadPoolExecutor(max_workers=len(tasks), thread_name_prefix='depth-fetch') as pool:
            futs = [pool.submit(_fetch, ex_name, sym, fn) for ex_name, sym, fn in tasks]
            for f in as_completed(futs):
                pass

    def monitor(self):
        logger.info(f"Starting monitor loop ({self._FETCH_SCAN_INTERVAL:.0f}s fetch+scan interval)...")
        try:
            while True:
                t0 = time.time()

                # 1. Fetch REST-only depths (KDX, MX) in parallel
                self._fetch_all_depths()

                # 2. Snapshot USDT/MYR once so every pair in this scan uses
                #    an identical rate.
                loop_usdt_myr = self.cache.get_usdt_myr()

                # 3. Scan all pairs and triangles with fresh data
                for pair in self.pairs:
                    prices = self.get_prices(pair, usdt_myr=loop_usdt_myr)
                    if not prices:
                        continue
                    opportunities = calculate_opportunities(prices, MIN_PROFIT_PCT)
                    for opp in opportunities:
                        if not should_alert(opp):
                            continue
                        send_telegram_alert(opp, pair)

                for tri in self.triangles:
                    fee = TAKER_FEES.get(tri['exchange'], Decimal('0.001'))
                    result = calculate_triangle_opportunity(self.cache, tri, fee, MIN_PROFIT_PCT)
                    if result:
                        send_triangle_alert(result)

                # 4. Sleep remainder of the 10-minute interval
                elapsed = time.time() - t0
                sleep_for = max(0.0, self._FETCH_SCAN_INTERVAL - elapsed)
                time.sleep(sleep_for)

        except KeyboardInterrupt:
            logger.info("Monitor stopped by user.")
        finally:
            self.stop()

# ----------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------
if __name__ == "__main__":
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        logger.error("TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID must be set in api.txt")
        sys.exit(1)

    try:
        import resource
        soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        target = min(4096, hard) if hard != resource.RLIM_INFINITY else 4096
        if soft < target:
            resource.setrlimit(resource.RLIMIT_NOFILE, (target, hard))
    except:
        pass

    reporter = Reporter()
    try:
        reporter.monitor()
    except KeyboardInterrupt:
        logger.info("Shutting down.")
        reporter.stop()