# Binance Futures RSI Bot (Binance-Handled Trailing Stop, 30m Optimized, SOLUSDT)
# FINAL PRODUCTION VERSION — ALL 22 FIXES + WS → POLLING FALLBACK
# ENHANCED: WebSocket failure → ONE-TIME TG + LOG → switch to REST polling (3s interval)
# ENHANCED: Zero spam, thread-safe, idempotent, crash-proof
# ENHANCED: Wilder RSI, Decimal math, safe quantize, recovery, clean logs

import argparse
import logging
import time
import hmac
import hashlib
import requests
import os
import signal
import sys
import csv
import threading
import traceback
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone, timedelta
import schedule
from urllib.parse import urlencode
import atexit
import websocket
import json
import queue
import feedparser  # ← NEW
import socket

# ------------------- CONFIGURATION -------------------
RISK_PCT = Decimal("0.005")  # 0.5% per trade
SL_PCT = Decimal("0.0075")  # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2.0")  # 2R trailing distance
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 54
BUY_RSI_MAX = 66
SELL_RSI_MIN = 34
SELL_RSI_MAX = 46
POSITION_CHECK_INTERVAL = 60
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = 5.0
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RATE_LIMIT_CHECK_INTERVAL = 60
RATE_LIMIT_THRESHOLD = 80
RECOVERY_CHECK_INTERVAL = 10  # Seconds between recovery checks
TRAIL_UPDATE_THROTTLE = 10.0  # Alert trailing updates every 10 seconds max
POLLING_INTERVAL = 3  # ENHANCED: Polling interval after WS failure
# ---------------------------------------------------------------------------------------
# === CONFIG: BLACKOUT WINDOWS (UTC) ===
# (weekday: 0=Mon..6=Sun, None=every day), (start_h, m), (end_h, m)
NEWS_BLACKOUT_WINDOWS = [
    (4, (12, 25), (13, 5)),     # Friday 12:30–13:00 UTC (NFP)
    (2, (18, 55), (19, 35)),     # Wednesday 19:00–19:30 UTC (FOMC)
]

# === CONFIG: LIVE API ===
LIVE_APIS = [
    "https://nfs.faireconomy.media/ff_calendar_thisweek.json",
    "https://ec.forexprostools.com/?columns=exc_currency,exc_type&timezone=utc"
]
LOCAL_CALENDAR = "high_impact_calendar.json"          # you update weekly
LOCAL_OVERRIDE = "news_calendar_override.json"       # one-off manual block
CACHE_DURATION = 300  # 5 min
HIGH_IMPACT_KEYWORDS = {
    "NFP", "NONFARM", "CPI", "FOMC", "GDP", "UNEMPLOYMENT", "RATE DECISION",
    "PCE", "CORE", "ISM", "JOLTS", "OPEC", "SNB", "BOJ", "GEOPOLITICAL",
    "RETAIL SALES", "ADP", "FLASH", "PRELIMINARY"
}
BUFFER_MINUTES = 5
# === DRAWDOWN-SCALED RISK (NO ATR) ===
BASE_RISK_PCT = Decimal("0.005")        # 0.5% when drawdown = 0%
MAX_DRAWDOWN_PCT = Decimal("0.20")      # Risk → 0 at 20% daily drawdown
MIN_RISK_PCT = Decimal("0.001")         # Never go below 0.1%
# CONFIG SLIPAGE
MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")

# ------------------- GLOBAL STATE -------------------
STOP_REQUESTED = False
client = None
symbol_filters_cache = None
klines_cache = None
klines_cache_time = 0
last_rate_limit_check = 0
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data = []
last_trade_date = None
last_exit_candle_time = None
socket.setdefaulttimeout(10)
# ENHANCED: Thread-safe stop & order cancellation
_stop_lock = threading.Lock()
_orders_cancelled = False

# ENHANCED: WebSocket → Polling fallback state
_ws_failed = False
_polling_active = False
_price_queue = queue.Queue()  # Shared price source (WS or polling)
# ---------------------------------------------------------------------------------------
# === INTERNAL STATE ===
_news_lock = threading.Lock()
_news_cache: list = []
_cache_ts = 0.0
NEWS_LOCK = False          # <--- blocks entry + forces emergency close
VOLATILITY_ABORT = False   # set by ATR spike check (see trading loop)
# === DAILY DRAWDOWN PROTECTION ===
daily_start_equity = None
account_size = None
drawdown_protection_enabled = True
last_news_guard_msg: str | None = None
news_guard_was_active: bool = False
_last_news_block_reason = None
# ---------------------------------------------------------------------------------------
# 4. FETCHERS
# ----------------------------------------------------------------------
def _fetch_json(url: str) -> list | None:
    try:
        r = requests.get(url, timeout=8)
        if r.status_code == 200:
            return r.json()
    except Exception:
        return None
    return None

def _load_local_calendar() -> list:
    if os.path.exists(LOCAL_CALENDAR):
        try:
            with open(LOCAL_CALENDAR) as f:
                return json.load(f)
        except Exception:
            pass
    return []

def _load_override() -> list:
    if os.path.exists(LOCAL_OVERRIDE):
        try:
            with open(LOCAL_OVERRIDE) as f:
                return json.load(f)
        except Exception:
            pass
    return []

def _parse_event(event) -> datetime | None:
    """Return UTC event datetime or None."""
    dt_str = event.get("date") or event.get("timestamp")
    if not dt_str:
        return None
    try:
        # faireconomy: ISO with Z, investing.com: unix ms
        if isinstance(dt_str, (int, float)):
            return datetime.fromtimestamp(dt_str, tz=timezone.utc)
        return datetime.fromisoformat(dt_str.replace("Z", "+00:00"))
    except Exception:
        return None
    
# ----------------------------------------------------------------------
# 4. HELPERS
# ----------------------------------------------------------------------
def _time_in_window(now_utc, start_hm, end_hm):
    start = datetime(now_utc.year, now_utc.month, now_utc.day, *start_hm, tzinfo=timezone.utc)
    end = datetime(now_utc.year, now_utc.month, now_utc.day, *end_hm, tzinfo=timezone.utc)
    if end <= start:
        end += timedelta(days=1)
    return start <= now_utc <= end

def _in_blackout_window(now_utc=None):
    now = now_utc or datetime.now(timezone.utc)
    for wd, start, end in NEWS_BLACKOUT_WINDOWS:
        if wd is None or wd == now.weekday():
            if _time_in_window(now, start, end):
                return True, f"Blackout: {start}–{end} UTC"
    return False, None

# ----------------------------------------------------------------------
# 5. CORE REFRESHER (runs every 60 s)
# ----------------------------------------------------------------------
def _refresh_news():
    global _news_cache, _cache_ts
    now = datetime.now(timezone.utc)
    events = []

    # === 1. Existing economic calendars ===
    for api in LIVE_APIS:
        data = _fetch_json(api)
        if data:
            events.extend(data)
            break
    events.extend(_load_local_calendar())
    events.extend(_load_override())

    high = []
    for e in events:
        title = (e.get("title") or e.get("event") or "").upper()
        impact = (e.get("impact") or "").lower()
        if impact != "high" and not any(k in title for k in HIGH_IMPACT_KEYWORDS):
            continue
        dt = _parse_event(e)
        if dt:
            high.append({"dt": dt, "title": title})

def news_heartbeat():
    global NEWS_LOCK
    while not STOP_REQUESTED:
        _refresh_news()
        now = datetime.now(timezone.utc)
        news_lock = False

        # Economic events
        for ev in _news_cache:
            if (ev["dt"] - timedelta(minutes=BUFFER_MINUTES) <= now <= 
                ev["dt"] + timedelta(minutes=BUFFER_MINUTES)):
                news_lock = True
                break
        static_block, _ = _in_blackout_window(now)
        NEWS_LOCK = news_lock or static_block
        time.sleep(60)

# ----------------------------------------------------------------------
# 6. PUBLIC GUARD (called from trading loop)
# ----------------------------------------------------------------------
_last_news_block_reason = None  # ← MOVE TO TOP

def is_news_blocked(now_utc: datetime | None = None) -> tuple[bool, str | None]:
    global _last_news_block_reason
    now = now_utc or datetime.now(timezone.utc)

    with _news_lock:
        for ev in _news_cache:
            if (ev["dt"] - timedelta(minutes=BUFFER_MINUTES) <= now <= 
                ev["dt"] + timedelta(minutes=BUFFER_MINUTES)):
                reason = f"Live: {ev['title']} @ {ev['dt'].strftime('%H:%M')} UTC"
                if reason != _last_news_block_reason:
                    _last_news_block_reason = reason
                return True, reason

    blocked, reason = _in_blackout_window(now)
    if blocked:
        if reason != _last_news_block_reason:
            _last_news_block_reason = reason
        return True, reason

    if os.path.exists("FORCE_NO_TRADE_TODAY.txt"):
        reason = "Manual override"
        if reason != _last_news_block_reason:
            _last_news_block_reason = reason
        return True, reason

    # === BLACKOUT ENDED ===
    if _last_news_block_reason is not None:
        log("NEWS GUARD -> All clear. Trading resumed.", telegram_bot, telegram_chat_id)
        _last_news_block_reason = None

    return False, None

# ----------------------------------------------------------------------
# 7. EMERGENCY CLOSE (call from monitor_trade_mt5 when NEWS_LOCK flips)
# ----------------------------------------------------------------------
def emergency_close_on_news(client, symbol, trade_state, bot, chat_id):
    if not trade_state.active:
        return
    log("NEWS EMERGENCY CLOSE TRIGGERED", bot, chat_id)
    _request_stop(symbol=symbol, telegram_bot=bot, telegram_chat_id=chat_id)
    trade_state.active = False
    telegram_post(bot, chat_id,
                  f"EMERGENCY CLOSE – HIGH IMPACT NEWS\n"
                  f"Symbol: {symbol} | Side: {trade_state.side}")

# ----------------------------------------------------------------------
# 8. VOLATILITY PROXY (optional – set VOLATILITY_ABORT)
# ----------------------------------------------------------------------
def check_volatility_abort(klines: list, period: int = 14) -> bool:
    """Return True if ATR > 3× 20-period mean."""
    if len(klines) < period + 1:
        return False
    import numpy as np
    highs  = np.array([float(k[2]) for k in klines[-period-20:]])
    lows   = np.array([float(k[3]) for k in klines[-period-20:]])
    closes = np.array([float(k[4]) for k in klines[-period-20:]])
    tr = np.maximum(highs[1:] - lows[1:], np.abs(highs[1:] - closes[:-1]),
                    np.abs(lows[1:] - closes[:-1]))
    atr = np.mean(tr[-period:])
    mean20 = np.mean(tr[-20:])
    return atr > mean20 * 3.0

# === DAILY DRAWDOWN PROTECTION ===
def emergency_close_on_drawdown(client, symbol, bot, chat_id):
    log("DAILY DRAWDOWN EMERGENCY CLOSE TRIGGERED", bot, chat_id)
    _request_stop(symbol=symbol, telegram_bot=bot, telegram_chat_id=chat_id)
    telegram_post(bot, chat_id, "EMERGENCY SHUTDOWN – DRAWDOWN >4%")
# ------------------- PNL LOGGING -------------------
def init_pnl_log():
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r'])
            writer.writeheader()

def log_pnl(trade_id, side, entry, exit_price, qty, R):
    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty
    pnl_r = pnl_usd / R if R > 0 else 0
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': entry,
        'exit': exit_price,
        'pnl_usd': float(pnl_usd),
        'pnl_r': float(pnl_r)
    }
    pnl_data.append(row)
    with open(PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=row.keys())
        writer.writerow(row)
    return row

# ------------------- LOGGING SETUP -------------------
class CustomFormatter(logging.Formatter):
    def formatTime(self, record, datefmt=None):
        dt = datetime.fromtimestamp(record.created, tz=timezone.utc)
        return dt.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3] + '+00:00'

logger = logging.getLogger()
logger.handlers.clear()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(CustomFormatter(fmt='[%(asctime)s] %(message)s'))
logger.addHandler(console_handler)
file_handler = logging.FileHandler('bot.log')
file_handler.setFormatter(CustomFormatter(fmt='[%(asctime)s] %(message)s'))
logger.addHandler(file_handler)

def log(message, telegram_bot=None, telegram_chat_id=None):
    logger.info(message)
    if telegram_bot and telegram_chat_id:
        telegram_post(telegram_bot, telegram_chat_id, message)

# ------------------- TELEGRAM (3x retry + backoff) -------------------
def telegram_post(token, chat_id, text, parse_mode=None):
    if not token or not chat_id:
        return
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {"chat_id": chat_id, "text": text}
    if parse_mode:
        payload["parse_mode"] = parse_mode
    retries = 3
    backoff = 1
    for attempt in range(retries):
        try:
            response = requests.post(url, json=payload, timeout=10)
            if response.status_code == 200:
                return
            else:
                logger.error(f"Telegram send failed (attempt {attempt+1}): HTTP {response.status_code}: {response.text}")
        except Exception as e:
            logger.error(f"Telegram send failed (attempt {attempt+1}): {e}")
        time.sleep(backoff)
        backoff *= 2

# ------------------- TELEGRAM MESSAGES -------------------
def send_trade_telegram(trade_details, bot, chat_id):
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"- Trailing Activation: {trade_details['trail_activation']:.4f}\n"
        f"- Qty: {trade_details['qty']}\n"
    )
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol, side, entry_price, exit_price, qty, pnl_usd, pnl_r, reason, bot, chat_id):
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry Price: {entry_price:.4f}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Reason: {reason}\n"
        f"- Qty: {qty}\n"
        f"- PNL: {pnl_usd:.2f} USDT ({pnl_r:.2f}R)\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_activation_telegram(symbol, side, activation_price, initial_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Activated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Activation Price: {float(activation_price):.4f}\n"
        f"- Initial Stop Price: {float(initial_stop_price):.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_update_telegram(symbol, side, new_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {float(new_stop_price):.4f}\n"
    )
    telegram_post(bot, chat_id, message)

# ------------------- PNL REPORTS -------------------
def calculate_pnl_report(period):
    now = datetime.now(timezone.utc)
    if period == 'daily':
        start_time = now.replace(hour=0, minute=0, second=0, microsecond=0)
    elif period == 'weekly':
        start_time = now - timedelta(days=now.weekday())
        start_time = start_time.replace(hour=0, minute=0, second=0, microsecond=0)
    elif period == 'monthly':
        start_time = now.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    else:
        return "Invalid period specified."
    filtered_trades = [
        trade for trade in pnl_data
        if datetime.fromisoformat(trade['date']) >= start_time
    ]
    if not filtered_trades:
        return f"No trades recorded for the {period} period."
    total_pnl_usd = sum(trade['pnl_usd'] for trade in filtered_trades)
    total_pnl_r = sum(trade['pnl_r'] for trade in filtered_trades)
    num_trades = len(filtered_trades)
    avg_pnl_usd = total_pnl_usd / num_trades if num_trades > 0 else 0
    wins = sum(1 for trade in filtered_trades if trade['pnl_usd'] > 0)
    losses = num_trades - wins
    win_rate = (wins / num_trades * 100) if num_trades > 0 else 0
    return (
        f"{period.capitalize()} PNL Report:\n"
        f"- Total Trades: {num_trades}\n"
        f"- Total PNL: {total_pnl_usd:.2f} USDT\n"
        f"- Average PNL per Trade: {avg_pnl_usd:.2f} USDT\n"
        f"- Total PNL (R): {total_pnl_r:.2f}R\n"
        f"- Win Rate: {win_rate:.2f}% ({wins} wins, {losses} losses)\n"
    )

def send_daily_report(bot, chat_id):
    report = calculate_pnl_report('daily')
    subject = f"Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def send_weekly_report(bot, chat_id):
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def send_monthly_report(bot, chat_id):
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

# ------------------- STOP HANDLER (IDEMPOTENT) -------------------
def _request_stop(signum=None, frame=None, symbol=None, telegram_bot=None, telegram_chat_id=None):
    global STOP_REQUESTED, client, _orders_cancelled
    with _stop_lock:
        if STOP_REQUESTED:
            logger.info("Stop already requested; skipping duplicate cleanup.")
            return
        STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    if not client or not symbol:
        log("Client or symbol not defined; skipping position closure and order cancellation.")
        return
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
        if pos_amt != 0:
            side = "SELL" if pos_amt > 0 else "BUY"
            qty = abs(pos_amt)
            entry_price = Decimal(str(pos_item.get("entryPrice", "0"))) if pos_item else Decimal('0')
            response = client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": str(qty)
            })
            log(f"Closed position: qty={qty} {side}")
            exit_price = client.get_latest_fill_price(symbol, response.get("orderId"))
            if exit_price is None:
                ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                exit_price = Decimal(str(ticker.get("price")))
            exit_price_f = float(exit_price)
            R = entry_price * SL_PCT if entry_price else Decimal('0')
            pnl_row = log_pnl(len(pnl_data) + 1, "LONG" if pos_amt > 0 else "SHORT", float(entry_price), exit_price_f, float(qty), float(R))
            if telegram_bot and telegram_chat_id:
                send_closure_telegram(symbol, "LONG" if pos_amt > 0 else "SHORT", float(entry_price), exit_price_f, float(qty), pnl_row['pnl_usd'], pnl_row['pnl_r'], "Stop Requested", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Stop handler error while closing position: {str(e)}")
    with _stop_lock:
        if not _orders_cancelled:
            try:
                client.cancel_all_open_orders(symbol)
                log(f"All open orders cancelled for {symbol}.")
            except Exception as e:
                log(f"Failed to cancel open orders: {e}")
            _orders_cancelled = True

# ------------------- TIME SYNC -------------------
def check_time_offset(base_url):
    try:
        start_time = time.time()
        response = requests.get(f"{base_url}/fapi/v1/time", timeout=5)
        server_time_ms = response.json()['serverTime']
        offset = (datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc) - datetime.now(timezone.utc)).total_seconds()
        request_duration = time.time() - start_time
        log(f"Time offset from Binance: {offset} seconds, request duration: {request_duration:.3f}s")
        return request_duration
    except Exception as e:
        log(f"Binance time sync failed: {e}")
        return None

# ------------------- BINANCE CLIENT -------------------
class BinanceAPIError(Exception):
    def __init__(self, message, status_code=None, payload=None):
        super().__init__(message)
        self.status_code = status_code
        self.payload = payload

class BinanceClient:
    def __init__(self, api_key, api_secret, use_live=False, base_override=None):
        self.api_key = api_key
        self.api_secret = api_secret
        self.use_live = use_live
        self.base = base_override or ("https://fapi.binance.com" if use_live else "https://testnet.binancefuture.com")
        self.ping_latency = check_time_offset(self.base)
        self.dual_side = self._check_position_mode()
        log(f"Using base URL: {self.base}, Position Mode: {'Hedge' if self.dual_side else 'One-way'}")

    def _check_position_mode(self):
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            return response.get('dualSidePosition', False)
        except Exception as e:
            log(f"Position mode check failed: {str(e)}. Assuming one-way mode.")
            return False

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: dict = None):
        params = params.copy() if params else {}
        params["timestamp"] = int(time.time() * 1000)
        params["recvWindow"] = 30000
        query = urlencode({k: str(params[k]) for k in sorted(params.keys())})
        signature = self._sign(query)
        url = f"{self.base}{endpoint}?{query}&signature={signature}"
        headers = {"X-MBX-APIKEY": self.api_key}

        for attempt in range(MAX_RETRIES):
            try:
                r = requests.request(method, url, headers=headers, timeout=REQUEST_TIMEOUT)

                if r.status_code == 200:
                    return r.json()

                if r.status_code in (429, 503) or "throttled" in r.text.lower():
                    wait = (2 ** attempt) * 10
                    log(f"Rate limited (HTTP {r.status_code}). Retrying in {wait}s… (Attempt {attempt + 1}/{MAX_RETRIES})")
                    time.sleep(wait)
                    continue

                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", r.status_code, r.text)

            except (requests.exceptions.Timeout, requests.exceptions.ConnectionError) as e:
                if attempt < MAX_RETRIES - 1:
                    wait = (2 ** attempt) * 5
                    log(f"Network error: {e}. Retrying in {wait}s… (Attempt {attempt + 1}/{MAX_RETRIES})")
                    time.sleep(wait)
                    continue
                raise BinanceAPIError(f"Network failed after {MAX_RETRIES} retries: {str(e)}")
            except Exception as e:
                raise BinanceAPIError(f"Request failed: {str(e)}", payload=str(e))

        raise BinanceAPIError("Max retries exceeded")

    def public_request(self, path: str, params: dict = None):
        url = f"{self.base}{path}"
        try:
            r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                return r.json()
            else:
                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", r.status_code, r.text)
        except Exception as e:
            raise BinanceAPIError(f"Public request failed: {str(e)}", payload=str(e))

    def get_latest_trade_details(self, symbol):
        params = {"symbol": symbol, "limit": 1}
        try:
            response = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            trades = response if isinstance(response, list) else []
            if trades:
                trade = trades[0]
                return {
                    "price": Decimal(str(trade.get("price", "0"))),
                    "orderId": trade.get("orderId"),
                    "qty": Decimal(str(trade.get("qty", "0"))),
                    "side": trade.get("side")
                }
            return None
        except Exception as e:
            log(f"Failed to fetch latest trade details: {str(e)}")
            return None

    def get_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        response = self.send_signed_request("GET", "/fapi/v1/openOrders", params)
        return response if isinstance(response, list) else []

    def cancel_all_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        return self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", params)

    def cancel_order(self, symbol: str, order_id: int):
        params = {"symbol": symbol, "orderId": order_id}
        return self.send_signed_request("DELETE", "/fapi/v1/order", params)

    def get_latest_fill_price(self, symbol: str, order_id: int):
        params = {"symbol": symbol, "orderId": order_id}
        try:
            trades = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            if trades and len(trades) > 0:
                return Decimal(str(trades[-1].get("price", "0")))
            return None
        except Exception as e:
            log(f"Failed to fetch fill price: {str(e)}")
            return None

    def place_stop_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal, reduce_only: bool = True, position_side: str = None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "STOP_MARKET",
            "stopPrice": str(stop_price),
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false"
        }
        if self.dual_side and position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

    def place_take_profit_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal, reduce_only: bool = True, position_side: str = None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "TAKE_PROFIT_MARKET",
            "stopPrice": str(stop_price),
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false"
        }
        if self.dual_side and position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal, callback_rate: Decimal, activation_price: Decimal, reduce_only: bool = True, position_side: str = None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "TRAILING_STOP_MARKET",
            "callbackRate": str(callback_rate),
            "activationPrice": str(activation_price),
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false"
        }
        if self.dual_side and position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

# ------------------- INDICATORS (WILDER RSI) -------------------
def compute_rsi(closes, period=RSI_PERIOD):
    if len(closes) < period + 1:
        return None
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    gains = [max(d, 0) for d in deltas]
    losses = [max(-d, 0) for d in deltas]
    if len(gains) < period:
        return None
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
    if avg_loss == 0:
        return  100.0
    rs = avg_gain / avg_loss
    return round(100 - 100 / (1 + rs), 2)

def sma(data, period):
    if len(data) < period:
        return None
    return sum(data[-period:]) / period

def quantize_qty(qty: Decimal, step_size: Decimal) -> Decimal:
    q = (qty // step_size) * step_size
    if q == 0:
        q = step_size
    return q.quantize(step_size)

def quantize_price(p: Decimal, tick_size: Decimal, rounding=ROUND_HALF_EVEN) -> Decimal:
    return p.quantize(tick_size, rounding=rounding)

# === 45m AGGREGATION + ALIGNMENT (BEST VERSION) ===

def aggregate_klines_to_45m(klines_15m):
    if len(klines_15m) < 3:
        return []

    aggregated = []
    # Start from the newest complete group of 3 → guarantees a candle every 45 min
    for i in range(len(klines_15m) - 3, -1, -3):   # reverse loop, step -3
        chunk = klines_15m[i:i+3][::-1]             # take 3 and reverse to chronological
        if len(chunk) != 3:
            continue
        a, b, c = chunk[0], chunk[1], chunk[2]     # a = oldest, c = newest

        open_time  = int(a[0])
        close_time = int(c[6])

        # Strict perfect alignment (Binance 15m is always perfect)
        if close_time - open_time != 45 * 60 * 1000:
            continue

        high = max(float(a[2]), float(b[2]), float(c[2]))
        low  = min(float(a[3]), float(b[3]), float(c[3]))

        aggregated.append([
            open_time,
            float(a[1]),   # open
            high,
            low,
            float(c[4]),   # close
            float(a[5]) + float(b[5]) + float(c[5]),  # volume
            close_time
        ])

    aggregated.reverse()   # back to chronological order
    return aggregated

# ------------------- SYMBOL FILTERS -------------------
def get_symbol_filters(client: BinanceClient, symbol: str):
    global symbol_filters_cache
    if symbol_filters_cache is not None:
        return symbol_filters_cache
    info = client.public_request("/fapi/v1/exchangeInfo")
    s = next((x for x in info.get("symbols", []) if x.get("symbol") == symbol.upper()), None)
    if not s:
        raise ValueError(f"{symbol} not found in exchangeInfo")
    filters = {f["filterType"]: f for f in s.get("filters", [])}
    lot = filters.get("LOT_SIZE")
    if not lot:
        raise ValueError("LOT_SIZE filter missing for symbol")
    step_size = Decimal(str(lot["stepSize"]))
    min_qty = Decimal(str(lot["minQty"]))
    tick_size = Decimal(str(filters.get("PRICE_FILTER", {}).get("tickSize", "0.00000001")))
    min_notional = Decimal(str(filters.get("MIN_NOTIONAL", {}).get("notional", "0")))
    symbol_filters_cache = {"stepSize": step_size, "minQty": min_qty, "tickSize": tick_size, "minNotional": min_notional}
    return symbol_filters_cache

# ------------------- ORDERS (REUSABLE) -------------------
def place_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    entry_price = Decimal(str(trade_state.entry_price or '0'))
    qty_dec = Decimal(str(trade_state.qty))
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    pos_side = trade_state.side
    R = entry_price * SL_PCT
    if trade_state.side == "LONG":
        sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
        sl_rounding = ROUND_DOWN
        tp_price_dec = entry_price + (TP_MULT * R)
        tp_rounding = ROUND_UP
        trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R)
    else:
        sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
        sl_rounding = ROUND_UP
        tp_price_dec = entry_price - (TP_MULT * R)
        tp_rounding = ROUND_DOWN
        trail_activation_price_dec = entry_price - (TRAIL_TRIGGER_MULT * R)
    sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
    tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
    trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
    callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
    try:
        sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=pos_side)
        trade_state.sl_order_id = sl_order.get("orderId")
        trade_state.sl = float(sl_price_dec_quant)
        log(f"Placed STOP_MARKET SL: {sl_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)
    try:
        tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=pos_side)
        trade_state.tp_order_id = tp_order.get("orderId")
        trade_state.tp = float(tp_price_dec_quant)
        log(f"Placed TAKE_PROFIT_MARKET TP: {tp_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)
    try:
        trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, trail_activation_price_dec_quant, reduce_only=True, position_side=pos_side)
        trade_state.trail_order_id = trail_order.get("orderId")
        trade_state.trail_activation_price = float(trail_activation_price_dec_quant)
        log(f"Placed TRAILING_STOP_MARKET: {trail_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)

# ------------------- HELPER: KLINE DATA EXTRACTION -------------------
def closes_and_volumes_from_klines(klines):
    closes = [float(k[4]) for k in klines]
    volumes = [float(k[5]) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [float(k[1]) for k in klines]
    return closes, volumes, close_times, opens

# ------------------- DATA FETCHING -------------------
def fetch_klines(client, symbol, interval, limit=max(100, VOL_SMA_PERIOD + 50)):
    # preserve original requested timeframe
    requested = interval
    if requested == "45m":
        interval = "15m"
        limit = max(limit, 300)  # Need 3x more for safe aggregation

    try:
        raw = client.public_request("/fapi/v1/klines", {
            "symbol": symbol,
            "interval": interval,
            "limit": limit
        })

        # if the caller requested 45m, aggregate the fetched 15m klines
        if interval == "15m" and requested == "45m":
            return aggregate_klines_to_45m(raw)   # ← new drift-proof version

        return raw

    except Exception as e:
        log(f"Klines fetch failed: {e}")
        raise


def fetch_balance(client: BinanceClient):
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
        return Decimal(str(data.get("totalWalletBalance", 0)))
    except Exception as e:
        log(f"Balance fetch failed: {str(e)}")
        raise

def has_active_position(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        for p in positions:
            if p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != 0:
                return True
        return False
    except Exception as e:
        log(f"Position check failed: {str(e)}")
        return False

def fetch_open_positions_details(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        return next((p for p in positions if p.get("symbol") == symbol), None)
    except Exception as e:
        log(f"Position details fetch failed: {str(e)}")
        raise

# ------------------- TRADE STATE -------------------
class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price = None
        self.qty = None
        self.side = None
        self.entry_close_time = None
        self.initial_sl = None
        self.sl = None
        self.tp = None
        self.trail_activation_price = None
        self.highest_price = None
        self.lowest_price = None
        self.current_trail_stop = None
        self.trail_activated = False
        self.last_trail_alert = 0.0
        self.risk = None
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_order_id = None
def debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    """Recover missing SL/TP/Trailing orders. Idempotent. Thread-safe. No fake 'Stop Requested'."""
    if not trade_state.active:
        return

    try:
        open_orders = {o["orderId"]: o for o in client.get_open_orders(symbol)}

        # === RECOVER SL ===
        if trade_state.sl_order_id and trade_state.sl_order_id not in open_orders:
            log(f"SL missing (ID={trade_state.sl_order_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            sl_price = _calc_sl_price(trade_state.entry_price, trade_state.side, tick_size)
            new_sl = _place_stop_market(client, symbol, trade_state, sl_price)
            if new_sl:
                trade_state.sl_order_id = new_sl["orderId"]
                trade_state.sl = float(sl_price)
                _tg_notify("SL Recovered", f"New Stop: {trade_state.sl:.4f}\nOrder ID: {trade_state.sl_order_id}", symbol, telegram_bot, telegram_chat_id)
        # === RECOVER TP ===
        if trade_state.tp_order_id and trade_state.tp_order_id not in open_orders:
            log(f"TP missing (ID={trade_state.tp_order_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            tp_price = _calc_tp_price(trade_state.entry_price, trade_state.side, tick_size)
            new_tp = _place_take_profit(client, symbol, trade_state, tp_price)
            if new_tp:
                trade_state.tp_order_id = new_tp["orderId"]
                trade_state.tp = float(tp_price)
                _tg_notify("TP Recovered", f"New TP: {trade_state.tp:.4f}\nOrder ID: {trade_state.tp_order_id}", symbol, telegram_bot, telegram_chat_id)

        # === RECOVER TRAILING ===
        if trade_state.trail_order_id and trade_state.trail_order_id not in open_orders:
            log(f"Trailing missing (ID={trade_state.trail_order_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            act_price = _calc_trail_activation(trade_state.entry_price, trade_state.side, tick_size)
            new_trail = _place_trailing_stop(client, symbol, trade_state, act_price)
            if new_trail:
                trade_state.trail_order_id = new_trail["orderId"]
                trade_state.trail_activation_price = float(act_price)
                trade_state.current_trail_stop = float(new_trail.get("stopPrice") or act_price)
                _tg_notify("Trailing Recovered", f"Activation: {trade_state.trail_activation_price:.4f}\nOrder ID: {trade_state.trail_order_id}", symbol, telegram_bot, telegram_chat_id)

    except Exception as e:
        log(f"Recovery failed: {e}", telegram_bot, telegram_chat_id)


# === PRIVATE HELPERS (DRY + SAFE) ===
def _calc_sl_price(entry, side, tick_size):
    sl = Decimal(str(entry)) * (Decimal("1") - SL_PCT) if side == "LONG" else Decimal(str(entry)) * (Decimal("1") + SL_PCT)
    return quantize_price(sl, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

def _calc_tp_price(entry, side, tick_size):
    R = Decimal(str(entry)) * SL_PCT
    tp = Decimal(str(entry)) + (TP_MULT * R) if side == "LONG" else Decimal(str(entry)) - (TP_MULT * R)
    return quantize_price(tp, tick_size, ROUND_UP if side == "LONG" else ROUND_DOWN)

def _calc_trail_activation(entry, side, tick_size):
    R = Decimal(str(entry)) * SL_PCT
    act = Decimal(str(entry)) + (TRAIL_TRIGGER_MULT * R) if side == "LONG" else Decimal(str(entry)) - (TRAIL_TRIGGER_MULT * R)
    return quantize_price(act, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

def _place_stop_market(client, symbol, ts, price):
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = Decimal(str(ts.qty))
    try:
        return client.place_stop_market(symbol, side, qty, price, reduce_only=True, position_side=ts.side)
    except: return None

def _place_take_profit(client, symbol, ts, price):
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = Decimal(str(ts.qty))
    try:
        return client.place_take_profit_market(symbol, side, qty, price, reduce_only=True, position_side=ts.side)
    except: return None

def _place_trailing_stop(client, symbol, ts, act_price):
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = Decimal(str(ts.qty))
    rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
    try:
        return client.place_trailing_stop_market(symbol, side, qty, rate, act_price, reduce_only=True, position_side=ts.side)
    except: return None

def _tg_notify(title, body, symbol, bot, chat_id):
    if bot and chat_id:
        telegram_post(bot, chat_id, f"{title} for {symbol}\n{body}")
# ------------------- POLLING FALLBACK -------------------
def start_polling_mode(symbol, telegram_bot, telegram_chat_id):
    global _polling_active
    if _polling_active:
        return
    _polling_active = True
    log(f"Now polling price every {POLLING_INTERVAL}s via REST API.", telegram_bot, telegram_chat_id)

    def polling_loop():
        while _polling_active and not STOP_REQUESTED:
            try:
                ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                price = Decimal(str(ticker['price']))
                _price_queue.put(price)
            except Exception as e:
                log(f"Polling failed: {e}. Will retry...", telegram_bot, telegram_chat_id)
            time.sleep(POLLING_INTERVAL)

    threading.Thread(target=polling_loop, daemon=True).start()

# ------------------- MONITOR TRADE (FULLY CORRECTED) -------------------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, current_candle_close_time):
    global _orders_cancelled, _polling_active, _ws_failed
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    last_recovery_check = 0
    current_price = None
    ws = None
    ws_running = False

    # === WEBSOCKET CALLBACKS ===
    def on_message(ws_app, message):
        nonlocal current_price
        try:
            data = json.loads(message)
            if data.get('e') == 'trade' and 'p' in data:
                current_price = Decimal(str(data['p']))
                _price_queue.put(current_price)
        except Exception as e:
            log(f"WebSocket parse error: {e}", telegram_bot, telegram_chat_id)

    def on_error(ws_app, error):
        global _ws_failed
        if not _ws_failed and trade_state.active:
            log("WebSocket connection failed. Switching to polling mode.", telegram_bot, telegram_chat_id)
            telegram_post(telegram_bot, telegram_chat_id, "WebSocket failed  Switched to REST polling (3s)")
            _ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)

    def on_close(ws_app, close_status_code, close_reason):
        global _ws_failed
        if not _ws_failed and trade_state.active:
            log("WebSocket closed. Switching to polling mode.", telegram_bot, telegram_chat_id)
            _ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)

    def on_open(ws_app):
        subscribe_msg = {
            "method": "SUBSCRIBE",
            "params": [f"{symbol.lower()}@trade"],
            "id": 1
        }
        ws_app.send(json.dumps(subscribe_msg))
        log(f"WebSocket subscribed to {symbol.lower()}@trade", telegram_bot, telegram_chat_id)

    def start_ws():
        nonlocal ws, ws_running
        if ws_running:
            return
        base_url = "wss://fstream.binance.com/ws" if client.use_live else "wss://stream.binancefuture.com/ws"
        log(f"Connecting to WebSocket: {base_url}", telegram_bot, telegram_chat_id)
        ws = websocket.WebSocketApp(
            base_url,
            on_open=on_open,
            on_message=on_message,
            on_error=on_error,
            on_close=on_close
        )
        thread = threading.Thread(
            target=ws.run_forever,
            kwargs={'ping_interval': 20, 'ping_timeout': 10},
            daemon=True
        )
        thread.start()
        ws_running = True

    start_ws()

    try:
        while trade_state.active and not STOP_REQUESTED:
            # === FETCH KLINES FOR VOLATILITY ===
            try:
                klines = fetch_klines(client, symbol, "30m", limit=100)
            except:
                klines = []

            # NEWS EMERGENCY
            if NEWS_LOCK and trade_state.active:
                emergency_close_on_news(client, symbol, trade_state, telegram_bot, telegram_chat_id)
                return

            # DAILY DRAWDOWN CHECK
            if drawdown_protection_enabled and daily_start_equity is not None:
                try:
                    balance = fetch_balance(client)
                    pos = fetch_open_positions_details(client, symbol)
                    unrealized_pnl = Decimal(str(pos.get("unRealizedProfit", "0")))
                    current_equity = balance + unrealized_pnl
                    drawdown = (daily_start_equity - current_equity) / daily_start_equity
                    if drawdown > Decimal("0.04"):
                        log(f"DAILY DRAWDOWN BREACH: {drawdown:.1%} > 4% | AUTO-CLOSING ALL", telegram_bot, telegram_chat_id)
                        emergency_close_on_drawdown(client, symbol, telegram_bot, telegram_chat_id)
                        return
                except Exception as e:
                    log(f"Drawdown check failed: {e}", telegram_bot, telegram_chat_id)

            # VOLATILITY ABORT
            if len(klines) >= 100 and check_volatility_abort(klines):
                log("VOLATILITY EMERGENCY CLOSE – ATR SPIKE >3x", telegram_bot, telegram_chat_id)
                _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
                telegram_post(telegram_bot, telegram_chat_id, "EMERGENCY CLOSE – ATR SPIKE >3x")
                return
            # --- Recovery Check ---
            if time.time() - last_recovery_check >= RECOVERY_CHECK_INTERVAL:
                debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                last_recovery_check = time.time()

            # --- Get Latest Price ---
            try:
                current_price = _price_queue.get_nowait()
            except queue.Empty:
                pass

            # --- Position Check ---
            try:
                pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
                positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
                pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
                pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')

                if pos_amt == 0:
                    log("Position closed.", telegram_bot, telegram_chat_id)
                    trade_state.active = False

                    # --- Get Exit Price ---
                    latest_trade = client.get_latest_trade_details(symbol)
                    exit_price = latest_trade["price"] if latest_trade else None
                    if exit_price is None:
                        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        exit_price = Decimal(str(ticker.get("price", "0")))
                    exit_price_f = float(exit_price)

                    # --- Determine Exit Reason (Trailing > TP > SL > Manual) ---
                    reason = "Manual Close"
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        reason = "Stop Requested"
                    else:
                        try:
                            recent = client.send_signed_request("GET", "/fapi/v1/userTrades", {"symbol": symbol, "limit": 5})
                            close_trades = [t for t in recent if abs(Decimal(t.get('qty', '0'))) >= Decimal(str(trade_state.qty)) * Decimal('0.9')]
                            if close_trades:
                                exit_p = Decimal(close_trades[0]['price'])
                                # Check trailing stop first
                                if (trade_state.current_trail_stop and 
                                    abs(exit_p - Decimal(str(trade_state.current_trail_stop))) < tick_size * 20):
                                    reason = "Trailing Stop"
                                elif abs(exit_p - Decimal(str(trade_state.sl))) < tick_size * 20:
                                    reason = "Stop Loss"
                                elif abs(exit_p - Decimal(str(trade_state.tp))) < tick_size * 20:
                                    reason = "Take Profit"
                        except Exception as e:
                            log(f"Failed to detect exit reason: {e}", telegram_bot, telegram_chat_id)

                    # --- Log PNL ---
                    entry_price_safe = float(trade_state.entry_price or 0.0)
                    R = Decimal(str(entry_price_safe)) * SL_PCT
                    R_float = float(R)
                    pnl_row = log_pnl(
                        len(pnl_data) + 1,
                        trade_state.side,
                        entry_price_safe,
                        exit_price_f,
                        float(trade_state.qty or 0),
                        R_float
                    )

                    # --- Send Telegram ---
                    send_closure_telegram(
                        symbol, trade_state.side,
                        entry_price_safe, exit_price_f,
                        float(trade_state.qty or 0),
                        float(pnl_row['pnl_usd']), float(pnl_row['pnl_r']),
                        reason, telegram_bot, telegram_chat_id
                    )

                    # --- Cancel Orders (Thread-Safe) ---
                    with _stop_lock:
                        if not _orders_cancelled:
                            try:
                                client.cancel_all_open_orders(symbol)
                                log(f"Cancelled open orders. Reason: {reason}", telegram_bot, telegram_chat_id)
                            except Exception as e:
                                log(f"Failed to cancel orders: {e}", telegram_bot, telegram_chat_id)
                            _orders_cancelled = True

                    return  # Exit monitor cleanly

                # --- Fallback Price ---
                if current_price is None:
                    try:
                        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        current_price = Decimal(str(ticker.get("price")))
                    except:
                        pass

                # --- Update High/Low ---
                if trade_state.side == "LONG":
                    if trade_state.highest_price is None or current_price > trade_state.highest_price:
                        trade_state.highest_price = current_price
                else:
                    if trade_state.lowest_price is None or current_price < trade_state.lowest_price:
                        trade_state.lowest_price = current_price

                # --- Trailing Activation ---
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    trail_activation_price_dec = Decimal(str(trade_state.trail_activation_price))
                    if (trade_state.side == "LONG" and current_price >= trail_activation_price_dec) or \
                       (trade_state.side == "SHORT" and current_price <= trail_activation_price_dec):
                        trade_state.trail_activated = True
                        R_dec = Decimal(str(trade_state.risk))
                        activation_dec = Decimal(str(trade_state.trail_activation_price))

                        if trade_state.side == "LONG":
                            init_stop_raw = activation_dec - (TRAIL_DISTANCE_MULT * R_dec)
                            init_stop = float(quantize_price(init_stop_raw, tick_size, ROUND_DOWN))
                        else:
                            init_stop_raw = activation_dec + (TRAIL_DISTANCE_MULT * R_dec)
                            init_stop = float(quantize_price(init_stop_raw, tick_size, ROUND_UP))

                        send_trailing_activation_telegram(
                            symbol, trade_state.side,
                            float(current_price), init_stop,
                            telegram_bot, telegram_chat_id
                        )
                        trade_state.current_trail_stop = init_stop
                        trade_state.last_trail_alert = time.time()

                # --- TRAILING UPDATES (NATIVE BINANCE TRACKING ONLY) ---
                if trade_state.trail_activated and time.time() - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE:
                    R_dec = Decimal(str(trade_state.risk))
                    updated = False
                    new_stop_f = None

                    if trade_state.side == "LONG":
                        expected_stop_raw = trade_state.highest_price - (TRAIL_DISTANCE_MULT * R_dec)
                        expected_stop = quantize_price(expected_stop_raw, tick_size, ROUND_DOWN)
                        current_stop = Decimal(str(trade_state.current_trail_stop or '0'))
                        if expected_stop > current_stop:
                            updated = True
                            new_stop_f = float(expected_stop)
                    else:
                        expected_stop_raw = trade_state.lowest_price + (TRAIL_DISTANCE_MULT * R_dec)
                        expected_stop = quantize_price(expected_stop_raw, tick_size, ROUND_UP)
                        current_stop = Decimal(str(trade_state.current_trail_stop or '0'))
                        if expected_stop < current_stop:
                            updated = True
                            new_stop_f = float(expected_stop)

                    if updated:
                        trade_state.current_trail_stop = new_stop_f
                        trade_state.last_trail_alert = time.time()
                        send_trailing_update_telegram(symbol, trade_state.side, new_stop_f, telegram_bot, telegram_chat_id)

                time.sleep(1)

            except Exception as e:
                log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
                time.sleep(2)

    finally:
        if not trade_state.active:
            _polling_active = False
            _ws_failed = False
            try:
                if ws and ws_running:
                    ws.close()
            except:
                pass
# ------------------- TRADING LOOP -------------------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, telegram_bot, telegram_chat_id):
    global last_news_guard_msg, news_guard_was_active
    global last_trade_date
    trades_today = 0
    last_processed_time = 0
    trade_state = TradeState()
    qty_api = None  # ← ADD THIS
    pending_entry = False
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    min_qty = filters['minQty']
    tick_size = filters['tickSize']
    min_notional = filters['minNotional']
    max_trades_alert_sent = False

    # === DAILY RESET STATE ===
    current_date = datetime.now(timezone.utc).date()
    if last_trade_date != current_date:
        trades_today = 0
        last_trade_date = current_date
        max_trades_alert_sent = False
    daily_start_balance = fetch_balance(client)

    signal.signal(signal.SIGINT, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    signal.signal(signal.SIGTERM, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    log(f"Starting bot with symbol={symbol}, timeframe={timeframe}, risk_pct={risk_pct*100}%")

    # === RECOVER EXISTING POSITION ON STARTUP ===
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol)
        pos_amt = Decimal(str(pos.get("positionAmt", "0")))
        if pos_amt != 0:
            trade_state.active = True
            trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
            trade_state.qty = float(abs(pos_amt))
            trade_state.entry_price = float(Decimal(str(pos.get("entryPrice", "0"))))
            trade_state.risk = Decimal(str(trade_state.entry_price)) * SL_PCT
            trade_state.sl_order_id = None
            trade_state.tp_order_id = None
            trade_state.trail_order_id = None
            log("Existing position detected on startup. Recovering orders...", telegram_bot, telegram_chat_id)
            debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, close_time)

    # === MAIN LOOP ===
    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            # === DAILY RESET CHECK (UTC MIDNIGHT) ===
            current_date = datetime.now(timezone.utc).date()
            if last_trade_date != current_date:
                trades_today = 0
                last_trade_date = current_date
                daily_start_balance = fetch_balance(client)
                max_trades_alert_sent = False
                log(f"New UTC day: {current_date}. Resetting trade counter and balance.", telegram_bot, telegram_chat_id)

            # === MAX TRADES PER DAY ===
            if trades_today >= max_trades_per_day:
                if not max_trades_alert_sent:
                    log(f"Maximum trades reached for the day ({max_trades_per_day}). Sleeping until next day.", telegram_bot, telegram_chat_id)
                    max_trades_alert_sent = True
                time.sleep(60)
                continue

            # === MAX DAILY LOSS PROTECTION ===
            if use_max_loss:
                current_bal = fetch_balance(client)
                loss_threshold = daily_start_balance * (max_daily_loss_pct / Decimal("100"))
                if daily_start_balance - current_bal > loss_threshold:
                    log(f"Max daily loss reached ({loss_threshold:.2f} USDT). Waiting for next day.", telegram_bot, telegram_chat_id)
                    time.sleep(60)
                    continue

            # === GET SERVER TIME ===
            try:
                server_time_response = client.public_request("/fapi/v1/time")
                server_time = server_time_response["serverTime"]
            except Exception as e:
                log(f"Failed to get server time: {e}. Using local time.", telegram_bot, telegram_chat_id)
                server_time = int(time.time() * 1000)

            # === WAIT FOR NEXT CANDLE CLOSE ===
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                log(f"Waiting for candle close in {sleep_seconds:.2f}s ...", telegram_bot, telegram_chat_id)
                _safe_sleep(sleep_seconds)
                continue

            # ------------------------------------------------------------
            # 5. FETCH FRESH KLINES (WITH 45m AGGREGATION)
            # ------------------------------------------------------------
            try:
                klines = fetch_klines(client, symbol, timeframe)
            except Exception as e:
                log(f"Klines fetch failed: {e}", telegram_bot, telegram_chat_id)
                time.sleep(2)
                continue

            if not klines:
                log("No klines received — retrying in 5s")
                time.sleep(5)
                continue

            # ------------------------------------------------------------
            # 6. ALIGN TO LAST CANDLE CLOSE + ADD 100ms BUFFER
            # ------------------------------------------------------------
            last_candle = klines[-1]
            last_close_time = int(last_candle[6])  # ms
            close_time = last_close_time

            dt = datetime.fromtimestamp(last_close_time / 1000, tz=timezone.utc)
            log(f"Aligned to {timeframe} candle close: {dt.strftime('%H:%M')} UTC")

            # ------------------------------------------------------------
            # 7. PREVENT REPROCESSING SAME CANDLE
            # ------------------------------------------------------------
            if last_close_time <= last_processed_time:
                log("Candle already processed or not fully closed.")
                time.sleep(1)
                continue
            last_processed_time = last_close_time + 100
            # ------------------------------------------------------------
            # 8. EXTRACT OHLCV DATA
            # ------------------------------------------------------------
            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            curr_vol = volumes[-1]
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price

            # ------------------------------------------------------------
            # 9. COMPUTE INDICATORS
            # ------------------------------------------------------------
            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD) if len(volumes) >= VOL_SMA_PERIOD else 0

            # === SMART CANDLE LOG (ONLY ON CHANGE) ===
            current_state = f"{close_price:.4f}|{rsi:.2f}|{curr_vol:.0f}|{vol_sma15:.2f}|{'G' if is_green_candle else 'R'}"
            if not hasattr(trading_loop, "last_candle_state") or current_state != trading_loop.last_candle_state:
                log(f"Candle: {close_price:.4f} RSI={rsi:.2f} Vol={curr_vol:.0f} SMA15={vol_sma15:.2f} {'Green' if is_green_candle else 'Red'}", telegram_bot, telegram_chat_id)
                trading_loop.last_candle_state = current_state

            # === ENTRY GUARDS ===
            
            # === NEWS GUARD – MUST BE INSIDE THE LOOP ===

            blocked, reason = is_news_blocked()
            now_active = blocked

            # Guard just became ACTIVE
            if now_active and not news_guard_was_active:
                msg = f"NEWS GUARD -> {reason}"
                log(msg, telegram_bot, telegram_chat_id)
                last_news_guard_msg = msg

                if trade_state.active:
                    emergency_close_on_news(client, symbol, trade_state,
                                            telegram_bot, telegram_chat_id)

                news_guard_was_active = True
                continue   # ← NOW VALID: inside while loop

            # Guard still ACTIVE
            elif now_active and news_guard_was_active:
                news_guard_was_active = True
                continue   # ← valid

            # Guard just became INACTIVE
            elif not now_active and news_guard_was_active:
                msg = "NEWS GUARD -> Cleared"
                log(msg, telegram_bot, telegram_chat_id)
                last_news_guard_msg = None
                news_guard_was_active = False
                # no continue → proceed to signal check

            # Guard never active
            else:
                news_guard_was_active = False
                
            if prevent_same_bar and getattr(trade_state, 'entry_close_time', None) == close_time:
                last_processed_time = close_time
                time.sleep(1)
                continue
            
            if last_exit_candle_time == close_time:
                log("Trade exited this candle. Skipping new entry until next bar.", telegram_bot, telegram_chat_id)
                last_processed_time = close_time
                _safe_sleep(1)
                continue

            if require_no_pos and has_active_position(client, symbol):
                last_processed_time = close_time
                time.sleep(1)
                continue

            if use_volume_filter and vol_sma15 is None:
                last_processed_time = close_time
                time.sleep(1)
                continue

            # === SIGNAL DETECTION ===
            buy_signal = (rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and (not use_volume_filter or curr_vol > vol_sma15))

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close -> {side_text}. Preparing entry.", telegram_bot, telegram_chat_id)
                pending_entry = True
                entry_price = close_price
                entry_price_f = float(entry_price)
                
                # === SLIPPAGE GUARD (PREVENT BAD ENTRY) ===
                MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")  # 0.2% max slippage
                try:
                    mark_data = client.public_request("/fapi/v1/premiumIndex", {"symbol": symbol})
                    mark_price = Decimal(str(mark_data["markPrice"]))
                    slippage_pct = abs(mark_price - entry_price) / entry_price
                    if slippage_pct > MAX_ENTRY_SLIPPAGE_PCT:
                        log(f"ENTRY SKIPPED: Slippage {float(slippage_pct*100):.3f}% > {float(MAX_ENTRY_SLIPPAGE_PCT*100):.1f}%", telegram_bot, telegram_chat_id)
                        pending_entry = False
                        continue
                except Exception as e:
                    log(f"Slippage check failed: {e}. Proceeding with market order.", telegram_bot, telegram_chat_id)

                # === CALCULATE RISK & LEVELS ===
                if buy_signal:
                    sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price + (tp_mult * R)
                    trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R)
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP
                    trail_rounding = ROUND_DOWN
                else:
                    sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price - (tp_mult * R)
                    trail_activation_price_dec = entry_price - (TRAIL_TRIGGER_MULT * R)
                    sl_rounding = ROUND_UP
                    tp_rounding = ROUND_DOWN
                    trail_rounding = ROUND_UP

                if R <= Decimal('0'):
                    log("Invalid R (R <= 0). Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue

                # === DRAWDOWN-SCALED RISK (SOFT THROTTLE) ===  ← INDENTED CORRECTLY
                bal = fetch_balance(client)
                drawdown = max(Decimal('0'), (daily_start_equity - bal) / daily_start_equity)
                dynamic_risk_pct = BASE_RISK_PCT * (Decimal('1') - drawdown / MAX_DRAWDOWN_PCT)
                dynamic_risk_pct = max(dynamic_risk_pct, MIN_RISK_PCT)

                risk_amount = bal * dynamic_risk_pct
                qty = risk_amount / R
                qty_api = quantize_qty(qty, step_size)

                log(f"Risk: DD={float(drawdown*100):.2f}% -> {float(dynamic_risk_pct*100):.3f}% | Qty={float(qty_api):.3f}", telegram_bot, telegram_chat_id)

                # === PRICE LEVELS ===
                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, ROUND_DOWN if buy_signal else ROUND_UP)

                # === PLACE MARKET ORDER ===
                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={entry_price_f}", telegram_bot, telegram_chat_id)
                try:
                    order_res = client.send_signed_request("POST", "/fapi/v1/order", {
                        "symbol": symbol,
                        "side": side_text,
                        "type": "MARKET",
                        "quantity": str(qty_api)
                    })
                    log(f"Market order placed: {order_res}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Failed to place market order: {e}", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue

                # === WAIT FOR FILL ===
                start_time = time.time()
                actual_qty = None
                while not STOP_REQUESTED and not os.path.exists("stop.txt"):
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break

                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        try:
                            client.send_signed_request("DELETE", "/fapi/v1/order", {"symbol": symbol, "orderId": order_res.get("orderId")})
                        except Exception as e:
                            log(f"Failed to cancel timed-out order: {e}", telegram_bot, telegram_chat_id)
                        log("Order fill timed out. Cancelling and skipping.", telegram_bot, telegram_chat_id)
                        pending_entry = False
                        break
                    time.sleep(0.5)

                if actual_qty is None:
                    pending_entry = False
                    continue

                # === GET ACTUAL FILL PRICE ===
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)
                actual_fill_price = Decimal(str(actual_fill_price_f))

                # === RECALCULATE LEVELS USING ACTUAL FILL ===
                if buy_signal:
                    sl_price_dec = actual_fill_price * (Decimal("1") - SL_PCT)
                    R = actual_fill_price * SL_PCT
                    tp_price_dec = actual_fill_price + (tp_mult * R)
                    trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R)
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP
                    trail_rounding = ROUND_DOWN
                else:
                    sl_price_dec = actual_fill_price * (Decimal("1") + SL_PCT)
                    R = actual_fill_price * SL_PCT
                    tp_price_dec = actual_fill_price - (tp_mult * R)
                    trail_activation_price_dec = actual_fill_price - (TRAIL_TRIGGER_MULT * R)
                    sl_rounding = ROUND_UP
                    tp_rounding = ROUND_DOWN
                    trail_rounding = ROUND_UP

                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, ROUND_DOWN if buy_signal else ROUND_UP)

                # === TRAILING BUFFER CHECK ===
                try:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    current_price = Decimal(str(ticker.get("price")))
                except Exception as e:
                    log(f"Failed to fetch current price: {e}", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue

                price_buffer = actual_fill_price * TRAIL_PRICE_BUFFER
                if buy_signal and trail_activation_price_dec_quant <= current_price + price_buffer:
                    log("Trailing activation too close to current price. Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
                elif not buy_signal and trail_activation_price_dec_quant >= current_price - price_buffer:
                    log("Trailing activation too close to current price. Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue

                # === ACTIVATE TRADE ===
                trade_state.active = True
                trade_state.entry_price = actual_fill_price_f
                trade_state.risk = float(R)
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                trade_state.initial_sl = sl_price_f
                trade_state.sl = sl_price_f
                trade_state.tp = tp_price_f
                trade_state.trail_activated = False
                trade_state.trail_activation_price = float(trail_activation_price_dec_quant)
                trade_state.highest_price = None
                trade_state.lowest_price = None
                trade_state.current_trail_stop = None

                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f}, "
                    f"sl={sl_price_f}, tp={tp_price_f}, trail_activation={float(trail_activation_price_dec_quant)}",
                    telegram_bot, telegram_chat_id)

                trade_details = {
                    'symbol': symbol,
                    'side': trade_state.side,
                    'entry': trade_state.entry_price,
                    'sl': trade_state.sl,
                    'tp': trade_state.tp,
                    'trail_activation': trade_state.trail_activation_price,
                    'qty': trade_state.qty
                }
                send_trade_telegram(trade_details, telegram_bot, telegram_chat_id)
                place_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)

                # === INCREMENT TRADE COUNTER & UPDATE DATE ===
                trades_today += 1
                last_trade_date = current_date
                pending_entry = False

                # === MONITOR TRADE ===
                monitor_trade(
                    client, symbol, trade_state, tick_size,
                    telegram_bot, telegram_chat_id,
                    close_time  # ← ADDED CORRECTLY
                )

            else:
                if not (trade_state.active or pending_entry):
                    log("No trade signal on candle close.", telegram_bot, telegram_chat_id)

            # === UPDATE LAST PROCESSED TIME ===
            last_processed_time = close_time
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            log(f"Waiting for candle close in {sleep_seconds:.2f}s ...", telegram_bot, telegram_chat_id)
            _safe_sleep(sleep_seconds)

        except Exception as e:
            log(f"Loop error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

    log("Trading loop exited.", telegram_bot, telegram_chat_id)

def interval_ms(interval):
    interval = interval.strip().lower()
    if interval.endswith("m"):
        try:
            minutes = int(interval[:-1])
            if minutes <= 0:
                raise ValueError
            return minutes * 60 * 1000
        except:
            raise ValueError(f"Invalid minutes in timeframe: {interval}")
    elif interval.endswith("h"):
        try:
            hours = int(interval[:-1])
            if hours <= 0:
                raise ValueError
            return hours * 60 * 60 * 1000
        except:
            raise ValueError(f"Invalid hours in timeframe: {interval}")
    else:
        raise ValueError(f"Unsupported timeframe: {interval}. Use e.g., 5m, 45m, 1h")

def _safe_sleep(total_seconds):
    remaining = float(total_seconds)
    while remaining > 0:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        time.sleep(min(1, remaining))
        remaining -= 1

def closes_and_volumes_from_klines(klines):
    closes = [float(k[4]) for k in klines]
    volumes = [float(k[5]) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [float(k[1]) for k in klines]
    return closes, volumes, close_times, opens

def run_scheduler(bot, chat_id):
    global daily_start_equity, account_size
    last_month = None
    def check_monthly_report():
        nonlocal last_month
        current_date = datetime.now(timezone.utc)
        if current_date.day == 1 and (last_month is None or current_date.month != last_month):
            send_monthly_report(bot, chat_id)
            last_month = current_date.month

    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot, chat_id))
    schedule.every().day.at("00:00").do(check_monthly_report)

    global daily_start_equity, account_size
    while True:
        # RESET @ 00:00 UTC
        now_utc = datetime.now(timezone.utc)
        if now_utc.hour == 0 and now_utc.minute < 5:
            try:
                current_balance = fetch_balance(client)
                account_size = current_balance
                daily_start_equity = current_balance
                log(f"DAILY RESET @ 00:00 UTC | New start equity: {float(daily_start_equity):.2f} USD", bot, chat_id)
                telegram_post(bot, chat_id, f"DAILY RESET\nEquity: ${float(daily_start_equity):.2f}")
            except Exception as e:
                log(f"Daily reset failed: {e}", bot, chat_id)
            time.sleep(300)
            continue
        schedule.run_pending()
        time.sleep(60)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Binance Trailing, 30m Optimized, SOLUSDT)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", required=True, help="Telegram Bot Token")
    parser.add_argument("--chat-id", required=True, help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol (default: SOLUSDT)")
    parser.add_argument("--timeframe", default="30m", help="Timeframe (default: 30m)")
    parser.add_argument("--max-trades", type=int, default=3, help="Max trades per day (default: 3)")
    parser.add_argument("--risk-pct", type=float, default=0.5, help="Risk percentage per trade (default: 0.5%)")
    parser.add_argument("--max-loss-pct", type=float, default=5.0, help="Max daily loss percentage (default: 5%)")
    parser.add_argument("--tp-mult", type=float, default=3.5, help="Take-profit multiplier (default: 3.5)")
    parser.add_argument("--no-trailing", dest='use_trailing', action='store_false', help="Disable trailing stop (default: enabled)")
    parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false', help="Allow entries on same bar (default: prevent same bar)")
    parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false', help="Allow entry even if there's an active position (default: require no pos)")
    parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false', help="Disable max daily loss protection (default: enabled)")
    parser.add_argument("--use-volume-filter", action='store_true', default=False, help="Use volume filter (vol > SMA15)")
    parser.add_argument("--no-volume-filter", action='store_false', dest='use_volume_filter', help="Disable volume filter")
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL for Binance API (advanced)")
    args = parser.parse_args()

    init_pnl_log()
    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    balance = fetch_balance(client)
    account_size = balance
    daily_start_equity = balance
    log(f"Daily drawdown protection ENABLED. Start equity: {float(daily_start_equity):.2f} USD", args.telegram_token, args.chat_id)
    log(f"Fetched balance: {float(balance):.2f} USDT", args.telegram_token, args.chat_id)
    threading.Thread(target=news_heartbeat, daemon=True).start()
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}, risk_pct={args.risk_pct}%, use_volume_filter={args.use_volume_filter}", args.telegram_token, args.chat_id)
    balance = fetch_balance(client)
    log(f"Fetched balance: {float(balance):.2f} USDT", args.telegram_token, args.chat_id)

    atexit.register(_request_stop, symbol=args.symbol, telegram_bot=args.telegram_token, telegram_chat_id=args.chat_id)

    try:
        threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()
        trading_loop(
            client=client,
            symbol=args.symbol,
            timeframe=args.timeframe,
            max_trades_per_day=args.max_trades,
            risk_pct=Decimal(str(args.risk_pct)) / Decimal("100"),
            max_daily_loss_pct=Decimal(str(args.max_loss_pct)),
            tp_mult=Decimal(str(args.tp_mult)),
            use_trailing=args.use_trailing,
            prevent_same_bar=args.prevent_same_bar,
            require_no_pos=args.require_no_pos,
            use_max_loss=args.use_max_loss,
            use_volume_filter=args.use_volume_filter,
            telegram_bot=args.telegram_token,
            telegram_chat_id=args.chat_id
        )
    finally:
        pass
