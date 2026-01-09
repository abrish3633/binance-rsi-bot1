# Binance Futures RSI Bot (Binance-Handled Trailing Stop, 45m Optimized, SOLUSDT)
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
from typing import Optional, Tuple, Dict, Any, List
import atexit
import websocket
import json
import queue
import socket
import platform
import numpy as np

# ------------------- CONFIGURATION -------------------
RISK_PCT = Decimal("0.068") # 6.8% per trade
SL_PCT = Decimal("0.0075") # 0.75%
TP_MULT = Decimal("9")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2") # 2.5R trailing distance
VOL_SMA_PERIOD = 16
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 1
INTERVAL_DEFAULT = "45m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = Decimal("55")
BUY_RSI_MAX = Decimal("65")
SELL_RSI_MIN = Decimal("35")
SELL_RSI_MAX = Decimal("45")
POSITION_CHECK_INTERVAL = 60
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = Decimal("5.0")
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RATE_LIMIT_CHECK_INTERVAL = 60
RATE_LIMIT_THRESHOLD = 80
RECOVERY_CHECK_INTERVAL = 10 # Seconds between recovery checks
TRAIL_UPDATE_THROTTLE = Decimal("10.0") # Alert trailing updates every 10 seconds max
POLLING_INTERVAL = 3 # ENHANCED: Polling interval after WS failure

# ---------------------------------------------------------------------------------------
# === CONFIG: BLACKOUT WINDOWS (UTC) ===
# (weekday: 0=Mon..6=Sun, None=every day), (start_h, m), (end_h, m)
NEWS_BLACKOUT_WINDOWS = [
    (4, (12, 25), (13, 5)), # Friday 12:30–13:00 UTC (NFP)
    (2, (18, 55), (19, 35)), # Wednesday 19:00–19:30 UTC (FOMC)
]

# === CONFIG: LIVE API ===
LIVE_APIS = [
    "https://nfs.faireconomy.media/ff_calendar_thisweek.json",
    "https://ec.forexprostools.com/?columns=exc_currency,exc_type&timezone=utc"
]
LOCAL_CALENDAR = "high_impact_calendar.json" # you update weekly
LOCAL_OVERRIDE = "news_calendar_override.json" # one-off manual block
CACHE_DURATION = 300 # 5 min
HIGH_IMPACT_KEYWORDS = {
    "NFP", "NONFARM", "CPI", "FOMC", "GDP", "UNEMPLOYMENT", "RATE DECISION",
    "PCE", "CORE", "ISM", "JOLTS", "OPEC", "SNB", "BOJ", "GEOPOLITICAL",
    "RETAIL SALES", "ADP", "FLASH", "PRELIMINARY"
}
BUFFER_MINUTES = 5

# === CONFIG: NEWS GUARD ===
NEWS_GUARD_ENABLED = True # ← Will be overridden by --no-news-guard

# if not NEWS_GUARD_ENABLED:
    # logging.getLogger().setLevel(logging.WARNING) # Optional: reduce noise

# CONFIG SLIPAGE
MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")
LOCK_FILE = os.path.join(os.getenv('TEMP', '/tmp'), 'sol_rsi_bot.lock')
BASE_RISK_PCT = Decimal("0.068") # 2.25% when drawdown = 0%
MAX_LEVERAGE = Decimal("9")

# === WEEKLY SCALING QUICK TOGGLE ===
ENABLE_WEEKLY_SCALING = True # ← Set to False to disable scaling completely

# ------------------- BOT STATE CLASS (BUNDLED GLOBALS) -------------------
class BotState:
    """Bundle all global state variables into a single class for better organization."""
    def __init__(self):
        # Core bot state
        self.STOP_REQUESTED = False
        self.client = None
        self.symbol_filters_cache: Dict[str, Dict[str, Decimal]] = {}  # FIXED: Changed from None to dict for symbol-specific caching
        self.klines_cache: Dict[str, Any] = {}
        self.klines_cache_time = Decimal("0")
        self.last_rate_limit_check = Decimal("0")
        self._position_closure_in_progress = False
    
        
        # PNL logging
        self.PNL_LOG_FILE = 'pnl_log.csv'
        self.pnl_data: List[Dict[str, Any]] = []
        self.last_trade_date: Optional[datetime] = None
        self.last_exit_candle_time: Optional[int] = None
        
        # Thread-safe state
        self._stop_lock = threading.Lock()
        self._orders_cancelled = False
        
        # WebSocket → Polling fallback state
        self._ws_failed = False
        self._polling_active = False
        self._price_queue = queue.Queue()  # Shared price source (WS or polling)
        
        # News guard state
        self._news_lock = threading.Lock()
        self._news_cache: List[Dict[str, Any]] = []
        self._cache_ts = Decimal("0.0")
        self.NEWS_LOCK = False  # <--- blocks entry + forces emergency close
        self.VOLATILITY_ABORT = False  # set by ATR spike check (see trading loop)
        self.last_news_guard_msg: Optional[str] = None
        self.news_guard_was_active: bool = False
        self._last_news_block_reason: Optional[str] = None
        
        # Risk management state
        self.weekly_peak_equity: Optional[Decimal] = None
        self.weekly_start_time: Optional[datetime] = None
        self.CONSEC_LOSSES = 0
        self.USE_CONSEC_LOSS_GUARD = True
        self.MAX_CONSEC_LOSSES = 3
        self.weekly_dd_alert_triggered = False
        
        # Trading state
        self.is_testnet = True
        self.consec_loss_guard_alert_sent = False
        self.last_processed_close_ms: Optional[int] = None
        self.last_candle_state: Optional[str] = None
        
        # Performance tracking
        self.max_trades_alert_sent = False
        self.daily_start_equity: Optional[Decimal] = None
        self.account_size: Optional[Decimal] = None

# Initialize global bot state
bot_state = BotState()

# ------------------- SINGLE INSTANCE LOCK WITH PID CHECK -------------------
def acquire_lock():
    """Acquire single instance lock with PID check to prevent stale locks."""
    try:
        # Check if lock file exists and contains a valid PID
        if os.path.exists(LOCK_FILE):
            try:
                with open(LOCK_FILE, 'r') as f:
                    pid_str = f.read().strip()
                    if pid_str and pid_str.isdigit():
                        pid = int(pid_str)
                        # Check if process is still running
                        if platform.system() == "Windows":
                            import psutil
                            try:
                                psutil.Process(pid)
                                # Process exists, another instance is running
                                print("Another instance is already running! Exiting.")
                                sys.exit(1)
                            except (psutil.NoSuchProcess, psutil.AccessDenied):
                                # Process doesn't exist, stale lock file
                                os.unlink(LOCK_FILE)
                        else:
                            # Unix: try sending signal 0 to check if process exists
                            try:
                                os.kill(pid, 0)
                                # Process exists, another instance is running
                                print("Another instance is already running! Exiting.")
                                sys.exit(1)
                            except OSError:
                                # Process doesn't exist, stale lock file
                                os.unlink(LOCK_FILE)
            except Exception as e:
                # If we can't read/parse the lock file, remove it and continue
                try:
                    os.unlink(LOCK_FILE)
                except:
                    pass
        
        # Create new lock file with current PID
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
        
        # On Unix systems, add file locking
        if platform.system() != "Windows":
            try:
                import fcntl
                lock_handle = open(LOCK_FILE, 'r+')
                fcntl.lockf(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                # Keep lock file open while bot runs
                return lock_handle
            except Exception as e:
                print(f"Failed to acquire file lock: {e}")
                sys.exit(1)
        
        return None
        
    except FileExistsError:
        print("Another instance is already running! Exiting.")
        sys.exit(1)
    except FileNotFoundError:
        # Windows TEMP may not exist
        os.makedirs(os.path.dirname(LOCK_FILE), exist_ok=True)
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
        return None

# Acquire lock at startup
LOCK_HANDLE = acquire_lock()

# ------------------- MEMORY LIMIT (Linux / OCI only) -------------------
if platform.system() != "Windows":
    try:
        import resource
        SOFT = HARD = 680 * 1024 * 1024 # ~680 MB
        resource.setrlimit(resource.RLIMIT_AS, (SOFT, HARD))
        print(f"[Startup] Memory limit set to ~680 MB")
    except Exception as e:
        print(f"[Startup] Could not set memory limit: {e}")
else:
    print("[Startup] Windows detected – skipping Unix-only features (normal for local testing)")

# ---------------------------------------------------------------------------------------
# 4. FETCHERS
# ----------------------------------------------------------------------
def get_server_time(client):
    try:
        resp = client.public_request("/fapi/v1/time")
        return int(resp['serverTime'])
    except Exception as e:
        log(f"Server time fetch failed: {e}")
        return int(time.time() * 1000) # Fallback to local
  
def _fetch_json(url: str) -> List[Any] | None:
    try:
        r = requests.get(url, timeout=8)
        if r.status_code == 200:
            return r.json()
    except Exception:
        return None
    return None

def _load_local_calendar() -> List[Any]:
    if os.path.exists(LOCAL_CALENDAR):
        try:
            with open(LOCAL_CALENDAR) as f:
                return json.load(f)
        except Exception:
            pass
    return []

def _load_override() -> List[Any]:
    if os.path.exists(LOCAL_OVERRIDE):
        try:
            with open(LOCAL_OVERRIDE) as f:
                return json.load(f)
        except Exception:
            pass
    return []

def _parse_event(event: Dict[str, Any]) -> Optional[datetime]:
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
def _time_in_window(now_utc: datetime, start_hm: Tuple[int, int], end_hm: Tuple[int, int]) -> bool:
    start = datetime(now_utc.year, now_utc.month, now_utc.day, *start_hm, tzinfo=timezone.utc)
    end = datetime(now_utc.year, now_utc.month, now_utc.day, *end_hm, tzinfo=timezone.utc)
    if end <= start:
        end += timedelta(days=1)
    return start <= now_utc <= end

def _in_blackout_window(now_utc: Optional[datetime] = None) -> Tuple[bool, Optional[str]]:
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
    global bot_state
    now = datetime.now(timezone.utc)
    events: List[Dict[str, Any]] = []
    # === 1. Existing economic calendars ===
    for api in LIVE_APIS:
        data = _fetch_json(api)
        if data:
            events.extend(data)
            break
    events.extend(_load_local_calendar())
    events.extend(_load_override())
    high: List[Dict[str, Any]] = []
    for e in events:
        title = (e.get("title") or e.get("event") or "").upper()
        impact = (e.get("impact") or "").lower()
        if impact != "high" and not any(k in title for k in HIGH_IMPACT_KEYWORDS):
            continue
        dt = _parse_event(e)
        if dt:
            high.append({"dt": dt, "title": title})
        # ←←← THIS LINE WAS MISSING ←←←
    bot_state._news_cache = high
    bot_state._cache_ts = Decimal(str(time.time()))

def news_heartbeat():
    global bot_state
    while not bot_state.STOP_REQUESTED:
        _refresh_news()
        now = datetime.now(timezone.utc)
        news_lock = False
        # Economic events
        for ev in bot_state._news_cache:
            if (ev["dt"] - timedelta(minutes=BUFFER_MINUTES) <= now <=
                ev["dt"] + timedelta(minutes=BUFFER_MINUTES)):
                news_lock = True
                break
        static_block, _ = _in_blackout_window(now)
        bot_state.NEWS_LOCK = news_lock or static_block
        time.sleep(60)

# ----------------------------------------------------------------------
# 6. PUBLIC GUARD (called from trading loop)
# ----------------------------------------------------------------------
def is_news_blocked(now_utc: Optional[datetime] = None) -> Tuple[bool, Optional[str]]:
    global bot_state
    now = now_utc or datetime.now(timezone.utc)
    with bot_state._news_lock:
        for ev in bot_state._news_cache:
            if (ev["dt"] - timedelta(minutes=BUFFER_MINUTES) <= now <=
                ev["dt"] + timedelta(minutes=BUFFER_MINUTES)):
                reason = f"Live: {ev['title']} @ {ev['dt'].strftime('%H:%M')} UTC"
                if reason != bot_state._last_news_block_reason:
                    bot_state._last_news_block_reason = reason
                return True, reason
    blocked, reason = _in_blackout_window(now)
    if blocked:
        if reason != bot_state._last_news_block_reason:
            bot_state._last_news_block_reason = reason
        return True, reason
    if os.path.exists("FORCE_NO_TRADE_TODAY.txt"):
        reason = "Manual override"
        if reason != bot_state._last_news_block_reason:
            bot_state._last_news_block_reason = reason
        return True, reason
    # ←←←←← DELETE OR COMMENT OUT THIS LINE ←←←←←
    # log("NEWS GUARD -> All clear. Trading resumed.", telegram_bot, telegram_chat_id)
    if bot_state._last_news_block_reason is not None:
        bot_state._last_news_block_reason = None
        # Optional: you can keep a console log, it goes to bot.log anyway
        logger.info("NEWS GUARD -> All clear. Trading resumed.")
    return False, None

# ----------------------------------------------------------------------
# 7. EMERGENCY CLOSE (call from monitor_trade_mt5 when NEWS_LOCK flips)
# ----------------------------------------------------------------------
def emergency_close_on_news(client: Any, symbol: str, trade_state: Any, bot: Optional[str], chat_id: Optional[str]):
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
def check_volatility_abort(klines: List[List[Any]], period: int = 14) -> bool:
    """Return True if ATR > 3× 20-period mean."""
    if len(klines) < period + 1:
        return False
    import numpy as np
    highs = np.array([float(k[2]) for k in klines[-period-20:]])
    lows = np.array([float(k[3]) for k in klines[-period-20:]])
    closes = np.array([float(k[4]) for k in klines[-period-20:]])
    tr = np.maximum(highs[1:] - lows[1:], np.abs(highs[1:] - closes[:-1]),
                    np.abs(lows[1:] - closes[:-1]))
    atr = np.mean(tr[-period:])
    mean20 = np.mean(tr[-20:])
    return atr > mean20 * 3.0

# ------------------- RISK MANAGEMENT FUNCTIONS (SPLIT) -------------------
def check_weekly_drawdown_stop(current_equity: Decimal, symbol: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> bool:
    """
    Check if weekly 20% drawdown stop is triggered.
    Returns True if trading should be blocked due to weekly DD >= 20%.
    """
    global bot_state
    
    now = datetime.now(timezone.utc)
    current_monday = now - timedelta(days=now.weekday())
    current_monday = current_monday.replace(hour=0, minute=0, second=0, microsecond=0)
    log(f"DEBUG: Today={now.date()} Weekday={now.weekday()} WeeklyStart={bot_state.weekly_start_time} ConsecLosses={bot_state.CONSEC_LOSSES}", telegram_bot, telegram_chat_id)
    
    current_week_monday = now - timedelta(days=now.weekday())
    current_week_monday = current_week_monday.replace(hour=0, minute=0, second=0, microsecond=0)
    
    # === NEW WEEK DETECTED → RESET ===
    if (bot_state.weekly_start_time is None or 
        current_week_monday != bot_state.weekly_start_time):
        bot_state.weekly_start_time = current_monday
        bot_state.weekly_peak_equity = current_equity
        bot_state.weekly_dd_alert_triggered = False
        bot_state.consec_loss_guard_alert_sent = False
        if telegram_bot and telegram_chat_id:
            log(f"NEW WEEK -> Weekly peak reset to ${current_equity:,.2f}", telegram_bot, telegram_chat_id)
    
    # === UPDATE PEAK IF HIGHER ===
    if bot_state.weekly_peak_equity is None or current_equity > bot_state.weekly_peak_equity:
        bot_state.weekly_peak_equity = current_equity
    
    # === CHECK 20% DD LIMIT ===
    if bot_state.weekly_peak_equity <= Decimal("0"):
        return True  # Block trading
    
    weekly_dd = (bot_state.weekly_peak_equity - current_equity) / bot_state.weekly_peak_equity
    if weekly_dd >= Decimal("0.20"):
        # One-time alert
        if not bot_state.weekly_dd_alert_triggered:
            msg = f"🚨 WEEKLY 20% DD REACHED! Closing ALL positions (DD: {weekly_dd:.2%})"
            log(msg, telegram_bot, telegram_chat_id)
            bot_state.weekly_dd_alert_triggered = True
        return True  # Block trading
    
    # Reset alert when recovered
    if bot_state.weekly_dd_alert_triggered:
        bot_state.weekly_dd_alert_triggered = False
        log("Weekly DD recovered – trading resumed.", telegram_bot, telegram_chat_id)
    
    return False  # Trading allowed

def execute_emergency_close_on_weekly_dd(client: Any, symbol: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    """
    Execute emergency close of positions when weekly DD >= 20%.
    This is separated from the check function for single responsibility.
    """
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        
        # Normalize response to list of dicts
        if isinstance(pos_resp, dict) and 'data' in pos_resp:
            positions = pos_resp['data']
        elif isinstance(pos_resp, list):
            positions = pos_resp
        else:
            log(f"Unexpected positionRisk response type: {type(pos_resp)}. Skipping close.", telegram_bot, telegram_chat_id)
            positions = []
        
        # Defensive: Find matching symbol only if item is dict
        pos_item = None
        for item in positions:
            if isinstance(item, dict) and item.get("symbol") == symbol:
                pos_item = item
                break
        
        if pos_item is None:
            # No position found for symbol
            return
        
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0")))
        
        if pos_amt != Decimal("0"):
            side = "SELL" if pos_amt > Decimal("0") else "BUY"
            qty = abs(pos_amt)
            client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": str(qty)
            })
            log(f"EMERGENCY CLOSE: Position closed (qty={qty} {side}) due to weekly DD", telegram_bot, telegram_chat_id)
            
    except Exception as e:
        log(f"Emergency close failed: {str(e)}", telegram_bot, telegram_chat_id)

def get_current_risk_pct(
    current_equity: Decimal,
    client: Any, # BinanceClient instance
    symbol: str = "SOLUSDT", # Made parameter with default for flexibility
    telegram_bot: Optional[str] = None,
    telegram_chat_id: Optional[str] = None
) -> Decimal:
    """
    SIMPLE FIXED 20% WEEKLY DD STOP (Pine Script style)
    - Blocks new trades if weekly DD >= 20%
    - Emergency closes open positions if DD >= 20%
    - Resets consecutive loss streak and alert flag on new week
    """
    # Check if weekly DD stop is triggered
    dd_stop_triggered = check_weekly_drawdown_stop(current_equity, symbol, telegram_bot, telegram_chat_id)
    
    if dd_stop_triggered:
        # Execute emergency close if needed
        execute_emergency_close_on_weekly_dd(client, symbol, telegram_bot, telegram_chat_id)
        return Decimal("0")  # No risk allowed
    
    return Decimal("1")  # Full risk allowed

# ------------------- PNL LOGGING WITH DECIMAL FIELDS -------------------
PNL_FIELDS = ['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r', 'loss_streak']

def init_pnl_log():
    if not os.path.exists(bot_state.PNL_LOG_FILE):
        with open(bot_state.PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
            writer.writeheader()

def log_pnl(trade_id: int, side: str, entry: Decimal, exit_price: Decimal, qty: Decimal, R: Decimal) -> Dict[str, Any]:
    global bot_state
    
    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty
    
    # FIXED: Add divide-by-zero guard with Decimal
    total_risk = qty * R
    if total_risk > Decimal("0"):
        pnl_r = pnl_usd / total_risk
    else:
        pnl_r = Decimal("0") if pnl_usd >= Decimal("0") else Decimal("-1")
    
    # === CONSECUTIVE LOSS TRACKING WITH DECIMAL ===
    denominator = entry * qty if entry and qty else Decimal("1")
    loss_pct = abs(pnl_usd) / denominator if pnl_usd < Decimal("0") else Decimal("0")
    is_full_loss = loss_pct >= Decimal("0.0074")  # ~0.75% loss (1R)
    
    if pnl_usd < Decimal("0") and is_full_loss:
        bot_state.CONSEC_LOSSES += 1
    else:
        bot_state.CONSEC_LOSSES = 0  # Any profit or partial loss resets streak
    
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': float(entry),          # Convert to float for CSV storage
        'exit': float(exit_price),      # Convert to float for CSV storage
        'pnl_usd': float(pnl_usd),      # Convert to float for CSV storage
        'pnl_r': float(pnl_r),          # Convert to float for CSV storage
        'loss_streak': bot_state.CONSEC_LOSSES
    }
    
    bot_state.pnl_data.append(row)
    
    # FIXED: Use consistent PNL_FIELDS for CSV writing
    with open(bot_state.PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
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

def log(message: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    """
    Safe logging - logs to console/file, tries Telegram but won't crash.
    """
    # 1. ALWAYS log to console/file
    try:
        logger.info(message)
    except:
        print(f"[LOG-FAIL] {message[:200]}")  # Truncate if crazy long
    
    # 2. Try Telegram if credentials exist
    if telegram_bot and telegram_chat_id:
        telegram_post(telegram_bot, telegram_chat_id, message)

# ------------------- TELEGRAM (BULLETPROOF - NEVER CRASHES) -------------------
def telegram_post(token: Optional[str], chat_id: Optional[str], text: str, parse_mode: Optional[str] = None):
    """
    Send Telegram message. If ANYTHING goes wrong, just return silently.
    Bot continues trading regardless of Telegram status.
    """
    # QUICK CHECKS
    if not token or not chat_id:
        return
    
    # Don't even try if token looks obviously wrong
    if ':' not in token:
        return
    
    try:
        # Truncate if crazy long (Telegram limit: 4096 chars)
        if len(text) > 4000:
            text = text[:3900] + "\n...[truncated]"
        
        # One simple attempt with timeout
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        requests.post(
            url, 
            json={"chat_id": chat_id, "text": text}, 
            timeout=(3, 5)  # 3s connect, 5s read timeout
        )
    except:
        # IGNORE EVERYTHING - bot must not crash!
        pass

# ------------------- TELEGRAM MESSAGES WITH DECIMAL -------------------
def send_trade_telegram(trade_details: Dict[str, Any], bot: Optional[str], chat_id: Optional[str]):
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

def send_closure_telegram(symbol: str, side: str, entry_price: Decimal, exit_price: Decimal, qty: Decimal, pnl_usd: Decimal, pnl_r: Decimal, reason: str, bot: Optional[str], chat_id: Optional[str]):
    global bot_state
    
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry Price: {entry_price:.4f}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Reason: {reason}\n"
        f"- Qty: {qty:.5f}\n"
        f"- PNL: {pnl_usd:.2f} USDT ({pnl_r:.2f}R)\n"
        f"- Loss Streak: {bot_state.CONSEC_LOSSES}"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_activation_telegram(symbol: str, side: str, activation_price: Decimal, initial_stop_price: Decimal, bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"Trailing Stop Activated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Activation Price: {activation_price:.4f}\n"
        f"- Initial Stop Price: {initial_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_update_telegram(symbol: str, side: str, new_stop_price: Decimal, bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {new_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

# ------------------- PNL REPORTS WITH DECIMAL -------------------
def calculate_pnl_report(period: str) -> str:
    global bot_state
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
        trade for trade in bot_state.pnl_data
        if datetime.fromisoformat(trade['date']) >= start_time
    ]
    
    if not filtered_trades:
        return f"No trades recorded for the {period} period."
    
    total_pnl_usd = Decimal(str(sum(trade['pnl_usd'] for trade in filtered_trades)))
    total_pnl_r = Decimal(str(sum(trade['pnl_r'] for trade in filtered_trades)))
    num_trades = len(filtered_trades)
    avg_pnl_usd = total_pnl_usd / Decimal(str(num_trades)) if num_trades > 0 else Decimal("0")
    wins = sum(1 for trade in filtered_trades if trade['pnl_usd'] > 0)
    losses = num_trades - wins
    win_rate = (Decimal(str(wins)) / Decimal(str(num_trades)) * Decimal("100")) if num_trades > 0 else Decimal("0")
    
    return (
        f"{period.capitalize()} PNL Report:\n"
        f"- Total Trades: {num_trades}\n"
        f"- Total PNL: {total_pnl_usd:.2f} USDT\n"
        f"- Average PNL per Trade: {avg_pnl_usd:.2f} USDT\n"
        f"- Total PNL (R): {total_pnl_r:.2f}R\n"
        f"- Win Rate: {win_rate:.2f}% ({wins} wins, {losses} losses)\n"
    )

def send_daily_report(bot: Optional[str], chat_id: Optional[str]):
    report = calculate_pnl_report('daily')
    subject = f"Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def send_weekly_report(bot: Optional[str], chat_id: Optional[str]):
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

def send_monthly_report(bot: Optional[str], chat_id: Optional[str]):
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    telegram_post(bot, chat_id, f"{subject}\n{report}")

# ------------------- STOP HANDLER (IDEMPOTENT) WITH DECIMAL -------------------
def _request_stop(signum: Optional[int] = None, frame: Any = None, symbol: Optional[str] = None, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    global bot_state
    with bot_state._stop_lock:
        if bot_state.STOP_REQUESTED:
            logger.info("Stop already requested; skipping duplicate cleanup.")
            return
        bot_state.STOP_REQUESTED = True
    
    # ADD THIS: Set flag to prevent monitor_trade from also processing closure
    bot_state._position_closure_in_progress = True
    
    log("Stop requested. Closing positions and cancelling orders...", telegram_bot, telegram_chat_id)
    
    if not bot_state.client or not symbol:
        log("Client or symbol not defined; skipping position closure and order cancellation.", telegram_bot, telegram_chat_id)
        bot_state._position_closure_in_progress = False  # CLEAR FLAG
        return
    
    try:
        pos_resp = bot_state.client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
        
        if pos_amt != Decimal('0'):
            side = "SELL" if pos_amt > Decimal('0') else "BUY"
            qty = abs(pos_amt)
            entry_price_dec = Decimal(str(pos_item.get("entryPrice", "0"))) if pos_item else Decimal('0')
            entry_price_f = float(entry_price_dec)
            
            # Place market close
            response = bot_state.client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": str(qty)
            })
            market_order_id = response.get("orderId")
            log(f"Closed position: qty={qty} {side} (orderId: {market_order_id})", telegram_bot, telegram_chat_id)
            
            # === Get EXACT fill price from userTrades (not ticker fallback) ===
            exit_price_dec: Optional[Decimal] = None
            if market_order_id:
                time.sleep(0.8) # Allow fill propagation
                try:
                    trades = bot_state.client.send_signed_request("GET", "/fapi/v1/userTrades", {
                        "symbol": symbol,
                        "orderId": market_order_id,
                        "limit": 10
                    })
                    filled_trades = [t for t in trades if Decimal(str(t.get("qty", "0"))) > Decimal('0')]
                    if filled_trades:
                        # Use last fill (most accurate)
                        exit_price_dec = Decimal(str(filled_trades[-1]["price"]))
                except Exception as e:
                    log(f"Failed to fetch exact fill from userTrades: {e}", telegram_bot, telegram_chat_id)
            
            if exit_price_dec is None:
                log("⚠️ Exact fill price unavailable. Using ticker as last resort.", telegram_bot, telegram_chat_id)
                try:
                    ticker = bot_state.client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price_dec = Decimal(str(ticker.get("price", "0")))
                except Exception as e:
                    log(f"Ticker fallback failed: {e}", telegram_bot, telegram_chat_id)
                    exit_price_dec = Decimal("0")
            
            exit_price_f = float(exit_price_dec)
            R_float = float(entry_price_dec * SL_PCT)
            
            # Log PNL with Decimal values
            pnl_row = log_pnl(
                len(bot_state.pnl_data) + 1,
                "LONG" if pos_amt > Decimal('0') else "SHORT",
                entry_price_dec,
                exit_price_dec,
                qty,
                entry_price_dec * SL_PCT
            )
            
            # Telegram
            if telegram_bot and telegram_chat_id:
                send_closure_telegram(
                    symbol=symbol,
                    side="LONG" if pos_amt > Decimal('0') else "SHORT",
                    entry_price=entry_price_dec,
                    exit_price=exit_price_dec,
                    qty=qty,
                    pnl_usd=Decimal(str(pnl_row['pnl_usd'])),
                    pnl_r=Decimal(str(pnl_row['pnl_r'])),
                    reason="Stop Requested",
                    bot=telegram_bot,
                    chat_id=telegram_chat_id
                )
    
    except Exception as e:
        log(f"Stop handler error while closing position: {str(e)}", telegram_bot, telegram_chat_id)
    
    # Final cleanup
    with bot_state._stop_lock:
        if not bot_state._orders_cancelled:
            try:
                bot_state.client.cancel_all_open_orders(symbol)
                log(f"All open orders cancelled for {symbol}.", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to cancel open orders: {e}", telegram_bot, telegram_chat_id)
            bot_state._orders_cancelled = True
    bot_state._position_closure_in_progress = False
# ------------------- TIME SYNC -------------------
def check_time_offset(base_url: str) -> Optional[float]:
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

# ------------------- BINANCE CLIENT WITH DECIMAL -------------------
class BinanceAPIError(Exception):
    def __init__(self, message: str, status_code: Optional[int] = None, payload: Optional[str] = None):
        super().__init__(message)
        self.status_code = status_code
        self.payload = payload

class BinanceClient:
    def __init__(self, api_key: str, api_secret: str, use_live: bool = False, base_override: Optional[str] = None):
        self.api_key = api_key
        self.api_secret = api_secret
        self.use_live = use_live
        self.base = base_override or ("https://fapi.binance.com" if use_live else "https://testnet.binancefuture.com")
        self.ping_latency = check_time_offset(self.base)
        self.dual_side = self._check_position_mode()
        log(f"Using base URL: {self.base}, Position Mode: {'Hedge' if self.dual_side else 'One-way'}")
      
    def set_leverage(self, symbol: str, leverage: int):
        """Set leverage for a symbol"""
        params = {
            "symbol": symbol,
            "leverage": leverage
        }
        return self.send_signed_request("POST", "/fapi/v1/leverage", params)
  
    def get_algo_fill_details(self, symbol: str, algo_id: int) -> Tuple[Optional[Decimal], Optional[Decimal]]:
        if not algo_id:
            return None, None
      
        params = {"symbol": symbol, "algoId": algo_id}
      
        try:
            order = self.send_signed_request("GET", "/fapi/v1/algoOrder", params)
            if isinstance(order, dict):
                status = order.get("orderStatus")
                if status in ["FILLED", "PARTIALLY_FILLED"]:
                    avg_price_str = order.get("avgPrice", "0")
                    qty_str = order.get("executedQty", "0")
                    return (
                        Decimal(avg_price_str) if avg_price_str != "0" else None,
                        Decimal(qty_str) if qty_str != "0" else None
                    )
        except Exception as e:
            log(f"Error querying algo fill details for algoId {algo_id}: {e}")
      
        return None, None  # ← No historical fallback — rely on closure detection instead
  
    def _check_position_mode(self) -> bool:
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            return response.get('dualSidePosition', False)
        except Exception as e:
            log(f"Position mode check failed: {str(e)}. Assuming one-way mode.")
            return False

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: Optional[Dict[str, Any]] = None) -> Any:
        params = params.copy() if params else {}
        params["timestamp"] = get_server_time(self)  # Use accurate server time
        params["recvWindow"] = 60000  # 60-second window for safety
        
        # Build query string with sorted keys (Binance requirement)
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
                # Any other non-200 error
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

    def public_request(self, path: str, params: Optional[Dict[str, Any]] = None) -> Any:
        url = f"{self.base}{path}"
        try:
            r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                return r.json()
            else:
                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", r.status_code, r.text)
        except Exception as e:
            raise BinanceAPIError(f"Public request failed: {str(e)}", payload=str(e))

    def get_latest_trade_details(self, symbol: str) -> Optional[Dict[str, Any]]:
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

    def get_open_orders(self, symbol: str) -> List[Any]:
        params = {"symbol": symbol}
        response = self.send_signed_request("GET", "/fapi/v1/openOrders", params)
        return response if isinstance(response, list) else []

    def cancel_all_open_orders(self, symbol: str):
        """FINAL ZOMBIE KILLER — 2025 compliant. Smart logs + full annihilation."""
        try:
            # 1. Cancel all regular orders — instant bulk cancel
            self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol, "recvWindow": 60000})
            log(f"[ZOMBIE KILLER] All regular orders nuked for {symbol}")
            
            # 2. Handle algo orders (STOP/TP/TRAILING) — smart detection + accurate logs
            try:
                resp = self.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
                algo_orders = resp if isinstance(resp, list) else []
              
                if not algo_orders:
                    log(f"[ZOMBIE KILLER] No algo orders found — clean")
                    return
                
                log(f"[ZOMBIE KILLER] Found {len(algo_orders)} algo order(s) → TERMINATING")
                for order in algo_orders:
                    algo_id = order.get("algoId")
                    order_type = order.get("orderType", "ALGO")
                    if algo_id:
                        self.send_signed_request("DELETE", "/fapi/v1/algoOrder", {
                            "symbol": symbol,
                            "algoId": str(algo_id)
                        })
                        log(f"[ZOMBIE KILLER] TERMINATED {order_type} algoId={algo_id}")
                        time.sleep(0.1)  # Rate limit safety
            except Exception as e:
                log(f"[ZOMBIE KILLER] Algo cleanup failed: {e}")
        except Exception as e:
            log(f"[ZOMBIE KILLER] Critical failure: {e}")
  
    def cancel_order(self, symbol: str, order_id: int) -> Any:
        params = {"symbol": symbol, "orderId": order_id}
        return self.send_signed_request("DELETE", "/fapi/v1/order", params)

    def get_latest_fill_price(self, symbol: str, order_id: int) -> Optional[Decimal]:
        params = {"symbol": symbol, "orderId": order_id}
        try:
            trades = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            if trades and len(trades) > 0:
                return Decimal(str(trades[-1].get("price", "0")))
            return None
        except Exception as e:
            log(f"Failed to fetch fill price: {str(e)}")
            return None

    def place_algo_order(self, symbol: str, side: str, quantity: Decimal,
                         order_type: str, trigger_price: Optional[Decimal] = None,
                         activation_price: Optional[Decimal] = None, callback_rate: Optional[Decimal] = None,
                         reduce_only: bool = True) -> Any:
        params = {
            "algoType": "CONDITIONAL",
            "symbol": symbol,
            "side": side,
            "type": order_type,  # ← FIXED: lowercase 't' — this was the bug
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false",
            "timeInForce": "GTE_GTC",
            "priceProtect": "true"  # Add this
        }
        
        if trigger_price is not None:
            params["triggerPrice"] = str(trigger_price)  # ← Docs confirm: triggerPrice for SL/TP
            params["workingType"] = "CONTRACT_PRICE"
        if activation_price is not None:
            params["activatePrice"] = str(activation_price)
        if callback_rate is not None:
            params["callbackRate"] = str(callback_rate)
        
        return self.send_signed_request("POST", "/fapi/v1/algoOrder", params)

    def place_stop_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                          reduce_only: bool = True, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "STOP_MARKET", trigger_price=stop_price, reduce_only=reduce_only)

    def place_take_profit_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                                reduce_only: bool = True, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "TAKE_PROFIT_MARKET", trigger_price=stop_price, reduce_only=reduce_only)

    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal,
                                  callback_rate: Decimal, activation_price: Decimal,
                                  reduce_only: bool = True, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "TRAILING_STOP_MARKET",
                                     activation_price=activation_price, callback_rate=callback_rate, reduce_only=reduce_only)

# ------------------- INDICATORS (WILDER RSI) WITH DECIMAL -------------------
def compute_rsi(closes: List[Decimal], period: int = RSI_PERIOD) -> Optional[Decimal]:
    """Compute RSI with Decimal precision."""
    if len(closes) < period + 1:
        return None
    
    # Convert Decimal to float for RSI calculation (standard RSI libraries use floats)
    # But we'll return as Decimal
    closes_float = [float(c) for c in closes]
    deltas = [closes_float[i] - closes_float[i-1] for i in range(1, len(closes_float))]
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
        return Decimal("100.0")
    
    rs = avg_gain / avg_loss
    rsi_value = 100 - 100 / (1 + rs)
    return Decimal(str(round(rsi_value, 2)))

def sma(data: List[Decimal], period: int) -> Optional[Decimal]:
    """Simple Moving Average with Decimal precision."""
    if len(data) < period:
        return None
    # Use Decimal arithmetic
    return sum(data[-period:]) / Decimal(str(period))

def quantize_qty(qty: Decimal, step_size: Decimal) -> Decimal:
    q = (qty // step_size) * step_size
    if q == Decimal("0"):
        q = step_size
    return q.quantize(step_size)

def quantize_price(p: Decimal, tick_size: Decimal, rounding=ROUND_HALF_EVEN) -> Decimal:
    return p.quantize(tick_size, rounding=rounding)

# === 45m AGGREGATION + ALIGNMENT (BEST VERSION) ===
def aggregate_klines_to_45m(klines_15m: List[List[Any]]) -> List[List[Any]]:
    if len(klines_15m) < 3:
        return []
    aggregated: List[List[Any]] = []
    EXPECTED = 45 * 60 * 1000
    TOLERANCE = 5000  # 5-second tolerance (covers any Binance drift)
    
    # Work backwards from the newest candle (guarantees we get the latest complete 45m candle)
    for i in range(len(klines_15m) - 1, 1, -1):
        # Align to every 45-minute boundary from the newest candle
        close_time = int(klines_15m[i][6])
        open_time_expected = close_time - EXPECTED
        
        # Find the oldest candle that matches the expected 45m window
        for j in range(i - 2, -1, -1):
            if abs(int(klines_15m[j][0]) - open_time_expected) <= TOLERANCE:
                # Found a matching group of 3 candles
                chunk = klines_15m[j:j+3]
                if len(chunk) == 3:
                    a, b, c = chunk
                    high = max(float(a[2]), float(b[2]), float(c[2]))
                    low = min(float(a[3]), float(b[3]), float(c[3]))
                    volume = float(a[5]) + float(b[5]) + float(c[5])
                    aggregated.append([
                        int(a[0]),
                        float(a[1]),
                        high,
                        low,
                        float(c[4]),
                        volume,
                        int(c[6])
                    ])
                break
        
        # Stop once we have enough history (we only need ~100 candles)
        if len(aggregated) >= 500:
            break
    
    aggregated.reverse()
    return aggregated

# ------------------- SYMBOL FILTERS WITH PROPER CACHE -------------------
def get_symbol_filters(client: BinanceClient, symbol: str) -> Dict[str, Decimal]:
    global bot_state
    """Get symbol filters with proper symbol-specific caching."""
    
    # FIXED: Check cache for this specific symbol
    if symbol in bot_state.symbol_filters_cache:
        return bot_state.symbol_filters_cache[symbol]
    
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
    
    # FIXED: Cache by symbol
    bot_state.symbol_filters_cache[symbol] = {
        "stepSize": step_size, 
        "minQty": min_qty, 
        "tickSize": tick_size, 
        "minNotional": min_notional
    }
    
    return bot_state.symbol_filters_cache[symbol]

# ------------------- TRADE STATE WITH DECIMAL -------------------
class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price: Optional[Decimal] = None
        self.qty: Optional[Decimal] = None
        self.side: Optional[str] = None
        self.entry_close_time: Optional[int] = None
        self.initial_sl: Optional[Decimal] = None
        self.sl: Optional[Decimal] = None
        self.tp: Optional[Decimal] = None
        self.trail_activation_price: Optional[Decimal] = None
        self.highest_price: Optional[Decimal] = None
        self.lowest_price: Optional[Decimal] = None
        self.current_trail_stop: Optional[Decimal] = None
        self.trail_activated = False
        self.last_trail_alert = Decimal("0.0")
        self.risk: Optional[Decimal] = None
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_order_id = None
        self.sl_algo_id = None
        self.tp_algo_id = None
        self.trail_algo_id = None

# ------------------- HELPER: KLINE DATA EXTRACTION WITH DECIMAL -------------------
def closes_and_volumes_from_klines(klines: List[List[Any]]) -> Tuple[List[Decimal], List[Decimal], List[int], List[Decimal]]:
    # Convert to Decimal for precision
    closes = [Decimal(str(k[4])) for k in klines]
    volumes = [Decimal(str(k[5])) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [Decimal(str(k[1])) for k in klines]
    return closes, volumes, close_times, opens

# ------------------- ORDERS (REUSABLE) WITH DECIMAL -------------------
def place_orders(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    log(f"DEBUG: place_orders received trail_activation_price = {trade_state.trail_activation_price}", telegram_bot, telegram_chat_id)
    """
    Places SL, TP, and Trailing Stop orders.
    Relies on trade_state having:
      - entry_price (actual fill price) as Decimal
      - qty as Decimal
      - side ("LONG" or "SHORT")
      - trail_activation_price (pre-calculated, quantized, buffered, correct direction) as Decimal
      - sl, tp (will be set here) as Decimal
    """
    if not trade_state.active or not trade_state.entry_price or trade_state.trail_activation_price is None:
        log("ERROR: place_orders called with incomplete trade_state (missing entry or trail activation)", telegram_bot, telegram_chat_id)
        return
    
    entry_price = trade_state.entry_price  # Already Decimal
    qty_dec = trade_state.qty  # Already Decimal
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    R = entry_price * SL_PCT
    callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
    
    # === RECALCULATE SL and TP with actual entry ===
    if trade_state.side == "LONG":
        sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
        sl_rounding = ROUND_DOWN
        tp_price_dec = entry_price + (TP_MULT * R)
        tp_rounding = ROUND_UP
    else:  # SHORT
        sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
        sl_rounding = ROUND_UP
        tp_price_dec = entry_price - (TP_MULT * R)
        tp_rounding = ROUND_DOWN
    
    sl_price_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
    tp_price_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
    
    # === USE PRE-CALCULATED TRAIL ACTIVATION ===
    trail_activation_price_quant = trade_state.trail_activation_price  # Already Decimal
    log(f"DEBUG: Sending activation_price to Binance = {trail_activation_price_quant:.4f}", telegram_bot, telegram_chat_id)
    
    # === OPTIONAL: FINAL VALIDATION AGAINST CURRENT MARKET PRICE ===
    try:
        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
        current_price = Decimal(str(ticker["price"]))
      
        if trade_state.side == "LONG" and trail_activation_price_quant <= current_price:
            log(f"WARNING: Trailing activation {trail_activation_price_quant} <= current {current_price} for LONG — may trigger immediately!", telegram_bot, telegram_chat_id)
        elif trade_state.side == "SHORT" and trail_activation_price_quant >= current_price:
            log(f"WARNING: Trailing activation {trail_activation_price_quant} >= current {current_price} for SHORT — may trigger immediately!", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Could not fetch current price for trailing validation: {e}", telegram_bot, telegram_chat_id)
    
    # === PLACE ORDERS ===
    failures = 0
    
    # Stop Loss
    try:
        sl_order = client.place_stop_market(
            symbol, close_side, qty_dec, sl_price_quant,
            reduce_only=True
        )
        trade_state.sl_order_id = sl_order.get("orderId")
        trade_state.sl_algo_id = sl_order.get("algoId")
        trade_state.sl = sl_price_quant  # Store as Decimal
        log(f"Placed STOP_MARKET SL at {sl_price_quant:.4f}: {sl_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)
    
    # Take Profit
    try:
        tp_order = client.place_take_profit_market(
            symbol, close_side, qty_dec, tp_price_quant,
            reduce_only=True
        )
        trade_state.tp_order_id = tp_order.get("orderId")
        trade_state.tp_algo_id = tp_order.get("algoId")
        trade_state.tp = tp_price_quant  # Store as Decimal
        log(f"Placed TAKE_PROFIT_MARKET TP at {tp_price_quant:.4f}: {tp_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)
    
    # Trailing Stop
    try:
        trail_order = client.place_trailing_stop_market(
            symbol, close_side, qty_dec,
            callback_rate=callback_rate,
            activation_price=trail_activation_price_quant,
            reduce_only=True
        )
        trade_state.trail_order_id = trail_order.get("orderId")
        trade_state.trail_algo_id = trail_order.get("algoId")
        # trail_activation_price already stored upstream, but confirm
        trade_state.trail_activation_price = trail_activation_price_quant  # Already Decimal
        log(f"Placed TRAILING_STOP_MARKET (activation: {trail_activation_price_quant:.4f}, callback: {callback_rate:.2f}%): {trail_order}",
            telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)
    
    # === EMERGENCY: All protective orders failed ===
    if failures >= 3:
        emergency_msg = (
            f"🚨 EMERGENCY CLOSE: ALL PROTECTIVE ORDERS FAILED 🚨\n"
            f"Symbol: {symbol} | Side: {trade_state.side}\n"
            f"Entry: {trade_state.entry_price:.4f} | Qty: {trade_state.qty}\n"
            f"Closing naked position IMMEDIATELY!"
        )
        log(emergency_msg, telegram_bot, telegram_chat_id)
        telegram_post(telegram_bot, telegram_chat_id, emergency_msg)
        try:
            _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
            log("EMERGENCY: Position closed due to protective order failures.", telegram_bot, telegram_chat_id)
        except Exception as close_e:
            log(f"EMERGENCY CLOSE FAILED: {close_e} — MANUAL INTERVENTION REQUIRED!", telegram_bot, telegram_chat_id)
        trade_state.active = False

# ------------------- DATA FETCHING WITH DECIMAL -------------------
def fetch_klines(client: BinanceClient, symbol: str, interval: str, limit: int = max(500, VOL_SMA_PERIOD * 3)) -> List[List[Any]]:
    requested = interval
    if requested == "45m":
        interval = "15m"
        limit = max(limit, 1500)  # Need enough 15m candles
    try:
        raw = client.public_request("/fapi/v1/klines", {
            "symbol": symbol,
            "interval": interval,
            "limit": limit
        })
        # === THIS IS THE CRITICAL FIX ===
        if requested == "45m":
            raw = aggregate_klines_to_45m(raw)  # ← DRIFT-PROOF VERSION APPLIED HERE
            # Optional: one-time startup message
            if len(raw) > 0 and len(raw) < 50:
                log(f"45m aggregation complete — {len(raw)} candles ready (from 15m data)", None, None)
        return raw
    except Exception as e:
        log(f"Klines fetch failed: {e}", None, None)
        return []
  
def ensure_tv_quality_data(klines: List[List[Any]], timeframe: str, is_testnet: bool = False) -> Tuple[bool, str]:
    """
    Strict on mainnet, relaxed on testnet.
    """
    if not klines:
        return False, "No data"
    min_candles = 150 if timeframe == "45m" else 250
    if len(klines) < min_candles:
        return False, f"Only {len(klines)} candles (need {min_candles}+)"
    
    interval = interval_ms(timeframe)
    
    # Adjust strictness based on network
    if is_testnet:
        check_recent = min(30, len(klines))
        max_allowed_gap_ms = interval * 2  # Very forgiving
    else:
        check_recent = min(100, len(klines))
        max_allowed_gap_ms = 300000  # 5 minutes max (strict)
    
    for i in range(len(klines) - check_recent + 1, len(klines)):
        if i == 0:
            continue
        prev_close_ms = int(klines[i-1][6])
        curr_open_ms = int(klines[i][0])
        expected_open_ms = prev_close_ms + interval
        diff_ms = curr_open_ms - expected_open_ms
        if abs(diff_ms) > max_allowed_gap_ms:
            diff_min = diff_ms / 60000
            if is_testnet and diff_ms < 0 and i > 50:
                continue  # Ignore old negative gaps on testnet
            return False, f"Gap detected at candle {i}: {diff_min:.1f} min diff"
    
    # Price validation (always strict - recent only)
    recent = klines[-20:]
    for idx, candle in enumerate(recent):
        if Decimal(str(candle[4])) <= Decimal("0") or Decimal(str(candle[1])) <= Decimal("0"):
            return False, f"Invalid price in recent candle"
    
    return True, f"OK: {len(klines)} candles (quality check passed)"

def fetch_balance(client: BinanceClient) -> Decimal:
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
        return Decimal(str(data.get("totalWalletBalance", "0")))
    except Exception as e:
        log(f"Balance fetch failed: {str(e)}")
        raise
  
def trading_allowed(client: BinanceClient, symbol: str, telegram_bot: Optional[str], telegram_chat_id: Optional[str]) -> bool:
    """Simple check for weekly DD and consecutive loss guards"""
    global bot_state
    
    # 1. Weekly DD Guard (20% hard stop)
    current_balance = fetch_balance(client)
    risk_allowed = get_current_risk_pct(
        current_equity=current_balance,
        client=client,
        symbol=symbol,
        telegram_bot=telegram_bot,
        telegram_chat_id=telegram_chat_id
    )
    if risk_allowed <= Decimal("0"):
        return False  # Weekly DD stop triggered
    
    # 2. Consecutive Loss Guard
    if bot_state.USE_CONSEC_LOSS_GUARD and bot_state.CONSEC_LOSSES >= bot_state.MAX_CONSEC_LOSSES:
        if not bot_state.consec_loss_guard_alert_sent:
            log(f"CONSECUTIVE FULL LOSSES REACHED ({bot_state.CONSEC_LOSSES}) — TRADING PAUSED UNTIL NEXT WEEK OR WIN", telegram_bot, telegram_chat_id)
            bot_state.consec_loss_guard_alert_sent = True
        return False
  
    return True

def has_active_position(client: BinanceClient, symbol: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> bool:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        for p in positions:
            if isinstance(p, dict) and p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != Decimal("0"):
                return True
        return False
    except Exception as e:
        log(f"Position check failed: {str(e)}", telegram_bot, telegram_chat_id)
        return False

def fetch_open_positions_details(client: BinanceClient, symbol: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> Optional[Dict[str, Any]]:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        for p in positions:
            if isinstance(p, dict) and p.get("symbol") == symbol:
                return p
        return None
    except Exception as e:
        log(f"Position details fetch failed: {str(e)}", telegram_bot, telegram_chat_id)
        raise

# ------------------- RECOVERY FUNCTIONS WITH RATE LIMIT HANDLING -------------------
def _retry_with_rate_limit(func: Any, *args: Any, max_retries: int = 3, **kwargs: Any) -> Any:
    """Wrapper for recovery functions to handle rate limits."""
    for attempt in range(max_retries):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            error_str = str(e).lower()
            if 'rate limit' in error_str or '429' in error_str or '503' in error_str:
                wait_time = (2 ** attempt) * 2  # Exponential backoff
                log(f"Rate limited in recovery. Attempt {attempt+1}/{max_retries}. Waiting {wait_time}s...")
                time.sleep(wait_time)
                continue
            else:
                raise
    raise Exception(f"Recovery failed after {max_retries} retries due to rate limits")

def debug_and_recover_expired_orders(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> bool:
    """Recover missing protective algo orders. Idempotent. Thread-safe."""
    global bot_state
    
    # ADD THIS: Don't run recovery if we're in the middle of closing
    if bot_state._position_closure_in_progress:
        return False
    
    if not trade_state.active:
        return False
  
    try:
        # Verify position exists
        pos_resp = _retry_with_rate_limit(
            client.send_signed_request, "GET", "/fapi/v2/positionRisk", {"symbol": symbol}
        )
        positions = pos_resp.get('data') if isinstance(pos_resp, dict) else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        if not pos_item or Decimal(str(pos_item.get("positionAmt", "0"))) == Decimal("0"):
            return False
      
        # Emergency close on ~1% adverse move (symmetric for long/short)
        current_price = Decimal(str(_retry_with_rate_limit(
            client.public_request, "/fapi/v1/ticker/price", {"symbol": symbol}
        )["price"]))
        entry = trade_state.entry_price  # Already Decimal
      
        adverse_move = False
        if trade_state.side == "LONG" and current_price <= entry * Decimal("0.99"):
            adverse_move = True
        elif trade_state.side == "SHORT" and current_price >= entry * Decimal("1.01"):
            adverse_move = True
      
        if adverse_move:
            log(f"EMERGENCY CLOSE: Price moved adversely ~1% | Entry={entry:.4f} Current={current_price:.4f}", telegram_bot, telegram_chat_id)
            _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
            trade_state.active = False
            return True  # Action taken (closure)
      
        # Fetch ONLY open algo orders (protectives are algo)
        algo_resp = _retry_with_rate_limit(
            client.send_signed_request, "GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol}
        )
        algo_open = algo_resp if isinstance(algo_resp, list) else []
        open_algo_ids = {o.get("algoId") for o in algo_open if o.get("algoId") is not None}
      
        recovered = False
      
        # Recover SL
        if trade_state.sl_algo_id and trade_state.sl_algo_id not in open_algo_ids:
            log(f"SL missing (algoId={trade_state.sl_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            sl_price = _calc_sl_price(trade_state.entry_price, trade_state.side, tick_size)
            new_sl = _place_stop_market(client, symbol, trade_state, sl_price)
            if new_sl and new_sl.get("algoId"):
                trade_state.sl_algo_id = new_sl["algoId"]
                trade_state.sl = sl_price  # Already Decimal
                log(f"SL RECOVERED | New algoId={trade_state.sl_algo_id} | Price={sl_price:.4f}", telegram_bot, telegram_chat_id)
                recovered = True
      
        # Recover TP
        if trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids:
            log(f"TP missing (algoId={trade_state.tp_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            tp_price = _calc_tp_price(trade_state.entry_price, trade_state.side, tick_size)
            new_tp = _place_take_profit(client, symbol, trade_state, tp_price)
            if new_tp and new_tp.get("algoId"):
                trade_state.tp_algo_id = new_tp["algoId"]
                trade_state.tp = tp_price  # Already Decimal
                log(f"TP RECOVERED | New algoId={trade_state.tp_algo_id} | Price={tp_price:.4f}", telegram_bot, telegram_chat_id)
                recovered = True
      
        # Recover Trailing — preserve original activation
        if trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids:
            log(f"Trailing missing (algoId={trade_state.trail_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            act_price = trade_state.trail_activation_price  # Already Decimal
            new_trail = _place_trailing_stop(client, symbol, trade_state, act_price)
            if new_trail and new_trail.get("algoId"):
                trade_state.trail_algo_id = new_trail["algoId"]
                log(f"TRAILING RECOVERED | New algoId={trade_state.trail_algo_id} | Activation={act_price:.4f}", telegram_bot, telegram_chat_id)
                recovered = True
      
        if recovered:
            log("Recovery complete — protective orders restored.", telegram_bot, telegram_chat_id)
      
        return recovered
      
    except Exception as e:
        log(f"Recovery failed: {e}", telegram_bot, telegram_chat_id)
        return False
      
# === PRIVATE HELPERS (DRY + SAFE) ===
def _calc_sl_price(entry: Optional[Decimal], side: Optional[str], tick_size: Decimal) -> Decimal:
    if entry is None or side is None:
        return Decimal("0")
    sl = entry * (Decimal("1") - SL_PCT) if side == "LONG" else entry * (Decimal("1") + SL_PCT)
    return quantize_price(sl, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

def _calc_tp_price(entry: Optional[Decimal], side: Optional[str], tick_size: Decimal) -> Decimal:
    if entry is None or side is None:
        return Decimal("0")
    R = entry * SL_PCT
    tp = entry + (TP_MULT * R) if side == "LONG" else entry - (TP_MULT * R)
    return quantize_price(tp, tick_size, ROUND_UP if side == "LONG" else ROUND_DOWN)

def _calc_trail_activation(entry: Optional[Decimal], side: Optional[str], tick_size: Decimal) -> Decimal:
    if entry is None or side is None:
        return Decimal("0")
    R = entry * SL_PCT
    act = entry + (TRAIL_TRIGGER_MULT * R) if side == "LONG" else entry - (TRAIL_TRIGGER_MULT * R)
    return quantize_price(act, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

def _place_stop_market(client: BinanceClient, symbol: str, ts: TradeState, price: Decimal) -> Optional[Any]:
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty
    if qty is None:
        return None
    try:
        return client.place_stop_market(symbol, side, qty, price, reduce_only=True, position_side=ts.side)
    except Exception as e:
        log(f"Failed to place stop market: {e}")
        return None

def _place_take_profit(client: BinanceClient, symbol: str, ts: TradeState, price: Decimal) -> Optional[Any]:
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty
    if qty is None:
        return None
    try:
        return client.place_take_profit_market(symbol, side, qty, price, reduce_only=True, position_side=ts.side)
    except Exception as e:
        log(f"Failed to place take profit: {e}")
        return None

def _place_trailing_stop(client: BinanceClient, symbol: str, ts: TradeState, act_price: Decimal) -> Optional[Any]:
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty
    if qty is None:
        return None
    rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
    try:
        return client.place_trailing_stop_market(symbol, side, qty, rate, act_price, reduce_only=True, position_side=ts.side)
    except Exception as e:
        log(f"Failed to place trailing stop: {e}")
        return None

def _tg_notify(title: str, body: str, symbol: str, bot: Optional[str], chat_id: Optional[str]):
    if bot and chat_id:
        telegram_post(bot, chat_id, f"{title} for {symbol}\n{body}")

# ------------------- POLLING FALLBACK -------------------
def start_polling_mode(symbol: str, telegram_bot: Optional[str], telegram_chat_id: Optional[str]):
    global bot_state
    if bot_state._polling_active:
        return
    bot_state._polling_active = True
    log(f"Now polling price every {POLLING_INTERVAL}s via REST API.", telegram_bot, telegram_chat_id)
    
    def polling_loop():
        while bot_state._polling_active and not bot_state.STOP_REQUESTED:
            try:
                ticker = bot_state.client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                price = Decimal(str(ticker['price']))
                bot_state._price_queue.put(price)
            except Exception as e:
                log(f"Polling failed: {e}. Will retry...", telegram_bot, telegram_chat_id)
            time.sleep(POLLING_INTERVAL)
    
    threading.Thread(target=polling_loop, daemon=True).start()

# ------------------- MONITOR TRADE WITH DECIMAL -------------------
def monitor_trade(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, telegram_bot: Optional[str], telegram_chat_id: Optional[str], current_candle_close_time: int):
    global bot_state
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    trade_start_time = Decimal(str(time.time()))
    last_recovery_check = Decimal("0")
    current_price: Optional[Decimal] = None
    ws = None
    ws_running = False
    
    # === WEBSOCKET CALLBACKS ===
    def on_message(ws_app: Any, message: str):
        nonlocal current_price
        try:
            data = json.loads(message)
            if data.get('e') == 'trade' and 'p' in data:
                current_price = Decimal(str(data['p']))
                bot_state._price_queue.put(current_price)
        except Exception as e:
            log(f"WebSocket parse error: {e}", telegram_bot, telegram_chat_id)
    
    def on_error(ws_app: Any, error: Any):
        global bot_state
        if not bot_state._ws_failed and trade_state.active:
            log(f"WebSocket connection error: {error}. Switching to polling mode.", telegram_bot, telegram_chat_id)
            # REMOVE emergency telegram message - this is not an emergency
            # telegram_post(telegram_bot, telegram_chat_id, "WebSocket failed Switched to REST polling (3s)")
            bot_state._ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)
    
    def on_close(ws_app: Any, close_status_code: Any, close_reason: Any):
        global bot_state
        if not bot_state._ws_failed and trade_state.active:
            log("WebSocket closed. Switching to polling mode.", telegram_bot, telegram_chat_id)
            bot_state._ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)
    
    def on_open(ws_app: Any):
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
        while trade_state.active and not bot_state.STOP_REQUESTED:
            if current_price is None:
                time.sleep(1)
                continue
            
            # === FETCH KLINES FOR VOLATILITY ===
            try:
                klines = fetch_klines(client, symbol, "30m", limit=100)
            except Exception as e:
                log(f"Failed to fetch klines: {e}", telegram_bot, telegram_chat_id)
                klines = []
            
            # VOLATILITY ABORT
            if len(klines) >= 100 and check_volatility_abort(klines):
                log("VOLATILITY EMERGENCY CLOSE – ATR SPIKE >3x", telegram_bot, telegram_chat_id)
                _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
                telegram_post(telegram_bot, telegram_chat_id, "EMERGENCY CLOSE – ATR SPIKE >3x")
                return
            
            # --- Recovery Check ---
            if Decimal(str(time.time())) - last_recovery_check >= Decimal(str(RECOVERY_CHECK_INTERVAL)):
                # Optional: Brief status every minute to prove the check is alive
                if int(time.time()) % 60 == 0:
                    log("Periodic recovery check running...", telegram_bot, telegram_chat_id)
              
                recovered = debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
              
                last_recovery_check = Decimal(str(time.time()))
              
                if recovered:
                    log("Recovery successful — missing protective orders restored.", telegram_bot, telegram_chat_id)
            
            # --- Get Latest Price (WITH SANITY CHECK) ---
            try:
                price_candidate = bot_state._price_queue.get_nowait()
                # CRITICAL: Reject insane prices (0, negative, or absurdly high)
                if (price_candidate <= Decimal('0') or
                    price_candidate > Decimal('1000')):  # SOL will never be >$1000 soon
                    log(f"IGNORED INSANE PRICE: {price_candidate}", telegram_bot, telegram_chat_id)
                    continue
                current_price = price_candidate
            except queue.Empty:
                pass
            
            # --- Position Check ---
            try:
                pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
              
                # Normalize to list of dicts
                if isinstance(pos_resp, dict) and 'data' in pos_resp:
                    positions = pos_resp['data']
                elif isinstance(pos_resp, list):
                    positions = pos_resp
                else:
                    log(f"Unexpected positionRisk response type: {type(pos_resp)}", telegram_bot, telegram_chat_id)
                    positions = []
              
                # Defensive: Find matching symbol only if item is dict
                pos_item = None
                for item in positions:
                    if isinstance(item, dict) and item.get("symbol") == symbol:
                        pos_item = item
                        break
              
                if pos_item is None:
                    log("No position data found for symbol during monitor", telegram_bot, telegram_chat_id)
                    pos_amt = Decimal('0')
                else:
                    pos_amt = Decimal(str(pos_item.get("positionAmt", "0")))
              
                if pos_amt == Decimal('0') and trade_state.active:
                    # ADD THIS CHECK: If closure is already being handled by _request_stop, skip
                    if bot_state._position_closure_in_progress:
                        log("Position closure already in progress by stop handler. Skipping duplicate processing.", telegram_bot, telegram_chat_id)
                        trade_state.active = False
                        return  # Exit monitor_trade immediately
                    
                    # === POSITION CLOSED – DETERMINE EXACT REASON & FILL PRICE ===
                    log("Position closed (verified via positionAmt == 0). Determining exit reason and exact fill price...", telegram_bot, telegram_chat_id)
                    trade_state.active = False
                    # Give Binance time to finalize internal state
                    time.sleep(1.2)
                    reason = "Unknown"
                    exit_price_dec: Optional[Decimal] = None
                    try:
                        # Fetch open algo orders (specific to conditional/algo types)
                        algo_open_resp = client.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
                        algo_open = algo_open_resp if isinstance(algo_open_resp, list) else []
                        open_algo_ids = {o.get("algoId") for o in algo_open if o.get("algoId")}
                        # Use stored algo IDs (updated by place_orders/recovery)
                        sl_algo_id = trade_state.sl_algo_id
                        tp_algo_id = trade_state.tp_algo_id
                        trail_algo_id = trade_state.trail_algo_id
                        # Priority check: Trailing → SL → TP
                        triggered_id = None
                        if (trade_state.trail_activated and trail_algo_id and trail_algo_id not in open_algo_ids):
                            reason = "Trailing Stop"
                            triggered_id = trail_algo_id
                        elif sl_algo_id and sl_algo_id not in open_algo_ids:
                            reason = "Stop Loss"
                            triggered_id = sl_algo_id
                        elif tp_algo_id and tp_algo_id not in open_algo_ids:
                            reason = "Take Profit"
                            triggered_id = tp_algo_id
                        else:
                            reason = "Manual Close" if not bot_state.STOP_REQUESTED else "Stop Requested"
                        # Primary: Get exact fill price from triggered algo order's trades
                        if triggered_id:
                            exit_price_dec = client.get_latest_fill_price(symbol, triggered_id)
                    except Exception as e:
                        log(f"Error detecting protective order trigger: {e}. Falling back to trade history.", telegram_bot, telegram_chat_id)
                    # Fallback if no protective fill price
                    if exit_price_dec is None:
                        latest = client.get_latest_trade_details(symbol)
                        if latest and latest.get("price"):
                            exit_price_dec = Decimal(str(latest["price"]))
                            reason = reason if reason != "Unknown" else "Recent Trade (Likely Protective Order)"
                        else:
                            # Absolute last resort
                            try:
                                ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                                exit_price_dec = Decimal(str(ticker.get("price", "0")))
                                reason = reason if reason != "Unknown" else "Market Close (No Fill Data)"
                            except Exception as e:
                                log(f"Ticker fallback failed during closure: {e}", telegram_bot, telegram_chat_id)
                                exit_price_dec = Decimal("0")
                                reason = "Unknown (Data Unavailable)"
                    
                    exit_price = exit_price_dec if exit_price_dec else Decimal("0")
                    # --- Log PNL ---
                    entry_price_safe = trade_state.entry_price or Decimal("0")
                    R = entry_price_safe * SL_PCT
                    pnl_row = log_pnl(
                        len(bot_state.pnl_data) + 1,
                        trade_state.side or "UNKNOWN",
                        entry_price_safe,
                        exit_price,
                        trade_state.qty or Decimal("0"),
                        R
                    )
                    # --- Enhanced Logging ---
                    log(f"Position closed by {reason}", telegram_bot, telegram_chat_id)
                    log(
                        f"Entry: {entry_price_safe:.4f} → Exit: {exit_price:.4f} | "
                        f"PNL: {Decimal(str(pnl_row['pnl_usd'])):.2f} USDT ({Decimal(str(pnl_row['pnl_r'])):.2f}R)",
                        telegram_bot, telegram_chat_id
                    )
                    # --- Telegram Notification ---
                    send_closure_telegram(
                        symbol=symbol,
                        side=trade_state.side or "UNKNOWN",
                        entry_price=entry_price_safe,
                        exit_price=exit_price,
                        qty=trade_state.qty or Decimal("0"),
                        pnl_usd=Decimal(str(pnl_row['pnl_usd'])),
                        pnl_r=Decimal(str(pnl_row['pnl_r'])),
                        reason=reason,
                        bot=telegram_bot,
                        chat_id=telegram_chat_id
                    )
                    # --- Final Cleanup: Eliminate any lingering orders ---
                    try:
                        client.cancel_all_open_orders(symbol)
                        log("[ZOMBIE KILLER] Nuclear strike executed — all ghosts eliminated", telegram_bot, telegram_chat_id)
                    except Exception as e:
                        log(f"Cleanup cancel failed: {e}", telegram_bot, telegram_chat_id)
                    # Prevent duplicate processing
                    bot_state._orders_cancelled = True
                    return  # Exit monitor_trade cleanly
              
                # --- Update High/Low ---
                if current_price is not None:
                    if trade_state.side == "LONG":
                        if trade_state.highest_price is None or current_price > trade_state.highest_price:
                            trade_state.highest_price = current_price
                    else:  # SHORT
                        if trade_state.lowest_price is None or current_price < trade_state.lowest_price:
                            trade_state.lowest_price = current_price
                
                # --- Trailing Activation (WITH INSANE PRICE PROTECTION) ---
                if (not trade_state.trail_activated and
                    trade_state.trail_activation_price and
                    current_price is not None and
                    current_price > Decimal('1')):
                    trail_activation_price_dec = trade_state.trail_activation_price  # Already Decimal
                    if ((trade_state.side == "LONG" and current_price >= trail_activation_price_dec) or
                        (trade_state.side == "SHORT" and current_price <= trail_activation_price_dec)):
                        trade_state.trail_activated = True
                        R_dec = trade_state.risk  # Already Decimal
                        activation_dec = trade_state.trail_activation_price  # Already Decimal
                        
                        if trade_state.side == "LONG":
                            init_stop_raw = activation_dec - (TRAIL_DISTANCE_MULT * R_dec)
                            init_stop = quantize_price(init_stop_raw, tick_size, ROUND_DOWN)
                        else:
                            init_stop_raw = activation_dec + (TRAIL_DISTANCE_MULT * R_dec)
                            init_stop = quantize_price(init_stop_raw, tick_size, ROUND_UP)
                        
                        send_trailing_activation_telegram(
                            symbol, trade_state.side or "UNKNOWN",
                            current_price, init_stop,
                            telegram_bot, telegram_chat_id
                        )
                        trade_state.current_trail_stop = init_stop
                        trade_state.last_trail_alert = Decimal(str(time.time()))
                
                # --- TRAILING UPDATES (NATIVE BINANCE TRACKING ONLY) ---
                if trade_state.trail_activated and Decimal(str(time.time())) - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE and current_price is not None:
                    R_dec = trade_state.risk  # Already Decimal
                    updated = False
                    new_stop: Optional[Decimal] = None
                    
                    if trade_state.side == "LONG":
                        expected_stop_raw = trade_state.highest_price - (TRAIL_DISTANCE_MULT * R_dec)
                        expected_stop = quantize_price(expected_stop_raw, tick_size, ROUND_DOWN)
                        current_stop = trade_state.current_trail_stop or Decimal('0')
                        if expected_stop > current_stop:
                            updated = True
                            new_stop = expected_stop
                    else:
                        expected_stop_raw = trade_state.lowest_price + (TRAIL_DISTANCE_MULT * R_dec)
                        expected_stop = quantize_price(expected_stop_raw, tick_size, ROUND_UP)
                        current_stop = trade_state.current_trail_stop or Decimal('0')
                        if expected_stop < current_stop:
                            updated = True
                            new_stop = expected_stop
                    
                    if updated and new_stop:
                        trade_state.current_trail_stop = new_stop
                        trade_state.last_trail_alert = Decimal(str(time.time()))
                        send_trailing_update_telegram(symbol, trade_state.side or "UNKNOWN", new_stop, telegram_bot, telegram_chat_id)
                
                time.sleep(1)
            except Exception as e:
                log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
                time.sleep(2)
    finally:
        if not trade_state.active:
            bot_state._polling_active = False
            bot_state._ws_failed = False
            try:
                if ws and ws_running:
                    ws.close()
            except Exception as e:
                log(f"Error closing WebSocket: {e}", telegram_bot, telegram_chat_id)

# ------------------- TRADING LOOP WITH DECIMAL -------------------
def trading_loop(client: BinanceClient, symbol: str, timeframe: str, max_trades_per_day: int, risk_pct: Decimal, max_daily_loss_pct: Decimal, tp_mult: Decimal, use_trailing: bool, prevent_same_bar: bool, require_no_pos: bool, use_max_loss: bool, use_volume_filter: bool, telegram_bot: Optional[str], telegram_chat_id: Optional[str]):
    global bot_state
    global last_news_guard_msg, news_guard_was_active
    global last_no_klines_log
  
    interval_seconds = interval_ms(timeframe) / 1000.0
    trades_today = 0
    last_processed_time = 0
    trade_state = TradeState()
    qty_api: Optional[Decimal] = None
    pending_entry = False
  
    # Get filters once
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    min_qty = filters['minQty']
    tick_size = filters['tickSize']
    min_notional = filters['minNotional']
    bot_state.max_trades_alert_sent = False
  
    last_trade_date = datetime.now(timezone.utc).date()
    log(f"Bot started on {last_trade_date}. Trades today: {trades_today}", telegram_bot, telegram_chat_id)
    signal.signal(signal.SIGINT, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    signal.signal(signal.SIGTERM, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    log(f"Starting bot with symbol={symbol}, timeframe={timeframe}, risk_pct={risk_pct*Decimal('100'):.1f}%")
    
    # === RECOVER EXISTING POSITION ON STARTUP ===
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol, telegram_bot, telegram_chat_id)
        if pos:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt != Decimal("0"):
                trade_state.active = True
                trade_state.side = "LONG" if pos_amt > Decimal("0") else "SHORT"
                trade_state.qty = abs(pos_amt)
                trade_state.entry_price = Decimal(str(pos.get("entryPrice", "0")))
                trade_state.risk = trade_state.entry_price * SL_PCT
                trade_state.sl_order_id = None
                trade_state.tp_order_id = None
                trade_state.trail_order_id = None
                log("Existing position detected on startup. Recovering orders...", telegram_bot, telegram_chat_id)
                debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, int(time.time() * 1000))
    
    # === MAIN TRADING LOOP — WITH DECIMAL CONSISTENCY ===
    while not bot_state.STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            # === IF IN TRADE → STAY COMPLETELY SILENT UNTIL EXIT ===
            if trade_state.active:
                monitor_trade(
                    client, symbol, trade_state, tick_size,
                    telegram_bot, telegram_chat_id,
                    trade_state.entry_close_time or int(time.time() * 1000)
                )
                continue  # Back to loop after trade ends
            
            # === DAILY RESET ===
            now_date = datetime.now(timezone.utc).date()
            if last_trade_date != now_date:
                old_date = last_trade_date or "None"
                last_trade_date = now_date
                trades_today = 0
                bot_state.max_trades_alert_sent = False
                daily_start_balance = fetch_balance(client)
                log(f"NEW DAY → {old_date} → {now_date} | Trades reset | Equity: ${daily_start_balance:.2f}", telegram_bot, telegram_chat_id)
            
            if trades_today >= max_trades_per_day:
                if not bot_state.max_trades_alert_sent:
                    log(f"Max trades reached ({max_trades_per_day}). No more today.", telegram_bot, telegram_chat_id)
                    bot_state.max_trades_alert_sent = True
                time.sleep(60)
                continue
            
            if not trading_allowed(client, symbol, telegram_bot, telegram_chat_id):
                time.sleep(1)
                continue
          
            current_balance = fetch_balance(client)
            log(f"Risk allowed: {BASE_RISK_PCT:.3%}", telegram_bot, telegram_chat_id)
            
            # === FETCH KLINES & VALIDATE QUALITY ===
            klines = fetch_klines(client, symbol, timeframe)
            # Rough detection based on key pattern (testnet keys often start with specific prefixes)
            bot_state.is_testnet = True
            is_good, msg = ensure_tv_quality_data(klines, timeframe, is_testnet=bot_state.is_testnet)
            if not is_good:
                log(f"Data quality failed: {msg}. Skipping this cycle.", telegram_bot, telegram_chat_id)
                time.sleep(10)
                continue
            
            latest_close_ms = int(klines[-1][6])
            # Optional: Warn if data appears stale (non-blocking, just visibility)
            now_ms = int(time.time() * 1000)
            stale_minutes = (now_ms - latest_close_ms) / 60000
            if stale_minutes > 90:  # More than 1.5 hours behind → likely connection issue
                log(f"⚠️ Warning: Latest candle is {stale_minutes:.1f} minutes old — possible delay in data feed",
                    telegram_bot, telegram_chat_id)
            
            # === ALIGN TO NEW CANDLE CLOSE ===
            if bot_state.last_processed_close_ms is not None and latest_close_ms <= bot_state.last_processed_close_ms:
                wait_sec = max(1.0, (latest_close_ms + interval_ms(timeframe) - int(time.time() * 1000)) / 1000.0 + 2)
                next_dt = datetime.fromtimestamp((latest_close_ms + interval_ms(timeframe)) / 1000, tz=timezone.utc)
                log(f"Waiting for next {timeframe} candle close in {wait_sec:.1f}s → {next_dt.strftime('%H:%M')} UTC",
                    telegram_bot, telegram_chat_id)
                _safe_sleep(wait_sec)
                continue
            
            bot_state.last_processed_close_ms = latest_close_ms
            dt = datetime.fromtimestamp(latest_close_ms / 1000, tz=timezone.utc)
            log(f"Aligned to {timeframe} candle close: {dt.strftime('%H:%M')} UTC", telegram_bot, telegram_chat_id)
          
            close_price = Decimal(str(klines[-1][4]))
            open_price = Decimal(str(klines[-1][1]))
            curr_vol = Decimal(str(klines[-1][5]))
            is_green_candle = close_price > open_price
            closes, volumes, _, _ = closes_and_volumes_from_klines(klines)
            
            # RSI calculation now uses Decimal list
            rsi = compute_rsi(closes)
            
            # SMA calculation now uses Decimal list
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD) if len(volumes) >= VOL_SMA_PERIOD else None
            
            # Format state string with Decimal values
            rsi_str = f"{rsi:.2f}" if rsi else "None"
            vol_sma15_str = f"{vol_sma15:.2f}" if vol_sma15 else "None"
            state = f"{close_price:.4f}|{rsi_str}|{curr_vol:.0f}|{vol_sma15_str}|{'G' if is_green_candle else 'R'}"
            
            if bot_state.last_candle_state is None or state != bot_state.last_candle_state:
                # Create display variables for the log message
                rsi_display = f"{rsi:.2f}" if rsi else "N/A"
                vol_sma15_display = f"{vol_sma15:.2f}" if vol_sma15 else "N/A"
                log(f"Candle: {close_price:.4f} RSI={rsi_display} Vol={curr_vol:.0f} SMA15={vol_sma15_display} {'Green' if is_green_candle else 'Red'}", telegram_bot, telegram_chat_id)
                bot_state.last_candle_state = state
            
            # Volume comparison uses Decimal
            buy_signal = (rsi and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_volume_filter or (vol_sma15 and curr_vol > vol_sma15)))
            sell_signal = (rsi and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and not is_green_candle and (not use_volume_filter or (vol_sma15 and curr_vol > vol_sma15)))
            
            if (buy_signal or sell_signal) and not pending_entry:
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close → {side_text}. Preparing entry.", telegram_bot, telegram_chat_id)
                pending_entry = True
                entry_price = close_price  # Already Decimal
                
                # === SLIPPAGE GUARD ===
                MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")
                entry_price_dec = entry_price
                slippage_pct: Optional[Decimal] = None
                current_price: Optional[Decimal] = None
                source = ""
                
                try:
                    ticker = client.public_request("/fapi/v1/ticker/bookTicker", {"symbol": symbol})
                    bid = Decimal(str(ticker.get("bidPrice") or "0"))
                    ask = Decimal(str(ticker.get("askPrice") or "0"))
                    if bid > Decimal("0") and ask > Decimal("0"):
                        current_price = (bid + ask) / Decimal("2")
                        slippage_pct = abs(current_price - entry_price_dec) / entry_price_dec
                        source = "bookTicker midpoint"
                    else:
                        raise ValueError("Invalid bid/ask prices")
                except Exception as e1:
                    try:
                        mark_data = client.public_request("/fapi/v1/premiumIndex", {"symbol": symbol})
                        current_price = Decimal(str(mark_data["markPrice"]))
                        slippage_pct = abs(current_price - entry_price_dec) / entry_price_dec
                        source = "mark price (fallback)"
                    except Exception as e2:
                        log(f"Mark price also failed ({e2}). Proceeding without slippage guard.", telegram_bot, telegram_chat_id)
                        slippage_pct = Decimal("0")
                        source = "none (disabled)"
                
                # Final decision with Decimal comparison
                if slippage_pct and slippage_pct > MAX_ENTRY_SLIPPAGE_PCT:
                    current_price_str = f"{current_price:.4f}" if current_price else "N/A"
                    log(
                        f"ENTRY SKIPPED: Estimated slippage {slippage_pct*Decimal('100'):.3f}% > 0.2% "
                        f"[{source}]\n"
                        f" Candle close: {entry_price_dec:.4f} → Current: {current_price_str}",
                        telegram_bot, telegram_chat_id
                    )
                    pending_entry = False
                    continue
                else:
                    current_price_str = f"{current_price:.4f}" if current_price else "N/A"
                    slippage_display = slippage_pct * Decimal('100') if slippage_pct else Decimal('0')
                    log(
                        f"Slippage check passed: {slippage_display:.3f}% "
                        f"[{source}]\n"
                        f" Close: {entry_price_dec:.4f} → Current: {current_price_str}",
                        telegram_bot, telegram_chat_id
                    )
                
                # === CALCULATE RISK & LEVELS WITH DECIMAL ===
                if buy_signal:
                    sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price + (TP_MULT * R)
                    trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R)
                else:
                    sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price - (TP_MULT * R)
                    trail_activation_price_dec = entry_price - (TRAIL_TRIGGER_MULT * R)
                
                if R <= Decimal('0'):
                    log("Invalid R. Skipping.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    continue
                
                risk_amount_usd = current_balance * BASE_RISK_PCT
                max_notional_by_leverage = current_balance * MAX_LEVERAGE
                max_qty_by_leverage = max_notional_by_leverage / entry_price
                qty_raw = risk_amount_usd / R
                qty = min(qty_raw, max_qty_by_leverage)
                qty = qty * Decimal("0.7")
                qty_api = quantize_qty(qty, step_size)
                
                # MIN_NOTIONAL check with Decimal
                if (qty_api * entry_price) < min_notional:
                    log(f"Qty too small → SKIP (Notional: {qty_api * entry_price:.2f} < Min: {min_notional:.2f})", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    continue
                
                log(f"===== TRADE ENTRY DETAILS =====", telegram_bot, telegram_chat_id)
                log(f"Direction: {side_text} | Price: ${entry_price:.4f}", telegram_bot, telegram_chat_id)
                log(f"Quantity: {qty_api:.5f} SOL | Notional: ${qty_api * entry_price:.2f}", telegram_bot, telegram_chat_id)
                log(f"Risk: {BASE_RISK_PCT:.1%} (${risk_amount_usd:.2f})", telegram_bot, telegram_chat_id)
                log(f"Balance: ${current_balance:.2f}", telegram_bot, telegram_chat_id)
                log(f"===== END ENTRY DETAILS =====", telegram_bot, telegram_chat_id)
                
                log(f"Sending MARKET {side_text} order: qty={qty_api}", telegram_bot, telegram_chat_id)
                order_res = client.send_signed_request("POST", "/fapi/v1/order", {
                    "symbol": symbol, "side": side_text, "type": "MARKET", "quantity": str(qty_api)
                })
                log(f"Market order placed: {order_res}", telegram_bot, telegram_chat_id)
                
                start_time = time.time()
                actual_qty: Optional[Decimal] = None
                
                while not bot_state.STOP_REQUESTED:
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break
                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        log("Order fill timeout. Cancelling.", telegram_bot, telegram_chat_id)
                        pending_entry = False
                        break
                    time.sleep(0.5)
                
                if actual_qty is None:
                    pending_entry = False
                    continue
                
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    actual_fill_price = entry_price
                
                actual_fill_price_dec = actual_fill_price  # Keep as Decimal
                
                # === RECALCULATE ALL LEVELS WITH ACTUAL FILL PRICE ===
                R = actual_fill_price_dec * SL_PCT
                
                if buy_signal:  # LONG
                    sl_price_dec = actual_fill_price_dec * (Decimal("1") - SL_PCT)
                    sl_rounding = ROUND_DOWN
                    tp_price_dec = actual_fill_price_dec + (TP_MULT * R)
                    tp_rounding = ROUND_UP
                    trail_raw = actual_fill_price_dec + (TRAIL_TRIGGER_MULT * R)
                    trail_buffered = trail_raw + TRAIL_PRICE_BUFFER
                    trail_activation_quant = quantize_price(trail_buffered, tick_size, ROUND_UP)
                else:  # SHORT
                    sl_price_dec = actual_fill_price_dec * (Decimal("1") + SL_PCT)
                    sl_rounding = ROUND_UP
                    tp_price_dec = actual_fill_price_dec - (TP_MULT * R)
                    tp_rounding = ROUND_DOWN
                    trail_raw = actual_fill_price_dec - (TRAIL_TRIGGER_MULT * R)
                    trail_buffered = trail_raw - TRAIL_PRICE_BUFFER
                    trail_activation_quant = quantize_price(trail_buffered, tick_size, ROUND_DOWN)
                
                sl_price_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                tp_price_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                final_trail_activation = trail_activation_quant  # Already Decimal
                
                # === ACTIVATE TRADE STATE WITH DECIMAL VALUES ===
                trade_state.active = True
                trade_state.entry_price = actual_fill_price_dec  # Store as Decimal
                trade_state.risk = R  # Store as Decimal
                trade_state.qty = actual_qty  # Store as Decimal
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = latest_close_ms
                trade_state.initial_sl = sl_price_quant  # Store as Decimal
                trade_state.sl = sl_price_quant  # Store as Decimal
                trade_state.tp = tp_price_quant  # Store as Decimal
                trade_state.trail_activated = False
                trade_state.trail_activation_price = final_trail_activation  # Store as Decimal
                
                log(f"DEBUG: Stored trail_activation_price = {final_trail_activation:.4f} in trade_state", telegram_bot, telegram_chat_id)
                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_dec:.4f}, "
                    f"sl={sl_price_quant:.4f}, tp={tp_price_quant:.4f}, trail_activation={final_trail_activation:.4f}",
                    telegram_bot, telegram_chat_id)
                
                # Telegram message with Decimal values
                tg_msg = (
                    f"NEW TRADE\n"
                    f"━━━━━━━━━━━━━━━━\n"
                    f"{trade_state.side} {symbol}\n"
                    f"Entry: {actual_fill_price_dec:.4f}\n"
                    f"Qty: {actual_qty:.5f} SOL\n"
                    f"SL: {sl_price_quant:.4f}\n"
                    f"TP: {tp_price_quant:.4f} ({TP_MULT}xR)\n"
                    f"Trail Activation: {final_trail_activation:.4f}\n"
                    f"Risk: {BASE_RISK_PCT:.1%} of equity\n"
                    f"━━━━━━━━━━━━━━━━"
                )
                telegram_post(telegram_bot, telegram_chat_id, tg_msg)
                
                # === PLACE PROTECTIVE ORDERS ===
                log(f"DEBUG: place_orders received trail_activation_price = {trade_state.trail_activation_price}", telegram_bot, telegram_chat_id)
                place_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                trades_today += 1
                pending_entry = False
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, latest_close_ms)
            else:
                if not pending_entry:
                    log("No trade signal on candle close.", telegram_bot, telegram_chat_id)
            
            # === PERFECT 45m WAIT — BINANCE SERVER TIME ALIGNED ===
            if timeframe == "45m":
                try:
                    # get Binance server time (ms)
                    server_time = int(client.public_request("/fapi/v1/time")["serverTime"])
                except Exception as e:
                    log(f"Failed to fetch server time: {e}", telegram_bot, telegram_chat_id)
                    # fallback to local time
                    server_time = int(time.time() * 1000)
                # true 45-minute grid using server time
                interval = interval_ms(timeframe)
                next_close_ms = ((server_time // interval) * interval) + interval
            else:
                # Native Binance alignment for other timeframes
                try:
                    server_time = int(client.public_request("/fapi/v1/time")["serverTime"])
                except Exception as e:
                    log(f"Failed to fetch server time: {e}", telegram_bot, telegram_chat_id)
                    server_time = int(time.time() * 1000)
                interval = interval_ms(timeframe)
                next_close_ms = ((server_time // interval) * interval) + interval
            
            # === WAIT ===
            now_ms = int(time.time() * 1000)
            wait_sec = max(2.0, (next_close_ms - now_ms) / 1000.0 + 2.0)
            next_dt_log = datetime.fromtimestamp(next_close_ms / 1000, tz=timezone.utc)
            log(
                f"Waiting for next {timeframe} candle close in {wait_sec:.1f}s → "
                f"{next_dt_log.strftime('%H:%M')} UTC",
                telegram_bot,
                telegram_chat_id
            )
            _safe_sleep(wait_sec)
        
        except Exception as e:
            import traceback
            error_msg = f"Loop error: {str(e)}"
            full_trace = traceback.format_exc()
          
            logger.error(error_msg)
            logger.error(full_trace)
          
            try:
                telegram_post(telegram_bot, telegram_chat_id, f"⚠️ BOT ERROR ⚠️\n{error_msg}")
            except NameError:
                pass
            except Exception as e2:
                logger.error(f"Telegram error during exception handling: {e2}")
          
            time.sleep(2)
    
    log("Trading loop exited.", telegram_bot, telegram_chat_id)

def interval_ms(interval: str) -> int:
    interval = interval.strip().lower()
    if interval == "45m":
        return 45 * 60 * 1000  # 2700000 ms
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

def _safe_sleep(total_seconds: float):
    remaining = Decimal(str(total_seconds))
    while remaining > Decimal("0"):
        if bot_state.STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        sleep_time = min(Decimal("1"), remaining)
        time.sleep(float(sleep_time))
        remaining -= Decimal("1")

def run_scheduler(bot: Optional[str], chat_id: Optional[str]):
    global bot_state
    last_month: Optional[int] = None
    
    def daily_reset_job():
        """Handles equity reset and logging at 00:00 UTC."""
        try:
            # Uses your existing fetch_balance function
            current_balance = fetch_balance(bot_state.client)
            if current_balance > 0:
                bot_state.account_size = current_balance
                bot_state.daily_start_equity = current_balance
                log(f"DAILY RESET @ 00:00 UTC | New start equity: ${bot_state.daily_start_equity:.2f} USD", bot, chat_id)
                telegram_post(bot, chat_id, f"🔄 *DAILY RESET*\nEquity: ${bot_state.daily_start_equity:.2f}")
        except Exception as e:
            log(f"Daily reset failed: {e}", bot, chat_id)

    def weekly_reset_job():
        """Clears consecutive loss streak on Monday 00:00 UTC."""
        bot_state.CONSEC_LOSSES = 0
        bot_state.consec_loss_guard_alert_sent = False
        log("WEEKLY RESET: Consecutive loss streak cleared.", bot, chat_id)
        telegram_post(bot, chat_id, "🔄 *WEEKLY RESET*\nConsecutive losses cleared. Trading guard reset.")

    def check_monthly_report():
        nonlocal last_month
        current_date = datetime.now(timezone.utc)
        if current_date.day == 1 and (last_month is None or current_date.month != last_month):
            send_monthly_report(bot, chat_id) 
            last_month = current_date.month
    
    # Schedule all tasks using the schedule library for reliability
    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot, chat_id))
    schedule.every().day.at("00:00").do(daily_reset_job)
    schedule.every().monday.at("00:00").do(weekly_reset_job)
    schedule.every().day.at("00:00").do(check_monthly_report)
    
    log("Scheduler Initialized: Daily/Weekly resets and reporting active.", bot, chat_id)

    # Main loop that respects the bot's shutdown signal
    while not bot_state.STOP_REQUESTED:
        schedule.run_pending()
        time.sleep(1)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Binance Trailing, 45m Optimized, SOLUSDT)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", required=True, help="Telegram Bot Token")
    parser.add_argument("--chat-id", required=True, help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol (default: SOLUSDT)")
    parser.add_argument("--timeframe", default="45m", help="Timeframe (default: 45m)")
    parser.add_argument("--max-trades", type=int, default=1, help="Max trades per day (default: 1)")
    parser.add_argument("--risk-pct", type=float, default=6.8, help="Risk percentage per trade (default: 6.8%)")
    parser.add_argument("--max-loss-pct", type=float, default=6.8, help="Max daily loss percentage (default: 6.8%)")
    parser.add_argument("--tp-mult", type=float, default=9, help="Take-profit multiplier (default: 9)")
    parser.add_argument("--no-trailing", dest='use_trailing', action='store_false', help="Disable trailing stop")
    parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false')
    parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false')
    parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false')
    parser.add_argument("--use-volume-filter", action='store_true', default=False)
    parser.add_argument("--no-volume-filter", action='store_false', dest='use_volume_filter')
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--base-url", default=None)
    parser.add_argument("--no-news-guard", action="store_true", help="Completely disable news/economic calendar guard")
    args = parser.parse_args()
    
    if args.no_news_guard:
        NEWS_GUARD_ENABLED = False
        print("[CONFIG] News Guard FULLY DISABLED via --no-news-guard")
    else:
        NEWS_GUARD_ENABLED = True
    
    init_pnl_log()
    
    # ======================== SINGLE, BULLETPROOF SHUTDOWN ========================
    _shutdown_done = False
    
    def graceful_shutdown(sig: Optional[int] = None, frame: Any = None):
        global _shutdown_done
        if _shutdown_done:
            return
        _shutdown_done = True
        
        reason = {
            signal.SIGINT: "Ctrl+C",
            signal.SIGTERM: "SIGTERM / systemd",
        }.get(sig, "Clean exit")
        
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            reason = "KILL FLAG / Manual stop"
        
        goodbye = (
            f"RSI BOT STOPPED\n"
            f"Symbol: {args.symbol}\n"
            f"Timeframe: {args.timeframe}\n"
            f"Reason: {reason}\n"
            f"Time: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC"
        )
        
        try:
            log(goodbye, args.telegram_token, args.chat_id)
        except Exception as e:
            print(f"Error during goodbye log: {e}")
        
        # Clean lock file
        try:
            if LOCK_HANDLE:
                try:
                    LOCK_HANDLE.close()
                except:
                    pass
            if os.path.exists(LOCK_FILE):
                os.unlink(LOCK_FILE)
        except Exception as e:
            print(f"Error cleaning lock file: {e}")
        
        # Remove kill flag
        try:
            if os.path.exists("/tmp/STOP_BOT_NOW"):
                os.unlink("/tmp/STOP_BOT_NOW")
        except Exception as e:
            print(f"Error removing kill flag: {e}")
        
        os._exit(0)
    
    # Register exactly once
    signal.signal(signal.SIGINT, graceful_shutdown)
    signal.signal(signal.SIGTERM, graceful_shutdown)
    atexit.register(graceful_shutdown)
    
    # ======================== IMMORTAL BOT LOOP ========================
    while True:
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            log("STOP_BOT_NOW flag detected – shutting down permanently", args.telegram_token, args.chat_id)
            graceful_shutdown()
            break
        
        try:
            bot_state.client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
            balance = fetch_balance(bot_state.client)
            bot_state.account_size = balance
            bot_state.daily_start_equity = balance
          
            # Set leverage on Binance
            leverage_to_set = 9  # or whatever you want
            bot_state.client.set_leverage(args.symbol, leverage_to_set)
            log(f"Set Binance leverage to {leverage_to_set}x for {args.symbol}", args.telegram_token, args.chat_id)
            
            # Format risk % safely and precisely with Decimal
            risk_pct_display = Decimal(str(args.risk_pct))
            log(f"Simple Weekly DD Guard: 20% hard stop", args.telegram_token, args.chat_id)
            log(f"Consecutive Loss Guard: 3 full losses stop", args.telegram_token, args.chat_id)
            log(f"Base Risk: {BASE_RISK_PCT*Decimal('100'):.2f}% per trade", args.telegram_token, args.chat_id)
            log(f"Fetched balance: ${balance:.2f} USDT", args.telegram_token, args.chat_id)
            
            if NEWS_GUARD_ENABLED:
                threading.Thread(target=news_heartbeat, daemon=True).start()
                log("Economic calendar monitoring: ENABLED", args.telegram_token, args.chat_id)
            else:
                log("Economic calendar monitoring: DISABLED (--no-news-guard)", args.telegram_token, args.chat_id)
            
            log(f"STARTING BOT → {args.symbol} | {args.timeframe} | "
                f"Risk: {risk_pct_display:.3f}% | "
                f"Volume Filter: {'ON' if args.use_volume_filter else 'OFF'} | "
                f"Mode: {'LIVE' if args.live else 'TESTNET'}",
                args.telegram_token, args.chat_id)
            
            threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()
            
            trading_loop(
                client=bot_state.client,
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
            
            log("Bot stopped cleanly – exiting.", args.telegram_token, args.chat_id)
            break
        
        except Exception as e:
            import traceback
            error_msg = f"BOT CRASHED → RESTARTING IN 15s\n{traceback.format_exc()}"
            try:
                log(error_msg, args.telegram_token, args.chat_id)
                telegram_post(args.telegram_token, args.chat_id, "BOT CRASHED – RESTARTING IN 15s")
            except Exception as e2:
                print(f"Error during crash logging: {e2}")
            time.sleep(15)
