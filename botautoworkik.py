# Binance Futures RSI Bot — MERGED MAIN + INSURANCE (Hedge Mode)
# CORRECTED PRODUCTION VERSION — Dual‑leg with positionSide and 50% safety factor
# All fixes applied: insurance fill detection, positionSide everywhere, recovery for both legs

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
from telegram.ext.filters import COMMAND
from telegram import Update
from telegram.ext import Application, CommandHandler, ContextTypes, MessageHandler, filters
import asyncio
import telegram

# ------------------- CONFIGURATION -------------------
RISK_PCT = Decimal("0.068")  # 6.8% per trade (MAIN LEG)
SL_PCT = Decimal("0.0075")  # 0.75%
TP_MULT = Decimal("9")       # MAIN LEG TP multiplier
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2")  # 2.5R trailing distance
VOL_SMA_PERIOD = 16
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 1
INTERVAL_DEFAULT = "45m"
ORDER_FILL_TIMEOUT = 90
BUY_RSI_MIN = Decimal("55")
BUY_RSI_MAX = Decimal("65")
SELL_RSI_MIN = Decimal("35")
SELL_RSI_MAX = Decimal("45")
POSITION_CHECK_INTERVAL = 30
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = Decimal("5.0")
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RATE_LIMIT_CHECK_INTERVAL = 60
RATE_LIMIT_THRESHOLD = 80
RECOVERY_CHECK_INTERVAL = 10  # Seconds between recovery checks
TRAIL_UPDATE_THROTTLE = Decimal("10.0")  # Alert trailing updates every 10 seconds max
POLLING_INTERVAL = 3  # Polling interval after WS failure

# ==================== INSURANCE / HEDGE MODE CONFIGURATION ====================
INSURANCE_ENABLED = True            # Master switch for insurance leg
INSURANCE_DELAY_MS = 1200            # Delay before opening insurance leg (ms)
SAFETY_FACTOR = Decimal("0.90")      # 50% safety factor (as requested)

# Virtual split configuration (emulating two separate accounts)
MAIN_VIRTUAL_CAPITAL = Decimal("250")      # $250 virtual capital for MAIN
INSURANCE_VIRTUAL_CAPITAL = Decimal("250") # $250 virtual capital for INSURANCE
MARGIN_USAGE_PCT = Decimal("0.75")         # Use 75% of virtual capital ($187.50 each)
# ========================================================================

# For recovery only (insurance TP/SL are normally set in trading loop)
INSURANCE_SL_MULT = Decimal("1.0")   # 1R SL
INSURANCE_TP_MULT = Decimal("1.25")   # 1.25R TP

# ---------------------------------------------------------------------------------------
# === CONFIG: BLACKOUT WINDOWS (UTC) ===
# (weekday: 0=Mon..6=Sun, None=every day), (start_h, m), (end_h, m)
NEWS_BLACKOUT_WINDOWS = [
    (4, (12, 25), (13, 5)),  # Friday 12:30–13:00 UTC (NFP)
    (2, (18, 55), (19, 35)),  # Wednesday 19:00–19:30 UTC (FOMC)
]

# === CONFIG: LIVE API ===
LIVE_APIS = [
    "https://nfs.faireconomy.media/ff_calendar_thisweek.json",
    "https://ec.forexprostools.com/?columns=exc_currency,exc_type&timezone=utc"
]
LOCAL_CALENDAR = "high_impact_calendar.json"  # you update weekly
LOCAL_OVERRIDE = "news_calendar_override.json"  # one-off manual block
CACHE_DURATION = 300  # 5 min
HIGH_IMPACT_KEYWORDS = {
    "NFP", "NONFARM", "CPI", "FOMC", "GDP", "UNEMPLOYMENT", "RATE DECISION",
    "PCE", "CORE", "ISM", "JOLTS", "OPEC", "SNB", "BOJ", "GEOPOLITICAL",
    "RETAIL SALES", "ADP", "FLASH", "PRELIMINARY"
}
BUFFER_MINUTES = 5

# === CONFIG: NEWS GUARD ===
NEWS_GUARD_ENABLED = True  # ← Will be overridden by --no-news-guard

# if not NEWS_GUARD_ENABLED:
    # logging.getLogger().setLevel(logging.WARNING) # Optional: reduce noise

# CONFIG SLIPAGE
MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")
LOCK_FILE = os.path.join(os.getenv('TEMP', '/tmp'), 'edison_insurance_bot.lock')
BASE_RISK_PCT = Decimal("0.068")  # 6.8% when drawdown = 0%
MAX_LEVERAGE = Decimal("9")        # MAIN LEG leverage

# === WEEKLY SCALING QUICK TOGGLE ===
ENABLE_WEEKLY_SCALING = True  # ← Set to False to disable scaling completely
HALF_R_THRESHOLD = Decimal("0.00375")  # 0.5R threshold (0.5 * 0.0075 = 0.375%)

# ------------------- BOT STATE CLASS (BUNDLED GLOBALS) -------------------
class BotState:
    """Bundle all global state variables into a single class for better organization."""
    def __init__(self):
        # Core bot state
        self.STOP_REQUESTED = False
        self.client = None
        self.symbol_filters_cache: Dict[str, Dict[str, Decimal]] = {}
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
        self.last_no_klines_log = 0  # Added for trading_loop
        
        # Performance tracking
        self.max_trades_alert_sent = False
        self.daily_start_equity: Optional[Decimal] = None
        self.account_size: Optional[Decimal] = None
        
        # Dual-leg trading state
        self.RESTART_REQUESTED = False
        self._restart_lock = threading.Lock()
        self.start_time = datetime.now(timezone.utc)
        self.current_trade = None      # Will hold the main trade state
        self.insurance_trade = None    # Will hold the insurance trade state
        self.INSURANCE_ACTIVE = False  # Flag if insurance leg is active

# Initialize global bot state
bot_state = BotState()
LOCK_HANDLE = None  # Add this line

# ------------------- SINGLE INSTANCE LOCK WITH PID CHECK -------------------
def acquire_lock():
    """Acquire single instance lock with PID check to prevent stale locks."""
    global LOCK_HANDLE
    
    try:
        # Check if lock file exists and contains a valid PID
        if os.path.exists(LOCK_FILE):
            try:
                with open(LOCK_FILE, 'r') as f:
                    pid_str = f.read().strip()
                    if pid_str and pid_str.isdigit():
                        pid = int(pid_str)
                        
                        # Special case: if it's the same PID as current process, it's a restart
                        if pid == os.getpid():
                            print(f"Same PID {pid} - this is a restart, continuing...")
                            # Just use the existing lock file
                            pass
                        else:
                            # Check if process is still running
                            process_exists = False
                            if platform.system() == "Windows":
                                import psutil
                                try:
                                    psutil.Process(pid)
                                    process_exists = True
                                except (psutil.NoSuchProcess, psutil.AccessDenied):
                                    process_exists = False
                            else:
                                # Unix: try sending signal 0 to check if process exists
                                try:
                                    os.kill(pid, 0)
                                    process_exists = True
                                except OSError:
                                    process_exists = False
                            
                            if process_exists:
                                # Process exists, another instance is running
                                print(f"Another instance is already running with PID {pid}! Exiting.")
                                sys.exit(1)
                            else:
                                # Process doesn't exist, stale lock file
                                print(f"Removing stale lock file from PID {pid}")
                                os.unlink(LOCK_FILE)
            except Exception as e:
                print(f"Error reading lock file: {e}")
                # If we can't read/parse the lock file, remove it and continue
                try:
                    os.unlink(LOCK_FILE)
                except:
                    pass
        
        # Create new lock file with current PID
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
            f.flush()
            os.fsync(f.fileno())  # Ensure it's written to disk
        
        print(f"Lock file created with PID {os.getpid()}")
        
        # On Unix systems, add file locking
        if platform.system() != "Windows":
            try:
                import fcntl
                lock_handle = open(LOCK_FILE, 'r+')
                fcntl.lockf(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                print(f"Exclusive file lock acquired")
                # Keep lock file open while bot runs
                return lock_handle
            except (IOError, OSError) as e:
                print(f"Failed to acquire file lock: {e}")
                # If we can't get the lock, another instance might have it
                # Check if it's our own PID
                with open(LOCK_FILE, 'r') as f:
                    file_pid = int(f.read().strip())
                    if file_pid == os.getpid():
                        print("Lock file has our PID but couldn't get lock - continuing anyway")
                        return None
                sys.exit(1)
            except Exception as e:
                print(f"Unexpected error acquiring lock: {e}")
                sys.exit(1)
        
        return None
        
    except FileExistsError:
        print("Another instance is already running! Exiting.")
        sys.exit(1)
    except FileNotFoundError:
        # Directory may not exist
        os.makedirs(os.path.dirname(LOCK_FILE), exist_ok=True)
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
        return None

# ------------------- MEMORY LIMIT (Linux / OCI only) -------------------
# Removed memory limit cap completely — let the OS manage it
# (previously: resource.setrlimit capped at ~680 MB — caused OOM crashes)

# Optional: Show current memory usage at startup (requires psutil)
try:
    import psutil
    mem_mb = psutil.Process().memory_info().rss / 1024**2
    print(f"[Startup] Initial memory usage: {mem_mb:.1f} MB")
except ImportError:
    print("[Startup] Install psutil to monitor memory: pip install psutil")
except Exception as e:
    print(f"[Startup] Could not read memory usage: {e}")

# Keep the original Windows check if you ever run locally on Windows
if platform.system() == "Windows":
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
        return int(time.time() * 1000)  # Fallback to local
  
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
    
    # FIXED: Use np.maximum for two arrays at a time
    tr1 = highs[1:] - lows[1:]
    tr2 = np.abs(highs[1:] - closes[:-1])
    tr3 = np.abs(lows[1:] - closes[:-1])
    
    # Combine step by step
    tr = np.maximum(tr1, tr2)
    tr = np.maximum(tr, tr3)
    
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
    # log(f"DEBUG: Today={now.date()} Weekday={now.weekday()} WeeklyStart={bot_state.weekly_start_time} ConsecLosses={bot_state.CONSEC_LOSSES}", telegram_bot, telegram_chat_id)
    
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
    client: Any,  # BinanceClient instance
    symbol: str = "SOLUSDT",  # Made parameter with default for flexibility
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
PNL_FIELDS = ['date', 'trade_id', 'side', 'leg_type', 'entry', 'exit', 'pnl_usd', 'pnl_r', 'loss_streak']

def init_pnl_log():
    if not os.path.exists(bot_state.PNL_LOG_FILE):
        with open(bot_state.PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
            writer.writeheader()

def log_pnl(trade_id: int, side: str, entry: Decimal, exit_price: Decimal, qty: Decimal, R: Decimal, leg_type: str = "MAIN") -> Dict[str, Any]:
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
        'leg_type': leg_type,
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
def send_trade_telegram(trade_details: Dict[str, Any], leg_type: str, bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"📈 {leg_type} LEG ENTRY\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"Symbol: {trade_details['symbol']}\n"
        f"Side: {trade_details['side']}\n"
        f"Entry Price: {trade_details['entry']:.4f}\n"
        f"SL: {trade_details['sl']:.4f}\n"
        f"TP: {trade_details['tp']:.4f}\n"
        f"Qty: {trade_details['qty']:.5f} SOL\n"
        f"Leverage: {trade_details.get('leverage', 'N/A')}x\n"
    )
    if trade_details.get('trail_activation'):
        message += f"Trailing Activation: {trade_details['trail_activation']:.4f}\n"
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol: str, side: str, entry_price: Decimal, exit_price: Decimal, 
                          qty: Decimal, pnl_usd: Decimal, pnl_r: Decimal, reason: str, 
                          leg_type: str, bot: Optional[str], chat_id: Optional[str]):
    global bot_state
    
    message = (
        f"🔴 {leg_type} LEG CLOSED\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"Symbol: {symbol}\n"
        f"Side: {side}\n"
        f"Entry Price: {entry_price:.4f}\n"
        f"Exit Price: {exit_price:.4f}\n"
        f"Reason: {reason}\n"
        f"Qty: {qty:.5f}\n"
        f"PNL: {pnl_usd:.2f} USDT ({pnl_r:.2f}R)\n"
        f"Loss Streak: {bot_state.CONSEC_LOSSES}"
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
    
    # Split by leg type
    main_wins = sum(1 for trade in filtered_trades if trade['leg_type'] == 'MAIN' and trade['pnl_usd'] > 0)
    insurance_wins = sum(1 for trade in filtered_trades if trade['leg_type'] == 'INSURANCE' and trade['pnl_usd'] > 0)
    
    return (
        f"{period.capitalize()} PNL Report:\n"
        f"- Total Trades: {num_trades}\n"
        f"- Total PNL: {total_pnl_usd:.2f} USDT\n"
        f"- Average PNL per Trade: {avg_pnl_usd:.2f} USDT\n"
        f"- Total PNL (R): {total_pnl_r:.2f}R\n"
        f"- Win Rate: {win_rate:.2f}% ({wins} wins, {losses} losses)\n"
        f"- MAIN Wins: {main_wins} | INSURANCE Wins: {insurance_wins}\n"
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
    
def daily_memory_log(bot: Optional[str] = None, chat_id: Optional[str] = None):
    """Log current memory usage once per day at 00:01 UTC"""
    global bot_state
    try:
        import psutil
        import gc
        process = psutil.Process()
        mem_mb = process.memory_info().rss / 1024 / 1024
        obj_count = len(gc.get_objects())
        
        log(f"📊 DAILY MEMORY USAGE: {mem_mb:.1f} MB | Objects: {obj_count:,}", bot, chat_id)
        
        if mem_mb > 800:
            log(f"⚠️ High memory warning: {mem_mb:.1f} MB", bot, chat_id)
            
    except Exception as e:
        log(f"❌ Memory log error: {e}", bot, chat_id)
        
# ------------------- STOP HANDLER (IDEMPOTENT) WITH DECIMAL -------------------
def _request_stop(signum: Optional[int] = None, frame: Any = None, symbol: Optional[str] = None, 
                  telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    global bot_state
    
    with bot_state._stop_lock:
        if bot_state.STOP_REQUESTED:
            logger.info("Stop already requested; skipping duplicate cleanup.")
            return
        bot_state.STOP_REQUESTED = True
    
    bot_state._position_closure_in_progress = True
    log("🛑 STOP REQUESTED — Closing ALL positions and cancelling orders...", telegram_bot, telegram_chat_id)

    if not bot_state.client or not symbol:
        log("Client or symbol not available. Skipping closure.", telegram_bot, telegram_chat_id)
        bot_state._position_closure_in_progress = False
        return

    closed_positions = False

    try:
        # Get fresh positions
        pos_resp = bot_state.client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp.get('data') if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp
        if not isinstance(positions, list):
            positions = [positions] if isinstance(positions, dict) else []

        for pos in positions:
            if not isinstance(pos, dict) or pos.get("symbol") != symbol:
                continue

            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt == Decimal('0'):
                continue

            position_side = pos.get("positionSide")
            entry_price_dec = Decimal(str(pos.get("entryPrice", "0")))
            qty = abs(pos_amt)
            close_side = "SELL" if pos_amt > Decimal('0') else "BUY"

            # Determine leg type
            leg_type = "UNKNOWN"
            if bot_state.current_trade and bot_state.current_trade.active and position_side == bot_state.current_trade.side:
                leg_type = "MAIN"
            elif bot_state.insurance_trade and bot_state.insurance_trade.active and position_side == bot_state.insurance_trade.side:
                leg_type = "INSURANCE"

            log(f"Closing {leg_type} leg → {position_side} | Qty: {qty} | Side: {close_side}", 
                telegram_bot, telegram_chat_id)

            # Place market close
            order_params = {
                "symbol": symbol,
                "side": close_side,
                "type": "MARKET",
                "quantity": str(qty)
            }
            if position_side:
                order_params["positionSide"] = position_side

            response = bot_state.client.send_signed_request("POST", "/fapi/v1/order", order_params)
            market_order_id = response.get("orderId")

            # Wait longer for fill confirmation
            time.sleep(1.5)

            # Get exact exit price
            exit_price_dec = Decimal("0")
            try:
                trades = bot_state.client.send_signed_request("GET", "/fapi/v1/userTrades", {
                    "symbol": symbol,
                    "orderId": market_order_id,
                    "limit": 10
                })
                filled = [t for t in trades if Decimal(str(t.get("qty", "0"))) > Decimal('0')]
                if filled:
                    exit_price_dec = Decimal(str(filled[-1]["price"]))
            except Exception as e:
                log(f"Failed to get exact fill price: {e}", telegram_bot, telegram_chat_id)

            if exit_price_dec == Decimal("0"):
                try:
                    ticker = bot_state.client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price_dec = Decimal(str(ticker.get("price", "0")))
                except:
                    pass

            # Log PNL
            R = entry_price_dec * SL_PCT
            pnl_row = log_pnl(
                len(bot_state.pnl_data) + 1,
                "LONG" if pos_amt > Decimal('0') else "SHORT",
                entry_price_dec,
                exit_price_dec,
                qty,
                R,
                leg_type
            )

            send_closure_telegram(
                symbol=symbol,
                side="LONG" if pos_amt > Decimal('0') else "SHORT",
                entry_price=entry_price_dec,
                exit_price=exit_price_dec,
                qty=qty,
                pnl_usd=Decimal(str(pnl_row.get('pnl_usd', 0))),
                pnl_r=Decimal(str(pnl_row.get('pnl_r', 0))),
                reason="Stop Requested",
                leg_type=leg_type,
                bot=telegram_bot,
                chat_id=telegram_chat_id
            )

            closed_positions = True

        if closed_positions:
            log("✅ All positions successfully closed via market orders.", telegram_bot, telegram_chat_id)
        else:
            log("No open positions found at stop time.", telegram_bot, telegram_chat_id)

    except Exception as e:
        log(f"Error while closing positions: {str(e)}", telegram_bot, telegram_chat_id)

    # Final order cleanup
    try:
        bot_state.client.cancel_all_open_orders(symbol)
        log(f"All open orders cancelled for {symbol}.", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Order cancellation failed: {e}", telegram_bot, telegram_chat_id)

    bot_state._orders_cancelled = True
    bot_state._position_closure_in_progress = False

    # Clear bot state
    bot_state.current_trade = None
    bot_state.insurance_trade = None
    bot_state.INSURANCE_ACTIVE = False

    log("🛑 Stop process completed.", telegram_bot, telegram_chat_id)
    
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
                         reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        params = {
            "algoType": "CONDITIONAL",
            "symbol": symbol,
            "side": side,
            "type": order_type,
            "quantity": str(quantity),
            "timeInForce": "GTE_GTC",
            "priceProtect": "true"
        }
        if reduce_only:
            params["reduceOnly"] = "true"
        if position_side:
            params["positionSide"] = position_side
        
        if trigger_price is not None:
            params["triggerPrice"] = str(trigger_price)
            params["workingType"] = "CONTRACT_PRICE"
        if activation_price is not None:
            params["activatePrice"] = str(activation_price)
        if callback_rate is not None:
            params["callbackRate"] = str(callback_rate)
        
        return self.send_signed_request("POST", "/fapi/v1/algoOrder", params)

    def place_stop_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                          reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "STOP_MARKET", trigger_price=stop_price, reduce_only=reduce_only, position_side=position_side)

    def place_take_profit_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                                reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "TAKE_PROFIT_MARKET", trigger_price=stop_price, reduce_only=reduce_only, position_side=position_side)

    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal,
                                  callback_rate: Decimal, activation_price: Decimal,
                                  reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "TRAILING_STOP_MARKET",
                                     activation_price=activation_price, callback_rate=callback_rate, reduce_only=reduce_only, position_side=position_side)
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
        self.leg_type = "MAIN"  # "MAIN" or "INSURANCE"
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
def place_orders(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal,
                 telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    if not trade_state.active or not trade_state.entry_price:
        log("ERROR: place_orders called with incomplete trade_state (missing entry)", telegram_bot, telegram_chat_id)
        return

    entry_price = trade_state.entry_price
    qty_dec = trade_state.qty
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    position_side = trade_state.side.upper()

    # If insurance leg and SL/TP already set, use them directly
    if trade_state.leg_type == "INSURANCE" and trade_state.sl is not None and trade_state.tp is not None:
        sl_price_quant = trade_state.sl
        tp_price_quant = trade_state.tp
        use_trailing = False
    else:
        # MAIN leg: compute SL and TP
        R = entry_price * SL_PCT
        if trade_state.side == "LONG":
            sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
            sl_rounding = ROUND_DOWN
            tp_price_dec = entry_price + (TP_MULT * R)
            tp_rounding = ROUND_UP
        else:
            sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
            sl_rounding = ROUND_UP
            tp_price_dec = entry_price - (TP_MULT * R)
            tp_rounding = ROUND_DOWN
        sl_price_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
        tp_price_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
        use_trailing = True

    # === PLACE ORDERS ===
    failures = 0

    # Stop Loss
    try:
        sl_order = client.place_stop_market(
            symbol, close_side, qty_dec, sl_price_quant,
            reduce_only=False, position_side=position_side  # ← FIXED
        )
        trade_state.sl_order_id = sl_order.get("orderId")
        trade_state.sl_algo_id = sl_order.get("algoId")
        trade_state.sl = sl_price_quant
        log(f"[{trade_state.leg_type}] Placed STOP_MARKET SL at {sl_price_quant:.4f}: {sl_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"[{trade_state.leg_type}] Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)

    # Take Profit
    try:
        tp_order = client.place_take_profit_market(
            symbol, close_side, qty_dec, tp_price_quant,
            reduce_only=False, position_side=position_side  # ← FIXED
        )
        trade_state.tp_order_id = tp_order.get("orderId")
        trade_state.tp_algo_id = tp_order.get("algoId")
        trade_state.tp = tp_price_quant
        log(f"[{trade_state.leg_type}] Placed TAKE_PROFIT_MARKET TP at {tp_price_quant:.4f}: {tp_order}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"[{trade_state.leg_type}] Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)

    # Trailing Stop (only for MAIN leg)
    if use_trailing and trade_state.trail_activation_price is not None:
        callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
        try:
            trail_order = client.place_trailing_stop_market(
                symbol, close_side, qty_dec,
                callback_rate=callback_rate,
                activation_price=trade_state.trail_activation_price,
                reduce_only=False, position_side=position_side  # ← FIXED
            )
            trade_state.trail_order_id = trail_order.get("orderId")
            trade_state.trail_algo_id = trail_order.get("algoId")
            trade_state.trail_activated = True
            log(f"[{trade_state.leg_type}] Placed TRAILING_STOP_MARKET (activation: {trade_state.trail_activation_price:.4f}, callback: {callback_rate:.2f}%): {trail_order}",
                telegram_bot, telegram_chat_id)
        except Exception as e:
            failures += 1
            log(f"[{trade_state.leg_type}] Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)
    else:
        if not use_trailing:
            log(f"[{trade_state.leg_type}] Trailing stop disabled for this leg", telegram_bot, telegram_chat_id)

    # === EMERGENCY: All protective orders failed ===
    if failures >= 2:  # At least SL and TP failed
        emergency_msg = (
            f"🚨 EMERGENCY CLOSE: PROTECTIVE ORDERS FAILED 🚨\n"
            f"Leg: {trade_state.leg_type} | Symbol: {symbol} | Side: {trade_state.side}\n"
            f"Entry: {trade_state.entry_price:.4f} | Qty: {trade_state.qty}\n"
            f"Closing naked position IMMEDIATELY!"
        )
        log(emergency_msg, telegram_bot, telegram_chat_id)
        telegram_post(telegram_bot, telegram_chat_id, emergency_msg)
        try:
            _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
            log(f"EMERGENCY: {trade_state.leg_type} leg closed due to protective order failures.", telegram_bot, telegram_chat_id)
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
        # Return all positions for this symbol (could be both sides)
        return [p for p in positions if isinstance(p, dict) and p.get("symbol") == symbol]
    except Exception as e:
        log(f"Position details fetch failed: {str(e)}", telegram_bot, telegram_chat_id)
        raise

def get_position_amt_for_side(client: BinanceClient, symbol: str, side: str) -> Decimal:
    """
    Get position amount for a specific side (LONG or SHORT) in hedge mode.
    Returns positive for long, negative for short? Actually Binance returns absolute.
    For consistency, we return absolute quantity, and side indicates direction.
    """
    try:
        positions = fetch_open_positions_details(client, symbol)
        for pos in positions:
            if pos.get("positionSide") == side.upper():
                return Decimal(str(pos.get("positionAmt", "0")))
        return Decimal('0')
    except Exception as e:
        log(f"Failed to get position for side {side}: {e}")
        return Decimal('0')
def has_any_active_leg() -> bool:
    """Return True if MAIN or INSURANCE (or both) legs are still active."""
    global bot_state
    main_active = bot_state.current_trade is not None and bot_state.current_trade.active
    ins_active = bot_state.insurance_trade is not None and bot_state.insurance_trade.active
    return main_active or ins_active
# ------------------- SLIPPAGE CHECK HELPER -------------------
def _check_slippage(client: BinanceClient, symbol: str, entry_price: Decimal, 
                    telegram_bot: Optional[str], telegram_chat_id: Optional[str]) -> Tuple[bool, Decimal]:
    """Check slippage and return (passed, actual_price)"""
    try:
        ticker = client.public_request("/fapi/v1/ticker/bookTicker", {"symbol": symbol})
        bid = Decimal(str(ticker.get("bidPrice") or "0"))
        ask = Decimal(str(ticker.get("askPrice") or "0"))
        if bid > Decimal("0") and ask > Decimal("0"):
            current_price = (bid + ask) / Decimal("2")
            slippage_pct = abs(current_price - entry_price) / entry_price
            source = "bookTicker midpoint"
        else:
            raise ValueError("Invalid bid/ask prices")
    except Exception as e1:
        try:
            mark_data = client.public_request("/fapi/v1/premiumIndex", {"symbol": symbol})
            current_price = Decimal(str(mark_data["markPrice"]))
            slippage_pct = abs(current_price - entry_price) / entry_price
            source = "mark price (fallback)"
        except Exception as e2:
            log(f"Mark price also failed ({e2}). Proceeding without slippage guard.", telegram_bot, telegram_chat_id)
            return True, entry_price
    
    if slippage_pct > MAX_ENTRY_SLIPPAGE_PCT:
        log(f"ENTRY SKIPPED: Estimated slippage {slippage_pct*Decimal('100'):.3f}% > 0.2% [{source}]", 
            telegram_bot, telegram_chat_id)
        return False, entry_price
    
    return True, current_price

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
    if trade_state.leg_type == "INSURANCE":
        return False
    # ADD THIS: Don't run recovery if we're in the middle of closing
    if bot_state._position_closure_in_progress:
        return False
    
    if not trade_state.active:
        return False
  
    try:
        # Verify position exists for this leg's side
        position_side = trade_state.side.upper()
        pos_amt = get_position_amt_for_side(client, symbol, position_side)
        if pos_amt == Decimal("0"):
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
            log(f"[{trade_state.leg_type}] EMERGENCY CLOSE: Price moved adversely ~1% | Entry={entry:.4f} Current={current_price:.4f}", telegram_bot, telegram_chat_id)
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
            log(f"[{trade_state.leg_type}] SL missing (algoId={trade_state.sl_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            sl_price = _calc_sl_price(trade_state.entry_price, trade_state.side, tick_size)
            new_sl = _place_stop_market(client, symbol, trade_state, sl_price)
            if new_sl and new_sl.get("algoId"):
                trade_state.sl_algo_id = new_sl["algoId"]
                trade_state.sl = sl_price
                log(f"[{trade_state.leg_type}] SL RECOVERED | New algoId={trade_state.sl_algo_id} | Price={sl_price:.4f}", telegram_bot, telegram_chat_id)
                recovered = True
      
        # Recover TP
        if trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids:
            log(f"[{trade_state.leg_type}] TP missing (algoId={trade_state.tp_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            tp_price = _calc_tp_price(trade_state.entry_price, trade_state.side, tick_size, trade_state.leg_type)
            new_tp = _place_take_profit(client, symbol, trade_state, tp_price)
            if new_tp and new_tp.get("algoId"):
                trade_state.tp_algo_id = new_tp["algoId"]
                trade_state.tp = tp_price
                log(f"[{trade_state.leg_type}] TP RECOVERED | New algoId={trade_state.tp_algo_id} | Price={tp_price:.4f}", telegram_bot, telegram_chat_id)
                recovered = True
      
        # Recover Trailing — preserve original activation (only for MAIN leg)
        if trade_state.leg_type == "MAIN" and trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids:
            log(f"[{trade_state.leg_type}] Trailing missing (algoId={trade_state.trail_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            act_price = trade_state.trail_activation_price
            new_trail = _place_trailing_stop(client, symbol, trade_state, act_price)
            if new_trail and new_trail.get("algoId"):
                trade_state.trail_algo_id = new_trail["algoId"]
                # Set trail_activated to True after successful recovery
                trade_state.trail_activated = True
                log(f"[{trade_state.leg_type}] TRAILING RECOVERED | New algoId={trade_state.trail_algo_id} | Activation={act_price:.4f}", telegram_bot, telegram_chat_id)
                recovered = True
      
        if recovered:
            log(f"[{trade_state.leg_type}] Recovery complete — protective orders restored.", telegram_bot, telegram_chat_id)
      
        return recovered
      
    except Exception as e:
        log(f"[{trade_state.leg_type}] Recovery failed: {e}", telegram_bot, telegram_chat_id)
        return False
      
# === PRIVATE HELPERS (DRY + SAFE) ===
def _calc_sl_price(entry: Optional[Decimal], side: Optional[str], tick_size: Decimal, leg_type: str = "MAIN") -> Decimal:
    if entry is None or side is None:
        return Decimal("0")
    if leg_type == "INSURANCE":
        sl_mult = INSURANCE_SL_MULT
    else:
        sl_mult = Decimal("1")
    
    sl = entry * (Decimal("1") - (SL_PCT * sl_mult)) if side == "LONG" else entry * (Decimal("1") + (SL_PCT * sl_mult))
    return quantize_price(sl, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

def _calc_tp_price(entry: Optional[Decimal], side: Optional[str], tick_size: Decimal, leg_type: str = "MAIN") -> Decimal:
    if entry is None or side is None:
        return Decimal("0")
    R = entry * SL_PCT
    if leg_type == "INSURANCE":
        tp_mult = INSURANCE_TP_MULT
    else:
        tp_mult = TP_MULT
    
    tp = entry + (tp_mult * R) if side == "LONG" else entry - (tp_mult * R)
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
        # FIXED: reduce_only=False for new protective orders
        return client.place_stop_market(symbol, side, qty, price, reduce_only=False, position_side=ts.side.upper())
    except Exception as e:
        log(f"Failed to place stop market: {e}")
        return None

def _place_take_profit(client: BinanceClient, symbol: str, ts: TradeState, price: Decimal) -> Optional[Any]:
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty
    if qty is None:
        return None
    try:
        # FIXED: reduce_only=False
        return client.place_take_profit_market(symbol, side, qty, price, reduce_only=False, position_side=ts.side.upper())
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
        # FIXED: reduce_only=False
        return client.place_trailing_stop_market(symbol, side, qty, rate, act_price, reduce_only=False, position_side=ts.side.upper())
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
                if price <= 0 or price > Decimal('1000'):
                    continue
                bot_state._price_queue.put(price)
            except Exception as e:
                log(f"Polling failed: {e}. Will retry...", telegram_bot, telegram_chat_id)
            time.sleep(POLLING_INTERVAL)
    
    threading.Thread(target=polling_loop, daemon=True).start()

def get_position_amt(client: BinanceClient, symbol: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> Decimal:
    """Get current net position amount for a symbol (positive for long, negative for short)."""
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        # In hedge mode, net is sum of both sides (one positive, one negative)
        net = Decimal('0')
        for p in positions:
            if isinstance(p, dict) and p.get("symbol") == symbol:
                amt = Decimal(str(p.get("positionAmt", "0")))
                net += amt
        return net
    except Exception as e:
        log(f"Failed to get net position amount: {e}", telegram_bot, telegram_chat_id)
        return Decimal('0')
    
def recover_existing_positions(client, symbol, tick_size, telegram_bot, telegram_chat_id):
    """Recover and monitor existing positions - orders already on Binance."""
    global bot_state
    try:
        # Get all positions for the symbol
        positions = fetch_open_positions_details(client, symbol, telegram_bot, telegram_chat_id)
        if not positions:
            return
        
        for pos in positions:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt == Decimal('0'):
                continue
            
            position_side = pos.get("positionSide")  # "LONG" or "SHORT"
            entry_price = Decimal(str(pos.get("entryPrice", "0")))
            qty = abs(pos_amt)
            
            # Determine leg type (main or insurance) based on existing state?
            # We'll try to match with stored trades; if not, default to MAIN
            leg_type = "MAIN"
            if bot_state.insurance_trade and bot_state.insurance_trade.active:
                if (position_side == "LONG" and bot_state.insurance_trade.side == "LONG") or \
                   (position_side == "SHORT" and bot_state.insurance_trade.side == "SHORT"):
                    leg_type = "INSURANCE"
            elif bot_state.current_trade and bot_state.current_trade.active:
                if (position_side == "LONG" and bot_state.current_trade.side == "LONG") or \
                   (position_side == "SHORT" and bot_state.current_trade.side == "SHORT"):
                    leg_type = "MAIN"
            
            # Create trade state
            trade_state = TradeState()
            trade_state.active = True
            trade_state.leg_type = leg_type
            trade_state.side = "LONG" if position_side == "LONG" else "SHORT"
            trade_state.qty = qty
            trade_state.entry_price = entry_price
            trade_state.risk = entry_price * SL_PCT
            trade_state.entry_close_time = int(time.time() * 1000)
            
            # Calculate TP and trail based on leg type
            if leg_type == "INSURANCE":
                trade_state.tp = _calc_tp_price(entry_price, trade_state.side, tick_size, "INSURANCE")
                trade_state.trail_activation_price = None
                trade_state.trail_activated = False
            else:
                trade_state.tp = _calc_tp_price(entry_price, trade_state.side, tick_size, "MAIN")
                trade_state.trail_activation_price = _calc_trail_activation(entry_price, trade_state.side, tick_size)
                # Trail will be activated later when price reaches activation; we don't know if it was already activated
                # For simplicity, we set trail_activated = False initially; monitoring will handle if needed
                trade_state.trail_activated = False
            
            trade_state.sl = _calc_sl_price(entry_price, trade_state.side, tick_size)
            
            # Store in bot_state
            if leg_type == "INSURANCE":
                bot_state.insurance_trade = trade_state
                bot_state.INSURANCE_ACTIVE = True
            else:
                bot_state.current_trade = trade_state
            
            # Start monitoring
            threading.Thread(
                target=monitor_trade,
                args=(client, symbol, trade_state, tick_size, 
                      telegram_bot, telegram_chat_id, int(time.time() * 1000)),
                daemon=True
            ).start()
            
            log(f"✅ Position recovery complete - {leg_type} leg ({position_side}) resumed", 
                telegram_bot, telegram_chat_id)
            
    except Exception as e:
        log(f"❌ Position recovery error: {e}", telegram_bot, telegram_chat_id)

# ------------------- MONITOR TRADE WITH DECIMAL -------------------
def monitor_trade(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, 
                  telegram_bot: Optional[str], telegram_chat_id: Optional[str], current_candle_close_time: int):
    global bot_state
    import psutil
    log(f"[{trade_state.leg_type}] Monitoring active trade...", telegram_bot, telegram_chat_id)
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
                price = Decimal(str(data['p']))
                if price <= 0 or price > Decimal('1000'):
                    return
                current_price = price
                bot_state._price_queue.put(price)        
        except Exception as e:
            log(f"[{trade_state.leg_type}] WebSocket parse error: {e}", telegram_bot, telegram_chat_id)
    
    def on_error(ws_app: Any, error: Any):
        global bot_state
        if not bot_state._ws_failed and trade_state.active:
            log(f"[{trade_state.leg_type}] WebSocket connection error: {error}. Switching to polling mode.", telegram_bot, telegram_chat_id)
            bot_state._ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)
    
    def on_close(ws_app: Any, close_status_code: Any, close_reason: Any):
        global bot_state
        if not bot_state._ws_failed and trade_state.active:
            log(f"[{trade_state.leg_type}] WebSocket closed. Switching to polling mode.", telegram_bot, telegram_chat_id)
            bot_state._ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)
    
    def on_open(ws_app: Any):
        subscribe_msg = {
            "method": "SUBSCRIBE",
            "params": [f"{symbol.lower()}@trade"],
            "id": 1
        }
        ws_app.send(json.dumps(subscribe_msg))
        log(f"[{trade_state.leg_type}] WebSocket subscribed to {symbol.lower()}@trade", telegram_bot, telegram_chat_id)
    
    def start_ws():
        nonlocal ws, ws_running
        if ws_running:
            return
        base_url = "wss://fstream.binance.com/ws" if client.use_live else "wss://stream.binancefuture.com/ws"
        log(f"[{trade_state.leg_type}] Connecting to WebSocket: {base_url}", telegram_bot, telegram_chat_id)
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
            # Respect emergency stop / closure in progress
            if bot_state._position_closure_in_progress or bot_state.STOP_REQUESTED:
                log(f"[{trade_state.leg_type}] Stop in progress - exiting monitor thread", telegram_bot, telegram_chat_id)
                trade_state.active = False
                return
            
            if current_price is None:
                time.sleep(1)
                continue
            
            # === FETCH KLINES FOR VOLATILITY ===
            try:
                klines = fetch_klines(client, symbol, "30m", limit=100)
            except Exception as e:
                log(f"[{trade_state.leg_type}] Failed to fetch klines: {e}", telegram_bot, telegram_chat_id)
                klines = []
            
            # VOLATILITY ABORT
            if len(klines) >= 100 and check_volatility_abort(klines):
                log(f"[{trade_state.leg_type}] VOLATILITY EMERGENCY CLOSE – ATR SPIKE >3x", telegram_bot, telegram_chat_id)
                _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
                telegram_post(telegram_bot, telegram_chat_id, f"EMERGENCY CLOSE – ATR SPIKE >3x ({trade_state.leg_type})")
                return
            
            # --- Recovery Check ---
            if Decimal(str(time.time())) - last_recovery_check >= Decimal(str(RECOVERY_CHECK_INTERVAL)):
                recovered = debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                last_recovery_check = Decimal(str(time.time()))
                if recovered:
                    log(f"[{trade_state.leg_type}] Recovery successful — missing protective orders restored.", telegram_bot, telegram_chat_id)
            
            # --- Get Latest Price (WITH SANITY CHECK) ---
            try:
                price_candidate = bot_state._price_queue.get_nowait()
                if (price_candidate <= Decimal('0') or price_candidate > Decimal('1000')):
                    log(f"[{trade_state.leg_type}] IGNORED INSANE PRICE: {price_candidate}", telegram_bot, telegram_chat_id)
                    continue
                current_price = price_candidate
            except queue.Empty:
                pass
            
            # --- Position Check (for this leg's side) ---
            try:
                pos_amt_side = get_position_amt_for_side(client, symbol, trade_state.side.upper())
                
                if pos_amt_side == Decimal('0') and trade_state.active:
                    if bot_state._position_closure_in_progress:
                        log(f"[{trade_state.leg_type}] Position closure already in progress. Skipping duplicate processing.", telegram_bot, telegram_chat_id)
                        trade_state.active = False
                        return
                    
                    log(f"[{trade_state.leg_type}] Position closed (verified via {trade_state.side} side positionAmt == 0). Determining exit reason...", telegram_bot, telegram_chat_id)
                    trade_state.active = False
                    time.sleep(1.2)
                    
                    reason = "Unknown"
                    exit_price_dec: Optional[Decimal] = None
                    
                    try:
                        algo_open_resp = client.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
                        algo_open = algo_open_resp if isinstance(algo_open_resp, list) else []
                        open_algo_ids = {o.get("algoId") for o in algo_open if o.get("algoId") is not None}
                        
                        sl_algo_id = trade_state.sl_algo_id
                        tp_algo_id = trade_state.tp_algo_id
                        trail_algo_id = trade_state.trail_algo_id
                        
                        triggered_id = None
                        if (trade_state.leg_type == "MAIN" and trade_state.trail_activated and trail_algo_id and trail_algo_id not in open_algo_ids):
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
                        
                        if triggered_id:
                            exit_price_dec = client.get_latest_fill_price(symbol, triggered_id)
                    except Exception as e:
                        log(f"[{trade_state.leg_type}] Error detecting trigger: {e}", telegram_bot, telegram_chat_id)
                    
                    if exit_price_dec is None:
                        latest = client.get_latest_trade_details(symbol)
                        if latest and latest.get("price"):
                            exit_price_dec = Decimal(str(latest["price"]))
                            reason = reason if reason != "Unknown" else "Recent Trade"
                        else:
                            try:
                                ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                                exit_price_dec = Decimal(str(ticker.get("price", "0")))
                                reason = reason if reason != "Unknown" else "Market Close"
                            except Exception as e:
                                log(f"[{trade_state.leg_type}] Ticker fallback failed: {e}", telegram_bot, telegram_chat_id)
                                exit_price_dec = Decimal("0")
                    
                    exit_price = exit_price_dec if exit_price_dec else Decimal("0")
                    entry_price_safe = trade_state.entry_price or Decimal("0")
                    R = entry_price_safe * SL_PCT
                    
                    # === PNL LOGGING (exactly as you had it) ===
                    pnl_row = log_pnl(
                        len(bot_state.pnl_data) + 1,
                        trade_state.side or "UNKNOWN",
                        entry_price_safe,
                        exit_price,
                        trade_state.qty or Decimal("0"),
                        R,
                        trade_state.leg_type
                    )
                    
                    log(f"[{trade_state.leg_type}] Position closed by {reason}", telegram_bot, telegram_chat_id)
                    log(f"[{trade_state.leg_type}] Entry: {entry_price_safe:.4f} → Exit: {exit_price:.4f} | PNL: {Decimal(str(pnl_row['pnl_usd'])):.2f} USDT ({Decimal(str(pnl_row['pnl_r'])):.2f}R)", telegram_bot, telegram_chat_id)
                    
                    send_closure_telegram(
                        symbol=symbol,
                        side=trade_state.side or "UNKNOWN",
                        entry_price=entry_price_safe,
                        exit_price=exit_price,
                        qty=trade_state.qty or Decimal("0"),
                        pnl_usd=Decimal(str(pnl_row['pnl_usd'])),
                        pnl_r=Decimal(str(pnl_row['pnl_r'])),
                        reason=reason,
                        leg_type=trade_state.leg_type,
                        bot=telegram_bot,
                        chat_id=telegram_chat_id
                    )
                    
                    # === TARGETED CLEANUP — Only this leg's orders ===
                    try:
                        algo_open_resp = client.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
                        algo_open = algo_open_resp if isinstance(algo_open_resp, list) else []
                        
                        leg_algo_ids = set()
                        if trade_state.sl_algo_id:   leg_algo_ids.add(trade_state.sl_algo_id)
                        if trade_state.tp_algo_id:   leg_algo_ids.add(trade_state.tp_algo_id)
                        if trade_state.trail_algo_id: leg_algo_ids.add(trade_state.trail_algo_id)
                        
                        cancelled = 0
                        for order in algo_open:
                            algo_id = order.get("algoId")
                            if algo_id and algo_id in leg_algo_ids:
                                try:
                                    client.send_signed_request("DELETE", "/fapi/v1/algoOrder", {
                                        "symbol": symbol,
                                        "algoId": str(algo_id)
                                    })
                                    log(f"[{trade_state.leg_type}] Cancelled its own algoId={algo_id}", telegram_bot, telegram_chat_id)
                                    cancelled += 1
                                    time.sleep(0.1)
                                except Exception as e:
                                    log(f"[{trade_state.leg_type}] Failed to cancel algoId={algo_id}: {e}", telegram_bot, telegram_chat_id)
                        
                        if cancelled == 0:
                            log(f"[{trade_state.leg_type}] No remaining algo orders found for this leg.", telegram_bot, telegram_chat_id)
                        
                        # Only do full cleanup if BOTH legs are now inactive
                        if not has_any_active_leg():
                            client.cancel_all_open_orders(symbol)
                            log(f"[ZOMBIE KILLER] Nuclear strike executed — all ghosts eliminated", telegram_bot, telegram_chat_id)
                        else:
                            log(f"[{trade_state.leg_type}] Leg closed — other leg still active. Its orders preserved.", telegram_bot, telegram_chat_id)
                            
                    except Exception as e:
                        log(f"[{trade_state.leg_type}] Order cleanup error: {e}", telegram_bot, telegram_chat_id)
                    
                    # Clear only this leg's state
                    if trade_state.leg_type == "INSURANCE":
                        bot_state.insurance_trade = None
                        bot_state.INSURANCE_ACTIVE = False
                    else:
                        bot_state.current_trade = None
                    
                    bot_state._orders_cancelled = True
                    return
              
                # --- Update High/Low for trailing (unchanged) ---
                if current_price is not None:
                    if trade_state.side == "LONG":
                        if trade_state.highest_price is None or current_price > trade_state.highest_price:
                            trade_state.highest_price = current_price
                    else:
                        if trade_state.lowest_price is None or current_price < trade_state.lowest_price:
                            trade_state.lowest_price = current_price
                
                # --- TRAILING UPDATES (only for MAIN leg) — unchanged ---
                if trade_state.leg_type == "MAIN" and trade_state.trail_activated and Decimal(str(time.time())) - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE and current_price is not None:
                    R_dec = trade_state.risk
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
                        
            except Exception as e:
                log(f"[{trade_state.leg_type}] Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
                time.sleep(2)
            
            # === HEARTBEAT ===
            if int(time.time()) % 2700 == 0:
                now_str = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')
                price_now = current_price if current_price is not None else Decimal("0")
                
                mem_str = "N/A"
                try:
                    mem_str = f"{psutil.Process().memory_info().rss / 1024**2:.0f} MB"
                except Exception as e:
                    pass
                
                entry_str = f"{trade_state.entry_price:.4f}" if trade_state.entry_price else "N/A"
                sl_str = f"{trade_state.sl:.4f}" if trade_state.sl else "N/A"
                
                hb_msg = (
                    f"[{trade_state.leg_type} HB {now_str}] Monitoring {trade_state.side} | "
                    f"Price: {price_now:.2f} | "
                    f"Entry: {entry_str} | "
                    f"SL: {sl_str} | "
                    f"Mem: {mem_str}"
                )
                log(hb_msg, telegram_bot, telegram_chat_id)
            
            time.sleep(1)
    finally:
        if not trade_state.active:
            bot_state._polling_active = False
            bot_state._ws_failed = False
            try:
                if ws and ws_running:
                    ws.close()
            except Exception as e:
                log(f"[{trade_state.leg_type}] Error closing WebSocket: {e}", telegram_bot, telegram_chat_id)

# ------------------- TRADING LOOP WITH DECIMAL -------------------
def trading_loop(client: BinanceClient, symbol: str, timeframe: str, max_trades_per_day: int,
                 risk_pct: Decimal, max_daily_loss_pct: Decimal, tp_mult: Decimal,
                 use_trailing: bool, prevent_same_bar: bool, require_no_pos: bool,
                 use_max_loss: bool, use_volume_filter: bool, telegram_bot: Optional[str],
                 telegram_chat_id: Optional[str]):
    global bot_state

    # === STATE TRACKING FOR CLEAN LOGGING ===
    last_position_state = "FLAT"
    last_candle_logged_ms = None
    last_trade_date = datetime.now(timezone.utc).date()
    trades_today = 0
    pending_entry = False
    bot_state.max_trades_alert_sent = False

    # Get symbol filters once (outside the loop)
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    min_notional = filters['minNotional']
    tick_size = filters['tickSize']

    log(f"🚀 Trading loop started → {symbol} | {timeframe} | Insurance: {'ENABLED' if INSURANCE_ENABLED else 'DISABLED'}",
        telegram_bot, telegram_chat_id)

    while not bot_state.STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            # === CRITICAL SAFETY CLEANUP ===
            any_leg_active = has_any_active_leg()

            # Sync real Binance position with bot state
            try:
                long_amt = get_position_amt_for_side(client, symbol, "LONG")
                short_amt = get_position_amt_for_side(client, symbol, "SHORT")
                real_position = abs(long_amt) + abs(short_amt)

                if real_position == Decimal('0') and any_leg_active:
                    log("⚠️ State desync: Binance flat but bot shows active trade → Resetting state",
                        telegram_bot, telegram_chat_id)
                    bot_state.current_trade = None
                    bot_state.insurance_trade = None
                    bot_state.INSURANCE_ACTIVE = False
                    any_leg_active = False
            except Exception as e:
                log(f"Position verification error: {e}", telegram_bot, telegram_chat_id)

            # Clear stale objects
            if bot_state.current_trade and not bot_state.current_trade.active:
                bot_state.current_trade = None
            if bot_state.insurance_trade and not bot_state.insurance_trade.active:
                bot_state.insurance_trade = None
                bot_state.INSURANCE_ACTIVE = False

            any_leg_active = has_any_active_leg()
            current_state = "ACTIVE" if any_leg_active else "FLAT"

            # === STATE CHANGE LOGGING ===
            if current_state != last_position_state:
                if current_state == "ACTIVE":
                    log("🚀 POSITION OPENED → Entering silent monitoring mode", telegram_bot, telegram_chat_id)
                else:
                    log("✅ POSITION CLOSED → Resuming signal scanning", telegram_bot, telegram_chat_id)
                last_position_state = current_state

            # === DAILY RESET ===
            now_date = datetime.now(timezone.utc).date()
            if last_trade_date != now_date:
                old_date = last_trade_date or "None"
                last_trade_date = now_date
                trades_today = 0
                bot_state.max_trades_alert_sent = False
                daily_start_balance = fetch_balance(client)
                log(f"NEW DAY → {old_date} → {now_date} | Trades reset | Equity: ${daily_start_balance:.2f}",
                    telegram_bot, telegram_chat_id)

            if trades_today >= max_trades_per_day:
                if not bot_state.max_trades_alert_sent:
                    log(f"Max trades reached ({max_trades_per_day}). No more today.", telegram_bot, telegram_chat_id)
                    bot_state.max_trades_alert_sent = True
                time.sleep(60)
                continue

            if not trading_allowed(client, symbol, telegram_bot, telegram_chat_id):
                time.sleep(1)
                continue

            # === FETCH KLINES & VALIDATE ===
            klines = fetch_klines(client, symbol, timeframe)
            bot_state.is_testnet = True
            is_good, msg = ensure_tv_quality_data(klines, timeframe, is_testnet=bot_state.is_testnet)
            if not is_good:
                log(f"Data quality failed: {msg}. Skipping cycle.", telegram_bot, telegram_chat_id)
                time.sleep(10)
                continue

            latest_close_ms = int(klines[-1][6])

            # === CANDLE DATA ===
            close_price = Decimal(str(klines[-1][4]))
            open_price = Decimal(str(klines[-1][1]))
            curr_vol = Decimal(str(klines[-1][5]))
            is_green_candle = close_price > open_price
            closes, volumes, _, _ = closes_and_volumes_from_klines(klines)
           
            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD) if len(volumes) >= VOL_SMA_PERIOD else None
           
            rsi_str = f"{rsi:.2f}" if rsi else "N/A"
            vol_sma15_str = f"{vol_sma15:.2f}" if vol_sma15 else "N/A"

            # === CANDLE LOG: ONLY WHEN FLAT + NEW CANDLE ===
            if current_state == "FLAT" and latest_close_ms != last_candle_logged_ms:
                log(f"Candle: {close_price:.4f} RSI={rsi_str} Vol={curr_vol:.0f} SMA15={vol_sma15_str} {'Green' if is_green_candle else 'Red'}",
                    telegram_bot, telegram_chat_id)
                last_candle_logged_ms = latest_close_ms

            # === DURING ACTIVE TRADE → STAY SILENT ===
            if current_state == "ACTIVE":
                wait_sec = max(2.0, (latest_close_ms + interval_ms(timeframe) - int(time.time() * 1000)) / 1000.0 + 2)
                _safe_sleep(wait_sec)
                continue

            # === ONLY WHEN FLAT: Check for new candle ===
            if bot_state.last_processed_close_ms is not None and latest_close_ms <= bot_state.last_processed_close_ms:
                wait_sec = max(1.0, (latest_close_ms + interval_ms(timeframe) - int(time.time() * 1000)) / 1000.0 + 2)
                next_dt = datetime.fromtimestamp((latest_close_ms + interval_ms(timeframe)) / 1000, tz=timezone.utc)
                log(f"Waiting for next {timeframe} candle → {next_dt.strftime('%H:%M')} UTC",
                    telegram_bot, telegram_chat_id)
                _safe_sleep(wait_sec)
                continue

            bot_state.last_processed_close_ms = latest_close_ms

            dt = datetime.fromtimestamp(latest_close_ms / 1000, tz=timezone.utc)
            log(f"Aligned to {timeframe} candle close: {dt.strftime('%H:%M')} UTC — Checking signals",
                telegram_bot, telegram_chat_id)

            # ==================== SIGNAL LOGIC ====================
            buy_signal = (rsi and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and
                         (not use_volume_filter or (vol_sma15 and curr_vol > vol_sma15)))
            sell_signal = (rsi and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and not is_green_candle and
                          (not use_volume_filter or (vol_sma15 and curr_vol > vol_sma15)))

            if buy_signal or sell_signal:
                original_side = "BUY" if buy_signal else "SELL"
                insurance_side = "SELL" if buy_signal else "BUY"
               
                log(f"📊 SIGNAL DETECTED → MAIN: {original_side} | INSURANCE: {insurance_side}",
                    telegram_bot, telegram_chat_id)

                # SLIPPAGE CHECK
                slippage_passed, _ = _check_slippage(client, symbol, close_price, telegram_bot, telegram_chat_id)
                if not slippage_passed:
                    continue

                # === MAIN LEG ENTRY ===
                entry_price = close_price
                R_main = entry_price * SL_PCT
                actual_balance = fetch_balance(client)

                main_virtual = actual_balance / Decimal("2")
                main_margin = main_virtual * MARGIN_USAGE_PCT
                main_risk = main_virtual * BASE_RISK_PCT

                qty_raw = main_risk / R_main
                max_by_margin = (main_margin * MAX_LEVERAGE) / entry_price
                qty_main = min(qty_raw, max_by_margin, Decimal("25"))
                qty_main = quantize_qty(qty_main, step_size)

                if (qty_main * entry_price) < min_notional:
                    log("Main leg quantity too small → skipping", telegram_bot, telegram_chat_id)
                    continue

                main_position_side = "LONG" if original_side == "BUY" else "SHORT"
                order_res_main = client.send_signed_request("POST", "/fapi/v1/order", {
                    "symbol": symbol, "side": original_side, "type": "MARKET",
                    "quantity": str(qty_main), "positionSide": main_position_side
                })

                # Wait for main fill
                start_time = time.time()
                actual_qty_main = None
                while not bot_state.STOP_REQUESTED and (time.time() - start_time) < ORDER_FILL_TIMEOUT:
                    pos_amt = get_position_amt_for_side(client, symbol, main_position_side)
                    if pos_amt > Decimal('0.001'):
                        actual_qty_main = pos_amt
                        log(f"✅ Main fill detected! Qty: {actual_qty_main:.5f} SOL", telegram_bot, telegram_chat_id)
                        break
                    time.sleep(1)

                if actual_qty_main is None:
                    try:
                        order_status = client.send_signed_request("GET", "/fapi/v1/order", {
                            "symbol": symbol, "orderId": order_res_main.get("orderId")
                        })
                        if order_status.get("status") == "FILLED":
                            actual_qty_main = Decimal(str(order_status.get("executedQty", "0")))
                            log(f"✅ Main fill detected via order status! Qty: {actual_qty_main:.5f} SOL", telegram_bot, telegram_chat_id)
                    except Exception as e:
                        log(f"Order status check failed: {e}", telegram_bot, telegram_chat_id)

                if actual_qty_main is None or actual_qty_main <= Decimal('0'):
                    log("❌ Main leg fill failed. Aborting trade.", telegram_bot, telegram_chat_id)
                    continue

                actual_fill_price_dec = client.get_latest_fill_price(symbol, order_res_main.get("orderId")) or entry_price

                # === CREATE & ACTIVATE MAIN TRADE STATE ===
                main_trade_state = TradeState()
                main_trade_state.active = True
                main_trade_state.leg_type = "MAIN"
                main_trade_state.entry_price = actual_fill_price_dec
                main_trade_state.qty = actual_qty_main
                main_trade_state.side = "LONG" if original_side == "BUY" else "SHORT"
                main_trade_state.entry_close_time = latest_close_ms
                main_trade_state.risk = actual_fill_price_dec * SL_PCT
                main_trade_state.trail_activated = False

                # Calculate levels
                R_main = actual_fill_price_dec * SL_PCT
                if main_trade_state.side == "LONG":
                    sl_price_dec = actual_fill_price_dec * (Decimal("1") - SL_PCT)
                    tp_price_dec = actual_fill_price_dec + (TP_MULT * R_main)
                    trail_raw = actual_fill_price_dec + (TRAIL_TRIGGER_MULT * R_main)
                    trail_buffered = trail_raw + TRAIL_PRICE_BUFFER
                    trail_activation_quant = quantize_price(trail_buffered, tick_size, ROUND_UP)
                else:
                    sl_price_dec = actual_fill_price_dec * (Decimal("1") + SL_PCT)
                    tp_price_dec = actual_fill_price_dec - (TP_MULT * R_main)
                    trail_raw = actual_fill_price_dec - (TRAIL_TRIGGER_MULT * R_main)
                    trail_buffered = trail_raw - TRAIL_PRICE_BUFFER
                    trail_activation_quant = quantize_price(trail_buffered, tick_size, ROUND_DOWN)

                main_trade_state.sl = quantize_price(sl_price_dec, tick_size, ROUND_DOWN if main_trade_state.side == "LONG" else ROUND_UP)
                main_trade_state.tp = quantize_price(tp_price_dec, tick_size, ROUND_UP if main_trade_state.side == "LONG" else ROUND_DOWN)
                main_trade_state.trail_activation_price = trail_activation_quant

                # Send Telegram & Place orders
                tg_msg_main = f"📈 MAIN LEG ENTRY\n{symbol} {main_trade_state.side}\nEntry: {actual_fill_price_dec:.4f}\nQty: {actual_qty_main:.5f}\nSL: {main_trade_state.sl:.4f}\nTP: {main_trade_state.tp:.4f}"
                telegram_post(telegram_bot, telegram_chat_id, tg_msg_main)

                place_orders(client, symbol, main_trade_state, tick_size, telegram_bot, telegram_chat_id)
                bot_state.current_trade = main_trade_state

                threading.Thread(
                    target=monitor_trade,
                    args=(client, symbol, main_trade_state, tick_size, telegram_bot, telegram_chat_id, latest_close_ms),
                    daemon=True
                ).start()

                                # === INSURANCE LEG ===
                if INSURANCE_ENABLED:
                    log(f"Waiting {INSURANCE_DELAY_MS}ms before insurance entry...", telegram_bot, telegram_chat_id)
                    time.sleep(INSURANCE_DELAY_MS / 1000.0)
                    
                    ins_virtual_equity = actual_balance / 2
                    ins_margin_available = ins_virtual_equity * MARGIN_USAGE_PCT
                    
                    qty_insurance = actual_qty_main
                    max_qty_by_margin_ins = (ins_margin_available * MAX_LEVERAGE) / entry_price
                    if qty_insurance > max_qty_by_margin_ins:
                        qty_insurance = max_qty_by_margin_ins
                    
                    qty_insurance = min(qty_insurance, Decimal("25"))
                    qty_insurance = quantize_qty(qty_insurance * SAFETY_FACTOR, step_size)
                    
                    log(f"INSURANCE: Virtual=${ins_virtual_equity:.2f} | Margin=${ins_margin_available:.2f} | Calculated Qty={qty_insurance:.5f} SOL",
                        telegram_bot, telegram_chat_id)
                    
                    if (qty_insurance * entry_price) < min_notional:
                        log(f"Insurance leg quantity too small → SKIPPING INSURANCE", telegram_bot, telegram_chat_id)
                    else:
                        insurance_side = "SELL" if original_side == "BUY" else "BUY"
                        insurance_position_side = "SHORT" if original_side == "BUY" else "LONG"
                        
                        log(f"[DEBUG] Placing INSURANCE {insurance_side} order | positionSide={insurance_position_side} | qty={qty_insurance:.5f}", 
                            telegram_bot, telegram_chat_id)
                        
                        # Place the order
                        order_res_insurance = client.send_signed_request("POST", "/fapi/v1/order", {
                            "symbol": symbol, 
                            "side": insurance_side, 
                            "type": "MARKET", 
                            "quantity": str(qty_insurance),
                            "positionSide": insurance_position_side
                        })
                        
                        insurance_order_id = order_res_insurance.get("orderId")
                        log(f"[DEBUG] Insurance order placed. orderId={insurance_order_id}", telegram_bot, telegram_chat_id)

                        # === IMPROVED + HEAVY DEBUG FILL DETECTION ===
                        start_time_ins = time.time()
                        actual_qty_insurance = None
                        max_wait = 120  # 2 minutes
                        
                        log(f"[DEBUG] Starting insurance fill detection. Max wait: {max_wait}s | Querying positionSide={insurance_position_side}", 
                            telegram_bot, telegram_chat_id)
                        
                        pos_amt_before = get_position_amt_for_side(client, symbol, insurance_position_side)
                        log(f"[DEBUG] Position before insurance: {pos_amt_before:.5f}", telegram_bot, telegram_chat_id)
                        
                        while not bot_state.STOP_REQUESTED and (time.time() - start_time_ins) < max_wait:
                            pos_amt_now = get_position_amt_for_side(client, symbol, insurance_position_side)
                            delta = pos_amt_now - pos_amt_before
                            
                            log(f"[DEBUG] Check | Now={pos_amt_now:.5f} | Delta={delta:.5f} | Time elapsed={(time.time()-start_time_ins):.1f}s", 
                                telegram_bot, telegram_chat_id)
                            
                            if delta > Decimal('0.0002'):          # Very forgiving threshold
                                actual_qty_insurance = pos_amt_now
                                log(f"✅ Insurance fill detected via position! Qty={actual_qty_insurance:.5f} SOL", 
                                    telegram_bot, telegram_chat_id)
                                break
                            
                            # Extra check via order status
                            if insurance_order_id:
                                try:
                                    order_status = client.send_signed_request("GET", "/fapi/v1/order", {
                                        "symbol": symbol, 
                                        "orderId": insurance_order_id
                                    })
                                    status = order_status.get("status")
                                    executed = Decimal(str(order_status.get("executedQty", "0")))
                                    log(f"[DEBUG] Order status: {status} | Executed Qty={executed:.5f}", telegram_bot, telegram_chat_id)
                                    
                                    if status == "FILLED" and executed > Decimal('0.0001'):
                                        actual_qty_insurance = executed
                                        log(f"✅ Insurance fill confirmed via order status! Qty={actual_qty_insurance:.5f}", 
                                            telegram_bot, telegram_chat_id)
                                        break
                                except Exception as e:
                                    log(f"[DEBUG] Order status check failed: {e}", telegram_bot, telegram_chat_id)
                            
                            time.sleep(1.8)   # Balanced sleep
                        
                        # === FINAL RESULT ===
                        if actual_qty_insurance is None or actual_qty_insurance <= Decimal('0'):
                            log("❌ Insurance leg fill failed after 120s. Continuing with main leg only.", 
                                telegram_bot, telegram_chat_id)
                            log(f"[DEBUG] Final position on {insurance_position_side}: {get_position_amt_for_side(client, symbol, insurance_position_side):.5f}", 
                                telegram_bot, telegram_chat_id)
                        else:
                            # === Create insurance trade state ===
                            insurance_trade_state = TradeState()
                            insurance_trade_state.active = True
                            insurance_trade_state.leg_type = "INSURANCE"
                            insurance_trade_state.side = "LONG" if insurance_side == "BUY" else "SHORT"
                            insurance_trade_state.entry_price = actual_fill_price_dec
                            insurance_trade_state.qty = actual_qty_insurance
                            insurance_trade_state.entry_close_time = latest_close_ms
                            insurance_trade_state.risk = actual_fill_price_dec * SL_PCT
                            insurance_trade_state.trail_activated = False
                            
                            R = actual_fill_price_dec * SL_PCT
                            if original_side == "BUY":
                                sl_price_dec = actual_fill_price_dec + R
                                tp_price_dec = actual_fill_price_dec - (R * Decimal("1.25"))
                                sl_rounding = ROUND_UP
                                tp_rounding = ROUND_DOWN
                            else:
                                sl_price_dec = actual_fill_price_dec - R
                                tp_price_dec = actual_fill_price_dec + (R * Decimal("1.25"))
                                sl_rounding = ROUND_DOWN
                                tp_rounding = ROUND_UP
                            
                            insurance_trade_state.sl = quantize_price(sl_price_dec, tick_size, sl_rounding)
                            insurance_trade_state.tp = quantize_price(tp_price_dec, tick_size, tp_rounding)
                            insurance_trade_state.trail_activation_price = None
                            
                            tg_msg_insurance = (
                                f"🛡️ INSURANCE LEG ENTRY\n"
                                f"━━━━━━━━━━━━━━━━\n"
                                f"{insurance_trade_state.side} {symbol}\n"
                                f"Entry: {actual_fill_price_dec:.4f}\n"
                                f"Qty: {actual_qty_insurance:.5f} SOL\n"
                                f"SL: {insurance_trade_state.sl:.4f} (1R)\n"
                                f"TP: {insurance_trade_state.tp:.4f} (1.25R)\n"
                                f"Virtual Capital: ${ins_virtual_equity:.2f}\n"
                                f"Trailing: DISABLED"
                            )
                            telegram_post(telegram_bot, telegram_chat_id, tg_msg_insurance)
                            
                            place_orders(client, symbol, insurance_trade_state, tick_size, telegram_bot, telegram_chat_id)
                            
                            bot_state.insurance_trade = insurance_trade_state
                            bot_state.INSURANCE_ACTIVE = True
                            
                            threading.Thread(
                                target=monitor_trade,
                                args=(client, symbol, insurance_trade_state, tick_size, 
                                      telegram_bot, telegram_chat_id, latest_close_ms),
                                daemon=True
                            ).start()
                            log(f"✅ Insurance leg monitoring started", telegram_bot, telegram_chat_id)
                
                trades_today += 1
                continue

            else:
                log("No trade signal on candle close.", telegram_bot, telegram_chat_id)

            # === WAIT FOR NEXT CANDLE WHEN FLAT ===
            wait_sec = max(2.0, (latest_close_ms + interval_ms(timeframe) - int(time.time() * 1000)) / 1000.0 + 2)
            _safe_sleep(wait_sec)

        except Exception as e:
            import traceback
            log(f"Trading loop error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(5)

    log("Trading loop exited cleanly.", telegram_bot, telegram_chat_id)

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

import pickle

# ------------------- PERSISTENT STATE MANAGEMENT -------------------
STATE_FILE = 'bot_state.pkl'

def save_bot_state():
    """Save critical bot state to disk"""
    global bot_state
    try:
        persistent_data = {
            'pnl_data': bot_state.pnl_data[-1000:] if hasattr(bot_state, 'pnl_data') else [],
            'last_trade_date': getattr(bot_state, 'last_trade_date', None),
            'CONSEC_LOSSES': getattr(bot_state, 'CONSEC_LOSSES', 0),
            'weekly_peak_equity': getattr(bot_state, 'weekly_peak_equity', None),
            'weekly_start_time': getattr(bot_state, 'weekly_start_time', None),
            'account_size': getattr(bot_state, 'account_size', None),
            'daily_start_equity': getattr(bot_state, 'daily_start_equity', None),
            'INSURANCE_ACTIVE': getattr(bot_state, 'INSURANCE_ACTIVE', False)
        }
        
        # Save insurance trade state if active
        if bot_state.INSURANCE_ACTIVE and bot_state.insurance_trade:
            persistent_data['insurance_trade'] = {
                'active': bot_state.insurance_trade.active,
                'side': bot_state.insurance_trade.side,
                'qty': float(bot_state.insurance_trade.qty) if bot_state.insurance_trade.qty else None,
                'entry_price': float(bot_state.insurance_trade.entry_price) if bot_state.insurance_trade.entry_price else None,
                'sl': float(bot_state.insurance_trade.sl) if bot_state.insurance_trade.sl else None,
                'tp': float(bot_state.insurance_trade.tp) if bot_state.insurance_trade.tp else None,
            }
        
        with open(STATE_FILE, 'wb') as f:
            pickle.dump(persistent_data, f)
        log("💾 Bot state saved to disk", None, None)
    except Exception as e:
        log(f"❌ Failed to save state: {e}", None, None)

def load_bot_state():
    """Load critical bot state from disk"""
    global bot_state
    if not os.path.exists(STATE_FILE):
        log("📂 No saved state found - starting fresh", None, None)
        return
    
    try:
        with open(STATE_FILE, 'rb') as f:
            data = pickle.load(f)
        
        bot_state.pnl_data = data.get('pnl_data', [])
        bot_state.last_trade_date = data.get('last_trade_date')
        bot_state.CONSEC_LOSSES = data.get('CONSEC_LOSSES', 0)
        bot_state.weekly_peak_equity = data.get('weekly_peak_equity')
        bot_state.weekly_start_time = data.get('weekly_start_time')
        bot_state.account_size = data.get('account_size')
        bot_state.daily_start_equity = data.get('daily_start_equity')
        bot_state.INSURANCE_ACTIVE = data.get('INSURANCE_ACTIVE', False)
        
        # Restore insurance trade state if needed
        if bot_state.INSURANCE_ACTIVE and 'insurance_trade' in data:
            ins_data = data['insurance_trade']
            trade_state = TradeState()
            trade_state.active = ins_data.get('active', False)
            trade_state.leg_type = "INSURANCE"
            trade_state.side = ins_data.get('side')
            trade_state.qty = Decimal(str(ins_data['qty'])) if ins_data.get('qty') else None
            trade_state.entry_price = Decimal(str(ins_data['entry_price'])) if ins_data.get('entry_price') else None
            trade_state.sl = Decimal(str(ins_data['sl'])) if ins_data.get('sl') else None
            trade_state.tp = Decimal(str(ins_data['tp'])) if ins_data.get('tp') else None
            bot_state.insurance_trade = trade_state
        
        log(f"💾 Bot state loaded - {len(bot_state.pnl_data)} trades restored", None, None)
    except Exception as e:
        log(f"❌ Failed to load state: {e}", None, None)
        
def run_scheduler(bot: Optional[str], chat_id: Optional[str]):
    global bot_state
    last_month: Optional[int] = None
    
    def daily_reset_job():
        """Handles equity reset and logging at 00:00 UTC."""
        try:
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
            
    def daily_restart_job():
        """Safe daily restart - preserves positions, really restarts process"""
        global bot_state
        
        has_position = False
        position_details = ""
        if (bot_state.client and bot_state.current_trade and 
            bot_state.current_trade.active and bot_state.current_trade.qty):
            has_position = True
            position_details = (f"MAIN: {bot_state.current_trade.side} "
                               f"{bot_state.current_trade.qty} SOL "
                               f"@ {bot_state.current_trade.entry_price:.2f}")
        
        if bot_state.INSURANCE_ACTIVE and bot_state.insurance_trade and bot_state.insurance_trade.qty:
            has_position = True
            position_details += (f" | INSURANCE: {bot_state.insurance_trade.side} "
                                f"{bot_state.insurance_trade.qty} SOL "
                                f"@ {bot_state.insurance_trade.entry_price:.2f}")
        
        log("🔄 DAILY RESTART: Starting real process restart...", bot, chat_id)
        
        try:
            save_bot_state()
            log("💾 State saved - trades preserved", bot, chat_id)
        except Exception as e:
            log(f"⚠️ State save warning: {e}", bot, chat_id)
        
        if has_position:
            msg = (f"🔄 Daily restart - POSITIONS PRESERVED!\n"
                   f"{position_details}\n"
                   f"SL/TP orders remain active on Binance")
            telegram_post(bot, chat_id, msg)
            log(f"✅ Active positions preserved: {position_details}", bot, chat_id)
        else:
            telegram_post(bot, chat_id, "🔄 Daily restart - no active positions")
        
        time.sleep(2)
        
        log("🚀 Restarting Python process NOW - positions safe on Binance", bot, chat_id)
        import os, sys
        os.execv(sys.executable, [sys.executable] + sys.argv)
        
    # Schedule all tasks
    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot, chat_id))
    schedule.every().day.at("00:00").do(daily_reset_job)
    schedule.every().day.at("00:01").do(lambda: daily_memory_log(bot, chat_id))
    schedule.every().day.at("00:02").do(daily_restart_job)
    schedule.every().monday.at("00:00").do(weekly_reset_job)
    schedule.every().day.at("00:00").do(check_monthly_report)
    
    log("Scheduler Initialized: Daily/Weekly resets and reporting active.", bot, chat_id)

    while not bot_state.STOP_REQUESTED:
        schedule.run_pending()
        time.sleep(1)

# ==================== TELEGRAM COMMAND HANDLERS ====================
async def cmd_restart(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Telegram /restart - safely restarts bot, preserves positions"""
    global bot_state, args, LOCK_HANDLE
    
    chat_id = str(update.effective_chat.id)
    
    if chat_id != str(args.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    has_position = False
    position_details = ""
    if (bot_state.client and bot_state.current_trade and 
        bot_state.current_trade.active and bot_state.current_trade.qty):
        has_position = True
        position_details = (f"MAIN: {bot_state.current_trade.side} "
                           f"{bot_state.current_trade.qty} SOL "
                           f"@ {bot_state.current_trade.entry_price:.2f}")
    
    if bot_state.INSURANCE_ACTIVE and bot_state.insurance_trade and bot_state.insurance_trade.qty:
        has_position = True
        position_details += (f"\nINSURANCE: {bot_state.insurance_trade.side} "
                            f"{bot_state.insurance_trade.qty} SOL "
                            f"@ {bot_state.insurance_trade.entry_price:.2f}")
    
    if has_position:
        await update.message.reply_text(
            f"🔄 *Restarting with ACTIVE POSITIONS*\n\n"
            f"📊 *Positions:*\n{position_details}\n\n"
            f"🛡️ *SL/TP orders stay on Binance*\n"
            f"🤖 Bot will resume monitoring after restart\n\n"
            f"Restarting in 2 seconds...",
            parse_mode='Markdown'
        )
    else:
        await update.message.reply_text("🔄 Restarting bot now...")
    
    try:
        save_bot_state()
        await update.message.reply_text("💾 Trade history saved")
    except:
        await update.message.reply_text("⚠️ Save warning - restarting anyway")
    
    log("🔧 Manual restart via Telegram", args.telegram_token, args.chat_id)
    
    await asyncio.sleep(2)
    
    try:
        if LOCK_HANDLE:
            LOCK_HANDLE.close()
            print("Lock handle closed successfully for restart")
    except Exception as e:
        print(f"Error closing lock handle during restart: {e}")
    
    time.sleep(1)
    
    log("🚀 Executing manual restart now (One-Way mode will be forced)", 
        args.telegram_token, args.chat_id)
    import os, sys
    os.execv(sys.executable, [sys.executable] + sys.argv)

async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Command: /status — quick bot health check"""
    global bot_state, args
    
    chat_id = str(update.effective_chat.id)
    
    if chat_id != str(args.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    balance = fetch_balance(bot_state.client) if bot_state.client else Decimal("0")
    # Get net position amount for display
    pos_amt = get_position_amt(bot_state.client, args.symbol, args.telegram_token, args.chat_id) if bot_state.client else Decimal("0")
    
    import psutil
    process = psutil.Process()
    mem_mb = process.memory_info().rss / 1024 / 1024
    
    main_status = "No active trade"
    if bot_state.current_trade and bot_state.current_trade.active:
        main_status = f"{bot_state.current_trade.side} @ {bot_state.current_trade.entry_price:.2f} | Qty: {bot_state.current_trade.qty:.4f}"
    
    insurance_status = "Not active"
    if bot_state.INSURANCE_ACTIVE and bot_state.insurance_trade and bot_state.insurance_trade.active:
        insurance_status = f"{bot_state.insurance_trade.side} @ {bot_state.insurance_trade.entry_price:.2f} | Qty: {bot_state.insurance_trade.qty:.4f}"
    
    status_lines = [
        f"🤖 *Edison Bot Status*",
        f"",
        f"📊 *Balance:* `${float(balance):.2f}`",
        f"📈 *Net Position:* `{float(pos_amt):.2f} SOL`",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"📌 *MAIN Leg:* `{main_status}`",
        f"🛡️ *INSURANCE Leg:* `{insurance_status}`",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"💾 *Trades Stored:* `{len(bot_state.pnl_data)}`",
        f"🧠 *Memory:* `{mem_mb:.1f} MB`",
        f"🆔 *PID:* `{os.getpid()}`",
        f"⏰ *Uptime:* `{datetime.now(timezone.utc) - bot_state.start_time}`" if hasattr(bot_state, 'start_time') else ""
    ]
    
    await update.message.reply_text("\n".join(status_lines), parse_mode='Markdown')

async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Command: /help — show available commands"""
    chat_id = str(update.effective_chat.id)
    
    if chat_id != str(args.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    help_text = (
        "🤖 *Available Commands:*\n\n"
        "/status - Show bot status (balance, positions, memory)\n"
        "/restart - Gracefully restart the bot (preserves positions)\n"
        "/help - Show this help message\n\n"
        f"*Insurance Mode:* {'ENABLED' if INSURANCE_ENABLED else 'DISABLED'} (Full Hedge)\n"
        f"*Virtual Split:* MAIN ${MAIN_VIRTUAL_CAPITAL} | INSURANCE ${INSURANCE_VIRTUAL_CAPITAL}\n"
        f"*Margin Usage:* {MARGIN_USAGE_PCT*100:.0f}% of virtual capital\n"
        f"*Main Risk:* {BASE_RISK_PCT*100:.1f}% | *Safety Factor:* {SAFETY_FACTOR*100:.0f}%"
    )
    await update.message.reply_text(help_text, parse_mode='Markdown')

async def unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = str(update.effective_chat.id)
    if chat_id != str(args.chat_id):
        return
    if update.message and update.message.text and update.message.text.startswith('/'):
        await update.message.reply_text("❓ Unknown command. Try /help")
         
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Merged Main + Insurance)")
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
    parser.add_argument("--disable-insurance", action="store_true", help="Disable insurance leg (opposite direction)")
    args = parser.parse_args()
    
    # Override INSURANCE_ENABLED if command line flag is used
    if args.disable_insurance:
        INSURANCE_ENABLED = False
        print("[CONFIG] Insurance leg DISABLED via --disable-insurance")
    
    LOCK_HANDLE = acquire_lock()
    
    if args.no_news_guard:
        NEWS_GUARD_ENABLED = False
        print("[CONFIG] News Guard FULLY DISABLED via --no-news-guard")
    else:
        NEWS_GUARD_ENABLED = True
    
    init_pnl_log()
    
    # ======================== LOAD SAVED STATE ========================
    load_bot_state()
    # ===== TEMPORARY: RESET WEEKLY DD GUARD =====
    bot_state.weekly_start_time = None
    bot_state.weekly_peak_equity = None
    bot_state.weekly_dd_alert_triggered = False
    log("⚠️ WEEKLY DRAWDOWN GUARD RESET - TRADING ENABLED", args.telegram_token, args.chat_id)
# ===========================================
        # ======================== SINGLE, BULLETPROOF SHUTDOWN ========================
    _shutdown_done = False
    
    def graceful_shutdown(sig: Optional[int] = None, frame: Any = None, 
                          symbol: Optional[str] = None, 
                          telegram_bot: Optional[str] = None, 
                          telegram_chat_id: Optional[str] = None):
        global _shutdown_done, bot_state, args, LOCK_HANDLE
        
        symbol = symbol or getattr(args, 'symbol', None)
        telegram_bot = telegram_bot or getattr(args, 'telegram_token', None)
        telegram_chat_id = telegram_chat_id or getattr(args, 'chat_id', None)
        
        if _shutdown_done:
            return
        _shutdown_done = True

        reason = {
            signal.SIGINT: "Ctrl+C",
            signal.SIGTERM: "SIGTERM / systemd",
        }.get(sig, "Clean exit")
        
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            reason = "KILL FLAG / Manual stop"

        log(f"🛑 Shutdown requested ({reason}). Starting clean closure...", telegram_bot, telegram_chat_id)
        
        # Save state first
        try:
            save_bot_state()
        except Exception as e:
            log(f"Warning: Failed to save state: {e}", telegram_bot, telegram_chat_id)

        # === CRITICAL: Actually close positions using _request_stop ===
        if bot_state.client and symbol:
            log("Calling _request_stop to close positions...", telegram_bot, telegram_chat_id)
            try:
                _request_stop(
                    symbol=symbol,
                    telegram_bot=telegram_bot,
                    telegram_chat_id=telegram_chat_id
                )
            except Exception as e:
                log(f"Error during _request_stop: {e}", telegram_bot, telegram_chat_id)
        else:
            log("No client or symbol available — skipping position closure", telegram_bot, telegram_chat_id)

        # Final order cleanup (just in case)
        try:
            if bot_state.client and symbol:
                bot_state.client.cancel_all_open_orders(symbol)
                log(f"All open orders cancelled for {symbol}.", telegram_bot, telegram_chat_id)
        except Exception as e:
            log(f"Final order cleanup failed: {e}", telegram_bot, telegram_chat_id)

        # Clear states
        bot_state.current_trade = None
        bot_state.insurance_trade = None
        bot_state.INSURANCE_ACTIVE = False

        goodbye = (
            f"✅ RSI BOT STOPPED CLEANLY\n"
            f"Symbol: {symbol}\n"
            f"Timeframe: {getattr(args, 'timeframe', 'N/A')}\n"
            f"Reason: {reason}\n"
            f"Time: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
            f"Insurance Mode: {'ENABLED' if INSURANCE_ENABLED else 'DISABLED'}\n"
            f"Positions: Closed successfully"
        )

        try:
            log(goodbye, telegram_bot, telegram_chat_id)
        except Exception as e:
            print(f"Error sending goodbye message: {e}")

        # Clean up lock file
        if sig is not None:
            try:
                if LOCK_HANDLE:
                    LOCK_HANDLE.close()
                if os.path.exists(LOCK_FILE):
                    os.unlink(LOCK_FILE)
                    log(f"Lock file removed: {LOCK_FILE}", telegram_bot, telegram_chat_id)
            except Exception as e:
                print(f"Error cleaning lock file: {e}")

        # Remove kill flag if exists
        try:
            if os.path.exists("/tmp/STOP_BOT_NOW"):
                os.unlink("/tmp/STOP_BOT_NOW")
        except:
            pass

        log("Bot shutdown completed. Exiting.", telegram_bot, telegram_chat_id)
        os._exit(0)
        
    def signal_handler_wrapper(sig, frame):
        graceful_shutdown(sig, frame, args.symbol, args.telegram_token, args.chat_id)
    
    # Register signals and atexit
    signal.signal(signal.SIGINT, signal_handler_wrapper)
    signal.signal(signal.SIGTERM, signal_handler_wrapper)
    atexit.register(lambda: graceful_shutdown(None, None, args.symbol, args.telegram_token, args.chat_id))
    
    # ======================== IMMORTAL BOT LOOP ========================
    while True:
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            log("STOP_BOT_NOW flag detected – shutting down permanently", args.telegram_token, args.chat_id)
            graceful_shutdown(None, None, args.symbol, args.telegram_token, args.chat_id)
            break
        
        try:
            bot_state.client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
            
            # Force Hedge Mode
            try:
                bot_state.client.send_signed_request("POST", "/fapi/v1/positionSide/dual", {"dualSidePosition": "true"})
                log("✅ Hedge Mode enabled for dual legs", args.telegram_token, args.chat_id)
            except Exception as e:
                log(f"⚠️ Could not set Hedge Mode (might already be active): {e}", args.telegram_token, args.chat_id)
            
            balance = fetch_balance(bot_state.client)
            bot_state.account_size = balance
            bot_state.daily_start_equity = balance
          
            leverage_to_set = 9
            bot_state.client.set_leverage(args.symbol, leverage_to_set)
            log(f"Set Binance leverage to {leverage_to_set}x for {args.symbol}", args.telegram_token, args.chat_id)
            
            risk_pct_display = Decimal(str(args.risk_pct))
            log(f"Simple Weekly DD Guard: 20% hard stop", args.telegram_token, args.chat_id)
            log(f"Consecutive Loss Guard: 3 losses ≥0.5R stop", args.telegram_token, args.chat_id)
            log(f"Base Risk (MAIN): {BASE_RISK_PCT*Decimal('100'):.2f}% per trade", args.telegram_token, args.chat_id)
            if INSURANCE_ENABLED:
                log(f"Safety Factor: {SAFETY_FACTOR*100:.0f}% applied to both legs", args.telegram_token, args.chat_id)
            log(f"Fetched balance: ${balance:.2f} USDT", args.telegram_token, args.chat_id)
            
            if NEWS_GUARD_ENABLED:
                threading.Thread(target=news_heartbeat, daemon=True).start()
                log("Economic calendar monitoring: ENABLED", args.telegram_token, args.chat_id)
            else:
                log("Economic calendar monitoring: DISABLED (--no-news-guard)", args.telegram_token, args.chat_id)
            
            log(f"STARTING BOT → {args.symbol} | {args.timeframe} | "
                f"Risk: {risk_pct_display:.3f}% | "
                f"Volume Filter: {'ON' if args.use_volume_filter else 'OFF'} | "
                f"Mode: {'LIVE' if args.live else 'TESTNET'} | "
                f"Insurance: {'ENABLED' if INSURANCE_ENABLED else 'DISABLED'}",
                args.telegram_token, args.chat_id)
            
            # ========== POSITION RECOVERY ==========
            filters = get_symbol_filters(bot_state.client, args.symbol)
            tick_size = filters['tickSize']
            
            recover_existing_positions(bot_state.client, args.symbol, tick_size, 
                                      args.telegram_token, args.chat_id)
            
            # ========== MEMORY USAGE ON STARTUP ==========
            import psutil
            mem_mb = psutil.Process().memory_info().rss / 1024 / 1024
            log(f"🧠 Fresh process memory: {mem_mb:.1f} MB", args.telegram_token, args.chat_id)
            log(f"🚀 Bot started - PID: {os.getpid()}", args.telegram_token, args.chat_id)
            
            # Start scheduler in background thread
            threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()
            
            # ========== START TRADING LOOP IN BACKGROUND THREAD ==========
            trading_thread = threading.Thread(
                target=trading_loop,
                args=(
                    bot_state.client,
                    args.symbol,
                    args.timeframe,
                    args.max_trades,
                    Decimal(str(args.risk_pct)) / Decimal("100"),
                    Decimal(str(args.max_loss_pct)),
                    Decimal(str(args.tp_mult)),
                    args.use_trailing,
                    args.prevent_same_bar,
                    args.require_no_pos,
                    args.use_max_loss,
                    args.use_volume_filter,
                    args.telegram_token,
                    args.chat_id
                ),
                daemon=True,
                name="TradingLoop"
            )
            trading_thread.start()
            log("🚀 Trading loop started in background thread", args.telegram_token, args.chat_id)
            
            # ========== TELEGRAM LISTENER - RUNNING IN MAIN THREAD ==========
            if args.telegram_token and args.chat_id:
                try:
                    requests.post(
                        f"https://api.telegram.org/bot{args.telegram_token}/deleteWebhook",
                        timeout=5
                    )
                    log("Cleaned up any old Telegram webhook/polling sessions",
                        args.telegram_token, args.chat_id)
                    time.sleep(2)
                except Exception as e:
                    log(f"Cleanup old Telegram sessions failed (usually harmless): {e}",
                        args.telegram_token, args.chat_id)

                from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes
                from telegram import Update
                
                application = Application.builder().token(args.telegram_token).build()

                application.add_handler(CommandHandler("restart", cmd_restart))
                application.add_handler(CommandHandler("status", cmd_status))
                application.add_handler(CommandHandler("help", cmd_help))
                application.add_handler(MessageHandler(filters.COMMAND, unknown))

                log("📱 Telegram command listener starting in main thread (/restart, /status, /help)",
                    args.telegram_token, args.chat_id)

                try:
                    application.run_polling(
                        drop_pending_updates=True,
                        stop_signals=None,
                        allowed_updates=Update.ALL_TYPES
                    )
                except Exception as e:
                    log(f"Telegram polling stopped: {e}", args.telegram_token, args.chat_id)
            
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
