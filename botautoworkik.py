# Binance Futures RSI Bot (Binance-Handled Trailing Stop, 30m Optimized, SOLUSDT)
# FINAL PRODUCTION VERSION — ALL CRITICAL & HIGH-SEVERITY FIXES APPLIED

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

# Add to global variables section if missing:
daily_start_equity = None
account_size = None

# ------------------- CONFIGURATION -------------------
RISK_PCT = Decimal("0.068")  # 6.8% per trade
SL_PCT = Decimal("0.0075")  # 0.75%
TP_MULT = Decimal("9")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2")  # 2.5R trailing distance
VOL_SMA_PERIOD = 16
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 1
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 55
BUY_RSI_MAX = 65
SELL_RSI_MIN = 35
SELL_RSI_MAX = 45
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
MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")
BASE_RISK_PCT = Decimal("0.068")        # 2.25% when drawdown = 0%
MAX_LEVERAGE = Decimal("9")
# === CONFIG: WEEKLY SCALING QUICK TOGGLE ===
ENABLE_WEEKLY_SCALING = True      # ← Set to False to disable scaling completely

# ------------------- GLOBAL STATE -------------------
STOP_REQUESTED = False
client = None
symbol_filters_cache = {}
klines_cache = None
klines_cache_time = 0
last_rate_limit_check = 0
PNL_LOG_FILE = 'pnl_log.csv'
PNL_FIELDS = ['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r', 'loss_streak']
pnl_data = []
pnl_lock = threading.Lock()  # FIXED: Lock for thread-safe PNL writing
last_trade_date = None
last_exit_candle_time = None
socket.setdefaulttimeout(10)
# ENHANCED: Thread-safe stop & order cancellation
_stop_lock = threading.Lock()
_orders_cancelled = False

# ENHANCED: WebSocket → Polling fallback state
_ws_failed = False
_polling_active = False
_price_queue = queue.Queue(maxsize=1000)  # FIXED: Limit queue size to prevent memory growth

# News guard state
NEWS_GUARD_ENABLED = True
_news_lock = threading.Lock()
_news_cache: List[Dict[str, Any]] = []
_cache_ts = 0.0
NEWS_LOCK = False          # <--- blocks entry + forces emergency close
VOLATILITY_ABORT = False   # set by ATR spike check (see trading loop)

last_news_guard_msg: Optional[str] = None
news_guard_was_active: bool = False
_last_news_block_reason: Optional[str] = None
weekly_peak_equity = None
weekly_start_time = None

# Consecutive losses tracking
CONSEC_LOSSES = 0
USE_CONSEC_LOSS_GUARD = True
MAX_CONSEC_LOSSES = 3
weekly_dd_alert_triggered = False
LOCK_HANDLE = None

class BotState:
    def __init__(self):
        self.consec_loss_guard_alert_sent = False
        self.last_processed_close_ms = None
        self.last_candle_state = None
        self.current_risk_pct = Decimal("1.0")

bot_state = BotState()

# ------------------- TRADE STATE (FIXED: Use Decimal for all numeric fields) -------------------
class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price: Optional[Decimal] = None  # FIXED: Use Decimal
        self.qty: Optional[Decimal] = None  # FIXED: Use Decimal
        self.side: Optional[str] = None
        self.entry_close_time = None
        self.initial_sl: Optional[Decimal] = None  # FIXED: Use Decimal
        self.sl: Optional[Decimal] = None  # FIXED: Use Decimal
        self.tp: Optional[Decimal] = None  # FIXED: Use Decimal
        self.trail_activation_price: Optional[Decimal] = None  # FIXED: Use Decimal
        self.highest_price: Optional[Decimal] = None  # FIXED: Use Decimal
        self.lowest_price: Optional[Decimal] = None  # FIXED: Use Decimal
        self.current_trail_stop: Optional[Decimal] = None  # FIXED: Use Decimal
        self.trail_activated = False
        self.last_trail_alert = 0.0
        self.risk: Optional[Decimal] = None  # FIXED: Use Decimal
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_order_id = None
        self.sl_algo_id = None
        self.tp_algo_id = None
        self.trail_algo_id = None

# ------------------- PNL LOGGING (FIXED: Thread-safe with lock) -------------------
def init_pnl_log():
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
            writer.writeheader()

def log_pnl(trade_id, side, entry, exit_price, qty, R):
    global CONSEC_LOSSES
    
    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty
    
    # FIXED: Safe division
    total_risk = qty * R
    if total_risk > 0:
        pnl_r = pnl_usd / total_risk
    else:
        pnl_r = Decimal("0")
    
    # === CONSECUTIVE LOSS TRACKING ===
    denom = (entry * qty) if entry and qty else Decimal("1")
    loss_pct = abs(pnl_usd) / denom if pnl_usd < 0 else Decimal("0")
    is_full_loss = loss_pct >= Decimal("0.0074")  # ~0.75% loss (1R)
    
    if pnl_usd < 0 and is_full_loss:
        CONSEC_LOSSES += 1
    else:
        CONSEC_LOSSES = 0  # Any profit or partial loss resets streak
    
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': float(entry),
        'exit': float(exit_price),
        'pnl_usd': float(pnl_usd),
        'pnl_r': float(pnl_r),
        'loss_streak': CONSEC_LOSSES
    }
    
    # FIXED: Thread-safe file writing
    with pnl_lock:
        pnl_data.append(row)
        with open(PNL_LOG_FILE, 'a', newline='') as f:
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

# ------------------- TELEGRAM MESSAGES (missing ones) -------------------
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
    
    with pnl_lock:
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

# ------------------- SCHEDULER -------------------
def run_scheduler(bot, chat_id):
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

    while True:
        schedule.run_pending()
        time.sleep(60)

# ==================== 45m AGGREGATION FUNCTION ====================
def aggregate_klines_to_45m(klines_15m):
    if len(klines_15m) < 3:
        return []

    aggregated = []
    EXPECTED = 45 * 60 * 1000
    TOLERANCE = 5000  # 5-second tolerance

    # Work backwards from the newest candle
    for i in range(len(klines_15m) - 1, 1, -1):
        close_time = int(klines_15m[i][6])
        open_time_expected = close_time - EXPECTED

        # Find the oldest candle that matches the expected 45m window
        for j in range(i - 2, -1, -1):
            if abs(int(klines_15m[j][0]) - open_time_expected) <= TOLERANCE:
                chunk = klines_15m[j:j+3]
                if len(chunk) == 3:
                    a, b, c = chunk
                    high = max(float(a[2]), float(b[2]), float(c[2]))
                    low  = min(float(a[3]), float(b[3]), float(c[3]))
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
        if len(aggregated) >= 500:
            break

    aggregated.reverse()
    return aggregated

# ==================== FETCH KLINES WITH AGGREGATION ====================
def fetch_klines(client, symbol, interval, limit=max(500, VOL_SMA_PERIOD * 3)):
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

        if requested == "45m":
            raw = aggregate_klines_to_45m(raw)

        return raw

    except Exception as e:
        log(f"Klines fetch failed: {e}", None, None)
        return []
# ------------------- RISK MANAGEMENT (FIXED) -------------------
def check_weekly_dd(current_equity: Decimal, telegram_bot=None, telegram_chat_id=None) -> bool:
    """
    Check weekly drawdown without side effects.
    Returns True if trading is allowed (DD < 20%), False if DD >= 20%.
    """
    global weekly_peak_equity, weekly_start_time, weekly_dd_alert_triggered

    now = datetime.now(timezone.utc)
    current_monday = now - timedelta(days=now.weekday())
    current_monday = current_monday.replace(hour=0, minute=0, second=0, microsecond=0)

    # === NEW WEEK DETECTED → RESET ===
    if weekly_start_time is None or now >= current_monday + timedelta(weeks=1):
        weekly_start_time = current_monday
        weekly_peak_equity = current_equity
        weekly_dd_alert_triggered = False
        if telegram_bot and telegram_chat_id:
            log(f"NEW WEEK -> Weekly peak reset to ${float(current_equity):.2f}", telegram_bot, telegram_chat_id)

    # === UPDATE PEAK IF HIGHER ===
    if weekly_peak_equity is None or current_equity > weekly_peak_equity:
        weekly_peak_equity = current_equity

    # === CHECK 20% DD LIMIT ===
    if weekly_peak_equity <= 0:
        return False

    weekly_dd = (weekly_peak_equity - current_equity) / weekly_peak_equity

    if weekly_dd >= Decimal("0.20"):
        if not weekly_dd_alert_triggered:
            msg = f"🚨 WEEKLY 20% DD REACHED! Trading paused (DD: {weekly_dd:.2%})"
            log(msg, telegram_bot, telegram_chat_id)
            weekly_dd_alert_triggered = True
        return False
    else:
        # Reset alert when recovered
        if weekly_dd_alert_triggered:
            weekly_dd_alert_triggered = False
            log("Weekly DD recovered – trading resumed.", telegram_bot, telegram_chat_id)
        return True

def emergency_close_on_dd(client, symbol, telegram_bot=None, telegram_chat_id=None):
    """
    Emergency close positions if weekly DD >= 20%.
    Separate function from DD check to avoid side effects.
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
            return
        
        # Find position for symbol
        pos_item = None
        for item in positions:
            if isinstance(item, dict) and item.get("symbol") == symbol:
                pos_item = item
                break
        
        if pos_item is None:
            return
        
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0")))
        
        if pos_amt != 0:
            side = "SELL" if pos_amt > 0 else "BUY"
            qty = abs(pos_amt)
            # FIXED: Add reduceOnly to prevent accidental position opening
            client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": str(qty),
                "reduceOnly": "true"  # FIXED: Ensure reduce-only
            })
            log(f"EMERGENCY CLOSE: Position closed (qty={qty} {side}) due to weekly DD >= 20%", telegram_bot, telegram_chat_id)
            
    except Exception as e:
        log(f"Emergency close failed: {str(e)}", telegram_bot, telegram_chat_id)

def get_current_risk_pct(
    current_equity: Decimal,
    client,              # BinanceClient instance
    symbol: str = "SOLUSDT",
    telegram_bot=None,
    telegram_chat_id=None
) -> Decimal:
    """
    Get current risk percentage (0 or 1).
    Now calls emergency close separately if needed.
    """
    # First check if we need to emergency close
    if not check_weekly_dd(current_equity, telegram_bot, telegram_chat_id):
        emergency_close_on_dd(client, symbol, telegram_bot, telegram_chat_id)
        return Decimal("0")
    
    # Check consecutive losses
    if USE_CONSEC_LOSS_GUARD and CONSEC_LOSSES >= MAX_CONSEC_LOSSES:
        if not bot_state.consec_loss_guard_alert_sent:
            log(f"CONSECUTIVE FULL LOSSES REACHED ({CONSEC_LOSSES}) — TRADING PAUSED UNTIL NEXT WEEK OR WIN", telegram_bot, telegram_chat_id)
            bot_state.consec_loss_guard_alert_sent = True
        return Decimal("0")
    
    return Decimal("1")

# ==================== SINGLE INSTANCE LOCK (WITH PID CHECK) ====================
def acquire_lock():
    """Acquire lock with PID check to prevent stale locks."""
    global LOCK_HANDLE
    LOCK_FILE = os.path.join(os.getenv('TEMP', '/tmp'), 'sol_rsi_bot.lock')
    
    # Check if lock file exists and contains a valid PID
    if os.path.exists(LOCK_FILE):
        try:
            with open(LOCK_FILE, 'r') as f:
                pid_str = f.read().strip()
                if pid_str.isdigit():
                    pid = int(pid_str)
                    # Check if process is still running
                    try:
                        os.kill(pid, 0)  # Does nothing if process exists
                        print("Another instance is already running! Exiting.")
                        sys.exit(1)
                    except OSError:
                        # Process doesn't exist, remove stale lock
                        os.unlink(LOCK_FILE)
        except Exception:
            pass  # If we can't read, try to create new lock
    
    try:
        # Create lock file with current PID
        LOCK_HANDLE = open(LOCK_FILE, 'w')
        LOCK_HANDLE.write(str(os.getpid()))
        LOCK_HANDLE.flush()
        
        # Optional real lock on Linux only
        if platform.system() != "Windows":
            try:
                import fcntl
                fcntl.lockf(LOCK_HANDLE.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except Exception:
                print("Another instance is already running! Exiting.")
                sys.exit(1)
                
    except FileExistsError:
        print("Another instance is already running! Exiting.")
        sys.exit(1)
    except Exception as e:
        print(f"Lock error: {e}")
        sys.exit(1)

# ==================== MEMORY LIMIT (Linux / OCI only) ====================
if platform.system() != "Windows":
    try:
        import resource
        SOFT = HARD = 680 * 1024 * 1024   # ~680 MB
        resource.setrlimit(resource.RLIMIT_AS, (SOFT, HARD))
        print(f"[Startup] Memory limit set to ~680 MB")
    except Exception as e:
        print(f"[Startup] Could not set memory limit: {e}")
else:
    print("[Startup] Windows detected – skipping Unix-only features (normal for local testing)")

# ------------------- SERVER TIME -------------------
def get_server_time(client):  
    try:  
        resp = client.public_request("/fapi/v1/time")  
        return int(resp['serverTime'])  
    except Exception as e:  
        log(f"Server time fetch failed: {e}")  
        return int(time.time() * 1000)  # Fallback to local

# ------------------- STOP HANDLER (FIXED: Clean shutdown flow) -------------------
def _request_stop(signum=None, frame=None, symbol=None, telegram_bot=None, telegram_chat_id=None):
    global STOP_REQUESTED, client, _orders_cancelled
    with _stop_lock:
        if STOP_REQUESTED:
            logger.info("Stop already requested; skipping duplicate cleanup.")
            return
        STOP_REQUESTED = True

    log("Stop requested. Closing positions and cancelling orders...", telegram_bot, telegram_chat_id)
    if not client or not symbol:
        log("Client or symbol not defined; skipping position closure and order cancellation.", telegram_bot, telegram_chat_id)
        return

    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')

        if pos_amt != 0:
            side = "SELL" if pos_amt > 0 else "BUY"
            qty = abs(pos_amt)
            entry_price_dec = Decimal(str(pos_item.get("entryPrice", "0"))) if pos_item else Decimal('0')

            # FIXED: Add reduceOnly to prevent accidental position opening
            response = client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": str(qty),
                "reduceOnly": "true"  # FIXED: Ensure reduce-only
            })
            market_order_id = response.get("orderId")
            log(f"Closed position: qty={qty} {side} (orderId: {market_order_id})", telegram_bot, telegram_chat_id)

            # === Get EXACT fill price from userTrades (not ticker fallback) ===
            exit_price_dec = None
            if market_order_id:
                time.sleep(0.8)  # Allow fill propagation
                try:
                    trades = client.send_signed_request("GET", "/fapi/v1/userTrades", {
                        "symbol": symbol,
                        "orderId": market_order_id,
                        "limit": 10
                    })
                    filled_trades = [t for t in trades if Decimal(str(t.get("qty", "0"))) > 0]
                    if filled_trades:
                        # Use last fill (most accurate)
                        exit_price_dec = Decimal(str(filled_trades[-1]["price"]))
                except Exception as e:
                    log(f"Failed to fetch exact fill from userTrades: {e}", telegram_bot, telegram_chat_id)

            if exit_price_dec is None:
                log("⚠️ Exact fill price unavailable. Using ticker as last resort.", telegram_bot, telegram_chat_id)
                try:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price_dec = Decimal(str(ticker.get("price", "0")))
                except Exception as e:
                    log(f"Ticker fallback failed: {e}", telegram_bot, telegram_chat_id)
                    exit_price_dec = Decimal("0")

            exit_price_f = float(exit_price_dec)
            entry_price_f = float(entry_price_dec)
            R_decimal = entry_price_dec * SL_PCT  # FIXED: Keep as Decimal

            # Log PNL
            pnl_row = log_pnl(
                len(pnl_data) + 1,
                "LONG" if pos_amt > 0 else "SHORT",
                entry_price_dec,
                exit_price_dec,
                qty,
                R_decimal  # FIXED: Pass Decimal, not float
            )

            # Telegram
            if telegram_bot and telegram_chat_id:
                send_closure_telegram(
                    symbol=symbol,
                    side="LONG" if pos_amt > 0 else "SHORT",
                    entry_price=entry_price_f,
                    exit_price=exit_price_f,
                    qty=float(qty),
                    pnl_usd=pnl_row['pnl_usd'],
                    pnl_r=pnl_row['pnl_r'],
                    reason="Stop Requested",
                    bot=telegram_bot,
                    chat_id=telegram_chat_id
                )

    except Exception as e:
        log(f"Stop handler error while closing position: {str(e)}", telegram_bot, telegram_chat_id)

    # Final cleanup with retry logic
    with _stop_lock:
        if not _orders_cancelled:
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    client.cancel_all_open_orders(symbol)
                    log(f"All open orders cancelled for {symbol}.", telegram_bot, telegram_chat_id)
                    break
                except Exception as e:
                    if attempt < max_retries - 1:
                        wait = (2 ** attempt) * 2
                        log(f"Failed to cancel open orders (attempt {attempt+1}/{max_retries}): {e}. Retrying in {wait}s...", telegram_bot, telegram_chat_id)
                        time.sleep(wait)
                    else:
                        log(f"Failed to cancel open orders after {max_retries} attempts: {e}", telegram_bot, telegram_chat_id)
            _orders_cancelled = True

# ------------------- TIME SYNC -------------------
def get_time_sync_latency(base_url):
    """Get request latency to Binance server."""
    try:
        start_time = time.time()
        response = requests.get(f"{base_url}/fapi/v1/time", timeout=5)
        server_time_ms = response.json()['serverTime']
        offset = (datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc) - datetime.now(timezone.utc)).total_seconds()
        request_duration = time.time() - start_time
        log(f"Time sync: offset={offset:.3f}s, latency={request_duration:.3f}s")
        return request_duration  # Return latency, not offset
    except Exception as e:
        log(f"Binance time sync failed: {e}")
        return None

# ------------------- BINANCE CLIENT (FIXED: API endpoints and parameters) -------------------
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
        # FIXED: Updated testnet endpoints
        self.base = base_override or ("https://fapi.binance.com" if use_live else "https://testnet.binancefuture.com")
        self.ws_base = "wss://fstream.binance.com" if use_live else "wss://stream.binancefuture.com"
        self.ping_latency = get_time_sync_latency(self.base)
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
        
        return None, None
    
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
        params["timestamp"] = get_server_time(self)
        params["recvWindow"] = 60000

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
        """Cancel all open orders with retry logic."""
        max_retries = 3
        for attempt in range(max_retries):
            try:
                # Cancel regular orders
                self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol, "recvWindow": 60000})
                log(f"[ORDER CANCEL] All regular orders cancelled for {symbol}")

                # Cancel algo orders
                try:
                    resp = self.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
                    algo_orders = resp if isinstance(resp, list) else []
                    
                    if algo_orders:
                        log(f"[ORDER CANCEL] Found {len(algo_orders)} algo order(s)")
                        for order in algo_orders:
                            algo_id = order.get("algoId")
                            if algo_id:
                                self.send_signed_request("DELETE", "/fapi/v1/algoOrder", {
                                    "symbol": symbol,
                                    "algoId": str(algo_id)
                                })
                                time.sleep(0.1)
                except Exception as e:
                    log(f"[ORDER CANCEL] Algo cleanup warning: {e}")

                return
            except Exception as e:
                if attempt < max_retries - 1:
                    wait = (2 ** attempt) * 2
                    log(f"[ORDER CANCEL] Failed (attempt {attempt+1}/{max_retries}): {e}. Retrying in {wait}s...")
                    time.sleep(wait)
                else:
                    log(f"[ORDER CANCEL] Failed after {max_retries} attempts: {e}")
                    raise

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

    def place_algo_order(self, symbol: str, side: str, quantity: Decimal,
                         order_type: str, trigger_price: Decimal = None,
                         activation_price: Decimal = None, callback_rate: Decimal = None,
                         reduce_only: bool = True):
        params = {
            "algoType": "CONDITIONAL",
            "symbol": symbol,
            "side": side,
            "type": order_type,
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false",
            "timeInForce": "GTC",  # FIXED: Use standard GTC instead of GTE_GTC
            "priceProtect": "true"
        }
        
        # FIXED: Add positionSide if in hedge mode
        if self.dual_side:
            if side == "BUY":
                params["positionSide"] = "LONG"
            else:
                params["positionSide"] = "SHORT"
        
        if trigger_price is not None:
            params["triggerPrice"] = str(trigger_price)
            params["workingType"] = "CONTRACT_PRICE"
        if activation_price is not None:
            params["activatePrice"] = str(activation_price)
        if callback_rate is not None:
            # FIXED: Binance expects callback rate as percentage (e.g., 1.5 for 1.5%)
            params["callbackRate"] = str(callback_rate)

        return self.send_signed_request("POST", "/fapi/v1/algoOrder", params)

    def place_stop_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                          reduce_only: bool = True):
        return self.place_algo_order(symbol, side, quantity, "STOP_MARKET", trigger_price=stop_price, reduce_only=reduce_only)

    def place_take_profit_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                                reduce_only: bool = True):
        return self.place_algo_order(symbol, side, quantity, "TAKE_PROFIT_MARKET", trigger_price=stop_price, reduce_only=reduce_only)

    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal,
                                  callback_rate: Decimal, activation_price: Decimal,
                                  reduce_only: bool = True):
        # FIXED: Binance expects callback rate as percentage (e.g., 1.5 for 1.5%)
        return self.place_algo_order(symbol, side, quantity, "TRAILING_STOP_MARKET",
                                     activation_price=activation_price, callback_rate=callback_rate, reduce_only=reduce_only)

# ------------------- INDICATORS -------------------
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

# ------------------- SYMBOL FILTERS (FIXED: Better error handling) -------------------
def get_symbol_filters(client: BinanceClient, symbol: str):
    """Get symbol filters with per-symbol caching."""
    global symbol_filters_cache
    
    symbol = symbol.upper()
    
    # Check cache
    if symbol in symbol_filters_cache:
        return symbol_filters_cache[symbol]
    
    # Fetch from API
    info = client.public_request("/fapi/v1/exchangeInfo")
    s = next((x for x in info.get("symbols", []) if x.get("symbol") == symbol), None)
    if not s:
        raise ValueError(f"{symbol} not found in exchangeInfo")
    
    filters = {f["filterType"]: f for f in s.get("filters", [])}
    
    # Get LOT_SIZE filter (required)
    lot = filters.get("LOT_SIZE")
    if not lot:
        raise ValueError(f"LOT_SIZE filter missing for {symbol}")
    
    step_size = Decimal(str(lot["stepSize"]))
    min_qty = Decimal(str(lot["minQty"]))
    
    # Get PRICE_FILTER (required)
    price_filter = filters.get("PRICE_FILTER")
    if not price_filter:
        # Try MARKET_LOT_SIZE as fallback
        market_lot = filters.get("MARKET_LOT_SIZE")
        if market_lot:
            tick_size = Decimal(str(market_lot.get("stepSize", "0.00000001")))
        else:
            raise ValueError(f"PRICE_FILTER and MARKET_LOT_SIZE filters missing for {symbol}")
    else:
        tick_size = Decimal(str(price_filter.get("tickSize", "0.00000001")))
    
    # Get MIN_NOTIONAL (optional)
    min_notional = Decimal("0")
    min_notional_filter = filters.get("MIN_NOTIONAL")
    if min_notional_filter:
        min_notional = Decimal(str(min_notional_filter.get("notional", "0")))
    
    # Get MARKET_LOT_SIZE for validation
    market_lot = filters.get("MARKET_LOT_SIZE", {})
    
    # Store in cache
    symbol_filters_cache[symbol] = {
        "stepSize": step_size,
        "minQty": min_qty,
        "tickSize": tick_size,
        "minNotional": min_notional,
        "marketLotStepSize": Decimal(str(market_lot.get("stepSize", step_size)))
    }
    
    return symbol_filters_cache[symbol]

# ------------------- ORDERS (FIXED: Consistent Decimal usage) -------------------
def place_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    """Place SL, TP, and Trailing Stop orders."""
    if not trade_state.active or not trade_state.entry_price or trade_state.trail_activation_price is None:
        log("ERROR: place_orders called with incomplete trade_state", telegram_bot, telegram_chat_id)
        return

    # FIXED: Use Decimal directly from trade_state
    entry_price = trade_state.entry_price
    qty_dec = trade_state.qty
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    R = entry_price * SL_PCT
    
    # FIXED: Binance expects callback rate as percentage (e.g., 1.5 for 1.5%)
    callback_rate = (TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')).quantize(Decimal('0.01'))

    # === RECALCULATE SL and TP ===
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
    trail_activation_price_quant = trade_state.trail_activation_price  # Already Decimal

    failures = 0

    # === SL ===
    try:
        sl_order = client.place_stop_market(
            symbol, close_side, qty_dec, sl_price_quant,
            reduce_only=True
        )
        trade_state.sl_order_id = sl_order.get("orderId")
        trade_state.sl_algo_id = sl_order.get("algoId")
        trade_state.sl = sl_price_quant
        log(f"Placed STOP_MARKET SL at {float(sl_price_quant):.4f}: {json.dumps(sl_order, indent=2)}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)

    # === TP ===
    try:
        tp_order = client.place_take_profit_market(
            symbol, close_side, qty_dec, tp_price_quant,
            reduce_only=True
        )
        trade_state.tp_order_id = tp_order.get("orderId")
        trade_state.tp_algo_id = tp_order.get("algoId")
        trade_state.tp = tp_price_quant
        log(f"Placed TAKE_PROFIT_MARKET TP at {float(tp_price_quant):.4f}: {json.dumps(tp_order, indent=2)}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)

    # === TRAILING STOP ===
    try:
        trail_order = client.place_trailing_stop_market(
            symbol, close_side, qty_dec,
            callback_rate=callback_rate,
            activation_price=trail_activation_price_quant,
            reduce_only=True
        )
        trade_state.trail_order_id = trail_order.get("orderId")
        trade_state.trail_algo_id = trail_order.get("algoId")
        log(f"Placed TRAILING_STOP_MARKET (activation: {float(trail_activation_price_quant):.4f}, callback: {float(callback_rate):.2f}%): "
        f"{json.dumps(trail_order, indent=2)}", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)

    # === EMERGENCY: All protective orders failed ===
    if failures >= 3:
        emergency_msg = (
            f"🚨 EMERGENCY CLOSE: ALL PROTECTIVE ORDERS FAILED 🚨\n"
            f"Symbol: {symbol} | Side: {trade_state.side}\n"
            f"Entry: {float(trade_state.entry_price):.4f} | Qty: {float(trade_state.qty):.5f}\n"
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

# ------------------- HELPER: KLINE DATA EXTRACTION -------------------
def closes_and_volumes_from_klines(klines):
    closes = [float(k[4]) for k in klines]
    volumes = [float(k[5]) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [float(k[1]) for k in klines]
    return closes, volumes, close_times, opens

# ------------------- DATA FETCHING -------------------
def ensure_tv_quality_data(klines, timeframe, is_testnet=False):
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
        if float(candle[4]) <= 0 or float(candle[1]) <= 0:
            return False, f"Invalid price in recent candle"

    return True, f"OK: {len(klines)} candles (quality check passed)"

def fetch_balance(client: BinanceClient):
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
        return Decimal(str(data.get("totalWalletBalance", 0)))
    except Exception as e:
        log(f"Balance fetch failed: {str(e)}")
        raise

def trading_allowed(client, symbol, telegram_bot, telegram_chat_id) -> bool:
    """Simple check for weekly DD and consecutive loss guards"""
    current_balance = fetch_balance(client)
    risk_allowed = get_current_risk_pct(
        current_equity=current_balance,
        client=client,
        symbol=symbol,
        telegram_bot=telegram_bot,
        telegram_chat_id=telegram_chat_id
    )
    return risk_allowed > Decimal("0")

def has_active_position(client: BinanceClient, symbol: str, telegram_bot=None, telegram_chat_id=None):
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        for p in positions:
            if isinstance(p, dict) and p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != 0:
                return True
        return False
    except Exception as e:
        log(f"Position check failed: {str(e)}", telegram_bot, telegram_chat_id)
        return False

def fetch_open_positions_details(client: BinanceClient, symbol: str, telegram_bot=None, telegram_chat_id=None):
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

# ------------------- RECOVERY FUNCTIONS -------------------
def debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    """Recover missing protective algo orders with proper error handling."""
    if not trade_state.active:
        return False
    
    try:
        # Verify position exists
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp.get('data') if isinstance(pos_resp, dict) else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        if not pos_item or Decimal(str(pos_item.get("positionAmt", "0"))) == 0:
            return False
        
        # Emergency close on ~1% adverse move
        current_price = Decimal(str(client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})["price"]))
        entry = Decimal(str(trade_state.entry_price))
        
        adverse_move = False
        if trade_state.side == "LONG" and current_price <= entry * Decimal("0.99"):
            adverse_move = True
        elif trade_state.side == "SHORT" and current_price >= entry * Decimal("1.01"):
            adverse_move = True
        
        if adverse_move:
            log(f"EMERGENCY CLOSE: Price moved adversely ~1% | Entry={float(entry):.4f} Current={float(current_price):.4f}", telegram_bot, telegram_chat_id)
            _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
            trade_state.active = False
            return True
        
        # Fetch open algo orders with rate limit handling
        max_retries = 3
        for attempt in range(max_retries):
            try:
                algo_resp = client.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
                algo_open = algo_resp if isinstance(algo_resp, list) else []
                open_algo_ids = {o.get("algoId") for o in algo_open if o.get("algoId") is not None}
                break
            except Exception as e:
                if attempt < max_retries - 1:
                    wait_time = (2 ** attempt) * 5  # Exponential backoff
                    log(f"Rate limited fetching algo orders, retrying in {wait_time}s...", telegram_bot, telegram_chat_id)
                    time.sleep(wait_time)
                else:
                    log(f"Failed to fetch algo orders after {max_retries} attempts: {e}", telegram_bot, telegram_chat_id)
                    return False
        
        recovered = False
        
        # Helper functions for order placement
        def _calc_sl_price(entry, side, tick_size):
            sl = entry * (Decimal("1") - SL_PCT) if side == "LONG" else entry * (Decimal("1") + SL_PCT)
            return quantize_price(sl, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

        def _calc_tp_price(entry, side, tick_size):
            R = entry * SL_PCT
            tp = entry + (TP_MULT * R) if side == "LONG" else entry - (TP_MULT * R)
            return quantize_price(tp, tick_size, ROUND_UP if side == "LONG" else ROUND_DOWN)

        def _calc_trail_activation(entry, side, tick_size):
            R = entry * SL_PCT
            act = entry + (TRAIL_TRIGGER_MULT * R) if side == "LONG" else entry - (TRAIL_TRIGGER_MULT * R)
            return quantize_price(act, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

        # Recover SL
        if trade_state.sl_algo_id and trade_state.sl_algo_id not in open_algo_ids:
            log(f"SL missing (algoId={trade_state.sl_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            sl_price = _calc_sl_price(trade_state.entry_price, trade_state.side, tick_size)
            try:
                new_sl = _place_stop_market(client, symbol, trade_state, sl_price, telegram_bot, telegram_chat_id)
                if new_sl and new_sl.get("algoId"):
                    trade_state.sl_algo_id = new_sl["algoId"]
                    trade_state.sl = sl_price  # Fixed: Keep as Decimal, not float
                    log(f"SL RECOVERED | New algoId={trade_state.sl_algo_id} | Price={float(sl_price):.4f}", telegram_bot, telegram_chat_id)
                    recovered = True
            except Exception as e:
                log(f"Failed to recover SL: {e}", telegram_bot, telegram_chat_id)
        
        # Recover TP
        if trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids:
            log(f"TP missing (algoId={trade_state.tp_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            tp_price = _calc_tp_price(trade_state.entry_price, trade_state.side, tick_size)
            try:
                new_tp = _place_take_profit(client, symbol, trade_state, tp_price, telegram_bot, telegram_chat_id)
                if new_tp and new_tp.get("algoId"):
                    trade_state.tp_algo_id = new_tp["algoId"]
                    trade_state.tp = tp_price  # Fixed: Keep as Decimal, not float
                    log(f"TP RECOVERED | New algoId={trade_state.tp_algo_id} | Price={float(tp_price):.4f}", telegram_bot, telegram_chat_id)
                    recovered = True
            except Exception as e:
                log(f"Failed to recover TP: {e}", telegram_bot, telegram_chat_id)
        
        # Recover Trailing
        if trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids:
            log(f"Trailing missing (algoId={trade_state.trail_algo_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            act_price = trade_state.trail_activation_price or _calc_trail_activation(trade_state.entry_price, trade_state.side, tick_size)
            try:
                new_trail = _place_trailing_stop(client, symbol, trade_state, act_price, telegram_bot, telegram_chat_id)
                if new_trail and new_trail.get("algoId"):
                    trade_state.trail_algo_id = new_trail["algoId"]
                    log(f"TRAILING RECOVERED | New algoId={trade_state.trail_algo_id} | Activation={float(act_price):.4f}", telegram_bot, telegram_chat_id)
                    recovered = True
            except Exception as e:
                log(f"Failed to recover trailing: {e}", telegram_bot, telegram_chat_id)
        
        if recovered:
            log("Recovery complete — protective orders restored.", telegram_bot, telegram_chat_id)
        
        return recovered
        
    except Exception as e:
        log(f"Recovery failed: {e}", telegram_bot, telegram_chat_id)
        return False
    
def _calc_sl_price(entry: Decimal, side: str, tick_size: Decimal) -> Decimal:
    """Calculate stop loss price."""
    if side == "LONG":
        sl = entry * (Decimal("1") - SL_PCT)
        return quantize_price(sl, tick_size, ROUND_DOWN)
    else:  # SHORT
        sl = entry * (Decimal("1") + SL_PCT)
        return quantize_price(sl, tick_size, ROUND_UP)

def _calc_tp_price(entry: Decimal, side: str, tick_size: Decimal) -> Decimal:
    """Calculate take profit price."""
    R = entry * SL_PCT
    if side == "LONG":
        tp = entry + (TP_MULT * R)
        return quantize_price(tp, tick_size, ROUND_UP)
    else:  # SHORT
        tp = entry - (TP_MULT * R)
        return quantize_price(tp, tick_size, ROUND_DOWN)

def _calc_trail_activation(entry: Decimal, side: str, tick_size: Decimal) -> Decimal:
    """Calculate trailing stop activation price."""
    R = entry * SL_PCT
    if side == "LONG":
        act = entry + (TRAIL_TRIGGER_MULT * R)
        return quantize_price(act, tick_size, ROUND_DOWN)
    else:  # SHORT
        act = entry - (TRAIL_TRIGGER_MULT * R)
        return quantize_price(act, tick_size, ROUND_UP)

def _place_stop_market(client, symbol, ts, price: Decimal, telegram_bot=None, telegram_chat_id=None):
    """Place stop market order."""
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty or Decimal("0")
    try:
        response = client.place_stop_market(symbol, side, qty, price, reduce_only=True)
        log(f"[RECOVERY] Placed STOP_MARKET: {json.dumps(response, indent=2)}", telegram_bot, telegram_chat_id)
        return response
    except Exception:
        return None
    
def _place_take_profit(client, symbol, ts, price: Decimal, telegram_bot=None, telegram_chat_id=None):
    """Place take profit market order."""
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty or Decimal("0")
    try:
        response = client.place_take_profit_market(symbol, side, qty, price, reduce_only=True)
        log(f"[RECOVERY] Placed TAKE_PROFIT_MARKET: {json.dumps(response, indent=2)}", telegram_bot, telegram_chat_id)
        return response
    except Exception:
        return None

def _place_trailing_stop(client, symbol, ts, act_price: Decimal, telegram_bot=None, telegram_chat_id=None):
    """Place trailing stop market order."""
    side = "SELL" if ts.side == "LONG" else "BUY"
    qty = ts.qty or Decimal("0")
    rate = (TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')).quantize(Decimal('0.01'))
    try:
        response = client.place_trailing_stop_market(symbol, side, qty, rate, act_price, reduce_only=True)
        log(f"[RECOVERY] Placed TRAILING_STOP_MARKET: {json.dumps(response, indent=2)}", telegram_bot, telegram_chat_id)
        return response
    except Exception:
        return None
    
# ------------------- TELEGRAM MESSAGES -------------------
def send_trailing_activation_telegram(symbol, side, activation_price, initial_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Activated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Activation Price: {activation_price:.4f}\n"
        f"- Initial Stop Price: {initial_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_update_telegram(symbol, side, new_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {new_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol, side, entry_price, exit_price, qty, pnl_usd, pnl_r, reason, bot, chat_id):
    global CONSEC_LOSSES
    
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry Price: {entry_price:.4f}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Reason: {reason}\n"
        f"- Qty: {qty}\n"
        f"- PNL: {pnl_usd:.2f} USDT ({pnl_r:.2f}R)\n"
        f"- Loss Streak: {CONSEC_LOSSES}"
    )
    telegram_post(bot, chat_id, message)

# ------------------- MONITOR TRADE (FIXED: Complete with all logic) -------------------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, current_candle_close_time):
    global _orders_cancelled, _polling_active, _ws_failed
    
    # Initialize all variables at top of function
    trade_start_time = time.time()
    last_recovery_check = 0
    current_price = None
    ws = None
    ws_running = False
    
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)

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
            start_polling_mode(client, symbol, telegram_bot, telegram_chat_id)

    def on_close(ws_app, close_status_code, close_reason):
        global _ws_failed
        if not _ws_failed and trade_state.active:
            log("WebSocket closed. Switching to polling mode.", telegram_bot, telegram_chat_id)
            _ws_failed = True
            start_polling_mode(client, symbol, telegram_bot, telegram_chat_id)

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
        base_url = f"{client.ws_base}/ws"  # FIXED: Use client.ws_base
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
            if current_price is None:
                time.sleep(1)
                continue
            
            # === RECOVERY CHECK ===
            if time.time() - last_recovery_check >= RECOVERY_CHECK_INTERVAL:
                try:
                    debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Recovery check error: {e}", telegram_bot, telegram_chat_id)
                last_recovery_check = time.time()

            # === GET LATEST PRICE ===
            try:
                price_candidate = _price_queue.get_nowait()
                if price_candidate > Decimal('0') and price_candidate <= Decimal('1000'):  # Sanity check
                    current_price = price_candidate
            except queue.Empty:
                pass

            # === POSITION CHECK ===
            try:
                pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
                
                # Normalize response
                if isinstance(pos_resp, dict) and 'data' in pos_resp:
                    positions = pos_resp['data']
                elif isinstance(pos_resp, list):
                    positions = pos_resp
                else:
                    log(f"Unexpected positionRisk response type: {type(pos_resp)}", telegram_bot, telegram_chat_id)
                    positions = []
                
                # Find position
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
                
                if pos_amt == 0 and trade_state.active:
                    # === POSITION CLOSED – DETERMINE EXACT REASON & FILL PRICE ===
                    log("Position closed (verified via positionAmt == 0). Determining exit reason and exact fill price...", telegram_bot, telegram_chat_id)
                    trade_state.active = False

                    # Give Binance time to finalize internal state
                    time.sleep(1.2)

                    reason = "Unknown"
                    exit_price_dec = None

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
                            reason = "Manual Close" if not STOP_REQUESTED else "Stop Requested"

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

                    # --- Log PNL ---
                    entry_price_safe = trade_state.entry_price or Decimal("0")
                    R = entry_price_safe * SL_PCT

                    pnl_row = log_pnl(
                        len(pnl_data) + 1,
                        trade_state.side,
                        entry_price_safe,
                        exit_price_dec or Decimal("0"),
                        trade_state.qty or Decimal("0"),
                        R
                    )

                    # --- Enhanced Logging ---
                    log(f"Position closed by {reason}", telegram_bot, telegram_chat_id)
                    log(
                        f"Entry: {float(entry_price_safe):.4f} → Exit: {float(exit_price_dec or 0):.4f} | "
                        f"PNL: {pnl_row['pnl_usd']:.2f} USDT ({pnl_row['pnl_r']:.2f}R)",
                        telegram_bot, telegram_chat_id
                    )

                    # --- Telegram Notification ---
                    send_closure_telegram(
                        symbol=symbol,
                        side=trade_state.side,
                        entry_price=float(entry_price_safe),
                        exit_price=float(exit_price_dec or 0),
                        qty=float(trade_state.qty or 0),
                        pnl_usd=float(pnl_row['pnl_usd']),
                        pnl_r=float(pnl_row['pnl_r']),
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
                    _orders_cancelled = True

                    return  # Exit monitor_trade cleanly
                
                # Update high/low prices
                if current_price is not None:
                    if trade_state.side == "LONG":
                        if trade_state.highest_price is None or current_price > trade_state.highest_price:
                            trade_state.highest_price = current_price
                    else:  # SHORT
                        if trade_state.lowest_price is None or current_price < trade_state.lowest_price:
                            trade_state.lowest_price = current_price

                # Trailing activation check
                if (not trade_state.trail_activated and 
                    trade_state.trail_activation_price and 
                    current_price is not None and 
                    current_price > Decimal('1')):
                    
                    trail_activation_price_dec = trade_state.trail_activation_price
                    if ((trade_state.side == "LONG" and current_price >= trail_activation_price_dec) or
                        (trade_state.side == "SHORT" and current_price <= trail_activation_price_dec)):

                        trade_state.trail_activated = True
                        R_dec = trade_state.risk or Decimal("0")
                        activation_dec = trade_state.trail_activation_price

                        if trade_state.side == "LONG":
                            init_stop_raw = activation_dec - (TRAIL_DISTANCE_MULT * R_dec)
                            init_stop = quantize_price(init_stop_raw, tick_size, ROUND_DOWN)
                        else:
                            init_stop_raw = activation_dec + (TRAIL_DISTANCE_MULT * R_dec)
                            init_stop = quantize_price(init_stop_raw, tick_size, ROUND_UP)

                        send_trailing_activation_telegram(
                            symbol, trade_state.side,
                            float(current_price), float(init_stop),
                            telegram_bot, telegram_chat_id
                        )
                        trade_state.current_trail_stop = init_stop
                        trade_state.last_trail_alert = time.time()

                # --- TRAILING UPDATES (NATIVE BINANCE TRACKING ONLY) ---
                if trade_state.trail_activated and time.time() - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE and current_price is not None:
                    R_dec = trade_state.risk or Decimal("0")
                    updated = False
                    new_stop = None

                    if trade_state.side == "LONG":
                        if trade_state.highest_price:
                            expected_stop_raw = trade_state.highest_price - (TRAIL_DISTANCE_MULT * R_dec)
                            expected_stop = quantize_price(expected_stop_raw, tick_size, ROUND_DOWN)
                            current_stop = trade_state.current_trail_stop or Decimal("0")
                            if expected_stop > current_stop:
                                updated = True
                                new_stop = expected_stop
                    else:
                        if trade_state.lowest_price:
                            expected_stop_raw = trade_state.lowest_price + (TRAIL_DISTANCE_MULT * R_dec)
                            expected_stop = quantize_price(expected_stop_raw, tick_size, ROUND_UP)
                            current_stop = trade_state.current_trail_stop or Decimal("0")
                            if expected_stop < current_stop:
                                updated = True
                                new_stop = expected_stop

                    if updated and new_stop:
                        trade_state.current_trail_stop = new_stop
                        trade_state.last_trail_alert = time.time()
                        send_trailing_update_telegram(symbol, trade_state.side, float(new_stop), telegram_bot, telegram_chat_id)

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
            except Exception:
                pass

# ------------------- START POLLING MODE -------------------
def start_polling_mode(client, symbol, telegram_bot, telegram_chat_id):
    """Start polling mode with client passed as parameter."""
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
# ------------------- TRADING LOOP (FIXED: Complete signature and consistent Decimal usage) -------------------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, telegram_bot, telegram_chat_id):
    # FIXED: Complete function signature
    global last_news_guard_msg, news_guard_was_active
    
    interval_seconds = interval_ms(timeframe) / 1000.0
    trades_today = 0
    trade_state = TradeState()
    pending_entry = False
    
    # Get filters
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    min_qty = filters['minQty']
    tick_size = filters['tickSize']
    min_notional = filters['minNotional']
    max_trades_alert_sent = False
    
    last_trade_date = datetime.now(timezone.utc).date()
    log(f"Bot started on {last_trade_date}. Trades today: {trades_today}", telegram_bot, telegram_chat_id)

    # FIXED: Signal handlers removed - handled in main shutdown flow only
    log(f"Starting bot with symbol={symbol}, timeframe={timeframe}, risk_pct={float(risk_pct*100):.1f}%")

    # === RECOVER EXISTING POSITION ===
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol, telegram_bot, telegram_chat_id)
        if pos:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt != 0:
                trade_state.active = True
                trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
                trade_state.qty = abs(pos_amt)  # FIXED: Keep as Decimal
                trade_state.entry_price = Decimal(str(pos.get("entryPrice", "0")))  # FIXED: Keep as Decimal
                trade_state.risk = trade_state.entry_price * SL_PCT  # FIXED: Keep as Decimal
                trade_state.sl_order_id = None
                trade_state.tp_order_id = None
                trade_state.trail_order_id = None
                log("Existing position detected on startup. Recovering orders...", telegram_bot, telegram_chat_id)
                debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, int(time.time() * 1000))

    # === MAIN LOOP ===
    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            if trade_state.active:
                monitor_trade(
                    client, symbol, trade_state, tick_size,
                    telegram_bot, telegram_chat_id,
                    trade_state.entry_close_time
                )
                continue

            # === DAILY RESET ===
            now_date = datetime.now(timezone.utc).date()
            if last_trade_date != now_date:
                last_trade_date = now_date
                trades_today = 0
                max_trades_alert_sent = False
                daily_start_balance = fetch_balance(client)
                log(f"NEW DAY → {now_date} | Trades reset | Equity: ${float(daily_start_balance):.2f}", telegram_bot, telegram_chat_id)

            if trades_today >= max_trades_per_day:
                if not max_trades_alert_sent:
                    log(f"Max trades reached ({max_trades_per_day}). No more today.", telegram_bot, telegram_chat_id)
                    max_trades_alert_sent = True
                time.sleep(60)
                continue

            if not trading_allowed(client, symbol, telegram_bot, telegram_chat_id):
                time.sleep(1)
                continue
            
            current_balance = fetch_balance(client)

            # === FETCH KLINES ===
            klines = fetch_klines(client, symbol, timeframe)
            is_testnet = not client.use_live
            is_good, msg = ensure_tv_quality_data(klines, timeframe, is_testnet=is_testnet)
            if not is_good:
                log(f"Data quality failed: {msg}. Skipping this cycle.", telegram_bot, telegram_chat_id)
                time.sleep(10)
                continue

            latest_close_ms = int(klines[-1][6])

            # Check alignment
            if bot_state.last_processed_close_ms is not None and latest_close_ms <= bot_state.last_processed_close_ms:
                wait_sec = max(1.0, (latest_close_ms + interval_ms(timeframe) - int(time.time() * 1000)) / 1000.0 + 2)
                next_dt = datetime.fromtimestamp((latest_close_ms + interval_ms(timeframe)) / 1000, tz=timezone.utc)
                log(f"Waiting for next {timeframe} candle close in {wait_sec:.1f}s → {next_dt.strftime('%H:%M')} UTC", 
                    telegram_bot, telegram_chat_id)
                _safe_sleep(wait_sec)
                continue

            bot_state.last_processed_close_ms = latest_close_ms

            # Process candle
            dt = datetime.fromtimestamp(latest_close_ms / 1000, tz=timezone.utc)
            log(f"Aligned to {timeframe} candle close: {dt.strftime('%H:%M')} UTC", telegram_bot, telegram_chat_id)
            
            close_price = Decimal(str(klines[-1][4]))
            open_price = Decimal(str(klines[-1][1]))
            curr_vol = float(klines[-1][5])
            is_green_candle = close_price > open_price

            closes, volumes, _, _ = closes_and_volumes_from_klines(klines)
            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD) if len(volumes) >= VOL_SMA_PERIOD else None

            state = f"{close_price:.4f}|{rsi:.2f}|{curr_vol:.0f}|{vol_sma15:.2f}|{'G' if is_green_candle else 'R'}"
            if bot_state.last_candle_state is None or state != bot_state.last_candle_state:
                log(f"Candle: {close_price:.4f} RSI={rsi:.2f} Vol={curr_vol:.0f} SMA15={vol_sma15:.2f} {'Green' if is_green_candle else 'Red'}", telegram_bot, telegram_chat_id)
                bot_state.last_candle_state = state

            buy_signal = (rsi and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and not is_green_candle and (not use_volume_filter or curr_vol > vol_sma15))

            if (buy_signal or sell_signal) and not pending_entry:
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close → {side_text}. Preparing entry.", telegram_bot, telegram_chat_id)
                pending_entry = True
                entry_price = close_price

                # === SLIPPAGE GUARD ===
                slippage_pct = None
                current_price = None
                source = ""

                try:
                    ticker = client.public_request("/fapi/v1/ticker/bookTicker", {"symbol": symbol})
                    bid = Decimal(str(ticker.get("bidPrice") or "0"))
                    ask = Decimal(str(ticker.get("askPrice") or "0"))

                    if bid > 0 and ask > 0:
                        current_price = (bid + ask) / 2
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
                        slippage_pct = Decimal("0")
                        source = "none (disabled)"

                if slippage_pct > MAX_ENTRY_SLIPPAGE_PCT:
                    log(
                        f"ENTRY SKIPPED: Estimated slippage {float(slippage_pct*100):.3f}% > 0.2% "
                        f"[{source}]\n"
                        f"   Candle close: {float(entry_price):.4f} → Current: {float(current_price):.4f}",
                        telegram_bot, telegram_chat_id
                    )
                    pending_entry = False
                    continue

                # Calculate levels
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

                # Calculate quantity
                risk_amount_usd = current_balance * BASE_RISK_PCT
                max_notional_by_leverage = current_balance * MAX_LEVERAGE
                max_qty_by_leverage = max_notional_by_leverage / entry_price
                qty_raw = risk_amount_usd / R
                qty = min(qty_raw, max_qty_by_leverage)
                qty = qty * Decimal("0.7")
                qty_api = quantize_qty(qty, step_size)

                if (qty_api * entry_price) < min_notional:
                    log(f"Qty too small → SKIP", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    continue

                # Log entry details
                log(f"===== TRADE ENTRY DETAILS =====", telegram_bot, telegram_chat_id)
                log(f"Direction: {side_text} | Price: ${float(entry_price):.4f}", telegram_bot, telegram_chat_id)
                log(f"Quantity: {float(qty_api):.5f} SOL | Notional: ${float(qty_api * entry_price):.2f}", telegram_bot, telegram_chat_id)
                log(f"Risk: {BASE_RISK_PCT:.1%} (${float(risk_amount_usd):.2f})", telegram_bot, telegram_chat_id)
                log(f"Balance: ${float(current_balance):.2f}", telegram_bot, telegram_chat_id)
                log(f"===== END ENTRY DETAILS =====", telegram_bot, telegram_chat_id)

                # Place order
                log(f"Sending MARKET {side_text} order: qty={qty_api}", telegram_bot, telegram_chat_id)
                order_res = client.send_signed_request("POST", "/fapi/v1/order", {
                    "symbol": symbol, "side": side_text, "type": "MARKET", "quantity": str(qty_api)
                })
                log(f"Market order placed: {json.dumps(order_res, indent=2)}", telegram_bot, telegram_chat_id)

                # Wait for fill
                start_time = time.time()
                actual_qty = None
                while not STOP_REQUESTED:
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

                # Get actual fill price
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    actual_fill_price = entry_price
                actual_fill_price_dec = actual_fill_price

                # Recalculate with actual fill price
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

                # FIXED: Store all values as Decimal in trade_state
                trade_state.active = True
                trade_state.entry_price = actual_fill_price_dec
                trade_state.risk = R
                trade_state.qty = actual_qty
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = latest_close_ms
                trade_state.initial_sl = sl_price_quant
                trade_state.sl = sl_price_quant
                trade_state.tp = tp_price_quant
                trade_state.trail_activated = False
                trade_state.trail_activation_price = trail_activation_quant

                log(f"Position opened: {trade_state.side}, qty={float(actual_qty):.5f}, entry={float(actual_fill_price_dec):.4f}, "
                    f"sl={float(sl_price_quant):.4f}, tp={float(tp_price_quant):.4f}, trail_activation={float(trail_activation_quant):.4f}",
                    telegram_bot, telegram_chat_id)

                # Telegram message
                tg_msg = (
                    f"NEW TRADE\n"
                    f"━━━━━━━━━━━━━━━━\n"
                    f"{trade_state.side} {symbol}\n"
                    f"Entry: {float(actual_fill_price_dec):.4f}\n"
                    f"Qty: {float(actual_qty):.5f} SOL\n"
                    f"SL: {float(sl_price_quant):.4f}\n"
                    f"TP: {float(tp_price_quant):.4f} ({TP_MULT}xR)\n"
                    f"Trail Activation: {float(trail_activation_quant):.4f}\n"
                    f"Risk: {BASE_RISK_PCT:.1%} of equity\n"
                    f"━━━━━━━━━━━━━━━━"
                )
                telegram_post(telegram_bot, telegram_chat_id, tg_msg)

                # Place protective orders
                place_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)

                trades_today += 1
                pending_entry = False

                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, latest_close_ms)

            else:
                if not pending_entry:
                    log("No trade signal on candle close.", telegram_bot, telegram_chat_id)

            # Wait for next candle
            try:
                server_time = int(client.public_request("/fapi/v1/time")["serverTime"])
            except Exception as e:
                log(f"Failed to fetch server time: {e}", telegram_bot, telegram_chat_id)
                server_time = int(time.time() * 1000)

            interval = interval_ms(timeframe)
            next_close_ms = ((server_time // interval) * interval) + interval

            # Wait
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
            error_msg = f"Loop error: {str(e)}"
            full_trace = traceback.format_exc()
            
            logger.error(error_msg)
            logger.error(full_trace)
            
            try:
                telegram_post(telegram_bot, telegram_chat_id, f"⚠️ BOT ERROR ⚠️\n{error_msg}")
            except Exception:
                pass
            
            time.sleep(2)

    log("Trading loop exited.", telegram_bot, telegram_chat_id)

# ------------------- UTILITY FUNCTIONS -------------------
def interval_ms(interval):
    interval = interval.strip().lower()
    if interval == "45m":
        return 45 * 60 * 1000  # 2700000 ms
    if interval.endswith("m"):
        try:
            minutes = int(interval[:-1])
            if minutes <= 0:
                raise ValueError
            return minutes * 60 * 1000
        except ValueError:
            raise ValueError(f"Invalid minutes in timeframe: {interval}")
    elif interval.endswith("h"):
        try:
            hours = int(interval[:-1])
            if hours <= 0:
                raise ValueError
            return hours * 60 * 60 * 1000
        except ValueError:
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

# ------------------- MAIN ENTRY POINT (FIXED: Clean shutdown flow) -------------------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Binance Trailing, 30m Optimized, SOLUSDT)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", required=True, help="Telegram Bot Token")
    parser.add_argument("--chat-id", required=True, help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol (default: SOLUSDT)")
    parser.add_argument("--timeframe", default="30m", help="Timeframe (default: 30m)")
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

    NEWS_GUARD_ENABLED = not args.no_news_guard
    print(f"[CONFIG] News Guard {'DISABLED' if args.no_news_guard else 'ENABLED'}")

    # Initialize lock and PNL log
    acquire_lock()
    init_pnl_log()

    # FIXED: Single consistent shutdown handler
    _shutdown_done = False

    def graceful_shutdown(sig=None, frame=None):
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

        # First call _request_stop to close positions and cancel orders
        if client and args.symbol:
            try:
                _request_stop(symbol=args.symbol, telegram_bot=args.telegram_token, telegram_chat_id=args.chat_id)
            except Exception as e:
                log(f"Error during stop request: {e}", args.telegram_token, args.chat_id)

        goodbye = (
            f"RSI BOT STOPPED\n"
            f"Symbol: {args.symbol}\n"
            f"Timeframe: {args.timeframe}\n"
            f"Reason: {reason}\n"
            f"Time: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC"  # FIXED: Date format
        )

        try:
            log(goodbye, args.telegram_token, args.chat_id)
        except Exception:
            pass

        # Clean lock file
        try:
            LOCK_FILE = os.path.join(os.getenv('TEMP', '/tmp'), 'sol_rsi_bot.lock')
            if os.path.exists(LOCK_FILE):
                os.unlink(LOCK_FILE)
        except Exception:
            pass

        # Remove kill flag
        try:
            if os.path.exists("/tmp/STOP_BOT_NOW"):
                os.unlink("/tmp/STOP_BOT_NOW")
        except Exception:
            pass

        os._exit(0)

    # FIXED: Register signal handlers once in main
    signal.signal(signal.SIGINT, graceful_shutdown)
    signal.signal(signal.SIGTERM, graceful_shutdown)
    atexit.register(graceful_shutdown)

    # Main bot loop
    while True:
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            log("STOP_BOT_NOW flag detected – shutting down permanently", args.telegram_token, args.chat_id)
            graceful_shutdown()
            break

        try:
            client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
            balance = fetch_balance(client)
            
            # Set leverage
            leverage_to_set = 9
            client.set_leverage(args.symbol, leverage_to_set)
            log(f"Set Binance leverage to {leverage_to_set}x for {args.symbol}", args.telegram_token, args.chat_id)

            risk_pct_display = float(Decimal(str(args.risk_pct)))

            log(f"Simple Weekly DD Guard: 20% hard stop", args.telegram_token, args.chat_id)
            log(f"Consecutive Loss Guard: 3 full losses stop", args.telegram_token, args.chat_id)
            log(f"Base Risk: {float(BASE_RISK_PCT*100):.2f}% per trade", args.telegram_token, args.chat_id)
            log(f"Fetched balance: {float(balance):.2f} USDT", args.telegram_token, args.chat_id)

            if NEWS_GUARD_ENABLED:
                log("Economic calendar monitoring: ENABLED", args.telegram_token, args.chat_id)
            else:
                log("Economic calendar monitoring: DISABLED", args.telegram_token, args.chat_id)

            log(f"STARTING BOT → {args.symbol} | {args.timeframe} | "
                f"Risk: {risk_pct_display:.3f}% | "
                f"Volume Filter: {'ON' if args.use_volume_filter else 'OFF'} | "
                f"Mode: {'LIVE' if args.live else 'TESTNET'}",
                args.telegram_token, args.chat_id)

            # Start trading
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

            log("Bot stopped cleanly – exiting.", args.telegram_token, args.chat_id)
            break

        except Exception as e:
            error_msg = f"BOT CRASHED → RESTARTING IN 15s\n{traceback.format_exc()}"
            try:
                log(error_msg, args.telegram_token, args.chat_id)
                telegram_post(args.telegram_token, args.chat_id, "BOT CRASHED – RESTARTING IN 15s")
            except Exception:
                pass
            time.sleep(15)
