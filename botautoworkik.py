# Binance Futures RSI Bot (MANUAL Trailing Stop Only, 30m Optimized, SOLUSDT)
# FINAL PRODUCTION VERSION — ONLY MANUAL TRAILING — ALL 22+ FIXES PRESERVED
# ENHANCED: WebSocket → REST polling fallback (3s), Decimal math, Wilder RSI, safe quantize, recovery, clean logs
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
POLLING_INTERVAL = 3  # Polling interval after WS failure

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
last_exit_candle_time = None  # ← FIXED: DECLARED GLOBALLY
# Thread-safe stop & order cancellation
_stop_lock = threading.Lock()
_orders_cancelled = False
# WebSocket → Polling fallback state
_ws_failed = False
_polling_active = False
_price_queue = queue.Queue()  # Shared price source (WS or polling)

# ------------------- PNL LOGGING -------------------
def init_pnl_log():
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r'])
            writer.writeheader()

def log_pnl(trade_id, side, entry, exit_price, qty, R):
    entry = Decimal(str(entry))
    exit_price = Decimal(str(exit_price))
    qty = Decimal(str(qty))
    R = Decimal(str(R))
    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty
    pnl_r = pnl_usd / R if R > 0 else Decimal('0')
   
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': float(entry),
        'exit': float(exit_price),
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
    close_time_text = ""
    if 'close_time_ms' in trade_details and trade_details['close_time_ms']:
        try:
            ct = datetime.fromtimestamp(trade_details['close_time_ms']/1000, tz=timezone.utc)
            local = ct.astimezone()
            close_time_text = f"- Candle close (UTC): {ct.strftime('%Y-%m-%d %H:%M:%S')}\n- Candle close (local): {local.strftime('%Y-%m-%d %H:%M:%S')}\n"
        except Exception:
            close_time_text = ""
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"{close_time_text}"
        f"- Manual Trail Activation: {trade_details['trail_activation']:.4f}\n"
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
        f"Manual Trailing Stop Activated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Activation Price: {activation_price:.4f}\n"
        f"- Initial Stop Price: {initial_stop_price:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_update_telegram(symbol, side, new_stop_price, bot, chat_id):
    message = (
        f"Manual Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {new_stop_price:.4f}\n"
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
        response = requests.get(f"{base_url}/fapi/v1/time", timestamp=5)
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
        try:
            r = requests.request(method, url, headers=headers, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                return r.json()
            elif r.status_code == 429 or "throttled" in r.text.lower():
                wait = 60
                log(f"Rate limited. Sleeping {wait}s...")
                time.sleep(wait)
                raise BinanceAPIError("Rate limited", r.status_code, r.text)
            else:
                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", r.status_code, r.text)
        except Exception as e:
            raise BinanceAPIError(f"Request failed: {str(e)}", payload=str(e))

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
        return 100.0
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
    TOLERANCE_MS = 2000
    for i in range(0, len(klines_15m) - 2, 3):
        a, b, c = klines_15m[i], klines_15m[i+1], klines_15m[i+2]
        open_time = int(a[0])
        close_time = int(c[6])
        expected_duration = 3 * 15 * 60 * 1000
        if abs((close_time - open_time) - expected_duration) > TOLERANCE_MS:
            continue
        high = max(float(a[2]), float(b[2]), float(c[2]))
        low = min(float(a[3]), float(b[3]), float(c[3]))
        volume = float(a[5]) + float(b[5]) + float(c[5])
        aggregated.append([
            open_time,
            float(a[1]),
            high,
            low,
            float(c[4]),
            volume,
            close_time
        ])
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

# ------------------- HELPER: KLINE DATA EXTRACTION -------------------
def closes_and_volumes_from_klines(klines):
    closes = [float(k[4]) for k in klines]
    volumes = [float(k[5]) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [float(k[1]) for k in klines]
    return closes, volumes, close_times, opens

# ------------------- HELPER: INTERVAL IN MS -------------------
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

# ------------------- DATA FETCHING -------------------
def fetch_klines(client, symbol, interval, limit=max(100, VOL_SMA_PERIOD + 50)):
    requested = interval
    if requested == "45m":
        interval = "15m"
        limit = max(limit, 300)
    try:
        raw = client.public_request("/fapi/v1/klines", {
            "symbol": symbol,
            "interval": interval,
            "limit": limit
        })
        if interval == "15m" and requested == "45m":
            return aggregate_klines_to_45m(raw)
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
        self.entry_order_id = None

def debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    if not trade_state.active:
        return
    try:
        open_orders = {o["orderId"]: o for o in client.get_open_orders(symbol)}
        if trade_state.sl_order_id and trade_state.sl_order_id not in open_orders:
            log(f"SL missing (ID={trade_state.sl_order_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            sl_price = _calc_sl_price(trade_state.entry_price, trade_state.side, tick_size)
            new_sl = client.place_stop_market(symbol, "SELL" if trade_state.side == "LONG" else "BUY", Decimal(str(trade_state.qty)), sl_price, reduce_only=True, position_side=trade_state.side)
            if new_sl:
                trade_state.sl_order_id = new_sl["orderId"]
                trade_state.sl = float(sl_price)
                telegram_post(telegram_bot, telegram_chat_id, f"SL Recovered: New Stop {trade_state.sl:.4f}")
        if trade_state.tp_order_id and trade_state.tp_order_id not in open_orders:
            log(f"TP missing (ID={trade_state.tp_order_id}). Re-issuing...", telegram_bot, telegram_chat_id)
            tp_price = _calc_tp_price(trade_state.entry_price, trade_state.side, tick_size)
            new_tp = client.place_take_profit_market(symbol, "SELL" if trade_state.side == "LONG" else "BUY", Decimal(str(trade_state.qty)), tp_price, reduce_only=True, position_side=trade_state.side)
            if new_tp:
                trade_state.tp_order_id = new_tp["orderId"]
                trade_state.tp = float(tp_price)
                telegram_post(telegram_bot, telegram_chat_id, f"TP Recovered: New TP {trade_state.tp:.4f}")
    except Exception as e:
        log(f"Recovery failed: {e}", telegram_bot, telegram_chat_id)

def _calc_sl_price(entry, side, tick_size):
    sl = Decimal(str(entry)) * (Decimal("1") - SL_PCT) if side == "LONG" else Decimal(str(entry)) * (Decimal("1") + SL_PCT)
    return quantize_price(sl, tick_size, ROUND_DOWN if side == "LONG" else ROUND_UP)

def _calc_tp_price(entry, side, tick_size):
    R = Decimal(str(entry)) * SL_PCT
    tp = Decimal(str(entry)) + (TP_MULT * R) if side == "LONG" else Decimal(str(entry)) - (TP_MULT * R)
    return quantize_price(tp, tick_size, ROUND_UP if side == "LONG" else ROUND_DOWN)

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

# ------------------- MONITOR TRADE (FULL MANUAL TRAILING) -------------------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, current_candle_close_time):
    global _orders_cancelled, _polling_active, _ws_failed, last_exit_candle_time
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    last_recovery_check = 0
    current_price = None
    ws = None
    ws_running = False

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
            telegram_post(telegram_bot, telegram_chat_id, "WebSocket failed to Switched to REST polling (3s)")
            _ws_failed = True
            start_polling_mode(symbol, telegram_bot, telegram_chat_id)

    def on_close(ws_app, close_status_code, close_reason):
        global _ws_failed
        if not _ws_failed and trade_state.active:
            log("WebSocket closed. Switching to polling mode.", telegram_bot, telegram_chat_id)
            telegram_post(telegram_bot, telegram_chat_id, "WebSocket closed to Switched to REST polling (3s)")
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
            if time.time() - last_recovery_check >= RECOVERY_CHECK_INTERVAL:
                debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                last_recovery_check = time.time()

            try:
                current_price = _price_queue.get_nowait()
            except queue.Empty:
                pass

            try:
                pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
                positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
                pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
                pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
                if pos_amt == 0:
                    log("Position closed.", telegram_bot, telegram_chat_id)
                    trade_state.active = False
                    exit_price = None
                    try:
                        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        exit_price = Decimal(str(ticker.get("price", "0")))
                    except:
                        pass
                    open_orders = []
                    try:
                        open_orders = client.get_open_orders(symbol)
                    except Exception as e:
                        log(f"Failed to fetch open orders: {e}", telegram_bot, telegram_chat_id)
                    reason = "Manual Close"
                    close_price = None
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        reason = "Stop Requested"
                    elif trade_state.sl_order_id and not any(o.get("orderId") == trade_state.sl_order_id for o in open_orders):
                        close_price = client.get_latest_fill_price(symbol, trade_state.sl_order_id)
                        reason = "Stop Loss"
                    elif trade_state.tp_order_id and not any(o.get("orderId") == trade_state.tp_order_id for o in open_orders):
                        close_price = client.get_latest_fill_price(symbol, trade_state.tp_order_id)
                        reason = "Take Profit"
                    elif trade_state.trail_activated and trade_state.current_trail_stop is not None:
                        close_price = current_price or exit_price
                        reason = "Manual Trailing Stop"
                    else:
                        close_price = client.get_latest_fill_price(symbol, trade_state.entry_order_id or trade_state.sl_order_id)
                        reason = "Manual Close"
                    exit_price_f = float(close_price or exit_price or 0)
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
                    send_closure_telegram(
                        symbol, trade_state.side,
                        entry_price_safe, exit_price_f,
                        float(trade_state.qty or 0),
                        float(pnl_row['pnl_usd']), float(pnl_row['pnl_r']),
                        reason, telegram_bot, telegram_chat_id
                    )
                    last_exit_candle_time = current_candle_close_time
                    with _stop_lock:
                        if not _orders_cancelled:
                            try:
                                client.cancel_all_open_orders(symbol)
                                log(f"Cancelled open orders. Reason: {reason}", telegram_bot, telegram_chat_id)
                            except Exception as e:
                                log(f"Failed to cancel orders: {e}", telegram_bot, telegram_chat_id)
                            _orders_cancelled = True
                    return
                if current_price is None:
                    try:
                        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        current_price = Decimal(str(ticker.get("price")))
                    except:
                        pass
                if trade_state.side == "LONG":
                    if trade_state.highest_price is None or current_price > trade_state.highest_price:
                        trade_state.highest_price = current_price
                else:
                    if trade_state.lowest_price is None or current_price < trade_state.lowest_price:
                        trade_state.lowest_price = current_price
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    act_price = Decimal(str(trade_state.trail_activation_price))
                    if (trade_state.side == "LONG" and current_price >= act_price) or \
                       (trade_state.side == "SHORT" and current_price <= act_price):
                        trade_state.trail_activated = True
                        R_dec = Decimal(str(trade_state.risk))
                        if trade_state.side == "LONG":
                            init_stop = quantize_price(act_price - (TRAIL_DISTANCE_MULT * R_dec), tick_size, ROUND_DOWN)
                        else:
                            init_stop = quantize_price(act_price + (TRAIL_DISTANCE_MULT * R_dec), tick_size, ROUND_UP)
                        trade_state.current_trail_stop = float(init_stop)
                        send_trailing_activation_telegram(symbol, trade_state.side, float(current_price), trade_state.current_trail_stop, telegram_bot, telegram_chat_id)
                        trade_state.last_trail_alert = time.time()
                if trade_state.trail_activated and time.time() - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE:
                    R_dec = Decimal(str(trade_state.risk))
                    updated = False
                    new_stop = None
                    if trade_state.side == "LONG":
                        raw = trade_state.highest_price - (TRAIL_DISTANCE_MULT * R_dec)
                        new_stop = quantize_price(raw, tick_size, ROUND_DOWN)
                        if new_stop > Decimal(str(trade_state.current_trail_stop or '0')):
                            updated = True
                    else:
                        raw = trade_state.lowest_price + (TRAIL_DISTANCE_MULT * R_dec)
                        new_stop = quantize_price(raw, tick_size, ROUND_UP)
                        if new_stop < Decimal(str(trade_state.current_trail_stop or '0')):
                            updated = True
                    if updated:
                        trade_state.current_trail_stop = float(new_stop)
                        trade_state.last_trail_alert = time.time()
                        send_trailing_update_telegram(symbol, trade_state.side, trade_state.current_trail_stop, telegram_bot, telegram_chat_id)
                        if (trade_state.side == "LONG" and current_price <= new_stop) or \
                           (trade_state.side == "SHORT" and current_price >= new_stop):
                            log(f"Manual trailing stop hit @ {float(current_price):.4f}. Closing position.", telegram_bot, telegram_chat_id)
                            try:
                                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                                qty_dec = Decimal(str(trade_state.qty))
                                client.send_signed_request("POST", "/fapi/v1/order", {
                                    "symbol": symbol,
                                    "side": close_side,
                                    "type": "MARKET",
                                    "quantity": str(qty_dec),
                                    "reduceOnly": "true"
                                })
                                log(f"Closed on manual trailing stop: {close_side} {qty_dec}", telegram_bot, telegram_chat_id)
                            except Exception as e:
                                log(f"Failed to close on trailing: {e}", telegram_bot, telegram_chat_id)
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

def place_sl_order_closepos(client: BinanceClient, symbol: str, stop_price: str, side: str):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "STOP_MARKET",
        "closePosition": "true",
        "stopPrice": stop_price,
        "recvWindow": 30000
    }
    if client.dual_side:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_tp_order_closepos(client: BinanceClient, symbol: str, stop_price: str, side: str):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "TAKE_PROFIT_MARKET",
        "closePosition": "true",
        "stopPrice": stop_price,
        "recvWindow": 30000
    }
    if client.dual_side:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

# ------------------- TRADING LOOP -------------------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult,
                 use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter,
                 telegram_bot, telegram_chat_id):
    global last_trade_date, last_exit_candle_time
    trades_today = 0
    last_processed_time = 0
    trade_state = TradeState()
    pending_entry = False
    max_trades_alert_sent = False

    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    min_qty = filters['minQty']
    tick_size = filters['tickSize']
    min_notional = filters['minNotional']

    current_date = datetime.now(timezone.utc).date()
    if last_trade_date != current_date:
        trades_today = 0
        last_trade_date = current_date
        max_trades_alert_sent = False
    daily_start_balance = fetch_balance(client)

    signal.signal(signal.SIGINT, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    signal.signal(signal.SIGTERM, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    log(f"Bot started: {symbol} | {timeframe} | Risk: {risk_pct*100:.2f}%")

    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol)
        pos_amt = Decimal(str(pos.get("positionAmt", "0")))
        if pos_amt != 0:
            trade_state.active = True
            trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
            trade_state.qty = float(abs(pos_amt))
            trade_state.entry_price = float(Decimal(str(pos.get("entryPrice", "0"))))
            trade_state.risk = Decimal(str(trade_state.entry_price)) * SL_PCT
            trade_state.sl_order_id = trade_state.tp_order_id = trade_state.entry_order_id = None
            log("Recovering existing position...", telegram_bot, telegram_chat_id)
            debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            try:
                latest_kline = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": "1m", "limit": 1})
                close_time_for_recovery = int(latest_kline[0][6]) if latest_kline else 0
            except Exception as e:
                log(f"Kline fetch failed during recovery: {e}", telegram_bot, telegram_chat_id)
                close_time_for_recovery = 0
            monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, close_time_for_recovery)

    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            current_date = datetime.now(timezone.utc).date()
            if last_trade_date != current_date:
                trades_today = 0
                last_trade_date = current_date
                daily_start_balance = fetch_balance(client)
                max_trades_alert_sent = False
                log(f"New UTC day: {current_date} — Resetting counters", telegram_bot, telegram_chat_id)

            if trades_today >= max_trades_per_day:
                if not max_trades_alert_sent:
                    log(f"Max trades ({max_trades_per_day}) reached. Sleeping until next day.", telegram_bot, telegram_chat_id)
                    max_trades_alert_sent = True
                time.sleep(60)
                continue

            if use_max_loss:
                current_bal = fetch_balance(client)
                loss_threshold = daily_start_balance * (max_daily_loss_pct / Decimal("100"))
                if daily_start_balance - current_bal > loss_threshold:
                    log(f"Max daily loss hit ({loss_threshold:.2f} USDT). Paused until next day.", telegram_bot, telegram_chat_id)
                    time.sleep(60)
                    continue

            try:
                server_time = client.public_request("/fapi/v1/time")["serverTime"]
            except Exception as e:
                log(f"Server time failed: {e}. Using local time.", telegram_bot, telegram_chat_id)
                server_time = int(time.time() * 1000)

            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                log(f"Waiting for candle close in {sleep_seconds:.2f}s ...", telegram_bot, telegram_chat_id)
                _safe_sleep(sleep_seconds)
                continue

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

            last_candle = klines[-1]
            last_close_time = int(last_candle[6])
            close_time = last_close_time
            dt = datetime.fromtimestamp(last_close_time / 1000, tz=timezone.utc)
            log(f"Aligned to {timeframe} candle close: {dt.strftime('%H:%M')} UTC")

            if last_close_time <= last_processed_time:
                log("Candle already processed or not fully closed.")
                time.sleep(1)
                continue
            last_processed_time = last_close_time + 100

            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            curr_vol = volumes[-1]
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price

            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD) if len(volumes) >= VOL_SMA_PERIOD else 0
            log(f"Candle: {float(close_price):.4f} | RSI: {rsi or 'N/A'} | Vol: {curr_vol:.2f} | SMA15: {vol_sma15:.2f} | {'Green' if is_green_candle else 'Red' if is_red_candle else 'Doji'}", telegram_bot, telegram_chat_id)

            if prevent_same_bar and getattr(trade_state, 'entry_close_time', None) == last_close_time:
                log("Entry already attempted this bar. Skipping.", telegram_bot, telegram_chat_id)
                last_processed_time = close_time
                time.sleep(1)
                continue
            if last_exit_candle_time == last_close_time:
                log("Trade exited this candle. Skipping new entry.", telegram_bot, telegram_chat_id)
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

            buy_signal = (rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and
                          (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and
                           (not use_volume_filter or curr_vol > vol_sma15))
            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                close_side_for_orders = "SELL" if buy_signal else "BUY"
                log(f"SIGNAL to {side_text}. Preparing entry.", telegram_bot, telegram_chat_id)
                pending_entry = True
                entry_price = close_price
                entry_price_f = float(entry_price)

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
                if R <= 0:
                    pending_entry = False
                    time.sleep(1)
                    continue

                bal = fetch_balance(client)
                risk_amount = bal * risk_pct
                qty = risk_amount / R
                qty_api = quantize_qty(qty, step_size)
                if qty_api < min_qty:
                    qty_api = min_qty
                notional = qty_api * entry_price
                if notional < min_notional:
                    qty_api = quantize_qty(min_notional / entry_price, step_size)

                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, trail_rounding)

                log(f"Placing MARKET {side_text} | Qty: {qty_api} | Entry: {entry_price_f:.4f}", telegram_bot, telegram_chat_id)
                try:
                    order_res = client.send_signed_request("POST", "/fapi/v1/order", {
                        "symbol": symbol,
                        "side": side_text,
                        "type": "MARKET",
                        "quantity": str(qty_api)
                    })
                    trade_state.entry_order_id = order_res.get("orderId")
                    log(f"Order placed: {order_res}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Order failed: {e}", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue

                start_time = time.time()
                actual_qty = None
                while not STOP_REQUESTED and not os.path.exists("stop.txt"):
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != 0:
                        actual_qty = abs(pos_amt)
                        break
                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        try:
                            client.send_signed_request("DELETE", "/fapi/v1/order", {"symbol": symbol, "orderId": order_res.get("orderId")})
                        except:
                            pass
                        log("Fill timeout. Cancelled.", telegram_bot, telegram_chat_id)
                        pending_entry = False
                        break
                    time.sleep(0.5)
                if actual_qty is None:
                    pending_entry = False
                    continue

                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)
                actual_fill_price = Decimal(str(actual_fill_price_f))

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
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, trail_rounding)

                try:
                    current_price = Decimal(str(client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})["price"]))
                except:
                    current_price = actual_fill_price
                price_buffer = actual_fill_price * TRAIL_PRICE_BUFFER
                if (buy_signal and trail_activation_price_dec_quant <= current_price + price_buffer) or \
                   (not buy_signal and trail_activation_price_dec_quant >= current_price - price_buffer):
                    log("Trail activation too close. Skipping.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue

                trade_state.active = True
                trade_state.entry_price = actual_fill_price_f
                trade_state.risk = R
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                trade_state.initial_sl = float(sl_price_dec_quant)
                trade_state.sl = float(sl_price_dec_quant)
                trade_state.tp = float(tp_price_dec_quant)
                trade_state.trail_activated = False
                trade_state.trail_activation_price = float(trail_activation_price_dec_quant)
                trade_state.highest_price = trade_state.lowest_price = trade_state.current_trail_stop = None
                log(f"Position opened: {trade_state.side} | Qty: {actual_qty} | Entry: {actual_fill_price_f:.4f}")

                trade_details = {
                    'symbol': symbol,
                    'side': trade_state.side,
                    'entry': trade_state.entry_price,
                    'sl': trade_state.sl,
                    'tp': trade_state.tp,
                    'trail_activation': trade_state.trail_activation_price,
                    'qty': trade_state.qty,
                    'close_time_ms': close_time
                }
                send_trade_telegram(trade_details, telegram_bot, telegram_chat_id)

                log("Placing SL/TP orders...", telegram_bot, telegram_chat_id)
                sl_res = place_sl_order_closepos(client, symbol, str(sl_price_dec_quant), close_side_for_orders)
                trade_state.sl_order_id = sl_res.get("orderId")
                log(f"SL placed: {sl_res}", telegram_bot, telegram_chat_id)

                tp_res = place_tp_order_closepos(client, symbol, str(tp_price_dec_quant), close_side_for_orders)
                trade_state.tp_order_id = tp_res.get("orderId")
                log(f"TP placed: {tp_res}", telegram_bot, telegram_chat_id)

                trades_today += 1
                last_trade_date = current_date
                pending_entry = False
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id, close_time)
            else:
                if not (trade_state.active or pending_entry):
                    log("No signal on this candle.", telegram_bot, telegram_chat_id)

            last_processed_time = close_time
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            log(f"Waiting for next candle in {sleep_seconds:.2f}s ...", telegram_bot, telegram_chat_id)
            _safe_sleep(sleep_seconds)
        except Exception as e:
            log(f"Loop error: {e}", telegram_bot, telegram_chat_id)
            time.sleep(2)
    log("Trading loop exited.", telegram_bot, telegram_chat_id)

def _safe_sleep(total_seconds):
    remaining = float(total_seconds)
    while remaining > 0:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        time.sleep(min(1, remaining))
        remaining -= 1

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

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Manual Trailing Only, 30m Optimized, SOLUSDT)")
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
    parser.add_argument("--use-trailing", action='store_true', default=True, help="Enable trailing stop")
    parser.add_argument("--no-trailing", dest='use_trailing', action='store_false')
    parser.add_argument("--prevent-same-bar", action='store_true', default=True)
    parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false')
    parser.add_argument("--require-no-pos", action='store_true', default=True)
    parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false')
    parser.add_argument("--use-max-loss", action='store_true', default=True)
    parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false')
    parser.add_argument("--use-volume-filter", action='store_true', default=False)
    parser.add_argument("--no-volume-filter", dest='use_volume_filter', action='store_false')
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL")
    args = parser.parse_args()

    init_pnl_log()
    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
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
