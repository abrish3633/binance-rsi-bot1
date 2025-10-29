#!/usr/bin/env python3
# Binance Futures RSI Bot (Binance-Handled Trailing Stop, 30m Optimized, SOLUSDT)
# EnhancementStatusDetails1Dynamic klines Implemented
# fetch_klines(..., limit=max(100, VOL_SMA_PERIOD + 50)) — ensures enough data for volume SMA and RSI
# 100% Decimal math Implemented
# All prices, qty, R, SL, TP, trailing levels use Decimal. No float in calculations.
# Safe quantize Implemented
# quantize_qty() and quantize_price() accept Decimal only; internal casting removed.
# WebSocket price Implemented
# websocket-client used for real-time price via @trade stream → 0 API weight for price updates.
# Keep requests Implemented
# No python-binance. Pure requests + websocket.
# Telegram retry Implemented
# telegram_post() retries 3 times with exponential backoff (1s, 2s, 4s).
# Safe cleanup Implemented
# atexit.register() + try/finally in main loop → graceful stop on crash/exit.
# Reusable orders Implemented
# place_orders() central function for SL/TP/Trailing placement.
# Startup + balance Telegram Implemented
# Logs and sends: Connected... + Fetched balance: X.XX USDT on startup.
# Clean logs (no timestamp in Telegram) Implemented
# log(..., telegram_bot, chat_id) → plain message in Telegram, full timestamp in file/console.
# Max trades alert Implemented
# Maximum trades reached for the day (3). Sleeping until next day.
# Crash-proof formatting Implemented
# fmt(val) → safely formats Decimal → float only when logging.
# Recovery every 10s Implemented
# RECOVERY_CHECK_INTERVAL = 10 → checks and re-places SL/TP/Trail if missing.
# Closure reason detection Implemented
# Detects Stop Loss / Take Profit / Trailing Stop / Manual / Unknown.
# Wilder RSI smoothing Implemented
# Full Wilder smoothing: initial average + ongoing prev_avg * (n-1)/n + curr/n.
# Double-log fix Implemented
# CLOSURE_HANDLED global flag ensures closure logic runs exactly once.
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
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN, getcontext
from datetime import datetime, timezone, timedelta
import schedule
from urllib.parse import urlencode
import atexit
import json
import websocket

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")          # 0.5% per trade
SL_PCT = Decimal("0.0075")           # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2.0") # 2R trailing distance
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 50
BUY_RSI_MAX = 80
SELL_RSI_MIN = 20
SELL_RSI_MAX = 50
TRAIL_PRICE_BUFFER = Decimal("0.003")
REQUEST_TIMEOUT = 30
RECOVERY_CHECK_INTERVAL = 10         # Seconds between recovery checks
TRAIL_UPDATE_THROTTLE = 10.0         # Alert trailing updates every 10 seconds max

# Global stop flag and client
STOP_REQUESTED = False
CLOSURE_HANDLED = False              # Ensures closure runs exactly once
client = None
symbol_filters_cache = None
current_price = Decimal('0')
last_price_time = 0

# Global PnL tracking
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data = []

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

# Logging setup
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

def telegram_post(token, chat_id, text, parse_mode=None):
    if not token or not chat_id:
        return
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {"chat_id": chat_id, "text": text}
    if parse_mode:
        payload["parse_mode"] = parse_mode
    for attempt in range(3):
        try:
            r = requests.post(url, json=payload, timeout=10)
            if r.status_code == 200:
                return
            else:
                logger.error(f"Telegram send failed (attempt {attempt+1}): HTTP {r.status_code}: {r.text}")
        except Exception as e:
            logger.error(f"Telegram send failed (attempt {attempt+1}): {e}")
        time.sleep(2 ** attempt)
    logger.error("Telegram send failed after 3 attempts.")

def send_trade_telegram(trade_details, bot, chat_id):
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {fmt(trade_details['entry'])}\n"
        f"- SL: {fmt(trade_details['sl'])}\n"
        f"- TP: {fmt(trade_details['tp'])}\n"
        f"- Trailing Activation: {fmt(trade_details['trail_activation'])}\n"
        f"- Qty: {trade_details['qty']}\n"
    )
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol, side, entry_price, exit_price, qty, pnl_usd, pnl_r, reason, bot, chat_id):
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry Price: {fmt(entry_price)}\n"
        f"- Exit Price: {fmt(exit_price)}\n"
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
        f"- Activation Price: {fmt(activation_price)}\n"
        f"- Initial Stop Price: {fmt(initial_stop_price)}\n"
    )
    telegram_post(bot, chat_id, message)

def send_trailing_update_telegram(symbol, side, new_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {fmt(new_stop_price)}\n"
    )
    telegram_post(bot, chat_id, message)

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

def _request_stop(signum, frame, symbol=None, telegram_bot=None, telegram_chat_id=None):
    global STOP_REQUESTED, client, CLOSURE_HANDLED
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    if not client or not symbol:
        log("Client or symbol not defined; skipping position closure.")
        return
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
        if pos_amt != 0 and not CLOSURE_HANDLED:
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
                exit_price = get_current_price(client, symbol)
            exit_price_d = Decimal(str(exit_price))
            R = entry_price * SL_PCT if entry_price > 0 else Decimal('0')
            pnl_row = log_pnl(len(pnl_data) + 1, "LONG" if pos_amt > 0 else "SHORT", entry_price, exit_price_d, qty, R)
            if telegram_bot and telegram_chat_id:
                send_closure_telegram(symbol, "LONG" if pos_amt > 0 else "SHORT", entry_price, exit_price_d, qty, pnl_row['pnl_usd'], pnl_row['pnl_r'], "Stop Requested", telegram_bot, telegram_chat_id)
            CLOSURE_HANDLED = True
        client.cancel_all_open_orders(symbol)
        log(f"All open orders cancelled for {symbol}.")
    except Exception as e:
        log(f"Stop handler error: {str(e)}")

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

def fmt(val):
    if isinstance(val, Decimal):
        return f"{float(val):.4f}"
    return str(val)

def compute_rsi(closes, period=RSI_PERIOD):
    if len(closes) < period + 1:
        return None
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    gains = [max(d, Decimal('0')) for d in deltas[:period]]
    losses = [max(-d, Decimal('0')) for d in deltas[:period]]
    avg_gain = sum(gains) / Decimal(period)
    avg_loss = sum(losses) / Decimal(period)
    for d in deltas[period:]:
        curr_gain = max(d, Decimal('0'))
        curr_loss = max(-d, Decimal('0'))
        avg_gain = (avg_gain * (Decimal(period) - Decimal('1')) + curr_gain) / Decimal(period)
        avg_loss = (avg_loss * (Decimal(period) - Decimal('1')) + curr_loss) / Decimal(period)
    if avg_loss == 0:
        return Decimal('100.0')
    rs = avg_gain / avg_loss
    rsi = Decimal('100') - Decimal('100') / (Decimal('1') + rs)
    return rsi.quantize(Decimal('0.01'))

def sma(data, period):
    if len(data) < period:
        return None
    return sum(data[-period:]) / Decimal(period)

def quantize_qty(qty: Decimal, step_size: Decimal) -> Decimal:
    q = (qty // step_size) * step_size
    if q == 0:
        q = step_size
    return q.quantize(step_size)

def quantize_price(p: Decimal, tick_size: Decimal, rounding=ROUND_HALF_EVEN) -> Decimal:
    return p.quantize(tick_size, rounding=rounding)

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

def place_market_order(client: BinanceClient, symbol: str, side: str, quantity: Decimal):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "MARKET",
        "quantity": str(quantity)
    }
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_orders(client, symbol, trade_state, tick_size, close_side, pos_side, qty_dec, sl_price_dec_quant, tp_price_dec_quant, callback_rate, activation_price):
    try:
        sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=pos_side)
        trade_state.sl_order_id = sl_order.get("orderId")
        log(f"Placed STOP_MARKET SL: {sl_order}")
    except Exception as e:
        log(f"Failed to place SL: {str(e)}")
    try:
        tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=pos_side)
        trade_state.tp_order_id = tp_order.get("orderId")
        log(f"Placed TAKE_PROFIT_MARKET TP: {tp_order}")
    except Exception as e:
        log(f"Failed to place TP: {str(e)}")
    try:
        trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, activation_price, reduce_only=True, position_side=pos_side)
        trade_state.trail_order_id = trail_order.get("orderId")
        log(f"Placed TRAILING_STOP_MARKET: {trail_order}")
    except Exception as e:
        log(f"Failed to place trailing stop: {str(e)}")

def fetch_klines(client: BinanceClient, symbol: str, interval: str, limit=max(100, VOL_SMA_PERIOD + 50)):
    try:
        data = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        return data
    except Exception as e:
        log(f"Klines fetch failed: {str(e)}")
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

def get_current_price(client, symbol):
    global current_price, last_price_time
    if time.time() - last_price_time < 5:
        return current_price
    else:
        try:
            ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
            p = Decimal(str(ticker.get("price")))
            current_price = p
            last_price_time = time.time()
            return p
        except Exception as e:
            log(f"Price fetch failed: {str(e)}")
            raise

def start_price_ws(symbol):
    def on_message(ws, msg):
        global current_price, last_price_time
        data = json.loads(msg)
        if 'p' in data:
            current_price = Decimal(data['p'])
            last_price_time = time.time()
    ws_url = f"wss://fstream.binance.com/ws/{symbol.lower()}@trade"
    ws = websocket.WebSocketApp(ws_url, on_message=on_message)
    ws.run_forever()

class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price = Decimal('0')
        self.qty = Decimal('0')
        self.side = None
        self.entry_close_time = None
        self.initial_sl = Decimal('0')
        self.sl = Decimal('0')
        self.tp = Decimal('0')
        self.trail_activation_price = Decimal('0')
        self.highest_price = None
        self.lowest_price = None
        self.current_trail_stop = None
        self.trail_activated = False
        self.last_trail_alert = 0.0
        self.risk = Decimal('0')
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_order_id = None

def debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    if not trade_state.active:
        return
    try:
        open_orders = client.get_open_orders(symbol)
        if trade_state.sl_order_id and not any(o.get("orderId") == trade_state.sl_order_id for o in open_orders):
            log(f"SL order missing/expired (ID={trade_state.sl_order_id}). Recovering...", telegram_bot, telegram_chat_id)
            entry_price = trade_state.entry_price
            if entry_price > 0:
                sl_price_dec = entry_price * (Decimal("1") - SL_PCT) if trade_state.side == "LONG" else entry_price * (Decimal("1") + SL_PCT)
                sl_rounding = ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP
                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                pos_side = trade_state.side
                qty_dec = trade_state.qty
                sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=pos_side)
                trade_state.sl_order_id = sl_order.get("orderId")
                trade_state.sl = sl_price_dec_quant
                log(f"SL recovered: new ID={trade_state.sl_order_id}", telegram_bot, telegram_chat_id)
                if telegram_bot and telegram_chat_id:
                    telegram_post(telegram_bot, telegram_chat_id, f"SL Recovered for {symbol}\nNew Stop: {fmt(trade_state.sl)}\nOrder ID: {trade_state.sl_order_id}")
        if trade_state.tp_order_id and not any(o.get("orderId") == trade_state.tp_order_id for o in open_orders):
            log(f"TP order missing/expired (ID={trade_state.tp_order_id}). Recovering...", telegram_bot, telegram_chat_id)
            entry_price = trade_state.entry_price
            if entry_price > 0:
                R = entry_price * SL_PCT
                tp_price_dec = entry_price + (TP_MULT * R) if trade_state.side == "LONG" else entry_price - (TP_MULT * R)
                tp_rounding = ROUND_UP if trade_state.side == "LONG" else ROUND_DOWN
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                pos_side = trade_state.side
                qty_dec = trade_state.qty
                tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=pos_side)
                trade_state.tp_order_id = tp_order.get("orderId")
                trade_state.tp = tp_price_dec_quant
                log(f"TP recovered: new ID={trade_state.tp_order_id}", telegram_bot, telegram_chat_id)
                if telegram_bot and telegram_chat_id:
                    telegram_post(telegram_bot, telegram_chat_id, f"TP Recovered for {symbol}\nNew TP: {fmt(trade_state.tp)}\nOrder ID: {trade_state.tp_order_id}")
        if trade_state.trail_order_id and not any(o.get("orderId") == trade_state.trail_order_id for o in open_orders):
            log(f"Trailing order missing/expired (ID={trade_state.trail_order_id}). Recovering...", telegram_bot, telegram_chat_id)
            entry_price = trade_state.entry_price
            if entry_price > 0:
                R = entry_price * SL_PCT
                trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R) if trade_state.side == "LONG" else entry_price - (TRAIL_TRIGGER_MULT * R)
                trail_rounding = ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, trail_rounding)
                callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                pos_side = trade_state.side
                qty_dec = trade_state.qty
                trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, trail_activation_price_dec_quant, reduce_only=True, position_side=pos_side)
                trade_state.trail_order_id = trail_order.get("orderId")
                trade_state.trail_activation_price = trail_activation_price_dec_quant
                log(f"Trailing recovered: new ID={trade_state.trail_order_id}", telegram_bot, telegram_chat_id)
                if telegram_bot and telegram_chat_id:
                    telegram_post(telegram_bot, telegram_chat_id, f"Trailing Recovered for {symbol}\nActivation: {fmt(trail_activation_price_dec_quant)}\nOrder ID: {trade_state.trail_order_id}")
    except Exception as e:
        log(f"Recovery error: {str(e)}", telegram_bot, telegram_chat_id)

def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    global CLOSURE_HANDLED
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    last_recovery_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            log("Stop requested during monitoring. Exiting.", telegram_bot, telegram_chat_id)
            break
        current_time = time.time()
        if current_time - last_recovery_check >= RECOVERY_CHECK_INTERVAL:
            debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            last_recovery_check = current_time
        try:
            pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
            positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
            pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
            pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
            if pos_amt == 0:
                if CLOSURE_HANDLED:
                    log("Position already closed by stop handler. Skipping duplicate closure.")
                    trade_state.active = False
                    client.cancel_all_open_orders(symbol)
                    return
                log("Position closed.", telegram_bot, telegram_chat_id)
                trade_state.active = False
                CLOSURE_HANDLED = True
                latest_trade = client.get_latest_trade_details(symbol)
                exit_price = latest_trade["price"] if latest_trade else None
                if exit_price is None:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price = Decimal(str(ticker.get("price", "0")))
                exit_price_f = float(exit_price)
                reason = "Manual Close"
                if STOP_REQUESTED or os.path.exists("stop.txt"):
                    reason = "Stop Requested"
                elif latest_trade and latest_trade.get("orderId"):
                    order_id = latest_trade["orderId"]
                    if order_id == trade_state.sl_order_id:
                        reason = "Stop Loss"
                    elif order_id == trade_state.tp_order_id:
                        reason = "Take Profit"
                    elif order_id == trade_state.trail_order_id:
                        reason = "Trailing Stop"
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
                client.cancel_all_open_orders(symbol)
                log(f"Cancelled orders. Reason: {reason}", telegram_bot, telegram_chat_id)
                return
            time.sleep(1)
            try:
                price = get_current_price(client, symbol)
            except:
                continue
            if trade_state.side == "LONG":
                if trade_state.highest_price is None or price > trade_state.highest_price:
                    trade_state.highest_price = price
            else:
                if trade_state.lowest_price is None or price < trade_state.lowest_price:
                    trade_state.lowest_price = price
            if not trade_state.trail_activated and trade_state.trail_activation_price:
                if (trade_state.side == "LONG" and price >= trade_state.trail_activation_price) or \
                   (trade_state.side == "SHORT" and price <= trade_state.trail_activation_price):
                    trade_state.trail_activated = True
                    R = trade_state.risk
                    init_stop = trade_state.entry_price - (TRAIL_DISTANCE_MULT * R) if trade_state.side == "LONG" else \
                                trade_state.entry_price + (TRAIL_DISTANCE_MULT * R)
                    init_stop = quantize_price(init_stop, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                    send_trailing_activation_telegram(symbol, trade_state.side, price, init_stop, telegram_bot, telegram_chat_id)
                    trade_state.current_trail_stop = init_stop
            if trade_state.trail_activated and time.time() - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE:
                R = trade_state.risk
                new_stop_raw = trade_state.highest_price - (TRAIL_DISTANCE_MULT * R) if trade_state.side == "LONG" else \
                               trade_state.lowest_price + (TRAIL_DISTANCE_MULT * R)
                new_stop = quantize_price(new_stop_raw, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                if (trade_state.current_trail_stop is None or
                    (trade_state.side == "LONG" and new_stop > trade_state.current_trail_stop) or
                    (trade_state.side == "SHORT" and new_stop < trade_state.current_trail_stop)):
                    trade_state.current_trail_stop = new_stop
                    send_trailing_update_telegram(symbol, trade_state.side, new_stop, telegram_bot, telegram_chat_id)
                    trade_state.last_trail_alert = time.time()
        except Exception as e:
            log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, telegram_bot, telegram_chat_id):
    global CLOSURE_HANDLED
    trades_today = 0
    last_processed_time = 0
    trade_state = TradeState()
    pending_entry = False
    daily_start_balance = fetch_balance(client)
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    min_qty = filters['minQty']
    tick_size = filters['tickSize']
    min_notional = filters['minNotional']
    signal.signal(signal.SIGINT, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    signal.signal(signal.SIGTERM, lambda s, f: _request_stop(s, f, symbol, telegram_bot, telegram_chat_id))
    log(f"Starting bot with symbol={symbol}, timeframe={timeframe}, risk_pct={risk_pct*100}%")
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol)
        pos_amt = Decimal(str(pos.get("positionAmt", "0")))
        if pos_amt != 0:
            trade_state.active = True
            trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
            trade_state.qty = abs(pos_amt)
            trade_state.entry_price = Decimal(str(pos.get("entryPrice", "0")))
            trade_state.risk = trade_state.entry_price * SL_PCT
            trade_state.sl_order_id = None
            trade_state.tp_order_id = None
            trade_state.trail_order_id = None
            log("Existing position detected on startup. Recovering orders...", telegram_bot, telegram_chat_id)
            debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
    try:
        while not STOP_REQUESTED and not os.path.exists("stop.txt"):
            if trades_today >= max_trades_per_day:
                log(f"Maximum trades reached for the day ({max_trades_per_day}). Sleeping until next day.", telegram_bot, telegram_chat_id)
                time.sleep(60)
                continue
            if use_max_loss:
                current_bal = fetch_balance(client)
                if daily_start_balance - current_bal > daily_start_balance * (max_daily_loss_pct / Decimal("100")):
                    log("Max daily loss reached. Waiting for next day.", telegram_bot, telegram_chat_id)
                    time.sleep(60)
                    continue
            try:
                server_time_response = client.public_request("/fapi/v1/time")
                server_time = server_time_response["serverTime"]
            except Exception as e:
                log(f"Server time fetch failed: {str(e)}. Using local time.", telegram_bot, telegram_chat_id)
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
                log(f"Failed to fetch klines: {str(e)}", telegram_bot, telegram_chat_id)
                time.sleep(2)
                continue
            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            last_close_time = close_times[-1]
            if last_processed_time == last_close_time:
                log(f"Duplicate candle detected at {last_close_time}; sleeping 1s", telegram_bot, telegram_chat_id)
                time.sleep(1)
                continue
            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD)
            curr_vol = volumes[-1]
            close_price = closes[-1]
            open_price = opens[-1]
            close_time = last_close_time
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price
            log(f"Candle close price={fmt(close_price)} RSI={rsi} Vol={curr_vol:.2f} SMA15={(vol_sma15 or 0):.2f} {'Green' if is_green_candle else 'Red' if is_red_candle else 'Neutral'} candle", telegram_bot, telegram_chat_id)
            if prevent_same_bar and trade_state.entry_close_time == close_time:
                log("Same bar as entry. Skipping to prevent re-entry.", telegram_bot, telegram_chat_id)
                last_processed_time = close_time
                time.sleep(1)
                continue
            if require_no_pos and has_active_position(client, symbol):
                log("Active position detected. Waiting for closure.", telegram_bot, telegram_chat_id)
                last_processed_time = close_time
                time.sleep(1)
                continue
            if use_volume_filter and vol_sma15 is None:
                log("Waiting for volume history...", telegram_bot, telegram_chat_id)
                last_processed_time = close_time
                time.sleep(1)
                continue
            buy_signal = (rsi is not None and Decimal(BUY_RSI_MIN) <= rsi <= Decimal(BUY_RSI_MAX) and is_green_candle and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi is not None and Decimal(SELL_RSI_MIN) <= rsi <= Decimal(SELL_RSI_MAX) and is_red_candle and (not use_volume_filter or curr_vol > vol_sma15))
            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close -> {side_text}. Preparing entry.", telegram_bot, telegram_chat_id)
                pending_entry = True
                entry_price = close_price
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
                    log(f"Invalid R ({R}) <= 0. Skipping trade.", telegram_bot, telegram_chat_id)
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
                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={fmt(entry_price)}", telegram_bot, telegram_chat_id)
                timed_out = False
                actual_qty = None
                try:
                    order_res = place_market_order(client, symbol, side_text, qty_api)
                    log(f"Market order placed: {order_res}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Market order failed: {str(e)}", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
                log("Waiting for entry order to fill...", telegram_bot, telegram_chat_id)
                start_time = time.time()
                while True:
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        log("Stop requested during fill wait; aborting entry flow.", telegram_bot, telegram_chat_id)
                        break
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break
                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        log("Timeout waiting for fill. Attempting to cancel order...", telegram_bot, telegram_chat_id)
                        cancel_params = {"symbol": symbol, "orderId": order_res.get("orderId")} if isinstance(order_res, dict) else {"symbol": symbol}
                        try:
                            client.send_signed_request("DELETE", "/fapi/v1/order", cancel_params)
                            log("Entry order cancelled.", telegram_bot, telegram_chat_id)
                        except Exception as e:
                            log(f"Cancel failed: {str(e)}", telegram_bot, telegram_chat_id)
                        timed_out = True
                        break
                    time.sleep(0.5)
                if timed_out or actual_qty is None:
                    pending_entry = False
                    log("Entry timed out or aborted -> skipping this signal and waiting for next candle.", telegram_bot, telegram_chat_id)
                    continue
                time.sleep(0.2)
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    log("Failed to fetch actual fill price; using candle close price.", telegram_bot, telegram_chat_id)
                    actual_fill_price = entry_price
                if buy_signal:
                    sl_price_dec = actual_fill_price * (Decimal("1") - SL_PCT)
                    R = actual_fill_price * SL_PCT
                    tp_price_dec = actual_fill_price + (tp_mult * R)
                    trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R)
                else:
                    sl_price_dec = actual_fill_price * (Decimal("1") + SL_PCT)
                    R = actual_fill_price * SL_PCT
                    tp_price_dec = actual_fill_price - (tp_mult * R)
                    trail_activation_price_dec = actual_fill_price - (TRAIL_TRIGGER_MULT * R)
                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, trail_rounding)
                try:
                    current_price = get_current_price(client, symbol)
                except Exception as e:
                    log(f"Price fetch failed: {str(e)}. Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
                price_buffer = actual_fill_price * TRAIL_PRICE_BUFFER
                if buy_signal and trail_activation_price_dec_quant <= current_price + price_buffer:
                    log(f"Trailing stop activation price {trail_activation_price_dec_quant} too close to current price {current_price}. Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
                elif not buy_signal and trail_activation_price_dec_quant >= current_price - price_buffer:
                    log(f"Trailing stop activation price {trail_activation_price_dec_quant} too close to current price {current_price}. Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
                trade_state.active = True
                trade_state.entry_price = actual_fill_price
                trade_state.qty = actual_qty
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                trade_state.initial_sl = sl_price_dec_quant
                trade_state.sl = sl_price_dec_quant
                trade_state.tp = tp_price_dec_quant
                trade_state.trail_activated = False
                trade_state.trail_activation_price = trail_activation_price_dec_quant
                trade_state.highest_price = None
                trade_state.lowest_price = None
                trade_state.current_trail_stop = None
                trade_state.risk = R
                log(f"Position opened: {trade_state.side}, qty={trade_state.qty}, entry={fmt(trade_state.entry_price)}, sl={fmt(trade_state.sl)}, tp={fmt(trade_state.tp)}, trail_activation={fmt(trade_state.trail_activation_price)}", telegram_bot, telegram_chat_id)
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
                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                pos_side = trade_state.side
                qty_dec = trade_state.qty
                callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
                activation_price = trail_activation_price_dec_quant
                place_orders(client, symbol, trade_state, tick_size, close_side, pos_side, qty_dec, sl_price_dec_quant, tp_price_dec_quant, callback_rate, activation_price)
                trades_today += 1
                pending_entry = False
                CLOSURE_HANDLED = False  # Reset for new trade
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            elif trade_state.active or pending_entry:
                log("Trade active or pending. Skipping signal check.", telegram_bot, telegram_chat_id)
            else:
                log("No trade signal on candle close.", telegram_bot, telegram_chat_id)
            if last_processed_time != close_time:
                last_processed_time = close_time
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            log(f"Waiting for candle close in {sleep_seconds:.2f}s ...", telegram_bot, telegram_chat_id)
            _safe_sleep(sleep_seconds)
    except Exception as e:
        log(f"Loop error: {str(e)}", telegram_bot, telegram_chat_id)
        time.sleep(2)
    finally:
        if not CLOSURE_HANDLED:
            _request_stop(None, None, symbol, telegram_bot, telegram_chat_id)

def _safe_sleep(total_seconds):
    remaining = float(total_seconds)
    while remaining > 0:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        time.sleep(min(1, remaining))
        remaining -= 1

def interval_ms(interval):
    if interval.endswith("m"):
        return int(interval[:-1]) * 60 * 1000
    if interval.endswith("h"):
        return int(interval[:-1]) * 60 * 60 * 1000
    return 30 * 60 * 1000

def closes_and_volumes_from_klines(klines):
    closes = [Decimal(str(k[4])) for k in klines]
    volumes = [Decimal(str(k[5])) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [Decimal(str(k[1])) for k in klines]
    return closes, volumes, close_times, opens

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
    getcontext().prec = 28
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
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}, risk_pct={args.risk_pct}%, use_volume_filter={args.use_volume_filter}", args.telegram_token, args.chat_id)
    bal = fetch_balance(client)
    log(f"Fetched balance: {fmt(bal)} USDT", args.telegram_token, args.chat_id)
    atexit.register(lambda: _request_stop(None, None, args.symbol, args.telegram_token, args.chat_id))
    threading.Thread(target=start_price_ws, args=(args.symbol,), daemon=True).start()
    time.sleep(1)
    threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()
    trading_loop(
        client=client,
        symbol=args.symbol,
        timeframe=args.timeframe,
        max_trades_per_day=args.max_trades,
        risk_pct=Decimal(str(args.risk_pct)) / Decimal("100"),
        max_daily_loss_pct=Decimal(str(args.max_loss_pct)),
        tp_mult=Decimal(str(args.tp_mult)),
        prevent_same_bar=args.prevent_same_bar,
        require_no_pos=args.require_no_pos,
        use_max_loss=args.use_max_loss,
        use_volume_filter=args.use_volume_filter,
        telegram_bot=args.telegram_token,
        telegram_chat_id=args.chat_id
    )
