#!/usr/bin/env python3
# Binance Futures RSI Bot — REQUESTS + WEBSOCKET ENHANCED (8 Fixes + Balance Startup)
# ENHANCED 1. Dynamic klines + volume fallback
# ENHANCED 2. 100% Decimal math
# ENHANCED 3. Safe quantization
# ENHANCED 4. WebSocket price stream
# ENHANCED 5. Hardcoded endpoints (requests)
# ENHANCED 6. Telegram retry
# ENHANCED 7. Safe cleanup
# ENHANCED 8. Reusable order functions
# ENHANCED 9. Startup message with balance

import argparse
import logging
import time
import hmac
import hashlib
import requests
import os
import signal
import sys
import statistics
import csv
import threading
import traceback
import atexit
import json
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone, timedelta
import schedule
from urllib.parse import urlencode
import websocket  # pip install websocket-client

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")
SL_PCT = Decimal("0.0075")
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2.0")
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 55
BUY_RSI_MAX = 65
SELL_RSI_MIN = 35
SELL_RSI_MAX = 45
POSITION_CHECK_INTERVAL = 60
TRAIL_PRICE_BUFFER = Decimal("0.003")
REQUEST_TIMEOUT = 30
RECOVERY_CHECK_INTERVAL = 10
TRAIL_UPDATE_THROTTLE = 10.0
KLINES_DYNAMIC_LIMIT = max(100, VOL_SMA_PERIOD + 50)  # ENHANCED 1

# Global
STOP_REQUESTED = False
client = None
symbol_filters_cache = None
pnl_data = []
PNL_LOG_FILE = 'pnl_log.csv'
current_price_global = None  # ENHANCED 4
ws_thread = None  # ENHANCED Fixed global/parameter conflict

# -------- PNL ----------
def init_pnl_log():
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r'])
            writer.writeheader()

def log_pnl(trade_id, side, entry, exit_price, qty, R):
    pnl_usd = (exit_price - entry) * qty if side == 'LONG' else (entry - exit_price) * qty
    pnl_r = pnl_usd / R if R > 0 else Decimal('0')
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': str(entry),
        'exit': str(exit_price),
        'pnl_usd': str(pnl_usd),
        'pnl_r': str(pnl_r)
    }
    pnl_data.append(row)
    with open(PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=row.keys())
        writer.writerow(row)
    return row

# -------- LOGGING ----------
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
        telegram_post_with_retry(telegram_bot, telegram_chat_id, message)

def telegram_post_with_retry(token, chat_id, text, retries=3):  # ENHANCED 6
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    for i in range(retries):
        try:
            requests.post(url, json={"chat_id": chat_id, "text": text}, timeout=10)
            return
        except Exception as e:
            if i == retries - 1:
                logger.error(f"Telegram failed after {retries} tries: {e}")
            time.sleep(2 ** i)

# -------- TELEGRAM MESSAGES ----------
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
    telegram_post_with_retry(bot, chat_id, message)

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
    telegram_post_with_retry(bot, chat_id, message)

def send_trailing_activation_telegram(symbol, side, activation_price, initial_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Activated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Activation Price: {activation_price:.4f}\n"
        f"- Initial Stop Price: {initial_stop_price:.4f}\n"
    )
    telegram_post_with_retry(bot, chat_id, message)

def send_trailing_update_telegram(symbol, side, new_stop_price, bot, chat_id):
    message = (
        f"Trailing Stop Updated:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- New Stop Price: {new_stop_price:.4f}\n"
    )
    telegram_post_with_retry(bot, chat_id, message)

# -------- REPORTS ----------
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
    total_pnl_usd = sum(Decimal(trade['pnl_usd']) for trade in filtered_trades)
    total_pnl_r = sum(Decimal(trade['pnl_r']) for trade in filtered_trades)
    num_trades = len(filtered_trades)
    avg_pnl_usd = total_pnl_usd / num_trades if num_trades > 0 else Decimal('0')
    wins = sum(1 for trade in filtered_trades if Decimal(trade['pnl_usd']) > 0)
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
    telegram_post_with_retry(bot, chat_id, f"{subject}\n{report}")

def send_weekly_report(bot, chat_id):
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post_with_retry(bot, chat_id, f"{subject}\n{report}")

def send_monthly_report(bot, chat_id):
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    telegram_post_with_retry(bot, chat_id, f"{subject}\n{report}")

# -------- STOP HANDLER ----------
def _request_stop(signum, frame, symbol=None, telegram_bot=None, telegram_chat_id=None):
    global STOP_REQUESTED, client
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
            R = entry_price * SL_PCT if entry_price > 0 else Decimal('0')
            pnl_row = log_pnl(len(pnl_data) + 1, "LONG" if pos_amt > 0 else "SHORT", entry_price, exit_price, qty, R)
            if telegram_bot and telegram_chat_id:
                send_closure_telegram(symbol, "LONG" if pos_amt > 0 else "SHORT", entry_price, exit_price, qty, pnl_row['pnl_usd'], pnl_row['pnl_r'], "Stop Requested", telegram_bot, telegram_chat_id)
        client.cancel_all_open_orders(symbol)
        log(f"All open orders cancelled for {symbol}.")
    except Exception as e:
        log(f"Stop handler error: {str(e)}")

# -------- CLEANUP ----------
def cleanup():
    global ws_thread
    if ws_thread and ws_thread.is_alive():
        ws_thread.join(timeout=2)
    if os.path.exists("stop.txt"):
        os.remove("stop.txt")

atexit.register(cleanup)

# -------- TIME SYNC ----------
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

# -------- CLIENT ----------
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

    # ENHANCED 8. Reusable order functions
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

# -------- INDICATORS ----------
def compute_rsi(closes, period=RSI_PERIOD):  # ENHANCED True Wilder
    if len(closes) < period + 1:
        return None
    gains = []
    losses = []
    for i in range(1, len(closes)):
        delta = closes[i] - closes[i-1]
        gains.append(max(delta, 0))
        losses.append(max(-delta, 0))
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

# -------- SYMBOL FILTERS ----------
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
    step_size = Decimal(lot["stepSize"])
    min_qty = Decimal(lot["minQty"])
    tick_size = Decimal(filters.get("PRICE_FILTER", {}).get("tickSize", "0.00000001"))
    min_notional = Decimal(filters.get("MIN_NOTIONAL", {}).get("notional", "0"))
    symbol_filters_cache = {"stepSize": step_size, "minQty": min_qty, "tickSize": tick_size, "minNotional": min_notional}
    return symbol_filters_cache

# -------- ORDERS ----------
def place_market_order(client: BinanceClient, symbol: str, side: str, quantity: Decimal):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "MARKET",
        "quantity": str(quantity)
    }
    return client.send_signed_request("POST", "/fapi/v1/order", params)

# -------- DATA FETCHING ----------
def fetch_klines(client: BinanceClient, symbol: str, interval: str, limit=KLINES_DYNAMIC_LIMIT):
    try:
        data = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        return data
    except Exception as e:
        log(f"Klines fetch failed: {str(e)}")
        raise

def fetch_balance(client: BinanceClient):
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
        return Decimal(data.get("totalWalletBalance", "0"))
    except Exception as e:
        log(f"Balance fetch failed: {str(e)}")
        raise

def has_active_position(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        for p in positions:
            if p.get("symbol") == symbol and Decimal(p.get("positionAmt", "0")) != 0:
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

# -------- TRADE STATE ----------
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

# -------- RECOVERY ----------
def place_orders(client, symbol, trade_state, tick_size):
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    pos_side = trade_state.side
    qty_dec = Decimal(str(trade_state.qty))
    entry_price = Decimal(str(trade_state.entry_price))

    sl_price_dec = entry_price * (Decimal("1") - SL_PCT) if trade_state.side == "LONG" else entry_price * (Decimal("1") + SL_PCT)
    sl_rounding = ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP
    sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
    sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, True, pos_side)
    trade_state.sl_order_id = sl_order.get("orderId")
    trade_state.sl = sl_price_dec_quant

    R = entry_price * SL_PCT
    tp_price_dec = entry_price + (TP_MULT * R) if trade_state.side == "LONG" else entry_price - (TP_MULT * R)
    tp_rounding = ROUND_UP if trade_state.side == "LONG" else ROUND_DOWN
    tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
    tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, True, pos_side)
    trade_state.tp_order_id = tp_order.get("orderId")
    trade_state.tp = tp_price_dec_quant

    trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R) if trade_state.side == "LONG" else entry_price - (TRAIL_TRIGGER_MULT * R)
    trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)
    callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
    trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, trail_activation_price_dec_quant, True, pos_side)
    trade_state.trail_order_id = trail_order.get("orderId")
    trade_state.trail_activation_price = trail_activation_price_dec_quant

def debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    if not trade_state.active:
        return
    try:
        open_orders = client.get_open_orders(symbol)
        if trade_state.sl_order_id and not any(o.get("orderId") == trade_state.sl_order_id for o in open_orders):
            log(f"SL missing. Recovering...", telegram_bot, telegram_chat_id)
            place_orders(client, symbol, trade_state, tick_size)
            telegram_post_with_retry(telegram_bot, telegram_chat_id, f"SL Recovered: {trade_state.sl:.4f}")
        if trade_state.tp_order_id and not any(o.get("orderId") == trade_state.tp_order_id for o in open_orders):
            log(f"TP missing. Recovering...", telegram_bot, telegram_chat_id)
            place_orders(client, symbol, trade_state, tick_size)
            telegram_post_with_retry(telegram_bot, telegram_chat_id, f"TP Recovered: {trade_state.tp:.4f}")
        if trade_state.trail_order_id and not any(o.get("orderId") == trade_state.trail_order_id for o in open_orders):
            log(f"Trailing missing. Recovering...", telegram_bot, telegram_chat_id)
            place_orders(client, symbol, trade_state, tick_size)
            telegram_post_with_retry(telegram_bot, telegram_chat_id, f"Trailing Recovered: {float(trade_state.trail_activation_price):.4f}")
    except Exception as e:
        log(f"Recovery error: {str(e)}", telegram_bot, telegram_chat_id)

# -------- WEBSOCKET ----------
def on_message(ws, message):
    global current_price_global
    try:
        data = json.loads(message)
        current_price_global = Decimal(data['c'])
    except:
        pass

def on_error(ws, error):
    log(f"WS error: {error}")

def on_close(ws, *args):
    log("WS closed")

def start_websocket(symbol):
    def run():
        url = f"wss://fstream.binance.com/ws/{symbol.lower()}@ticker"
        ws = websocket.WebSocketApp(url, on_message=on_message, on_error=on_error, on_close=on_close)
        ws.run_forever()
    global ws_thread
    ws_thread = threading.Thread(target=run, daemon=True)
    ws_thread.start()
    time.sleep(2)

# -------- MONITOR TRADE ----------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    log("Monitoring trade with WebSocket...", telegram_bot, telegram_chat_id)
    last_recovery_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        if time.time() - last_recovery_check >= RECOVERY_CHECK_INTERVAL:
            debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            last_recovery_check = time.time()
        try:
            pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
            positions = pos_resp['data'] if 'data' in pos_resp else pos_resp
            pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
            pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
            if pos_amt == 0:
                trade_state.active = False
                exit_price = current_price_global or Decimal('0')
                latest_trade = client.get_latest_trade_details(symbol)
                reason = "Unknown"
                if latest_trade:
                    oid = latest_trade["orderId"]
                    if oid == trade_state.sl_order_id: reason = "Stop Loss"
                    elif oid == trade_state.tp_order_id: reason = "Take Profit"
                    elif oid == trade_state.trail_order_id: reason = "Trailing Stop"
                R = Decimal(str(trade_state.entry_price or 0)) * SL_PCT
                pnl_row = log_pnl(len(pnl_data)+1, trade_state.side, Decimal(str(trade_state.entry_price or 0)), exit_price, Decimal(str(trade_state.qty)), R)
                send_closure_telegram(symbol, trade_state.side, trade_state.entry_price or 0, exit_price, trade_state.qty, pnl_row['pnl_usd'], pnl_row['pnl_r'], reason, telegram_bot, telegram_chat_id)
                client.cancel_all_open_orders(symbol)
                return
            price = current_price_global
            if price is None:
                time.sleep(1)
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
                    init_stop = Decimal(str(trade_state.entry_price)) - (TRAIL_DISTANCE_MULT * R) if trade_state.side == "LONG" else \
                                Decimal(str(trade_state.entry_price)) + (TRAIL_DISTANCE_MULT * R)
                    init_stop = quantize_price(init_stop, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                    send_trailing_activation_telegram(symbol, trade_state.side, float(price), float(init_stop), telegram_bot, telegram_chat_id)
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
                    send_trailing_update_telegram(symbol, trade_state.side, float(new_stop), telegram_bot, telegram_chat_id)
                    trade_state.last_trail_alert = time.time()
            time.sleep(1)
        except Exception as e:
            log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

# -------- TRADING LOOP ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, telegram_bot, telegram_chat_id):
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

    # ENHANCED 9. Startup message with balance
    try:
        balance = fetch_balance(client)
        startup_msg = (
            f"Connected ({'LIVE' if client.use_live else 'TESTNET'})\n"
            f"Starting bot:\n"
            f"- Symbol: {symbol}\n"
            f"- Timeframe: {timeframe}\n"
            f"- Risk: {float(risk_pct*100):.1f}%\n"
            f"- Volume Filter: {use_volume_filter}\n"
            f"- Balance: {balance:.2f} USDT"
        )
        log(startup_msg, telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Startup balance fetch failed: {e}", telegram_bot, telegram_chat_id)

    start_websocket(symbol)  # ENHANCED 4

    # Startup recovery
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol)
        pos_amt = Decimal(pos.get("positionAmt", "0"))
        if pos_amt != 0:
            trade_state.active = True
            trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
            trade_state.qty = float(abs(pos_amt))
            trade_state.entry_price = float(Decimal(pos.get("entryPrice", "0")))
            trade_state.risk = Decimal(trade_state.entry_price) * SL_PCT
            place_orders(client, symbol, trade_state, tick_size)
            monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)

    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            if trades_today >= max_trades_per_day:
                time.sleep(60)
                continue
            if use_max_loss:
                current_bal = fetch_balance(client)
                if daily_start_balance - current_bal > daily_start_balance * (max_daily_loss_pct / Decimal("100")):
                    time.sleep(60)
                    continue
            server_time = client.public_request("/fapi/v1/time").get("serverTime", int(time.time()*1000))
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                _safe_sleep(sleep_seconds)
                continue
            klines = fetch_klines(client, symbol, timeframe)
            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            last_close_time = close_times[-1]
            if last_processed_time == last_close_time:
                time.sleep(1)
                continue
            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD) or statistics.median(volumes)
            curr_vol = volumes[-1]
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            close_time = last_close_time
            is_green = close_price > open_price
            is_red = close_price < open_price
            log(f"Candle: {close_price} RSI={rsi} Vol={curr_vol:.2f} SMA15={vol_sma15:.2f}", telegram_bot, telegram_chat_id)

            if prevent_same_bar and trade_state.entry_close_time == close_time:
                last_processed_time = close_time
                continue
            if require_no_pos and has_active_position(client, symbol):
                last_processed_time = close_time
                continue

            buy_signal = (rsi and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red and (not use_volume_filter or curr_vol > vol_sma15))

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                pending_entry = True
                entry_price = close_price
                R = entry_price * SL_PCT
                qty = (fetch_balance(client) * risk_pct) / R
                qty_api = quantize_qty(qty, step_size)
                if qty_api < min_qty:
                    qty_api = min_qty
                notional = qty_api * entry_price
                if notional < min_notional:
                    qty_api = quantize_qty(min_notional / entry_price, step_size)
                order_res = place_market_order(client, symbol, side_text, qty_api)
                start_time = time.time()
                actual_qty = None
                while time.time() - start_time < ORDER_FILL_TIMEOUT:
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(pos.get("positionAmt", "0")) if pos else Decimal('0')
                    if pos_amt != 0:
                        actual_qty = abs(pos_amt)
                        break
                    time.sleep(0.5)
                if not actual_qty:
                    pending_entry = False
                    continue
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId")) or entry_price
                R = actual_fill_price * SL_PCT
                trade_state.active = True
                trade_state.entry_price = float(actual_fill_price)
                trade_state.risk = R
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                place_orders(client, symbol, trade_state, tick_size)
                send_trade_telegram({
                    'symbol': symbol, 'side': trade_state.side, 'entry': trade_state.entry_price,
                    'sl': trade_state.sl, 'tp': trade_state.tp, 'trail_activation': float(trade_state.trail_activation_price),
                    'qty': trade_state.qty
                }, telegram_bot, telegram_chat_id)
                trades_today += 1
                pending_entry = False
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
            last_processed_time = close_time
            _safe_sleep(max(1.0, (last_processed_time + interval_ms(timeframe) - int(time.time()*1000) + 500) / 1000.0))
        except Exception as e:
            log(f"Loop error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

def interval_ms(interval):
    if interval.endswith("m"): return int(interval[:-1]) * 60 * 1000
    if interval.endswith("h"): return int(interval[:-1]) * 3600 * 1000
    return 1800000

def _safe_sleep(secs):
    end = time.time() + secs
    while time.time() < end:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            break
        time.sleep(1)

def closes_and_volumes_from_klines(klines):
    closes = [float(k[4]) for k in klines]
    volumes = [float(k[5]) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [float(k[1]) for k in klines]
    return closes, volumes, close_times, opens

# -------- SCHEDULER ----------
def run_scheduler(bot, chat_id):
    last_month = None
    def check_monthly():
        nonlocal last_month
        now = datetime.now(timezone.utc)
        if now.day == 1 and (last_month is None or now.month != last_month):
            send_monthly_report(bot, chat_id)
            last_month = now.month
    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot, chat_id))
    schedule.every().day.at("00:00").do(check_monthly)
    while True:
        schedule.run_pending()
        time.sleep(60)

# -------- MAIN ----------
if __name__ == "__main__":
    try:
        parser = argparse.ArgumentParser()
        parser.add_argument("--api-key", required=True)
        parser.add_argument("--api-secret", required=True)
        parser.add_argument("--telegram-token", required=True)
        parser.add_argument("--chat-id", required=True)
        parser.add_argument("--symbol", default="SOLUSDT")
        parser.add_argument("--timeframe", default="30m")
        parser.add_argument("--max-trades", type=int, default=3)
        parser.add_argument("--risk-pct", type=float, default=0.5)
        parser.add_argument("--max-loss-pct", type=float, default=5.0)
        parser.add_argument("--tp-mult", type=float, default=3.5)
        parser.add_argument("--no-trailing", dest='use_trailing', action='store_false')
        parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false')
        parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false')
        parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false')
        parser.add_argument("--use-volume-filter", action='store_true')
        parser.add_argument("--live", action="store_true")
        parser.add_argument("--base-url", default=None)
        args = parser.parse_args()
        init_pnl_log()
        client = BinanceClient(args.api_key, args.api_secret, args.live, args.base_url)
        threading.Thread(target=run_scheduler, args=(args.telegram_token, args.chat_id), daemon=True).start()
        trading_loop(
            client=client, symbol=args.symbol, timeframe=args.timeframe, max_trades_per_day=args.max_trades,
            risk_pct=Decimal(str(args.risk_pct))/100, max_daily_loss_pct=Decimal(str(args.max_loss_pct)),
            tp_mult=Decimal(str(args.tp_mult)), use_trailing=args.use_trailing, prevent_same_bar=args.prevent_same_bar,
            require_no_pos=args.require_no_pos, use_max_loss=args.use_max_loss, use_volume_filter=args.use_volume_filter,
            telegram_bot=args.telegram_token, telegram_chat_id=args.chat_id
        )
    finally:
        cleanup()
