#!/usr/bin/env python3
# bot.py
# Optimized Binance Futures RSI bot for 5m timeframe with manual trailing stop and Telegram notifications
# Changes:
# - Ensured synchronous Telegram calls for python-telegram-bot==13.7
# - Added detailed position logging in has_active_position
# - Fixed positionSide inclusion to only apply in Hedge Mode to resolve -4061 error
# - Implemented manual trailing stop logic: activates at 1.25 R, initial stop at 0.25 R above initial SL, trails 2 R behind
# - Increased recvWindow from 15000 to 30000 to address -1021 timestamp errors

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
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone
from urllib.parse import urlencode
import telegram

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")          # 0.5% per trade
SL_PCT = Decimal("0.0075")           # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2.0")
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "5m"
ORDER_FILL_TIMEOUT = 10  # seconds
BUY_RSI_MIN = 50
BUY_RSI_MAX = 70
SELL_RSI_MIN = 30
SELL_RSI_MAX = 50
CALLBACK_RATE_MIN = Decimal("0.1")   # Binance minimum callbackRate (percent)
CALLBACK_RATE_MAX = Decimal("5.0")   # safety cap
POSITION_CHECK_INTERVAL = 30         # seconds, for API efficiency
TRAIL_PRICE_BUFFER = Decimal("0.002")  # 0.2% buffer to avoid -2021 errors

# Global stop flag and client
STOP_REQUESTED = False
client = None
symbol_filters_cache = None

def _request_stop(signum, frame, symbol=None):
    global STOP_REQUESTED, client
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    try:
        if client and symbol:
            pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 30000})
            pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
            if pos_amt != 0:
                side = "SELL" if pos_amt > 0 else "BUY"
                qty = abs(pos_amt)
                try:
                    params = {
                        "symbol": symbol,
                        "side": side,
                        "type": "MARKET",
                        "quantity": str(qty),
                        "recvWindow": 30000
                    }
                    if client.dual_side:
                        params["positionSide"] = "LONG" if side == "BUY" else "SHORT"
                    client.send_signed_request("POST", "/fapi/v1/order", params)
                    log(f"Closed position: qty={qty} {side}")
                except Exception as e:
                    log(f"Failed to close position: {str(e)}")
            client.cancel_all_open_orders(symbol)
            log(f"All open orders cancelled for {symbol}.")
        else:
            log("Client or symbol not defined; skipping position closure and order cancellation.")
    except Exception as e:
        log(f"Failed to handle stop: {str(e)}")

# -------- TIME SYNC CHECK ----------
def check_time_offset(base_url):
    try:
        response = requests.get(f"{base_url}/fapi/v1/time", timeout=5)
        server_time_ms = response.json()['serverTime']
        server_time = datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc)
        local_time = datetime.now(timezone.utc)
        offset = (server_time - local_time).total_seconds()
        log(f"Time offset from Binance: {offset} seconds")
        if abs(offset) > 5:
            log("Warning: Clock offset > 5s. Using recvWindow=30000.")
    except Exception as e:
        log(f"Binance time sync failed: {str(e)}")

# -------- POSITION MODE CHECK ----------
def check_position_mode(client):
    try:
        response = client.send_signed_request("GET", "/fapi/v1/positionSide/dual", {"recvWindow": 30000})
        dual_side = response.get("dualSidePosition", False)
        if dual_side:
            log("Warning: Account is in Hedge Mode. Script assumes One-Way Mode. Consider switching to One-Way Mode in Binance settings.")
        else:
            log("Account is in One-Way Mode, as expected.")
        return dual_side
    except Exception as e:
        log(f"Failed to check position mode: {str(e)}. Assuming One-Way Mode.")
        return False

# -------- BINANCE CLIENT ----------
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
        print(f"🔗 Using base URL: {self.base}")
        check_time_offset(self.base)
        # Determine and enforce position mode. Store in self.dual_side (True if Hedge Mode).
        try:
            resp = None
            try:
                resp = self.send_signed_request("GET", "/fapi/v1/positionSide/dual", {"recvWindow": 30000})
            except Exception:
                resp = None
            self.dual_side = False
            if isinstance(resp, dict):
                self.dual_side = resp.get('dualSidePosition', False)
            if self.dual_side:
                log("Account in Hedge Mode; attempting to switch to One-Way Mode.")
                try:
                    self.send_signed_request("POST", "/fapi/v1/positionSide/dual", {"dualSidePosition": "false", "recvWindow": 30000})
                    self.dual_side = False
                    log("Successfully switched to One-Way Mode.")
                except Exception as e:
                    log(f"Failed to set One-Way Mode: {e}")
        except Exception as e:
            self.dual_side = False
            log(f"Could not determine position mode: {e}. Assuming One-Way Mode.")

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
        for attempt in range(3):
            try:
                r = requests.request(method, url, headers=headers, timeout=20)
                if r.status_code == 200:
                    response = r.json()
                    if isinstance(response, dict) and response.get("code") not in (None, 200):
                        raise BinanceAPIError(f"API error: {response.get('msg', 'Unknown error')} (code {response.get('code')})", status_code=r.status_code, payload=response)
                    return response
                else:
                    try:
                        payload = r.json()
                    except Exception:
                        payload = r.text
                    raise BinanceAPIError(f"HTTP {r.status_code}: {payload}", status_code=r.status_code, payload=payload)
            except BinanceAPIError as e:
                if attempt < 2:
                    time.sleep(2 ** attempt)
                    continue
                raise
            except Exception as e:
                if attempt < 2:
                    time.sleep(2 ** attempt)
                    continue
                raise BinanceAPIError(f"Request failed after retries: {str(e)}", payload=str(e))

    def public_request(self, path: str, params: dict = None):
        url = f"{self.base}{path}"
        for attempt in range(2):
            try:
                r = requests.get(url, params=params, timeout=20, headers={})
                if r.status_code == 200:
                    return r.json()
                else:
                    try:
                        payload = r.json()
                    except Exception:
                        payload = r.text
                    raise BinanceAPIError(f"Public API error: {payload}", status_code=r.status_code, payload=payload)
            except Exception as e:
                time.sleep(1)
                if attempt == 1:
                    raise BinanceAPIError(f"Public API request failed: {str(e)}", payload=str(e))

    def get_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        return self.send_signed_request("GET", "/fapi/v1/openOrders", params)

    def cancel_all_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        return self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", params)

    def get_latest_fill_price(self, symbol: str, order_id: int):
        params = {"symbol": symbol, "orderId": order_id}
        try:
            trades = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            if trades and len(trades) > 0:
                return Decimal(str(trades[-1].get("price", "0")))
            return None
        except BinanceAPIError as e:
            log(f"Failed to fetch fill price: {str(e)}, payload: {e.payload}")
            return None
        except Exception as e:
            log(f"Failed to fetch fill price: {str(e)}")
            return None

# -------- UTILITIES & INDICATORS ----------
def compute_rsi(closes, period=RSI_PERIOD):
    if len(closes) < period + 1:
        return None
    deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    gains = [max(0, d) for d in deltas]
    losses = [abs(min(0, d)) for d in deltas]
    avg_gain = statistics.mean(gains[-period:])
    avg_loss = statistics.mean(losses[-period:])
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    rsi = 100 - (100 / (1 + rs))
    return round(rsi, 2)

def sma(data, period):
    if len(data) < period:
        return None
    return sum(data[-period:]) / period

def quantize_qty(qty, step_size):
    step = Decimal(str(step_size))
    q = (Decimal(str(qty)) // step) * step
    if q == 0:
        q = step
    return q.quantize(step)

def quantize_price(p, tick_size, rounding=ROUND_HALF_EVEN):
    return Decimal(str(p)).quantize(Decimal(str(tick_size)), rounding=rounding)

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
    step_size = Decimal(str(lot["stepSize"]))
    min_qty = Decimal(str(lot["minQty"]))
    tick_size = Decimal(str(filters.get("PRICE_FILTER", {}).get("tickSize", "0.00000001")))
    min_notional = Decimal(str(filters.get("MIN_NOTIONAL", {}).get("notional", "0")))
    symbol_filters_cache = {"stepSize": step_size, "minQty": min_qty, "tickSize": tick_size, "minNotional": min_notional}
    return symbol_filters_cache

# -------- ORDERS ----------
def place_market_order(client: BinanceClient, symbol: str, side: str, quantity):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "MARKET",
        "quantity": str(quantity)
    }
    if client.dual_side:
        params["positionSide"] = "LONG" if side == "BUY" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_sl_order_closepos(client: BinanceClient, symbol: str, stop_price, side: str):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "STOP_MARKET",
        "closePosition": "true",
        "stopPrice": str(stop_price)
    }
    if client.dual_side:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_tp_order_closepos(client: BinanceClient, symbol: str, stop_price, side: str):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "TAKE_PROFIT_MARKET",
        "closePosition": "true",
        "stopPrice": str(stop_price)
    }
    if client.dual_side:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_trailing_stop(client: BinanceClient, symbol: str, side: str, stop_price, qty):
    filters = get_symbol_filters(client, symbol)
    stop_price_quant = quantize_price(stop_price, filters['tickSize'])
    qty_quant = quantize_qty(qty, filters['stepSize'])
    params = {
        "symbol": symbol,
        "side": side,
        "type": "STOP_MARKET",
        "closePosition": "true",
        "stopPrice": str(stop_price_quant),
        "quantity": str(qty_quant)
    }
    if client.dual_side:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    try:
        response = client.send_signed_request("POST", "/fapi/v1/order", params)
        log(f"Trailing stop (STOP_MARKET) placed: stopPrice={stop_price_quant}, qty={qty_quant}")
        return response
    except BinanceAPIError as e:
        log(f"Trailing stop error: {str(e)}, payload: {e.payload}")
        raise

# -------- DATA FETCHING ----------
def fetch_klines(client: BinanceClient, symbol: str, interval: str, limit=100):
    try:
        klines = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        return klines
    except BinanceAPIError as e:
        log(f"Klines fetch failed: {str(e)}, payload: {e.payload}")
        raise
    except Exception as e:
        log(f"Klines fetch failed: {str(e)}")
        raise

def fetch_balance(client: BinanceClient):
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account", {"recvWindow": 30000})
        balance = Decimal(str(data.get("totalWalletBalance", 0)))
        log(f"Fetched balance: {balance} USDT")
        return balance
    except BinanceAPIError as e:
        log(f"Balance fetch failed: {str(e)}, payload: {e.payload}")
        raise
    except Exception as e:
        log(f"Balance fetch failed: {str(e)}")
        raise

def has_active_position(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 30000})
        for p in positions:
            if p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != 0:
                log(f"Active position detected: {p}")
                return True
        return False
    except BinanceAPIError as e:
        log(f"Position check failed: {str(e)}, payload: {e.payload}")
        return False
    except Exception as e:
        log(f"Position check failed: {str(e)}")
        return False

def fetch_open_positions_details(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 30000})
        return next((p for p in positions if p.get("symbol") == symbol), None)
    except BinanceAPIError as e:
        log(f"Position details fetch failed: {str(e)}, payload: {e.payload}")
        raise
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
        self.exit_close_time = None
        self.sl = None
        self.tp = None
        self.trail_activated = False
        self.trail_order_id = None
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_activation_price = None
        self.highest_price = None  # Track highest price for longs
        self.lowest_price = None   # Track lowest price for shorts
        self.current_trail_stop = None  # Current trailing stop price
        self.risk = None  # Store R value
        self.initial_sl = None  # Store initial SL

# -------- LOGGING SETUP ----------
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

import asyncio

def send_telegram_sync(telegram_bot, chat_id, text, **kwargs):
    """Send Telegram messages safely without reusing connection pool."""
    if not telegram_bot or not chat_id:
        return
    try:
        import requests
        token = telegram_bot.token if hasattr(telegram_bot, "token") else None
        if not token:
            return
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        payload = {"chat_id": chat_id, "text": text}
        if "parse_mode" in kwargs:
            payload["parse_mode"] = kwargs["parse_mode"]
        requests.post(url, json=payload, timeout=10)
    except Exception as e:
        logger.error(f"Failed to send Telegram message: {e}")

def log(message, telegram_bot=None, telegram_chat_id=None):
    logger.info(message)
    if telegram_bot and telegram_chat_id:
        try:
            send_telegram_sync(telegram_bot, telegram_chat_id, message)
        except Exception as e:
            logger.error(f"Failed to send Telegram message: {str(e)}")

# -------- TRADE MONITORING ----------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    last_position_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            log("Stop requested during monitoring. Exiting.", telegram_bot, telegram_chat_id)
            break
        try:
            current_time = time.time()
            if current_time - last_position_check >= POSITION_CHECK_INTERVAL:
                # Fetch current price
                try:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    current_price = Decimal(str(ticker.get("price")))
                except BinanceAPIError as e:
                    log(f"Price fetch failed: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                    time.sleep(2)
                    continue
                except Exception as e:
                    log(f"Price fetch failed: {str(e)}", telegram_bot, telegram_chat_id)
                    time.sleep(2)
                    continue

                # Update highest/lowest price
                if trade_state.side == "LONG":
                    trade_state.highest_price = max(trade_state.highest_price or current_price, current_price)
                else:
                    trade_state.lowest_price = min(trade_state.lowest_price or current_price, current_price)

                # Check for trailing stop activation
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    if (trade_state.side == "LONG" and current_price >= trade_state.trail_activation_price) or \
                       (trade_state.side == "SHORT" and current_price <= trade_state.trail_activation_price):
                        log(f"Trailing stop activated at price={current_price}", telegram_bot, telegram_chat_id)
                        trade_state.trail_activated = True
                        # Set initial trailing stop at 0.25 R above/below initial SL
                        initial_trail_stop = trade_state.initial_sl + Decimal("0.25") * trade_state.risk if trade_state.side == "LONG" else \
                                            trade_state.initial_sl - Decimal("0.25") * trade_state.risk
                        initial_trail_stop_quant = quantize_price(initial_trail_stop, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                        trade_state.current_trail_stop = initial_trail_stop_quant
                        try:
                            trail_side = "SELL" if trade_state.side == "LONG" else "BUY"
                            trail_res = place_trailing_stop(client, symbol, trail_side, initial_trail_stop_quant, Decimal(str(trade_state.qty)))
                            trade_state.trail_order_id = trail_res.get("orderId")
                            log(f"Initial trailing stop placed: stopPrice={initial_trail_stop_quant}", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to place initial trailing stop: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)

                # Update trailing stop if activated
                if trade_state.trail_activated and trade_state.trail_order_id:
                    new_stop_price = None
                    if trade_state.side == "LONG":
                        new_stop_price = trade_state.highest_price - 2 * trade_state.risk
                    else:
                        new_stop_price = trade_state.lowest_price + 2 * trade_state.risk
                    new_stop_price_quant = quantize_price(new_stop_price, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                    if new_stop_price_quant != trade_state.current_trail_stop:
                        # Cancel existing trailing stop order
                        try:
                            client.send_signed_request("DELETE", "/fapi/v1/order", {"symbol": symbol, "orderId": trade_state.trail_order_id})
                            log(f"Cancelled previous trailing stop order: orderId={trade_state.trail_order_id}", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to cancel trailing stop order: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                        # Place new trailing stop order
                        try:
                            trail_side = "SELL" if trade_state.side == "LONG" else "BUY"
                            trail_res = place_trailing_stop(client, symbol, trail_side, new_stop_price_quant, Decimal(str(trade_state.qty)))
                            trade_state.trail_order_id = trail_res.get("orderId")
                            trade_state.current_trail_stop = new_stop_price_quant
                            log(f"Updated trailing stop: stopPrice={new_stop_price_quant}", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to update trailing stop: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)

                # Check position status
                pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 30000})
                pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
                last_position_check = current_time
                if pos_amt == Decimal('0'):
                    # Position closed, check why
                    open_orders = client.get_open_orders(symbol)
                    trail_order = next((o for o in open_orders if o.get("orderId") == trade_state.trail_order_id), None) if trade_state.trail_activated else None
                    sl_order = next((o for o in open_orders if o.get("orderId") == trade_state.sl_order_id), None) if trade_state.sl_order_id else None
                    tp_order = next((o for o in open_orders if o.get("orderId") == trade_state.tp_order_id), None) if trade_state.tp_order_id else None
                    close_side = "BUY" if trade_state.side == "SHORT" else "SELL"
                    close_qty = Decimal(str(trade_state.qty))
                    close_price = None
                    if trade_state.trail_activated and not trail_order:
                        close_price = client.get_latest_fill_price(symbol, trade_state.trail_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (trailing stop executed): {close_side}, qty={close_qty}, price={close_price_str}", telegram_bot, telegram_chat_id)
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after trailing stop execution.", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                        return
                    elif sl_order is None and trade_state.sl_order_id:
                        close_price = client.get_latest_fill_price(symbol, trade_state.sl_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (stop-loss executed): {close_side}, qty={close_qty}, price={close_price_str}", telegram_bot, telegram_chat_id)
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after stop-loss execution.", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                        return
                    elif tp_order is None and trade_state.tp_order_id:
                        close_price = client.get_latest_fill_price(symbol, trade_state.tp_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (take-profit executed): {close_side}, qty={close_qty}, price={close_price_str}", telegram_bot, telegram_chat_id)
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after take-profit execution.", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                        return
                    else:
                        close_price = client.get_latest_fill_price(symbol, trade_state.trail_order_id or trade_state.sl_order_id or trade_state.tp_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (unknown reason): {close_side}, qty={close_qty}, price={close_price_str}", telegram_bot, telegram_chat_id)
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after unexpected closure.", telegram_bot, telegram_chat_id)
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                        return
                time.sleep(1)
        except BinanceAPIError as e:
            log(f"Monitor error: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
            time.sleep(2)
        except Exception as e:
            log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

# -------- TRADING LOOP ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, telegram_bot=None, telegram_chat_id=None):
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
    signal.signal(signal.SIGINT, lambda s, f: _request_stop(s, f, symbol))
    signal.signal(signal.SIGTERM, lambda s, f: _request_stop(s, f, symbol))

    log(f"Connected ({'LIVE' if client.use_live else 'TESTNET'}). Starting bot with symbol={symbol}, timeframe={timeframe}", telegram_bot, telegram_chat_id)
    
    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            if trades_today >= max_trades_per_day:
                log("Max trades reached for today. Waiting for next day.", telegram_bot, telegram_chat_id)
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
            except BinanceAPIError as e:
                log(f"Server time fetch failed: {str(e)}, payload: {e.payload}. Using local time.", telegram_bot, telegram_chat_id)
                server_time = int(time.time() * 1000)
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
                klines = fetch_klines(client, symbol, timeframe, limit=100)
            except BinanceAPIError as e:
                log(f"Failed to fetch klines: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                time.sleep(2)
                continue
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
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            close_time = last_close_time
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price

            log(f"Candle close price={close_price} RSI={rsi} Vol={curr_vol:.2f} SMA15={(vol_sma15 or 0):.2f} {'Green' if is_green_candle else 'Red' if is_red_candle else 'Neutral'} candle", telegram_bot, telegram_chat_id)

            if prevent_same_bar and trade_state.exit_close_time == close_time:
                log("Same bar as exit. Skipping to prevent re-entry.", telegram_bot, telegram_chat_id)
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

            buy_signal = (rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and (not use_volume_filter or curr_vol > vol_sma15))

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close -> {side_text}. Preparing entry.", telegram_bot, telegram_chat_id)
                pending_entry = True

                entry_price = close_price
                entry_price_f = float(entry_price)
                if buy_signal:
                    sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price + (tp_mult * R)
                    close_side_for_sl = "SELL"
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP
                else:
                    sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
                    R = entry_price * SL_PCT
                    tp_price_dec = entry_price - (tp_mult * R)
                    close_side_for_sl = "BUY"
                    sl_rounding = ROUND_DOWN
                    tp_rounding = ROUND_UP

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
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)

                # Calculate trailing stop activation price
                if buy_signal:
                    trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R)
                else:
                    trail_activation_price_dec = entry_price - (TRAIL_TRIGGER_MULT * R)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)

                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={entry_price_f}", telegram_bot, telegram_chat_id)
                timed_out = False
                actual_qty = None
                try:
                    order_res = place_market_order(client, symbol, side_text, qty_api)
                    log(f"Market order placed: {order_res}", telegram_bot, telegram_chat_id)
                except BinanceAPIError as e:
                    log(f"Market order failed: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
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
                        except BinanceAPIError as e:
                            log(f"Cancel failed: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                        except Exception as e:
                            log(f"Cancel failed: {str(e)}", telegram_bot, telegram_chat_id)
                        timed_out = True
                        break
                    time.sleep(0.5)

                if timed_out or actual_qty is None:
                    pending_entry = False
                    log("Entry timed out or aborted -> skipping this signal and waiting for next candle.", telegram_bot, telegram_chat_id)
                    continue

                # Fetch actual fill price
                time.sleep(0.2)  # 200ms delay for fill data
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    log("Failed to fetch actual fill price; using candle close price.", telegram_bot, telegram_chat_id)
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)

                # Recalculate SL, TP, and trailing activation based on actual fill price
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
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)

                # Check if trailing stop activation price is too close to current price
                try:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    current_price = Decimal(str(ticker.get("price")))
                except BinanceAPIError as e:
                    log(f"Price fetch failed: {str(e)}, payload: {e.payload}. Skipping trade.", telegram_bot, telegram_chat_id)
                    pending_entry = False
                    time.sleep(1)
                    continue
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
                trade_state.entry_price = actual_fill_price_f
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                trade_state.initial_sl = sl_price_dec_quant
                trade_state.sl = sl_price_f
                trade_state.tp = tp_price_f
                trade_state.trail_activated = False
                trade_state.trail_order_id = None
                trade_state.sl_order_id = None
                trade_state.tp_order_id = None
                trade_state.trail_activation_price = trail_activation_price_dec_quant
                trade_state.highest_price = actual_fill_price if buy_signal else None
                trade_state.lowest_price = actual_fill_price if not buy_signal else None
                trade_state.current_trail_stop = None
                trade_state.risk = R
                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f}, sl={sl_price_f}, tp={tp_price_f}, trail_activation={trail_activation_price_dec_quant}", telegram_bot, telegram_chat_id)

                try:
                    log("Cancelling all existing open orders for symbol before placing SL/TP...", telegram_bot, telegram_chat_id)
                    try:
                        cancel_res = client.cancel_all_open_orders(symbol)
                        log(f"Cancel all orders response: {cancel_res}", telegram_bot, telegram_chat_id)
                    except BinanceAPIError as e:
                        log(f"Failed to cancel existing orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                    except Exception as e:
                        log(f"Failed to cancel existing orders: {str(e)}. Proceeding with SL/TP placement.", telegram_bot, telegram_chat_id)

                    sl_res = place_sl_order_closepos(client, symbol, str(sl_price_dec_quant), close_side_for_sl)
                    trade_state.sl_order_id = sl_res.get("orderId")
                    log(f"SL response: {sl_res}", telegram_bot, telegram_chat_id)
                    tp_res = place_tp_order_closepos(client, symbol, str(tp_price_dec_quant), close_side_for_sl)
                    trade_state.tp_order_id = tp_res.get("orderId")
                    log(f"TP response: {tp_res}", telegram_bot, telegram_chat_id)

                except BinanceAPIError as e:
                    log(f"Could not place SL/TP orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Could not place SL/TP orders: {str(e)}", telegram_bot, telegram_chat_id)

                try:
                    open_orders = client.get_open_orders(symbol)
                    log(f"Open orders after SL/TP placement: {open_orders}", telegram_bot, telegram_chat_id)
                except BinanceAPIError as e:
                    log(f"Failed to fetch open orders: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Failed to fetch open orders: {str(e)}", telegram_bot, telegram_chat_id)

                trades_today += 1
                pending_entry = False
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

        except BinanceAPIError as e:
            log(f"Loop error: {str(e)}, payload: {e.payload}", telegram_bot, telegram_chat_id)
            time.sleep(2)
        except Exception as e:
            log(f"Loop error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

    log("Trading loop exited.", telegram_bot, telegram_chat_id)

def interval_ms(interval):
    if interval.endswith("m"):
        return int(interval[:-1]) * 60 * 1000
    if interval.endswith("h"):
        return int(interval[:-1]) * 60 * 60 * 1000
    return 5 * 60 * 1000  # 5m default

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

# -------- TELEGRAM SETUP ----------
def init_telegram(token, chat_id):
    try:
        bot = telegram.Bot(token=token)
        # Test Telegram connection: support both sync and async bot.get_me()
        try:
            res = bot.get_me()
            if asyncio.iscoroutine(res):
                asyncio.run(res)
            log("Telegram bot initialized successfully.")
        except Exception as e:
            # Try async run as fallback
            try:
                asyncio.run(bot.get_me())
                log("Telegram bot initialized successfully.")
            except Exception as e2:
                log(f"Failed to initialize Telegram bot: {e2}")
                return None, None
        return bot, chat_id
    except Exception as e:
        log(f"Failed to initialize Telegram bot: {str(e)}")
        return None, None

# -------- ENTRY POINT ----------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Headless, 5m Optimized, Manual Trailing Stop, Telegram Notifications)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", help="Telegram Bot Token")
    parser.add_argument("--chat-id", help="Telegram Chat ID")
    parser.add_argument("--symbol", default="BTCUSDT", help="Trading symbol (default: BTCUSDT)")
    parser.add_argument("--timeframe", default="5m", help="Timeframe (default: 5m)")
    parser.add_argument("--max-trades", type=int, default=3, help="Max trades per day (default: 3)")
    parser.add_argument("--risk-pct", type=float, default=1.0, help="Risk percentage per trade (default: 1%)")
    parser.add_argument("--max-loss-pct", type=float, default=5.0, help="Max daily loss percentage (default: 5%)")
    parser.add_argument("--tp-mult", type=float, default=3.5, help="Take-profit multiplier (default: 3.5)")
    parser.add_argument("--no-trailing", dest='use_trailing', action='store_false', help="Disable trailing stop (default: enabled)")
    parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false', help="Allow entries on same bar (default: prevent same bar)")
    parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false', help="Allow entry even if there's an active position (default: require no pos)")
    parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false', help="Disable max daily loss protection (default: enabled)")
    parser.add_argument("--use-volume-filter", action='store_true', default=False, help="Use volume filter (vol > SMA15, default: False)")
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL for Binance API (advanced)")

    args = parser.parse_args()

    telegram_bot, telegram_chat_id = init_telegram(args.telegram_token, args.chat_id) if args.telegram_token and args.chat_id else (None, None)

    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    
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
        telegram_bot=telegram_bot,
        telegram_chat_id=telegram_chat_id
    )

import requests as _requests
def telegram_post(token, chat_id, text, parse_mode=None):
    """Send Telegram message via direct HTTP POST (creates its own connection each call)."""
    if not token or not chat_id:
        return
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = { "chat_id": chat_id, "text": text }
    if parse_mode:
        payload["parse_mode"] = parse_mode
    try:
        _requests.post(url, json=payload, timeout=10)
    except Exception as e:
        logger.error(f"Telegram HTTP send failed: {e}")
