#!/usr/bin/env python3
# Last_Gptmodgrok_Impotis3_Mod_Hedless2MergedTrailfixed11_5m_EnhancedBuffer_FillPrice_Cleaned8.py
# Optimized Binance Futures RSI bot for 5m timeframe with immediate trailing stop
# Changes from Cleaned7.py:
# - Added initial stopPrice calculation and logging in place_trailing_stop
# - Added debug log for stopPrice updates in monitor_trade
# - Retained closure price, side, qty logs and trailing stop activation log
# - No changes to strategy, timeframe, or order behavior

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
            pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 15000})
            pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
            if pos_amt != 0:
                side = "SELL" if pos_amt > 0 else "BUY"
                qty = abs(pos_amt)
                try:
                    client.send_signed_request("POST", "/fapi/v1/order", {
                        "symbol": symbol,
                        "side": side,
                        "type": "MARKET",
                        "quantity": str(qty),
                        "recvWindow": 15000
                    })
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
            log("Warning: Clock offset > 5s. Using recvWindow=15000.")
    except Exception as e:
        log(f"Binance time sync failed: {str(e)}")

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

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: dict = None):
        params = params.copy() if params else {}
        params["timestamp"] = int(time.time() * 1000)
        params["recvWindow"] = 15000
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
    params = {"symbol": symbol, "side": side, "type": "MARKET", "quantity": str(quantity)}
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_sl_order_closepos(client: BinanceClient, symbol: str, stop_price, side: str):
    params = {"symbol": symbol, "side": side, "type": "STOP_MARKET", "closePosition": "true", "stopPrice": str(stop_price)}
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_tp_order_closepos(client: BinanceClient, symbol: str, stop_price, side: str):
    params = {"symbol": symbol, "side": side, "type": "TAKE_PROFIT_MARKET", "closePosition": "true", "stopPrice": str(stop_price)}
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_trailing_stop(client: BinanceClient, symbol: str, side: str, activation_price, callback_rate, qty):
    filters = get_symbol_filters(client, symbol)
    activation_price_quant = quantize_price(activation_price, filters['tickSize'])
    qty_quant = quantize_qty(qty, filters['stepSize'])
    callback_rate_dec = min(max(Decimal(str(callback_rate)).quantize(Decimal('0.01')), CALLBACK_RATE_MIN), CALLBACK_RATE_MAX)
    initial_stop_price = quantize_price(activation_price_quant * (Decimal('1') + callback_rate_dec / Decimal('100')) if side == "BUY" else activation_price_quant * (Decimal('1') - callback_rate_dec / Decimal('100')), filters['tickSize'])
    log(f"Calculated initial trailing stopPrice={initial_stop_price} for activationPrice={activation_price_quant}, callbackRate={callback_rate_dec}%")
    params = {
        "symbol": symbol,
        "side": side,
        "type": "TRAILING_STOP_MARKET",
        "activationPrice": str(activation_price_quant),
        "callbackRate": str(callback_rate_dec),
        "quantity": str(qty_quant),
        "reduceOnly": "true"
    }
    try:
        response = client.send_signed_request("POST", "/fapi/v1/order", params)
        log(f"Trailing stop response stopPrice={response.get('stopPrice', 'unknown')}")
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
        data = client.send_signed_request("GET", "/fapi/v2/account", {"recvWindow": 15000})
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
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 15000})
        return any(p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != 0 for p in positions)
    except BinanceAPIError as e:
        log(f"Position check failed: {str(e)}, payload: {e.payload}")
        return False
    except Exception as e:
        log(f"Position check failed: {str(e)}")
        return False

def fetch_open_positions_details(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 15000})
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
        self.trail_activation_price = None  # Store activation price

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

log = logger.info

# -------- TRADE MONITORING ----------
def monitor_trade(client, symbol, trade_state, tick_size):
    log("Monitoring active trade...")
    last_position_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            log("Stop requested during monitoring. Exiting.")
            break
        try:
            current_time = time.time()
            if current_time - last_position_check >= POSITION_CHECK_INTERVAL:
                # Check current price for trailing stop activation
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    try:
                        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        current_price = Decimal(str(ticker.get("price")))
                        if (trade_state.side == "LONG" and current_price >= trade_state.trail_activation_price) or \
                           (trade_state.side == "SHORT" and current_price <= trade_state.trail_activation_price):
                            log(f"Trailing stop activated at price={current_price}")
                            trade_state.trail_activated = True
                    except BinanceAPIError as e:
                        log(f"Price fetch failed: {str(e)}, payload: {e.payload}")
                    except Exception as e:
                        log(f"Price fetch failed: {str(e)}")

                # Check trailing stop order for updated stopPrice
                if trade_state.trail_activated and trade_state.trail_order_id:
                    try:
                        orders = client.get_open_orders(symbol)
                        trail_order = next((o for o in orders if o.get("orderId") == trade_state.trail_order_id), None)
                        if trail_order:
                            stop_price = trail_order.get("stopPrice", "unknown")
                            log(f"Trailing stop update: stopPrice={stop_price}")
                    except BinanceAPIError as e:
                        log(f"Failed to fetch trailing stop update: {str(e)}, payload: {e.payload}")
                    except Exception as e:
                        log(f"Failed to fetch trailing stop update: {str(e)}")

                # Check position status
                pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
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
                        log(f"Position closed (trailing stop executed): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after trailing stop execution.")
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}")
                        return
                    elif sl_order is None and trade_state.sl_order_id:
                        close_price = client.get_latest_fill_price(symbol, trade_state.sl_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (stop-loss executed): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after stop-loss execution.")
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}")
                        return
                    elif tp_order is None and trade_state.tp_order_id:
                        close_price = client.get_latest_fill_price(symbol, trade_state.tp_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (take-profit executed): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after take-profit execution.")
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}")
                        return
                    else:
                        close_price = client.get_latest_fill_price(symbol, trade_state.trail_order_id or trade_state.sl_order_id or trade_state.tp_order_id)
                        close_price_str = str(close_price.quantize(Decimal(str(tick_size)))) if close_price else "unknown"
                        log(f"Position closed (unknown reason): {close_side}, qty={close_qty}, price={close_price_str}")
                        trade_state.active = False
                        trade_state.exit_close_time = int(current_time * 1000)
                        try:
                            client.cancel_all_open_orders(symbol)
                            log("All open orders cancelled after unexpected closure.")
                        except BinanceAPIError as e:
                            log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}")
                        return
                time.sleep(1)
        except BinanceAPIError as e:
            log(f"Monitor error: {str(e)}, payload: {e.payload}")
            time.sleep(2)
        except Exception as e:
            log(f"Monitor error: {str(e)}")
            time.sleep(2)

# -------- TRADING LOOP ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter):
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

    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            if trades_today >= max_trades_per_day:
                log("Max trades reached for today. Waiting for next day.")
                time.sleep(60)
                continue

            if use_max_loss:
                current_bal = fetch_balance(client)
                if daily_start_balance - current_bal > daily_start_balance * (max_daily_loss_pct / Decimal("100")):
                    log("Max daily loss reached. Waiting for next day.")
                    time.sleep(60)
                    continue

            try:
                server_time_response = client.public_request("/fapi/v1/time")
                server_time = server_time_response["serverTime"]
            except BinanceAPIError as e:
                log(f"Server time fetch failed: {str(e)}, payload: {e.payload}. Using local time.")
                server_time = int(time.time() * 1000)
            except Exception as e:
                log(f"Server time fetch failed: {str(e)}. Using local time.")
                server_time = int(time.time() * 1000)

            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                log(f"Waiting for candle close in {sleep_seconds:.2f}s ...")
                _safe_sleep(sleep_seconds)
                continue

            try:
                klines = fetch_klines(client, symbol, timeframe, limit=100)
            except BinanceAPIError as e:
                log(f"Failed to fetch klines: {str(e)}, payload: {e.payload}")
                time.sleep(2)
                continue
            except Exception as e:
                log(f"Failed to fetch klines: {str(e)}")
                time.sleep(2)
                continue

            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            last_close_time = close_times[-1]

            if last_processed_time == last_close_time:
                log(f"Duplicate candle detected at {last_close_time}; sleeping 1s")
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

            log(f"Candle close price={close_price} RSI={rsi} Vol={curr_vol:.2f} SMA15={(vol_sma15 or 0):.2f} {'Green' if is_green_candle else 'Red' if is_red_candle else 'Neutral'} candle")

            if prevent_same_bar and trade_state.exit_close_time == close_time:
                log("Same bar as exit. Skipping to prevent re-entry.")
                last_processed_time = close_time
                time.sleep(1)
                continue

            if require_no_pos and has_active_position(client, symbol):
                log("Active position detected. Waiting for closure.")
                last_processed_time = close_time
                time.sleep(1)
                continue

            if use_volume_filter and vol_sma15 is None:
                log("Waiting for volume history...")
                last_processed_time = close_time
                time.sleep(1)
                continue

            buy_signal = (rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and (not use_volume_filter or curr_vol > vol_sma15))

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = close_time
                side_text = "BUY" if buy_signal else "SELL"
                log(f"Signal on candle close -> {side_text}. Preparing entry.")
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
                    log(f"Invalid R ({R}) <= 0. Skipping trade.")
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

                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={entry_price_f}")
                timed_out = False
                actual_qty = None
                try:
                    order_res = place_market_order(client, symbol, side_text, qty_api)
                    log(f"Market order placed: {order_res}")
                except BinanceAPIError as e:
                    log(f"Market order failed: {str(e)}, payload: {e.payload}")
                    pending_entry = False
                    time.sleep(1)
                    continue
                except Exception as e:
                    log(f"Market order failed: {str(e)}")
                    pending_entry = False
                    time.sleep(1)
                    continue

                log("Waiting for entry order to fill...")
                start_time = time.time()
                while True:
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        log("Stop requested during fill wait; aborting entry flow.")
                        break
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break
                    if time.time() - start_time > ORDER_FILL_TIMEOUT:
                        log("Timeout waiting for fill. Attempting to cancel order...")
                        cancel_params = {"symbol": symbol, "orderId": order_res.get("orderId")} if isinstance(order_res, dict) else {"symbol": symbol}
                        try:
                            client.send_signed_request("DELETE", "/fapi/v1/order", cancel_params)
                            log("Entry order cancelled.")
                        except BinanceAPIError as e:
                            log(f"Cancel failed: {str(e)}, payload: {e.payload}")
                        except Exception as e:
                            log(f"Cancel failed: {str(e)}")
                        timed_out = True
                        break
                    time.sleep(0.5)

                if timed_out or actual_qty is None:
                    pending_entry = False
                    log("Entry timed out or aborted -> skipping this signal and waiting for next candle.")
                    continue

                # Fetch actual fill price
                time.sleep(0.2)  # 200ms delay for fill data
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    log("Failed to fetch actual fill price; using candle close price.")
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)

                # Calculate trailing stop parameters
                if buy_signal:
                    trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R)
                else:
                    trail_activation_price_dec = actual_fill_price - (TRAIL_TRIGGER_MULT * R)
                trail_distance_dec = TRAIL_DISTANCE_MULT * R
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)
                trail_activation_price_f = float(trail_activation_price_dec_quant)
                callback_rate_dec = (trail_distance_dec / trail_activation_price_dec * Decimal("100")).quantize(Decimal('0.01'))
                callback_rate_f = float(callback_rate_dec)

                # Check if trailing stop activation price is too close to current price
                try:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    current_price = Decimal(str(ticker.get("price")))
                except BinanceAPIError as e:
                    log(f"Price fetch failed: {str(e)}, payload: {e.payload}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue
                except Exception as e:
                    log(f"Price fetch failed: {str(e)}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue

                price_buffer = actual_fill_price * TRAIL_PRICE_BUFFER
                if buy_signal and trail_activation_price_dec_quant <= current_price + price_buffer:
                    log(f"Trailing stop activation price {trail_activation_price_dec_quant} too close to current price {current_price}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue
                elif not buy_signal and trail_activation_price_dec_quant >= current_price - price_buffer:
                    log(f"Trailing stop activation price {trail_activation_price_dec_quant} too close to current price {current_price}. Skipping trade.")
                    pending_entry = False
                    time.sleep(1)
                    continue

                trade_state.active = True
                trade_state.entry_price = actual_fill_price_f
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = close_time
                trade_state.sl = sl_price_f
                trade_state.tp = tp_price_f
                trade_state.trail_activated = False
                trade_state.trail_order_id = None
                trade_state.sl_order_id = None
                trade_state.tp_order_id = None
                trade_state.trail_activation_price = trail_activation_price_dec_quant  # Store activation price
                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f}, sl={sl_price_f}, tp={tp_price_f}")

                try:
                    log("Cancelling all existing open orders for symbol before placing SL/TP...")
                    try:
                        cancel_res = client.cancel_all_open_orders(symbol)
                        log(f"Cancel all orders response: {cancel_res}")
                    except BinanceAPIError as e:
                        log(f"Failed to cancel existing orders: {str(e)}, payload: {e.payload}")
                    except Exception as e:
                        log(f"Failed to cancel existing orders: {str(e)}. Proceeding with SL/TP placement.")

                    sl_res = place_sl_order_closepos(client, symbol, str(sl_price_dec_quant), close_side_for_sl)
                    trade_state.sl_order_id = sl_res.get("orderId")
                    log(f"SL response: {sl_res}")
                    tp_res = place_tp_order_closepos(client, symbol, str(tp_price_dec_quant), close_side_for_sl)
                    trade_state.tp_order_id = tp_res.get("orderId")
                    log(f"TP response: {tp_res}")

                    if use_trailing:
                        log(f"Placing trailing stop: activationPrice={trail_activation_price_f}, callbackRate={callback_rate_f}%")
                        trail_side = "SELL" if buy_signal else "BUY"
                        try:
                            trail_res = place_trailing_stop(client, symbol, trail_side, trail_activation_price_f, callback_rate_f, Decimal(str(actual_qty)))
                            trade_state.trail_activated = False  # Reset, will be set on price check
                            trade_state.trail_order_id = trail_res.get("orderId")
                            log(f"Trailing stop response: {trail_res}")
                        except BinanceAPIError as e:
                            log(f"Failed to place trailing stop: {str(e)}, payload: {e.payload}. Continuing with SL/TP only.")

                except BinanceAPIError as e:
                    log(f"Could not place SL/TP orders: {str(e)}, payload: {e.payload}")
                except Exception as e:
                    log(f"Could not place SL/TP orders: {str(e)}")

                try:
                    open_orders = client.get_open_orders(symbol)
                    log(f"Open orders after SL/TP and trailing stop attempt: {open_orders}")
                except BinanceAPIError as e:
                    log(f"Failed to fetch open orders: {str(e)}, payload: {e.payload}")
                except Exception as e:
                    log(f"Failed to fetch open orders: {str(e)}")

                trades_today += 1
                pending_entry = False
                monitor_trade(client, symbol, trade_state, tick_size)

            elif trade_state.active or pending_entry:
                log("Trade active or pending. Skipping signal check.")

            else:
                log("No trade signal on candle close.")

            if last_processed_time != close_time:
                last_processed_time = close_time

            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            log(f"Waiting for candle close in {sleep_seconds:.2f}s ...")
            _safe_sleep(sleep_seconds)

        except BinanceAPIError as e:
            log(f"Loop error: {str(e)}, payload: {e.payload}")
            time.sleep(2)
        except Exception as e:
            log(f"Loop error: {str(e)}")
            time.sleep(2)

    log("Trading loop exited.")

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

# -------- ENTRY POINT ----------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI Bot (Headless, 5m Optimized, Immediate Trailing Stop, Cleaned)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
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

    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}")

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
        use_volume_filter=args.use_volume_filter
    )
