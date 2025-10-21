#!/usr/bin/env python3
# Fixed_SOL15_30m_SOLUSDT.py
# Changes:
# - Fixed trailing stop distance calculation in monitor_trade (use 2 * |sl - entry|)
# - Added Telegram retry logic (3 attempts, exponential backoff)
# - Added Telegram notification and PNL logging in _request_stop for manual closure
# - Ensured clean loop exit after STOP_REQUESTED
# - Maintained all previous fixes (TP=185.9766 for entry=190.99, trailing=2.85685, etc.)

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
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone
from urllib.parse import urlencode
from telegram import Bot
import schedule
import asyncio
import backoff

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")          # 0.5% per trade
SL_PCT = Decimal("0.0075")           # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MACD_FAST = 12
MACD_SLOW = 26
MACD_SIGNAL = 9
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 50
BUY_RSI_MAX = 70
SELL_RSI_MIN = 30
SELL_RSI_MAX = 50
CALLBACK_RATE_MIN = Decimal("0.1")
CALLBACK_RATE_MAX = Decimal("5.0")
POSITION_CHECK_INTERVAL = 60
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = 5.0

# Global stop flag and client
STOP_REQUESTED = False
client = None
symbol_filters_cache = None
klines_cache = None
klines_cache_time = 0

# Global PnL tracking
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data = []  # List of dicts: {'date': str, 'trade_id': int, 'side': str, 'entry': float, 'exit': float, 'pnl_usd': float, 'pnl_r': float}

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
    return row  # Return for Telegram notification

@backoff.on_exception(backoff.expo, Exception, max_tries=3, max_time=10)
async def send_telegram_message(bot, chat_id, message):
    try:
        await bot.send_message(chat_id=chat_id, text=message)
        log(f"Telegram message sent: {message[:50]}...")
    except Exception as e:
        log(f"Telegram send failed: {str(e)}")
        raise

def send_trade_telegram(trade_details, bot, chat_id):
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"- Trailing Activation: {trade_details['trail_activation']:.4f}\n"
        f"- Qty: {trade_details['qty']}"
    )
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, message))).start()

def send_close_telegram(symbol, side, qty, exit_price, exit_reason, bot, chat_id):
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Qty: {qty}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Reason: {exit_reason}"
    )
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, message))).start()

def send_daily_report(bot, chat_id):
    report = calculate_pnl_report('daily')
    subject = f"Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def send_weekly_report(bot, chat_id):
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def send_monthly_report(bot, chat_id):
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def calculate_pnl_report(period='daily'):
    if not pnl_data:
        return "No trades recorded."
    from datetime import timedelta
    end_date = datetime.now(timezone.utc)
    if period == 'daily':
        start_date = end_date - timedelta(days=1)
    elif period == 'weekly':
        start_date = end_date - timedelta(weeks=1)
    elif period == 'monthly':
        start_date = end_date - timedelta(days=30)  # Approximate
    else:
        return "Invalid period."
    period_trades = [trade for trade in pnl_data if datetime.fromisoformat(trade['date']) >= start_date]
    if not period_trades:
        return f"No trades in {period} period."
    total_pnl_usd = sum(trade['pnl_usd'] for trade in period_trades)
    total_pnl_r = sum(trade['pnl_r'] for trade in period_trades)
    num_trades = len(period_trades)
    wins = len([t for t in period_trades if t['pnl_r'] > 0])
    win_rate = (wins / num_trades * 100) if num_trades > 0 else 0
    report = f"{period.capitalize()} PnL Report:\n- Trades: {num_trades}\n- Win Rate: {win_rate:.2f}%\n- Total PnL: ${total_pnl_usd:.2f}\n- Total PnL: {total_pnl_r:.2f}R"
    return report

def _request_stop(signum, frame, symbol=None, trade_state=None, telegram_bot=None, telegram_chat_id=None):
    global STOP_REQUESTED, client
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    try:
        if client and symbol:
            pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
            pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
            if pos_amt != 0:
                side = "SELL" if pos_amt > 0 else "BUY"
                qty = abs(pos_amt)
                try:
                    params = {"symbol": symbol, "side": side, "type": "MARKET", "quantity": str(qty)}
                    is_hedge_mode = client.get_position_mode()
                    if is_hedge_mode:
                        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
                    close_order = client.send_signed_request("POST", "/fapi/v1/order", params)
                    log(f"Closed position: qty={qty} {side}")
                    if trade_state and telegram_bot and telegram_chat_id:
                        exit_price = client.get_latest_fill_price(symbol, close_order.get("orderId"))
                        exit_price = Decimal(str(exit_price)) if exit_price else Decimal(str(trade_state.sl))
                        entry_price = Decimal(str(trade_state.entry_price))
                        R = abs(Decimal(str(trade_state.sl)) - entry_price)
                        pnl = qty * (exit_price - entry_price) * (-1 if trade_state.side == "SHORT" else 1)
                        trade_id = len(pnl_data) + 1
                        log_pnl(trade_id, trade_state.side, float(entry_price), float(exit_price), qty, R)
                        send_close_telegram(symbol, trade_state.side, qty, float(exit_price), "Manual Stop", telegram_bot, telegram_chat_id)
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
            log("Warning: Clock offset > 5s. Using recvWindow=10000.")
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
        for attempt in range(5):
            try:
                response = requests.get(f"{self.base}/fapi/v1/time", timeout=5)
                server_time_ms = response.json()['serverTime']
                params["timestamp"] = server_time_ms
            except Exception as e:
                log(f"Time sync failed (attempt {attempt+1}/5): {str(e)}. Using local time.")
                params["timestamp"] = int(time.time() * 1000)
            params["recvWindow"] = 10000
            query = urlencode({k: str(params[k]) for k in sorted(params.keys())})
            signature = self._sign(query)
            url = f"{self.base}{endpoint}?{query}&signature={signature}"
            headers = {"X-MBX-APIKEY": self.api_key}
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
                if attempt < 4:
                    time.sleep(2 ** attempt)
                    continue
                raise
            except Exception as e:
                if attempt < 4:
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

    def get_position_mode(self):
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            dual_side = response.get("dualSidePosition", False)
            mode = "Hedge Mode" if dual_side else "One-Way Mode"
            log(f"Account position mode: {mode}")
            return dual_side
        except BinanceAPIError as e:
            log(f"Failed to fetch position mode: {str(e)}, payload: {e.payload}")
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
    return round(rsi, 3)

def compute_macd(closes, fast=MACD_FAST, slow=MACD_SLOW, signal=MACD_SIGNAL):
    if len(closes) < slow + signal:
        return None, None, None, None
    closes_dec = [Decimal(str(c)) for c in closes]
    ema_fast = []
    ema_slow = []
    k_fast = Decimal('2') / (fast + 1)
    k_slow = Decimal('2') / (slow + 1)
    ema_fast.append(sum(closes_dec[:fast]) / fast)
    ema_slow.append(sum(closes_dec[:slow]) / slow)
    for i in range(1, len(closes_dec)):
        if i >= fast:
            ema_fast.append(closes_dec[i] * k_fast + ema_fast[-1] * (1 - k_fast))
        if i >= slow:
            ema_slow.append(closes_dec[i] * k_slow + ema_slow[-1] * (1 - k_slow))
    if len(ema_fast) < slow - fast + 1:
        return None, None, None, None
    macd_line = [f - s for f, s in zip(ema_fast[-(slow - fast + 1):], ema_slow)]
    signal_line = []
    k_signal = Decimal('2') / (signal + 1)
    signal_line.append(sum(macd_line[:signal]) / signal)
    for i in range(1, len(macd_line)):
        signal_line.append(macd_line[i] * k_signal + signal_line[-1] * (1 - k_signal))
    macd = macd_line[-1]
    signal_val = signal_line[-1]
    hist = macd - signal_val
    prev_macd = macd_line[-2] if len(macd_line) >= 2 else None
    prev_signal = signal_line[-2] if len(signal_line) >= 2 else None
    bullish_crossover = prev_macd and prev_signal and prev_macd <= prev_signal and macd > signal_val
    bearish_crossover = prev_macd and prev_signal and prev_macd >= prev_signal and macd < signal_val
    return round(float(macd), 3), round(float(signal_val), 3), bullish_crossover, bearish_crossover

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
    tick_size_dec = Decimal(str(tick_size))
    precision = abs(tick_size_dec.as_tuple().exponent)
    return Decimal(str(p)).quantize(Decimal(f'0.{"0" * precision}'), rounding=rounding)

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
    log(f"Fetched symbol filters for {symbol}: tickSize={tick_size}, stepSize={step_size}, minQty={min_qty}, minNotional={min_notional}")
    return symbol_filters_cache

# -------- ORDERS ----------
def place_market_order(client: BinanceClient, symbol: str, side: str, quantity):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "MARKET",
        "quantity": str(quantity)
    }
    is_hedge_mode = client.get_position_mode()
    if is_hedge_mode:
        params["positionSide"] = "LONG" if side == "BUY" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_sl_order_closepos(client: BinanceClient, symbol: str, stop_price, side: str):
    filters = get_symbol_filters(client, symbol)
    tick_size = filters['tickSize']
    stop_price_quant = quantize_price(stop_price, tick_size, ROUND_DOWN)
    log(f"Placing SL order: stopPrice={stop_price_quant}, tickSize={tick_size}")
    params = {
        "symbol": symbol,
        "side": side,
        "type": "STOP_MARKET",
        "closePosition": "true",
        "stopPrice": str(stop_price_quant),
        "goodTillDate": 0
    }
    is_hedge_mode = client.get_position_mode()
    if is_hedge_mode:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_tp_order_closepos(client: BinanceClient, symbol: str, stop_price, side: str):
    filters = get_symbol_filters(client, symbol)
    tick_size = filters['tickSize']
    stop_price_quant = quantize_price(stop_price, tick_size, ROUND_UP)
    log(f"Placing TP order: stopPrice={stop_price_quant}, tickSize={tick_size}")
    params = {
        "symbol": symbol,
        "side": side,
        "type": "TAKE_PROFIT_MARKET",
        "closePosition": "true",
        "stopPrice": str(stop_price_quant),
        "goodTillDate": 0
    }
    is_hedge_mode = client.get_position_mode()
    if is_hedge_mode:
        params["positionSide"] = "LONG" if side == "SELL" else "SHORT"
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def place_trailing_stop(client: BinanceClient, symbol: str, side: str, activation_price, callback_rate, qty, sl_price, R):
    filters = get_symbol_filters(client, symbol)
    tick_size = filters['tickSize']
    activation_price_quant = quantize_price(activation_price, tick_size)
    qty_quant = quantize_qty(qty, filters['stepSize'])
    callback_rate_dec = min(max(Decimal(str(callback_rate)).quantize(Decimal('0.01')), CALLBACK_RATE_MIN), CALLBACK_RATE_MAX)
    trail_distance = 2 * R
    initial_stop_price = quantize_price(
        activation_price_quant + trail_distance if side == "BUY" else activation_price_quant - trail_distance,
        tick_size
    )
    log(f"Trailing stop setup: activationPrice={activation_price_quant}, trailDistance={trail_distance} (2R), initialStopPrice={initial_stop_price}, callbackRate={callback_rate_dec}%")
    params = {
        "symbol": symbol,
        "side": side,
        "type": "TRAILING_STOP_MARKET",
        "activationPrice": str(activation_price_quant),
        "callbackRate": str(callback_rate_dec),
        "quantity": str(qty_quant),
        "reduceOnly": "true"
    }
    is_hedge_mode = client.get_position_mode()
    if is_hedge_mode:
        params["positionSide"] = "LONG" if side == "BUY" else "SHORT"
    try:
        response = client.send_signed_request("POST", "/fapi/v1/order", params)
        returned_stop_price = Decimal(str(response.get('stopPrice', '0')))
        returned_callback_rate = Decimal(str(response.get('priceRate', '0')))
        log(f"Trailing stop placed: stopPrice={returned_stop_price}, activationPrice={activation_price_quant}, trailDistance={trail_distance} (2R), callbackRate={returned_callback_rate}%")
        if returned_stop_price != initial_stop_price or returned_callback_rate != callback_rate_dec:
            log(f"Warning: Binance response differs - expected stopPrice={initial_stop_price}, callbackRate={callback_rate_dec}%")
        return response
    except BinanceAPIError as e:
        log(f"Trailing stop error: {str(e)}, payload: {e.payload}")
        if e.payload and isinstance(e.payload, dict) and e.payload.get('code') == -1111:
            log(f"Precision error detected. Falling back to STOP_MARKET at initialStopPrice={initial_stop_price}")
            params = {
                "symbol": symbol,
                "side": side,
                "type": "STOP_MARKET",
                "stopPrice": str(initial_stop_price),
                "quantity": str(qty_quant),
                "reduceOnly": "true"
            }
            if is_hedge_mode:
                params["positionSide"] = "LONG" if side == "BUY" else "SHORT"
            try:
                response = client.send_signed_request("POST", "/fapi/v1/order", params)
                log(f"Fallback STOP_MARKET placed: stopPrice={initial_stop_price}, qty={qty_quant}")
                return response
            except BinanceAPIError as e:
                log(f"Fallback STOP_MARKET failed: {str(e)}, payload: {e.payload}")
                raise
        raise

# -------- DATA FETCHING ----------
def fetch_klines(client: BinanceClient, symbol: str, interval: str, limit=100):
    global klines_cache, klines_cache_time
    current_time = time.time()
    if klines_cache and (current_time - klines_cache_time) < KLINES_CACHE_DURATION:
        log("Using cached klines")
        return klines_cache
    try:
        klines = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        klines_cache = klines
        klines_cache_time = current_time
        return klines
    except BinanceAPIError as e:
        log(f"Klines fetch failed: {str(e)}, payload: {e.payload}")
        raise
    except Exception as e:
        log(f"Klines fetch failed: {str(e)}")
        raise

def fetch_balance(client: BinanceClient):
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
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
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        return any(p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != 0 for p in positions)
    except BinanceAPIError as e:
        log(f"Position check failed: {str(e)}, payload: {e.payload}")
        return False
    except Exception as e:
        log(f"Position check failed: {str(e)}")
        return False

def fetch_open_positions_details(client: BinanceClient, symbol: str):
    try:
        positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
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
from decimal import Decimal, ROUND_DOWN, ROUND_UP

def place_trailing_stop(client: BinanceClient, symbol: str, side: str, activation_price, callback_rate, qty, sl_price, R):
    """
    Place a trailing stop that aims to maintain trail_distance = 2 * R.
    - Ensures closePosition=true and reduceOnly=true.
    - Handles immediate stopPrice==0 (Binance computes actual stop later).
    - Re-queries open orders shortly after placement to get confirmed stopPrice.
    """
    filters = get_symbol_filters(client, symbol)
    tick_size = filters['tickSize']
    activation_price_quant = quantize_price(Decimal(str(activation_price)), tick_size)
    qty_quant = quantize_qty(qty, filters['stepSize'])
    callback_rate_dec = min(max(Decimal(str(callback_rate)).quantize(Decimal('0.01')), CALLBACK_RATE_MIN), CALLBACK_RATE_MAX)

    trail_distance = (Decimal('2') * Decimal(str(R))).quantize(tick_size)
    # expected initial stop (activation - 2R for LONG close=SELL, activation + 2R for SHORT close=BUY)
    if side == "SELL":
        expected_initial_stop = (activation_price_quant - trail_distance).quantize(tick_size)
    else:
        expected_initial_stop = (activation_price_quant + trail_distance).quantize(tick_size)

    log(f"Trailing stop setup: activationPrice={activation_price_quant}, trailDistance={trail_distance} (2R), expectedInitialStop={expected_initial_stop}, callbackRate={callback_rate_dec}%")

    params = {
        "symbol": symbol,
        "side": side,
        "type": "TRAILING_STOP_MARKET",
        "activationPrice": str(activation_price_quant),
        "callbackRate": str(callback_rate_dec),
        "quantity": str(qty_quant),
        "reduceOnly": "true",
        "closePosition": "true"
    }

    is_hedge_mode = client.get_position_mode()
    if is_hedge_mode:
        params["positionSide"] = "LONG" if side == "BUY" else "SHORT"

    try:
        response = client.send_signed_request("POST", "/fapi/v1/order", params)
        # Log immediate response (stopPrice may be zero initially)
        returned_stop_price = Decimal(str(response.get('stopPrice', '0'))) if response.get('stopPrice') is not None else Decimal('0')
        returned_price_rate = response.get('priceRate') or response.get('price_rate') or response.get('callbackRate')
        log(f"Trailing stop placed (immediate response): orderId={response.get('orderId')}, stopPrice={returned_stop_price}, priceRate={returned_price_rate}")

        # If stopPrice==0, Binance will compute effective stop later. Re-query open orders to fetch actual stopPrice.
        try:
            time.sleep(0.7)  # short delay for Binance to compute stopPrice
            open_orders = client.get_open_orders(symbol)
            # Find the trailing order by orderId (if present) or by type TRAILING_STOP_MARKET and matching qty
            order_id = response.get('orderId')
            trail_order = None
            if order_id:
                trail_order = next((o for o in open_orders if o.get('orderId') == order_id), None)
            if not trail_order:
                # fallback: find a TRAILING_STOP_MARKET reduceOnly closePosition order matching qty
                trail_order = next((o for o in open_orders if o.get('type') == 'TRAILING_STOP_MARKET' and o.get('reduceOnly') in (True, 'true', 'True') and Decimal(str(o.get('origQty', o.get('quantity', '0')))) == qty_quant), None)
            if trail_order:
                confirmed_stop_price = Decimal(str(trail_order.get('stopPrice', '0')))
                confirmed_activate = Decimal(str(trail_order.get('activationPrice', trail_order.get('activatePrice', '0')) or '0'))
                log(f"Trailing stop confirmed on openOrders: orderId={trail_order.get('orderId')}, stopPrice={confirmed_stop_price}, activationPrice={confirmed_activate}, callbackRate={trail_order.get('priceRate') or trail_order.get('price_rate') or trail_order.get('callbackRate')}")
                # Compare confirmed_stop_price to expected_initial_stop with tolerance = few ticks
                tolerance = tick_size * Decimal('3')  # e.g., allow 3 ticks drift
                if confirmed_stop_price != 0 and abs(confirmed_stop_price - expected_initial_stop) > tolerance:
                    log(f"Warning: Confirmed trailing stopPrice {confirmed_stop_price} differs from expectedInitialStop {expected_initial_stop} by more than {tolerance}.")
                return trail_order
            else:
                log("Trailing stop placed but not found in open orders (immediate). Returning API response.")
                return response
        except Exception as e:
            log(f"Failed to re-check open orders after placing trailing stop: {str(e)}. Returning initial response.")
            return response

    except BinanceAPIError as e:
        log(f"Trailing stop error: {str(e)}, payload: {e.payload}")
        # Keep precision fallback behavior
        if e.payload and isinstance(e.payload, dict) and e.payload.get('code') == -1111:
            log(f"Precision error detected. Falling back to STOP_MARKET at expectedInitialStop={expected_initial_stop}")
            params_fb = {
                "symbol": symbol,
                "side": side,
                "type": "STOP_MARKET",
                "stopPrice": str(expected_initial_stop),
                "quantity": str(qty_quant),
                "reduceOnly": "true",
                "closePosition": "true"
            }
            if is_hedge_mode:
                params_fb["positionSide"] = "LONG" if side == "BUY" else "SHORT"
            resp_fb = client.send_signed_request("POST", "/fapi/v1/order", params_fb)
            log(f"Fallback STOP_MARKET placed: stopPrice={expected_initial_stop}, respOrderId={resp_fb.get('orderId')}")
            return resp_fb
        raise

def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id):
    """
    Monitor active trade; improved trailing stop distance calculations and logging.
    """
    log("Monitoring active trade...")
    last_position_check = 0
    tick_size_dec = Decimal(str(tick_size))
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            log("Stop requested during monitoring. Exiting.")
            _request_stop(None, None, symbol, trade_state, telegram_bot, telegram_chat_id)
            break
        try:
            current_time = time.time()
            if current_time - last_position_check >= POSITION_CHECK_INTERVAL:
                pos = fetch_open_positions_details(client, symbol)
                pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                if pos_amt == Decimal('0'):
                    # Position closed - gather close reason and price
                    open_orders = client.get_open_orders(symbol)
                    trail_order = None
                    if trade_state.trail_order_id:
                        trail_order = next((o for o in open_orders if o.get("orderId") == trade_state.trail_order_id), None)
                    sl_order = next((o for o in open_orders if o.get("orderId") == trade_state.sl_order_id), None) if trade_state.sl_order_id else None
                    tp_order = next((o for o in open_orders if o.get("orderId") == trade_state.tp_order_id), None) if trade_state.tp_order_id else None

                    close_side = "BUY" if trade_state.side == "SHORT" else "SELL"
                    close_qty = Decimal(str(trade_state.qty))
                    close_price = client.get_latest_fill_price(symbol, trade_state.sl_order_id or trade_state.tp_order_id or trade_state.trail_order_id)
                    close_price = Decimal(str(close_price)) if close_price else Decimal(str(trade_state.sl))
                    close_price_str = str(close_price.quantize(tick_size_dec))
                    R = (Decimal(str(trade_state.sl)) - Decimal(str(trade_state.entry_price))) if trade_state.side == "LONG" else (Decimal(str(trade_state.entry_price)) - Decimal(str(trade_state.sl)))
                    R = abs(R)
                    exit_reason = "Unknown"
                    if trade_state.trail_activated and not trail_order:
                        exit_reason = "Trailing Stop"
                        log(f"Position closed (trailing stop executed): {close_side}, qty={close_qty}, price={close_price_str}")
                    elif sl_order is None and trade_state.sl_order_id:
                        exit_reason = "Stop-Loss"
                        log(f"Position closed (stop-loss executed): {close_side}, qty={close_qty}, price={close_price_str}")
                    elif tp_order is None and trade_state.tp_order_id:
                        exit_reason = "Take-Profit"
                        log(f"Position closed (take-profit executed): {close_side}, qty={close_qty}, price={close_price_str}")
                    else:
                        log(f"Position closed (unknown reason): {close_side}, qty={close_qty}, price={close_price_str}")

                    log_pnl(len(pnl_data) + 1, trade_state.side, trade_state.entry_price, Decimal(str(close_price)), close_qty, R)
                    send_close_telegram(symbol, trade_state.side, trade_state.qty, Decimal(str(close_price)), exit_reason, telegram_bot, telegram_chat_id)
                    trade_state.active = False
                    trade_state.exit_close_time = int(current_time * 1000)
                    try:
                        client.cancel_all_open_orders(symbol)
                        log("All open orders cancelled after position closure.")
                    except BinanceAPIError as e:
                        log(f"Failed to cancel orders: {str(e)}, payload: {e.payload}")
                    return

                unrealized_pnl = Decimal(str(pos.get("unrealizedProfit", "0"))) if pos else Decimal('0')
                if unrealized_pnl == 0:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    current_price = Decimal(str(ticker.get("price")))
                    entry_price = Decimal(str(trade_state.entry_price))
                    pos_amt_abs = abs(pos_amt)
                    unrealized_pnl = (current_price - entry_price) * pos_amt_abs if pos_amt > 0 else (entry_price - current_price) * pos_amt_abs
                log(f"Unrealized PNL: {unrealized_pnl.quantize(Decimal('0.01'))} USDT")

                # Check activation
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    try:
                        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        current_price = Decimal(str(ticker.get("price")))
                        if (trade_state.side == "LONG" and current_price >= Decimal(str(trade_state.trail_activation_price))) or \
                           (trade_state.side == "SHORT" and current_price <= Decimal(str(trade_state.trail_activation_price))):
                            log(f"Trailing stop activated at price={current_price} (activationPrice={trade_state.trail_activation_price})")
                            trade_state.trail_activated = True
                    except BinanceAPIError as e:
                        log(f"Price fetch failed: {str(e)}, payload: {e.payload}")
                    except Exception as e:
                        log(f"Price fetch failed: {str(e)}")

                # If trailing is active and there's a trail_order_id, fetch the open order to read stopPrice
                if trade_state.trail_activated and trade_state.trail_order_id:
                    try:
                        orders = client.get_open_orders(symbol)
                        trail_order = next((o for o in orders if o.get("orderId") == trade_state.trail_order_id), None)
                        if trail_order:
                            stop_price = Decimal(str(trail_order.get("stopPrice", "0")))
                            # current price
                            current_price = Decimal(str(client.public_request("/fapi/v1/ticker/price", {"symbol": symbol}).get("price")))
                            expected_trail_distance = (Decimal('2') * abs(Decimal(str(trade_state.sl)) - Decimal(str(trade_state.entry_price)))).quantize(tick_size_dec)
                            # Compute actual trail distance: abs(currentPrice - stopPrice) (direction-agnostic)
                            trail_distance = abs(current_price - stop_price).quantize(tick_size_dec)
                            log(f"Trailing stop update: stopPrice={stop_price.quantize(tick_size_dec)}, currentPrice={current_price.quantize(tick_size_dec)}, trailDistance={trail_distance} (expected 2R={expected_trail_distance})")
                            # Tolerance = a few ticks
                            tolerance = tick_size_dec * Decimal('3')
                            if stop_price == 0:
                                # Binance may return 0 until it computes; re-query next cycle
                                log("Note: trailing stop stopPrice==0 in openOrders; will re-check on next cycle.")
                            elif abs(trail_distance - expected_trail_distance) > tolerance:
                                log(f"Warning: Trailing distance {trail_distance} deviates from expected 2R={expected_trail_distance} by more than {tolerance}.")
                        else:
                            log("Trailing stop order not found in open orders; position may have closed or order changed.")
                    except BinanceAPIError as e:
                        log(f"Failed to fetch trailing stop update: {str(e)}, payload: {e.payload}")
                    except Exception as e:
                        log(f"Failed to fetch trailing stop update: {str(e)}")

                last_position_check = current_time
            time.sleep(1)
        except BinanceAPIError as e:
            log(f"Monitor error: {str(e)}, payload: {e.payload}")
            time.sleep(2)
        except Exception as e:
            log(f"Monitor error: {str(e)}")
            time.sleep(2)

# -------- TRADING LOOP ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, use_macd, telegram_bot, telegram_chat_id):
    global R
    log(f"Starting trading loop with timeframe={timeframe}, symbol={symbol}, risk_pct={risk_pct*100}%, use_volume_filter={use_volume_filter}, use_macd={use_macd}")
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
    is_hedge_mode = client.get_position_mode()
    log(f"Position mode cached: {'Hedge Mode' if is_hedge_mode else 'One-Way Mode'}")
    signal.signal(signal.SIGINT, lambda s, f: _request_stop(s, f, symbol, trade_state, telegram_bot, telegram_chat_id))
    signal.signal(signal.SIGTERM, lambda s, f: _request_stop(s, f, symbol, trade_state, telegram_bot, telegram_chat_id))

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
            macd, signal_val, bullish_crossover, bearish_crossover = compute_macd(closes) if use_macd else (None, None, True, True)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD)
            curr_vol = volumes[-1]
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            close_time = last_close_time
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price

            log(f"Candle open={open_price}, close={close_price}, RSI={rsi}, MACD={macd if use_macd else 'N/A'}, Signal={signal_val if use_macd else 'N/A'}, Vol={curr_vol:.2f}, SMA15={(vol_sma15 or 0):.2f}, {'Green' if is_green_candle else 'Red' if is_red_candle else 'Neutral'} candle")

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

            buy_signal = (rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and
                          (not use_macd or bullish_crossover) and (not use_volume_filter or curr_vol > vol_sma15))
            sell_signal = (rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and
                           (not use_macd or bearish_crossover) and (not use_volume_filter or curr_vol > vol_sma15))

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
                        if is_hedge_mode:
                            cancel_params["positionSide"] = "LONG" if side_text == "BUY" else "SHORT"
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

                time.sleep(0.2)
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    log("Failed to fetch actual fill price; using candle close price.")
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)

                if buy_signal:
                    sl_price_dec = actual_fill_price * (Decimal("1") - SL_PCT)
                    R = actual_fill_price * SL_PCT
                    tp_price_dec = actual_fill_price + (tp_mult * R)
                    close_side_for_sl = "SELL"
                else:
                    sl_price_dec = actual_fill_price * (Decimal("1") + SL_PCT)
                    R = actual_fill_price * SL_PCT
                    tp_price_dec = actual_fill_price - (tp_mult * R)
                    close_side_for_sl = "BUY"
                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)

                if buy_signal:
                    trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R)
                else:
                    trail_activation_price_dec = actual_fill_price - (TRAIL_TRIGGER_MULT * R)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)
                trail_activation_price_f = float(trail_activation_price_dec_quant)
                callback_rate_dec = (2 * R / trail_activation_price_dec * Decimal("100")).quantize(Decimal('0.01'))
                callback_rate_f = float(callback_rate_dec)

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
                trade_state.trail_activation_price = trail_activation_price_dec_quant
                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f}, sl={sl_price_f}, tp={tp_price_f}, trailActivation={trail_activation_price_f}, trailDistance={2 * R} (2R)")

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

                try:
                    log("Cancelling all existing open orders for symbol before placing SL/TP...")
                    try:
                        cancel_res = client.cancel_all_open_orders(symbol)
                        log(f"Cancel all orders response: {cancel_res}")
                    except BinanceAPIError as e:
                        log(f"Failed to cancel existing orders: {str(e)}, payload: {e.payload}")
                    except Exception as e:
                        log(f"Failed to cancel existing orders: {str(e)}. Proceeding with SL/TP placement.")

                    try:
                        sl_res = place_sl_order_closepos(client, symbol, sl_price_dec_quant, close_side_for_sl)
                        trade_state.sl_order_id = sl_res.get("orderId")
                        log(f"SL response: {sl_res}")
                    except BinanceAPIError as e:
                        if e.payload and isinstance(e.payload, dict) and e.payload.get('code') == -1111:
                            log(f"SL precision error. Re-fetching filters and retrying...")
                            symbol_filters_cache = None
                            filters = get_symbol_filters(client, symbol)
                            tick_size = filters['tickSize']
                            sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                            sl_res = place_sl_order_closepos(client, symbol, sl_price_dec_quant, close_side_for_sl)
                            trade_state.sl_order_id = sl_res.get("orderId")
                            log(f"SL retry response: {sl_res}")
                        else:
                            raise

                    try:
                        tp_res = place_tp_order_closepos(client, symbol, tp_price_dec_quant, close_side_for_sl)
                        trade_state.tp_order_id = tp_res.get("orderId")
                        log(f"TP response: {tp_res}")
                    except BinanceAPIError as e:
                        if e.payload and isinstance(e.payload, dict) and e.payload.get('code') == -1111:
                            log(f"TP precision error. Re-fetching filters and retrying...")
                            symbol_filters_cache = None
                            filters = get_symbol_filters(client, symbol)
                            tick_size = filters['tickSize']
                            tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                            tp_res = place_tp_order_closepos(client, symbol, tp_price_dec_quant, close_side_for_sl)
                            trade_state.tp_order_id = tp_res.get("orderId")
                            log(f"TP retry response: {tp_res}")
                        else:
                            raise

                    if use_trailing:
                        log(f"Placing trailing stop: activationPrice={trail_activation_price_f}, callbackRate={callback_rate_f}%, trailDistance={2 * R} (2R)")
                        try:
                            trail_res = place_trailing_stop(client, symbol, close_side_for_sl, trail_activation_price_f, callback_rate_f, Decimal(str(actual_qty)), sl_price_dec_quant, R)
                            trade_state.trail_activated = False
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
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)

            elif trade_state.active or pending_entry:
                log("Trade active or pending. Skipping signal check.")

            else:
                log("No trade signal on candle close.")

            if last_processed_time != close_time:
                last_processed_time = close_time

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
    return 30 * 60 * 1000

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

# -------- SCHEDULER FOR REPORTS ----------
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

# -------- ENTRY POINT ----------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures RSI+MACD Bot (Headless, 30m Optimized, SOLUSDT)")
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
    parser.add_argument("--use-macd", action='store_true', default=False, help="Use MACD confirmation (default: False)")
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL for Binance API (advanced)")

    args = parser.parse_args()

    init_pnl_log()

    telegram_bot = Bot(token=args.telegram_token)

    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}, risk_pct={args.risk_pct}%, use_volume_filter={args.use_volume_filter}, use_macd={args.use_macd}")

    threading.Thread(target=lambda: run_scheduler(telegram_bot, args.chat_id), daemon=True).start()

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
        use_macd=args.use_macd,
        telegram_bot=telegram_bot,
        telegram_chat_id=args.chat_id
    )
