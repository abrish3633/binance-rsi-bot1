#!/usr/bin/env python3
# Binance Futures RSI Bot (SOLUSDT, 30m, Trailing Stop, Telegram Alerts)
# LOGGING + TELEGRAM: EXACTLY AS YOU SPECIFIED
# Startup, Balance, Candle, Signal, Entry, Orders, Monitoring — ALL VERBOSE

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
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone
from urllib.parse import urlencode

# -------- STRATEGY CONFIG ----------
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
BUY_RSI_MIN = 50
BUY_RSI_MAX = 80
SELL_RSI_MIN = 20
SELL_RSI_MAX = 50
REQUEST_TIMEOUT = 30
RECOVERY_CHECK_INTERVAL = 10
TRAIL_UPDATE_THROTTLE = 10.0

# Global stop flag
STOP_REQUESTED = False

# PnL tracking
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data = []

def init_pnl_log():
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r'])
            writer.writeheader()

def log_pnl(trade_id, side, entry, exit_price, qty, R):
    entry = float(entry)
    exit_price = float(exit_price)
    qty = float(qty)
    R = float(R) if R > 0 else 0.0
    pnl_usd = (exit_price - entry) * qty if side == 'LONG' else (entry - exit_price) * qty
    pnl_r = pnl_usd / R if R > 0 else 0.0
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'entry': f"{entry:.4f}",
        'exit': f"{exit_price:.4f}",
        'pnl_usd': round(pnl_usd, 2),
        'pnl_r': round(pnl_r, 2)
    }
    pnl_data.append(row)
    with open(PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=row.keys())
        if f.tell() == 0:
            writer.writeheader()
        writer.writerow({k: str(v) if isinstance(v, float) else v for k, v in row.items()})
    return row

# Logging
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

def telegram_post(token, chat_id, text):
    if not token or not chat_id:
        return
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    try:
        requests.post(url, json={"chat_id": chat_id, "text": text}, timeout=10)
    except Exception as e:
        logger.error(f"Telegram send failed: {e}")

def send_trade_telegram(trade_details, bot, chat_id):
    message = (
        f"New Trade Entry:\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"- Trailing Activation: {trade_details['trail_activation']:.4f}\n"
        f"- Qty: {trade_details['qty']:.4f}\n"
    )
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol, side, entry_price, exit_price, qty, pnl_usd, pnl_r, reason, bot, chat_id):
    entry_price = float(entry_price) if entry_price is not None else 0.0
    exit_price = float(exit_price)
    qty = float(qty)
    pnl_usd = float(pnl_usd)
    pnl_r = float(pnl_r)
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry Price: {entry_price:.4f}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Reason: {reason}\n"
        f"- Qty: {qty:.4f}\n"
        f"- PNL: {pnl_usd:+.2f} USDT ({pnl_r:+.2f}R)\n"
    )
    telegram_post(bot, chat_id, message)

# -------- STOP HANDLER ----------
def _request_stop(signum, frame, symbol=None, telegram_bot=None, telegram_chat_id=None, client=None):
    global STOP_REQUESTED
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...", telegram_bot, telegram_chat_id)
    if not client or not symbol:
        log("Client or symbol not defined; skipping closure.")
        return
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp['data'] if isinstance(pos_resp, dict) and 'data' in pos_resp else pos_resp if isinstance(pos_resp, list) else []
        pos_item = next((p for p in positions if p.get("symbol") == symbol), None)
        pos_amt = Decimal(str(pos_item.get("positionAmt", "0"))) if pos_item else Decimal('0')
        if pos_amt != 0:
            side = "SELL" if pos_amt > 0 else "BUY"
            qty = abs(pos_amt)
            entry_price = float(Decimal(str(pos_item.get("entryPrice", "0")))) if pos_item else 0.0
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
            R = Decimal(str(entry_price)) * SL_PCT if entry_price else Decimal('0')
            pnl_row = log_pnl(len(pnl_data) + 1, "LONG" if pos_amt > 0 else "SHORT", entry_price, exit_price_f, float(qty), float(R))
            if telegram_bot and telegram_chat_id:
                send_closure_telegram(symbol, "LONG" if pos_amt > 0 else "SHORT", entry_price, exit_price_f, float(qty), pnl_row['pnl_usd'], pnl_row['pnl_r'], "Stop Requested", telegram_bot, telegram_chat_id)
        client.cancel_all_open_orders(symbol)
        log(f"All open orders cancelled for {symbol}.")
    except Exception as e:
        log(f"Stop handler error: {str(e)}")

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
        self.dual_side = self._check_position_mode()

    def _check_position_mode(self):
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            return response.get('dualSidePosition', False)
        except:
            return False

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: dict = None):
        params = params or {}
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
            raise BinanceAPIError(f"Request failed: {str(e)}")

    def public_request(self, path: str, params: dict = None):
        url = f"{self.base}{path}"
        try:
            r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                return r.json()
            else:
                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}")
        except Exception as e:
            raise BinanceAPIError(f"Public request failed: {str(e)}")

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
            log(f"Failed to fetch latest trade: {str(e)}")
            return None

    def get_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        response = self.send_signed_request("GET", "/fapi/v1/openOrders", params)
        return response if isinstance(response, list) else []

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

# -------- UTILITIES ----------
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
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return round(100 - 100 / (1 + rs), 2)

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

def get_symbol_filters(client: BinanceClient, symbol: str):
    info = client.public_request("/fapi/v1/exchangeInfo")
    s = next((x for x in info.get("symbols", []) if x.get("symbol") == symbol.upper()), None)
    if not s:
        raise ValueError(f"{symbol} not found")
    filters = {f["filterType"]: f for f in s.get("filters", [])}
    lot = filters.get("LOT_SIZE")
    if not lot:
        raise ValueError("LOT_SIZE missing")
    step_size = Decimal(str(lot["stepSize"]))
    min_qty = Decimal(str(lot["minQty"]))
    tick_size = Decimal(str(filters.get("PRICE_FILTER", {}).get("tickSize", "0.00000001")))
    min_notional = Decimal(str(filters.get("MIN_NOTIONAL", {}).get("notional", "0")))
    return {"stepSize": step_size, "minQty": min_qty, "tickSize": tick_size, "minNotional": min_notional}

def place_market_order(client: BinanceClient, symbol: str, side: str, quantity):
    params = {
        "symbol": symbol,
        "side": side,
        "type": "MARKET",
        "quantity": str(quantity)
    }
    return client.send_signed_request("POST", "/fapi/v1/order", params)

def fetch_klines(client: BinanceClient, symbol: str, interval: str, limit=100):
    data = client.public_request("/fapi/v1/klines", {"symbol": symbol, "interval": interval, "limit": limit})
    return data

def fetch_balance(client: BinanceClient):
    data = client.send_signed_request("GET", "/fapi/v2/account")
    return Decimal(str(data.get("totalWalletBalance", 0)))

def has_active_position(client: BinanceClient, symbol: str):
    positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
    for p in positions:
        if p.get("symbol") == symbol and Decimal(str(p.get("positionAmt", "0"))) != 0:
            return True
    return False

def fetch_open_positions_details(client: BinanceClient, symbol: str):
    positions = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
    return next((p for p in positions if p.get("symbol") == symbol), None)

# -------- TRADE STATE ----------
class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price = None
        self.qty = None
        self.side = None
        self.entry_close_time = None
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
def debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    if not trade_state.active:
        return
    try:
        open_orders = client.get_open_orders(symbol)
        entry_price = Decimal(str(trade_state.entry_price or 0))
        if entry_price <= 0:
            return

        if trade_state.sl_order_id and not any(o.get("orderId") == trade_state.sl_order_id for o in open_orders):
            log(f"SL missing. Recovering...", telegram_bot, telegram_chat_id)
            sl_price_dec = entry_price * (Decimal("1") - SL_PCT) if trade_state.side == "LONG" else entry_price * (Decimal("1") + SL_PCT)
            sl_rounding = ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP
            sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            qty_dec = Decimal(str(trade_state.qty))
            sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=trade_state.side)
            trade_state.sl_order_id = sl_order.get("orderId")
            trade_state.sl = float(sl_price_dec_quant)
            telegram_post(telegram_bot, telegram_chat_id, f"SL Recovered\nStop: {trade_state.sl:.4f}\nID: {trade_state.sl_order_id}")

        if trade_state.tp_order_id and not any(o.get("orderId") == trade_state.tp_order_id for o in open_orders):
            log(f"TP missing. Recovering...", telegram_bot, telegram_chat_id)
            R = entry_price * SL_PCT
            tp_price_dec = entry_price + (TP_MULT * R) if trade_state.side == "LONG" else entry_price - (TP_MULT * R)
            tp_rounding = ROUND_UP if trade_state.side == "LONG" else ROUND_DOWN
            tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            qty_dec = Decimal(str(trade_state.qty))
            tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=trade_state.side)
            trade_state.tp_order_id = tp_order.get("orderId")
            trade_state.tp = float(tp_price_dec_quant)
            telegram_post(telegram_bot, telegram_chat_id, f"TP Recovered\nTP: {trade_state.tp:.4f}\nID: {trade_state.tp_order_id}")

        if trade_state.trail_order_id and not any(o.get("orderId") == trade_state.trail_order_id for o in open_orders):
            log(f"Trailing missing. Recovering...", telegram_bot, telegram_chat_id)
            R = entry_price * SL_PCT
            trail_activation_price_dec = entry_price + (TRAIL_TRIGGER_MULT * R) if trade_state.side == "LONG" else entry_price - (TRAIL_TRIGGER_MULT * R)
            trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)
            callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            qty_dec = Decimal(str(trade_state.qty))
            trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, trail_activation_price_dec_quant, reduce_only=True, position_side=trade_state.side)
            trade_state.trail_order_id = trail_order.get("orderId")
            trade_state.trail_activation_price = trail_activation_price_dec_quant
            telegram_post(telegram_bot, telegram_chat_id, f"Trailing Recovered\nActivation: {float(trail_activation_price_dec_quant):.4f}\nID: {trade_state.trail_order_id}")

    except Exception as e:
        log(f"Recovery error: {str(e)}", telegram_bot, telegram_chat_id)

# -------- MONITOR TRADE ----------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    last_recovery_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
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
                log("Position closed.", telegram_bot, telegram_chat_id)
                trade_state.active = False
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
                price_data = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                price = Decimal(str(price_data["price"]))
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
                    R = Decimal(str(trade_state.risk))
                    init_stop = trade_state.entry_price - (TRAIL_DISTANCE_MULT * float(R)) if trade_state.side == "LONG" else \
                                trade_state.entry_price + (TRAIL_DISTANCE_MULT * float(R))
                    init_stop = quantize_price(Decimal(str(init_stop)), tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                    send_trailing_activation_telegram(symbol, trade_state.side, float(price), float(init_stop), telegram_bot, telegram_chat_id)
                    trade_state.current_trail_stop = init_stop

            if trade_state.trail_activated and time.time() - trade_state.last_trail_alert >= TRAIL_UPDATE_THROTTLE:
                R = Decimal(str(trade_state.risk))
                new_stop_raw = trade_state.highest_price - (TRAIL_DISTANCE_MULT * R) if trade_state.side == "LONG" else \
                               trade_state.lowest_price + (TRAIL_DISTANCE_MULT * R)
                new_stop = quantize_price(new_stop_raw, tick_size, ROUND_DOWN if trade_state.side == "LONG" else ROUND_UP)
                if (trade_state.current_trail_stop is None or
                    (trade_state.side == "LONG" and new_stop > trade_state.current_trail_stop) or
                    (trade_state.side == "SHORT" and new_stop < trade_state.current_trail_stop)):
                    trade_state.current_trail_stop = new_stop
                    send_trailing_update_telegram(symbol, trade_state.side, float(new_stop), telegram_bot, telegram_chat_id)
                    trade_state.last_trail_alert = time.time()

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

    # Signal handlers
    def make_handler(client):
        def handler(signum, frame):
            _request_stop(signum, frame, symbol, telegram_bot, telegram_chat_id, client)
        return handler
    signal.signal(signal.SIGINT, make_handler(client))
    signal.signal(signal.SIGTERM, make_handler(client))

    # === STARTUP LOG + TELEGRAM ===
    mode = 'LIVE' if client.use_live else 'TESTNET'
    startup_msg = (
        f"Connected ({mode}). Starting bot with "
        f"symbol={symbol}, timeframe={timeframe}, risk_pct={risk_pct*100:.1f}%, "
        f"use_volume_filter={use_volume_filter}\n"
        f"Fetched balance: {daily_start_balance:.2f} USDT"
    )
    log(startup_msg, telegram_bot, telegram_chat_id)

    # Recovery
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol)
        pos_amt = Decimal(str(pos.get("positionAmt", "0")))
        if pos_amt != 0:
            trade_state.active = True
            trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
            trade_state.qty = float(abs(pos_amt))
            trade_state.entry_price = float(Decimal(str(pos.get("entryPrice", "0"))))
            trade_state.risk = Decimal(str(trade_state.entry_price)) * SL_PCT
            log("Existing position detected. Recovering orders...", telegram_bot, telegram_chat_id)
            debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
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
            server_time = int(time.time() * 1000)
            try:
                server_time_response = client.public_request("/fapi/v1/time")
                server_time = server_time_response["serverTime"]
            except:
                pass
            next_close_ms = last_processed_time + interval_ms(timeframe)
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                log(f"Waiting for candle close in {sleep_seconds:.2f}s", telegram_bot, telegram_chat_id)
                _safe_sleep(sleep_seconds)
                continue
            klines = fetch_klines(client, symbol, timeframe, limit=100)
            closes, volumes, close_times, opens = closes_and_volumes_from_klines(klines)
            last_close_time = close_times[-1]
            if last_processed_time == last_close_time:
                time.sleep(1)
                continue

            rsi = compute_rsi(closes)
            vol_sma15 = sma(volumes, VOL_SMA_PERIOD)
            curr_vol = volumes[-1]
            close_price = Decimal(str(closes[-1]))
            open_price = Decimal(str(opens[-1]))
            is_green_candle = close_price > open_price
            is_red_candle = close_price < open_price
            candle_color = "Green" if is_green_candle else "Red" if is_red_candle else "Doji"

            log(f"Candle close price={close_price} RSI={rsi:.2f} Vol={curr_vol:.2f} SMA15={vol_sma15:.2f} {candle_color} candle", telegram_bot, telegram_chat_id)

            signal_msg = None
            if (rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green_candle and (not use_volume_filter or curr_vol > vol_sma15)):
                signal_msg = "Signal on candle close -> BUY. Preparing entry."
            elif (rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red_candle and (not use_volume_filter or curr_vol > vol_sma15)):
                signal_msg = "Signal on candle close -> SELL. Preparing entry."
            else:
                signal_msg = "No trade signal on candle close."
            log(signal_msg, telegram_bot, telegram_chat_id)

            if prevent_same_bar and trade_state.entry_close_time == last_close_time:
                last_processed_time = last_close_time
                continue
            if require_no_pos and has_active_position(client, symbol):
                last_processed_time = last_close_time
                continue
            if use_volume_filter and vol_sma15 is None:
                last_processed_time = last_close_time
                continue

            buy_signal = signal_msg and "BUY" in signal_msg
            sell_signal = signal_msg and "SELL" in signal_msg

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry:
                last_processed_time = last_close_time
                side_text = "BUY" if buy_signal else "SELL"
                pending_entry = True
                entry_price = close_price
                R = entry_price * SL_PCT
                if R <= 0:
                    pending_entry = False
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

                log(f"Sending MARKET {side_text} order: qty={qty_api}, entry_price={entry_price}", telegram_bot, telegram_chat_id)
                order_res = place_market_order(client, symbol, side_text, qty_api)
                log(f"Market order placed: {order_res}", telegram_bot, telegram_chat_id)

                log("Waiting for entry order to fill...", telegram_bot, telegram_chat_id)
                start_time = time.time()
                actual_qty = None
                while time.time() - start_time < ORDER_FILL_TIMEOUT:
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        break
                    pos = fetch_open_positions_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0"))) if pos else Decimal('0')
                    if pos_amt != 0:
                        actual_qty = abs(pos_amt)
                        break
                    time.sleep(0.5)
                if not actual_qty:
                    pending_entry = False
                    continue

                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if not actual_fill_price:
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)
                R = actual_fill_price * SL_PCT
                sl_price_dec = actual_fill_price * (Decimal("1") - SL_PCT) if buy_signal else actual_fill_price * (Decimal("1") + SL_PCT)
                tp_price_dec = actual_fill_price + (tp_mult * R) if buy_signal else actual_fill_price - (tp_mult * R)
                trail_activation_price_dec = actual_fill_price + (TRAIL_TRIGGER_MULT * R) if buy_signal else actual_fill_price - (TRAIL_TRIGGER_MULT * R)
                sl_rounding = ROUND_DOWN if buy_signal else ROUND_UP
                tp_rounding = ROUND_UP if buy_signal else ROUND_DOWN
                sl_price_dec_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size)

                trade_state.active = True
                trade_state.entry_price = actual_fill_price_f
                trade_state.risk = R
                trade_state.qty = float(actual_qty)
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = last_close_time
                trade_state.sl = float(sl_price_dec_quant)
                trade_state.tp = float(tp_price_dec_quant)
                trade_state.trail_activation_price = trail_activation_price_dec_quant

                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f:.4f}, "
                    f"sl={sl_price_dec_quant:.4f}, tp={tp_price_dec_quant:.4f}, "
                    f"trail_activation={trail_activation_price_dec_quant:.4f}", telegram_bot, telegram_chat_id)

                trade_details = {
                    'symbol': symbol,
                    'side': trade_state.side,
                    'entry': trade_state.entry_price,
                    'sl': trade_state.sl,
                    'tp': trade_state.tp,
                    'trail_activation': float(trail_activation_price_dec_quant),
                    'qty': trade_state.qty
                }
                send_trade_telegram(trade_details, telegram_bot, telegram_chat_id)

                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                qty_dec = Decimal(str(trade_state.qty))

                sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=trade_state.side)
                log(f"Placed STOP_MARKET SL: {sl_order}", telegram_bot, telegram_chat_id)
                trade_state.sl_order_id = sl_order.get("orderId")

                tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=trade_state.side)
                log(f"Placed TAKE_PROFIT_MARKET TP: {tp_order}", telegram_bot, telegram_chat_id)
                trade_state.tp_order_id = tp_order.get("orderId")

                callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
                trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, trail_activation_price_dec_quant, reduce_only=True, position_side=trade_state.side)
                log(f"Placed TRAILING_STOP_MARKET: {trail_order}", telegram_bot, telegram_chat_id)
                trade_state.trail_order_id = trail_order.get("orderId")

                trades_today += 1
                pending_entry = False
                monitor_trade(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)

            last_processed_time = last_close_time
            _safe_sleep(1)
        except Exception as e:
            log(f"Loop error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)
    log("Trading loop exited.", telegram_bot, telegram_chat_id)

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

# -------- ENTRY POINT ----------
if __name__ == "__main__":
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
    args = parser.parse_args()
    init_pnl_log()
    
    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live)
    
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
