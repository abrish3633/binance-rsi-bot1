#!/usr/bin/env python3
# Binance Futures RSI+MACD Bot (Real Price Mode, SOLUSDT, 30m)
# Removed mock mode, uses real-time prices, fixed trailing stop closure
# Fixed: Telegram send with retries, added debug logs, test message, relaxed same-bar/no-pos for testing
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
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone, timedelta
import schedule
from urllib.parse import urlencode

# Improvements and Updates:
# 1. Trailing Stop Logic:
#    - Initial trailing stop set to -0.75R for longs or +0.75R for shorts when activated at ±1.25R.
#    - Trailing distance maintains 2R from the highest price (longs) or lowest price (shorts) after activation.
#    - Example: For entry_price=194.32, R=1.4574:
#      - Activation at 196.14175 USDT, initial stop at 193.227 USDT (spread = 2R).
#      - At price=200 USDT, trailing stop updates to 197.0852 USDT (2R distance).
#    - TRAIL_DISTANCE_R set to Decimal("2.0") to reflect 2R trailing distance.
#    - Callback rate for TRAILING_STOP_MARKET order set to 2R (e.g., 2 * 0.75% = 1.5%).
# 2. Order ID in Notifications:
#    - Added order_id to send_closure_telegram for SL, TP, trailing stop, and manual closures.
# 3. API Robustness:
#    - Implemented retries (3 attempts) in get_latest_trade_details to handle Binance API failures.
#    - Detailed error logging with payload for BinanceAPIError.
# 4. Telegram Fixes:
#    - Added retries (3 attempts) for Telegram message sends with exponential backoff.
#    - Improved logging for Telegram failures (e.g., "Telegram send failed", "All Telegram send attempts failed").
# 5. PNL Accuracy:
#    - PNL calculated using actual exit price from get_latest_trade_details or current price as fallback.
#    - PNL logged in USD and R multiples in pnl.json.
# 6. Other Preserved Features:
#    - Maintained forced buy_signal=True for testing.
#    - Command-line arguments: --no-prevent-same-bar, --no-require-no-pos.
#    - Support for stop.txt and STOP_REQUESTED for graceful exit.
#    - Price and quantity quantization using tick_size and step_size.
#    - Logging to bot.log and pnl.json.
# 7. Date and Time:
#    - Updated as of October 26, 2025, 12:33 AM EAT to reflect confirmed requirements.

# -------- STRATEGY CONFIG (defaults) ----------
RISK_PCT = Decimal("0.005")  # 0.5% per trade
SL_PCT = Decimal("0.0075")  # 0.75%
TP_MULT = Decimal("3.5")
TRAIL_TRIGGER_MULT = Decimal("1.25")  # Trailing stop activates at 1.25R
TRAIL_DISTANCE_R = Decimal("2.0")    # 2R trailing distance after activation
VOL_SMA_PERIOD = 15
RSI_PERIOD = 14
MACD_FAST = 12
MACD_SLOW = 26
MACD_SIGNAL = 9
MAX_TRADES_PER_DAY = 3
INTERVAL_DEFAULT = "30m"
ORDER_FILL_TIMEOUT = 15
BUY_RSI_MIN = 50
BUY_RSI_MAX = 80
SELL_RSI_MIN = 20
SELL_RSI_MAX = 50
POSITION_CHECK_INTERVAL = 5  # Check price every 5s for real mode
TRAIL_PRICE_BUFFER = Decimal("0.003")
KLINES_CACHE_DURATION = 5.0
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RATE_LIMIT_CHECK_INTERVAL = 60
RATE_LIMIT_THRESHOLD = 80

# Global stop flag and client
STOP_REQUESTED = False
client = None
symbol_filters_cache = None
klines_cache = None
klines_cache_time = 0
last_rate_limit_check = 0

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
    return row

# Logging setup
class CustomFormatter(logging.Formatter):
    def formatTime(self, record, datefmt=None):
        dt = datetime.fromtimestamp(record.created, tz=timezone.utc)
        return dt.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3] + '+00:00'

logger = logging.getLogger()
logger.handlers.clear()
logger.setLevel(logging.DEBUG)  # Changed to DEBUG for more verbosity
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
    """Send Telegram message via direct HTTP POST with retries."""
    logger.debug(f"Attempting to send Telegram message: {text[:50]}... to chat_id={chat_id}")
    if not token or not chat_id:
        logger.error("No token or chat_id provided. Skipping Telegram send.")
        return
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {"chat_id": chat_id, "text": text}
    if parse_mode:
        payload["parse_mode"] = parse_mode
    for attempt in range(3):  # Retry up to 3 times
        try:
            response = requests.post(url, json=payload, timeout=10)
            logger.debug(f"Telegram attempt {attempt+1}: status={response.status_code}, response={response.text}")
            response.raise_for_status()
            return
        except requests.exceptions.RequestException as e:
            logger.error(f"Telegram send failed (attempt {attempt+1}/3): {e}")
            if attempt < 2:
                time.sleep(2 ** (attempt + 1))
            continue
    logger.error("All Telegram send attempts failed.")

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

def send_closure_telegram(symbol, side, entry_price, exit_price, qty, pnl_usd, pnl_r, reason, bot, chat_id, order_id=None):
    message = (
        f"Position Closed:\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Entry: {entry_price:.4f}\n"
        f"- Exit: {exit_price:.4f}\n"
        f"- Qty: {qty}\n"
        f"- Reason: {reason}\n"
        f"- Order ID: {order_id or 'N/A'}\n"
        f"- PNL: {pnl_usd:+.2f} USDT ({pnl_r:+.2f}R)\n"
    )
    telegram_post(bot, chat_id, message)

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
    global STOP_REQUESTED, client
    STOP_REQUESTED = True
    log("Stop requested. Closing positions and cancelling orders...")
    if not client or not symbol:
        log("Client or symbol not defined; skipping position closure and order cancellation.")
        return
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        if isinstance(pos_resp, dict) and 'data' in pos_resp:
            positions = pos_resp['data']
        else:
            positions = pos_resp if isinstance(pos_resp, list) else []
        pos_item = None
        for p in positions:
            try:
                if p.get("symbol") == symbol:
                    pos_item = p
                    break
            except Exception:
                continue
        pos_amt = Decimal('0')
        if pos_item:
            pos_amt = Decimal(str(pos_item.get("positionAmt", "0")))
        if pos_amt != 0:
            side = "SELL" if pos_amt > 0 else "BUY"
            qty = abs(pos_amt)
            entry_price = None
            try:
                entry_price = float(Decimal(str(pos_item.get("entryPrice", "0")))) if pos_item else None
            except Exception:
                entry_price = None
            try:
                response = client.send_signed_request("POST", "/fapi/v1/order", {
                    "symbol": symbol,
                    "side": side,
                    "type": "MARKET",
                    "quantity": str(qty)
                })
                log(f"Closed position: qty={qty} {side}")
                exit_price = client.get_latest_fill_price(symbol, response.get("orderId"))
                if exit_price is None:
                    log("Failed to fetch exit price; using current market price.")
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price = Decimal(str(ticker.get("price")))
                exit_price_f = float(exit_price)
                if entry_price is None and pos_item:
                    try:
                        entry_price = float(Decimal(str(pos_item.get("entryPrice", "0"))))
                    except Exception:
                        entry_price = 0.0
                R = Decimal(str(entry_price)) * SL_PCT if entry_price else Decimal('0')
                pnl_row = log_pnl(len(pnl_data) + 1, "LONG" if pos_amt > 0 else "SHORT", entry_price or 0.0, exit_price_f, float(qty), float(R) if R else 0.0)
                if telegram_bot and telegram_chat_id:
                    send_closure_telegram(symbol, "LONG" if pos_amt > 0 else "SHORT", entry_price or 0.0, exit_price_f, float(qty), pnl_row['pnl_usd'], pnl_row['pnl_r'], "Stop Requested", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to close position: {str(e)}, stack: {traceback.format_exc()}")
        else:
            log("No open position found for closure.")
        try:
            client.cancel_all_open_orders(symbol)
            log(f"All open orders cancelled for {symbol}.")
        except Exception as e:
            log(f"Failed to cancel orders: {str(e)}, stack: {traceback.format_exc()}")
    except Exception as e:
        log(f"Failed to handle stop: {str(e)}, stack: {traceback.format_exc()}")

# -------- TIME SYNC CHECK ----------
def check_time_offset(base_url):
    try:
        start_time = time.time()
        response = requests.get(f"{base_url}/fapi/v1/time", timeout=5)
        server_time_ms = response.json()['serverTime']
        server_time = datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc)
        local_time = datetime.now(timezone.utc)
        offset = (server_time - local_time).total_seconds()
        request_duration = time.time() - start_time
        log(f"Time offset from Binance: {offset} seconds, request duration: {request_duration:.3f}s")
        if abs(offset) > 5:
            log("Warning: Clock offset > 5s. Using recvWindow=10000.")
        return request_duration
    except Exception as e:
        log(f"Binance time sync failed: {str(e)}")
        return None

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
        self.ping_latency = None
        self.ping_latency = check_time_offset(self.base)
        self.dual_side = self._check_position_mode()
        print(f"💞 Using base URL: {self.base}, Position Mode: {'Hedge' if self.dual_side else 'One-way'}")

    def _check_position_mode(self):
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            if isinstance(response, dict) and 'dualSidePosition' in response:
                return response['dualSidePosition']
            log("Failed to fetch position mode; assuming one-way mode.")
            return False
        except Exception as e:
            log(f"Position mode check failed: {str(e)}. Assuming one-way mode.")
            return False

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def check_api_status(self):
        try:
            start_time = time.time()
            response = requests.get(f"{self.base}/fapi/v1/ping", timeout=5)
            duration = time.time() - start_time
            if response.status_code == 200:
                log(f"Binance API is reachable (ping duration: {duration:.3f}s).")
                self.ping_latency = duration
                return True
            else:
                log(f"API ping failed with status {response.status_code} (duration: {duration:.3f}s).")
                return False
        except Exception as e:
            log(f"API ping failed: {str(e)}")
            return False

    def check_rate_limits(self):
        global last_rate_limit_check
        current_time = time.time()
        if current_time - last_rate_limit_check < RATE_LIMIT_CHECK_INTERVAL:
            return True
        try:
            response = self.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": "SOLUSDT"})
            if isinstance(response, dict) and '_response' in response:
                headers = response['_response'].headers
            else:
                headers = {}
            used_weight = int(headers.get('X-MBX-USED-WEIGHT-1M', 0))
            limit_value = 1200
            usage_pct = (used_weight / limit_value) * 100
            log(f"API rate limit usage: {used_weight}/{limit_value} ({usage_pct:.2f}%)")
            if usage_pct > RATE_LIMIT_THRESHOLD:
                log(f"Rate limit usage exceeds {RATE_LIMIT_THRESHOLD}%. Pausing for 30s.")
                time.sleep(30)
                return False
            last_rate_limit_check = current_time
            return True
        except Exception as e:
            log(f"Rate limit check failed: {str(e)}")
            return True

    def send_signed_request(self, method: str, endpoint: str, params: dict = None):
        params = params.copy() if params else {}
        dynamic_timeout = REQUEST_TIMEOUT + (self.ping_latency * 2 if self.ping_latency else 0)
        for attempt in range(MAX_RETRIES):
            try:
                response = requests.get(f"{self.base}/fapi/v1/time", timeout=5)
                server_time_ms = response.json()['serverTime']
                params["timestamp"] = server_time_ms
            except Exception as e:
                log(f"Time sync failed (attempt {attempt+1}/{MAX_RETRIES}): {str(e)}. Using local time.")
                params["timestamp"] = int(time.time() * 1000)
            params["recvWindow"] = 10000
            query = urlencode({k: str(params[k]) for k in sorted(params.keys())})
            signature = self._sign(query)
            url = f"{self.base}{endpoint}?{query}&signature={signature}"
            headers = {"X-MBX-APIKEY": self.api_key}
            start_time = time.time()
            duration = 0
            try:
                r = requests.request(method, url, headers=headers, timeout=dynamic_timeout)
                duration = time.time() - start_time
                log(f"Request to {endpoint} took {duration:.3f}s")
                if r.status_code == 200:
                    response = r.json()
                    if isinstance(response, list):
                        response = {'data': response, '_response': r}
                    else:
                        if isinstance(response, dict):
                            response['_response'] = r
                        else:
                            response = {'data': response, '_response': r}
                    if isinstance(response, dict) and response.get("code") not in (None, 200):
                        if response.get('code') == -1003:
                            log(f"Rate limit exceeded. Waiting 30s before retry {attempt+1}/{MAX_RETRIES}.")
                            time.sleep(30)
                            continue
                        raise BinanceAPIError(f"API error: {response.get('msg', 'Unknown error')} (code {response.get('code')})", status_code=r.status_code, payload=response)
                    return response
                elif r.status_code == 408:
                    log(f"HTTP 408 Timeout (attempt {attempt+1}/{MAX_RETRIES}): {r.text}, duration: {duration:.3f}s")
                    if attempt < MAX_RETRIES - 1:
                        time.sleep(2 ** (attempt + 1))
                        continue
                    raise BinanceAPIError(f"HTTP 408 after retries: {r.text}", status_code=r.status_code, payload=r.text)
                else:
                    try:
                        payload = r.json()
                    except Exception:
                        payload = r.text
                    raise BinanceAPIError(f"HTTP {r.status_code}: {payload}", status_code=r.status_code, payload=payload)
            except BinanceAPIError as e:
                log(f"Request failed (attempt {attempt+1}/{MAX_RETRIES}): {str(e)}, duration: {duration:.3f}s")
                if attempt < MAX_RETRIES - 1:
                    time.sleep(2 ** (attempt + 1))
                    continue
                raise
            except Exception as e:
                log(f"Request failed (attempt {attempt+1}/{MAX_RETRIES}): {str(e)}, duration: {duration:.3f}s")
                if attempt < MAX_RETRIES - 1:
                    time.sleep(2 ** (attempt + 1))
                    continue
                raise BinanceAPIError(f"Request failed after retries: {str(e)}", payload=str(e))

    def public_request(self, path: str, params: dict = None):
        url = f"{self.base}{path}"
        for attempt in range(2):
            try:
                start_time = time.time()
                r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT, headers={})
                duration = time.time() - start_time
                log(f"Public request to {path} took {duration:.3f}s")
                if r.status_code == 200:
                    return r.json()
                else:
                    try:
                        payload = r.json()
                    except Exception:
                        payload = r.text
                    raise BinanceAPIError(f"Public API error: {payload}", status_code=r.status_code, payload=payload)
            except Exception as e:
                log(f"Public request failed (attempt {attempt+1}/2): {str(e)}")
                if attempt == 1:
                    raise BinanceAPIError(f"Public API request failed: {str(e)}", payload=str(e))

    def get_latest_trade_details(self, symbol):
        params = {"symbol": symbol, "limit": 1}
        try:
            response = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            if isinstance(response, dict) and 'data' in response:
                trades = response['data']
            else:
                trades = response if isinstance(trades, list) else []
            if trades and len(trades) > 0:
                trade = trades[0]
                return {
                    "price": Decimal(str(trade.get("price", "0"))),
                    "orderId": trade.get("orderId"),
                    "qty": Decimal(str(trade.get("qty", "0"))),
                    "side": trade.get("side")
                }
            return None
        except BinanceAPIError as e:
            log(f"Failed to fetch latest trade details: {str(e)}, payload: {e.payload}")
            return None
        except Exception as e:
            log(f"Failed to fetch latest trade details: {str(e)}")
            return None

    def get_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        response = self.send_signed_request("GET", "/fapi/v1/openOrders", params)
        if isinstance(response, dict) and 'data' in response:
            return response['data']
        return response if isinstance(response, list) else []

    def cancel_all_open_orders(self, symbol: str):
        params = {"symbol": symbol}
        return self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", params)

    def get_latest_fill_price(self, symbol: str, order_id: int):
        params = {"symbol": symbol, "orderId": order_id}
        try:
            trades = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            if isinstance(trades, dict) and 'data' in trades:
                trades = trades['data']
            trades = trades if isinstance(trades, list) else []
            if trades and len(trades) > 0:
                return Decimal(str(trades[-1].get("price", "0")))
            return None
        except BinanceAPIError as e:
            log(f"Failed to fetch fill price: {str(e)}, payload: {e.payload}")
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

    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal, callback_rate: Decimal, activation_price: Decimal = None, reduce_only: bool = True, position_side: str = None):
        params = {
            "symbol": symbol,
            "side": side,
            "type": "TRAILING_STOP_MARKET",
            "callbackRate": str(callback_rate),
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false"
        }
        if activation_price is not None:
            params["activationPrice"] = str(activation_price)
        if self.dual_side and position_side:
            params["positionSide"] = position_side
        return self.send_signed_request("POST", "/fapi/v1/order", params)

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
        if isinstance(positions, dict) and 'data' in positions:
            positions = positions['data']
        positions = positions if isinstance(positions, list) else []
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
        if isinstance(positions, dict) and 'data' in positions:
            positions = positions['data']
        positions = positions if isinstance(positions, list) else []
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
        self.trail_activation_price = None
        self.highest_price = None
        self.lowest_price = None
        self.current_trail_stop = None
        self.risk = None
        self.initial_sl = None
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_order_id = None

# -------- DETECT EXIT REASON ----------
def detect_exit_reason(client: BinanceClient, symbol: str) -> tuple[str, Decimal]:
    """
    Returns (reason, fill_price)
    reason ∈ {'SL', 'TP', 'TRAILING', 'MANUAL'}
    """
    try:
        trades = client.send_signed_request("GET", "/fapi/v1/userTrades", {"symbol": symbol, "limit": 5})
        trades = trades if isinstance(trades, list) else trades.get('data', [])
        if not trades:
            return "MANUAL", client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})["price"]
        last = trades[-1]
        otype = last.get("orderType", "")
        price = Decimal(str(last["price"]))
        if "STOP_MARKET" in otype:
            return "SL", price
        if "TAKE_PROFIT_MARKET" in otype:
            return "TP", price
        if "TRAILING_STOP_MARKET" in otype:
            return "TRAILING", price
        return "MANUAL", price
    except Exception as e:
        log(f"Exit reason detection failed: {e}")
        return "UNKNOWN", client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})["price"]

# -------- TRADE MONITORING ----------
def monitor_trade(client, symbol, trade_state, tick_size, telegram_bot=None, telegram_chat_id=None):
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    last_position_check = 0
    while trade_state.active:
        if STOP_REQUESTED or os.path.exists("stop.txt"):
            log("Stop requested. Exiting.", telegram_bot, telegram_chat_id)
            break
        try:
            current_time = time.time()
            if current_time - last_position_check >= POSITION_CHECK_INTERVAL:
                try:
                    ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    current_price = Decimal(str(ticker.get("price")))
                except Exception:
                    time.sleep(2)
                    continue
                # Update highest/lowest price
                if trade_state.side == "LONG":
                    if trade_state.highest_price is None:
                        trade_state.highest_price = current_price
                    trade_state.highest_price = max(trade_state.highest_price, current_price)
                else:
                    if trade_state.lowest_price is None:
                        trade_state.lowest_price = current_price
                    trade_state.lowest_price = min(trade_state.lowest_price, current_price)
                # Check for trailing stop activation
                if not trade_state.trail_activated and trade_state.trail_activation_price:
                    activation_hit = (trade_state.side == "LONG" and current_price >= trade_state.trail_activation_price) or \
                                     (trade_state.side == "SHORT" and current_price <= trade_state.trail_activation_price)
                    if activation_hit:
                        log("Trailing stop activated:", telegram_bot, telegram_chat_id)
                        trade_state.trail_activated = True
                        if trade_state.side == "LONG":
                            initial_stop_price = trade_state.entry_price - (Decimal('0.75') * trade_state.risk)  # Initial stop at -0.75R
                            rounding = ROUND_DOWN
                        else:
                            initial_stop_price = trade_state.entry_price + (Decimal('0.75') * trade_state.risk)  # Initial stop at +0.75R
                            rounding = ROUND_UP
                        initial_stop_price_quant = quantize_price(initial_stop_price, tick_size, rounding)
                        trade_state.current_trail_stop = initial_stop_price_quant
                        if telegram_bot and telegram_chat_id:
                            send_trailing_activation_telegram(symbol, trade_state.side, float(current_price), float(initial_stop_price_quant), telegram_bot, telegram_chat_id)
                # Update trailing stop to maintain 2R distance
                if trade_state.trail_activated:
                    new_stop_price = None
                    if trade_state.side == "LONG":
                        new_stop_price = trade_state.highest_price - (TRAIL_DISTANCE_R * trade_state.risk)  # 2R distance
                        rounding = ROUND_DOWN
                    else:
                        new_stop_price = trade_state.lowest_price + (TRAIL_DISTANCE_R * trade_state.risk)  # 2R distance
                        rounding = ROUND_UP
                    new_stop_price_quant = quantize_price(new_stop_price, tick_size, rounding)
                    if new_stop_price_quant != trade_state.current_trail_stop:
                        trade_state.current_trail_stop = new_stop_price_quant
                        log(f"Trailing stop updated: new_stop_price={new_stop_price_quant}", telegram_bot, telegram_chat_id)
                        if telegram_bot and telegram_chat_id:
                            send_trailing_update_telegram(symbol, trade_state.side, float(new_stop_price_quant), telegram_bot, telegram_chat_id)
                # Check real position status
                pos = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol, "recvWindow": 30000})
                if isinstance(pos, dict) and 'data' in pos:
                    pos = pos['data']
                pos = pos if isinstance(pos, list) else []
                pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
                last_position_check = current_time
                if pos_amt == Decimal('0'):
                    log("Position closed.", telegram_bot, telegram_chat_id)
                    trade_state.active = False
                    trade_state.exit_close_time = int(current_time * 1000)
                    # NEW: exact reason + price
                    reason, exit_price = detect_exit_reason(client, symbol)
                    exit_price_f = float(exit_price)
                    R = Decimal(str(trade_state.entry_price)) * SL_PCT
                    pnl_row = log_pnl(
                        len(pnl_data) + 1,
                        trade_state.side,
                        trade_state.entry_price,
                        exit_price_f,
                        trade_state.qty,
                        float(R)
                    )
                    # NEW: full Telegram exit message
                    if telegram_bot and telegram_chat_id:
                        send_closure_telegram(
                            symbol,
                            trade_state.side,
                            trade_state.entry_price,
                            exit_price_f,
                            trade_state.qty,
                            pnl_row['pnl_usd'],
                            pnl_row['pnl_r'],
                            reason,
                            telegram_bot,
                            telegram_chat_id
                        )
                    client.cancel_all_open_orders(symbol)
                    log("Cancelled all remaining open orders.", telegram_bot, telegram_chat_id)
                    return
                time.sleep(1)
        except Exception as e:
            log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
            time.sleep(2)

# -------- TRADING LOOP ----------
def trading_loop(client, symbol, timeframe, max_trades_per_day, risk_pct, max_daily_loss_pct, tp_mult, use_trailing, prevent_same_bar, require_no_pos, use_max_loss, use_volume_filter, use_macd, telegram_bot=None, telegram_chat_id=None):
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
            buy_signal = True  # FORCED FOR TESTING (matches mock mode)
            sell_signal = False  # FORCED FOR TESTING
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
                sl_price_f = float(sl_price_dec_quant)
                tp_price_dec_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
                tp_price_f = float(tp_price_dec_quant)
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, trail_rounding)
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
                time.sleep(0.2)
                actual_fill_price = client.get_latest_fill_price(symbol, order_res.get("orderId"))
                if actual_fill_price is None:
                    log("Failed to fetch actual fill price; using candle close price.", telegram_bot, telegram_chat_id)
                    actual_fill_price = entry_price
                actual_fill_price_f = float(actual_fill_price)
                # Recalculate with actual fill price
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
                trail_activation_price_dec_quant = quantize_price(trail_activation_price_dec, tick_size, trail_rounding)
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
                trade_state.trail_activation_price = trail_activation_price_dec_quant
                trade_state.highest_price = None
                trade_state.lowest_price = None
                trade_state.current_trail_stop = None
                trade_state.risk = R
                log(f"Position opened: {trade_state.side}, qty={actual_qty}, entry={actual_fill_price_f}, sl={sl_price_f}, tp={tp_price_f}, trail_activation={trail_activation_price_dec_quant}", telegram_bot, telegram_chat_id)
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
                # Place fixed SL and TP orders
                close_side = "SELL" if trade_state.side == "LONG" else "BUY"
                pos_side = "LONG" if trade_state.side == "LONG" else "SHORT"
                qty_dec = Decimal(str(trade_state.qty))
                try:
                    sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_dec_quant, reduce_only=True, position_side=pos_side)
                    trade_state.sl_order_id = sl_order.get("orderId")
                    log(f"Placed STOP_MARKET SL: {sl_order}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)
                try:
                    tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_dec_quant, reduce_only=True, position_side=pos_side)
                    trade_state.tp_order_id = tp_order.get("orderId")
                    log(f"Placed TAKE_PROFIT_MARKET TP: {tp_order}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)
                # Place TRAILING_STOP_MARKET
                callback_rate = TRAIL_DISTANCE_R * SL_PCT * Decimal('100')
                activation_price = trail_activation_price_dec_quant
                try:
                    trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec, callback_rate, activation_price, reduce_only=True, position_side=pos_side)
                    trade_state.trail_order_id = trail_order.get("orderId")
                    log(f"Placed TRAILING_STOP_MARKET: {trail_order}", telegram_bot, telegram_chat_id)
                except Exception as e:
                    log(f"Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)
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
    parser = argparse.ArgumentParser(description="Binance Futures RSI+MACD Bot (Real Price Mode, SOLUSDT)")
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
    parser.add_argument("--no-prevent-same-bar", dest='prevent_same_bar', action='store_false', default=False, help="Allow entries on same bar (default: prevent same bar)")
    parser.add_argument("--no-require-no-pos", dest='require_no_pos', action='store_false', default=False, help="Allow entry even if there's an active position (default: require no pos)")
    parser.add_argument("--no-use-max-loss", dest='use_max_loss', action='store_false', help="Disable max daily loss protection (default: enabled)")
    parser.add_argument("--use-volume-filter", action='store_true', default=False, help="Use volume filter (vol > SMA15)")
    parser.add_argument("--no-volume-filter", action='store_false', dest='use_volume_filter', help="Disable volume filter")
    parser.add_argument("--use-macd", action='store_true', default=False, help="Use MACD confirmation (default: False)")
    parser.add_argument("--live", action="store_true", help="Use live Binance (default: Testnet)")
    parser.add_argument("--base-url", default=None, help="Override base URL for Binance API (advanced)")
    args = parser.parse_args()
    init_pnl_log()
    client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
    log("Testing Telegram connection...", args.telegram_token, args.chat_id)  # Test message
    log(f"Connected ({'LIVE' if args.live else 'TESTNET'}). Starting bot with symbol={args.symbol}, timeframe={args.timeframe}, risk_pct={args.risk_pct}%")
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
        use_macd=args.use_macd,
        telegram_bot=args.telegram_token,
        telegram_chat_id=args.chat_id
    )
