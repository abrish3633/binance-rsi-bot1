#!/usr/bin/env python3
# Enhanced Binance Futures Trading Bot
# - Optimized for SOLUSDT on 30m timeframe
# - Uses RSI, MACD, volume filters for signals
# - Risk management with SL, TP, trailing stops
# - Telegram notifications for entries, exits, and reports
# - PnL tracking and periodic reports
# - Graceful shutdown with position closure
# - Improved indicator calculations using proper EMA for MACD and Wilder's RSI
# - Consistent use of Decimal for precision
# - Optimized API calls (public endpoints without signing)
# - Enhanced error handling and retries
# - Daily loss and trade count reset
# - Exact exit price from user trades
# - Leverage setting
# - PEP8 compliant, with docstrings and type hints

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
from decimal import Decimal, ROUND_DOWN, ROUND_UP
from datetime import datetime, timezone, timedelta, date
from urllib.parse import urlencode
from telegram import Bot
import schedule
import asyncio
import certifi
from typing import Dict, List, Optional, Tuple

# -------- LOGGING SETUP ----------
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

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
KLINES_CACHE_DURATION = 0  # Disabled for fresh data
KLINES_LIMIT = 200  # For accurate indicators

# Global flags and variables
STOP_REQUESTED = False
TRADE_ID_COUNTER = 0
PNL_LOG_FILE = 'pnl_log.csv'
pnl_data: List[Dict[str, any]] = []  # For in-memory PnL reports

def init_pnl_log() -> None:
    """Initialize PnL log CSV if it doesn't exist."""
    if not os.path.exists(PNL_LOG_FILE):
        with open(PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r'])
            writer.writeheader()

def log_pnl(trade_id: int, side: str, entry: Decimal, exit_price: Decimal, qty: Decimal, r: Decimal) -> None:
    """Log PnL for a closed trade to CSV and in-memory list."""
    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty
    pnl_r = pnl_usd / r if r > 0 else Decimal('0')
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
    logger.info(f"PnL logged for trade {trade_id}: {pnl_usd:.2f} USD ({pnl_r:.2f}R)")

def get_pnl_total_usd(period: str = 'daily') -> float:
    """Get total PnL USD for the specified period."""
    if not pnl_data:
        return 0.0
    end_date = datetime.now(timezone.utc)
    if period == 'daily':
        start_date = end_date - timedelta(days=1)
    elif period == 'weekly':
        start_date = end_date - timedelta(weeks=1)
    elif period == 'monthly':
        start_date = end_date - timedelta(days=30)  # Approximate
    else:
        raise ValueError("Invalid period.")
    period_trades = [trade for trade in pnl_data if datetime.fromisoformat(trade['date']) >= start_date]
    return sum(trade['pnl_usd'] for trade in period_trades)

def calculate_pnl_report(period: str = 'daily') -> str:
    """Generate PnL report for the specified period."""
    if not pnl_data:
        return "No trades recorded."
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
    report = (
        f"{period.capitalize()} PnL Report:\n"
        f"- Trades: {num_trades}\n"
        f"- Win Rate: {win_rate:.2f}%\n"
        f"- Total PnL: ${total_pnl_usd:.2f}\n"
        f"- Total PnL: {total_pnl_r:.2f}R"
    )
    return report

async def send_telegram_message(bot: Bot, chat_id: str, message: str) -> None:
    """Asynchronously send a message via Telegram."""
    try:
        await bot.send_message(chat_id=chat_id, text=message)
        logger.info(f"Telegram message sent: {message[:50]}...")
    except Exception as e:
        logger.error(f"Telegram send failed: {str(e)}")

def send_entry_telegram(trade_details: Dict[str, any], bot: Bot, chat_id: str) -> None:
    """Send Telegram notification for new trade entry."""
    message = (
        f"New Trade Entry (ID: {trade_details['trade_id']}):\n"
        f"- Symbol: {trade_details['symbol']}\n"
        f"- Side: {trade_details['side']}\n"
        f"- Entry Price: {trade_details['entry']:.4f}\n"
        f"- SL: {trade_details['sl']:.4f}\n"
        f"- TP: {trade_details['tp']:.4f}\n"
        f"- Trailing Activation: {trade_details['trail_activation']:.4f}\n"
        f"- Qty: {trade_details['qty']}"
    )
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, message))).start()

def send_exit_telegram(symbol: str, trade_id: int, side: str, exit_price: float, qty: float, reason: str, bot: Bot, chat_id: str) -> None:
    """Send Telegram notification for trade exit."""
    message = (
        f"Trade Exit (ID: {trade_id}):\n"
        f"- Symbol: {symbol}\n"
        f"- Side: {side}\n"
        f"- Exit Price: {exit_price:.4f}\n"
        f"- Qty: {qty}\n"
        f"- Reason: {reason}"
    )
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, message))).start()

def send_daily_report(bot: Bot, chat_id: str) -> None:
    """Send daily PnL report via Telegram."""
    report = calculate_pnl_report('daily')
    subject = f"Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def send_weekly_report(bot: Bot, chat_id: str) -> None:
    """Send weekly PnL report via Telegram."""
    report = calculate_pnl_report('weekly')
    subject = f"Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def send_monthly_report(bot: Bot, chat_id: str) -> None:
    """Send monthly PnL report via Telegram."""
    report = calculate_pnl_report('monthly')
    subject = f"Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    threading.Thread(target=lambda: asyncio.run(send_telegram_message(bot, chat_id, f"{subject}\n{report}"))).start()

def request_stop(signum: int, frame: any, client: 'BinanceClient', symbol: str) -> None:
    """Handle stop signal: close positions and cancel orders."""
    global STOP_REQUESTED
    STOP_REQUESTED = True
    logger.info("Stop requested. Closing positions and cancelling orders...")
    if client and symbol:
        try:
            pos = client.get_position_risk(symbol)
            pos_amt = Decimal(str(pos[0].get("positionAmt", "0"))) if pos and len(pos) > 0 else Decimal('0')
            if pos_amt != Decimal('0'):
                side = "SELL" if pos_amt > 0 else "BUY"
                qty = abs(pos_amt)
                client.create_order(symbol, side, "MARKET", quantity=str(qty))
                logger.info(f"Closed position: qty={qty} {side}")
            client.cancel_all_open_orders(symbol)
            logger.info(f"All open orders cancelled for {symbol}.")
        except Exception as e:
            logger.error(f"Failed to handle stop: {str(e)}")

# -------- TIME SYNC CHECK ----------
def check_time_offset(base_url: str) -> float:
    """Check time offset with Binance server, with retries."""
    max_attempts = 3
    for attempt in range(max_attempts):
        try:
            response = requests.get(f"{base_url}/fapi/v1/time", timeout=15, verify=certifi.where())
            server_time_ms = response.json()['serverTime']
            server_time = datetime.fromtimestamp(server_time_ms / 1000, tz=timezone.utc)
            local_time = datetime.now(timezone.utc)
            offset = (server_time - local_time).total_seconds()
            logger.info(f"Time offset from Binance: {offset:.2f} seconds (attempt {attempt+1}/{max_attempts})")
            return offset
        except Exception as e:
            logger.warning(f"Binance time sync failed (attempt {attempt+1}/{max_attempts}): {str(e)}")
            if attempt < max_attempts - 1:
                sleep_time = 2 ** attempt
                time.sleep(sleep_time)
    logger.error("All time sync attempts failed. Using local time.")
    return 0.0

# -------- BINANCE CLIENT ----------
class BinanceAPIError(Exception):
    """Custom exception for Binance API errors."""
    def __init__(self, message: str, status_code: Optional[int] = None, payload: Optional[any] = None):
        super().__init__(message)
        self.status_code = status_code
        self.payload = payload

class BinanceClient:
    """Binance Futures API client with signing, retries, and public/private separation."""
    def __init__(self, api_key: str, api_secret: str, use_live: bool = False, base_override: Optional[str] = None):
        self.api_key = api_key
        self.api_secret = api_secret
        self.use_live = use_live
        self.base = base_override or ("https://fapi.binance.com" if use_live else "https://testnet.binancefuture.com")
        logger.info(f"Using base URL: {self.base}")
        self.time_offset = check_time_offset(self.base)
        self.symbol_filters_cache: Dict[str, any] = {}
        self.klines_cache: Dict[str, any] = {}
        self.klines_cache_time: Dict[str, float] = {}

    def _get_server_time(self) -> int:
        """Fetch server time with fallback to local."""
        try:
            response = requests.get(f"{self.base}/fapi/v1/time", timeout=15, verify=certifi.where())
            return response.json()['serverTime']
        except Exception:
            logger.warning("Failed to fetch server time. Using local time.")
            return int((datetime.now(timezone.utc) + timedelta(seconds=self.time_offset)).timestamp() * 1000)

    def _sign(self, query_string: str) -> str:
        """Generate HMAC SHA256 signature."""
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_public_request(self, method: str, endpoint: str, params: Optional[Dict[str, any]] = None) -> any:
        """Send public API request without signing."""
        params = params or {}
        url = f"{self.base}{endpoint}"
        if params:
            url += "?" + urlencode(params)
        for attempt in range(5):
            try:
                r = requests.request(method, url, timeout=30, verify=certifi.where())
                r.raise_for_status()
                return r.json()
            except requests.exceptions.HTTPError as e:
                logger.warning(f"Public request failed (attempt {attempt+1}/5): HTTP {r.status_code} - {r.text}")
            except Exception as e:
                logger.warning(f"Public request failed (attempt {attempt+1}/5): {str(e)}")
            if attempt < 4:
                time.sleep(2 ** attempt)
        raise BinanceAPIError("Max retries exceeded for public request.")

    def send_signed_request(self, method: str, endpoint: str, params: Optional[Dict[str, any]] = None) -> any:
        """Send signed API request with retries."""
        params = params.copy() if params else {}
        params["timestamp"] = self._get_server_time()
        params["recvWindow"] = 10000
        query = urlencode(sorted(params.items()))
        signature = self._sign(query)
        url = f"{self.base}{endpoint}?{query}&signature={signature}"
        headers = {"X-MBX-APIKEY": self.api_key}
        for attempt in range(5):
            try:
                r = requests.request(method, url, headers=headers, timeout=30, verify=certifi.where())
                if r.status_code == 200:
                    response = r.json()
                    if isinstance(response, dict) and response.get("code") not in (None, 200):
                        raise BinanceAPIError(f"API error: {response.get('msg', 'Unknown')} (code {response.get('code')})", r.status_code, response)
                    return response
                else:
                    try:
                        payload = r.json()
                    except ValueError:
                        payload = r.text
                    raise BinanceAPIError(f"HTTP {r.status_code}: {payload}", r.status_code, payload)
            except BinanceAPIError as e:
                logger.warning(f"Signed request failed (attempt {attempt+1}/5): {str(e)}")
                if attempt < 4:
                    time.sleep(2 ** attempt)
                else:
                    raise
            except Exception as e:
                logger.warning(f"Signed request failed (attempt {attempt+1}/5): {str(e)}")
                if attempt < 4:
                    time.sleep(2 ** attempt)
                else:
                    raise

    def get_klines(self, symbol: str, interval: str, limit: int = KLINES_LIMIT) -> List[List[any]]:
        """Fetch klines (public)."""
        cache_key = f"{symbol}_{interval}_{limit}"
        current_time = time.time()
        if cache_key in self.klines_cache and current_time - self.klines_cache_time.get(cache_key, 0) < KLINES_CACHE_DURATION:
            return self.klines_cache[cache_key]
        params = {"symbol": symbol, "interval": interval, "limit": limit}
        klines = self.send_public_request("GET", "/fapi/v1/klines", params)
        self.klines_cache[cache_key] = klines
        self.klines_cache_time[cache_key] = current_time
        return klines

    def get_symbol_ticker(self, symbol: str) -> Dict[str, any]:
        """Fetch ticker price (public)."""
        params = {"symbol": symbol}
        return self.send_public_request("GET", "/fapi/v1/ticker/price", params)

    def get_exchange_info(self) -> Dict[str, any]:
        """Fetch exchange info (public)."""
        return self.send_public_request("GET", "/fapi/v1/exchangeInfo")

    def get_position_risk(self, symbol: str) -> List[Dict[str, any]]:
        """Fetch position risk (signed)."""
        params = {"symbol": symbol}
        return self.send_signed_request("GET", "/fapi/v2/positionRisk", params)

    def cancel_all_open_orders(self, symbol: str) -> any:
        """Cancel all open orders (signed)."""
        params = {"symbol": symbol}
        return self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", params)

    def get_open_orders(self, symbol: str) -> List[Dict[str, any]]:
        """Fetch open orders (signed)."""
        params = {"symbol": symbol}
        return self.send_signed_request("GET", "/fapi/v1/openOrders", params)

    def create_order(self, symbol: str, side: str, order_type: str, **kwargs: any) -> Dict[str, any]:
        """Create order (signed)."""
        params = {"symbol": symbol, "side": side, "type": order_type}
        params.update(kwargs)
        return self.send_signed_request("POST", "/fapi/v1/order", params)

    def get_account(self) -> Dict[str, any]:
        """Fetch account info (signed)."""
        return self.send_signed_request("GET", "/fapi/v2/account")

    def get_user_trades(self, symbol: str, startTime: Optional[int] = None, limit: int = 20) -> List[Dict[str, any]]:
        """Fetch recent user trades (signed)."""
        params = {"symbol": symbol, "limit": limit}
        if startTime:
            params["startTime"] = startTime
        return self.send_signed_request("GET", "/fapi/v1/userTrades", params)

    def set_leverage(self, symbol: str, leverage: int) -> Dict[str, any]:
        """Set leverage for symbol (signed)."""
        params = {"symbol": symbol, "leverage": leverage}
        return self.send_signed_request("POST", "/fapi/v1/leverage", params)

# -------- TRADE MANAGEMENT ----------
class TradeState:
    """Manages state of an active trade."""
    def __init__(self):
        self.active: bool = False
        self.trade_id: int = 0
        self.entry_price: Decimal = Decimal('0')
        self.qty: Decimal = Decimal('0')
        self.side: str = ""
        self.entry_close_time: int = 0
        self.exit_close_time: int = 0
        self.sl: Decimal = Decimal('0')
        self.tp: Decimal = Decimal('0')
        self.r: Decimal = Decimal('0')  # Risk amount (R)
        self.trail_activated: bool = False
        self.trail_order_id: Optional[int] = None
        self.sl_order_id: Optional[int] = None
        self.tp_order_id: Optional[int] = None
        self.trail_activation_price: Decimal = Decimal('0')

def fetch_balance(client: BinanceClient) -> Decimal:
    """Fetch available balance with retries."""
    max_attempts = 3
    for attempt in range(max_attempts):
        try:
            account = client.get_account()
            return Decimal(str(account.get('availableBalance', '0')))
        except Exception as e:
            logger.warning(f"Balance fetch failed (attempt {attempt+1}/{max_attempts}): {str(e)}")
            if attempt < max_attempts - 1:
                time.sleep(2 ** attempt)
    raise BinanceAPIError("Failed to fetch balance after max retries.")

def fetch_open_position_details(client: BinanceClient, symbol: str) -> Dict[str, any]:
    """Fetch position details."""
    return client.get_position_risk(symbol)[0]

def has_active_position(client: BinanceClient, symbol: str) -> bool:
    """Check if there's an active position."""
    pos = fetch_open_position_details(client, symbol)
    return abs(Decimal(str(pos.get("positionAmt", "0")))) > Decimal('0')

def place_market_order(client: BinanceClient, symbol: str, side: str, qty: Decimal) -> Dict[str, any]:
    """Place market order."""
    return client.create_order(symbol, side, 'MARKET', quantity=str(qty))

def place_sl_order(client: BinanceClient, symbol: str, price: Decimal, side: str) -> Dict[str, any]:
    """Place stop-loss order (close position)."""
    return client.create_order(symbol, side, 'STOP_MARKET', closePosition=True, stopPrice=str(price))

def place_tp_order(client: BinanceClient, symbol: str, price: Decimal, side: str) -> Dict[str, any]:
    """Place take-profit order (close position)."""
    return client.create_order(symbol, side, 'TAKE_PROFIT_MARKET', closePosition=True, stopPrice=str(price))

def place_trailing_stop(client: BinanceClient, symbol: str, side: str, activation_price: Decimal, callback_rate: Decimal) -> Dict[str, any]:
    """Place trailing stop order."""
    return client.create_order(
        symbol, side, 'TRAILING_STOP_MARKET',
        activationPrice=str(activation_price),
        callbackRate=str(callback_rate),
        closePosition=True
    )

def get_symbol_filters(client: BinanceClient, symbol: str) -> Dict[str, Decimal]:
    """Fetch and cache symbol filters."""
    if symbol not in client.symbol_filters_cache:
        exchange_info = client.get_exchange_info()
        for s in exchange_info["symbols"]:
            if s["symbol"] == symbol:
                filters = {f["filterType"]: f for f in s["filters"]}
                client.symbol_filters_cache[symbol] = {
                    "tickSize": Decimal(str(filters["PRICE_FILTER"]["tickSize"])),
                    "stepSize": Decimal(str(filters["LOT_SIZE"]["stepSize"])),
                    "minNotional": Decimal(str(filters["NOTIONAL"]["minNotional"]))
                }
                break
        else:
            raise ValueError(f"Symbol {symbol} not found in exchange info.")
    return client.symbol_filters_cache[symbol]

# -------- INDICATOR CALCULATIONS ----------
def calculate_ema(series: List[float], period: int) -> List[float]:
    """Calculate Exponential Moving Average (EMA) list."""
    emas = []
    if len(series) < period:
        return emas
    sma = statistics.mean(series[:period])
    emas = [sma] * (period - 1) + [sma]  # Pad for index alignment, but actually start from period
    alpha = 2 / (period + 1)
    for price in series[period:]:
        sma = alpha * price + (1 - alpha) * sma
        emas.append(sma)
    return emas

def calculate_macd(closes: List[float]) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    """Calculate MACD line, signal, and histogram."""
    if len(closes) < MACD_SLOW + MACD_SIGNAL - 1:
        return None, None, None
    ema_fast_full = calculate_ema(closes, MACD_FAST)
    ema_slow_full = calculate_ema(closes, MACD_SLOW)
    offset = len(ema_fast_full) - len(ema_slow_full)
    macd_lines = []
    for i in range(len(ema_slow_full)):
        fast_idx = i + offset
        if fast_idx < len(ema_fast_full):
            macd_lines.append(ema_fast_full[fast_idx] - ema_slow_full[i])
    if len(macd_lines) < MACD_SIGNAL:
        return macd_lines[-1] if macd_lines else None, None, None
    signal_full = calculate_ema(macd_lines, MACD_SIGNAL)
    macd_line = macd_lines[-1]
    signal = signal_full[-1]
    histogram = macd_line - signal
    return macd_line, signal, histogram

def calculate_rsi(closes: List[float], period: int = RSI_PERIOD) -> Optional[float]:
    """Calculate Wilder's RSI."""
    if len(closes) < period + 1:
        return None
    changes = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    initial_gains = [max(0, ch) for ch in changes[:period]]
    initial_losses = [abs(min(0, ch)) for ch in changes[:period]]
    avg_gain = sum(initial_gains) / period
    avg_loss = sum(initial_losses) / period
    for ch in changes[period:]:
        current_gain = max(0, ch)
        current_loss = abs(min(0, ch))
        avg_gain = (avg_gain * (period - 1) + current_gain) / period
        avg_loss = (avg_loss * (period - 1) + current_loss) / period
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))

# -------- MONITORING ----------
def monitor_trade(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, bot: Bot, chat_id: str) -> None:
    """Monitor active trade for closure and updates."""
    logger.info(f"Monitoring trade {trade_state.trade_id} ({trade_state.side})...")
    last_position_check = 0.0
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    while trade_state.active and not STOP_REQUESTED and not os.path.exists("stop.txt"):
        current_time = time.time()
        if current_time - last_position_check >= POSITION_CHECK_INTERVAL:
            try:
                pos = fetch_open_position_details(client, symbol)
                pos_amt = Decimal(str(pos.get("positionAmt", "0")))
                unrealized_pnl = Decimal(str(pos.get("unRealizedProfit", "0")))
                logger.info(f"Unrealized PnL: {unrealized_pnl:.2f} USDT")
                if abs(pos_amt) == Decimal('0'):
                    # Position closed
                    open_orders = client.get_open_orders(symbol)
                    trail_order = next((o for o in open_orders if o.get("orderId") == trade_state.trail_order_id), None) if trade_state.trail_order_id else None
                    sl_order = next((o for o in open_orders if o.get("orderId") == trade_state.sl_order_id), None) if trade_state.sl_order_id else None
                    tp_order = next((o for o in open_orders if o.get("orderId") == trade_state.tp_order_id), None) if trade_state.tp_order_id else None
                    # Get exact exit price from trades
                    recent_trades = client.get_user_trades(symbol, trade_state.entry_close_time)
                    close_trades = [t for t in recent_trades if t['side'] == close_side and Decimal(str(t['qty'])) == trade_state.qty]
                    exit_price = Decimal(str(close_trades[-1]['price'])) if close_trades else Decimal(str(client.get_symbol_ticker(symbol).get("price", "0")))
                    if trade_state.trail_activated and not trail_order:
                        reason = "Trailing Stop"
                    elif not sl_order and trade_state.sl_order_id:
                        reason = "Stop-Loss"
                    elif not tp_order and trade_state.tp_order_id:
                        reason = "Take-Profit"
                    else:
                        reason = "Unknown"
                    logger.info(f"Position closed ({reason}): {trade_state.side}, qty={trade_state.qty}, exit={exit_price:.4f}")
                    log_pnl(trade_state.trade_id, trade_state.side, trade_state.entry_price, exit_price, trade_state.qty, trade_state.r)
                    send_exit_telegram(symbol, trade_state.trade_id, trade_state.side, float(exit_price), float(trade_state.qty), reason, bot, chat_id)
                    client.cancel_all_open_orders(symbol)
                    trade_state.active = False
                    trade_state.exit_close_time = int(current_time * 1000)
                else:
                    # Check trailing activation
                    current_price = Decimal(str(client.get_symbol_ticker(symbol).get("price")))
                    if not trade_state.trail_activated and trade_state.trail_activation_price:
                        if (trade_state.side == "LONG" and current_price >= trade_state.trail_activation_price) or \
                           (trade_state.side == "SHORT" and current_price <= trade_state.trail_activation_price):
                            logger.info(f"Trailing stop activated at {current_price:.4f} (activation: {trade_state.trail_activation_price:.4f})")
                            trade_state.trail_activated = True
                last_position_check = current_time
            except Exception as e:
                logger.error(f"Monitor error: {str(e)}")
                time.sleep(2)

# -------- TRADING LOGIC ----------
def interval_ms(interval: str) -> int:
    """Convert interval string to milliseconds."""
    if interval.endswith("m"):
        return int(interval[:-1]) * 60 * 1000
    if interval.endswith("h"):
        return int(interval[:-1]) * 3600 * 1000
    raise ValueError(f"Invalid interval: {interval}")

def extract_klines_data(klines: List[List[any]]) -> Tuple[List[Decimal], List[Decimal], List[int], List[Decimal]]:
    """Extract closes, volumes, close times, opens from klines."""
    closes = [Decimal(str(k[4])) for k in klines]
    volumes = [Decimal(str(k[5])) for k in klines]
    close_times = [int(k[6]) for k in klines]
    opens = [Decimal(str(k[1])) for k in klines]
    if closes:
        logger.debug(f"Latest kline: close={closes[-1]}, volume={volumes[-1]}, time={datetime.fromtimestamp(close_times[-1]/1000, tz=timezone.utc)}")
    return closes, volumes, close_times, opens

def trading_loop(
    client: BinanceClient,
    symbol: str,
    timeframe: str,
    max_trades_per_day: int,
    risk_pct: Decimal,
    max_daily_loss_pct: Decimal,
    tp_mult: Decimal,
    use_trailing: bool,
    prevent_same_bar: bool,
    require_no_pos: bool,
    use_max_loss: bool,
    use_volume_filter: bool,
    use_macd: bool,
    bot: Bot,
    chat_id: str
) -> None:
    """Main trading loop: fetch data, check signals, manage trades."""
    global TRADE_ID_COUNTER
    last_processed_time: int = 0
    trades_today: int = 0
    last_day: date = datetime.now(timezone.utc).date()
    starting_bal: Decimal = fetch_balance(client)
    trade_state = TradeState()
    pending_entry: bool = False
    interval_millis = interval_ms(timeframe)
    while not STOP_REQUESTED and not os.path.exists("stop.txt"):
        try:
            current_day = datetime.now(timezone.utc).date()
            if current_day != last_day:
                trades_today = 0
                starting_bal = fetch_balance(client)
                last_day = current_day
                logger.info(f"New day {current_day}: Reset trades_today, starting_bal={starting_bal}")

            server_time = client._get_server_time()
            next_close_ms = last_processed_time + interval_millis
            sleep_seconds = max(1.0, (next_close_ms - server_time + 500) / 1000.0)
            if sleep_seconds > 1:
                logger.info(f"Waiting for next candle close in {sleep_seconds:.2f}s...")
                time.sleep(sleep_seconds)
                continue

            klines = client.get_klines(symbol, timeframe, limit=KLINES_LIMIT)
            raw_closes = [float(k[4]) for k in klines]
            closes, volumes, close_times, opens = extract_klines_data(klines)
            last_close_time = close_times[-1]

            if last_processed_time == last_close_time:
                logger.debug(f"Duplicate candle at {last_close_time}; skipping.")
                time.sleep(1)
                continue

            # Calculate indicators
            rsi = calculate_rsi(raw_closes)
            macd_line, macd_signal, _ = calculate_macd(raw_closes)
            bullish_crossover = macd_line > macd_signal if macd_line is not None and macd_signal is not None else False
            bearish_crossover = macd_line < macd_signal if macd_line is not None and macd_signal is not None else False
            vol_sma = statistics.mean([float(v) for v in volumes[-VOL_SMA_PERIOD:]]) if len(volumes) >= VOL_SMA_PERIOD else None
            curr_vol = float(volumes[-1])
            close_price = closes[-1]
            open_price = opens[-1]
            is_green = close_price > open_price
            is_red = close_price < open_price

            logger.info(
                f"Candle: open={open_price:.4f}, close={close_price:.4f}, RSI={'N/A' if rsi is None else f'{rsi:.2f}'}, "
                f"MACD={'N/A' if macd_line is None else f'{macd_line:.4f}'}, Signal={'N/A' if macd_signal is None else f'{macd_signal:.4f}'}, Vol={curr_vol:.2f}, SMA15={'N/A' if vol_sma is None else f'{vol_sma:.2f}'}, "
                f"{'Green' if is_green else 'Red' if is_red else 'Neutral'}"
            )

            if prevent_same_bar and trade_state.exit_close_time == last_close_time:
                logger.info("Same bar as exit; skipping entry.")
                last_processed_time = last_close_time
                continue

            if require_no_pos and has_active_position(client, symbol):
                logger.info("Active position exists; waiting for closure.")
                last_processed_time = last_close_time
                continue

            if use_volume_filter and (vol_sma is None or curr_vol <= vol_sma):
                logger.info("Insufficient volume or history; skipping.")
                last_processed_time = last_close_time
                continue

            buy_signal = rsi is not None and BUY_RSI_MIN <= rsi <= BUY_RSI_MAX and is_green and (not use_macd or bullish_crossover)
            sell_signal = rsi is not None and SELL_RSI_MIN <= rsi <= SELL_RSI_MAX and is_red and (not use_macd or bearish_crossover)

            if (buy_signal or sell_signal) and not trade_state.active and not pending_entry and trades_today < max_trades_per_day:
                if use_max_loss:
                    daily_pnl = get_pnl_total_usd('daily')
                    if daily_pnl < - (max_daily_loss_pct * starting_bal):
                        logger.info(f"Max daily loss exceeded ({daily_pnl:.2f} < -{max_daily_loss_pct * starting_bal:.2f}). No more trades today.")
                        last_processed_time = last_close_time
                        continue

                TRADE_ID_COUNTER += 1
                trade_state.trade_id = TRADE_ID_COUNTER
                side = "BUY" if buy_signal else "SELL"
                logger.info(f"{side} signal detected. Preparing entry (Trade ID: {trade_state.trade_id}).")
                pending_entry = True

                entry_price = close_price
                if buy_signal:
                    sl_price = entry_price * (Decimal(1) - SL_PCT)
                    r = entry_price * SL_PCT
                    tp_price = entry_price + (tp_mult * r)
                    trail_activation = entry_price + (TRAIL_TRIGGER_MULT * r)
                    close_side = "SELL"
                    sl_round = ROUND_DOWN
                    tp_round = ROUND_UP
                else:
                    sl_price = entry_price * (Decimal(1) + SL_PCT)
                    r = entry_price * SL_PCT
                    tp_price = entry_price - (tp_mult * r)
                    trail_activation = entry_price - (TRAIL_TRIGGER_MULT * r)
                    close_side = "BUY"
                    sl_round = ROUND_UP
                    tp_round = ROUND_DOWN

                if r <= 0:
                    logger.warning(f"Invalid R ({r}); skipping trade.")
                    pending_entry = False
                    continue

                bal = fetch_balance(client)
                risk_amount = bal * risk_pct
                qty = risk_amount / r
                filters = get_symbol_filters(client, symbol)
                qty = qty.quantize(filters["stepSize"], ROUND_DOWN)
                if qty * entry_price < filters["minNotional"]:
                    qty = (filters["minNotional"] / entry_price).quantize(filters["stepSize"], ROUND_DOWN)

                sl_price = sl_price.quantize(filters["tickSize"], sl_round)
                tp_price = tp_price.quantize(filters["tickSize"], tp_round)
                trail_activation = trail_activation.quantize(filters["tickSize"])
                callback_rate = ((Decimal(2) * r) / trail_activation * Decimal(100)).quantize(Decimal('0.01'))
                callback_rate = max(CALLBACK_RATE_MIN, min(CALLBACK_RATE_MAX, callback_rate))

                # Place market entry
                try:
                    place_market_order(client, symbol, side, qty)
                except Exception as e:
                    logger.error(f"Market order failed: {str(e)}")
                    pending_entry = False
                    continue

                # Wait for fill
                start_time = time.time()
                actual_qty = Decimal('0')
                while time.time() - start_time < ORDER_FILL_TIMEOUT:
                    if STOP_REQUESTED or os.path.exists("stop.txt"):
                        break
                    pos = fetch_open_position_details(client, symbol)
                    pos_amt = Decimal(str(pos.get("positionAmt", "0")))
                    if abs(pos_amt) > Decimal('0'):
                        actual_qty = abs(pos_amt)
                        break
                    time.sleep(0.5)

                if actual_qty == Decimal('0'):
                    logger.warning("Entry fill timeout; cancelling orders.")
                    client.cancel_all_open_orders(symbol)
                    pending_entry = False
                    continue

                actual_entry = Decimal(str(pos.get("entryPrice", "0")))  # Use actual entry from position
                trade_state.active = True
                trade_state.entry_price = actual_entry
                trade_state.qty = actual_qty
                trade_state.side = "LONG" if buy_signal else "SHORT"
                trade_state.entry_close_time = last_close_time
                trade_state.sl = sl_price
                trade_state.tp = tp_price
                trade_state.r = r
                trade_state.trail_activation_price = trail_activation
                logger.info(
                    f"Position opened (ID: {trade_state.trade_id}): {trade_state.side}, qty={actual_qty}, "
                    f"entry={actual_entry:.4f}, sl={sl_price:.4f}, tp={tp_price:.4f}, activation={trail_activation:.4f}"
                )

                send_entry_telegram({
                    'symbol': symbol,
                    'trade_id': trade_state.trade_id,
                    'side': trade_state.side,
                    'entry': float(actual_entry),
                    'sl': float(sl_price),
                    'tp': float(tp_price),
                    'trail_activation': float(trail_activation),
                    'qty': float(actual_qty)
                }, bot, chat_id)

                # Place SL/TP/Trailing
                client.cancel_all_open_orders(symbol)  # Clean slate
                try:
                    sl_res = place_sl_order(client, symbol, sl_price, close_side)
                    trade_state.sl_order_id = sl_res.get("orderId")
                    tp_res = place_tp_order(client, symbol, tp_price, close_side)
                    trade_state.tp_order_id = tp_res.get("orderId")
                    if use_trailing:
                        trail_res = place_trailing_stop(client, symbol, close_side, trail_activation, callback_rate)
                        trade_state.trail_order_id = trail_res.get("orderId")
                except BinanceAPIError as e:
                    if e.payload and e.payload.get('code') == -1111:
                        logger.warning("Precision error; refetching filters and retrying.")
                        del client.symbol_filters_cache[symbol]
                        filters = get_symbol_filters(client, symbol)
                        sl_price = sl_price.quantize(filters["tickSize"], sl_round)
                        tp_price = tp_price.quantize(filters["tickSize"], tp_round)
                        trail_activation = trail_activation.quantize(filters["tickSize"])
                        # Retry placement
                        sl_res = place_sl_order(client, symbol, sl_price, close_side)
                        trade_state.sl_order_id = sl_res.get("orderId")
                        tp_res = place_tp_order(client, symbol, tp_price, close_side)
                        trade_state.tp_order_id = tp_res.get("orderId")
                        if use_trailing:
                            trail_res = place_trailing_stop(client, symbol, close_side, trail_activation, callback_rate)
                            trade_state.trail_order_id = trail_res.get("orderId")
                    else:
                        logger.error(f"Failed to place bracket orders: {str(e)}")

                trades_today += 1
                pending_entry = False
                monitor_trade(client, symbol, trade_state, filters["tickSize"], bot, chat_id)

            last_processed_time = last_close_time

        except Exception as e:
            logger.error(f"Trading loop error: {str(e)}")
            time.sleep(2)

# -------- SCHEDULER FOR REPORTS ----------
def run_scheduler(bot: Bot, chat_id: str) -> None:
    """Run scheduler for periodic reports."""
    last_month: Optional[int] = None
    def check_monthly() -> None:
        nonlocal last_month
        now = datetime.now(timezone.utc)
        if now.day == 1 and (last_month is None or now.month != last_month):
            send_monthly_report(bot, chat_id)
            last_month = now.month

    schedule.every().day.at("23:59").do(send_daily_report, bot, chat_id)
    schedule.every().sunday.at("23:59").do(send_weekly_report, bot, chat_id)
    schedule.every().day.at("00:00").do(check_monthly)
    while not STOP_REQUESTED:
        schedule.run_pending()
        time.sleep(60)

# -------- ENTRY POINT ----------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Professional Binance Futures Trading Bot")
    parser.add_argument("--api-key", help="Binance API Key")
    parser.add_argument("--api-secret", help="Binance API Secret")
    parser.add_argument("--telegram-token", help="Telegram Bot Token")
    parser.add_argument("--chat-id", help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol (default: SOLUSDT)")
    parser.add_argument("--timeframe", default="30m", help="Timeframe (default: 30m)")
    parser.add_argument("--max-trades", type=int, default=3, help="Max trades per day (default: 3)")
    parser.add_argument("--risk-pct", type=float, default=0.5, help="Risk % per trade (default: 0.5)")
    parser.add_argument("--max-loss-pct", type=float, default=5.0, help="Max daily loss percentage (default: 5%)")
    parser.add_argument("--tp-mult", type=float, default=3.5, help="TP multiplier (default: 3.5)")
    parser.add_argument("--leverage", type=int, default=1, help="Leverage (default: 1)")
    parser.add_argument("--no-trailing", action="store_false", dest="use_trailing", help="Disable trailing stop")
    parser.add_argument("--allow-same-bar", action="store_false", dest="prevent_same_bar", help="Allow same-bar re-entry")
    parser.add_argument("--allow-pos", action="store_false", dest="require_no_pos", help="Allow trading with open pos")
    parser.add_argument("--no-max-loss", action="store_false", dest="use_max_loss", help="Disable max daily loss check")
    parser.add_argument("--no-volume", action="store_false", dest="use_volume_filter", help="Disable volume filter")
    parser.add_argument("--no-macd", action="store_false", dest="use_macd", help="Disable MACD")
    parser.add_argument("--live", action="store_true", help="Use live trading (default: testnet)")
    args = parser.parse_args()

    # Fallback to env vars for sensitive args
    args.api_key = args.api_key or os.getenv('API_KEY')
    args.api_secret = args.api_secret or os.getenv('API_SECRET')
    args.telegram_token = args.telegram_token or os.getenv('TELEGRAM_TOKEN')
    args.chat_id = args.chat_id or os.getenv('CHAT_ID')

    # Validate required sensitive args
    if not args.api_key or not args.api_secret or not args.telegram_token or not args.chat_id:
        raise ValueError("Missing required arguments: api_key, api_secret, telegram_token, chat_id (provide via args or env vars)")

    init_pnl_log()
    telegram_bot = Bot(token=args.telegram_token)
    binance_client = BinanceClient(args.api_key, args.api_secret, args.live)
    try:
        binance_client.set_leverage(args.symbol, args.leverage)
        logger.info(f"Leverage set to {args.leverage}x for {args.symbol}")
    except Exception as e:
        logger.warning(f"Failed to set leverage: {str(e)}")
    signal.signal(signal.SIGINT, lambda s, f: request_stop(s, f, binance_client, args.symbol))
    signal.signal(signal.SIGTERM, lambda s, f: request_stop(s, f, binance_client, args.symbol))
    threading.Thread(target=run_scheduler, args=(telegram_bot, args.chat_id), daemon=True).start()
    trading_loop(
        client=binance_client,
        symbol=args.symbol,
        timeframe=args.timeframe,
        max_trades_per_day=args.max_trades,
        risk_pct=Decimal(str(args.risk_pct / 100)),
        max_daily_loss_pct=Decimal(str(args.max_loss_pct / 100)),
        tp_mult=Decimal(str(args.tp_mult)),
        use_trailing=args.use_trailing,
        prevent_same_bar=args.prevent_same_bar,
        require_no_pos=args.require_no_pos,
        use_max_loss=args.use_max_loss,
        use_volume_filter=args.use_volume_filter,
        use_macd=args.use_macd,
        bot=telegram_bot,
        chat_id=args.chat_id
    )