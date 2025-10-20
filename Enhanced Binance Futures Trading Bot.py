import argparse
import time
import logging
import os
import json
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
from urllib.parse import urljoin
import schedule
from telegram import Bot
import asyncio
import math
from decimal import Decimal
import hmac
import hashlib
from urllib.parse import urlencode

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("bot.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class BinanceClient:
    BASE_URL_TESTNET = "https://testnet.binancefuture.com"
    BASE_URL_LIVE = "https://fapi.binance.com"

    def __init__(self, api_key: str, api_secret: str, use_testnet: bool = True):
        self.api_key = api_key
        self.api_secret = api_secret
        self.base_url = self.BASE_URL_TESTNET if use_testnet else self.BASE_URL_LIVE
        logger.info(f"Using base URL: {self.base_url}")
        self.time_offset = self._get_time_offset()

    def _get_time_offset(self, retries: int = 3) -> float:
        for attempt in range(1, retries + 1):
            try:
                response = requests.get(urljoin(self.base_url, "/fapi/v1/time"))
                response.raise_for_status()
                server_time = response.json()["serverTime"] / 1000
                local_time = time.time()
                offset = local_time - server_time
                logger.info(f"Time offset from Binance: {offset:.2f} seconds (attempt {attempt}/{retries})")
                return offset
            except Exception as e:
                logger.error(f"Time sync failed (attempt {attempt}/{retries}): {e}")
                if attempt == retries:
                    logger.warning("Using zero time offset after retries")
                    return 0.0
                time.sleep(1)
        return 0.0

    def _generate_signature(self, params: Dict) -> str:
        query_string = urlencode(params)
        return hmac.new(
            self.api_secret.encode('utf-8'),
            query_string.encode('utf-8'),
            hashlib.sha256
        ).hexdigest()

    def _request(self, method: str, endpoint: str, params: Dict = None, signed: bool = False) -> Dict:
        if params is None:
            params = {}
        headers = {"X-MBX-APIKEY": self.api_key}
        url = urljoin(self.base_url, endpoint)
        if signed:
            params['timestamp'] = int((time.time() - self.time_offset) * 1000)
            params['signature'] = self._generate_signature(params)
        try:
            response = requests.request(method, url, headers=headers, params=params)
            response.raise_for_status()
            return response.json()
        except Exception as e:
            logger.error(f"Request to {endpoint} failed: {e}")
            raise Exception(f"Binance API error: {e}")

    def get_klines(self, symbol: str, interval: str, limit: int = 100) -> List[Dict]:
        endpoint = "/fapi/v1/klines"
        params = {"symbol": symbol, "interval": interval, "limit": limit}
        return self._request("GET", endpoint, params)

    def get_balance(self) -> float:
        endpoint = "/fapi/v2/balance"
        balances = self._request("GET", endpoint, signed=True)
        for balance in balances:
            if balance["asset"] == "USDT":
                return float(balance["balance"])
        return 0.0

    def set_leverage(self, symbol: str, leverage: int) -> None:
        endpoint = "/fapi/v1/leverage"
        params = {"symbol": symbol, "leverage": leverage, "timestamp": int((time.time() - self.time_offset) * 1000)}
        params['signature'] = self._generate_signature(params)
        self._request("POST", endpoint, params, signed=True)
        logger.info(f"Leverage set to {leverage}x for {symbol}")

    def create_order(self, symbol: str, side: str, quantity: float, price: Optional[float] = None, order_type: str = "MARKET") -> Dict:
        endpoint = "/fapi/v1/order"
        params = {
            "symbol": symbol,
            "side": side,
            "type": order_type,
            "quantity": f"{quantity:.2f}",
            "timestamp": int((time.time() - self.time_offset) * 1000)
        }
        if price:
            params["price"] = f"{price:.2f}"
        params['signature'] = self._generate_signature(params)
        return self._request("POST", endpoint, params, signed=True)

class TradingBot:
    def __init__(self, config: Dict):
        self.client = BinanceClient(config["api_key"], config["api_secret"], not config["live"])
        self.symbol = config["symbol"]
        self.timeframe = config["timeframe"]
        self.max_trades = config["max_trades"]
        self.risk_pct = config["risk_pct"]
        self.max_loss_pct = config["max_loss_pct"]
        self.tp_mult = config["tp_mult"]
        self.use_trailing = config["use_trailing"]
        self.use_volume_filter = config["use_volume_filter"]
        self.telegram_bot = Bot(token=config["telegram_token"])
        self.chat_id = config["chat_id"]
        self.position = None
        self.trades = 0
        self.initial_balance = self.client.get_balance()
        logger.info(f"Initial balance: {self.initial_balance:.2f} USDT")

    async def send_telegram_message(self, message: str) -> None:
        try:
            await self.telegram_bot.send_message(chat_id=self.chat_id, text=message)
        except Exception as e:
            logger.error(f"Telegram send failed: {e}")

    def calculate_rsi(self, closes: List[float], period: int = 14) -> Optional[float]:
        if len(closes) < period + 1:
            return None
        gains = []
        losses = []
        for i in range(1, len(closes)):
            diff = closes[i] - closes[i - 1]
            if diff > 0:
                gains.append(diff)
                losses.append(0)
            else:
                gains.append(0)
                losses.append(-diff)
        avg_gain = sum(gains[-period:]) / period
        avg_loss = sum(losses[-period:]) / period
        if avg_loss == 0:
            return 100.0
        rs = avg_gain / avg_loss
        return 100 - (100 / (1 + rs))

    def calculate_macd(self, closes: List[float]) -> Tuple[Optional[float], Optional[float]]:
        if len(closes) < 26:
            return None, None
        short_ema = self.calculate_ema(closes, 12)
        long_ema = self.calculate_ema(closes, 26)
        if short_ema is None or long_ema is None:
            return None, None
        macd_line = short_ema - long_ema
        signal_line = self.calculate_ema([short_ema - long_ema for _ in range(len(closes))], 9)
        return macd_line, signal_line

    def calculate_ema(self, prices: List[float], period: int) -> Optional[float]:
        if len(prices) < period:
            return None
        multiplier = 2 / (period + 1)
        ema = sum(prices[:period]) / period
        for price in prices[period:]:
            ema = (price - ema) * multiplier + ema
        return ema

    def calculate_volume_sma(self, volumes: List[float], period: int = 15) -> Optional[float]:
        if len(volumes) < period:
            return None
        return sum(volumes[-period:]) / period

    def trading_loop(self):
        try:
            klines = self.client.get_klines(self.symbol, self.timeframe, limit=100)
            closes = [float(kline[4]) for kline in klines]
            volumes = [float(kline[5]) for kline in klines]
            rsi = self.calculate_rsi(closes)
            macd_line, macd_signal = self.calculate_macd(closes)
            curr_vol = volumes[-1]
            vol_sma = self.calculate_volume_sma(volumes)
            open_price = float(klines[-1][1])
            close_price = float(klines[-1][4])
            is_green = close_price > open_price
            is_red = close_price < open_price

            # Log candle data with proper handling of None values
            logger.info(
                f"Candle: open={open_price:.4f}, close={close_price:.4f}, "
                f"RSI={'N/A' if rsi is None else f'{rsi:.2f}'}, "
                f"MACD={'N/A' if macd_line is None else f'{macd_line:.4f}'}, "
                f"Signal={'N/A' if macd_signal is None else f'{macd_signal:.4f}'}, "
                f"Vol={curr_vol:.2f}, SMA15={'N/A' if vol_sma is None else f'{vol_sma:.2f}'}, "
                f"{'Green' if is_green else 'Red' if is_red else 'Neutral'}"
            )

            if self.trades >= self.max_trades:
                logger.info("Max trades reached")
                return

            balance = self.client.get_balance()
            if balance < self.initial_balance * (1 - self.max_loss_pct / 100):
                logger.info("Max loss reached")
                return

            if self.use_volume_filter and vol_sma and curr_vol < vol_sma:
                logger.info("Volume too low, skipping trade")
                return

            if rsi and rsi < 30 and macd_line and macd_signal and macd_line > macd_signal:
                quantity = (balance * self.risk_pct / 100) / close_price
                order = self.client.create_order(self.symbol, "BUY", quantity)
                self.position = {
                    "entry_price": close_price,
                    "quantity": quantity,
                    "side": "BUY",
                    "order_id": order["orderId"]
                }
                self.trades += 1
                message = f"Opened LONG: {self.symbol} at {close_price:.2f}, Qty: {quantity:.2f}"
                asyncio.run(self.send_telegram_message(message))
                logger.info(message)

            elif self.position and rsi and rsi > 70:
                order = self.client.create_order(self.symbol, "SELL", self.position["quantity"])
                self.position = None
                self.trades += 1
                message = f"Closed LONG: {self.symbol} at {close_price:.2f}"
                asyncio.run(self.send_telegram_message(message))
                logger.info(message)

            if self.use_trailing and self.position:
                trailing_price = close_price * (1 - 0.01)
                if close_price < trailing_price:
                    order = self.client.create_order(self.symbol, "SELL", self.position["quantity"])
                    self.position = None
                    self.trades += 1
                    message = f"Trailing stop hit: Closed LONG at {close_price:.2f}"
                    asyncio.run(self.send_telegram_message(message))
                    logger.info(message)

        except Exception as e:
            logger.error(f"Trading loop error: {e}")

def main():
    parser = argparse.ArgumentParser(description="Binance Futures Trading Bot")
    parser.add_argument("--symbol", default="BTCUSDT", help="Trading pair")
    parser.add_argument("--timeframe", default="5m", help="Chart timeframe")
    parser.add_argument("--max-trades", type=int, default=3, help="Max trades per session")
    parser.add_argument("--risk-pct", type=float, default=1.0, help="Risk percentage per trade")
    parser.add_argument("--max-loss-pct", type=float, default=5.0, help="Max loss percentage")
    parser.add_argument("--tp-mult", type=float, default=3.5, help="Take profit multiplier")
    parser.add_argument("--no-trailing", action="store_false", dest="use_trailing", help="Disable trailing stop")
    parser.add_argument("--no-volume", action="store_false", dest="use_volume_filter", help="Disable volume filter")
    parser.add_argument("--live", action="store_true", help="Use live trading")
    parser.add_argument("--api-key", default=os.getenv("API_KEY"), help="Binance API key")
    parser.add_argument("--api-secret", default=os.getenv("API_SECRET"), help="Binance API secret")
    parser.add_argument("--telegram-token", default=os.getenv("TELEGRAM_TOKEN"), help="Telegram bot token")
    parser.add_argument("--chat-id", default=os.getenv("CHAT_ID"), help="Telegram chat ID")
    args = parser.parse_args()

    config = {
        "symbol": args.symbol,
        "timeframe": args.timeframe,
        "max_trades": args.max_trades,
        "risk_pct": args.risk_pct,
        "max_loss_pct": args.max_loss_pct,
        "tp_mult": args.tp_mult,
        "use_trailing": args.use_trailing,
        "use_volume_filter": args.use_volume_filter,
        "live": args.live,
        "api_key": args.api_key,
        "api_secret": args.api_secret,
        "telegram_token": args.telegram_token,
        "chat_id": args.chat_id
    }

    bot = TradingBot(config)
    bot.client.set_leverage(config["symbol"], 1)

    schedule.every(5).minutes.do(bot.trading_loop)
    logger.info("Trading loop started")
    while True:
        schedule.run_pending()
        time.sleep(1)

if __name__ == "__main__":
    main()
