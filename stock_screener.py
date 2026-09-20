"""
================================================================================
 STOCK MOMENTUM, NEWS & AI-ANALYSIS SCREENER
================================================================================
Scans essentially every NYSE/NASDAQ/AMEX-listed common stock, cheaply ranks
them by price/volume momentum, then runs a deeper enrichment pass (news,
insider filings, retail sentiment, weather, AI analysis) on the strongest
~60 candidates each cycle, and shows you the final top 20. Refreshes every
10 minutes. Click any row for an AI-written explanation of why it scored
the way it did.

--------------------------------------------------------------------------
IMPORTANT / HONEST DISCLAIMER
--------------------------------------------------------------------------
No free (or paid) API combination can *reliably* predict 24-hour stock
price moves. This is a heuristic research/screening tool, not a crystal
ball, and not financial advice. It combines:
  - price momentum (1-day, 5-day) and volume vs. its recent average
  - news headlines (Finnhub + NewsAPI), sentiment-scored AND cross-checked
    against actual price data to catch exaggerated/false numeric claims
  - StockTwits retail bullish/bearish sentiment
  - SEC EDGAR recent Form 4 (insider) and 8-K (material event) filing counts
  - a small sector-weather adjustment
  - an AI (Groq or local Ollama) analysis pass on top of all of the above
into one transparent score. Always do your own research.

--------------------------------------------------------------------------
ON "ALL STOCKS AVAILABLE ON ROBINHOOD"
--------------------------------------------------------------------------
Robinhood has no free/official public API for listing tradable stocks or
pulling market data (as of 2026 they only offer a Crypto Trading API, and
a newer "agentic trading" integration for placing real trades on a real
account -- not what we want here). Unofficial libraries exist but require
logging in with your real brokerage username/password and violate
Robinhood's Terms of Service, risking your account -- this script does not
use them. Instead, it pulls the full official, free, no-key NASDAQ Symbol
Directory (nasdaqtrader.com), which lists essentially every NYSE, NASDAQ,
and AMEX common stock -- functionally the same universe Robinhood trades,
since Robinhood doesn't offer anything off those exchanges.

--------------------------------------------------------------------------
SETUP (PyCharm)
--------------------------------------------------------------------------
1. pip install yfinance requests pandas
2. Fill in / check the CONFIG section below:
     FINNHUB_API_KEY -> https://finnhub.io/register        (free, instant)
     NEWSAPI_KEY     -> https://newsapi.org/register       (free, instant)
     SEC_USER_AGENT  -> no signup, just "YourName your-email@example.com"
     AI_BACKEND      -> "groq" (cloud, free tier, needs GROQ_API_KEY below,
                         get one free at https://console.groq.com) or
                         "ollama" (fully local, NO key of any kind --
                         install from ollama.com, run `ollama pull llama3.2`
                         once; the Ollama app runs a local server for you)
3. Run the file. First scan happens on launch, then every 10 minutes.

   SECURITY NOTE: don't paste real API keys into chat tools, screenshots,
   or public repos. If a key was ever exposed anywhere outside your own
   machine, regenerate it from that provider's dashboard.

--------------------------------------------------------------------------
NOTES ON FREE-TIER LIMITS / PERFORMANCE
--------------------------------------------------------------------------
- Stage A (cheap momentum filter) batches yfinance downloads across the
  full universe in chunks run with light parallelism. With MAX_UNIVERSE_SIZE
  capped at 2000 tickers, this stage typically takes well under a minute
  but can vary a lot with your connection and Yahoo's mood -- scanning
  literally every US-listed ticker every 10 minutes is not realistic on
  free infrastructure, so this cap is a deliberate, honest trade-off.
  Raise/lower MAX_UNIVERSE_SIZE if you want to trade breadth for speed.
- Stage B (deep enrichment: news/social/SEC/AI) only runs on the top
  SHORTLIST_SIZE candidates from Stage A, in parallel, which is what keeps
  Finnhub/StockTwits/SEC/Groq calls within their free-tier rate limits.
- Groq free tier: ~30 requests/minute, 14,400 requests/day on the
  "quick" model used for scoring. With SHORTLIST_SIZE=60 candidates every
  10 minutes that's about 8,600 calls/day for scoring -- comfortably inside
  the limit at the default settings.
- NewsAPI.org free tier: 100 calls/day, so we only refresh its broad
  headline cache every 3rd cycle (~30 min).
================================================================================
"""

import io
import re
import os
import sys
import json
import time
import hashlib
import secrets
import threading
import webbrowser
import urllib.parse
import http.server
import concurrent.futures
from datetime import datetime, timedelta

import requests
import pandas as pd
import yfinance as yf

import tkinter as tk
from tkinter import ttk

# ============================================================================
# CONFIG
# ============================================================================
FINNHUB_API_KEY = "da58vo9r01qudf6n3odgda58vo9r01qudf6n3oe0"
NEWSAPI_KEY = "d157916a854f4fd7abf4311003c1255c"
SEC_USER_AGENT = "Steve Hudson Stanley bluecaveman0@gmail.com"

AI_BACKEND = "groq"  # "groq" or "ollama"

# Groq (cloud, free tier, needs a key -- https://console.groq.com)
GROQ_API_KEY = "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"
GROQ_BASE_URL = "https://api.groq.com/openai/v1/chat/completions"
# NOTE: no hardcoded model name here anymore -- discover_groq_model() asks Groq's
# /models endpoint at runtime which model(s) this key actually has access to, and
# picks one automatically. If that fails, the failure reason (bad key, no access,
# etc.) is what gets shown to you instead of a generic "model not found".

# Ollama (fully local, NO key needed at all -- install ollama.com, `ollama pull llama3.2`)
OLLAMA_BASE_URL = "http://localhost:11434"
OLLAMA_MODEL = "llama3.2"

UPDATE_INTERVAL_SECONDS = 600      # 10 minutes
NEWSAPI_EVERY_N_CYCLES = 3         # ~30 min, respects NewsAPI's 100/day cap
RELOAD_UNIVERSE_EVERY_N_CYCLES = 144  # ~once/day; the stock list rarely changes intraday

MAX_UNIVERSE_SIZE = 2000           # cap on how many tickers Stage A scans (see notes above)
UNIVERSE_CHUNK_SIZE = 150          # tickers per yfinance batch call (smaller chunks + more
                                    # parallelism below finish Stage A faster wall-clock)
UNIVERSE_MAX_PARALLEL_CHUNKS = 12  # Stage A is network-bound (yfinance HTTP calls), so raising
                                    # this speeds up wall-clock scan time substantially without
                                    # adding real CPU load -- was 5

SHORTLIST_SIZE = 60                # how many top-momentum candidates get the deep enrichment pass
MAX_PARALLEL_TICKERS = 14          # Finnhub/StockTwits/SEC concurrency for the shortlist
                                    # (network-bound, not rate-limited like Groq -- was 8)
AI_QUICK_MAX_PARALLEL = 3          # keep this modest -- respects Groq's ~30 req/min free-tier cap

# Quality filters -- see filter_quality_candidates(). Without these, thin/erratic
# penny stocks and micro-caps dominate a pure momentum ranking (see notes above).
MIN_STOCK_PRICE = 2.0              # ignore anything trading under $2/share
MIN_AVG_DOLLAR_VOLUME = 3_000_000  # ignore anything averaging under $3M/day traded (price x avg volume)
MAX_SANE_5D_PCT = 300              # ignore 5-day moves bigger than this -- likely a split/data artifact

# ============================================================================
# LOGO (base64-encoded PNG, embedded here so the app stays a single file --
# no separate image file to keep track of or lose)
# ============================================================================
LOGO_PNG_BASE64 = (
    "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"
)

# ============================================================================
# FALLBACK WATCHLIST (used only if the NASDAQ symbol files can't be reached)
# ============================================================================
FALLBACK_TICKERS = {
    "AAPL": "Apple Inc.", "MSFT": "Microsoft Corp.", "GOOGL": "Alphabet Inc.",
    "AMZN": "Amazon.com Inc.", "NVDA": "NVIDIA Corp.", "META": "Meta Platforms",
    "TSLA": "Tesla Inc.", "JPM": "JPMorgan Chase", "V": "Visa Inc.",
    "JNJ": "Johnson & Johnson", "WMT": "Walmart Inc.", "XOM": "Exxon Mobil",
    "UNH": "UnitedHealth Group", "PG": "Procter & Gamble", "HD": "Home Depot",
}

SECTOR_MAP = {  # only used for the small weather bonus; unmapped tickers just get 0
    "XOM": "energy", "CVX": "energy",
    "UAL": "airline", "DAL": "airline", "AAL": "airline", "BA": "airline",
    "DE": "agriculture", "ADM": "agriculture", "BG": "agriculture",
    "WMT": "retail", "COST": "retail", "HD": "retail", "NKE": "retail", "TGT": "retail",
}

WEATHER_CITIES = {
    "energy":      {"name": "Houston, TX", "lat": 29.76, "lon": -95.37},
    "agriculture": {"name": "Chicago, IL (grain belt proxy)", "lat": 41.88, "lon": -87.63},
    "airline":     {"name": "New York, NY (major hub)", "lat": 40.71, "lon": -74.01},
    "retail":      {"name": "Dallas, TX", "lat": 32.78, "lon": -96.80},
}

WORLD_CITIES = {
    "New York": "America/New_York",
    "London": "Europe/London",
    "Tokyo": "Asia/Tokyo",
    "Hong Kong": "Asia/Hong_Kong",
}

# Market benchmarks for context (a dict, so the same benchmark can never appear
# twice by construction). MSCI World and STOXX 600 use liquid ETF proxies since
# their raw index tickers aren't reliably available on free Yahoo Finance data;
# S&P 500, Russell 2000, and Shanghai Composite use their standard raw indices.
BENCHMARKS = {
    "S&P 500": "^GSPC",
    "Russell 2000": "^RUT",
    "MSCI World (ETF proxy: URTH)": "URTH",
    "STOXX Europe 600 (ETF proxy: EXSA.DE)": "EXSA.DE",
    "Shanghai Composite": "000001.SS",
}

POSITIVE_WORDS = [
    "beat", "beats", "surge", "surges", "soar", "soars", "rally", "rallies",
    "upgrade", "upgraded", "record", "growth", "profit", "gain", "gains",
    "strong", "outperform", "bullish", "buyback", "expansion", "breakthrough",
    "approval", "approved", "partnership", "deal", "acquire", "acquisition",
    "raise", "raised", "exceeds", "positive", "optimistic", "win", "wins",
]
NEGATIVE_WORDS = [
    "miss", "misses", "plunge", "plunges", "slump", "downgrade", "downgraded",
    "cut", "cuts", "loss", "losses", "weak", "underperform", "bearish",
    "lawsuit", "investigation", "recall", "layoffs", "layoff", "decline",
    "declines", "fall", "falls", "warning", "delay", "delayed", "fraud",
    "bankruptcy", "negative", "pessimistic", "probe", "fine", "fined",
]

RELIABLE_SOURCES = {
    "reuters", "bloomberg", "associated press", "ap news", "wall street journal",
    "the wall street journal", "cnbc", "marketwatch", "yahoo finance", "barron's",
    "financial times", "the new york times", "forbes", "business insider",
    "the economist", "npr", "axios",
}

# ============================================================================
# NASDAQ SYMBOL DIRECTORY (free, no key -- the "all stocks" universe source)
# ============================================================================
NASDAQ_LISTED_URL = "https://www.nasdaqtrader.com/dynamic/symdir/nasdaqlisted.txt"
OTHER_LISTED_URL = "https://www.nasdaqtrader.com/dynamic/symdir/otherlisted.txt"
EXCLUDE_NAME_KEYWORDS = ["warrant", "right", " unit", "preferred", "depositary",
                          " notes", "trust pfd", "acquisition corp"]
SYMBOL_PATTERN = re.compile(r'^[A-Z]{1,5}(\.[A-Z])?$')


def _clean_security_name(name):
    name = name.strip()
    for suffix in (" - Common Stock", " Common Stock", " Class A Common Stock",
                   " Class B Common Stock", " Class C Common Stock"):
        if name.endswith(suffix):
            return name[: -len(suffix)].strip()
    return name


def _is_probably_common_stock(name):
    lower = name.lower()
    return not any(kw in lower for kw in EXCLUDE_NAME_KEYWORDS)


def load_full_stock_universe():
    """
    Loads NASDAQ's free symbol directory (no key). Filtered to plain common
    stock (heuristically -- excludes warrants/units/preferred/SPACs by name
    keyword), capped at MAX_UNIVERSE_SIZE. Falls back to a small hardcoded
    list if the files can't be reached.
    """
    global _UNIVERSE
    universe = {}

    for url, symbol_col in ((NASDAQ_LISTED_URL, "Symbol"), (OTHER_LISTED_URL, "ACT Symbol")):
        try:
            resp = requests.get(url, timeout=20)
            df = pd.read_csv(io.StringIO(resp.text), sep="|", on_bad_lines="skip")
            if "Test Issue" in df.columns:
                df = df[df["Test Issue"] == "N"]
            if "ETF" in df.columns:
                df = df[df["ETF"] == "N"]
            # itertuples() instead of iterrows() -- iterrows() rebuilds a Series
            # (with dtype coercion) per row, which is the dominant cost of this
            # function on a ~10k-row file; itertuples() yields plain tuples and
            # is an order of magnitude faster for a loop like this.
            if symbol_col in df.columns and "Security Name" in df.columns:
                for symbol_val, name_val in zip(df[symbol_col], df["Security Name"]):
                    symbol = str(symbol_val).strip().upper()
                    name = str(name_val).strip()
                    if SYMBOL_PATTERN.match(symbol) and _is_probably_common_stock(name):
                        universe[symbol.replace(".", "-")] = _clean_security_name(name)
        except Exception as e:
            print(f"[universe load error - {url}] {e}")

    if not universe:
        print("[universe] NASDAQ symbol files unavailable -- using small fallback watchlist.")
        universe = dict(FALLBACK_TICKERS)

    if len(universe) > MAX_UNIVERSE_SIZE:
        # Simple deterministic cap. Raise MAX_UNIVERSE_SIZE for broader coverage.
        keys = sorted(universe.keys())[:MAX_UNIVERSE_SIZE]
        universe = {k: universe[k] for k in keys}

    _UNIVERSE = universe
    print(f"[universe] Loaded {len(_UNIVERSE)} tickers.")


# ============================================================================
# GLOBAL STATE
# ============================================================================
_UNIVERSE = {}
_TICKER_TO_CIK = {}
_NEWSAPI_CACHE_HEADLINES = []
_CYCLE_COUNT = 0

# ============================================================================
# PRICE DATA (yfinance, chunked + parallel for large universes)
# ============================================================================

def _download_price_chunk(symbols):
    results = {}
    try:
        data = yf.download(
            tickers=symbols, period="10d", interval="1d",
            group_by="ticker", progress=False, threads=True,
        )
    except Exception as e:
        print(f"[price chunk error] {e}")
        return results

    for sym in symbols:
        try:
            df = data[sym] if len(symbols) > 1 else data
            df = df.dropna()
            if len(df) < 2:
                continue
            last_close = float(df["Close"].iloc[-1])
            prev_close = float(df["Close"].iloc[-2])
            chg_1d_pct = (last_close - prev_close) / prev_close * 100.0

            five_day_ago = float(df["Close"].iloc[max(0, len(df) - 6)])
            chg_5d_pct = (last_close - five_day_ago) / five_day_ago * 100.0

            last_vol = float(df["Volume"].iloc[-1])
            avg_vol = float(df["Volume"].iloc[:-1].mean()) if len(df) > 1 else last_vol
            vol_ratio = (last_vol / avg_vol) if avg_vol > 0 else 1.0

            results[sym] = {
                "price": round(last_close, 2),
                "chg_1d_pct": round(chg_1d_pct, 2),
                "chg_5d_pct": round(chg_5d_pct, 2),
                "vol_ratio": round(vol_ratio, 2),
                "avg_volume": round(avg_vol),
            }
        except Exception:
            continue
    return results


def fetch_price_data_bulk(all_symbols):
    """Chunked, lightly-parallel batch download across the whole universe."""
    chunks = [all_symbols[i:i + UNIVERSE_CHUNK_SIZE] for i in range(0, len(all_symbols), UNIVERSE_CHUNK_SIZE)]
    results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=UNIVERSE_MAX_PARALLEL_CHUNKS) as executor:
        futures = [executor.submit(_download_price_chunk, c) for c in chunks]
        for future in concurrent.futures.as_completed(futures):
            try:
                results.update(future.result())
            except Exception as e:
                print(f"[bulk price error] {e}")
    return results


def filter_quality_candidates(price_data):
    """
    Drops stocks that are too thin/cheap/erratic to be a meaningful momentum
    signal. Without this, a pure momentum ranking gets dominated by penny
    stocks and micro-caps -- names like a sub-$2 stock with a recent reverse
    split can show a 50%+ "move" that's really just illiquidity or corporate
    action noise, not a genuine signal. This filter runs BEFORE ranking, on
    the full scanned universe, so the shortlist only ever draws from stocks
    with real trading liquidity behind their price action.
    """
    filtered = {}
    for sym, stats in price_data.items():
        if stats["price"] < MIN_STOCK_PRICE:
            continue
        dollar_volume = stats["price"] * stats["avg_volume"]
        if dollar_volume < MIN_AVG_DOLLAR_VOLUME:
            continue
        if abs(stats["chg_5d_pct"]) > MAX_SANE_5D_PCT:
            continue  # very likely a reverse split / data artifact, not real momentum
        filtered[sym] = stats
    return filtered


def basic_momentum_score(stats):
    """Cheap, price/volume-only score used ONLY to pick the Stage-B shortlist."""
    return stats["chg_1d_pct"] * 1.0 + stats["chg_5d_pct"] * 0.4 + (stats["vol_ratio"] - 1.0) * 3.0


# ============================================================================
# NEWS: Finnhub (per-ticker) + NewsAPI (broad, throttled) -- with source tags
# ============================================================================

def fetch_finnhub_headlines(symbol, max_items=5):
    if not FINNHUB_API_KEY or "YOUR_" in FINNHUB_API_KEY:
        return []
    today = datetime.utcnow().date()
    two_days_ago = today - timedelta(days=2)
    try:
        resp = requests.get(
            "https://finnhub.io/api/v1/company-news",
            params={"symbol": symbol, "from": two_days_ago.isoformat(),
                    "to": today.isoformat(), "token": FINNHUB_API_KEY},
            timeout=10,
        )
        if resp.status_code != 200:
            return []
        items = resp.json()
        return [
            {"headline": it.get("headline", ""), "source": it.get("source", "Finnhub")}
            for it in items if it.get("headline")
        ][:max_items]
    except Exception as e:
        print(f"[finnhub news error {symbol}] {e}")
        return []


def refresh_newsapi_cache_if_due():
    global _NEWSAPI_CACHE_HEADLINES, _CYCLE_COUNT
    if not NEWSAPI_KEY or "YOUR_" in NEWSAPI_KEY:
        return
    if _CYCLE_COUNT % NEWSAPI_EVERY_N_CYCLES != 0:
        return
    try:
        resp = requests.get(
            "https://newsapi.org/v2/top-headlines",
            params={"category": "business", "language": "en", "pageSize": 100, "apiKey": NEWSAPI_KEY},
            timeout=15,
        )
        data = resp.json()
        if data.get("status") == "ok":
            _NEWSAPI_CACHE_HEADLINES = [
                {"headline": a.get("title") or "", "source": (a.get("source") or {}).get("name", "NewsAPI")}
                for a in data.get("articles", []) if a.get("title")
            ]
    except Exception as e:
        print(f"[newsapi fetch error] {e}")


def match_newsapi_headlines_for_ticker(symbol, company_name, max_items=3):
    if not _NEWSAPI_CACHE_HEADLINES:
        return []
    name_key = company_name.split()[0].lower() if company_name else symbol.lower()
    matches = []
    for item in _NEWSAPI_CACHE_HEADLINES:
        h_lower = item["headline"].lower()
        if symbol.lower() in h_lower or name_key in h_lower:
            matches.append(item)
        if len(matches) >= max_items:
            break
    return matches


# ============================================================================
# CLAIM VERIFICATION + SOURCE RELIABILITY
# (e.g. catches a headline claiming an absurd % move that real price data
#  contradicts, regardless of who said it or how "reliable" they normally are)
# ============================================================================

PERCENT_CLAIM_REGEX = re.compile(r'(-?\d[\d,]*(?:\.\d+)?)\s*%')


def extract_percent_claims(text):
    claims = []
    for raw in PERCENT_CLAIM_REGEX.findall(text):
        try:
            claims.append(float(raw.replace(",", "")))
        except ValueError:
            continue
    return claims


def check_headline_against_data(headline, price_stats):
    """Returns (contradicts: bool, note: str|None). Ground truth is the
    actual computed price data, not the claim, no matter the source."""
    claims = extract_percent_claims(headline)
    if not claims:
        return False, None
    actual_1d = price_stats["chg_1d_pct"]
    actual_5d = price_stats["chg_5d_pct"]
    for claim in claims:
        close_to_1d = abs(claim - actual_1d) <= 15
        close_to_5d = abs(claim - actual_5d) <= 15
        if abs(claim) > 100 or not (close_to_1d or close_to_5d):
            return True, (
                f"Headline cites {claim}% but actual market data shows "
                f"{actual_1d}% (1-day) / {actual_5d}% (5-day) -- treat this claim as unverified."
            )
    return False, None


def source_reliability_tag(source_name):
    if not source_name:
        return "unknown source"
    return "established financial press" if source_name.strip().lower() in RELIABLE_SOURCES else "unverified/lesser-known source"


def process_headlines(raw_items, price_stats):
    processed = []
    for item in raw_items:
        headline = item["headline"]
        source = item.get("source", "unknown")
        contradicts, note = check_headline_against_data(headline, price_stats)
        processed.append({
            "headline": headline, "source": source,
            "reliability": source_reliability_tag(source),
            "contradicts_data": contradicts, "note": note,
        })
    return processed


def keyword_sentiment_from_processed(processed_headlines):
    usable = [p["headline"] for p in processed_headlines if not p["contradicts_data"]]
    if not usable:
        return 0.0
    score = 0
    for h in usable:
        h_lower = h.lower()
        for w in POSITIVE_WORDS:
            if w in h_lower:
                score += 1
        for w in NEGATIVE_WORDS:
            if w in h_lower:
                score -= 1
    return round(score / max(1, len(usable)), 2)


# ============================================================================
# STOCKTWITS (retail sentiment, no key)
# ============================================================================

def fetch_stocktwits_sentiment(symbol):
    try:
        resp = requests.get(f"https://api.stocktwits.com/api/2/streams/symbol/{symbol}.json", timeout=8)
        if resp.status_code != 200:
            return 0.0, 0
        messages = resp.json().get("messages", [])
        bullish, bearish = 0, 0
        for m in messages:
            sentiment = (m.get("entities", {}) or {}).get("sentiment")
            if sentiment:
                label = sentiment.get("basic")
                if label == "Bullish":
                    bullish += 1
                elif label == "Bearish":
                    bearish += 1
        total = len(messages)
        ratio = round((bullish - bearish) / total, 2) if total > 0 else 0.0
        return ratio, total
    except Exception as e:
        print(f"[stocktwits error {symbol}] {e}")
        return 0.0, 0


# ============================================================================
# SEC EDGAR (insider Form 4 + 8-K material events, no key, needs User-Agent)
# ============================================================================

def load_ticker_to_cik_map():
    global _TICKER_TO_CIK
    if _TICKER_TO_CIK:
        return
    try:
        resp = requests.get(
            "https://www.sec.gov/files/company_tickers.json",
            headers={"User-Agent": SEC_USER_AGENT}, timeout=15,
        )
        for entry in resp.json().values():
            ticker = entry.get("ticker", "").upper()
            cik = str(entry.get("cik_str", "")).zfill(10)
            if ticker:
                _TICKER_TO_CIK[ticker] = cik
    except Exception as e:
        print(f"[SEC ticker map error] {e}")


def fetch_sec_recent_activity(symbol, lookback_days=3):
    default = {"form4_count": 0, "has_recent_8k": False}
    cik = _TICKER_TO_CIK.get(symbol.upper().replace("-", ".")) or _TICKER_TO_CIK.get(symbol.upper())
    if not cik:
        return default
    try:
        resp = requests.get(
            f"https://data.sec.gov/submissions/CIK{cik}.json",
            headers={"User-Agent": SEC_USER_AGENT}, timeout=15,
        )
        recent = resp.json().get("filings", {}).get("recent", {})
        forms = recent.get("form", [])
        dates = recent.get("filingDate", [])
        cutoff = datetime.utcnow().date() - timedelta(days=lookback_days)

        form4_count = 0
        has_8k = False
        for form, date_str in zip(forms, dates):
            try:
                filing_date = datetime.strptime(date_str, "%Y-%m-%d").date()
            except ValueError:
                continue
            if filing_date < cutoff:
                continue
            if form == "4":
                form4_count += 1
            elif form == "8-K":
                has_8k = True
        return {"form4_count": form4_count, "has_recent_8k": has_8k}
    except Exception as e:
        print(f"[SEC filings error {symbol}] {e}")
        return default


# ============================================================================
# WEATHER (Open-Meteo, no key) + WORLD TIME (WorldTimeAPI, no key)
# ============================================================================

def fetch_weather_adjustments():
    adjustments = {}
    for sector, city in WEATHER_CITIES.items():
        try:
            resp = requests.get(
                "https://api.open-meteo.com/v1/forecast",
                params={"latitude": city["lat"], "longitude": city["lon"], "current_weather": True},
                timeout=8,
            )
            temp_c = resp.json().get("current_weather", {}).get("temperature")
            adjustments[sector] = _weather_to_bonus(sector, temp_c)
        except Exception as e:
            print(f"[weather fetch error {sector}] {e}")
            adjustments[sector] = 0.0
    return adjustments


def _weather_to_bonus(sector, temp_c):
    if temp_c is None:
        return 0.0
    if sector == "energy":
        return 0.5 if (temp_c < 5 or temp_c > 33) else 0.0
    if sector == "airline":
        return -0.5 if (temp_c < -5 or temp_c > 38) else 0.0
    if sector == "agriculture":
        return 0.3 if (temp_c < 0 or temp_c > 32) else 0.0
    if sector == "retail":
        return 0.2 if (15 <= temp_c <= 25) else 0.0
    return 0.0


def fetch_world_times():
    out = {}
    for city, tz in WORLD_CITIES.items():
        try:
            resp = requests.get(f"https://worldtimeapi.org/api/timezone/{tz}", timeout=6)
            out[city] = datetime.fromisoformat(resp.json()["datetime"]).strftime("%H:%M")
        except Exception:
            out[city] = "—"
    return out


def fetch_benchmarks():
    """One batched download for all benchmark tickers (reuses the same chunk
    downloader as the main universe scan, so it's a single extra yfinance call)."""
    raw = _download_price_chunk(list(BENCHMARKS.values()))
    results = {}
    for name, ticker in BENCHMARKS.items():
        if ticker in raw:
            results[name] = raw[ticker]
    return results


# ============================================================================
# AI BACKEND (Groq cloud OR local Ollama -- picked via AI_BACKEND)
# ============================================================================

_GROQ_RESOLVED_MODEL = None   # discovered once at runtime, see discover_groq_model()
_GROQ_DIAGNOSIS = None        # human-readable explanation if discovery fails


def _test_groq_chat_model(model_id):
    """Actually try a trivial real chat-completion call against this model, rather than
    trusting its name. Catches specialty models (TTS voices, moderation classifiers, etc.)
    that don't match any keyword we'd think to exclude -- e.g. a text-to-speech voice model
    literally named 'canopylabs/orpheus-arabic-saudi' slipped past a keyword filter."""
    try:
        resp = requests.post(
            GROQ_BASE_URL,
            headers={"Authorization": f"Bearer {GROQ_API_KEY}", "Content-Type": "application/json"},
            json={"model": model_id, "messages": [{"role": "user", "content": "Say OK."}], "max_tokens": 5},
            timeout=15,
        )
        return "choices" in resp.json()
    except Exception:
        return False


def discover_groq_model():
    """
    Asks Groq which models this key can see, then actually test-calls candidates
    (rather than trusting a name-based guess) until one responds as a real chat
    model. Called once, lazily, before the first real Groq call.
    """
    global _GROQ_RESOLVED_MODEL, _GROQ_DIAGNOSIS
    if _GROQ_RESOLVED_MODEL or _GROQ_DIAGNOSIS:
        return  # already resolved (or already failed) this run

    if not GROQ_API_KEY or "YOUR_" in GROQ_API_KEY:
        _GROQ_DIAGNOSIS = "No Groq API key configured."
        return

    try:
        resp = requests.get(
            "https://api.groq.com/openai/v1/models",
            headers={"Authorization": f"Bearer {GROQ_API_KEY}"},
            timeout=15,
        )
        if resp.status_code == 401:
            _GROQ_DIAGNOSIS = (
                "Groq rejected this API key as invalid (401 Unauthorized). This is "
                "almost always a copy/paste issue (a stray space or a truncated key) "
                "or a key that was revoked -- it is NOT a model-name problem. Get a "
                "fresh key at https://console.groq.com/keys and replace GROQ_API_KEY."
            )
            return
        resp.raise_for_status()
        model_ids = [m["id"] for m in resp.json().get("data", [])]
        if not model_ids:
            _GROQ_DIAGNOSIS = (
                "Groq accepted the API key but reports zero available models for this "
                "account. Check https://console.groq.com/keys and the account's plan/status."
            )
            return

        # ONLY ever pick from known, plain chat-completion models with generous free-tier
        # quotas. No "grab whatever else is in the account's list" fallback -- that's what
        # kept landing on unsuitable models (a TTS voice model, then groq/compound, an
        # agentic tool-orchestration model with a 250-requests/DAY cap, nowhere near enough
        # for periodic scoring of dozens of tickers). If none of these are available, say so
        # plainly rather than substituting something that will just fail differently.
        preferred = ["llama-3.1-8b-instant", "llama-3.3-70b-versatile", "llama3-8b-8192",
                     "llama-3.1-70b-versatile", "gemma2-9b-it", "mixtral-8x7b-32768"]
        candidates = [m for m in preferred if m in model_ids]

        if not candidates:
            _GROQ_DIAGNOSIS = (
                "None of the standard chat models this tool knows about are available on "
                f"this account. Models this account actually has: {', '.join(model_ids)}. "
                "Either pick one of those and add it to the 'preferred' list inside "
                "discover_groq_model(), or switch AI_BACKEND to \"ollama\" instead."
            )
            return

        tried = []
        for model_id in candidates:
            tried.append(model_id)
            if _test_groq_chat_model(model_id):
                _GROQ_RESOLVED_MODEL = model_id
                print(f"[groq] Using model: {model_id} (verified with a real test call)")
                return

        _GROQ_DIAGNOSIS = (
            f"None of the standard chat models responded successfully to a real "
            f"chat-completion test call (tried: {', '.join(tried)}). Check "
            "https://console.groq.com/playground and this account's model access / "
            "terms acceptance, and its daily rate limits at "
            "https://console.groq.com/settings/billing."
        )
    except Exception as e:
        _GROQ_DIAGNOSIS = f"Could not reach Groq to discover available models: {e}"


def call_groq_chat(system_prompt, user_prompt, max_tokens=350):
    discover_groq_model()
    if _GROQ_DIAGNOSIS:
        return _GROQ_DIAGNOSIS
    try:
        resp = requests.post(
            GROQ_BASE_URL,
            headers={"Authorization": f"Bearer {GROQ_API_KEY}", "Content-Type": "application/json"},
            json={
                "model": _GROQ_RESOLVED_MODEL,
                "messages": [{"role": "system", "content": system_prompt},
                             {"role": "user", "content": user_prompt}],
                "temperature": 0.4,
                "max_tokens": max_tokens,
            },
            timeout=30,
        )
        data = resp.json()
        if "choices" in data:
            content = data["choices"][0]["message"]["content"].strip()
            finish_reason = data["choices"][0].get("finish_reason")
            if finish_reason == "length":
                content += "\n\n[response cut off -- raise max_tokens for longer answers]"
            return content
        return f"Groq API error: {data}"
    except Exception as e:
        return f"Groq API call failed: {e}"


def call_ollama_chat(system_prompt, user_prompt, max_tokens=350):
    try:
        resp = requests.post(
            f"{OLLAMA_BASE_URL}/api/chat",
            json={
                "model": OLLAMA_MODEL,
                "messages": [{"role": "system", "content": system_prompt},
                             {"role": "user", "content": user_prompt}],
                "stream": False,
                "options": {"num_predict": max_tokens},
            },
            timeout=60,
        )
        data = resp.json()
        return data.get("message", {}).get("content", "").strip()
    except requests.exceptions.ConnectionError:
        return ("Could not connect to Ollama. Make sure the Ollama app is running "
                "and you've pulled a model (e.g. `ollama pull llama3.2`).")
    except Exception as e:
        return f"Ollama call failed: {e}"


def call_ai_chat(system_prompt, user_prompt, purpose="quick"):
    """purpose='quick' -> frequent per-ticker scoring, short SCORE/REASON output,
    kept tight to stay fast and cheap. 'explain' -> rare on-click deep dive,
    given much more room so it doesn't get cut off mid-sentence."""
    max_tokens = 120 if purpose == "quick" else 700
    if AI_BACKEND == "groq":
        return call_groq_chat(system_prompt, user_prompt, max_tokens=max_tokens)
    return call_ollama_chat(system_prompt, user_prompt, max_tokens=max_tokens)



def ai_quick_score(symbol, name, stats, processed_headlines, sec_data, social_ratio):
    """Lightweight AI pass folded into the score, in addition to the keyword heuristics."""
    headline_lines = "\n".join(
        f"- ({p['reliability']}{', FLAGGED AS CONTRADICTING MARKET DATA' if p['contradicts_data'] else ''}) {p['headline']}"
        for p in processed_headlines
    ) or "(no recent headlines)"
    prompt = (
        f"Ticker {symbol} ({name}).\n"
        f"1-day change: {stats['chg_1d_pct']}%. 5-day change: {stats['chg_5d_pct']}%. "
        f"Volume vs avg: {stats['vol_ratio']}x.\n"
        f"StockTwits sentiment ratio: {social_ratio}.\n"
        f"SEC: {sec_data['form4_count']} Form 4 filings in 3 days; recent 8-K filed: {sec_data['has_recent_8k']}.\n"
        f"Headlines:\n{headline_lines}\n\n"
        "Respond with EXACTLY two lines:\n"
        "SCORE: <number from -1.0 (bearish) to 1.0 (bullish)>\n"
        "REASON: <one short sentence>"
    )
    system = (
        "You are a terse quantitative research assistant ranking stocks for a screener. "
        "CRITICAL: zero SEC filings, a 0.0 news-sentiment score, or a neutral StockTwits "
        "ratio mean NO DATA WAS FOUND -- treat these as unknowns, never as confirming "
        "anything bullish or bearish. Do not phrase an absence of data as if it were "
        "evidence (e.g. do not say 'no insider selling' when there were simply zero "
        "filings to look at). A large, sudden 1-day or 5-day price/volume move is itself "
        "a RISK signal (volatility, thin liquidity, single-event-driven), not purely a "
        "bullish one -- weigh it accordingly rather than reading it as pure buying pressure. "
        "Ignore any headline flagged as contradicting market data. Never claim certainty "
        "about future prices."
    )
    raw = call_ai_chat(system, prompt, purpose="quick")
    score, reason = 0.0, raw
    m = re.search(r"SCORE:\s*(-?\d+(?:\.\d+)?)", raw)
    if m:
        try:
            score = max(-1.0, min(1.0, float(m.group(1))))
        except ValueError:
            score = 0.0
    r = re.search(r"REASON:\s*(.+)", raw)
    if r:
        reason = r.group(1).strip()
    return score, reason


def call_ai_explain(context_text):
    system_prompt = (
        "You are a concise financial research assistant. You will be given raw "
        "quantitative data (price momentum, volume, news sentiment, StockTwits "
        "retail sentiment, SEC filing activity, and a prior quick AI score) plus "
        "recent headlines for one stock, some of which may be flagged as "
        "contradicting actual market data. "
        "CRITICAL: zero SEC filings, a 0.0 news-sentiment score, or a neutral "
        "StockTwits ratio all mean NO DATA WAS FOUND -- these are NOT evidence of "
        "low risk, investor confidence, or the absence of negative sentiment. Never "
        "phrase an absence of data as if it confirms something (do not say things "
        "like 'no insider selling keeps risk low' when there were simply zero "
        "filings, or 'no negative chatter' when the sentiment score is 0.0 because "
        "no headlines were found at all). Treat a large, sudden price/volume swing "
        "as a genuine risk factor to flag -- explosive short-term moves are often "
        "driven by a single news event or thin liquidity, not sustainable momentum. "
        "Explain in 4-6 short sentences why this stock scored the way it did, being "
        "specific about which factors actually drove it (and which factors are "
        "simply unknown/no-data, if relevant). Explicitly call out and disregard "
        "any claim flagged as contradicting market data. Do NOT claim certainty "
        "about future price moves. End with one sentence on the key risk or caveat."
    )
    return call_ai_chat(system_prompt, context_text, purpose="explain")


# ============================================================================
# SCORING
# ============================================================================

def compute_score(price_stats, sentiment_score, weather_bonus, social_ratio, social_volume, sec_data, ai_score=0.0):
    momentum_1d = price_stats["chg_1d_pct"]
    momentum_5d = price_stats["chg_5d_pct"]
    vol_ratio = price_stats["vol_ratio"]
    social_weight = social_ratio * min(social_volume / 20.0, 1.5)
    sec_bonus = min(sec_data["form4_count"], 5) * 0.3 + (1.0 if sec_data["has_recent_8k"] else 0.0)

    score = (
        momentum_1d * 1.0
        + momentum_5d * 0.4
        + (vol_ratio - 1.0) * 3.0
        + sentiment_score * 2.0
        + weather_bonus
        + social_weight * 1.5
        + sec_bonus
        + ai_score * 2.0
    )
    return round(score, 2)


def build_explanation_context(symbol, name, price_stats, processed_headlines, sentiment_score,
                               weather_bonus, social_ratio, social_volume, sec_data, score):
    lines = [
        f"Ticker: {symbol} ({name})",
        f"Current price: ${price_stats['price']}",
        f"1-day change: {price_stats['chg_1d_pct']}%",
        f"5-day change: {price_stats['chg_5d_pct']}%",
        f"Volume vs recent average: {price_stats['vol_ratio']}x",
        f"News keyword-sentiment score (non-contradicted headlines only): {sentiment_score}",
        f"StockTwits sentiment ratio: {social_ratio} across {social_volume} recent messages",
        f"SEC EDGAR: {sec_data['form4_count']} Form 4 (insider) filings in last 3 days; "
        f"recent 8-K (material event) filed: {sec_data['has_recent_8k']}",
        f"Weather/sector adjustment: {weather_bonus}",
        f"Composite score (pre-AI adjustment): {score}",
        "Recent headlines (source reliability + market-data cross-check):",
    ]
    if processed_headlines:
        for p in processed_headlines:
            flag = "FLAGGED - CONTRADICTS MARKET DATA" if p["contradicts_data"] else "ok"
            lines.append(f"  - [{p['source']} | {p['reliability']} | {flag}] {p['headline']}")
            if p["note"]:
                lines.append(f"      note: {p['note']}")
    else:
        lines.append("  (no recent headlines found)")
    return "\n".join(lines)


def process_single_ticker(symbol, name, stats, weather_adjustments):
    """All Stage-B network calls for ONE shortlisted ticker (runs in a thread pool)."""
    finnhub_items = fetch_finnhub_headlines(symbol)
    newsapi_items = match_newsapi_headlines_for_ticker(symbol, name)
    processed_headlines = process_headlines(finnhub_items + newsapi_items, stats)
    sentiment_score = keyword_sentiment_from_processed(processed_headlines)

    social_ratio, social_volume = fetch_stocktwits_sentiment(symbol)
    sec_data = fetch_sec_recent_activity(symbol)

    sector = SECTOR_MAP.get(symbol)
    weather_bonus = weather_adjustments.get(sector, 0.0) if sector else 0.0

    score = compute_score(stats, sentiment_score, weather_bonus, social_ratio, social_volume, sec_data)
    context = build_explanation_context(
        symbol, name, stats, processed_headlines, sentiment_score,
        weather_bonus, social_ratio, social_volume, sec_data, score,
    )
    return {
        "symbol": symbol, "name": name, "stats": stats,
        "processed_headlines": processed_headlines, "sentiment": sentiment_score,
        "weather_bonus": weather_bonus, "social_ratio": social_ratio,
        "social_volume": social_volume, "sec_data": sec_data,
        "score": score, "ai_score": 0.0, "ai_reason": "", "context": context,
    }


# ============================================================================
# ACCOUNTS (local JSON file, hashed+salted passwords -- login / create account)
# ============================================================================

def get_base_dir():
    """
    Directory where saved data (accounts, org keys, purchase logs) lives.
    When running as a normal .py script, that's the script's own folder.
    When running as a PyInstaller-built .exe, __file__ resolves to a temp
    extraction folder that gets wiped on every launch -- so in that case we
    use the folder the .exe itself lives in instead, which is what actually
    persists between runs.
    """
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


ACCOUNTS_PATH = os.path.join(get_base_dir(), "accounts.json")
ORG_KEYS_PATH = os.path.join(get_base_dir(), "org_keys.json")
DEFAULT_ACCOUNT_USERNAME = "Ayaan"
DEFAULT_ACCOUNT_PASSWORD = "rtandon"


def _hash_password(password, salt):
    return hashlib.sha256((salt + password).encode("utf-8")).hexdigest()


def load_accounts():
    if not os.path.exists(ACCOUNTS_PATH):
        return {}
    try:
        with open(ACCOUNTS_PATH, "r") as f:
            return json.load(f)
    except Exception as e:
        print(f"[accounts read error] {e}")
        return {}


def save_accounts(accounts):
    try:
        with open(ACCOUNTS_PATH, "w") as f:
            json.dump(accounts, f, indent=2)
        return True
    except Exception as e:
        print(f"[accounts save error] {e}")
        return False


def load_org_keys():
    if not os.path.exists(ORG_KEYS_PATH):
        return {}
    try:
        with open(ORG_KEYS_PATH, "r") as f:
            return json.load(f)
    except Exception as e:
        print(f"[org keys read error] {e}")
        return {}


def save_org_keys(org_keys):
    try:
        with open(ORG_KEYS_PATH, "w") as f:
            json.dump(org_keys, f, indent=2)
        return True
    except Exception as e:
        print(f"[org keys save error] {e}")
        return False


def ensure_default_account():
    accounts = load_accounts()
    if DEFAULT_ACCOUNT_USERNAME not in accounts:
        salt = secrets.token_hex(8)
        accounts[DEFAULT_ACCOUNT_USERNAME] = {
            "salt": salt,
            "password_hash": _hash_password(DEFAULT_ACCOUNT_PASSWORD, salt),
            "role": "owner",
            "org_key": None,
        }
        save_accounts(accounts)
    else:
        # Migrate a pre-existing Ayaan entry from before roles/org keys existed
        # (e.g. an accounts.json left over from testing an earlier version of
        # this script) -- otherwise it's stuck without role="owner" forever,
        # since the branch above only runs when the entry is missing entirely.
        entry = accounts[DEFAULT_ACCOUNT_USERNAME]
        if entry.get("role") != "owner":
            entry["role"] = "owner"
            entry["org_key"] = None
            save_accounts(accounts)


def find_account_key(accounts, username):
    """Case-insensitive username lookup -- returns the actual stored key
    (preserving its original casing) or None. Usernames are how people
    identify themselves; treating 'ayaan' and 'Ayaan' as different accounts
    is a footgun, not a feature."""
    username_lower = username.strip().lower()
    for key in accounts:
        if key.lower() == username_lower:
            return key
    return None


def get_account_role(username):
    accounts = load_accounts()
    key = find_account_key(accounts, username)
    if not key:
        return "member"
    return accounts[key].get("role", "member")  # legacy accounts without a role default to "member"


def generate_org_key():
    return "ORG-" + secrets.token_hex(6).upper()


def org_key_usage_count(org_key):
    return sum(1 for e in load_accounts().values() if e.get("org_key") == org_key)


def create_org_key(admin_username, admin_password, max_accounts):
    """
    Ayaan-only action (gated in the UI, not here). Creates a new org key with a
    seat limit, and designates admin_username as its admin -- promoting them if
    they already have an account, or creating one for them (admin_password
    required in that case) if they don't. Returns (success, message, key_or_None).
    """
    admin_username = admin_username.strip()
    if not admin_username:
        return False, "Admin username is required.", None
    if max_accounts < 1:
        return False, "Max accounts must be at least 1.", None

    accounts = load_accounts()
    key = generate_org_key()

    existing_key = find_account_key(accounts, admin_username)
    if existing_key:
        accounts[existing_key]["role"] = "admin"
        accounts[existing_key]["org_key"] = key
        resolved_admin_name = existing_key
    else:
        if not admin_password:
            return False, "That admin username doesn't exist yet -- enter a password to create it.", None
        salt = secrets.token_hex(8)
        accounts[admin_username] = {
            "salt": salt, "password_hash": _hash_password(admin_password, salt),
            "role": "admin", "org_key": key,
        }
        resolved_admin_name = admin_username

    if not save_accounts(accounts):
        return False, "Failed to save the admin account -- see console for details.", None

    org_keys = load_org_keys()
    org_keys[key] = {
        "max_accounts": max_accounts,
        "admin_username": resolved_admin_name,
        "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    }
    if not save_org_keys(org_keys):
        return False, "Admin account saved, but failed to save the org key -- see console for details.", None

    return True, f"Org key created: {key}", key


def delete_account(username):
    accounts = load_accounts()
    key = find_account_key(accounts, username)
    if not key:
        return False, "That account doesn't exist."
    if key == DEFAULT_ACCOUNT_USERNAME or accounts[key].get("role") == "owner":
        return False, "The owner account cannot be deleted."
    del accounts[key]
    if save_accounts(accounts):
        return True, "Account deleted."
    return False, "Failed to save -- see console for details."


def create_account(username, password, org_key):
    """Every account except the owner must be created with a valid, non-full org key."""
    username = username.strip()
    org_key = org_key.strip()
    if not username or not password or not org_key:
        return False, "Username, password, and org key are all required."
    accounts = load_accounts()
    if find_account_key(accounts, username):
        return False, "That username already exists."

    org_keys = load_org_keys()
    key_info = org_keys.get(org_key)
    if not key_info:
        return False, "That org key was not recognized."
    if org_key_usage_count(org_key) >= key_info["max_accounts"]:
        return False, "That org key has already reached its maximum number of accounts."

    salt = secrets.token_hex(8)
    accounts[username] = {
        "salt": salt, "password_hash": _hash_password(password, salt),
        "role": "member", "org_key": org_key,
    }
    if save_accounts(accounts):
        return True, "Account created -- you can log in now."
    return False, "Failed to save the new account -- see console for details."


def verify_login(username, password):
    accounts = load_accounts()
    key = find_account_key(accounts, username)
    if not key:
        return False
    entry = accounts[key]
    return _hash_password(password, entry["salt"]) == entry["password_hash"]


def check_login_eligibility(username):
    """After a password checks out, confirm the account is actually allowed to log
    in: the owner always is; everyone else needs a valid org key on file."""
    accounts = load_accounts()
    key = find_account_key(accounts, username)
    if not key:
        return False, "Account not found."
    entry = accounts[key]
    if entry.get("role") == "owner":
        return True, ""
    if not entry.get("org_key"):
        return False, "This account isn't linked to an org key -- ask Ayaan or an admin for one."
    return True, ""


# ============================================================================
# COMPANY PROFILE (Finnhub, "what is this stock" tab -- called lazily on click)
# ============================================================================

def fetch_company_profile(symbol):
    if not FINNHUB_API_KEY or "YOUR_" in FINNHUB_API_KEY:
        return {}
    try:
        resp = requests.get(
            "https://finnhub.io/api/v1/stock/profile2",
            params={"symbol": symbol, "token": FINNHUB_API_KEY},
            timeout=10,
        )
        if resp.status_code != 200:
            return {}
        return resp.json() or {}
    except Exception as e:
        print(f"[company profile error {symbol}] {e}")
        return {}


# ============================================================================
# HOLDINGS: SELL / WATCH / HOLD heuristic
# (Finnhub's free analyst recommendation-trend endpoint + your purchase price
#  + recent momentum -- combined into a simple, transparent, rule-based flag.
#  This is NOT financial advice, just a screener-style heuristic like the rest
#  of the tool.)
# ============================================================================

STOP_LOSS_PCT = -8          # down this much from your purchase price -> lean "sell" signal
TAKE_PROFIT_FADE_PCT = 20   # up this much, but momentum turning negative -> lean "sell" signal
SHARP_DROP_1D_PCT = -5
SHARP_DROP_5D_PCT = -10


def fetch_finnhub_recommendation_trend(symbol):
    """Most recent analyst buy/hold/sell consensus counts. Free Finnhub endpoint, updates monthly."""
    if not FINNHUB_API_KEY or "YOUR_" in FINNHUB_API_KEY:
        return None
    try:
        resp = requests.get(
            "https://finnhub.io/api/v1/stock/recommendation",
            params={"symbol": symbol, "token": FINNHUB_API_KEY},
            timeout=10,
        )
        if resp.status_code != 200:
            return None
        data = resp.json()
        return data[0] if data else None  # most recent period first
    except Exception as e:
        print(f"[recommendation trend error {symbol}] {e}")
        return None


def compute_holding_action(current_stats, price_paid, recommendation_trend):
    """
    Returns (action, reason_text). action is one of "Sell", "Watch", "Hold".
    Simple, explainable threshold rules -- not a prediction, just flags for
    you to look closer at. Always treat as a prompt to review, not an order.
    """
    bearish, bullish, reasons = 0, 0, []

    pct_gain = None
    if price_paid:
        pct_gain = round((current_stats["price"] - price_paid) / price_paid * 100, 2)
        if pct_gain <= STOP_LOSS_PCT:
            bearish += 1
            reasons.append(f"down {pct_gain}% from your purchase price")
        elif pct_gain >= TAKE_PROFIT_FADE_PCT and current_stats["chg_1d_pct"] < 0:
            bearish += 1
            reasons.append(f"up {pct_gain}% overall but today's momentum has turned negative")
        elif pct_gain > 0:
            bullish += 1

    if current_stats["chg_1d_pct"] <= SHARP_DROP_1D_PCT:
        bearish += 1
        reasons.append(f"sharp {current_stats['chg_1d_pct']}% drop today")
    if current_stats["chg_5d_pct"] <= SHARP_DROP_5D_PCT:
        bearish += 1
        reasons.append(f"{current_stats['chg_5d_pct']}% decline over the last 5 days")

    if recommendation_trend:
        sell_side = recommendation_trend.get("sell", 0) + recommendation_trend.get("strongSell", 0)
        buy_side = recommendation_trend.get("buy", 0) + recommendation_trend.get("strongBuy", 0)
        if sell_side > buy_side and sell_side > 0:
            bearish += 1
            reasons.append("analyst consensus leans Sell/Underweight")
        elif buy_side > sell_side:
            bullish += 1
            reasons.append("analyst consensus leans Buy")

    if bearish >= 2:
        action = "Sell"
    elif bearish == 1 and bearish >= bullish:
        action = "Watch"
    else:
        action = "Hold"

    reason_text = "; ".join(reasons) if reasons else "no strong signal either way"
    if pct_gain is not None:
        reason_text = f"{pct_gain:+.2f}% since purchase -- " + reason_text
    return action, reason_text


# ============================================================================
# PURCHASE LOG (one local JSON file PER ACCOUNT -- "log a purchase" tab)
# ============================================================================

def _purchase_log_path(username):
    safe_name = re.sub(r'[^A-Za-z0-9_-]', '_', username)
    return os.path.join(get_base_dir(), f"purchase_log_{safe_name}.json")


def load_purchase_log(username):
    path = _purchase_log_path(username)
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r") as f:
            return json.load(f)
    except Exception as e:
        print(f"[purchase log read error] {e}")
        return []


def save_purchase_entry(username, symbol, amount_text, time_text, price_paid=None):
    log = load_purchase_log(username)
    log.append({
        "symbol": symbol,
        "amount": amount_text,
        "price_paid": price_paid,  # float per-share price, or None if not provided
        "time": time_text,
        "logged_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    })
    try:
        with open(_purchase_log_path(username), "w") as f:
            json.dump(log, f, indent=2)
        return True
    except Exception as e:
        print(f"[purchase log save error] {e}")
        return False


def held_symbols_for_user(username):
    """Unique set of tickers this user has ever logged a purchase for."""
    return sorted({e["symbol"] for e in load_purchase_log(username)})


def summarize_holdings(username):
    """One summary row per symbol: number of buys, average price paid (if any were given),
    and the most recent amount/time logged."""
    by_symbol = {}
    for e in load_purchase_log(username):
        by_symbol.setdefault(e["symbol"], []).append(e)
    summaries = []
    for symbol, entries in by_symbol.items():
        priced = [e["price_paid"] for e in entries if e.get("price_paid")]
        avg_price_paid = round(sum(priced) / len(priced), 4) if priced else None
        latest = max(entries, key=lambda e: e["logged_at"])
        summaries.append({
            "symbol": symbol, "num_purchases": len(entries), "avg_price_paid": avg_price_paid,
            "latest_amount": latest["amount"], "latest_time": latest["time"],
        })
    return summaries


# ============================================================================
# MONEY POOLS + "BROOK THE BROKER" (one local JSON file PER ACCOUNT)
# --------------------------------------------------------------------------
# A "money pool" is just a named cash balance the user creates, tagged as
# either "paper" (fully simulated play money) or "real" (a manual tracking
# ledger for money that actually exists elsewhere). IMPORTANT: this app has
# no brokerage integration of any kind -- "real" pools never move real money
# or place real trades on their own. They just let the user track a real
# investing decision the same way the paper pools do.
#
# Brook is an extremely simple rules-based auto-invest toggle: when it's ON
# for a pool, any uninvested cash sitting in that pool gets split evenly
# between the top 2 stocks currently on the screener's ranked list that do
# NOT have a negative AI score. That's it -- no other strategy.
# ============================================================================

DEFAULT_PAPER_POOL_SEED = 500.0  # "you start off with 500 paperbucks"


def _pools_path(username):
    safe_name = re.sub(r'[^A-Za-z0-9_-]', '_', username)
    return os.path.join(get_base_dir(), f"pools_{safe_name}.json")


def load_pools(username):
    path = _pools_path(username)
    if not os.path.exists(path):
        return {"pools": [], "next_id": 1}
    try:
        with open(path, "r") as f:
            data = json.load(f)
        data.setdefault("pools", [])
        data.setdefault("next_id", 1)
        return data
    except Exception as e:
        print(f"[pools read error] {e}")
        return {"pools": [], "next_id": 1}


def _atomic_write_json(path, data):
    """Write-to-temp-then-rename so a reader (the desktop app, or the worker,
    whichever isn't the writer right now) never sees a half-written file. Once
    brook_worker.py can write these same pool files independently of the app,
    that's a real possibility, not just theoretical."""
    tmp_path = path + f".tmp-{os.getpid()}"
    with open(tmp_path, "w") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp_path, path)  # atomic on POSIX and Windows


def save_pools(username, data):
    try:
        _atomic_write_json(_pools_path(username), data)
        return True
    except Exception as e:
        print(f"[pools save error] {e}")
        return False


def find_pool(data, pool_id):
    for p in data["pools"]:
        if p["id"] == pool_id:
            return p
    return None


def create_pool(username, name, kind, starting_amount):
    """kind: 'paper' or 'real'. Returns (success, message)."""
    name = (name or "").strip()
    if not name:
        return False, "Pool name is required."
    if kind not in ("paper", "real"):
        return False, "Pool type must be paper or real."
    try:
        starting_amount = float(str(starting_amount).replace("$", "").replace(",", ""))
    except (TypeError, ValueError):
        return False, "Starting amount must be a number."
    if starting_amount < 0:
        return False, "Starting amount can't be negative."

    data = load_pools(username)
    if any(p["name"].lower() == name.lower() for p in data["pools"]):
        return False, "A pool with that name already exists."

    pool = {
        "id": data["next_id"],
        "name": name,
        "kind": kind,
        "cash": round(starting_amount, 2),
        "brook_enabled": False,
        "alpaca_linked": False,  # only meaningful for kind="real" -- see ALPACA section below
        "brook_state": None,     # {"symbols": [...], "checked_at": "..."} -- Brook's daily rebalance memory
        "holdings": {},   # symbol -> {"shares": float, "avg_price": float, "name": str}
        "history": [],
        "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    }
    data["pools"].append(pool)
    data["next_id"] += 1
    if not save_pools(username, data):
        return False, "Failed to save -- see console for details."
    return True, f"Pool '{name}' created with ${pool['cash']:,.2f}."


def delete_pool(username, pool_id):
    data = load_pools(username)
    pool = find_pool(data, pool_id)
    if not pool:
        return False, "Pool not found."
    data["pools"] = [p for p in data["pools"] if p["id"] != pool_id]
    if not save_pools(username, data):
        return False, "Failed to save -- see console for details."
    return True, f"Deleted pool '{pool['name']}'."


def deposit_to_pool(username, pool_id, amount, note="deposit"):
    try:
        amount = float(str(amount).replace("$", "").replace(",", ""))
    except (TypeError, ValueError):
        return False, "Amount must be a number."
    if amount <= 0:
        return False, "Amount must be greater than zero."
    data = load_pools(username)
    pool = find_pool(data, pool_id)
    if not pool:
        return False, "Pool not found."
    pool["cash"] = round(pool["cash"] + amount, 2)
    pool["history"].append({
        "type": note, "amount": round(amount, 2),
        "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    })
    if not save_pools(username, data):
        return False, "Failed to save -- see console for details."
    return True, f"Added ${amount:,.2f} to '{pool['name']}'."


def _buy_in_pool(pool, symbol, name, dollar_amount, price, actor="you"):
    """Mutates pool in place: deducts cash, adds/updates the holding. Caller saves."""
    if price is None or price <= 0:
        return False, f"No valid current price available for {symbol}."
    dollar_amount = round(min(dollar_amount, pool["cash"]), 2)
    if dollar_amount <= 0:
        return False, "Not enough cash in this pool to invest."
    shares = round(dollar_amount / price, 6)
    if shares <= 0:
        return False, "That amount is too small to buy any shares at the current price."
    pool["cash"] = round(pool["cash"] - dollar_amount, 2)
    holding = pool["holdings"].setdefault(symbol, {"shares": 0.0, "avg_price": price, "name": name})
    total_cost = holding["shares"] * holding["avg_price"] + shares * price
    holding["shares"] = round(holding["shares"] + shares, 6)
    holding["avg_price"] = round(total_cost / holding["shares"], 4) if holding["shares"] else price
    holding["name"] = name
    pool["history"].append({
        "type": "brook_buy" if actor == "brook" else "buy",
        "symbol": symbol, "shares": shares, "price": price, "amount": dollar_amount,
        "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    })
    return True, f"Bought {shares:g} shares of {symbol} @ ${price:,.2f} (${dollar_amount:,.2f})."


def invest_in_pool(username, pool_id, symbol, name, dollar_amount, price):
    try:
        dollar_amount = float(str(dollar_amount).replace("$", "").replace(",", ""))
    except (TypeError, ValueError):
        return False, "Amount must be a number."
    if dollar_amount <= 0:
        return False, "Amount must be greater than zero."
    data = load_pools(username)
    pool = find_pool(data, pool_id)
    if not pool:
        return False, "Pool not found."
    ok, msg = _buy_in_pool(pool, symbol, name, dollar_amount, price, actor="you")
    if ok and not save_pools(username, data):
        return False, "Failed to save -- see console for details."
    return ok, msg


def set_pool_brook(username, pool_id, enabled):
    data = load_pools(username)
    pool = find_pool(data, pool_id)
    if not pool:
        return False
    pool["brook_enabled"] = bool(enabled)
    return save_pools(username, data)


def set_pool_alpaca_link(username, pool_id, linked):
    data = load_pools(username)
    pool = find_pool(data, pool_id)
    if not pool:
        return False
    pool["alpaca_linked"] = bool(linked)
    return save_pools(username, data)


def _sell_in_pool(pool, symbol, price, actor="you"):
    """Mutates pool in place: sells the ENTIRE holding in `symbol`, adds proceeds to
    cash. Caller saves. Falls back to average cost if no live price is available."""
    holding = pool["holdings"].get(symbol)
    if not holding or holding["shares"] <= 0:
        return False, f"No holding in {symbol} to sell."
    sale_price = price if (price and price > 0) else holding["avg_price"]
    shares_sold = holding["shares"]
    proceeds = round(shares_sold * sale_price, 2)
    pool["cash"] = round(pool["cash"] + proceeds, 2)
    del pool["holdings"][symbol]
    pool["history"].append({
        "type": "brook_sell" if actor == "brook" else "sell",
        "symbol": symbol, "shares": shares_sold, "price": sale_price, "amount": proceeds,
        "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    })
    return True, f"Sold {shares_sold:g} shares of {symbol} @ ${sale_price:,.2f} (${proceeds:,.2f})."


def brook_pick_candidates(ranked_data):
    """Top 2 stocks on the current ranked list that do NOT have a negative AI score,
    in the list's existing (best-score-first) order."""
    return [r for r in (ranked_data or []) if r.get("ai_score", 0.0) >= 0][:2]


BROOK_REBALANCE_HOURS = 24  # how often Brook checks whether the top-2 picks have changed


def run_brook_for_pool(username, pool_id, ranked_data, price_lookup=None):
    """Brook's strategy, run once per scan cycle (or on demand -- including from
    brook_worker.py while the desktop app itself is closed):

    1. Daily reset (at most once every BROOK_REBALANCE_HOURS, and always on the
       very first run for a pool): sell EVERYTHING Brook is currently holding in
       this pool -- not just whichever pick fell out of the top-2 -- then lock in
       today's fresh top-2 (non-negative AI score) picks as the new target.
    2. Deploy step, every cycle: split whatever cash is currently idle (freed by
       the sale above, freshly deposited, or simply never invested yet) evenly
       across the currently-locked top-2 target -- NOT whatever the instantaneous
       leaderboard says this exact minute, so Brook doesn't chase a pick that
       flickers in and out of the top-2 between scans; that target only changes
       at the next daily reset.

    For pools linked to Alpaca (kind="real" + alpaca_linked=True), buys/sells are
    placed as real orders against that Alpaca account (paper or live, per the
    saved Brokerage Settings) instead of being computed locally.
    """
    candidates = brook_pick_candidates(ranked_data)
    if not candidates:
        return False, "Brook is waiting -- no qualifying stocks (non-negative AI score) right now."
    candidates_by_symbol = {r["symbol"]: r for r in ranked_data}
    price_lookup = price_lookup or {r["symbol"]: r["stats"]["price"] for r in ranked_data}
    current_symbols = sorted(r["symbol"] for r in candidates)

    data = load_pools(username)
    pool = find_pool(data, pool_id)
    if not pool:
        return False, "Pool not found."
    if not pool.get("brook_enabled"):
        return False, "Brook is off for this pool."

    use_alpaca = bool(pool.get("alpaca_linked"))
    broker_cfg = load_broker_config(username) if use_alpaca else None
    if use_alpaca and not (broker_cfg.get("api_key") and broker_cfg.get("api_secret")):
        return False, "Brook needs an Alpaca API key saved in Brokerage Settings before it can trade this pool."

    messages = []
    now = datetime.now()
    state = pool.get("brook_state") or {}

    due_for_reset = True  # no prior state at all (first run ever) -> always due
    if state.get("checked_at"):
        try:
            checked_at = datetime.strptime(state["checked_at"], "%Y-%m-%d %H:%M:%S")
            due_for_reset = (now - checked_at).total_seconds() / 3600.0 >= BROOK_REBALANCE_HOURS
        except ValueError:
            due_for_reset = True  # malformed timestamp -> treat as due

    if due_for_reset:
        if use_alpaca:
            held_symbols = [p["symbol"] for p in (alpaca_get_positions(broker_cfg) or [])]
        else:
            held_symbols = list(pool["holdings"].keys())
        for sym in held_symbols:
            if use_alpaca:
                ok, msg = alpaca_close_position(broker_cfg, sym)
            else:
                ok, msg = _sell_in_pool(pool, sym, price_lookup.get(sym), actor="brook")
            messages.append(msg)
        pool["brook_state"] = {"symbols": current_symbols, "checked_at": now.strftime("%Y-%m-%d %H:%M:%S")}
        target_symbols = current_symbols
    else:
        target_symbols = state.get("symbols") or current_symbols
        if not state.get("symbols"):
            pool["brook_state"] = {"symbols": current_symbols, "checked_at": now.strftime("%Y-%m-%d %H:%M:%S")}

    # Resolve each target symbol to a (name, price) -- prefer live ranked_data
    # (has both), fall back to the pool's own holding record + price_lookup for
    # a symbol that's temporarily off today's shortlist but still Brook's target.
    buy_targets = []
    for sym in target_symbols:
        if sym in candidates_by_symbol:
            r = candidates_by_symbol[sym]
            buy_targets.append((sym, r["name"], r["stats"]["price"]))
        else:
            price = price_lookup.get(sym)
            name = pool["holdings"].get(sym, {}).get("name", sym)
            if price and price > 0:
                buy_targets.append((sym, name, price))

    if use_alpaca:
        account = alpaca_get_account(broker_cfg)
        cash = float(account["cash"]) if account else 0.0
    else:
        cash = pool["cash"]

    if cash >= 1.0 and buy_targets:
        share = round(cash / len(buy_targets), 2)
        for sym, name, price in buy_targets:
            amt = min(share, cash)
            if use_alpaca:
                ok, msg = alpaca_place_notional_order(broker_cfg, sym, amt, side="buy")
            else:
                ok, msg = _buy_in_pool(pool, sym, name, amt, price, actor="brook")
            messages.append(msg)
    elif not messages:
        messages.append("Nothing new to invest -- cash is already fully deployed.")

    if not save_pools(username, data):
        return False, "Failed to save -- see console for details."
    return True, "Brook: " + " | ".join(m for m in messages if m)


def pool_holdings_value(pool, price_lookup):
    """price_lookup: dict symbol -> current price (float). Falls back to avg cost
    for symbols currently outside the live screener data (e.g. off the shortlist)."""
    total = 0.0
    for symbol, h in pool["holdings"].items():
        price = price_lookup.get(symbol, h["avg_price"])
        total += h["shares"] * price
    return round(total, 2)


# ============================================================================
# ALPACA BROKERAGE INTEGRATION (optional -- free paper AND real trading API)
# --------------------------------------------------------------------------
# Alpaca (alpaca.markets) offers a free, no-cost API for both PAPER trading
# (fake money, real market data -- great for testing) and LIVE trading (real
# money, real trades, subject to Alpaca's own account approval/KYC and terms).
# Same API either way -- only the base URL and the account behind the key
# differ. Nothing here works until an account pastes their own key into the
# Brokerage Settings dialog (see ScreenerApp._open_broker_settings) -- there
# are never any built-in/shared credentials.
# ============================================================================

def _broker_config_path(username):
    safe_name = re.sub(r'[^A-Za-z0-9_-]', '_', username)
    return os.path.join(get_base_dir(), f"broker_config_{safe_name}.json")


def load_broker_config(username):
    default = {"api_key": "", "api_secret": "", "paper": True, "live_confirmed": False}
    path = _broker_config_path(username)
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r") as f:
            cfg = json.load(f)
        for k, v in default.items():
            cfg.setdefault(k, v)
        return cfg
    except Exception as e:
        print(f"[broker config read error] {e}")
        return default


def save_broker_config(username, cfg):
    try:
        with open(_broker_config_path(username), "w") as f:
            json.dump(cfg, f, indent=2)
        return True
    except Exception as e:
        print(f"[broker config save error] {e}")
        return False


def alpaca_base_url(cfg):
    return "https://paper-api.alpaca.markets" if cfg.get("paper", True) else "https://api.alpaca.markets"


def alpaca_headers(cfg):
    return {"APCA-API-KEY-ID": cfg.get("api_key", ""), "APCA-API-SECRET-KEY": cfg.get("api_secret", "")}


def alpaca_request(cfg, method, path, json_body=None):
    url = alpaca_base_url(cfg) + path
    try:
        resp = requests.request(method, url, headers=alpaca_headers(cfg), json=json_body, timeout=10)
    except Exception as e:
        return None, f"Could not reach Alpaca: {e}"
    if resp.status_code >= 400:
        try:
            detail = resp.json().get("message", resp.text)
        except Exception:
            detail = resp.text
        return None, f"Alpaca error ({resp.status_code}): {detail}"
    try:
        return (resp.json() if resp.text else {}), None
    except Exception:
        return {}, None


def alpaca_test_connection(cfg):
    data, err = alpaca_request(cfg, "GET", "/v2/account")
    if err:
        return False, err
    mode = "PAPER" if cfg.get("paper", True) else "LIVE"
    return True, (
        f"Connected ({mode}). Cash: ${float(data.get('cash', 0)):,.2f}   "
        f"Buying power: ${float(data.get('buying_power', 0)):,.2f}"
    )


def alpaca_get_account(cfg):
    data, err = alpaca_request(cfg, "GET", "/v2/account")
    return data if not err else None


def alpaca_get_positions(cfg):
    data, err = alpaca_request(cfg, "GET", "/v2/positions")
    return data if not err else []


def alpaca_place_notional_order(cfg, symbol, notional, side="buy"):
    if notional < 1.0:
        return False, f"{side.capitalize()} order for {symbol} skipped -- amount too small."
    body = {"symbol": symbol, "notional": f"{notional:.2f}", "side": side, "type": "market", "time_in_force": "day"}
    data, err = alpaca_request(cfg, "POST", "/v2/orders", json_body=body)
    if err:
        return False, f"{side.capitalize()} order for {symbol} failed: {err}"
    return True, f"{side.capitalize()} order placed for {symbol}: ${notional:,.2f} notional (id {data.get('id', '?')})."


def alpaca_close_position(cfg, symbol):
    data, err = alpaca_request(cfg, "DELETE", f"/v2/positions/{symbol}")
    if err:
        return False, f"Closing {symbol} failed: {err}"
    return True, f"Closed entire {symbol} position."


# ============================================================================
# STARLING BANK INTEGRATION (optional -- funds a real, Alpaca-linked pool)
# --------------------------------------------------------------------------
# Starling is a bank, not a broker -- it can hold and move your money, but it
# can't buy stocks. So "funding a pool from Starling" means: send a real
# payment from your Starling account to the bank account behind your Alpaca
# account's ACH funding link, and that lands as Alpaca cash the app already
# reads for linked pools. There is deliberately no card-number field anywhere
# in this section: card numbers only work for a MERCHANT to charge you at
# checkout, there's no Starling endpoint for a third-party app to pull money
# on demand that way, and collecting/storing raw card numbers is a real
# security liability this app has no business taking on. Instead, this uses
# Starling's own OAuth login (like "Sign in with Google") -- you authorize the
# app once, it gets a token, it never sees your card or password.
#
# Setup the user has to do once, outside this app, that no code here can do
# for them: register a free app at https://developer.starlingbank.com, which
# gives a Client ID + Secret to paste into Brokerage Settings below. Sending
# real payments requires Starling's "pay-local:create" scope, which Starling
# grants on request for OAuth apps (not for simple personal access tokens) --
# worth knowing before assuming this "just works" the moment you sign up.
#
# NOTE ON API SHAPES: the endpoints/payloads below follow Starling's public
# v2 API as documented at https://developer.starlingbank.com/docs -- as with
# any bank API, double-check against their current docs / Sandbox before
# sending real money, since banks do version these endpoints over time.
# ============================================================================
STARLING_AUTH_URL = "https://oauth.starlingbank.com/authorize"
STARLING_TOKEN_URL = "https://oauth.starlingbank.com/oauth/access-token"
STARLING_API_BASE = "https://api.starlingbank.com/api/v2"
STARLING_REDIRECT_PORT = 8765
STARLING_REDIRECT_URI = f"http://localhost:{STARLING_REDIRECT_PORT}/callback"
STARLING_SCOPES = "account:read balance:read payees:read pay-local:create"


def _starling_config_path(username):
    safe_name = re.sub(r'[^A-Za-z0-9_-]', '_', username)
    return os.path.join(get_base_dir(), f"starling_config_{safe_name}.json")


def load_starling_config(username):
    default = {
        "client_id": "", "client_secret": "", "access_token": "", "refresh_token": "",
        "expires_at": 0,
        "dest_name": "", "dest_account_number": "", "dest_sort_code": "",  # where deposits go (Alpaca's ACH bank)
    }
    path = _starling_config_path(username)
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r") as f:
            cfg = json.load(f)
        for k, v in default.items():
            cfg.setdefault(k, v)
        return cfg
    except Exception as e:
        print(f"[starling config read error] {e}")
        return default


def save_starling_config(username, cfg):
    try:
        _atomic_write_json(_starling_config_path(username), cfg)
        return True
    except Exception as e:
        print(f"[starling config save error] {e}")
        return False


def starling_is_connected(username):
    cfg = load_starling_config(username)
    return bool(cfg.get("access_token") or cfg.get("refresh_token"))


def starling_connect(username, client_id, client_secret, timeout_seconds=120):
    """OAuth authorization-code flow: opens the user's browser to Starling's own
    login/consent page, runs a one-shot local server to catch the redirect
    (localhost only -- nothing external ever reaches it), then exchanges the
    code for tokens. Returns (ok, message)."""
    client_id = (client_id or "").strip()
    client_secret = (client_secret or "").strip()
    if not client_id or not client_secret:
        return False, "Starling Client ID and Client Secret are required."

    state = secrets.token_urlsafe(16)
    auth_url = (
        f"{STARLING_AUTH_URL}?client_id={urllib.parse.quote(client_id)}"
        f"&redirect_uri={urllib.parse.quote(STARLING_REDIRECT_URI)}"
        f"&response_type=code&scope={urllib.parse.quote(STARLING_SCOPES)}&state={state}"
    )

    caught = {}

    class _CallbackHandler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            caught["code"] = qs.get("code", [None])[0]
            caught["state"] = qs.get("state", [None])[0]
            caught["error"] = qs.get("error_description", qs.get("error", [None]))[0]
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.end_headers()
            self.wfile.write(b"<html><body><h3>Starling connected -- you can close this tab "
                              b"and go back to the app.</h3></body></html>")

        def log_message(self, fmt, *args):
            pass  # keep console clean -- this is a throwaway local server

    try:
        server = http.server.HTTPServer(("localhost", STARLING_REDIRECT_PORT), _CallbackHandler)
    except OSError as e:
        return False, f"Couldn't start the local callback listener on port {STARLING_REDIRECT_PORT}: {e}"
    server.timeout = timeout_seconds

    webbrowser.open(auth_url)
    server.handle_request()  # blocks for exactly one request, or times out
    server.server_close()

    if caught.get("error"):
        return False, f"Starling login was not completed: {caught['error']}"
    if not caught.get("code"):
        return False, "No response from Starling within the time limit -- try connecting again."
    if caught.get("state") != state:
        return False, "Starling login response failed a security check (state mismatch) -- try again."

    try:
        token_resp = requests.post(STARLING_TOKEN_URL, data={
            "grant_type": "authorization_code", "code": caught["code"],
            "client_id": client_id, "client_secret": client_secret,
            "redirect_uri": STARLING_REDIRECT_URI,
        }, timeout=15)
    except Exception as e:
        return False, f"Could not reach Starling to exchange the login code: {e}"
    if token_resp.status_code >= 400:
        return False, f"Starling token exchange failed ({token_resp.status_code}): {token_resp.text}"
    tok = token_resp.json()

    cfg = load_starling_config(username)
    cfg.update({
        "client_id": client_id, "client_secret": client_secret,
        "access_token": tok.get("access_token", ""), "refresh_token": tok.get("refresh_token", ""),
        "expires_at": time.time() + float(tok.get("expires_in", 3600)) - 60,
    })
    if not save_starling_config(username, cfg):
        return False, "Connected, but failed to save the token -- see console for details."
    return True, "Starling account connected."


def _starling_authed_config(username):
    """Returns a config dict with a fresh access token, refreshing it first if
    it's expired. Does not persist a refreshed token failure -- caller sees the
    stale token and gets a clear 401 back from Starling if refresh silently failed."""
    cfg = load_starling_config(username)
    if not cfg.get("access_token"):
        return cfg
    if time.time() < cfg.get("expires_at", 0):
        return cfg
    if not cfg.get("refresh_token"):
        return cfg
    try:
        resp = requests.post(STARLING_TOKEN_URL, data={
            "grant_type": "refresh_token", "refresh_token": cfg["refresh_token"],
            "client_id": cfg["client_id"], "client_secret": cfg["client_secret"],
        }, timeout=15)
        if resp.status_code < 400:
            tok = resp.json()
            cfg["access_token"] = tok.get("access_token", cfg["access_token"])
            cfg["refresh_token"] = tok.get("refresh_token", cfg["refresh_token"])
            cfg["expires_at"] = time.time() + float(tok.get("expires_in", 3600)) - 60
            save_starling_config(username, cfg)
    except Exception as e:
        print(f"[starling token refresh error] {e}")
    return cfg


def _starling_headers(cfg):
    return {"Authorization": f"Bearer {cfg.get('access_token', '')}", "Content-Type": "application/json"}


def starling_get_account(username):
    """Returns (account_uid, category_uid, error) for the user's primary
    Starling account -- both are needed for the balance and payment calls."""
    cfg = _starling_authed_config(username)
    if not cfg.get("access_token"):
        return None, None, "Not connected to Starling yet -- connect it in Brokerage Settings first."
    try:
        resp = requests.get(f"{STARLING_API_BASE}/accounts", headers=_starling_headers(cfg), timeout=10)
    except Exception as e:
        return None, None, f"Could not reach Starling: {e}"
    if resp.status_code >= 400:
        return None, None, f"Starling error ({resp.status_code}): {resp.text}"
    accounts = resp.json().get("accounts", [])
    if not accounts:
        return None, None, "No Starling accounts found on this login."
    acc = accounts[0]
    return acc["accountUid"], acc["defaultCategory"], None


def starling_get_balance(username):
    account_uid, _, err = starling_get_account(username)
    if err:
        return None, err
    cfg = _starling_authed_config(username)
    try:
        resp = requests.get(f"{STARLING_API_BASE}/accounts/{account_uid}/balance",
                             headers=_starling_headers(cfg), timeout=10)
    except Exception as e:
        return None, f"Could not reach Starling: {e}"
    if resp.status_code >= 400:
        return None, f"Starling error ({resp.status_code}): {resp.text}"
    bal = resp.json()
    return bal.get("effectiveBalance", {}).get("minorUnits", 0) / 100.0, None


def starling_send_payment(username, amount, reference="Pool funding"):
    """Sends a real UK Faster Payment from the user's Starling account to the
    saved destination (the bank behind their Alpaca ACH link), for the amount
    the user chose. Returns (ok, message). Amount is in GBP."""
    try:
        amount = float(amount)
    except (TypeError, ValueError):
        return False, "Amount must be a number."
    if amount <= 0:
        return False, "Amount must be greater than zero."

    cfg = _starling_authed_config(username)
    dest_name = cfg.get("dest_name", "").strip()
    dest_number = cfg.get("dest_account_number", "").strip()
    dest_sort = cfg.get("dest_sort_code", "").strip()
    if not (dest_name and dest_number and dest_sort):
        return False, "Save a destination account (name, account number, sort code) in Brokerage Settings first."

    account_uid, category_uid, err = starling_get_account(username)
    if err:
        return False, err

    # Register (or re-confirm) the destination as a payee -- Starling requires
    # payments to go through a saved payee rather than raw bank details inline.
    payee_body = {"payees": [{
        "name": dest_name, "payeeType": "BUSINESS",
        "accounts": [{"type": "UK_ACCOUNT_AND_SORT_CODE",
                      "accountIdentifier": dest_number, "bankIdentifier": dest_sort}],
    }]}
    try:
        payee_resp = requests.put(f"{STARLING_API_BASE}/payees", headers=_starling_headers(cfg),
                                   json=payee_body, timeout=15)
    except Exception as e:
        return False, f"Could not reach Starling to register the destination: {e}"
    if payee_resp.status_code >= 400:
        return False, f"Could not register destination account ({payee_resp.status_code}): {payee_resp.text}"
    payee_data = payee_resp.json()
    payees = payee_data.get("payees") or []
    if not payees or not payees[0].get("accounts"):
        return False, "Starling didn't return a payee reference to pay -- try again."
    payee_uid = payees[0]["payeeUid"]
    payee_account_uid = payees[0]["accounts"][0]["payeeAccountUid"]

    payment_body = {
        "amount": {"currency": "GBP", "minorUnits": int(round(amount * 100))},
        "reference": reference[:18],
        "payeeUid": payee_uid,
        "payeeAccountUid": payee_account_uid,
    }
    try:
        pay_resp = requests.put(
            f"{STARLING_API_BASE}/payments/local/account/{account_uid}/category/{category_uid}",
            headers=_starling_headers(cfg), json=payment_body, timeout=15,
        )
    except Exception as e:
        return False, f"Could not reach Starling to send the payment: {e}"
    if pay_resp.status_code >= 400:
        return False, f"Payment failed ({pay_resp.status_code}): {pay_resp.text}"
    return True, f"Sent £{amount:,.2f} from Starling to {dest_name}. Bank transfers aren't instant -- it may take a bit to land as Alpaca cash."


# ============================================================================
# LOGIN / CREATE ACCOUNT WINDOW (runs before the main app window)
# ============================================================================

class LoginWindow:
    def __init__(self):
        ensure_default_account()
        self.logged_in_username = None
        self.root = tk.Tk()
        self.root.title("Login — Tandon Corp Investment Database")
        self.root.geometry("380x290")

        # Logo images must be created against THIS root's Tk interpreter --
        # PhotoImage instances can't be shared across separate tk.Tk() roots.
        self._logo_full = tk.PhotoImage(data=LOGO_PNG_BASE64)
        self._logo_icon = self._logo_full.subsample(6, 6)
        self._logo_banner = self._logo_full.subsample(10, 10)
        self.root.iconphoto(True, self._logo_icon)

        self._build_ui()

    def _build_ui(self):
        banner = tk.Frame(self.root)
        banner.pack(pady=(20, 12))
        tk.Label(banner, image=self._logo_banner).pack(side="left")
        tk.Label(
            banner, text="ANDON CORP\nINVESTMENT DATABASE",
            font=("Times New Roman", 16, "bold"), fg="green", justify="left",
        ).pack(side="left")

        form = tk.Frame(self.root)
        form.pack(pady=6)
        tk.Label(form, text="Username:").grid(row=0, column=0, sticky="e", padx=6, pady=4)
        self.username_entry = tk.Entry(form)
        self.username_entry.grid(row=0, column=1, pady=4)
        tk.Label(form, text="Password:").grid(row=1, column=0, sticky="e", padx=6, pady=4)
        self.password_entry = tk.Entry(form, show="*")
        self.password_entry.grid(row=1, column=1, pady=4)

        self.error_label = tk.Label(self.root, text="", fg="red", font=("Segoe UI", 9))
        self.error_label.pack(pady=(4, 0))

        btn_frame = tk.Frame(self.root)
        btn_frame.pack(pady=12)
        tk.Button(btn_frame, text="Login", width=12, command=self._try_login).grid(row=0, column=0, padx=6)
        tk.Button(btn_frame, text="Create Account", width=14, command=self._open_create_account).grid(
            row=0, column=1, padx=6
        )

        self.root.bind("<Return>", lambda e: self._try_login())
        self.username_entry.focus_set()

    def _try_login(self):
        username = self.username_entry.get().strip()
        password = self.password_entry.get()
        if not verify_login(username, password):
            self.error_label.config(text="Invalid username or password.")
            return
        eligible, reason = check_login_eligibility(username)
        if not eligible:
            self.error_label.config(text=reason)
            return
        self.logged_in_username = username
        self.root.destroy()

    def _open_create_account(self):
        popup = tk.Toplevel(self.root)
        popup.title("Create Account")
        popup.geometry("360x290")

        tk.Label(popup, text="Create a new account", font=("Segoe UI", 11, "bold")).pack(pady=(14, 10))
        form = tk.Frame(popup)
        form.pack()
        tk.Label(form, text="Username:").grid(row=0, column=0, sticky="e", padx=6, pady=4)
        new_username = tk.Entry(form)
        new_username.grid(row=0, column=1, pady=4)
        tk.Label(form, text="Password:").grid(row=1, column=0, sticky="e", padx=6, pady=4)
        new_password = tk.Entry(form, show="*")
        new_password.grid(row=1, column=1, pady=4)
        tk.Label(form, text="Confirm Password:").grid(row=2, column=0, sticky="e", padx=6, pady=4)
        confirm_password = tk.Entry(form, show="*")
        confirm_password.grid(row=2, column=1, pady=4)
        tk.Label(form, text="Org Key:").grid(row=3, column=0, sticky="e", padx=6, pady=4)
        org_key_entry = tk.Entry(form)
        org_key_entry.grid(row=3, column=1, pady=4)

        tk.Label(
            popup, text="An org key is required -- get one from Ayaan or your org's admin.",
            fg="#555555", font=("Segoe UI", 8, "italic"), wraplength=320,
        ).pack(pady=(2, 0))

        msg_label = tk.Label(popup, text="", font=("Segoe UI", 9), wraplength=320)
        msg_label.pack(pady=6)

        def do_create():
            u = new_username.get().strip()
            p = new_password.get()
            c = confirm_password.get()
            k = org_key_entry.get().strip()
            if p != c:
                msg_label.config(text="Passwords do not match.", fg="red")
                return
            ok, message = create_account(u, p, k)
            msg_label.config(text=message, fg="green" if ok else "red")
            if ok:
                popup.after(1200, popup.destroy)

        tk.Button(popup, text="Create Account", command=do_create).pack(pady=8)

    def run(self):
        self.root.mainloop()
        return self.logged_in_username


# ============================================================================
# GUI
# ============================================================================

def compute_ranked_scan():
    """Core scan logic, pulled out of ScreenerApp so it has NO GUI/Tkinter
    dependency: reload the universe if due, bulk price fetch, momentum
    shortlist, deep enrichment (news/social/SEC/weather) + AI scoring.

    This is what both the desktop app (ScreenerApp._run_full_scan) and
    brook_worker.py call -- one scan implementation, two callers, so Brook can
    keep scanning and trading on the same logic while the desktop app is
    closed.

    Returns a dict: top20, results_by_symbol, quality_price_data, price_data,
    weather_adjustments, world_times, benchmarks, universe_size, quality_size.
    """
    global _CYCLE_COUNT
    if not _UNIVERSE or _CYCLE_COUNT % RELOAD_UNIVERSE_EVERY_N_CYCLES == 0:
        load_full_stock_universe()

    all_symbols = list(_UNIVERSE.keys())
    price_data = fetch_price_data_bulk(all_symbols)

    quality_price_data = filter_quality_candidates(price_data)
    ranked_candidates = sorted(quality_price_data.items(), key=lambda kv: basic_momentum_score(kv[1]), reverse=True)
    shortlist = [(sym, _UNIVERSE.get(sym, sym), stats) for sym, stats in ranked_candidates[:SHORTLIST_SIZE]]

    weather_adjustments = fetch_weather_adjustments()
    world_times = fetch_world_times()
    benchmarks = fetch_benchmarks()
    refresh_newsapi_cache_if_due()

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_PARALLEL_TICKERS) as executor:
        futures = {
            executor.submit(process_single_ticker, symbol, name, stats, weather_adjustments): symbol
            for symbol, name, stats in shortlist
        }
        for future in concurrent.futures.as_completed(futures):
            symbol = futures[future]
            try:
                results.append(future.result())
            except Exception as e:
                print(f"[ticker processing error {symbol}] {e}")

    # AI quick-score pass, modest concurrency to respect free-tier rate limits
    with concurrent.futures.ThreadPoolExecutor(max_workers=AI_QUICK_MAX_PARALLEL) as executor:
        futures = {
            executor.submit(ai_quick_score, r["symbol"], r["name"], r["stats"],
                             r["processed_headlines"], r["sec_data"], r["social_ratio"]): r
            for r in results
        }
        for future in concurrent.futures.as_completed(futures):
            r = futures[future]
            try:
                ai_score, ai_reason = future.result()
            except Exception as e:
                ai_score, ai_reason = 0.0, f"AI analysis failed: {e}"
            r["ai_score"] = ai_score
            r["ai_reason"] = ai_reason
            r["score"] = round(r["score"] + ai_score * 2.0, 2)
            r["context"] += f"\nAI quick-analysis score: {ai_score} -- {ai_reason}"

    results.sort(key=lambda r: r["score"], reverse=True)
    top20 = results[:20]
    results_by_symbol = {r["symbol"]: r for r in results}
    _CYCLE_COUNT += 1

    return {
        "top20": top20,
        "results_by_symbol": results_by_symbol,
        "quality_price_data": quality_price_data,
        "price_data": price_data,
        "weather_adjustments": weather_adjustments,
        "world_times": world_times,
        "benchmarks": benchmarks,
        "universe_size": len(_UNIVERSE),
        "quality_size": len(quality_price_data),
    }


class ScreenerApp:
    def __init__(self, root, username):
        self.root = root
        self.username = username
        self.root.title(f"Stock Momentum, News & AI Screener — logged in as {username}")
        self.root.geometry("1080x820")

        self.ranked_data = []
        self.raw_by_symbol = {}
        self.holdings_rows = []

        self._logo_full = tk.PhotoImage(data=LOGO_PNG_BASE64)
        self._logo_icon = self._logo_full.subsample(6, 6)
        self._logo_banner = self._logo_full.subsample(11, 11)
        self.root.iconphoto(True, self._logo_icon)

        self._build_ui()
        load_ticker_to_cik_map()
        self._start_background_updates()

    def _build_ui(self):
        PAD_X = 14
        self.root.configure(bg="#f4f6f5")

        # ---- Banner ----
        banner_frame = tk.Frame(self.root, bg="#f4f6f5")
        banner_frame.pack(fill="x", padx=PAD_X, pady=(12, 4))
        banner_inner = tk.Frame(banner_frame, bg="#f4f6f5")
        banner_inner.pack(anchor="center")
        tk.Label(banner_inner, image=self._logo_banner, bg="#f4f6f5").pack(side="left")
        tk.Label(
            banner_inner, text="ANDON CORP INVESTMENT DATABASE",
            font=("Times New Roman", 18, "bold"), fg="#146c2e", bg="#f4f6f5",
        ).pack(side="left")

        self.status_label = tk.Label(self.root, text="Loading...", font=("Segoe UI", 9), fg="#333333", bg="#f4f6f5")
        self.status_label.pack(fill="x", padx=PAD_X, pady=(0, 4))

        ttk.Separator(self.root, orient="horizontal").pack(fill="x", padx=PAD_X)

        # ---- Tabs ----
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=PAD_X, pady=(8, 4))

        screener_tab = tk.Frame(self.notebook, bg="#ffffff")
        holdings_tab = tk.Frame(self.notebook, bg="#ffffff")
        pools_tab = tk.Frame(self.notebook, bg="#ffffff")
        self.notebook.add(screener_tab, text="  Screener  ")
        self.notebook.add(holdings_tab, text="  Your Holdings  ")
        self.notebook.add(pools_tab, text="  Money Pools  ")

        self._build_screener_tab(screener_tab, PAD_X)
        self._build_holdings_tab(holdings_tab, PAD_X)
        self._build_pools_tab(pools_tab, PAD_X)

        # ---- Toolbar (always visible, outside the tabs) ----
        ttk.Separator(self.root, orient="horizontal").pack(fill="x", padx=PAD_X)
        bottom_frame = tk.Frame(self.root, pady=8, bg="#f4f6f5")
        bottom_frame.pack(fill="x", padx=PAD_X)
        tk.Button(bottom_frame, text="Refresh Now", command=self.manual_refresh, width=14).pack(side="left")
        if get_account_role(self.username) == "owner":
            tk.Button(bottom_frame, text="Admin Panel", command=self._open_admin_panel, width=14).pack(
                side="left", padx=8
            )

    def _build_screener_tab(self, parent, PAD_X):
        tk.Label(
            parent, text="Top 20 Stocks — Momentum / News / Social / SEC / AI Screener",
            font=("Segoe UI", 13, "bold"), bg="#ffffff",
        ).pack(anchor="w", padx=PAD_X, pady=(10, 2))

        tk.Label(
            parent,
            text="Heuristic research tool, not financial advice. Double-click any row for details, "
                 "AI reasoning, or to log a purchase.",
            fg="#777777", font=("Segoe UI", 8, "italic"), bg="#ffffff",
        ).pack(fill="x", padx=PAD_X, pady=(0, 6))

        # ---- Market context: world clock + benchmarks, side by side to save space ----
        context_frame = tk.Frame(parent, bg="#ffffff")
        context_frame.pack(fill="x", padx=PAD_X, pady=(0, 6))

        self.world_time_label = tk.Label(
            context_frame, text="World times: —", font=("Segoe UI", 8), fg="#555555", bg="#ffffff"
        )
        self.world_time_label.pack(anchor="w")

        benchmarks_columns = ("name", "price", "chg1d", "chg5d")
        self.benchmarks_tree = ttk.Treeview(context_frame, columns=benchmarks_columns, show="headings", height=5)
        for col, label, width in (("name", "Benchmark", 260), ("price", "Value", 90),
                                   ("chg1d", "1D %", 70), ("chg5d", "5D %", 70)):
            self.benchmarks_tree.heading(col, text=label)
            self.benchmarks_tree.column(col, width=width, anchor="w" if col == "name" else "center")
        self.benchmarks_tree.pack(fill="x", pady=(4, 0))

        ttk.Separator(parent, orient="horizontal").pack(fill="x", padx=PAD_X, pady=(6, 0))

        # ---- Main stock list ----
        columns = ("rank", "ticker", "name", "price", "chg1d", "chg5d", "volx", "social", "sec", "ai", "score")
        self.tree = ttk.Treeview(parent, columns=columns, show="headings", height=16)
        headers = {"rank": "#", "ticker": "Ticker", "name": "Company", "price": "Price",
                   "chg1d": "1D %", "chg5d": "5D %", "volx": "Vol x Avg",
                   "social": "Social", "sec": "SEC", "ai": "AI", "score": "Score"}
        widths = {"rank": 30, "ticker": 60, "name": 170, "price": 70, "chg1d": 60,
                  "chg5d": 60, "volx": 70, "social": 55, "sec": 80, "ai": 50, "score": 65}
        for col in columns:
            self.tree.heading(col, text=headers[col])
            self.tree.column(col, width=widths[col], anchor="center" if col != "name" else "w")
        self.tree.pack(fill="both", expand=True, padx=PAD_X, pady=6)
        self.tree.bind("<Double-1>", self._on_row_double_click)

    def _build_holdings_tab(self, parent, PAD_X):
        holdings_header = tk.Frame(parent, bg="#ffffff")
        holdings_header.pack(fill="x", padx=PAD_X, pady=(10, 2))
        tk.Label(
            holdings_header, text="Your Holdings — Sell / Watch / Hold",
            font=("Segoe UI", 11, "bold"), bg="#ffffff",
        ).pack(side="left")
        tk.Label(
            holdings_header, text="Heuristic only -- not financial advice. Double-click a row for details.",
            fg="#777777", font=("Segoe UI", 8, "italic"), bg="#ffffff",
        ).pack(side="left", padx=10)

        holdings_columns = ("ticker", "name", "purchases", "avg_paid", "current_price",
                             "pct_change", "action", "reason")
        self.holdings_tree = ttk.Treeview(parent, columns=holdings_columns, show="headings", height=16)
        holdings_headers = {"ticker": "Ticker", "name": "Company", "purchases": "# Buys",
                             "avg_paid": "Avg Paid", "current_price": "Current",
                             "pct_change": "% Chg", "action": "Action", "reason": "Reason"}
        holdings_widths = {"ticker": 55, "name": 150, "purchases": 55, "avg_paid": 70,
                            "current_price": 70, "pct_change": 65, "action": 65, "reason": 330}
        for col in holdings_columns:
            self.holdings_tree.heading(col, text=holdings_headers[col])
            self.holdings_tree.column(col, width=holdings_widths[col],
                                       anchor="center" if col not in ("name", "reason") else "w")
        self.holdings_tree.pack(fill="both", expand=True, padx=PAD_X, pady=(4, 10))
        self.holdings_tree.bind("<Double-1>", self._on_row_double_click)

    # ------------------------------------------------------------------
    # MONEY POOLS TAB
    # ------------------------------------------------------------------

    def _build_pools_tab(self, parent, PAD_X):
        header = tk.Frame(parent, bg="#ffffff")
        header.pack(fill="x", padx=PAD_X, pady=(10, 2))
        top_header_row = tk.Frame(header, bg="#ffffff")
        top_header_row.pack(fill="x")
        tk.Label(top_header_row, text="Money Pools", font=("Segoe UI", 12, "bold"), bg="#ffffff").pack(side="left")
        tk.Button(
            top_header_row, text="⚙ Brokerage Settings", command=self._open_broker_settings,
        ).pack(side="right")
        tk.Label(
            header,
            text="Paper pools are fully simulated -- no setup needed. Real-money pools start as a manual "
                 "tracking ledger, and can optionally be linked to a free Alpaca brokerage account (Paper "
                 "or Live) so buys/sells -- yours or Brook's -- place actual orders. Nothing trades for "
                 "real until you paste your own Alpaca API key into Brokerage Settings and link a pool to it.",
            fg="#777777", font=("Segoe UI", 8, "italic"), bg="#ffffff", wraplength=980, justify="left",
        ).pack(anchor="w", pady=(2, 8))

        # ---- One-click quick actions -- no dialogs needed for the common path ----
        quick_frame = tk.Frame(parent, bg="#eef7ee", padx=10, pady=10)
        quick_frame.pack(fill="x", padx=PAD_X, pady=(0, 10))
        tk.Button(
            quick_frame, text="▶  Start Paper Investing (500 paperbucks)",
            command=self._quick_start_paper_investing, bg="#146c2e", fg="white",
            font=("Segoe UI", 10, "bold"), padx=10, pady=6,
        ).pack(side="left")
        tk.Button(
            quick_frame, text="+ Create Custom Pool", command=self._open_create_pool_dialog,
            padx=10, pady=6,
        ).pack(side="left", padx=10)
        self.pools_quick_status = tk.Label(quick_frame, text="", font=("Segoe UI", 9), bg="#eef7ee", fg="#146c2e")
        self.pools_quick_status.pack(side="left", padx=10)

        columns = ("name", "kind", "cash", "invested", "total", "brook")
        self.pools_tree = ttk.Treeview(parent, columns=columns, show="headings", height=10)
        headers = {"name": "Pool", "kind": "Type", "cash": "Cash", "invested": "Invested Value",
                   "total": "Total Value", "brook": "Brook the Broker"}
        widths = {"name": 190, "kind": 130, "cash": 110, "invested": 130, "total": 120, "brook": 140}
        for col in columns:
            self.pools_tree.heading(col, text=headers[col])
            self.pools_tree.column(col, width=widths[col], anchor="center" if col != "name" else "w")
        self.pools_tree.pack(fill="both", expand=True, padx=PAD_X, pady=(0, 4))
        self.pools_tree.bind("<Double-1>", self._open_pool_detail)

        # ---- Quick actions on whichever pool is selected above -- Brook toggle
        # included, so turning Brook on/off never requires opening a popup. ----
        select_frame = tk.Frame(parent, bg="#ffffff", pady=8)
        select_frame.pack(fill="x", padx=PAD_X)
        tk.Label(
            select_frame, text="Click a pool above, then:", font=("Segoe UI", 9), bg="#ffffff", fg="#444444",
        ).pack(side="left")
        tk.Button(
            select_frame, text="Let Brook Manage This Pool", command=self._quick_enable_brook,
            padx=8,
        ).pack(side="left", padx=8)
        tk.Button(
            select_frame, text="Turn Brook Off", command=self._quick_disable_brook, padx=8,
        ).pack(side="left")
        tk.Button(
            select_frame, text="Add Money", command=self._quick_add_money_to_selected, padx=8,
        ).pack(side="left", padx=8)
        tk.Button(
            select_frame, text="Open Full Details", command=self._quick_open_selected, padx=8,
        ).pack(side="left")

        self.pools_select_status = tk.Label(parent, text="", font=("Segoe UI", 9), bg="#ffffff")
        self.pools_select_status.pack(anchor="w", padx=PAD_X, pady=(0, 8))

        self._refresh_pools_tree()

    def _selected_pool_id(self):
        selected = self.pools_tree.selection()
        if not selected:
            self.pools_select_status.config(text="Select a pool in the list above first.", fg="red")
            return None
        return int(selected[0])

    def _quick_start_paper_investing(self):
        """One click: creates (or reuses) a single default paper pool seeded with
        500 paperbucks, so 'turning on paper investing' never requires filling out
        a form."""
        data = load_pools(self.username)
        existing = next((p for p in data["pools"] if p["name"] == "Paper Investing"), None)
        if existing:
            self.pools_quick_status.config(
                text=f"Paper Investing is already on -- ${existing['cash']:,.2f} cash available.", fg="#146c2e"
            )
        else:
            ok, msg = create_pool(self.username, "Paper Investing", "paper", DEFAULT_PAPER_POOL_SEED)
            self.pools_quick_status.config(text=msg, fg="green" if ok else "red")
        self._refresh_pools_tree()

    def _quick_enable_brook(self):
        pool_id = self._selected_pool_id()
        if pool_id is None:
            return
        set_pool_brook(self.username, pool_id, True)
        ok, msg = run_brook_for_pool(self.username, pool_id, self.ranked_data, self._current_price_lookup())
        text = "Brook is now managing this pool."
        if msg:
            text += " " + msg
        self.pools_select_status.config(text=text, fg="#146c2e")
        self._refresh_pools_tree()

    def _quick_disable_brook(self):
        pool_id = self._selected_pool_id()
        if pool_id is None:
            return
        set_pool_brook(self.username, pool_id, False)
        self.pools_select_status.config(text="Brook turned off for this pool.", fg="#444444")
        self._refresh_pools_tree()

    def _quick_add_money_to_selected(self):
        pool_id = self._selected_pool_id()
        if pool_id is None:
            return
        data = load_pools(self.username)
        pool = find_pool(data, pool_id)
        if pool.get("alpaca_linked"):
            self.pools_select_status.config(
                text="This pool's cash comes straight from your Alpaca account -- deposit there "
                     "(bank transfer/ACH) rather than through this app.",
                fg="#a35a00",
            )
            return
        label = "Amount of real money to add to this pool ($):" if pool["kind"] == "real" else \
            "Amount of paper money to add to this pool ($):"
        amount = self._prompt_amount("Add Money", label, default="100")
        if amount is None:
            return
        ok, msg = deposit_to_pool(self.username, pool_id, amount)
        self.pools_select_status.config(text=msg, fg="green" if ok else "red")
        self._refresh_pools_tree()

    def _quick_open_selected(self):
        pool_id = self._selected_pool_id()
        if pool_id is None:
            return
        self._show_pool_window(pool_id)

    def _current_price_lookup(self):
        return {sym: r["stats"]["price"] for sym, r in self.raw_by_symbol.items()}

    def _pool_live_snapshot(self, pool):
        """Returns (cash, holdings_list, error). holdings_list items have symbol/
        shares/avg_price/current/value/gain. For an Alpaca-linked pool this is
        pulled live from the brokerage account (source of truth); otherwise it's
        computed from the local ledger + current screener prices."""
        if pool.get("alpaca_linked"):
            cfg = load_broker_config(self.username)
            if not (cfg.get("api_key") and cfg.get("api_secret")):
                return None, None, "Linked to Alpaca, but no API key is saved yet -- open Brokerage Settings."
            account = alpaca_get_account(cfg)
            if account is None:
                return None, None, "Could not reach Alpaca -- check your API key in Brokerage Settings."
            positions = alpaca_get_positions(cfg)
            holdings = []
            for p in positions:
                shares, avg_price = float(p["qty"]), float(p["avg_entry_price"])
                current = float(p.get("current_price", avg_price))
                value = float(p.get("market_value", shares * current))
                gain = float(p.get("unrealized_pl", (current - avg_price) * shares))
                holdings.append({"symbol": p["symbol"], "shares": shares, "avg_price": avg_price,
                                  "current": current, "value": value, "gain": gain})
            return float(account.get("cash", 0)), holdings, None

        price_lookup = self._current_price_lookup()
        holdings = []
        for symbol, h in pool["holdings"].items():
            current = price_lookup.get(symbol, h["avg_price"])
            value = h["shares"] * current
            gain = (current - h["avg_price"]) * h["shares"]
            holdings.append({"symbol": symbol, "shares": h["shares"], "avg_price": h["avg_price"],
                              "current": current, "value": value, "gain": gain})
        return pool["cash"], holdings, None

    def _refresh_pools_tree(self):
        if not hasattr(self, "pools_tree") or not self.pools_tree.winfo_exists():
            return
        for row in self.pools_tree.get_children():
            self.pools_tree.delete(row)
        data = load_pools(self.username)
        for pool in data["pools"]:
            cash, holdings, err = self._pool_live_snapshot(pool)
            if err:
                cash_str, invested_str, total_str = "—", "—", "—"
            else:
                invested = round(sum(h["value"] for h in holdings), 2)
                total = round(cash + invested, 2)
                cash_str, invested_str, total_str = f"${cash:,.2f}", f"${invested:,.2f}", f"${total:,.2f}"
            kind_label = pool["kind"].capitalize()
            if pool.get("alpaca_linked"):
                broker_cfg = load_broker_config(self.username)
                kind_label += " · Alpaca " + ("Paper" if broker_cfg.get("paper", True) else "LIVE")
            self.pools_tree.insert("", "end", iid=str(pool["id"]), values=(
                pool["name"], kind_label, cash_str, invested_str, total_str,
                "ON" if pool["brook_enabled"] else "off",
            ))

    def _run_brook_for_all_pools(self):
        """Called once per scan cycle. Any pool with Brook switched on gets a chance
        to deploy idle cash and/or rebalance into the current top-2 picks."""
        if not self.ranked_data:
            return
        data = load_pools(self.username)
        price_lookup = self._current_price_lookup()
        for pool in data["pools"]:
            if pool.get("brook_enabled"):
                run_brook_for_pool(self.username, pool["id"], self.ranked_data, price_lookup)
        self._refresh_pools_tree()

    def _prompt_amount(self, title, label_text, default=""):
        """Small modal popup that asks for a single positive dollar amount. Returns
        the float, or None if the user cancelled/closed it."""
        result = {"value": None}
        popup = tk.Toplevel(self.root)
        popup.title(title)
        popup.geometry("320x150")
        popup.transient(self.root)
        popup.grab_set()

        tk.Label(popup, text=label_text, wraplength=290, justify="left").pack(anchor="w", padx=14, pady=(16, 4))
        entry = tk.Entry(popup, width=20)
        entry.insert(0, default)
        entry.pack(padx=14)
        entry.focus_set()
        entry.select_range(0, "end")
        status = tk.Label(popup, text="", fg="red", font=("Segoe UI", 8))
        status.pack(anchor="w", padx=14, pady=(4, 0))

        def confirm():
            try:
                val = float(entry.get().replace("$", "").replace(",", ""))
                if val <= 0:
                    raise ValueError
            except ValueError:
                status.config(text="Enter a positive number.")
                return
            result["value"] = val
            popup.destroy()

        def cancel():
            popup.destroy()

        btns = tk.Frame(popup)
        btns.pack(pady=12)
        tk.Button(btns, text="OK", command=confirm, width=10).pack(side="left", padx=4)
        tk.Button(btns, text="Cancel", command=cancel, width=10).pack(side="left", padx=4)
        popup.bind("<Return>", lambda e: confirm())
        popup.protocol("WM_DELETE_WINDOW", cancel)
        popup.wait_window()
        return result["value"]

    def _force_popup_front(self, popup):
        """Makes a Toplevel modal-ish and guaranteed to be visible/focused on top
        of the main window, instead of sometimes opening behind it unnoticed."""
        popup.transient(self.root)
        popup.grab_set()
        popup.lift()
        popup.focus_force()
        popup.attributes("-topmost", True)
        popup.after(200, lambda: popup.attributes("-topmost", False))

    def _open_create_pool_dialog(self):
        popup = tk.Toplevel(self.root)
        popup.title("Create Money Pool")
        popup.geometry("400x300")
        self._force_popup_front(popup)

        tk.Label(popup, text="Pool name:").pack(anchor="w", padx=14, pady=(16, 2))
        name_entry = tk.Entry(popup, width=36)
        name_entry.pack(padx=14)
        name_entry.focus_set()

        tk.Label(popup, text="Type:").pack(anchor="w", padx=14, pady=(12, 2))
        kind_var = tk.StringVar(value="paper")
        kind_frame = tk.Frame(popup)
        kind_frame.pack(anchor="w", padx=14)
        tk.Radiobutton(kind_frame, text="Paper (simulated)", variable=kind_var, value="paper").pack(
            side="left", padx=(0, 10)
        )
        tk.Radiobutton(kind_frame, text="Real (manual tracking only)", variable=kind_var, value="real").pack(
            side="left"
        )

        tk.Label(popup, text="Starting amount ($):").pack(anchor="w", padx=14, pady=(12, 2))
        amount_entry = tk.Entry(popup, width=20)
        amount_entry.insert(0, str(int(DEFAULT_PAPER_POOL_SEED)))
        amount_entry.pack(padx=14)

        tk.Label(
            popup, text="Paper investing traditionally starts at 500 -- change this to whatever you like.",
            fg="#777777", font=("Segoe UI", 8, "italic"),
        ).pack(anchor="w", padx=14, pady=(2, 0))

        status_label = tk.Label(popup, text="", font=("Segoe UI", 9))
        status_label.pack(anchor="w", padx=14, pady=(10, 0))

        def do_create():
            ok, msg = create_pool(self.username, name_entry.get(), kind_var.get(), amount_entry.get())
            status_label.config(text=msg, fg="green" if ok else "red")
            if ok:
                self._refresh_pools_tree()
                popup.after(700, popup.destroy)

        tk.Button(popup, text="Create Pool", command=do_create).pack(pady=14)

    def _open_pool_detail(self, event):
        selected = self.pools_tree.selection()
        if not selected:
            return
        self._show_pool_window(int(selected[0]))

    def _show_pool_window(self, pool_id):
        data = load_pools(self.username)
        pool = find_pool(data, pool_id)
        if not pool:
            return

        popup = tk.Toplevel(self.root)
        popup.title(f"Money Pool — {pool['name']}")
        popup.geometry("680x580")
        self._force_popup_front(popup)

        top = tk.Frame(popup)
        top.pack(fill="x", padx=14, pady=(14, 4))
        tk.Label(top, text=pool["name"], font=("Segoe UI", 13, "bold")).pack(side="left")
        tk.Label(top, text=f"  ({pool['kind'].capitalize()})", font=("Segoe UI", 10), fg="#555555").pack(side="left")

        disclaimer_label = tk.Label(
            popup, text="", fg="#a35a00", font=("Segoe UI", 8, "italic"), wraplength=640, justify="left",
        )
        disclaimer_label.pack(fill="x", padx=14, pady=(0, 6))

        summary_label = tk.Label(popup, text="", font=("Segoe UI", 10, "bold"))
        summary_label.pack(anchor="w", padx=14, pady=(2, 8))

        columns = ("symbol", "shares", "avg_price", "current", "value", "gain")
        holdings_tree = ttk.Treeview(popup, columns=columns, show="headings", height=8)
        col_headers = {"symbol": "Ticker", "shares": "Shares", "avg_price": "Avg Price",
                       "current": "Current", "value": "Value", "gain": "Gain/Loss"}
        for col in columns:
            holdings_tree.heading(col, text=col_headers[col])
            holdings_tree.column(col, width=95, anchor="center")
        holdings_tree.pack(fill="both", expand=True, padx=14, pady=4)

        brook_status_label = tk.Label(popup, text="", font=("Segoe UI", 10, "bold"))
        brook_status_label.pack(anchor="w", padx=14, pady=(8, 0))

        action_status = tk.Label(popup, text="", font=("Segoe UI", 9), wraplength=640, justify="left")
        action_status.pack(anchor="w", padx=14, pady=(2, 0))

        def refresh_view():
            data2 = load_pools(self.username)
            p = find_pool(data2, pool_id)
            if not p:
                popup.destroy()
                return

            if p.get("alpaca_linked"):
                cfg = load_broker_config(self.username)
                mode = "PAPER (fake money)" if cfg.get("paper", True) else "LIVE (real money)"
                disclaimer_label.config(
                    text=f"Linked to Alpaca -- {mode}. Cash and holdings below come straight from that "
                         f"account. Buys/sells here (and Brook's) place real orders through Alpaca."
                )
            elif p["kind"] == "real":
                disclaimer_label.config(
                    text="Manual tracking ledger -- not linked to a brokerage. \"Add Money\", investing, "
                         "and Brook here just record numbers; nothing actually trades. Link to Alpaca "
                         "below to make it real."
                )
            else:
                disclaimer_label.config(text="Paper pool -- fully simulated with real market prices.")

            cash, holdings, err = self._pool_live_snapshot(p)
            for row in holdings_tree.get_children():
                holdings_tree.delete(row)
            if err:
                summary_label.config(text=err)
            else:
                for h in holdings:
                    holdings_tree.insert("", "end", iid=h["symbol"], values=(
                        h["symbol"], f"{h['shares']:g}", f"${h['avg_price']:,.4f}",
                        f"${h['current']:,.2f}", f"${h['value']:,.2f}",
                        f"{'+' if h['gain'] >= 0 else ''}${h['gain']:,.2f}",
                    ))
                invested = round(sum(h["value"] for h in holdings), 2)
                total = round(cash + invested, 2)
                summary_label.config(
                    text=f"Cash: ${cash:,.2f}    |    Invested: ${invested:,.2f}    |    Total: ${total:,.2f}"
                )

            brook_status_label.config(
                text=f"Brook the Broker: {'ON — auto-managing the current top 2' if p['brook_enabled'] else 'OFF'}",
                fg="#146c2e" if p["brook_enabled"] else "#555555",
            )
            link_btn.config(text="Unlink from Alpaca" if p.get("alpaca_linked") else "Link to Alpaca")
            link_btn.pack_forget()
            if p["kind"] == "real":
                link_btn.pack(side="left", padx=6)
            self._refresh_pools_tree()

        def do_deposit():
            p = find_pool(load_pools(self.username), pool_id)
            if p.get("alpaca_linked"):
                if not starling_is_connected(self.username):
                    action_status.config(
                        text="Cash for a linked pool lives in your Alpaca account. Deposit there directly, "
                             "or connect Starling in Brokerage Settings to fund it from here.",
                        fg="#a35a00",
                    )
                    return
                amount = self._prompt_amount("Deposit via Starling", "Amount to send from Starling (£):", default="100")
                if amount is None:
                    return
                action_status.config(text="Sending payment via Starling...", fg="#555555")
                popup.update_idletasks()

                def worker():
                    ok, msg = starling_send_payment(self.username, amount, reference=f"Fund {p['name']}"[:18])
                    def show():
                        action_status.config(text=msg, fg="green" if ok else "red")
                        refresh_view()
                    popup.after(0, show)

                threading.Thread(target=worker, daemon=True).start()
                return
            label = "Amount of real money to add to this pool ($):" if p["kind"] == "real" else \
                "Amount of paper money to add to this pool ($):"
            amount = self._prompt_amount("Add Money", label, default="100")
            if amount is None:
                return
            ok, msg = deposit_to_pool(self.username, pool_id, amount)
            action_status.config(text=msg, fg="green" if ok else "red")
            refresh_view()

        def do_invest():
            if not self.ranked_data:
                action_status.config(
                    text="Screener data isn't loaded yet -- wait for the next scan and try again.", fg="red"
                )
                return
            p = find_pool(load_pools(self.username), pool_id)
            self._open_manual_invest_dialog(
                pool_id, on_done=refresh_view, alpaca_linked=bool(p.get("alpaca_linked"))
            )

        def do_sell():
            sel = holdings_tree.selection()
            if not sel:
                action_status.config(text="Select a holding in the table above first.", fg="red")
                return
            symbol = sel[0]
            p = find_pool(load_pools(self.username), pool_id)
            if p.get("alpaca_linked"):
                cfg = load_broker_config(self.username)
                ok, msg = alpaca_close_position(cfg, symbol)
            else:
                data3 = load_pools(self.username)
                p3 = find_pool(data3, pool_id)
                price = self._current_price_lookup().get(symbol)
                ok, msg = _sell_in_pool(p3, symbol, price, actor="you")
                if ok:
                    save_pools(self.username, data3)
            action_status.config(text=msg, fg="green" if ok else "red")
            refresh_view()

        def toggle_brook():
            p = find_pool(load_pools(self.username), pool_id)
            new_state = not p["brook_enabled"]
            set_pool_brook(self.username, pool_id, new_state)
            if new_state:
                ok, msg = run_brook_for_pool(self.username, pool_id, self.ranked_data, self._current_price_lookup())
                action_status.config(
                    text=("Brook the Broker turned ON. " + msg) if msg else "Brook the Broker turned ON.",
                    fg="green",
                )
            else:
                action_status.config(text="Brook the Broker turned OFF for this pool.", fg="green")
            refresh_view()

        def run_brook_now():
            ok, msg = run_brook_for_pool(self.username, pool_id, self.ranked_data, self._current_price_lookup())
            action_status.config(text=msg, fg="green" if ok else "red")
            refresh_view()

        def toggle_alpaca_link():
            p = find_pool(load_pools(self.username), pool_id)
            if p["kind"] != "real":
                action_status.config(text="Only real-money pools can link to Alpaca.", fg="red")
                return
            new_state = not p.get("alpaca_linked", False)
            if new_state:
                cfg = load_broker_config(self.username)
                if not (cfg.get("api_key") and cfg.get("api_secret")):
                    action_status.config(
                        text="Save your Alpaca API key in Brokerage Settings first.", fg="red"
                    )
                    return
                ok, msg = alpaca_test_connection(cfg)
                if not ok:
                    action_status.config(text="Couldn't verify Alpaca connection: " + msg, fg="red")
                    return
                if not cfg.get("paper", True) and not cfg.get("live_confirmed", False):
                    action_status.config(
                        text="Brokerage Settings is set to LIVE trading but the real-money confirmation "
                             "box isn't checked -- open Brokerage Settings to confirm before linking.",
                        fg="red",
                    )
                    return
            set_pool_alpaca_link(self.username, pool_id, new_state)
            action_status.config(
                text=("Linked to Alpaca -- cash and holdings now come from your account. " + msg) if new_state
                else "Unlinked from Alpaca -- back to manual tracking.",
                fg="green",
            )
            refresh_view()

        def do_delete():
            ok, msg = delete_pool(self.username, pool_id)
            if ok:
                self._refresh_pools_tree()
                popup.destroy()
            else:
                action_status.config(text=msg, fg="red")

        btns = tk.Frame(popup, pady=10)
        btns.pack(fill="x", padx=14)
        tk.Button(btns, text="Add Money", command=do_deposit, width=12).pack(side="left")
        tk.Button(btns, text="Invest", command=do_invest, width=10).pack(side="left", padx=4)
        tk.Button(btns, text="Sell Selected", command=do_sell, width=13).pack(side="left")
        link_btn = tk.Button(btns, text="Link to Alpaca", command=toggle_alpaca_link, width=15)

        btns2 = tk.Frame(popup, pady=(0, 10))
        btns2.pack(fill="x", padx=14)
        tk.Button(btns2, text="Toggle Brook", command=toggle_brook, width=13).pack(side="left")
        tk.Button(btns2, text="Run Brook Now", command=run_brook_now, width=14).pack(side="left", padx=6)
        tk.Button(btns2, text="Delete Pool", command=do_delete, width=12, fg="#a30000").pack(side="right")

        refresh_view()

    def _open_manual_invest_dialog(self, pool_id, on_done, alpaca_linked=False):
        popup = tk.Toplevel(self.root)
        popup.title("Invest Manually")
        popup.geometry("420x260")
        self._force_popup_front(popup)

        if alpaca_linked:
            tk.Label(
                popup, text="This pool is linked to Alpaca -- this places a real market order.",
                fg="#a35a00", font=("Segoe UI", 8, "italic"), wraplength=380, justify="left",
            ).pack(fill="x", padx=14, pady=(10, 0))

        tk.Label(popup, text="Stock (from the current Top 20 list):").pack(anchor="w", padx=14, pady=(16, 2))
        options = [
            f"{r['symbol']} — {r['name']} (${r['stats']['price']:,.2f}, AI score {r['ai_score']:+.2f})"
            for r in self.ranked_data
        ]
        symbol_map = dict(zip(options, self.ranked_data))
        symbol_var = tk.StringVar()
        combo = ttk.Combobox(popup, textvariable=symbol_var, values=options, width=48, state="readonly")
        if options:
            combo.current(0)
        combo.pack(padx=14)

        tk.Label(popup, text="Amount to invest ($):").pack(anchor="w", padx=14, pady=(14, 2))
        amount_entry = tk.Entry(popup, width=20)
        amount_entry.pack(padx=14)
        amount_entry.focus_set()

        status_label = tk.Label(popup, text="", font=("Segoe UI", 9))
        status_label.pack(anchor="w", padx=14, pady=(10, 0))

        def do_buy():
            chosen = symbol_map.get(symbol_var.get())
            if not chosen:
                status_label.config(text="Pick a stock first.", fg="red")
                return
            try:
                amt = float(amount_entry.get().replace("$", "").replace(",", ""))
                if amt <= 0:
                    raise ValueError
            except ValueError:
                status_label.config(text="Enter a positive dollar amount.", fg="red")
                return
            if alpaca_linked:
                cfg = load_broker_config(self.username)
                ok, msg = alpaca_place_notional_order(cfg, chosen["symbol"], amt, side="buy")
            else:
                ok, msg = invest_in_pool(
                    self.username, pool_id, chosen["symbol"], chosen["name"], amt, chosen["stats"]["price"],
                )
            status_label.config(text=msg, fg="green" if ok else "red")
            if ok:
                on_done()
                popup.after(800, popup.destroy)

        tk.Button(popup, text="Buy", command=do_buy).pack(pady=14)

    def _open_broker_settings(self):
        cfg = load_broker_config(self.username)
        popup = tk.Toplevel(self.root)
        popup.title("Brokerage Settings")
        popup.geometry("500x560")
        self._force_popup_front(popup)

        notebook = ttk.Notebook(popup)
        notebook.pack(fill="both", expand=True, padx=8, pady=8)

        # ---------------- Alpaca tab (trading) ----------------
        alpaca_tab = tk.Frame(notebook)
        notebook.add(alpaca_tab, text="Alpaca (trading)")

        tk.Label(
            alpaca_tab, text="Alpaca Markets — free stock trading API", font=("Segoe UI", 12, "bold"),
        ).pack(anchor="w", padx=16, pady=(16, 2))
        tk.Label(
            alpaca_tab,
            text="Create a free account at alpaca.markets, generate an API key pair, and paste it below. "
                 "That's the only setup needed -- Paper mode trades fake money against real prices (start "
                 "here); Live trades real money. Once saved, link any real-money pool to Alpaca (in that "
                 "pool's window) to have your buys/sells -- and Brook's -- place actual orders through it.",
            fg="#555555", font=("Segoe UI", 9), wraplength=440, justify="left",
        ).pack(anchor="w", padx=16, pady=(0, 12))

        tk.Label(alpaca_tab, text="API Key ID:").pack(anchor="w", padx=16)
        key_entry = tk.Entry(alpaca_tab, width=48)
        key_entry.insert(0, cfg.get("api_key", ""))
        key_entry.pack(padx=16, pady=(0, 8))

        tk.Label(alpaca_tab, text="API Secret Key:").pack(anchor="w", padx=16)
        secret_entry = tk.Entry(alpaca_tab, width=48, show="*")
        secret_entry.insert(0, cfg.get("api_secret", ""))
        secret_entry.pack(padx=16, pady=(0, 10))

        mode_var = tk.StringVar(value="paper" if cfg.get("paper", True) else "live")
        tk.Radiobutton(
            alpaca_tab, text="Paper trading (fake money -- start here)", variable=mode_var, value="paper",
        ).pack(anchor="w", padx=16)
        tk.Radiobutton(
            alpaca_tab, text="Live trading (REAL MONEY, real trades)", variable=mode_var, value="live",
        ).pack(anchor="w", padx=16)

        confirm_var = tk.BooleanVar(value=cfg.get("live_confirmed", False))
        tk.Checkbutton(
            alpaca_tab, variable=confirm_var, justify="left", fg="#a30000", wraplength=420,
            text="I understand Live mode places real trades with real money automatically, "
                 "including via Brook with no per-trade confirmation from me.",
        ).pack(anchor="w", padx=16, pady=(8, 4))

        status_label = tk.Label(alpaca_tab, text="", font=("Segoe UI", 9), wraplength=440, justify="left")
        status_label.pack(anchor="w", padx=16, pady=(6, 0))

        def do_test():
            test_cfg = {
                "api_key": key_entry.get().strip(), "api_secret": secret_entry.get().strip(),
                "paper": mode_var.get() == "paper",
            }
            ok, msg = alpaca_test_connection(test_cfg)
            status_label.config(text=msg, fg="green" if ok else "red")

        def do_save():
            new_cfg = {
                "api_key": key_entry.get().strip(),
                "api_secret": secret_entry.get().strip(),
                "paper": mode_var.get() == "paper",
                "live_confirmed": bool(confirm_var.get()),
            }
            if not new_cfg["api_key"] or not new_cfg["api_secret"]:
                status_label.config(text="Both the key ID and secret key are required.", fg="red")
                return
            if mode_var.get() == "live" and not confirm_var.get():
                status_label.config(text="Check the confirmation box above to enable Live trading.", fg="red")
                return
            if save_broker_config(self.username, new_cfg):
                status_label.config(text="Saved.", fg="green")
                self._refresh_pools_tree()
            else:
                status_label.config(text="Failed to save -- see console for details.", fg="red")

        btns = tk.Frame(alpaca_tab, pady=12)
        btns.pack()
        tk.Button(btns, text="Test Connection", command=do_test, width=16).pack(side="left", padx=6)
        tk.Button(btns, text="Save", command=do_save, width=12).pack(side="left", padx=6)

        # ---------------- Starling tab (funding) ----------------
        starling_tab = tk.Frame(notebook)
        notebook.add(starling_tab, text="Starling (funding)")

        s_cfg = load_starling_config(self.username)

        tk.Label(
            starling_tab, text="Starling Bank — fund a pool from your real account", font=("Segoe UI", 12, "bold"),
        ).pack(anchor="w", padx=16, pady=(16, 2))
        tk.Label(
            starling_tab,
            text="Starling is a bank, not a broker -- it can't buy stocks itself. Connecting it lets you send "
                 "a real payment (you choose the amount each time) from your Starling account to the bank "
                 "account behind your Alpaca account's funding link, which then shows up as Alpaca cash for "
                 "a linked real pool. This uses Starling's own login (OAuth) -- the app never sees your card "
                 "number or your Starling password. Register a free developer app at "
                 "developer.starlingbank.com to get a Client ID/Secret first.",
            fg="#555555", font=("Segoe UI", 9), wraplength=450, justify="left",
        ).pack(anchor="w", padx=16, pady=(0, 10))

        s_status = tk.Label(
            starling_tab,
            text="Connected to Starling." if starling_is_connected(self.username) else "Not connected.",
            font=("Segoe UI", 9, "bold"),
            fg="#146c2e" if starling_is_connected(self.username) else "#555555",
        )
        s_status.pack(anchor="w", padx=16, pady=(0, 8))

        tk.Label(starling_tab, text="Client ID:").pack(anchor="w", padx=16)
        s_client_id = tk.Entry(starling_tab, width=48)
        s_client_id.insert(0, s_cfg.get("client_id", ""))
        s_client_id.pack(padx=16, pady=(0, 6))

        tk.Label(starling_tab, text="Client Secret:").pack(anchor="w", padx=16)
        s_client_secret = tk.Entry(starling_tab, width=48, show="*")
        s_client_secret.insert(0, s_cfg.get("client_secret", ""))
        s_client_secret.pack(padx=16, pady=(0, 6))

        s_connect_status = tk.Label(starling_tab, text="", font=("Segoe UI", 9), wraplength=450, justify="left")

        def do_connect():
            s_connect_status.config(text="Opening your browser to log into Starling...", fg="#555555")
            popup.update_idletasks()

            def worker():
                ok, msg = starling_connect(self.username, s_client_id.get(), s_client_secret.get())
                def show():
                    s_connect_status.config(text=msg, fg="green" if ok else "red")
                    if ok:
                        s_status.config(text="Connected to Starling.", fg="#146c2e")
                popup.after(0, show)

            threading.Thread(target=worker, daemon=True).start()

        tk.Button(starling_tab, text="Connect Starling Account", command=do_connect).pack(anchor="w", padx=16, pady=(0, 4))
        s_connect_status.pack(anchor="w", padx=16, pady=(0, 10))

        tk.Label(
            starling_tab, text="Deposit destination (the bank account behind your Alpaca ACH funding link):",
            font=("Segoe UI", 9, "bold"),
        ).pack(anchor="w", padx=16, pady=(4, 2))

        tk.Label(starling_tab, text="Account holder name:").pack(anchor="w", padx=16)
        s_dest_name = tk.Entry(starling_tab, width=48)
        s_dest_name.insert(0, s_cfg.get("dest_name", ""))
        s_dest_name.pack(padx=16, pady=(0, 6))

        tk.Label(starling_tab, text="Account number:").pack(anchor="w", padx=16)
        s_dest_number = tk.Entry(starling_tab, width=48)
        s_dest_number.insert(0, s_cfg.get("dest_account_number", ""))
        s_dest_number.pack(padx=16, pady=(0, 6))

        tk.Label(starling_tab, text="Sort code:").pack(anchor="w", padx=16)
        s_dest_sort = tk.Entry(starling_tab, width=48)
        s_dest_sort.insert(0, s_cfg.get("dest_sort_code", ""))
        s_dest_sort.pack(padx=16, pady=(0, 8))

        s_save_status = tk.Label(starling_tab, text="", font=("Segoe UI", 9), wraplength=450, justify="left")

        def do_save_starling():
            new_cfg = load_starling_config(self.username)  # keep tokens, only update these fields
            new_cfg.update({
                "dest_name": s_dest_name.get().strip(),
                "dest_account_number": s_dest_number.get().strip(),
                "dest_sort_code": s_dest_sort.get().strip(),
            })
            if save_starling_config(self.username, new_cfg):
                s_save_status.config(text="Saved.", fg="green")
            else:
                s_save_status.config(text="Failed to save -- see console for details.", fg="red")

        tk.Button(starling_tab, text="Save Destination", command=do_save_starling).pack(anchor="w", padx=16)
        s_save_status.pack(anchor="w", padx=16, pady=(4, 0))

    def _open_admin_panel(self):
        popup = tk.Toplevel(self.root)
        popup.title("Admin Panel")
        popup.geometry("680x520")

        notebook = ttk.Notebook(popup)
        notebook.pack(fill="both", expand=True, padx=8, pady=8)

        # ---------------- Accounts tab ----------------
        accounts_tab = tk.Frame(notebook)
        notebook.add(accounts_tab, text="Accounts")

        accounts_columns = ("username", "role", "org_key")
        accounts_tree = ttk.Treeview(accounts_tab, columns=accounts_columns, show="headings", height=14)
        for col, label, width in (("username", "Username", 150), ("role", "Role", 90), ("org_key", "Org Key", 180)):
            accounts_tree.heading(col, text=label)
            accounts_tree.column(col, width=width, anchor="w")
        accounts_tree.pack(fill="both", expand=True, padx=10, pady=(10, 4))

        accounts_msg = tk.Label(accounts_tab, text="", font=("Segoe UI", 9))
        accounts_msg.pack(anchor="w", padx=10)

        def refresh_accounts_tree():
            accounts_tree.delete(*accounts_tree.get_children())
            for uname, info in sorted(load_accounts().items()):
                accounts_tree.insert("", "end", iid=uname, values=(
                    uname, info.get("role", "member"), info.get("org_key") or "—",
                ))

        def do_delete_account():
            selected = accounts_tree.selection()
            if not selected:
                return
            uname = selected[0]
            ok, message = delete_account(uname)
            accounts_msg.config(text=message, fg="green" if ok else "red")
            if ok:
                refresh_accounts_tree()

        tk.Button(accounts_tab, text="Delete Selected Account", command=do_delete_account).pack(
            anchor="w", padx=10, pady=(4, 10)
        )
        refresh_accounts_tree()

        # ---------------- Org Keys tab ----------------
        keys_tab = tk.Frame(notebook)
        notebook.add(keys_tab, text="Org Keys")

        keys_columns = ("key", "admin", "used", "max")
        keys_tree = ttk.Treeview(keys_tab, columns=keys_columns, show="headings", height=8)
        for col, label, width in (("key", "Org Key", 180), ("admin", "Admin", 130),
                                   ("used", "Used", 60), ("max", "Max", 60)):
            keys_tree.heading(col, text=label)
            keys_tree.column(col, width=width, anchor="w")
        keys_tree.pack(fill="both", expand=False, padx=10, pady=(10, 4))

        def refresh_keys_tree():
            keys_tree.delete(*keys_tree.get_children())
            for key, info in load_org_keys().items():
                keys_tree.insert("", "end", iid=key, values=(
                    key, info.get("admin_username", "—"),
                    org_key_usage_count(key), info.get("max_accounts", "—"),
                ))

        refresh_keys_tree()

        tk.Label(keys_tab, text="Create a new Org Key", font=("Segoe UI", 10, "bold")).pack(
            anchor="w", padx=10, pady=(14, 4)
        )
        create_form = tk.Frame(keys_tab)
        create_form.pack(anchor="w", padx=10)
        tk.Label(create_form, text="Admin username (existing or new):").grid(row=0, column=0, sticky="e", pady=3)
        admin_username_entry = tk.Entry(create_form, width=24)
        admin_username_entry.grid(row=0, column=1, pady=3, padx=6)
        tk.Label(create_form, text="Admin password (only if new):").grid(row=1, column=0, sticky="e", pady=3)
        admin_password_entry = tk.Entry(create_form, width=24, show="*")
        admin_password_entry.grid(row=1, column=1, pady=3, padx=6)
        tk.Label(create_form, text="Max accounts under this key:").grid(row=2, column=0, sticky="e", pady=3)
        max_accounts_entry = tk.Entry(create_form, width=24)
        max_accounts_entry.insert(0, "5")
        max_accounts_entry.grid(row=2, column=1, pady=3, padx=6)

        keys_msg = tk.Label(keys_tab, text="", font=("Segoe UI", 9), wraplength=560)
        keys_msg.pack(anchor="w", padx=10, pady=(6, 0))

        def do_create_org_key():
            admin_username = admin_username_entry.get().strip()
            admin_password = admin_password_entry.get()
            try:
                max_accounts = int(max_accounts_entry.get().strip())
            except ValueError:
                keys_msg.config(text="Max accounts must be a whole number.", fg="red")
                return
            ok, message, key = create_org_key(admin_username, admin_password, max_accounts)
            keys_msg.config(text=message, fg="green" if ok else "red")
            if ok:
                admin_username_entry.delete(0, "end")
                admin_password_entry.delete(0, "end")
                refresh_keys_tree()
                refresh_accounts_tree()

        tk.Button(keys_tab, text="Create Org Key", command=do_create_org_key).pack(anchor="w", padx=10, pady=8)

    def _start_background_updates(self):
        threading.Thread(target=self._update_loop, daemon=True).start()

    def _update_loop(self):
        while True:
            self._run_full_scan()
            time.sleep(UPDATE_INTERVAL_SECONDS)

    def manual_refresh(self):
        threading.Thread(target=self._run_full_scan, daemon=True).start()

    def _run_full_scan(self):
        self.root.after(0, lambda: self.status_label.config(text="Updating..."))

        scan = compute_ranked_scan()
        top20 = scan["top20"]
        results_by_symbol = scan["results_by_symbol"]
        quality_price_data = scan["quality_price_data"]
        price_data = scan["price_data"]
        weather_adjustments = scan["weather_adjustments"]
        world_times = scan["world_times"]
        benchmarks = scan["benchmarks"]
        universe_size = scan["universe_size"]
        quality_size = scan["quality_size"]

        # --- Holdings: make sure every stock the user has logged a purchase for gets
        # processed too, even if it didn't make the momentum shortlist, so the "Your
        # Holdings" panel and its double-click details always have real data. ---
        holdings_rows = []
        for summary in summarize_holdings(self.username):
            symbol = summary["symbol"]
            if symbol not in results_by_symbol:
                stats = quality_price_data.get(symbol) or price_data.get(symbol)
                if not stats:
                    stats = _download_price_chunk([symbol]).get(symbol)
                if stats:
                    name = _UNIVERSE.get(symbol, symbol)
                    new_record = process_single_ticker(symbol, name, stats, weather_adjustments)
                    try:
                        ai_score, ai_reason = ai_quick_score(
                            new_record["symbol"], new_record["name"], new_record["stats"],
                            new_record["processed_headlines"], new_record["sec_data"], new_record["social_ratio"],
                        )
                    except Exception as e:
                        ai_score, ai_reason = 0.0, f"AI analysis failed: {e}"
                    new_record["ai_score"] = ai_score
                    new_record["ai_reason"] = ai_reason
                    new_record["score"] = round(new_record["score"] + ai_score * 2.0, 2)
                    new_record["context"] += f"\nAI quick-analysis score: {ai_score} -- {ai_reason}"
                    results_by_symbol[symbol] = new_record
                else:
                    continue  # couldn't get any price data for this holding this cycle

            record = results_by_symbol[symbol]
            rec_trend = fetch_finnhub_recommendation_trend(symbol)
            action, reason = compute_holding_action(record["stats"], summary["avg_price_paid"], rec_trend)
            holdings_rows.append({
                "symbol": symbol, "name": record["name"], "purchases": summary["num_purchases"],
                "avg_paid": summary["avg_price_paid"], "current_price": record["stats"]["price"],
                "action": action, "reason": reason,
            })

        self.ranked_data = top20
        self.raw_by_symbol = results_by_symbol
        self.holdings_rows = holdings_rows
        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        self.root.after(0, lambda: self._refresh_ui(now_str, world_times, universe_size, quality_size, benchmarks))
        # BUG FIX: this call was missing entirely, which is why Brook never actually
        # invested anything -- run_brook_for_all_pools() existed but nothing called
        # it after a scan finished. Scheduled via root.after because this method
        # runs on a background thread and _refresh_pools_tree() touches Tkinter
        # widgets, which must only happen on the main thread.
        self.root.after(0, self._run_brook_for_all_pools)

    def _refresh_ui(self, now_str, world_times, universe_size, quality_size, benchmarks):
        for row in self.tree.get_children():
            self.tree.delete(row)

        for i, r in enumerate(self.ranked_data, start=1):
            s = r["stats"]
            sec = r["sec_data"]
            sec_label = f"{sec['form4_count']}F4" + (" +8K" if sec["has_recent_8k"] else "")
            self.tree.insert("", "end", iid=r["symbol"], values=(
                i, r["symbol"], r["name"], f"${s['price']}",
                f"{s['chg_1d_pct']}%", f"{s['chg_5d_pct']}%", f"{s['vol_ratio']}x",
                f"{r['social_ratio']}", sec_label, f"{r['ai_score']}", r["score"],
            ))

        for row in self.holdings_tree.get_children():
            self.holdings_tree.delete(row)
        for h in self.holdings_rows:
            avg_paid_str = f"${h['avg_paid']}" if h["avg_paid"] is not None else "—"
            pct_str = "—"
            if h["avg_paid"]:
                pct_str = f"{(h['current_price'] - h['avg_paid']) / h['avg_paid'] * 100:+.2f}%"
            self.holdings_tree.insert("", "end", iid=h["symbol"], values=(
                h["symbol"], h["name"], h["purchases"], avg_paid_str,
                f"${h['current_price']}", pct_str, h["action"], h["reason"],
            ))

        self.status_label.config(
            text=f"Scanned {universe_size:,} • {quality_size:,} passed liquidity filter • "
                 f"top {SHORTLIST_SIZE} deep-analyzed • Last updated: {now_str} (every 10 min)"
        )
        wt = "   |   ".join(f"{city}: {t}" for city, t in world_times.items())
        self.world_time_label.config(text=f"World times: {wt}")

        for row in self.benchmarks_tree.get_children():
            self.benchmarks_tree.delete(row)
        for name, stats in benchmarks.items():
            self.benchmarks_tree.insert("", "end", values=(
                name, stats["price"], f"{stats['chg_1d_pct']}%", f"{stats['chg_5d_pct']}%",
            ))

    def _on_row_double_click(self, event):
        selected = self.tree.selection()
        if not selected:
            return
        symbol = selected[0]
        record = self.raw_by_symbol.get(symbol)
        if not record:
            return

        popup = tk.Toplevel(self.root)
        popup.title(symbol)
        popup.geometry("620x480")

        notebook = ttk.Notebook(popup)
        notebook.pack(fill="both", expand=True, padx=8, pady=8)

        # ---------------- Tab 1: What the stock is ----------------
        company_tab = tk.Frame(notebook)
        notebook.add(company_tab, text="What Is This Stock")
        tk.Label(company_tab, text=f"{symbol} — {record['name']}", font=("Segoe UI", 12, "bold")).pack(
            anchor="w", padx=10, pady=(10, 4)
        )
        company_text = tk.Text(company_tab, wrap="word", font=("Segoe UI", 10))
        company_text.pack(fill="both", expand=True, padx=10, pady=6)
        company_text.insert("1.0", "Loading company info...")
        company_text.config(state="disabled")

        def load_company_info():
            profile = fetch_company_profile(symbol)
            s = record["stats"]
            lines = [
                f"Ticker: {symbol}",
                f"Company: {record['name']}",
                f"Current price: ${s['price']}",
                f"1-day change: {s['chg_1d_pct']}%   |   5-day change: {s['chg_5d_pct']}%",
                f"Volume vs recent average: {s['vol_ratio']}x",
            ]
            if profile:
                if profile.get("finnhubIndustry"):
                    lines.append(f"Industry: {profile['finnhubIndustry']}")
                if profile.get("exchange"):
                    lines.append(f"Exchange: {profile['exchange']}")
                if profile.get("marketCapitalization"):
                    lines.append(f"Market cap: ${profile['marketCapitalization']:,.0f}M")
                if profile.get("ipo"):
                    lines.append(f"IPO date: {profile['ipo']}")
                if profile.get("weburl"):
                    lines.append(f"Website: {profile['weburl']}")
            else:
                lines.append("(No additional company profile data available for this ticker.)")
            text = "\n".join(lines)

            def update():
                company_text.config(state="normal")
                company_text.delete("1.0", "end")
                company_text.insert("1.0", text)
                company_text.config(state="disabled")

            popup.after(0, update)

        threading.Thread(target=load_company_info, daemon=True).start()

        # ---------------- Tab 2: Why it might rise ----------------
        why_tab = tk.Frame(notebook)
        notebook.add(why_tab, text="Why It Might Rise")
        why_text = tk.Text(why_tab, wrap="word", font=("Segoe UI", 10))
        why_text.pack(fill="both", expand=True, padx=10, pady=10)
        why_text.insert("1.0", "Generating explanation...")
        why_text.config(state="disabled")

        def fetch_and_show_explanation():
            explanation = call_ai_explain(record["context"])

            def update():
                why_text.config(state="normal")
                why_text.delete("1.0", "end")
                why_text.insert("1.0", explanation)
                why_text.config(state="disabled")

            popup.after(0, update)

        threading.Thread(target=fetch_and_show_explanation, daemon=True).start()

        # ---------------- Tab 3: Log a purchase ----------------
        log_tab = tk.Frame(notebook)
        notebook.add(log_tab, text="Log Purchase")

        form_frame = tk.Frame(log_tab)
        form_frame.pack(fill="x", padx=10, pady=10)

        tk.Label(form_frame, text="Amount bought (e.g. 10 shares or $500):").grid(
            row=0, column=0, sticky="w", pady=4
        )
        amount_entry = tk.Entry(form_frame, width=32)
        amount_entry.grid(row=0, column=1, pady=4, padx=6)

        tk.Label(form_frame, text="Price paid per share ($, optional):").grid(row=1, column=0, sticky="w", pady=4)
        price_entry = tk.Entry(form_frame, width=32)
        price_entry.grid(row=1, column=1, pady=4, padx=6)

        tk.Label(form_frame, text="Time of purchase:").grid(row=2, column=0, sticky="w", pady=4)
        time_entry = tk.Entry(form_frame, width=32)
        time_entry.insert(0, datetime.now().strftime("%Y-%m-%d %H:%M"))
        time_entry.grid(row=2, column=1, pady=4, padx=6)

        status_label = tk.Label(log_tab, text="", font=("Segoe UI", 9))
        status_label.pack(anchor="w", padx=10)

        tk.Label(
            log_tab,
            text="Price paid is optional but enables the Sell/Watch/Hold signal in \"Your Holdings\" below.",
            fg="#555555", font=("Segoe UI", 8, "italic"),
        ).pack(anchor="w", padx=10)

        history_label = tk.Label(log_tab, text="Logged purchases for this stock:", font=("Segoe UI", 9, "bold"))
        history_label.pack(anchor="w", padx=10, pady=(8, 0))
        history_text = tk.Text(log_tab, wrap="word", font=("Segoe UI", 9), height=10)
        history_text.pack(fill="both", expand=True, padx=10, pady=(4, 10))

        def refresh_history():
            entries = [e for e in load_purchase_log(self.username) if e["symbol"] == symbol]
            history_text.config(state="normal")
            history_text.delete("1.0", "end")
            if entries:
                for e in entries:
                    price_note = f" @ ${e['price_paid']}" if e.get("price_paid") else ""
                    history_text.insert("end", f"{e['time']} — {e['amount']}{price_note}  (logged {e['logged_at']})\n")
            else:
                history_text.insert("end", "No purchases logged yet for this stock.")
            history_text.config(state="disabled")

        def save_and_refresh():
            amount = amount_entry.get().strip()
            time_val = time_entry.get().strip()
            price_val_text = price_entry.get().strip()
            if not amount or not time_val:
                status_label.config(text="Please fill in the amount and time fields.", fg="red")
                return
            price_paid = None
            if price_val_text:
                try:
                    price_paid = float(price_val_text.replace("$", "").replace(",", ""))
                except ValueError:
                    status_label.config(text="Price paid must be a number (or leave it blank).", fg="red")
                    return
            if save_purchase_entry(self.username, symbol, amount, time_val, price_paid):
                status_label.config(text="Saved.", fg="green")
                amount_entry.delete(0, "end")
                price_entry.delete(0, "end")
                refresh_history()
            else:
                status_label.config(text="Failed to save -- see console for details.", fg="red")

        tk.Button(form_frame, text="Save Purchase", command=save_and_refresh).grid(
            row=3, column=0, columnspan=2, pady=8
        )

        refresh_history()


# ============================================================================
# MAIN
# ============================================================================

def _brook_worker_enabled_usernames():
    usernames = []
    for username in load_accounts():
        data = load_pools(username)
        if any(p.get("brook_enabled") for p in data.get("pools", [])):
            usernames.append(username)
    return usernames


def run_brook_worker():
    """Headless loop: keeps Brook scanning + trading with no GUI, so it can run
    on a machine/host that's always on (see --worker below). Reuses the exact
    same compute_ranked_scan/run_brook_for_pool the desktop app uses."""
    print(f"[brook worker] starting -- cycle interval {UPDATE_INTERVAL_SECONDS // 60} min. Ctrl+C to stop.")
    while True:
        try:
            usernames = _brook_worker_enabled_usernames()
            if not usernames:
                print("[brook worker] no Brook-enabled pools -- nothing to do this cycle.")
            else:
                scan = compute_ranked_scan()
                ranked_data = scan["top20"]
                price_lookup = {r["symbol"]: r["stats"]["price"] for r in ranked_data}
                for username in usernames:
                    for pool in load_pools(username).get("pools", []):
                        if pool.get("brook_enabled"):
                            ok, msg = run_brook_for_pool(username, pool["id"], ranked_data, price_lookup)
                            print(f"[brook worker] {username} / {pool['name']}: {msg}")
        except Exception as e:
            print(f"[brook worker] cycle failed: {e}")
        time.sleep(UPDATE_INTERVAL_SECONDS)


def main():
    if "--worker" in sys.argv:
        run_brook_worker()  # headless mode: no GUI, just keeps Brook trading -- see run_brook_worker()
        return
    login = LoginWindow()
    username = login.run()
    if not username:
        return  # login window was closed without a successful login

    root = tk.Tk()
    ScreenerApp(root, username)
    root.mainloop()


if __name__ == "__main__":
    main()
