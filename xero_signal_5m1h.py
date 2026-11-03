"""
XERO AI SOFTWARE — 5-MINUTE + 1-HOUR SIGNAL MONITOR   (signals only — NO trading)
=========================================================================
Dashboard : http://localhost:8050

5-MIN + 1-HOUR
  The dashboard shows the 5-minute chart on the LEFT and the 1-hour chart on the RIGHT.
  Each timeframe has its OWN candles and its OWN MAP / SIGNAL / IntBB / ExtBB calculation
  (the same MT5-exact maths, run separately on that timeframe's candles), its own signals,
  exits, ignored / repainted / confirmed events and its own CSV logs
  (<symbol>_candles.csv for the 5-minute, <symbol>_1h_candles.csv for the 1-hour).
  Telegram: the 5-minute and the 1-hour give their OWN signals, independently. ONE short message per
  entry and one per exit, saying which time frame it came from, e.g.
      "Crash 500 Index BUY from 1 hour time frame"      "Crash 500 Index BUY from 5 mins time frame"
      "Crash 500 Index EXIT BUY from 1 hour time frame"
  Nothing is sent for INVALID, BLOCKED or IGNORED rows (they stay on the dashboard).

PURPOSE
  Check that the strategy logic gives the same signals as your MT5 chart,
  before going back to the two-timeframe trading bot.

MT5-EXACT INDICATOR (this version)
  Your MQL4 indicator REPAINTS: its moving average (icTma) also looks at NEWER
  candles, and MT5 recalculates the last ~90 candles on every tick. So the line
  you see for an older candle keeps changing until ~33 newer candles exist.
  This program reproduces that calculation exactly (MAP, SIGNAL, IntBB) so its
  lines match your MT5 chart candle for candle, including the repainting:
    * Bar 0 = the candle still forming (MT5's current candle), bar 1 = last closed.
    * The dashboard shows "Bar 0" and "Bar 1" numbers you can read against MT5's
      Data Window (Ctrl+D) while looking at the same candles.
    * Bands follow the MQL4 setting BB_on_DCE_MA: with the default "DCE" the
      bands are calculated on the SIGNAL line (see BB_ON_SIGNAL below).

WHAT IT DOES
  * Streams REAL 5-minute candles from Deriv's public WebSocket
    (no login, no token, no trading possible). Nothing is built from ticks.
  * Gives signals only:
        BUY    MAP and SIGNAL both go below IntBB lower, MAP curves up, both are
               back inside, MAP rising, and the candle closes ABOVE external BB upper
        SELL   mirror image, candle closes BELOW external BB lower
        (1-HOUR: the External BB is removed - no band, no price filter. Only the
         MAP / SIGNAL / IntBB rules above decide its BUY / SELL.)
        EXIT   BUY  exits when MAP/SIGNAL cross while both are above the upper band
               SELL exits when they cross while both are below the lower band
        A second BUY/SELL while the first is still open (no exit yet) is shown as IGNORED.
        After an EXIT the next valid setup is a real signal in either direction.
        1-HOUR invalid: a 1-HOUR BUY/SELL is cancelled on an inside cross, a pull-out back out of
        the band, or by falling back inside after reaching the far band (INVALID BUY / SELL).
        INDEPENDENT SIGNALS: the 5-MIN and the 1-HOUR each give their own BUY / SELL and their own
        exit; neither waits for the other. (The old rule "a 5-MIN signal counts only while a 1-HOUR
        signal in the same direction is valid, otherwise BLOCKED" is still in the code and is
        switched off: DUAL_TF_GATE = False.)
        5-MIN EXIT: only the 5-MIN's OWN lines end its BUY / SELL - MAP and SIGNAL reach the
        upper band and cross each other while both are outside it (BUY), or the same below the
        lower band (SELL). The 1-HOUR ending or being cancelled does NOT exit a 5-MIN signal.
  * A live signal is judged when its candle closes, on the lines MT5 shows at that
    moment. Because the lines repaint, a signal can later disappear from MT5's
    history. The program tells you:
        REPAINTED AWAY  the signal no longer appears on the recalculated lines
        CONFIRMED       34+ candles later it is still there (the lines are final)
  * On start it replays the history Deriv sends, using the FINAL (repainted) lines
    like MT5's history chart. Those are marked HIST (no Telegram).

COMPARING WITH MT5
  * Times shown are UTC + TIME_OFFSET_HOURS. Set it so they match your MT5 clock.
  * Compare candle open/high/low/close first, then Bar 0 / Bar 1 values.
  * Files written to ./xero_signal_logs/ :
        <symbol>_candles.csv  every candle with MAP, SIGNAL, IntBB, ExtBB, events
        signals.csv           every BUY / SELL / EXIT / INVALID / BLOCKED / IGNORED / REPAINTED / CONFIRMED

Requirements:
    pip install websocket-client plotly dash dash-bootstrap-components requests
"""

import os
import io
import signal
import csv
import json
import time
import math
import itertools
import threading
import contextlib
import requests
import websocket
from collections import deque
from datetime import datetime, timedelta, timezone

import plotly.graph_objects as go
import dash
from dash import dcc, html
from dash.dependencies import Input, Output, State
import dash_bootstrap_components as dbc


def get_ts():
    return datetime.now().strftime("%H:%M:%S")


def get_dt():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


SIGNAL_LABEL = {'BUY': 'LONG BUY', 'SELL': 'SHORT SELL'}
SIGNAL_ICON  = {'BUY': '▲',        'SELL': '▼'}

# ============================================================
# CONFIGURATION
# ============================================================

# Deriv public market-data WebSocket (no authentication needed)
WS_URL        = "wss://api.derivws.com/trading/v1/options/ws/public"
# Candle sizes in seconds. Deriv accepts: 60, 120, 180, 300, 600, 900, 1800, 3600, 7200, 14400, 28800, 86400.
GRANULARITY     = 300    # LOWER time frame (the entry): 300 = 5 minutes
GRANULARITY_HTF = 3600   # HIGHER time frame (second chart): 3600 = 1 hour
ENABLE_HTF      = True   # set False to run the lower time frame monitor only
HISTORY_COUNT = 800     # candles requested at start (the MT5 calculation needs ~400)

# Shift the times shown by this many hours (UTC + offset) to match your MT5 clock
TIME_OFFSET_HOURS = 0

# Leave empty to watch every symbol below, or list a few, e.g. ["R_50", "1HZ30V"]
ONLY_SYMBOLS = []

LOG_DIR = "xero_signal_logs"

# Deriv recommends a `ping` request every 30-60 s so proxies / firewalls do not drop an idle connection
KEEPALIVE_SECONDS = 30

# Telegram alerts for live signals (optional; environment variables override)
TELEGRAM_TOKEN   = os.environ.get("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

# MT5 input BB_on_DCE_MA: in the MQL4 code `if(BB_on_DCE_MA)` is FALSE for "DCE" (the default),
# which puts the bands on the SIGNAL line. Set False if your MT5 input says "DCE smoothed"
# (bands on MAP).
BB_ON_SIGNAL    = True
MT5_REPLAY_BARS = 250   # how many candles are re-judged each time a candle closes

# After an EXIT, is the next setup in the SAME direction a real signal?
#   False (default): yes. A BUY/SELL is ignored only while the previous one is still open (no exit yet).
#   True           : no. After a BUY (even once it has exited) wait for a SELL, and vice versa.
REQUIRE_OPPOSITE_AFTER_EXIT = False

# ---- MAP parameters (MQL4 DCE) ----
PERIOD1       = 34
PERIOD2       = 22
PERIOD3       = 18
PERIOD4       = 33
PERIOD5       = 29
PERIOD6       = 14
SIGNAL_PERIOD = 5

# ---- Internal Bollinger Bands on MAP ----
BB_PERIOD    = 89
BB_DEVIATION = 1.0

# ---- External Bollinger Band on PRICE (candle closes) — entry filter ----
EXT_BB_PERIOD    = 60
EXT_BB_DEVIATION = 0.400

# The 1-HOUR (higher timeframe) does NOT use the External BB at all: no band on the chart and
# no price filter in the signal. Its BUY / SELL depend only on MAP / SIGNAL / IntBB (rules a-e).
# The 5-MIN keeps its External BB entry filter exactly as before.
HTF_USE_EXT_BB = False

# 1-HOUR only: a BUY / SELL is declared INVALID the moment MAP and SIGNAL cross back AGAINST it
# while both lines are still inside the IntBB bands and the move never reached the far band
# (a "whipsaw" / inside-band cross). The signal is cancelled right away, so the next real setup
# is accepted as a new signal instead of being shown as IGNORED. The 5-MIN is not affected.
HTF_WHIPSAW_INVALIDATION = True

# DUAL TIME FRAME GATE (currently OFF = the 5-MIN and the 1-HOUR give their own signals independently).
# True : a 5-MIN BUY (SELL) is a real signal only while a 1-HOUR BUY (SELL) is still valid.
# A 1-HOUR signal is valid from its candle close until it is cancelled (inside cross / pull-out /
# fell back inside) or ends normally (MAP and SIGNAL cross outside the far band). A 5-MIN signal
# that comes when no matching 1-HOUR signal is valid is shown as BLOCKED (not hidden).
# A 5-MIN candle that closes at the very same moment as a 1-HOUR candle is judged on the 1-HOUR
# state as it was BEFORE that 1-HOUR candle closed (so the result never depends on which message
# Deriv delivers first). Needs ENABLE_HTF = True.
DUAL_TF_GATE = False
HISTORY_WAIT_HTF_SECONDS = 25   # 5-MIN history waits this long for the 1-HOUR history, then goes ahead

# ---- Minimum excursion depth ----
MIN_EXCURSION_DEPTH_FRAC = 0.05

MIN_CANDLES       = max(PERIOD1, PERIOD2, PERIOD3, PERIOD4,
                        PERIOD5, PERIOD6, BB_PERIOD) + 30
PRICE_WINDOW_SIZE = MIN_CANDLES + 100
MAP_WINDOW_SIZE   = BB_PERIOD + SIGNAL_PERIOD + 50

# ============================================================
# SYMBOL LIST
# ============================================================

TRADING_SYMBOLS = [
    {"symbol": "R_10",    "name": "Volatility 10 Index"},
    {"symbol": "R_25",    "name": "Volatility 25 Index"},
    {"symbol": "R_50",    "name": "Volatility 50 Index"},
    {"symbol": "R_75",    "name": "Volatility 75 Index"},
    {"symbol": "R_100",   "name": "Volatility 100 Index"},
    {"symbol": "1HZ10V",  "name": "Volatility 10 (1s) Index"},
    {"symbol": "1HZ15V",  "name": "Volatility 15 (1s) Index"},
    {"symbol": "1HZ25V",  "name": "Volatility 25 (1s) Index"},
    {"symbol": "1HZ30V",  "name": "Volatility 30 (1s) Index"},
    {"symbol": "1HZ50V",  "name": "Volatility 50 (1s) Index"},
    {"symbol": "1HZ75V",  "name": "Volatility 75 (1s) Index"},
    {"symbol": "1HZ90V",  "name": "Volatility 90 (1s) Index"},
    {"symbol": "1HZ100V", "name": "Volatility 100 (1s) Index"},
    {"symbol": "JD10",    "name": "Jump 10 Index"},
    {"symbol": "JD25",    "name": "Jump 25 Index"},
    {"symbol": "JD50",    "name": "Jump 50 Index"},
    {"symbol": "JD75",    "name": "Jump 75 Index"},
    {"symbol": "JD100",   "name": "Jump 100 Index"},
    {"symbol": "stpRNG",  "name": "Step Range Index"},
    {"symbol": "stpRNG2", "name": "Step Range Index 2"},
    {"symbol": "stpRNG3", "name": "Step Range Index 3"},
    {"symbol": "stpRNG4", "name": "Step Range Index 4"},
    {"symbol": "stpRNG5", "name": "Step Range Index 5"},
    {"symbol": "CRASH500",  "name": "Crash 500 Index"},
    {"symbol": "CRASH1000", "name": "Crash 1000 Index"},
    {"symbol": "CRASH600",  "name": "Crash 600 Index"},
    {"symbol": "CRASH900",  "name": "Crash 900 Index"},
    {"symbol": "BOOM1000",  "name": "Boom 1000 Index"},
    {"symbol": "BOOM500",   "name": "Boom 500 Index"},
    {"symbol": "BOOM600",   "name": "Boom 600 Index"},
]


def monitored_symbols():
    allowed = [s['symbol'] for s in TRADING_SYMBOLS]
    if ONLY_SYMBOLS:
        return [s for s in ONLY_SYMBOLS if s in allowed] or allowed
    return allowed


def _gran_short(g):
    """300 -> '5-MIN', 3600 -> '1-HOUR'"""
    return f"{g // 3600}-HOUR" if g % 3600 == 0 else f"{g // 60}-MIN"


def _gran_words(g):
    """300 -> '5 mins', 3600 -> '1 hour'  (used in the Telegram text)"""
    if g % 3600 == 0:
        h = g // 3600
        return f"{h} hour" + ("" if h == 1 else "s")
    return f"{g // 60} mins"


def _gran_tag(g):
    """300 -> '5m', 3600 -> '1h'  (used in file names)"""
    return f"{g // 3600}h" if g % 3600 == 0 else f"{g // 60}m"


HTF_SUFFIX = "_" + _gran_tag(GRANULARITY_HTF)      # '_1h'  - added to a symbol to name its higher-time-frame stream
LTF_NAME   = _gran_short(GRANULARITY)              # '5-MIN'
HTF_NAME   = _gran_short(GRANULARITY_HTF)          # '1-HOUR'


def tf_key(symbol, gran):
    """State key for one symbol on one timeframe. The lower time frame keeps the plain symbol, the higher one gets a suffix."""
    return f"{symbol}{HTF_SUFFIX}" if gran == GRANULARITY_HTF else symbol


def split_key(key):
    """Inverse of tf_key: returns (real symbol, granularity in seconds)."""
    if key.endswith(HTF_SUFFIX):
        return key[:-len(HTF_SUFFIX)], GRANULARITY_HTF
    return key, GRANULARITY


def is_htf(key):
    """True for the higher timeframe stream."""
    return str(key).endswith(HTF_SUFFIX)


def uses_ext_bb(key):
    """True when this stream still uses the External BB (always for the lower time frame; for the higher one only if HTF_USE_EXT_BB)."""
    return HTF_USE_EXT_BB or not str(key).endswith(HTF_SUFFIX)


def tf_label(gran):
    return _gran_short(gran)


# ============================================================
# RUNTIME STATE
# ============================================================

symbol_data    = {}
data_lock      = threading.RLock()
running        = True
ws_app         = None

dashboard_data = {
    'scratch':       {},   # symbol -> 1-row scratch deque the strategy code writes to
    'candles':       {},   # (unused)
    'signals':       {},   # symbol -> deque of events, newest first
}

conn = {'connected': False, 'fmt': None, 'last_msg': 0.0, 'last_error': '', 'connects': 0, 'opened_at': 0.0}
req_counter = itertools.count(1)
req_map     = {}     # req_id -> symbol
sub_map     = {}     # subscription id -> symbol
probe       = {'event': threading.Event(), 'ok': False, 'error': None, 'req_id': None}
csv_lock    = threading.Lock()

# ============================================================
# STRATEGY CODE — copied unchanged from the trading bot
# ============================================================

def get_symbol_name(symbol):
    for s in TRADING_SYMBOLS:
        if s['symbol'] == symbol:
            return s['name']
    return symbol


def ic_tma(prices_list, period):
    n = len(prices_list)
    if n < period:
        return None
    sumw  = period + 1
    total = sumw * prices_list[-1]
    for j in range(1, period):
        k   = period - j + 1   # MQL4: k starts at `period` for j=1 (was period - j, off by one)
        idx = n - 1 - j
        sumw  += k
        total += k * (prices_list[idx] if idx >= 0 else prices_list[0])
    return total / sumw


def compute_map(prices_list):
    a1 = ic_tma(prices_list, PERIOD2)
    a2 = ic_tma(prices_list, PERIOD1)
    a3 = ic_tma(prices_list, PERIOD4)
    a4 = ic_tma(prices_list, PERIOD3)
    a5 = ic_tma(prices_list, PERIOD6)
    a6 = ic_tma(prices_list, PERIOD5)
    if None in (a1, a2, a3, a4, a5, a6):
        return None
    return (a1 - a2) + (a3 - a4) + (a5 - a6)


def calc_sma(dq, period):
    lst = list(dq)
    if len(lst) < period:
        return None
    return sum(lst[-period:]) / period


def calc_bb(values_list, period, deviation):
    lst = list(values_list)
    if len(lst) < period:
        return None, None
    seg      = lst[-period:]
    mean     = sum(seg) / period
    variance = sum((x - mean) ** 2 for x in seg) / period
    std      = math.sqrt(variance)
    return mean + deviation * std, mean - deviation * std


def _make_tf_state(label='HTF'):
    return {
        'label':        label,
        'prev_rel':     None,    # sign of (MAP - SIGNAL) on the previous candle
        'wait_logged':  False,   # MAP is back inside, waiting for SIGNAL
        'candle_count': 0,
        'close_prices': deque(maxlen=PRICE_WINDOW_SIZE),
        'map_window':   deque(maxlen=MAP_WINDOW_SIZE),

        'prev_map':   None,
        'prev_bb_up': None,
        'prev_bb_dn': None,
        'prev_sig':   None,
        'prev_close': None,

        'warming_up': True,

        'last_map':        None,
        'last_sig':        None,
        'last_bb_up':      None,
        'last_bb_dn':      None,

        'excursion_state':   None,
        'excursion_candles': 0,
        'excursion_extreme': None,
        'excursion_curved':  False,
        'excursion_both_out': False,  # MAP and SIGNAL were outside the band on the SAME candle
    }


def _process_candle(tf, candle, symbol, dashboard_key, ts, inject=None):
    """
    Process one closed tick-based candle for ONE engine (HTF gate or LTF trigger).
    The indicator maths and the excursion logic are identical for both engines.

    Returns (fire_result, cross_event)
      fire_result : 'BUY' / 'SELL' / None
          BUY  = MAP excursion below IntBB lower, curve, then BOTH MAP and SIGNAL
                 are back inside the band (MAP rising on that candle).
          SELL = mirror image above IntBB upper.
      cross_event : 'CROSS_ABOVE_UPPER' / 'CROSS_BELOW_LOWER' / None
          MAP and SIGNAL crossed each other while BOTH lines were outside the
          upper / lower band. The HTF gate uses this as the window exit.
    """
    lbl         = tf.get('label', 'HTF')
    close_price = float(candle['close'])

    tf['close_prices'].append(close_price)

    close_list = list(tf['close_prices'])

    # External Bollinger Band on price (period 60, deviation 0.4): entry filter
    use_ext = uses_ext_bb(symbol)
    if use_ext:
        ext_up, ext_dn = calc_bb(close_list, EXT_BB_PERIOD, EXT_BB_DEVIATION)
    else:
        ext_up = ext_dn = None      # 1-HOUR: External BB removed
    tf['last_ext_up'] = ext_up
    tf['last_ext_dn'] = ext_dn

    if inject is not None:
        # MT5-exact mode: MAP / SIGNAL / IntBB arrive precomputed from the MQL4 formulas
        map_val, sig_val = inject['map'], inject['sig']
        bb_up, bb_dn     = inject['bb_up'], inject['bb_dn']
    else:
        map_val = compute_map(close_list) if len(close_list) >= PERIOD1 else None

        if map_val is not None:
            tf['map_window'].append(map_val)
            mlen    = len(tf['map_window'])
            sig_val = calc_sma(tf['map_window'], SIGNAL_PERIOD) if mlen >= SIGNAL_PERIOD else None
            bb_up, bb_dn = (
                calc_bb(tf['map_window'], BB_PERIOD, BB_DEVIATION)
                if mlen >= BB_PERIOD else (None, None)
            )
        else:
            sig_val = bb_up = bb_dn = None

    tf['last_map']       = map_val
    tf['last_sig']       = sig_val
    tf['last_bb_up']     = bb_up
    tf['last_bb_dn']     = bb_dn

    if lbl == 'HTF' and map_val is not None and tf['candle_count'] % 10 == 0:
        if bb_up is not None:
            print(f"   [{symbol}] {lbl} MAP={map_val:.4f}  "
                  f"BB↑={bb_up:.4f}  BB↓={bb_dn:.4f}")
        else:
            print(f"   [{symbol}] {lbl} MAP={map_val:.4f}  BB=warming")

    all_ready = None not in (map_val, sig_val, bb_up, bb_dn)
    if all_ready and tf['warming_up']:
        tf['warming_up'] = False
        print(f"[{get_ts()}] [{symbol}] {lbl} READY — {tf['candle_count']} candles")
    elif tf['candle_count'] % 20 == 0 and tf['warming_up'] and lbl == 'HTF':
        print(f"[{get_ts()}] [{symbol}] {lbl} warming  "
              f"candles:{tf['candle_count']}/{MIN_CANDLES}")

    # ── MAP / SIGNAL cross detection (used for the HTF exit) ─────────────
    cross_event = None
    if map_val is not None and sig_val is not None:
        diff = map_val - sig_val
        rel  = 1 if diff > 0 else (-1 if diff < 0 else 0)
        if rel != 0:
            prev_rel = tf.get('prev_rel')
            if (prev_rel is not None and rel != prev_rel
                    and not tf['warming_up']
                    and bb_up is not None and bb_dn is not None):
                if map_val > bb_up and sig_val > bb_up:
                    cross_event = 'CROSS_ABOVE_UPPER'
                elif map_val < bb_dn and sig_val < bb_dn:
                    cross_event = 'CROSS_BELOW_LOWER'
            tf['prev_rel'] = rel

    # Store in dashboard
    dashboard_data[dashboard_key][symbol].append({
        'time':       ts,
        'open':       float(candle['open']),
        'high':       float(candle['high']),
        'low':        float(candle['low']),
        'close':      float(candle['close']),
        'map':        map_val,
        'signal':     sig_val,
        'bb_up':      bb_up,
        'bb_dn':      bb_dn,
        'ext_up':     ext_up,
        'ext_mid':    ((ext_up + ext_dn) / 2) if ext_up is not None else None,
        'ext_dn':     ext_dn,
    })

    prev_map   = tf['prev_map']
    prev_bb_up = tf['prev_bb_up']
    prev_bb_dn = tf['prev_bb_dn']

    if map_val is not None:
        tf['prev_map']   = map_val
        tf['prev_bb_up'] = bb_up
        tf['prev_bb_dn'] = bb_dn
    if sig_val is not None:
        tf['prev_sig'] = sig_val
    tf['prev_close'] = close_price

    if tf['warming_up']:
        return None, cross_event
    if None in (map_val, bb_up, bb_dn, prev_map, prev_bb_up, prev_bb_dn):
        return None, cross_event

    fire_result = None
    state       = tf['excursion_state']

    if state is None:
        # Start a BUY excursion when MAP drops below the lower band
        if map_val < bb_dn:
            tf['excursion_state']   = 'below'
            tf['excursion_both_out'] = (sig_val is not None and sig_val < bb_dn)
            tf['excursion_candles'] = 1
            tf['excursion_extreme'] = map_val
            tf['excursion_curved']  = False
            tf['wait_logged']       = False
        # Start a SELL excursion when MAP rises above the upper band
        elif map_val > bb_up:
            tf['excursion_state']   = 'above'
            tf['excursion_both_out'] = (sig_val is not None and sig_val > bb_up)
            tf['excursion_candles'] = 1
            tf['excursion_extreme'] = map_val
            tf['excursion_curved']  = False
            tf['wait_logged']       = False

    elif state == 'below':
        band_width = (bb_up - bb_dn) if (bb_up and bb_dn) else 0
        min_depth  = band_width * MIN_EXCURSION_DEPTH_FRAC

        map_out = map_val < bb_dn
        sig_out = (sig_val is not None) and (sig_val < bb_dn)

        if map_out:
            tf['wait_logged'] = False
            if sig_out:
                tf['excursion_both_out'] = True
            tf['excursion_candles'] += 1
            if map_val < tf['excursion_extreme']:
                tf['excursion_extreme'] = map_val
            elif map_val > prev_map:
                depth_cleared = bb_dn - tf['excursion_extreme']
                if depth_cleared >= min_depth:
                    tf['excursion_curved'] = True
        elif sig_out:
            # MAP is back inside the band but SIGNAL is still outside:
            # the excursion stays open. Fire only once SIGNAL is inside too.
            if not tf['wait_logged']:
                tf['wait_logged'] = True
                print(f"   [{symbol}] {lbl} ▲ BUY — MAP back inside, "
                      f"waiting for SIGNAL to re-enter lower band")
        else:
            # BOTH MAP and SIGNAL are back inside the lower band
            curved = tf['excursion_curved']
            rising = map_val > prev_map
            ext_ok = True if not use_ext else ((ext_up is not None) and (close_price > ext_up))
            both_out = tf['excursion_both_out']
            if curved and rising and ext_ok and both_out:
                print(f"   [{symbol}] {lbl} ▲ LONG BUY FIRE  "
                      f"MAP={map_val:.4f}  SIG={sig_val:.4f}  BB↓={bb_dn:.4f}  "
                      f"exc={tf['excursion_candles']}c  trough={tf['excursion_extreme']:.4f}  "
                      f"Price={close_price:.5f}")
                fire_result = 'BUY'
            else:
                reasons = []
                if not curved: reasons.append("no curve (too shallow or still falling)")
                if not rising: reasons.append("not rising on re-entry")
                if not both_out: reasons.append("SIGNAL never went outside the band together with MAP")
                if not ext_ok:
                    reasons.append("price not above external BB↑ "
                                   + (f"({close_price:.5f} <= {ext_up:.5f})" if ext_up is not None else "(band not ready)"))
                print(f"   [{symbol}] {lbl} ▲ LONG BUY re-entry REJECTED — {', '.join(reasons)}")
            tf['excursion_state']   = None
            tf['excursion_both_out'] = False
            tf['excursion_candles'] = 0
            tf['excursion_extreme'] = None
            tf['excursion_curved']  = False
            tf['wait_logged']       = False

    elif state == 'above':
        band_width = (bb_up - bb_dn) if (bb_up and bb_dn) else 0
        min_depth  = band_width * MIN_EXCURSION_DEPTH_FRAC

        map_out = map_val > bb_up
        sig_out = (sig_val is not None) and (sig_val > bb_up)

        if map_out:
            tf['wait_logged'] = False
            if sig_out:
                tf['excursion_both_out'] = True
            tf['excursion_candles'] += 1
            if map_val > tf['excursion_extreme']:
                tf['excursion_extreme'] = map_val
            elif map_val < prev_map:
                depth_cleared = tf['excursion_extreme'] - bb_up
                if depth_cleared >= min_depth:
                    tf['excursion_curved'] = True
        elif sig_out:
            if not tf['wait_logged']:
                tf['wait_logged'] = True
                print(f"   [{symbol}] {lbl} ▼ SELL — MAP back inside, "
                      f"waiting for SIGNAL to re-enter upper band")
        else:
            # BOTH MAP and SIGNAL are back inside the upper band
            curved  = tf['excursion_curved']
            falling = map_val < prev_map
            ext_ok  = True if not use_ext else ((ext_dn is not None) and (close_price < ext_dn))
            both_out = tf['excursion_both_out']
            if curved and falling and ext_ok and both_out:
                print(f"   [{symbol}] {lbl} ▼ SHORT SELL FIRE  "
                      f"MAP={map_val:.4f}  SIG={sig_val:.4f}  BB↑={bb_up:.4f}  "
                      f"exc={tf['excursion_candles']}c  peak={tf['excursion_extreme']:.4f}  "
                      f"Price={close_price:.5f}")
                fire_result = 'SELL'
            else:
                reasons = []
                if not curved:  reasons.append("no curve (too shallow or still rising)")
                if not falling: reasons.append("not falling on re-entry")
                if not both_out: reasons.append("SIGNAL never went outside the band together with MAP")
                if not ext_ok:
                    reasons.append("price not below external BB↓ "
                                   + (f"({close_price:.5f} >= {ext_dn:.5f})" if ext_dn is not None else "(band not ready)"))
                print(f"   [{symbol}] {lbl} ▼ SHORT SELL re-entry REJECTED — {', '.join(reasons)}")
            tf['excursion_state']   = None
            tf['excursion_both_out'] = False
            tf['excursion_candles'] = 0
            tf['excursion_extreme'] = None
            tf['excursion_curved']  = False
            tf['wait_logged']       = False

    return fire_result, cross_event


# ============================================================
# TELEGRAM (signals only)
# ============================================================

def send_telegram(message: str):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    def _send():
        try:
            url     = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
            payload = {"chat_id": TELEGRAM_CHAT_ID, "text": message, "parse_mode": "HTML"}
            r = requests.post(url, json=payload, timeout=10)
            if r.status_code == 200:
                print(f"[{get_ts()}] Telegram sent ✓")
            else:
                print(f"[{get_ts()}] Telegram error: {r.text}")
        except Exception as e:
            print(f"[{get_ts()}] Telegram exception: {e}")
    threading.Thread(target=_send, daemon=True).start()


def _run_label():
    if os.environ.get("GITHUB_ACTIONS") == "true":
        return f"GitHub Actions (run #{os.environ.get('GITHUB_RUN_NUMBER', '?')})"
    return "local machine"


def _notify_status(title, body):
    send_telegram(f"🤖 <b>XERO 5M/1H MONITOR — {title}</b>\n━━━━━━━━━━━━━━━━━━━━\n{body}\nRunning on: {_run_label()}\nTime: {get_dt()}")


# ============================================================
# PER-SYMBOL STATE
# ============================================================

def init_symbol(symbol, gran=None):
    if symbol in symbol_data:
        return
    symbol_data[symbol] = {
        'tf':                    _make_tf_state(LTF_NAME),
        'closed':                deque(maxlen=3000),   # closed candles, oldest -> newest
        'pending_check':         [],      # live signals waiting to be confirmed / repainted away
        'forming':               None,    # bar 0: candle still being built
        'last_closed_open_time': None,
        'active':                None,    # 'BUY' / 'SELL' until its exit cross
        'last_dir':              None,    # direction of the last accepted signal
        'active_since':          None,    # when the open signal fired
        'wh_prev_rel':           None,    # whipsaw check (1-HOUR): sign of MAP - SIGNAL on the previous candle
        'wh_outer':              False,   # whipsaw check (1-HOUR): the move already reached the far band
        'windows':               [],      # 1-HOUR only: when each 1-HOUR signal was valid {dir, since, start, end}
        'csv_ready':             False,
        'live_candles':          0,
        'gran':                  gran or GRANULARITY,   # seconds per candle of this stream
        'base':                  split_key(symbol)[0],  # the real Deriv symbol
    }
    dashboard_data['scratch'][symbol]       = deque(maxlen=1)
    dashboard_data['signals'][symbol]       = deque(maxlen=300)


def _open_dt(open_time):
    """Candle open time as a naive datetime: UTC + TIME_OFFSET_HOURS."""
    return (datetime.fromtimestamp(int(open_time), tz=timezone.utc).replace(tzinfo=None)
            + timedelta(hours=TIME_OFFSET_HOURS))


def _fmt_t(dt):
    return dt.strftime("%Y-%m-%d %H:%M")


# ============================================================
# CSV LOGS
# ============================================================

def _fnum(x):
    return "" if x is None else repr(float(x))


def _csv_path(name):
    return os.path.join(LOG_DIR, name)


def _init_csv(symbol):
    os.makedirs(LOG_DIR, exist_ok=True)
    with csv_lock:
        with open(_csv_path(f"{symbol}_candles.csv"), "w", newline="") as f:
            csv.writer(f).writerow(
                ["time", "open_time_epoch", "open", "high", "low", "close", "map", "signal",
                 "intbb_up", "intbb_dn", "extbb_up", "extbb_mid", "extbb_dn", "events", "historical"])
        sig_path = _csv_path("signals.csv")
        if not os.path.exists(sig_path):
            with open(sig_path, "w", newline="") as f:
                csv.writer(f).writerow(
                    ["time", "symbol", "event", "close", "map", "signal", "intbb_up", "intbb_dn",
                     "extbb_up", "extbb_dn", "note", "historical"])


def _write_candle_csv(symbol, c, ts, vals, kinds, historical):
    eu, ed = vals.get('ext_up'), vals.get('ext_dn')
    mid = ((eu + ed) / 2) if eu is not None and ed is not None else None
    with csv_lock:
        with open(_csv_path(f"{symbol}_candles.csv"), "a", newline="") as f:
            csv.writer(f).writerow([
                _fmt_t(ts), c['open_time'], _fnum(c['open']), _fnum(c['high']), _fnum(c['low']),
                _fnum(c['close']), _fnum(vals.get('map')), _fnum(vals.get('sig')),
                _fnum(vals.get('bb_up')), _fnum(vals.get('bb_dn')),
                _fnum(eu), _fnum(mid), _fnum(ed), " | ".join(kinds), 1 if historical else 0])


def _write_signal_csv(ev):
    with csv_lock:
        with open(_csv_path("signals.csv"), "a", newline="") as f:
            csv.writer(f).writerow([
                _fmt_t(ev['ts']), ev['symbol'], ev['kind'], _fnum(ev['close']), _fnum(ev['map']),
                _fnum(ev['sig']), _fnum(ev['bb_up']), _fnum(ev['bb_dn']),
                _fnum(ev['ext_up']), _fnum(ev['ext_dn']), ev['note'], 1 if ev['historical'] else 0])


# ============================================================
# SIGNAL LOGIC — signals only, nothing is ever traded
# ============================================================

def _emit(symbol, sd, kind, c, ts, note, historical, vals):
    ev = {
        'ts': ts, 'symbol': symbol, 'kind': kind, 'close': c['close'],
        'map': vals.get('map'), 'sig': vals.get('sig'),
        'bb_up': vals.get('bb_up'), 'bb_dn': vals.get('bb_dn'),
        'ext_up': vals.get('ext_up'), 'ext_dn': vals.get('ext_dn'),
        'note': note, 'historical': historical,
    }
    dashboard_data['signals'][symbol].appendleft(ev)
    _write_signal_csv(ev)

    if historical:
        return ev

    base_sym, g_ = split_key(symbol)
    name = get_symbol_name(base_sym) + f"  [{tf_label(g_)}]"
    base = kind.split()[-1]
    if kind in ('BUY', 'SELL'):
        head = f"🟢 {SIGNAL_ICON[kind]} {SIGNAL_LABEL[kind]} SIGNAL"
    elif kind.startswith('EXIT'):
        head = f"🚪 EXIT {SIGNAL_LABEL[base]}"
    elif kind.startswith('INVALID'):
        head = f"⛔ {SIGNAL_LABEL[base]} signal INVALID (whipsaw)"
    elif kind.startswith('BLOCKED'):
        head = f"🚫 {SIGNAL_LABEL[base]} signal BLOCKED (no valid 1-HOUR {SIGNAL_LABEL[base]})"
    elif kind.startswith('REPAINTED'):
        head = f"♻ {SIGNAL_LABEL[base]} signal REPAINTED AWAY"
    elif kind.startswith('CONFIRMED'):
        head = f"✅ {SIGNAL_LABEL[base]} signal CONFIRMED (lines are final)"
    else:
        head = f"⚪ {SIGNAL_LABEL[base]} ignored"
    print(f"[{get_ts()}] [{symbol}] {head}  candle={_fmt_t(ts)}  close={c['close']}  "
          f"MAP={_fnum(ev['map'])}  SIG={_fnum(ev['sig'])}  — {note}")

    # Telegram: every entry and every exit of EITHER time frame, as one short line that names the time frame,
    # e.g. "Crash 500 Index BUY from 1 hour time frame". Nothing for INVALID / BLOCKED / IGNORED / REPAINTED rows.
    if kind in ('BUY', 'SELL') or kind.startswith('EXIT'):
        send_telegram(f"{get_symbol_name(base_sym)} {kind} from {_gran_words(g_)} time frame")
    return ev


def _htf_sync_windows(sd, ts):
    """1-HOUR only: keep a time record of when a BUY / SELL was valid (from its candle close until it ended)."""
    end_t = ts + timedelta(seconds=sd['gran'])
    w = sd['windows']
    if w and w[-1]['end'] is None and (sd['active'] != w[-1]['dir'] or sd['active_since'] != w[-1]['since']):
        w[-1]['end'] = end_t
    if sd['active'] and (not w or w[-1]['end'] is not None):
        w.append({'dir': sd['active'], 'since': sd['active_since'], 'start': end_t, 'end': None})
    if len(w) > 500:
        del w[:-500]


def _htf_permits(key, direction, tc):
    """
    Does a valid 1-HOUR signal in this direction exist at time tc (the close time of the 5-MIN candle)?
    Returns (True, window) / (False, why).
    """
    base = split_key(key)[0]
    s5 = symbol_data.get(tf_key(base, GRANULARITY_HTF))
    if s5 is None or s5['last_closed_open_time'] is None:
        return False, "the 1-HOUR candles are not loaded yet"
    for w in reversed(s5['windows']):
        if w['dir'] == direction and w['start'] < tc and (w['end'] is None or tc <= w['end']):
            return True, w
    past = [w for w in s5['windows'] if w['dir'] == direction and w['start'] < tc]
    if past:
        return False, (f"no valid 1-HOUR {direction}: the last one (from {_fmt_t(past[-1]['since'])}) "
                       f"ended at {_fmt_t(past[-1]['end'])}")
    return False, f"no valid 1-HOUR {direction} yet"


def _rel(m, s_):
    return 1 if m > s_ else (-1 if m < s_ else 0)


def _whipsaw_check(symbol, sd, c, ts, historical, vals, kinds):
    """
    1-HOUR only. While a BUY (SELL) is open and neither line has reached the far band since the
    signal, it is INVALID immediately and is cancelled when either happens:
      1) INSIDE CROSS - MAP and SIGNAL cross back against it (MAP falls below SIGNAL after a BUY /
         rises above SIGNAL after a SELL) while BOTH lines are still inside the IntBB bands.
      2) PULL-OUT     - MAP and SIGNAL are BOTH back outside the same band they just re-entered
         (both below the lower band after a BUY / both above the upper band after a SELL) on the
         same candle close.
      3) FELL BACK    - the lines DID reach the far band, but MAP and SIGNAL are now BOTH back inside
         it (at or below the upper band after a BUY / at or above the lower band after a SELL) on
         a candle close without the normal end (the MAP/SIGNAL cross outside the band) having
         happened first. That move did not obey the 1-HOUR logic, so it is invalid.
    A new signal then needs the full BUY / SELL rules (a)-(e) to happen again.
    """
    act = sd['active']
    if act is None:
        sd['wh_prev_rel'] = None
        sd['wh_outer'] = False
        return
    m, s_, up, dn = vals.get('map'), vals.get('sig'), vals.get('bb_up'), vals.get('bb_dn')
    if None in (m, s_, up, dn):
        return
    rel  = _rel(m, s_)
    prev = sd['wh_prev_rel']
    was_outer = sd['wh_outer']                     # far band reached on an EARLIER candle
    if (m > up or s_ > up) if act == 'BUY' else (m < dn or s_ < dn):
        sd['wh_outer'] = True                      # the move did reach the far band
    inside  = (dn <= m <= up) and (dn <= s_ <= up)
    against = (act == 'BUY' and prev == 1 and rel == -1) or (act == 'SELL' and prev == -1 and rel == 1)
    if rel != 0:
        sd['wh_prev_rel'] = rel
    pulled_out = (m < dn and s_ < dn) if act == 'BUY' else (m > up and s_ > up)
    fell_back = was_outer and ((m <= up and s_ <= up) if act == 'BUY' else (m >= dn and s_ >= dn))
    if ((against and inside or pulled_out) and not sd['wh_outer']) or fell_back:
        if fell_back:
            why = ("MAP & SIGNAL reached the far band but fell back inside it without "
                   "crossing outside the band")
        elif pulled_out:
            why = "MAP & SIGNAL both went back outside the band (far band never reached)"
        else:
            why = "MAP/SIGNAL crossed back against the signal inside the bands (far band never reached)"
        _emit(symbol, sd, 'INVALID ' + act, c, ts,
              f"whipsaw: {why} - {act} from {_fmt_t(sd['active_since'])} cancelled",
              historical, vals)
        kinds.append('INVALID ' + act)
        sd['active']       = None
        sd['active_since'] = None
        sd['last_dir']     = None
        sd['wh_prev_rel']  = None
        sd['wh_outer']     = False


def _signal_update(symbol, sd, c, ts, fire, cross, historical, vals):
    """
    BUY / SELL signals and their exits.
      EXIT : MAP/SIGNAL cross each other while both are above the upper band (after a BUY)
             or both below the lower band (after a SELL).
      A new BUY/SELL is IGNORED while ANY previous signal is still open (no exit yet); a new
      signal never closes an open one. After an EXIT the next valid setup is a real signal,
      whichever direction.
    """
    kinds = []
    if HTF_WHIPSAW_INVALIDATION and is_htf(symbol):
        _whipsaw_check(symbol, sd, c, ts, historical, vals, kinds)
    act = sd['active']

    if act == 'BUY' and cross == 'CROSS_ABOVE_UPPER':
        _emit(symbol, sd, 'EXIT BUY', c, ts, "MAP/SIGNAL crossed above the upper band", historical, vals)
        kinds.append('EXIT BUY'); sd['active'] = None
    elif act == 'SELL' and cross == 'CROSS_BELOW_LOWER':
        _emit(symbol, sd, 'EXIT SELL', c, ts, "MAP/SIGNAL crossed below the lower band", historical, vals)
        kinds.append('EXIT SELL'); sd['active'] = None

    if fire:
        if sd['active'] is not None:
            # A signal ends ONLY on its own exit (or, on the 1-HOUR, when it is cancelled as invalid).
            # A new signal - even the opposite direction - never closes it.
            op = sd['active']
            since = f" from {_fmt_t(sd['active_since'])}" if sd.get('active_since') else ""
            why = (f"a {op} signal{since} is still open (no exit yet: MAP/SIGNAL have not crossed outside the "
                   f"{'upper' if op == 'BUY' else 'lower'} band)")
        elif REQUIRE_OPPOSITE_AFTER_EXIT and fire == sd['last_dir']:
            why = "same direction as the last signal — waiting for the opposite (REQUIRE_OPPOSITE_AFTER_EXIT)"
        else:
            why = None
        permit_note = ""
        if not why and DUAL_TF_GATE and ENABLE_HTF and not is_htf(symbol):
            ok, info5 = _htf_permits(symbol, fire, ts + timedelta(seconds=sd['gran']))
            if not ok:
                why = None
                _emit(symbol, sd, 'BLOCKED ' + fire, c, ts,
                      f"5-MIN {fire} blocked - {info5}", historical, vals)
                kinds.append('BLOCKED ' + fire)
                return kinds
            permit_note = f" | 1-HOUR {fire} valid since {_fmt_t(info5['since'])}"
        if why:
            _emit(symbol, sd, 'IGNORED ' + fire, c, ts, why, historical, vals)
            kinds.append('IGNORED ' + fire)
        else:
            sd['active']       = fire
            sd['active_since'] = ts
            sd['last_dir']     = fire
            if vals.get('map') is not None and vals.get('sig') is not None:
                sd['wh_prev_rel'] = _rel(vals['map'], vals['sig'])
            sd['wh_outer'] = False
            note = ("MAP & SIGNAL out, curved, both back inside, MAP "
                    + ("rising" if fire == 'BUY' else "falling")
                    + (", price beyond external BB" if uses_ext_bb(symbol) else "")
                    + permit_note)
            _emit(symbol, sd, fire, c, ts, note, historical, vals)
            kinds.append(fire)
    if is_htf(symbol):
        _htf_sync_windows(sd, ts)
    return kinds


# ============================================================
# MT5-EXACT INDICATOR  (the MQL4 formulas, repainting included)
# ============================================================

def _tma_mt5(c, t, period):
    """
    icTma() from the MQL4 indicator. c = closes oldest -> newest, c[-1] is bar 0.
    It averages OLDER candles and, where they exist, NEWER candles too (`if (j<=i)`),
    which is why MT5's line for a candle keeps changing as new candles arrive.
    """
    last = len(c) - 1
    sumw = period + 1
    s    = sumw * c[t]
    for j in range(1, period):
        k     = period - j + 1      # MQL4: for(j=1,k=period; ...; j++,k--)
        s    += k * c[t - j]
        sumw += k
        if t + j <= last:
            s    += k * c[t + j]
            sumw += k
    return s / sumw


def mt5_series(c):
    """
    MAP, SIGNAL and the two IntBB bands for every candle, as MT5 draws them now.
    MAP    = (TMA22-TMA34) + (TMA33-TMA18) + (TMA14-TMA29)
    SIGNAL = SMA(5) of MAP
    bands  = Bollinger(89, 1.0) on SIGNAL (BB_ON_SIGNAL) or on MAP; MT5 draws none on bar 0.
    """
    n         = len(c)
    first_map = max(PERIOD1, PERIOD2, PERIOD3, PERIOD4, PERIOD5, PERIOD6) - 1
    mp = [None] * n
    sg = [None] * n
    up = [None] * n
    dn = [None] * n
    for t in range(first_map, n):
        mp[t] = (_tma_mt5(c, t, PERIOD2) - _tma_mt5(c, t, PERIOD1)
                 + _tma_mt5(c, t, PERIOD4) - _tma_mt5(c, t, PERIOD3)
                 + _tma_mt5(c, t, PERIOD6) - _tma_mt5(c, t, PERIOD5))
    first_sig = first_map + SIGNAL_PERIOD - 1
    for t in range(first_sig, n):
        sg[t] = sum(mp[t - SIGNAL_PERIOD + 1:t + 1]) / SIGNAL_PERIOD
    src      = sg if BB_ON_SIGNAL else mp
    first_bb = (first_sig if BB_ON_SIGNAL else first_map) + BB_PERIOD - 1
    for t in range(first_bb, n - 1):
        seg  = src[t - BB_PERIOD + 1:t + 1]
        mean = sum(seg) / BB_PERIOD
        std  = math.sqrt(sum((x - mean) ** 2 for x in seg) / BB_PERIOD)
        up[t] = mean + BB_DEVIATION * std
        dn[t] = mean - BB_DEVIATION * std
    return mp, sg, up, dn


def _tail_len():
    """Candles needed to judge the last MT5_REPLAY_BARS bars (MAP 33 + SIGNAL 4 + bands 88 + margin)."""
    return MT5_REPLAY_BARS + 130


def _mt5_eval(symbol, closed_list, forming, keep_from, print_last):
    """
    Judge the strategy on the lines exactly as MT5 draws them right now.
    closed_list : closed candles oldest -> newest;  forming : bar 0 (or None).
    The same strategy code as the trading bot is run bar by bar over the recalculated lines.
    Decisions are kept only for bars at index >= keep_from; the last bar prints only if print_last.
    Returns (state, [per closed bar: open_time, fire, cross, vals]).
    """
    tf  = _make_tf_state('MT5')
    out = []
    n_closed = len(closed_list)
    if n_closed == 0:
        return tf, out
    bars   = list(closed_list) + ([forming] if forming else [])
    closes = [b['close'] for b in bars]
    mp, sg, up, dn = mt5_series(closes)
    dashboard_data['scratch'].setdefault(symbol, deque(maxlen=1))

    for t in range(n_closed):
        b      = bars[t]
        candle = {'open': b['open'], 'high': b['high'], 'low': b['low'], 'close': b['close']}
        ts     = _open_dt(b['open_time'])
        inject = {'map': mp[t], 'sig': sg[t], 'bb_up': up[t], 'bb_dn': dn[t]}
        if print_last and t == n_closed - 1:
            fire, cross = _process_candle(tf, candle, symbol, 'scratch', ts, inject)
        else:
            with contextlib.redirect_stdout(io.StringIO()):
                fire, cross = _process_candle(tf, candle, symbol, 'scratch', ts, inject)
        out.append({
            'open_time': b['open_time'], 'fire': fire, 'cross': cross,
            'vals': {'map': tf['last_map'], 'sig': tf['last_sig'],
                     'bb_up': tf['last_bb_up'], 'bb_dn': tf['last_bb_dn'],
                     'ext_up': tf.get('last_ext_up'), 'ext_dn': tf.get('last_ext_dn')},
        })
    return tf, out


def _history_pass(symbol, sd, n_new):
    """Judge newly received past candles on the final (repainted) lines, like MT5's history chart."""
    closed = list(sd['closed'])
    use    = closed[-(n_new + _tail_len()):]
    tf, out = _mt5_eval(symbol, use, sd['forming'], keep_from=len(use) - n_new, print_last=False)
    sd['tf'] = tf
    for o, c in zip(out[-n_new:], use[-n_new:]):
        ts    = _open_dt(c['open_time'])
        kinds = _signal_update(symbol, sd, c, ts, o['fire'], o['cross'], True, o['vals'])
        _write_candle_csv(symbol, c, ts, o['vals'], kinds, True)


def _repaint_check(symbol, sd, fire_by_time):
    """Compare live signals with the lines as MT5 has recalculated them since."""
    keep = []
    now_n = len(sd['closed'])
    for p in sd['pending_check']:
        cur = fire_by_time.get(p['open_time'])
        age = now_n - p['born']
        if cur != p['kind']:
            _emit(symbol, sd, 'REPAINTED AWAY ' + p['kind'], p['candle'], p['ts'],
                  f"the {p['kind']} signal of this candle is gone after {age} newer candle(s) — MT5's line changed",
                  False, p['vals'])
        elif age >= 34:
            _emit(symbol, sd, 'CONFIRMED ' + p['kind'], p['candle'], p['ts'],
                  f"still present after {age} newer candles — the lines are final", False, p['vals'])
        else:
            keep.append(p)
    sd['pending_check'] = keep


def _live_eval(symbol, sd, c):
    """A candle has just closed: judge it on the lines MT5 shows right now (bar 0 = the new candle)."""
    tail = list(sd['closed'])[-_tail_len():]
    tf, out = _mt5_eval(symbol, tail, sd['forming'], keep_from=len(tail) - 1, print_last=True)
    sd['tf'] = tf
    if not out:
        return
    last  = out[-1]
    ts    = _open_dt(c['open_time'])
    kinds = _signal_update(symbol, sd, c, ts, last['fire'], last['cross'], False, last['vals'])
    _write_candle_csv(symbol, c, ts, last['vals'], kinds, False)
    sd['live_candles'] += 1
    if last['fire'] and last['fire'] in kinds:
        sd['pending_check'].append({'open_time': c['open_time'], 'kind': last['fire'], 'born': len(sd['closed']),
                                    'candle': dict(c), 'ts': ts, 'vals': last['vals']})
    _repaint_check(symbol, sd, {o['open_time']: o['fire'] for o in out})


# ============================================================
# CANDLE STREAM (history + live updates)
# ============================================================

def _to_candle(d):
    t = d.get('open_time', d.get('epoch'))
    return {'open_time': int(t), 'open': float(d['open']), 'high': float(d['high']),
            'low': float(d['low']), 'close': float(d['close'])}


deferred_history = {}   # 5-MIN history waiting for the 1-HOUR history (the dual rule needs the 1-HOUR signals first)


def _flush_deferred(symbol):
    with data_lock:
        for cs in deferred_history.pop(symbol, []):
            _ingest_history_now(symbol, cs)


def _ingest_history(symbol, candles):
    """5-MIN history is held back until the 1-HOUR history is in, so every 5-MIN signal is judged against the 1-HOUR signals of its time."""
    if DUAL_TF_GATE and ENABLE_HTF and not is_htf(symbol):
        s5 = symbol_data.get(tf_key(symbol, GRANULARITY_HTF))
        if s5 is not None and s5['last_closed_open_time'] is None:
            deferred_history.setdefault(symbol, []).append(candles)
            t = threading.Timer(HISTORY_WAIT_HTF_SECONDS, _flush_deferred, args=(symbol,))
            t.daemon = True
            t.start()
            return
    _ingest_history_now(symbol, candles)
    if is_htf(symbol):
        _flush_deferred(split_key(symbol)[0])


def _ingest_history_now(symbol, candles):
    """First response: past candles. The newest one is still forming (bar 0); the rest are closed."""
    sd = symbol_data[symbol]
    uniq = {}
    for c in candles:
        uniq[c['open_time']] = c
    cs = [uniq[k] for k in sorted(uniq)]
    if not cs:
        return
    last  = cs[-1]
    lp    = sd['last_closed_open_time']
    newly = [c for c in cs[:-1] if lp is None or c['open_time'] > lp]
    for c in newly:
        sd['closed'].append(c)
    if newly:
        sd['last_closed_open_time'] = newly[-1]['open_time']
    sd['forming'] = last
    if not sd['csv_ready']:
        _init_csv(symbol)
        sd['csv_ready'] = True
    if newly:
        _history_pass(symbol, sd, len(newly))
    print(f"[{get_ts()}] [{symbol}] history loaded: {len(cs)} candles "
          f"({len(newly)} new)  forming={_fmt_t(_open_dt(last['open_time']))}")


def _ingest_update(symbol, c):
    """Live update of bar 0. A newer open_time means the previous candle has closed."""
    sd = symbol_data[symbol]
    f  = sd['forming']
    if f is None:
        sd['forming'] = c
        return
    if c['open_time'] == f['open_time']:
        sd['forming'] = c
    elif c['open_time'] > f['open_time']:
        sd['forming'] = c              # the new candle is bar 0 BEFORE judging, as in MT5
        lp = sd['last_closed_open_time']
        if lp is None or f['open_time'] > lp:
            sd['closed'].append(f)
            sd['last_closed_open_time'] = f['open_time']
            _live_eval(symbol, sd, f)
    # an older open_time is a stale duplicate: ignore


def _symbol_for(data, rid, sub_id, extra=None):
    sym = req_map.get(rid) or sub_map.get(sub_id)
    if sym:
        return sym
    echo = data.get('echo_req') or {}
    try:
        g = int((data.get('ohlc') or {}).get('granularity') or echo.get('granularity') or GRANULARITY)
    except Exception:
        g = GRANULARITY
    for cand in (extra, echo.get('underlying_symbol'), echo.get('ticks_history')):
        if isinstance(cand, str) and tf_key(cand, g) in symbol_data:
            return tf_key(cand, g)
    return None


def on_message(ws_app_, message):
    conn['last_msg'] = time.time()
    try:
        data = json.loads(message)
    except Exception:
        return
    rid = data.get('req_id') or (data.get('echo_req') or {}).get('req_id')

    if 'error' in data:
        err  = data['error']
        text = f"{err.get('code', '')}: {err.get('message', err)}"
        conn['last_error'] = text
        if probe['req_id'] is not None and rid == probe['req_id']:
            probe['error'] = text
            probe['event'].set()
        else:
            print(f"[{get_ts()}] ❌ Deriv error for {req_map.get(rid, '?')}: {text}")
        return

    try:
        if isinstance(data.get('candles'), list):
            sub_id = (data.get('subscription') or {}).get('id')
            sym    = _symbol_for(data, rid, sub_id)
            if sym and sub_id:
                sub_map[sub_id] = sym
            if probe['req_id'] is not None and rid == probe['req_id']:
                probe['ok'] = True
                probe['event'].set()
            if sym:
                candles = [_to_candle(x) for x in data['candles']]
                with data_lock:
                    _ingest_history(sym, candles)

        elif isinstance(data.get('ohlc'), dict):
            o      = data['ohlc']
            sub_id = o.get('id') or (data.get('subscription') or {}).get('id')
            sym    = _symbol_for(data, rid, sub_id, o.get('symbol') or o.get('underlying_symbol'))
            if sym:
                if sub_id:
                    sub_map[sub_id] = sym
                if 'open_time' not in o:
                    g_ = symbol_data[sym]['gran']
                    o['open_time'] = int(o['epoch']) // g_ * g_
                with data_lock:
                    _ingest_update(sym, _to_candle(o))
    except Exception as e:
        print(f"[{get_ts()}] ⚠ message handling error: {type(e).__name__}: {e}")


# ============================================================
# WEBSOCKET CONNECTION
# ============================================================

# Request layouts tried in this order until Deriv accepts one (the first that works is remembered).
#   0: ticks_history = 1  + underlying_symbol          (new style, as used for proposals)
#   1: ticks_history = "<symbol>"                      (as in the published ticks_history schema)
#   2: ticks_history = "<symbol>" + underlying_symbol
FORMAT_ORDER = (0, 1, 2)


def _build_request(symbol, fmt, req_id, gran=None):
    req = {
        "style":       "candles",
        "granularity": gran or GRANULARITY,
        "end":         "latest",
        "count":       HISTORY_COUNT,
        "subscribe":   1,
        "req_id":      req_id,
    }
    if fmt == 0:
        req["ticks_history"] = 1
        req["underlying_symbol"] = symbol
    elif fmt == 1:
        req["ticks_history"] = symbol
    else:
        req["ticks_history"] = symbol
        req["underlying_symbol"] = symbol
    return req


def _send_sub(symbol, fmt, gran=None):
    rid = next(req_counter)
    req_map[rid] = tf_key(symbol, gran or GRANULARITY)
    ws_app.send(json.dumps(_build_request(symbol, fmt, rid, gran)))
    return rid


def _subscribe_all():
    """Runs in its own thread after the socket opens."""
    try:
        syms = monitored_symbols()
        if conn['fmt'] is None:
            first = syms[0]
            for fmt in FORMAT_ORDER:
                probe['event'].clear(); probe['ok'] = False; probe['error'] = None
                probe['req_id'] = _send_sub(first, fmt)
                print(f"[{get_ts()}] Trying candle request layout {fmt} on {first} ...")
                probe['event'].wait(10)
                if probe['ok']:
                    conn['fmt'] = fmt
                    print(f"[{get_ts()}] ✓ Candle request layout {fmt} accepted by Deriv: "
                          f"{json.dumps(_build_request(first, fmt, 0))}")
                    break
                print(f"[{get_ts()}] ✗ Layout {fmt} not accepted: {probe['error'] or 'no response in 10s'}")
            probe['req_id'] = None
            if conn['fmt'] is None:
                print(f"[{get_ts()}] ❌ None of the candle request layouts worked. Last error: "
                      f"{conn['last_error'] or 'none'}\n   Paste this line to Claude so the request can be fixed.")
                return
            syms = syms[1:]
        # 5-minute candles for every symbol first, then the 1-hour candles
        jobs = [(s, GRANULARITY) for s in syms]
        if ENABLE_HTF:
            jobs += [(s, GRANULARITY_HTF) for s in monitored_symbols()]
        for s, g in jobs:
            if not running or not conn['connected']:
                return
            _send_sub(s, conn['fmt'], g)
            time.sleep(0.25)
        print(f"[{get_ts()}] Subscribed to candles for {len(monitored_symbols())} symbols"
              f"{' (5m + 1h)' if ENABLE_HTF else ' (5m)'}")
    except Exception as e:
        print(f"[{get_ts()}] Subscribe error: {type(e).__name__}: {e}")


def _keepalive(conn_id):
    """Send Deriv's API-level ping on a schedule while this connection is the current one."""
    while running and conn['connected'] and conn['connects'] == conn_id:
        time.sleep(KEEPALIVE_SECONDS)
        if not (running and conn['connected'] and conn['connects'] == conn_id):
            break
        try:
            ws_app.send(json.dumps({"ping": 1, "req_id": next(req_counter)}))
        except Exception:
            break


def on_open(ws_app_):
    conn['connected'] = True
    conn['connects'] += 1
    conn['last_msg']  = time.time()
    conn['opened_at'] = time.time()
    threading.Thread(target=_keepalive, args=(conn['connects'],), daemon=True).start()
    req_map.clear(); sub_map.clear()
    with data_lock:
        for sd in symbol_data.values():
            sd['forming'] = None      # history will be re-sent and fills any gap
    print(f"[{get_ts()}] Connected to Deriv public WebSocket")
    threading.Thread(target=_subscribe_all, daemon=True).start()


def on_error(ws_app_, error):
    print(f"[{get_ts()}] WebSocket error: {error}")


def on_close(ws_app_, code, msg):
    conn['connected'] = False
    up = int(time.time() - conn['opened_at']) if conn['opened_at'] else 0
    print(f"[{get_ts()}] WebSocket closed: {code} {msg}  (connection had been up {up}s)")


def _run_ws():
    global ws_app
    while running:
        ws_app = websocket.WebSocketApp(
            WS_URL, on_open=on_open, on_message=on_message,
            on_error=on_error, on_close=on_close)
        ws_app.run_forever(ping_interval=30, ping_timeout=10)
        conn['connected'] = False
        if not running:
            break
        print(f"[{get_ts()}] Reconnecting in 3s ...")
        time.sleep(3)


def _watchdog():
    """If no data arrives for 90s, drop the connection so it reconnects."""
    while running:
        time.sleep(15)
        if conn['connected'] and conn['last_msg'] and time.time() - conn['last_msg'] > 90:
            print(f"[{get_ts()}] No data for 90s — reconnecting")
            try:
                ws_app.close()
            except Exception:
                pass


def start_ws():
    for s in monitored_symbols():
        with data_lock:
            init_symbol(s, GRANULARITY)
            if ENABLE_HTF:
                init_symbol(tf_key(s, GRANULARITY_HTF), GRANULARITY_HTF)
    threading.Thread(target=_run_ws, daemon=True).start()
    threading.Thread(target=_watchdog, daemon=True).start()


# ============================================================
# DASH DASHBOARD  —  5-MINUTE on the left, 1-HOUR on the right
# ============================================================

app = dash.Dash(__name__, external_stylesheets=[dbc.themes.DARKLY])
app.title = "XERO AI — 5m + 1h Signal Monitor"

_sym_options = [{"label": f"{s['name']}  ({s['symbol']})", "value": s['symbol']} for s in TRADING_SYMBOLS]

_GRAPH_STYLE = {'height': 'calc(100vh - 150px)', 'minHeight': '620px', 'width': '100%'}
_GRAPH_CFG   = {'responsive': True, 'displaylogo': False}
_PANEL_STYLE = {"backgroundColor": "#0a0f16", "border": "1px solid #1e2d3d",
                "borderRadius": "4px", "fontSize": "0.75rem"}


def _tf_title(text, color):
    return html.Div(text, style={"textAlign": "center", "fontWeight": "700", "fontSize": "0.8rem",
                                 "letterSpacing": "1px", "color": color, "marginBottom": "2px"})


app.layout = html.Div([
    html.Div([
        html.Span("XERO AI SOFTWARE  ·  5-MIN + 1-HOUR SIGNAL MONITOR  ·  signals only (no trading)",
                  className="text-primary fw-bold", style={"fontSize": "1rem", "letterSpacing": "2px"}),
        html.Span(id='live-time', className="text-warning ms-4", style={"fontSize": "0.95rem"}),
    ], className="text-center mb-1"),
    html.Div(
        f"MT5-exact lines (repainting included)  |  each timeframe has its own MAP / SIGNAL  |  "
        f"IntBB({BB_PERIOD},{BB_DEVIATION}) on {'SIGNAL' if BB_ON_SIGNAL else 'MAP'}  |  "
        f"ExtBB({EXT_BB_PERIOD},{EXT_BB_DEVIATION}) on price (5-MIN only; 1-HOUR has no ExtBB)  |  times = UTC{TIME_OFFSET_HOURS:+d}h",
        className="text-center text-secondary mb-1", style={"fontSize": "0.7rem"}),
    html.Div(id='status-bar', className="mb-1"),

    # ---- controls row (same arrangement as the reference dashboard) ----
    dbc.Row([
        dbc.Col([html.Label("Symbol:", className="text-white fw-bold", style={"fontSize": "0.75rem"}),
                 dcc.Dropdown(id='sym-dd', options=_sym_options, value=monitored_symbols()[0],
                              clearable=False, style={"color": "#000"})], md=3),
        dbc.Col([html.Label("Signal diagnostic:", className="text-white fw-bold",
                            style={"fontSize": "0.75rem"}),
                 html.Div(dbc.Button("⬇ Download signal diagnostic CSV", id='btn-dl', color="primary",
                                     size="sm", style={"fontSize": "0.7rem"})),
                 dcc.Download(id='dl-csv')], md=3),
        dbc.Col([html.Label("5-min candles to display:", className="text-white fw-bold", style={"fontSize": "0.75rem"}),
                 dcc.Slider(id='win-3m', min=20, max=300, step=10, value=100,
                            marks={20: '20', 100: '100', 200: '200', 300: '300'})], md=3),
        dbc.Col([html.Label("1-hour candles to display:", className="text-white fw-bold", style={"fontSize": "0.75rem"}),
                 dcc.Slider(id='win-5m', min=20, max=300, step=10, value=100,
                            marks={20: '20', 100: '100', 200: '200', 300: '300'})], md=3),
    ], className="mb-1 g-2"),

    # ---- the two charts side by side: candles + ExtBB on top, MAP / SIGNAL / IntBB below ----
    dbc.Row([
        dbc.Col([_tf_title("5-MINUTE CANDLES", "#42a5f5"),
                 dcc.Graph(id='chart-3m', style=_GRAPH_STYLE, config=_GRAPH_CFG),
                 html.Div(id='readout-3m', className="p-2 mt-1", style=_PANEL_STYLE)], md=6, className="px-1"),
        dbc.Col([_tf_title("1-HOUR CANDLES", "#80deea"),
                 dcc.Graph(id='chart-5m', style=_GRAPH_STYLE, config=_GRAPH_CFG),
                 html.Div(id='readout-5m', className="p-2 mt-1", style=_PANEL_STYLE)], md=6, className="px-1"),
    ], className="g-1"),

    dbc.Row([
        dbc.Col([html.H6("5-MIN signals (newest first)", className="text-info mt-3"),
                 html.Div(id='signals-3m')], md=6, className="px-1"),
        dbc.Col([html.H6("1-HOUR signals (newest first)", className="text-info mt-3"),
                 html.Div(id='signals-5m')], md=6, className="px-1"),
    ], className="g-1"),

    dcc.Interval(id='interval', interval=1000, n_intervals=0),
], style={"backgroundColor": "#080c10", "padding": "6px 8px", "minHeight": "100vh"})


def _build_chart(key, candle_win, label, gran):
    """Returns (figure, info) for ONE timeframe. Lines are recalculated live exactly as MT5 draws them
    (repainting included), from THIS timeframe's own candles."""
    from plotly.subplots import make_subplots
    with data_lock:
        sd      = symbol_data.get(key)
        closed  = list(sd['closed'])[-(candle_win + _tail_len()):] if sd else []
        forming = dict(sd['forming']) if sd and sd['forming'] else None
        events  = list(dashboard_data['signals'].get(key, []))

    info = {}
    fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                        row_heights=[0.62, 0.38], vertical_spacing=0.05)
    if closed:
        bars     = closed + ([forming] if forming else [])
        closes   = [b['close'] for b in bars]
        mp, sg, up, dn = mt5_series(closes)
        n        = len(bars)
        n_closed = len(closed)
        times    = [_open_dt(b['open_time']) for b in bars]
        lo       = max(0, n_closed - candle_win)
        t0       = times[lo]
        idx_all  = range(lo, n)

        fig.add_trace(go.Candlestick(
            x=[times[i] for i in range(lo, n_closed)],
            open=[bars[i]['open'] for i in range(lo, n_closed)], high=[bars[i]['high'] for i in range(lo, n_closed)],
            low=[bars[i]['low'] for i in range(lo, n_closed)], close=[bars[i]['close'] for i in range(lo, n_closed)],
            name=f'{tf_label(gran)} candles', increasing_line_color='#26a69a', decreasing_line_color='#ef5350'),
            row=1, col=1)
        if forming:
            fig.add_trace(go.Candlestick(
                x=[times[n_closed]], open=[forming['open']], high=[forming['high']], low=[forming['low']],
                close=[forming['close']], name='bar 0 (forming)',
                increasing=dict(line=dict(color='#ffd54f', width=2), fillcolor='rgba(255,213,79,0.15)'),
                decreasing=dict(line=dict(color='#ffd54f', width=2), fillcolor='rgba(255,213,79,0.15)')),
                row=1, col=1)

        # external Bollinger on price (MT5's built-in: causal, uses the current close on bar 0)
        ex_t, ex_u, ex_m, ex_d = [], [], [], []
        for i in idx_all:
            if uses_ext_bb(key) and i >= EXT_BB_PERIOD - 1:
                u_, d_ = calc_bb(closes[i - EXT_BB_PERIOD + 1:i + 1], EXT_BB_PERIOD, EXT_BB_DEVIATION)
                ex_t.append(times[i]); ex_u.append(u_); ex_d.append(d_); ex_m.append((u_ + d_) / 2)
        if ex_t and uses_ext_bb(key):
            nm = f'ExtBB({EXT_BB_PERIOD},{EXT_BB_DEVIATION})'
            fig.add_trace(go.Scatter(x=ex_t, y=ex_u, mode='lines', name=nm + ' upper',
                line=dict(color='#4caf50', width=1.2)), row=1, col=1)
            fig.add_trace(go.Scatter(x=ex_t, y=ex_m, mode='lines', name=nm + ' mid',
                line=dict(color='#4caf50', width=1, dash='dot')), row=1, col=1)
            fig.add_trace(go.Scatter(x=ex_t, y=ex_d, mode='lines', name=nm + ' lower',
                line=dict(color='#4caf50', width=1.2)), row=1, col=1)

        for kind, (sym_, col, lab) in {'BUY': ('triangle-up', '#00e676', 'BUY signal'),
                                       'SELL': ('triangle-down', '#ff5252', 'SELL signal')}.items():
            ev = [e for e in events if e['kind'] == kind and e['ts'] >= t0]
            if ev:
                fig.add_trace(go.Scatter(x=[e['ts'] for e in ev], y=[e['close'] for e in ev], mode='markers',
                    name=lab, marker=dict(symbol=sym_, size=15, color=col,
                                          line=dict(color='white', width=1))), row=1, col=1)
        for pref, nm, mk in (('EXIT', 'EXIT', dict(symbol='x', size=12, color='#ffffff')),
                             ('INVALID', 'invalid (whipsaw)', dict(symbol='x-thin-open', size=14, color='#ff9800')),
                             ('BLOCKED', 'blocked (no 1-hour)', dict(symbol='square-open', size=11, color='#ff9800')),
                             ('IGNORED', 'ignored', dict(symbol='circle-open', size=11, color='#9e9e9e')),
                             ('REPAINTED', 'repainted away', dict(symbol='x', size=18, color='#ff9800')),
                             ('CONFIRMED', 'confirmed', dict(symbol='diamond-open', size=14, color='#00e5ff'))):
            ev = [e for e in events if e['kind'].startswith(pref) and e['ts'] >= t0]
            if ev:
                fig.add_trace(go.Scatter(x=[e['ts'] for e in ev], y=[e['close'] for e in ev], mode='markers',
                    name=nm, marker=mk), row=1, col=1)

        # price axis: fill the panel with the visible candles + ExtBB (small margin top and bottom)
        px = []
        for i in range(lo, n):
            px += [bars[i]['high'], bars[i]['low']]
        px += [v for v in ex_u + ex_d if v is not None]
        if px:
            plo, phi = min(px), max(px)
            prng = (phi - plo) or max(abs(phi) * 1e-4, 1e-6)
            fig.update_yaxes(range=[plo - prng * 0.05, phi + prng * 0.05], autorange=False, row=1, col=1)

        def line(vals, nm, **kw):
            pts = [(times[i], vals[i]) for i in idx_all if vals[i] is not None]
            if pts:
                fig.add_trace(go.Scatter(x=[p[0] for p in pts], y=[p[1] for p in pts],
                                         mode='lines', name=nm, **kw), row=2, col=1)
        line(mp, 'MAP',    line=dict(color='#ffd700', width=2))
        line(sg, 'Signal', line=dict(color='#42a5f5', width=1.5, dash='dot'))
        bb_src = 'SIGNAL' if BB_ON_SIGNAL else 'MAP'
        line(up, f'IntBB↑({BB_PERIOD},{BB_DEVIATION}) on {bb_src}', line=dict(color='#26a69a', width=1, dash='dash'))
        line(dn, f'IntBB↓({BB_PERIOD},{BB_DEVIATION}) on {bb_src}', line=dict(color='#ef5350', width=1, dash='dash'))
        fig.add_hline(y=0, line=dict(color='rgba(255,255,255,0.15)', width=1, dash='dash'), row=2, col=1)

        ind = [v[i] for v in (mp, sg, up, dn) for i in idx_all if v[i] is not None]
        if ind:
            lo_, hi_ = min(ind), max(ind)
            rng = (hi_ - lo_) or 1.0
            fig.update_yaxes(range=[lo_ - rng * 0.08, hi_ + rng * 0.08], autorange=False, row=2, col=1)

        i1, i0 = n_closed - 1, (n_closed if forming else None)
        info = {'bar1_time': times[i1], 'bar1': bars[i1], 'bar1_vals': (mp[i1], sg[i1], up[i1], dn[i1]),
                'bar0_time': times[i0] if i0 is not None else None,
                'bar0': forming, 'bar0_vals': (mp[i0], sg[i0]) if i0 is not None else None}

        # x axis: show exactly the requested candles, with a little room on the right for the forming candle
        gap   = timedelta(seconds=gran)
        shown = n_closed - lo
        pad   = max(4, int(shown * 0.06))
        fig.update_xaxes(range=[times[lo] - gap, times[-1] + gap * pad])
    else:
        fig.add_annotation(text="Waiting for candles from Deriv ...", xref="paper", yref="paper",
                           x=0.5, y=0.5, showarrow=False, font=dict(size=14, color="orange"))

    fig.update_layout(template='plotly_dark', hovermode='x unified', autosize=True,
                      margin=dict(l=55, r=15, t=8, b=30), plot_bgcolor='#0d1117', paper_bgcolor='#080c10',
                      showlegend=False, hoverlabel=dict(font_size=10),
                      uirevision=f"{key}-{candle_win}")
    fig.update_xaxes(gridcolor='#161e28', rangeslider_visible=False)
    fig.update_yaxes(gridcolor='#161e28')
    return fig, info


def _table(header, body_rows):
    return dbc.Table([html.Thead(html.Tr([html.Th(h) for h in header])), html.Tbody(body_rows)],
                     bordered=True, color="dark", hover=True, size='sm', className="table-dark",
                     style={"fontSize": "0.72rem"})


def _f5(x):
    return "—" if x is None else f"{x:.5f}"


def _tf_panel(sel_sym, gran, cw):
    """Everything shown for ONE timeframe: figure, number readout, signals table."""
    key = tf_key(sel_sym, gran)
    with data_lock:
        sd     = symbol_data.get(key)
        events = list(dashboard_data['signals'].get(key, []))[:60]
    tf = sd['tf'] if sd else {}

    fig, info = _build_chart(key, cw, tf_label(gran), gran)

    if info:
        b1, b0 = info['bar1'], info['bar0']
        m1, s1, u1, d1 = info['bar1_vals']
        lines = [html.Div(f"Bar 1 (last closed, {_fmt_t(info['bar1_time'])})   "
                          f"O {b1['open']}  H {b1['high']}  L {b1['low']}  C {b1['close']}   |   "
                          f"MAP {_f5(m1)}   SIGNAL {_f5(s1)}   IntBB↑ {_f5(u1)}   IntBB↓ {_f5(d1)}",
                          className="text-warning")]
        if b0:
            m0, s0 = info['bar0_vals']
            lines.append(html.Div(f"Bar 0 (forming, {_fmt_t(info['bar0_time'])})   "
                                  f"O {b0['open']}  H {b0['high']}  L {b0['low']}  C {b0['close']}   |   "
                                  f"MAP {_f5(m0)}   SIGNAL {_f5(s0)}   (changes with every tick, as in MT5)",
                                  style={"color": "#ffd54f"}))
        if uses_ext_bb(key):
            lines.append(html.Div(
                f"ExtBB↑ {_f5(tf.get('last_ext_up'))}   ExtBB↓ {_f5(tf.get('last_ext_dn'))}"
                if tf.get('last_ext_up') is not None else "ExtBB loading", style={"color": "#4caf50"}))
    else:
        lines = [html.Div("no data yet", className="text-secondary")]
    if sd and DUAL_TF_GATE and ENABLE_HTF and not is_htf(key):
        s5 = symbol_data.get(tf_key(sel_sym, GRANULARITY_HTF))
        w5 = (s5['windows'][-1] if s5 and s5['windows'] and s5['windows'][-1]['end'] is None else None)
        lines.append(html.Div(
            f"1-HOUR permission: {w5['dir'] + ' valid since ' + _fmt_t(w5['since']) if w5 else 'none (5-MIN signals are BLOCKED)'}",
            style={"color": "#ff9800"}))
    if sd:
        lines.append(html.Div(
            f"Active: {sd['active'] or 'none'}   Last signal: {sd['last_dir'] or 'none'}   "
            f"Excursion: {tf.get('excursion_state') or 'none'}   "
            f"Bands on: {'SIGNAL' if BB_ON_SIGNAL else 'MAP'}", className="text-info"))

    kind_cls = {'BUY': 'text-success', 'SELL': 'text-danger'}
    sig_rows = [html.Tr([
        html.Td(_fmt_t(e['ts'])),
        html.Td(e['kind'], className=kind_cls.get(e['kind'], 'text-secondary' if e['kind'].startswith('IGN')
                                                     else 'text-warning' if e['kind'].startswith('BLOCKED') else 'text-white')),
        html.Td(f"{e['close']}"), html.Td(f"{e['map']:.4f}" if e['map'] is not None else ""),
        html.Td(f"{e['sig']:.4f}" if e['sig'] is not None else ""),
        html.Td("HIST" if e['historical'] else "LIVE", className="text-secondary"),
        html.Td(e['note'], className="text-secondary"),
    ]) for e in events] or [html.Tr([html.Td("No signals yet", colSpan=7, className="text-secondary")])]
    return (fig, html.Div(lines),
            _table(["Candle", "Event", "Close", "MAP", "SIGNAL", "", "Note"], sig_rows))


@app.callback(
    [Output('live-time', 'children'), Output('status-bar', 'children'),
     Output('chart-3m', 'figure'), Output('readout-3m', 'children'),
     Output('signals-3m', 'children'),
     Output('chart-5m', 'figure'), Output('readout-5m', 'children'),
     Output('signals-5m', 'children')],
    [Input('interval', 'n_intervals'), Input('sym-dd', 'value'),
     Input('win-3m', 'value'), Input('win-5m', 'value')])
def refresh(n, sel_sym, cw1, cw5):
    with data_lock:
        def counts(gran):
            ss = [s for s in symbol_data.values() if s['gran'] == gran]
            return sum(1 for s in ss if not s['tf']['warming_up']), len(ss)
        r1, t1 = counts(GRANULARITY)
        r5, t5 = counts(GRANULARITY_HTF)
        live   = sum(s['live_candles'] for s in symbol_data.values())

    status = html.Div([
        html.Span("● CONNECTED" if conn['connected'] else "● DISCONNECTED",
                  className=("text-success" if conn['connected'] else "text-danger") + " fw-bold me-4"),
        html.Span(f"Request layout: {conn['fmt'] if conn['fmt'] is not None else 'negotiating'}", className="text-secondary me-4"),
        html.Span(f"5m ready: {r1}/{t1}", className="text-info me-3"),
        html.Span(f"1h ready: {r5}/{t5}" if ENABLE_HTF else "1h: off", className="text-info me-4"),
        html.Span(f"Live candles closed: {live}", className="text-info me-4"),
        html.Span(f"Last data: {int(time.time() - conn['last_msg'])}s ago" if conn['last_msg'] else "No data yet",
                  className="text-secondary me-4"),
        html.Span(f"Last error: {conn['last_error']}" if conn['last_error'] else "", className="text-danger"),
    ], className="d-flex flex-wrap p-1", style=dict(_PANEL_STYLE, fontSize="0.75rem"))

    f1, ro1, sg1 = _tf_panel(sel_sym, GRANULARITY,    cw1)
    f5, ro5, sg5 = _tf_panel(sel_sym, GRANULARITY_HTF, cw5)
    return (datetime.now().strftime("%Y-%m-%d %H:%M:%S"), status,
            f1, ro1, sg1, f5, ro5, sg5)


@app.callback(Output('dl-csv', 'data'), Input('btn-dl', 'n_clicks'), State('sym-dd', 'value'),
              prevent_initial_call=True)
def download_diagnostic(n_clicks, sel_sym):
    """One CSV: every signal event for both timeframes."""
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["timeframe", "candle", "record", "direction_or_event", "result", "close",
                "map", "signal", "intbb_up", "intbb_dn", "extbb_up", "extbb_dn", "historical", "detail"])
    with data_lock:
        for gran in (GRANULARITY, GRANULARITY_HTF):
            key = tf_key(sel_sym, gran)
            for e in reversed(list(dashboard_data['signals'].get(key, []))):
                w.writerow([tf_label(gran), _fmt_t(e['ts']), "signal", e['kind'], "", _fnum(e['close']),
                            _fnum(e['map']), _fnum(e['sig']), _fnum(e['bb_up']), _fnum(e['bb_dn']),
                            _fnum(e['ext_up']), _fnum(e['ext_dn']), 1 if e['historical'] else 0, e['note']])
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return dict(content=buf.getvalue(), filename=f"{sel_sym}_signal_diagnostic_{stamp}.csv", type="text/csv")


def run_dashboard():
    print(f"\n{'='*70}\n[{get_ts()}] Dashboard → http://localhost:8050\n{'='*70}\n")
    app.run(debug=False, host='0.0.0.0', port=8050)


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("XERO AI SOFTWARE — 5-MINUTE + 1-HOUR SIGNAL MONITOR  (signals only, NO trading)")
    print("=" * 70)
    print(f"  Candles     : real {GRANULARITY}s" + (f" and {GRANULARITY_HTF}s" if ENABLE_HTF else "") + " candles streamed from Deriv (public, no login)")
    print(f"  Endpoint    : {WS_URL}")
    print(f"  Symbols     : {len(monitored_symbols())}")
    print(f"  Indicator   : MT5-exact (repainting included), IntBB({BB_PERIOD},{BB_DEVIATION}) on {'SIGNAL' if BB_ON_SIGNAL else 'MAP'},"
          f"  ExtBB({EXT_BB_PERIOD},{EXT_BB_DEVIATION}) on price (5-MIN only; 1-HOUR has NO ExtBB)")
    print("  Signals are judged when a candle closes, on the lines MT5 shows at that moment;")
    print("  later you are told if a signal was REPAINTED AWAY or CONFIRMED.")
    print(f"  Times shown : UTC{TIME_OFFSET_HOURS:+d}h   Logs: ./{LOG_DIR}/")
    print("  5-MIN BUY  : MAP & SIGNAL both below IntBB lower, curve up, both back in, MAP rising, close > ExtBB upper")
    print("  5-MIN SELL : MAP & SIGNAL both above IntBB upper, curve down, both back in, MAP falling, close < ExtBB lower")
    print("  Each time frame gives its OWN signals (no gate). Telegram says which one, e.g. 'Crash 500 Index BUY from 1 hour time frame'")
    print("  1-HOUR BUY  : same but NO ExtBB filter (MAP/SIGNAL/IntBB rules only)")
    print("  1-HOUR SELL : same but NO ExtBB filter (MAP/SIGNAL/IntBB rules only)")
    print("  EXIT : BUY  -> MAP/SIGNAL cross while both above the upper band")
    print("         SELL -> MAP/SIGNAL cross while both below the lower band")
    print("=" * 70 + "\n")
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        print("  ⚠ Telegram not configured — alerts are printed only\n")

    start_ws()
    threading.Thread(target=run_dashboard, daemon=True).start()
    time.sleep(2)
    if os.environ.get("GITHUB_ACTIONS") == "true":
        _notify_status("STARTED ✅", f"Signals only (no trading). {len(monitored_symbols())} symbols, "
                                     f"5-min and 1-hour charts.\nYou will get a message for every BUY / SELL / EXIT.")
    try:
        while running:
            time.sleep(30)
    except KeyboardInterrupt:
        running = False
        signal.signal(signal.SIGINT, signal.SIG_IGN)   # a second Ctrl+C (timeout can send two) must not cut the shutdown short
        if os.environ.get("GITHUB_ACTIONS") == "true":
            _notify_status("RUN ENDED ⏹", "The 5h50m run is finished. The next run starts in about 5 minutes.")
            time.sleep(4)   # give the Telegram message time to leave before the process exits
        try:
            ws_app.close()
        except Exception:
            pass
