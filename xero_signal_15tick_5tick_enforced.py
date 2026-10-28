"""
XERO AI SOFTWARE — TICK-CANDLE SIGNAL MONITOR   (+ optional AUTO-TRADING)
=========================================================================
Dashboard : http://localhost:8050

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
  * Streams REAL ticks from Deriv's public WebSocket (no login, no token needed
    for the data) and builds tick candles from them (TICKS_PER_CANDLE ticks each).
    A candle closes when the first tick of the NEXT candle arrives, so that
    tick is bar 0 at the moment of judging (same as before).
  * AUTO-TRADING (optional, OFF unless DERIV_PAT (+ DERIV_APP_ID) is set): every LIVE, accepted 5-tick
    BUY / SELL entry (the same ones that send the Telegram line) opens a Deriv MULTUP / MULTDOWN contract on the
    base symbol, using the stake, TP / SL, MAX_OPEN_TRADES and per-symbol multipliers of xero_trader_1m.py.
    After a LOSING normal trade, the next trade is a RECOVERY trade (stake 2, TP 1, SL 1), then back to normal.
    15-tick signals, HIST, BLOCKED, INVALID and IGNORED rows never trade. Real accounts need ALLOW_REAL_TRADING=1.
  * Gives signals:
        BUY    MAP and SIGNAL both go below IntBB lower, MAP curves up, both are
               back inside, MAP rising  (15-tick: judged on candle close, NO external BB;
               5-tick: also needs the close ABOVE external BB upper)
        SELL   mirror image  (5-tick: close BELOW external BB lower)
        EXIT   BUY  exits when MAP/SIGNAL cross while both are above the upper band
               SELL exits when they cross while both are below the lower band
        A new signal while one is still open is shown as IGNORED; it never closes the open one
        (ONE_OPEN_SIGNAL). Each signal ends only on its own exit.
  * DUAL TIME FRAME: the 15-tick series is the gate, the 5-tick series is the entry.
        15-tick signal is valid until it exits (MAP/SIGNAL cross outside the far band) or is
        cancelled as INVALID: inside cross, pull-out, or fell back inside after reaching the far band.
        A 5-tick BUY / SELL counts only while a 15-tick signal in the same direction is valid;
        otherwise it is shown as BLOCKED (dashboard only).
  * Telegram: one short line per accepted 5-tick entry (e.g. "BUY — Volatility 25 Index") and one
    when that entry exits ("EXIT BUY — Volatility 25 Index"). Nothing for 15-tick signals or for
    INVALID / BLOCKED / IGNORED rows.
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
TICKS_PER_CANDLE = 15   # every candle is built from this many ticks
ALTERNATE_SIGNALS = False   # False = EVERY setup that meets the rules opens a signal (nothing is IGNORED). True = old behaviour: BUY/SELL must alternate
INTRABAR_EVERY_N_TICKS  = 1  # the rules are re-checked on the current lines every N ticks (no waiting for a candle to close)
SIGNAL_CLUSTER_CANDLES  = 0  # 0 = NO signal is ever suppressed for being near another one (still max one per candle per direction). Old value was 2 # the SAME setup can be re-detected on the next 1-2 candles as the lines repaint = ONE setup. A genuinely new setup needs >= 3 candles (out, curve, back in), so it is never merged
LATE_SETTLE_CANDLES = 40     # a candle older than this is judged on settled lines; a signal that shows up only then is logged as LATE
DIAG_INCLUDE_REJECTS = True   # signal diagnostic CSV: also log candles where a setup was REJECTED (shows WHY a signal you expected never fired)
TICKS_PER_CANDLE_2 = 5  # second, faster candle series shown to the RIGHT of the first (own MAP / SIGNAL / bands)
HISTORY_COUNT = 800     # candles built at start (the MT5 calculation needs ~400); requested as ticks (max 5000 ticks)

# Extra (older) history. Deriv sends only about 1000 ticks in one answer, so after the first answer
# the program asks for several OLDER batches per symbol and joins them before building candles.
EXTRA_HISTORY_BATCHES = 3      # how many older batches to fetch per symbol (0 = off, old behaviour)
OLDER_BATCH_TICKS     = 1000   # ticks asked for in each older batch
OLDER_REQUEST_GAP     = 0.5    # seconds between two older-batch requests (keeps under Deriv's rate limit)
OLDER_WAIT_SECONDS    = 12     # longest wait for the answers of one round before moving on

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

# ---- NEW RULE FOR THE HIGHER TIME FRAME ONLY (the 15-tick series) ----
# True : the 15-tick series has NO external BB (no filter, no lines drawn) and fires purely on the rules
#        (a)-(e): MAP out of IntBB -> SIGNAL out together -> MAP curves (>=5% of band width) -> MAP and SIGNAL
#        both back in -> MAP rising/falling on the re-entry candle. The 5-tick series is NOT changed.
# False: old behaviour (external BB filter on both series).
HTF_RULES_ONLY = True
# True : the 15-tick series is judged ONLY when its candle closes (no intrabar scan on the forming candle).
HTF_JUDGE_ON_CLOSE_ONLY = True
# True : a 15-tick BUY/SELL is CANCELLED the moment it becomes invalid (only if the lines never reached the
#        opposite band after the signal):
#          inside cross : BUY  -> MAP crosses below SIGNAL while both lines are inside the bands
#                         SELL -> MAP crosses above SIGNAL while both lines are inside the bands
#          pull-out     : BUY  -> MAP and SIGNAL both back below the lower band on the same candle
#                         SELL -> MAP and SIGNAL both back above the upper band on the same candle
#        The next signal then needs all five conditions again, starting from a new dip / peak.
HTF_INVALIDATION = True
#   FELL BACK (also part of HTF_INVALIDATION): the lines DID reach the far band, but MAP and SIGNAL are now BOTH
#   back inside it (BUY: at or below the upper band / SELL: at or above the lower band) on a candle close without the
#   normal end (MAP/SIGNAL crossing each other outside the band) having happened first -> that signal is invalid.

# DUAL TIME FRAME: a 5-tick (lower time frame) BUY / SELL is a real signal ONLY while a 15-tick (higher time frame)
# BUY / SELL in the same direction is still valid. A 15-tick signal is valid from its candle close until it is cancelled
# (inside cross / pull-out / fell back) or ends normally (MAP and SIGNAL cross outside the far band).
# A 5-tick signal that comes when no matching 15-tick signal is valid is shown as BLOCKED (not hidden, no alert).
# A 5-tick candle that ends on the very same tick as a 15-tick candle is judged on the 15-tick state as it was BEFORE
# that 15-tick candle closed. The 5-tick series has its OWN exit (its own MAP/SIGNAL cross outside the far band);
# the 15-tick ending does not exit it.
DUAL_TF_GATE = True
# True : while ANY signal of a series is open (no exit yet) a new BUY / SELL of that series is shown as IGNORED and a new
#        signal NEVER closes an open one (a signal ends only on its own exit, or - 15-tick - when it is cancelled as invalid).
# False: the old behaviour of this script (ALTERNATE_SIGNALS decides; an opposite signal closes the open one).
ONE_OPEN_SIGNAL = True

# ---- Minimum excursion depth ----
MIN_EXCURSION_DEPTH_FRAC = 0.05
TURN_CAN_COMPLETE_INSIDE_BAND = True   # True : MAP's high/low point is the turn, even if the very next candle is already back inside the band
                                       #        (a sharp V / inverted-V that re-enters in ONE candle still counts)
                                       # False: the candle that proves the turn must itself still be outside the band (strict)

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
]


def monitored_symbols():
    allowed = [s['symbol'] for s in TRADING_SYMBOLS]
    if ONLY_SYMBOLS:
        return [s for s in ONLY_SYMBOLS if s in allowed] or allowed
    return allowed


# ============================================================
# RUNTIME STATE
# ============================================================

symbol_data    = {}
ind_cache      = {}                # symbol / symbol+T5 -> cached FINAL indicator values (see mt5_series)
symbol_data5   = {}                # the 5-tick series has its OWN signal state per symbol (key = symbol + T5)
T5             = "_5t"            # suffix that marks the 5-tick series in logs / dashboard keys
data_lock      = threading.RLock()
running        = True
ws_app         = None

dashboard_data = {
    'scratch':       {},   # symbol -> 1-row scratch deque the strategy code writes to
    'candles':       {},   # (unused)
    'signals':       {},   # symbol -> deque of events, newest first
    'sym_decisions': {},   # symbol -> deque of FIRE / REJECT decisions, newest first
    'decisions':     [],   # scratch list the strategy code writes to (drained every candle)
}

conn = {'connected': False, 'fmt': None, 'last_msg': 0.0, 'last_error': '', 'connects': 0, 'opened_at': 0.0}
req_counter = itertools.count(1)
req_map     = {}     # req_id -> symbol
sub_map     = {}     # subscription id -> symbol
probe       = {'event': threading.Event(), 'ok': False, 'error': None, 'req_id': None}

# older-history loading (start-up only)
hist_state    = {'open': False}   # True while the start-up history is being collected
hist_load     = {}                # symbol -> {'ticks': {epoch: price}, 'buf': [live ticks meanwhile], 'exhausted': bool}
older_req     = {}                # req_id -> symbol  (older-batch requests)
older_pending = set()             # req_ids of the current round still waiting for an answer
csv_lock    = threading.Lock()

# ============================================================
# STRATEGY CODE — copied unchanged from the trading bot
# ============================================================

def get_symbol_name(symbol):
    if symbol.endswith(T5):
        return get_symbol_name(symbol[:-len(T5)]) + f" ({TICKS_PER_CANDLE_2}-tick)"
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


def calc_confidence(depth_cleared, min_depth, excursion_candles):
    """
    Heuristic 0-100 confidence score for a FIRE signal, built entirely from
    values the strategy already computes — NOT a machine-learning output,
    just a transparent composite of two signal-strength factors:

      - depth:   how far the excursion exceeded the minimum required
                 depth before curving back (deeper = more conviction)
      - candles: how many candles the excursion sustained before
                 re-entry (more confirmation, up to a point)

    Each factor is capped and weighted, then combined. Can be re-tuned
    later without touching anything else that depends on it.
    """
    depth_ratio  = min(depth_cleared / min_depth, 2.0) / 2.0 if min_depth > 0 else 0.5
    candle_score = min(excursion_candles / 5.0, 1.0)

    confidence = (depth_ratio * 0.6 + candle_score * 0.4) * 100
    return round(max(5.0, min(99.0, confidence)), 1)


def _log_decision(symbol, direction, decision, confidence, detail):
    """decision is 'FIRE' or 'REJECT'. confidence is None for rejects."""
    dashboard_data['decisions'].insert(0, {
        'time': get_dt(), 'ts': datetime.now(),
        'symbol': symbol, 'direction': direction,
        'decision': decision, 'confidence': confidence, 'detail': detail,
    })
    if len(dashboard_data['decisions']) > 200:
        dashboard_data['decisions'].pop()


def _exc_peak_init(tf, side, map_val, bb_up, bb_dn):
    """A new excursion starts on this candle: remember how far MAP is beyond the band AT THIS MOMENT
    (and what 5% of the band width is at this moment). The high/low point is judged against the band of
    the candle it happened on, not against the band of a later candle (the band keeps moving)."""
    tf['exc_peak_depth'] = (map_val - bb_up) if side == 'above' else (bb_dn - map_val)
    tf['exc_peak_min']   = (bb_up - bb_dn) * MIN_EXCURSION_DEPTH_FRAC
    tf['exc_prev_out']   = True


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
    is_htf = HTF_RULES_ONLY and not str(symbol).endswith(T5)   # the 15-tick (higher time frame) series
    if is_htf:
        ext_up, ext_dn = None, None          # external BB removed from the higher time frame
    else:
        ext_up, ext_dn = calc_bb(close_list, EXT_BB_PERIOD, EXT_BB_DEVIATION)
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

    # ── 15-tick only: the normal end (MAP/SIGNAL cross outside the far band) closes the tracked signal ──
    a0 = tf.get('htf_act')
    if a0 and ((a0['dir'] == 'BUY' and cross_event == 'CROSS_ABOVE_UPPER')
               or (a0['dir'] == 'SELL' and cross_event == 'CROSS_BELOW_LOWER')):
        tf['htf_act'] = None

    # ── 15-tick only: a fired BUY/SELL becomes INVALID (cancelled right away on this candle) ──
    if (is_htf and HTF_INVALIDATION and not tf['warming_up']
            and None not in (map_val, sig_val, bb_up, bb_dn)):
        a = tf.get('htf_act')
        if a:
            was_reached = a['reached']                        # far band already reached on an EARLIER candle
            rel_now = 1 if map_val > sig_val else (-1 if map_val < sig_val else 0)
            both_inside = (bb_dn <= map_val <= bb_up) and (bb_dn <= sig_val <= bb_up)
            inv = None
            if a['dir'] == 'BUY':
                if map_val >= bb_up or sig_val >= bb_up:
                    a['reached'] = True                       # lines reached the upper band: no invalidation any more
                if not a['reached']:
                    if a['prev_rel'] > 0 and rel_now < 0 and both_inside:
                        inv = 'INVALID_INSIDE_CROSS'
                    elif map_val < bb_dn and sig_val < bb_dn:
                        inv = 'INVALID_PULL_OUT'
                elif was_reached and map_val <= bb_up and sig_val <= bb_up:
                    inv = 'INVALID_FELL_BACK'                 # reached the upper band, now both back inside, no cross outside
            else:
                if map_val <= bb_dn or sig_val <= bb_dn:
                    a['reached'] = True                       # lines reached the lower band
                if not a['reached']:
                    if a['prev_rel'] < 0 and rel_now > 0 and both_inside:
                        inv = 'INVALID_INSIDE_CROSS'
                    elif map_val > bb_up and sig_val > bb_up:
                        inv = 'INVALID_PULL_OUT'
                elif was_reached and map_val >= bb_dn and sig_val >= bb_dn:
                    inv = 'INVALID_FELL_BACK'                 # reached the lower band, now both back inside, no cross outside
            if rel_now != 0:
                a['prev_rel'] = rel_now
            if inv:
                tf['htf_act'] = None
                cross_event = inv
                print(f"   [{symbol}] {lbl} ✖ {a['dir']} INVALID "
                      f"({'inside cross' if inv.endswith('CROSS') else ('fell back' if inv.endswith('BACK') else 'pull-out')}) "
                      f"MAP={map_val:.4f}  SIG={sig_val:.4f}")

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
            _exc_peak_init(tf, 'below', map_val, bb_up, bb_dn)
            tf['wait_logged']       = False
        # Start a SELL excursion when MAP rises above the upper band
        elif map_val > bb_up:
            tf['excursion_state']   = 'above'
            tf['excursion_both_out'] = (sig_val is not None and sig_val > bb_up)
            tf['excursion_candles'] = 1
            tf['excursion_extreme'] = map_val
            tf['excursion_curved']  = False
            _exc_peak_init(tf, 'above', map_val, bb_up, bb_dn)
            tf['wait_logged']       = False

    elif state == 'below':
        band_width = (bb_up - bb_dn) if (bb_up and bb_dn) else 0
        min_depth  = band_width * MIN_EXCURSION_DEPTH_FRAC

        map_out = map_val < bb_dn
        sig_out = (sig_val is not None) and (sig_val < bb_dn)

        # The low point counts once it was >= 5% of the band width BELOW THE BAND AT THAT MOMENT, and the turn is the
        # first higher MAP after that low - even if that higher MAP is already back inside the band.
        pk_ok = tf.get('exc_peak_depth') is not None and tf['exc_peak_depth'] >= tf.get('exc_peak_min', 0.0)
        if (not map_out) and TURN_CAN_COMPLETE_INSIDE_BAND and tf.get('exc_prev_out') and map_val > prev_map and pk_ok:
            tf['excursion_curved'] = True
        tf['exc_prev_out'] = map_out

        if map_out:
            tf['wait_logged'] = False
            if sig_out:
                tf['excursion_both_out'] = True
            tf['excursion_candles'] += 1
            if map_val < tf['excursion_extreme']:
                tf['excursion_extreme'] = map_val
                tf['exc_peak_depth'] = bb_dn - map_val
                tf['exc_peak_min']   = min_depth
            elif map_val > prev_map:
                if tf.get('exc_peak_depth') is not None and tf['exc_peak_depth'] >= tf.get('exc_peak_min', min_depth):
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
            ext_ok = True if is_htf else ((ext_up is not None) and (close_price > ext_up))
            both_out = tf['excursion_both_out']
            inside_ok = True if is_htf else ((map_val <= bb_up) and (sig_val is None or sig_val <= bb_up))   # truly INSIDE, not through the other side
            if curved and rising and ext_ok and both_out and inside_ok:
                print(f"   [{symbol}] {lbl} ▲ LONG BUY FIRE  "
                      f"MAP={map_val:.4f}  SIG={sig_val:.4f}  BB↓={bb_dn:.4f}  "
                      f"exc={tf['excursion_candles']}c  trough={tf['excursion_extreme']:.4f}  "
                      f"Price={close_price:.5f}")
                fire_result = 'BUY'
                if is_htf:
                    tf['htf_act'] = {'dir': 'BUY', 'reached': False,
                                     'prev_rel': (1 if map_val > sig_val else (-1 if map_val < sig_val else 0))}
                depth_cleared = bb_dn - tf['excursion_extreme']
                confidence = calc_confidence(depth_cleared, min_depth, tf['excursion_candles'])
                _log_decision(symbol, 'BUY', 'FIRE', confidence,
                               f"[{lbl}] Excursion curved after {tf['excursion_candles']} candles, "
                               f"MAP and SIGNAL re-entered above BB↓ while rising, "
                               + (f"price above external BB↑ ({ext_up:.5f})" if ext_up is not None else "no external-BB filter (15-tick rules)"))
            else:
                reasons = []
                if not curved: reasons.append("no curve (too shallow or still falling)")
                if not rising: reasons.append("not rising on re-entry")
                if not both_out: reasons.append("SIGNAL never went outside the band together with MAP")
                if not inside_ok: reasons.append("MAP/SIGNAL jumped past the upper band instead of coming back inside")
                if not ext_ok:
                    reasons.append("price not above external BB↑ "
                                   + (f"({close_price:.5f} <= {ext_up:.5f})" if ext_up is not None else "(band not ready)"))
                print(f"   [{symbol}] {lbl} ▲ LONG BUY re-entry REJECTED — {', '.join(reasons)}")
                _log_decision(symbol, 'BUY', 'REJECT', None, f"[{lbl}] " + ', '.join(reasons))
            tf['excursion_state']   = None
            tf['excursion_both_out'] = False
            tf['excursion_candles'] = 0
            tf['excursion_extreme'] = None
            tf['excursion_curved']  = False
            tf['wait_logged']       = False
            if map_val > bb_up:     # jumped clean through: this candle already begins a SELL excursion (rule 1 must not miss it)
                tf['excursion_state']    = 'above'
                tf['excursion_both_out'] = (sig_val is not None and sig_val > bb_up)
                tf['excursion_candles']  = 1
                tf['excursion_extreme']  = map_val
                _exc_peak_init(tf, 'above', map_val, bb_up, bb_dn)

    elif state == 'above':
        band_width = (bb_up - bb_dn) if (bb_up and bb_dn) else 0
        min_depth  = band_width * MIN_EXCURSION_DEPTH_FRAC

        map_out = map_val > bb_up
        sig_out = (sig_val is not None) and (sig_val > bb_up)

        # The high point counts once it was >= 5% of the band width ABOVE THE BAND AT THAT MOMENT, and the turn is the
        # first lower MAP after that high - even if that lower MAP is already back inside the band.
        pk_ok = tf.get('exc_peak_depth') is not None and tf['exc_peak_depth'] >= tf.get('exc_peak_min', 0.0)
        if (not map_out) and TURN_CAN_COMPLETE_INSIDE_BAND and tf.get('exc_prev_out') and map_val < prev_map and pk_ok:
            tf['excursion_curved'] = True
        tf['exc_prev_out'] = map_out

        if map_out:
            tf['wait_logged'] = False
            if sig_out:
                tf['excursion_both_out'] = True
            tf['excursion_candles'] += 1
            if map_val > tf['excursion_extreme']:
                tf['excursion_extreme'] = map_val
                tf['exc_peak_depth'] = map_val - bb_up
                tf['exc_peak_min']   = min_depth
            elif map_val < prev_map:
                if tf.get('exc_peak_depth') is not None and tf['exc_peak_depth'] >= tf.get('exc_peak_min', min_depth):
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
            ext_ok  = True if is_htf else ((ext_dn is not None) and (close_price < ext_dn))
            both_out = tf['excursion_both_out']
            inside_ok = True if is_htf else ((map_val >= bb_dn) and (sig_val is None or sig_val >= bb_dn))   # truly INSIDE, not through the other side
            if curved and falling and ext_ok and both_out and inside_ok:
                print(f"   [{symbol}] {lbl} ▼ SHORT SELL FIRE  "
                      f"MAP={map_val:.4f}  SIG={sig_val:.4f}  BB↑={bb_up:.4f}  "
                      f"exc={tf['excursion_candles']}c  peak={tf['excursion_extreme']:.4f}  "
                      f"Price={close_price:.5f}")
                fire_result = 'SELL'
                if is_htf:
                    tf['htf_act'] = {'dir': 'SELL', 'reached': False,
                                     'prev_rel': (1 if map_val > sig_val else (-1 if map_val < sig_val else 0))}
                depth_cleared = tf['excursion_extreme'] - bb_up
                confidence = calc_confidence(depth_cleared, min_depth, tf['excursion_candles'])
                _log_decision(symbol, 'SELL', 'FIRE', confidence,
                               f"[{lbl}] Excursion curved after {tf['excursion_candles']} candles, "
                               f"MAP and SIGNAL re-entered below BB↑ while falling, "
                               + (f"price below external BB↓ ({ext_dn:.5f})" if ext_dn is not None else "no external-BB filter (15-tick rules)"))
            else:
                reasons = []
                if not curved:  reasons.append("no curve (too shallow or still rising)")
                if not falling: reasons.append("not falling on re-entry")
                if not both_out: reasons.append("SIGNAL never went outside the band together with MAP")
                if not inside_ok: reasons.append("MAP/SIGNAL jumped past the lower band instead of coming back inside")
                if not ext_ok:
                    reasons.append("price not below external BB↓ "
                                   + (f"({close_price:.5f} >= {ext_dn:.5f})" if ext_dn is not None else "(band not ready)"))
                print(f"   [{symbol}] {lbl} ▼ SHORT SELL re-entry REJECTED — {', '.join(reasons)}")
                _log_decision(symbol, 'SELL', 'REJECT', None, f"[{lbl}] " + ', '.join(reasons))
            tf['excursion_state']   = None
            tf['excursion_both_out'] = False
            tf['excursion_candles'] = 0
            tf['excursion_extreme'] = None
            tf['excursion_curved']  = False
            tf['wait_logged']       = False
            if map_val < bb_dn:     # jumped clean through: this candle already begins a BUY excursion
                tf['excursion_state']    = 'below'
                tf['excursion_both_out'] = (sig_val is not None and sig_val < bb_dn)
                tf['excursion_candles']  = 1
                tf['excursion_extreme']  = map_val
                _exc_peak_init(tf, 'below', map_val, bb_up, bb_dn)

    return fire_result, cross_event


# ============================================================
# TELEGRAM (signals only)
# ============================================================

def send_telegram(message: str, on_fail=None):
    """Send in the background; retry up to 3 times. on_fail() is called only if every attempt failed."""
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    def _send():
        url     = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
        payload = {"chat_id": TELEGRAM_CHAT_ID, "text": message, "parse_mode": "HTML"}
        for attempt in range(1, 4):
            try:
                r = requests.post(url, json=payload, timeout=10)
                if r.status_code == 200:
                    print(f"[{get_ts()}] Telegram sent ✓")
                    return
                print(f"[{get_ts()}] Telegram error (try {attempt}/3): {r.text}")
            except Exception as e:
                print(f"[{get_ts()}] Telegram exception (try {attempt}/3): {e}")
            if attempt < 3:
                time.sleep(attempt)
        if on_fail:
            on_fail()
    threading.Thread(target=_send, daemon=True).start()


# ============================================================
# AUTO-TRADING (Deriv multipliers) — added on top of the signal logic
# The signal logic above/below is unchanged. When a LIVE BUY / SELL signal is
# emitted it is turned into a MULTUP / MULTDOWN contract. HIST and IGNORED
# signals never trade.
# ============================================================

import queue

# ---- Trade settings ----
BASE_STAKE      = 1
TAKE_PROFIT     = 0.30
STOP_LOSS       = 0.60
MAX_OPEN_TRADES = 10

# ---- Recovery trade ----
# When a normal trade LOSES (profit below 0), the NEXT trade that opens is a RECOVERY trade with these settings.
# After that one recovery trade (win or lose) the bot goes back to the normal stake / TP / SL. No further escalation.
RECOVERY_ENABLED = True
RECOVERY_STAKE   = 2
RECOVERY_TP      = 1
RECOVERY_SL      = 1

SYMBOL_MULTIPLIER = {
    "R_10":    2000,
    "R_25":    800,
    "R_50":    400,
    "R_75":    200,
    "R_100":   200,
    "1HZ10V":  2000,
    "1HZ15V":  300,
    "1HZ25V":  800,
    "1HZ30V":  140,
    "1HZ50V":  400,
    "1HZ75V":  200,
    "1HZ90V":  45,
    "1HZ100V": 200,
    "JD10":    300,
    "JD25":    150,
    "JD50":    60,
    "JD75":    50,
    "JD100":   30,
    "stpRNG":  3500,
    "stpRNG2": 2000,
    "stpRNG3": 1500,
    "stpRNG4": 1000,
    "stpRNG5": 500,
}

TRADE_CONTRACT = {'BUY': 'MULTUP', 'SELL': 'MULTDOWN'}   # BUY = price goes up, SELL = price goes down

# True: an EXIT signal also closes that symbol's open trade(s) of that direction.
# False (default): trades are closed only by TAKE_PROFIT / STOP_LOSS.
CLOSE_ON_EXIT = False

# ---- Credentials (environment variables; nothing is stored in this file) ----
#   DERIV_PAT         Personal Access Token with the `trade` scope (or an OAuth access token)
#   DERIV_APP_ID      App ID registered on developers.deriv.com (needed for PAT tokens)
#   DERIV_ACCOUNT_ID  OPTIONAL. Leave it empty and the program finds your DEMO account from the token by itself
#                     (a REAL account is used only when ALLOW_REAL_TRADING=1)
#   DERIV_CURRENCY    optional; otherwise read from the account balance (fallback USD)
#   ALLOW_REAL_TRADING=1   required before the program will trade on a REAL account
DERIV_PAT          = os.environ.get("DERIV_PAT", "")
DERIV_APP_ID       = os.environ.get("DERIV_APP_ID", "")
DERIV_ACCOUNT_ID   = os.environ.get("DERIV_ACCOUNT_ID", "")
DERIV_CURRENCY     = os.environ.get("DERIV_CURRENCY", "")
ALLOW_REAL_TRADING = os.environ.get("ALLOW_REAL_TRADING", "0") == "1"
OTP_URL            = "https://api.derivws.com/trading/v1/options/accounts/{account_id}/otp"

SIGNAL_MAX_AGE_SECONDS = 20     # a queued signal older than this is dropped, never traded late

trade_lock   = threading.RLock()
trade_queue  = queue.Queue()
trader = {
    'enabled':    bool(DERIV_PAT),
    'ready':      False,        # authenticated trading socket is open
    'ws':         None,
    'mode':       None,         # 'DEMO' / 'REAL'
    'currency':   DERIV_CURRENCY or None,
    'last_error': '',
}
open_trades  = {}   # contract_id -> {'symbol', 'direction', 'stake', 'opened'}
pending_buys = {}   # req_id -> {'symbol', 'direction', 'recovery', 'stake', 'tp', 'sl'}   (buy sent, no answer yet)
recovery_state = {'pending': False}   # True = the next trade opened is a RECOVERY trade (in memory only)


def trade_banner():
    return "AUTO-TRADING: MULTUP / MULTDOWN" if trader['enabled'] else "signals only (trading not configured)"


def trade_footer():
    return "Auto-trading is ON (see the trade messages)" if trader['enabled'] else "Signal only — no trade is placed"


def _trade_csv(event, symbol, direction, contract_id, detail, profit=""):
    os.makedirs(LOG_DIR, exist_ok=True)
    path = _csv_path("trades.csv")
    with csv_lock:
        new = not os.path.exists(path)
        with open(path, "a", newline="") as f:
            w = csv.writer(f)
            if new:
                w.writerow(["time", "event", "symbol", "direction", "contract_id", "detail", "profit"])
            w.writerow([get_dt(), event, symbol, direction, contract_id, detail, profit])


def _run_label():
    """Where is the bot running? On GitHub Actions it names the run, otherwise it just says 'local'."""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        return f"GitHub Actions (run #{os.environ.get('GITHUB_RUN_NUMBER', '?')})"
    return "local machine"


_notified = {'started': False, 'error': ''}


def _notify_status(title, body):
    send_telegram(f"🤖 <b>XERO BOT — {title}</b>\n━━━━━━━━━━━━━━━━━━━━\n{body}\nRunning on: {_run_label()}\nTime: {get_dt()}")


def _trade_notify(title, symbol, direction, extra):
    name = get_symbol_name(symbol)
    send_telegram(f"💹 <b>XERO TRADE — {title}</b>\n━━━━━━━━━━━━━━━━━━━━\n"
                  f"Pair: <b>{name}</b>\nSymbol: {symbol}\nDirection: {direction}\n{extra}\n"
                  f"Account: {trader['mode'] or '?'}\nTime: {get_dt()}")


# ---------- called by the signal code ----------

def trader_on_signal(symbol, direction, candle):
    """A LIVE BUY / SELL signal was emitted. Never blocks: it only queues the order."""
    if not trader['enabled']:
        return
    trade_queue.put(('OPEN', symbol, direction, time.time()))


def trader_on_exit(symbol, direction):
    if trader['enabled'] and CLOSE_ON_EXIT:
        trade_queue.put(('CLOSE', symbol, direction, time.time()))


# ---------- order worker ----------

def _trade_worker():
    while running:
        try:
            item = trade_queue.get(timeout=1)
        except queue.Empty:
            continue
        try:
            if item[0] == 'OPEN':
                _open_trade(item[1], item[2], item[3])
            elif item[0] == 'CLOSE':
                _close_trades(item[1], item[2])
        except Exception as e:
            print(f"[{get_ts()}] ⚠ trade worker error: {type(e).__name__}: {e}")


def _skip(symbol, direction, why):
    print(f"[{get_ts()}] [{symbol}] TRADE SKIPPED ({direction}): {why}")
    _trade_csv("SKIPPED", symbol, direction, "", why)


def _open_trade(symbol, direction, queued_at):
    if time.time() - queued_at > SIGNAL_MAX_AGE_SECONDS:
        return _skip(symbol, direction, "signal was too old by the time it could be sent")
    if not trader['ready'] or trader['ws'] is None:
        return _skip(symbol, direction, "trading connection is not ready")
    mult = SYMBOL_MULTIPLIER.get(symbol)
    if mult is None:
        return _skip(symbol, direction, "no multiplier set for this symbol")
    with trade_lock:
        if len(open_trades) + len(pending_buys) >= MAX_OPEN_TRADES:
            return _skip(symbol, direction, f"MAX_OPEN_TRADES ({MAX_OPEN_TRADES}) reached")
        rid = next(req_counter)
        is_rec = bool(RECOVERY_ENABLED and recovery_state['pending'])
        if is_rec:
            recovery_state['pending'] = False      # this trade uses up the recovery turn
        stake, tp, sl = (RECOVERY_STAKE, RECOVERY_TP, RECOVERY_SL) if is_rec else (BASE_STAKE, TAKE_PROFIT, STOP_LOSS)
        pending_buys[rid] = {'symbol': symbol, 'direction': direction, 'recovery': is_rec,
                             'stake': stake, 'tp': tp, 'sl': sl}
    req = {
        "buy":   "1",
        "price": stake,                            # most we are willing to pay = the stake
        "parameters": {
            "amount":            stake,
            "basis":             "stake",
            "contract_type":     TRADE_CONTRACT[direction],
            "currency":          trader['currency'] or "USD",
            "multiplier":        mult,
            "underlying_symbol": symbol,
            "limit_order":       {"take_profit": tp, "stop_loss": sl},
        },
        "req_id": rid,
    }
    try:
        trader['ws'].send(json.dumps(req))
        print(f"[{get_ts()}] [{symbol}] ➜ sending {TRADE_CONTRACT[direction]}{' (RECOVERY)' if is_rec else ''}  "
              f"stake={stake}  x{mult}  TP={tp}  SL={sl}")
    except Exception as e:
        with trade_lock:
            pending_buys.pop(rid, None)
            if is_rec:
                recovery_state['pending'] = True   # the recovery turn was not used

        _skip(symbol, direction, f"send failed: {type(e).__name__}: {e}")


def _close_trades(symbol, direction):
    with trade_lock:
        ids = [cid for cid, t in open_trades.items() if t['symbol'] == symbol and t['direction'] == direction]
    for cid in ids:
        try:
            trader['ws'].send(json.dumps({"sell": cid, "price": 0, "req_id": next(req_counter)}))
            print(f"[{get_ts()}] [{symbol}] ➜ closing {direction} contract {cid} (EXIT signal)")
        except Exception as e:
            print(f"[{get_ts()}] [{symbol}] close failed: {type(e).__name__}: {e}")


# ---------- trading WebSocket (authenticated, separate from the public candle feed) ----------

ACCOUNTS_URL = "https://api.derivws.com/trading/v1/options/accounts"
_resolved_account = {'id': DERIV_ACCOUNT_ID or ""}


def _find_account_id(headers):
    """DERIV_ACCOUNT_ID not set: ask Deriv which accounts this token owns and pick one.
    DEMO by default; a REAL account is chosen only when ALLOW_REAL_TRADING=1."""
    r = requests.get(ACCOUNTS_URL, headers=headers, timeout=15)
    if r.status_code != 200:
        raise RuntimeError(f"Could not list accounts: HTTP {r.status_code} {r.text[:200]}")
    accounts = r.json().get('data') or []
    want = 'real' if ALLOW_REAL_TRADING else 'demo'
    for a in accounts:
        if a.get('account_type') == want and a.get('status', 'active') == 'active' and a.get('account_id'):
            acc = a['account_id']
            print(f"[{get_ts()}] Using {want.upper()} account {acc[:3]}****  (found automatically from the token)")
            return acc
    found = ", ".join(sorted({f"{a.get('account_type')}/{a.get('status')}" for a in accounts})) or "none"
    raise RuntimeError(f"No active {want} account found for this token (accounts seen: {found}). "
                       f"Set DERIV_ACCOUNT_ID yourself or check the token.")


def _get_otp_url():
    headers = {"Authorization": f"Bearer {DERIV_PAT}"}
    if DERIV_APP_ID:
        headers["Deriv-App-ID"] = DERIV_APP_ID
    if not _resolved_account['id']:
        _resolved_account['id'] = _find_account_id(headers)
    r = requests.post(OTP_URL.format(account_id=_resolved_account['id']), headers=headers, timeout=15)
    if r.status_code != 200:
        raise RuntimeError(f"OTP request failed: HTTP {r.status_code} {r.text[:200]}")
    return r.json()['data']['url']


def _t_send(ws, obj):
    ws.send(json.dumps(obj))


def _t_on_open(ws):
    trader['ready'] = True
    print(f"[{get_ts()}] Trading socket connected ({trader['mode']} account)")
    if not _notified['started']:
        _notified['started'] = True
        _notify_status("STARTED ✅",
                       f"Auto-trading is ON ({trader['mode']} account)\n"
                       f"Stake: {BASE_STAKE} | TP: {TAKE_PROFIT} | SL: {STOP_LOSS}\n"
                       f"Recovery after a loss: stake {RECOVERY_STAKE} | TP {RECOVERY_TP} | SL {RECOVERY_SL}\n"
                       f"Max open trades: {MAX_OPEN_TRADES} | Close on EXIT: {CLOSE_ON_EXIT}\n"
                       f"Waiting for live signals — you will get a message for every trade.")
    _notified['error'] = ''
    _t_send(ws, {"balance": 1, "req_id": next(req_counter)})
    _t_send(ws, {"portfolio": 1, "req_id": next(req_counter)})
    with trade_lock:
        ids = list(open_trades)
    for cid in ids:
        _t_send(ws, {"proposal_open_contract": 1, "contract_id": cid, "subscribe": 1, "req_id": next(req_counter)})
    threading.Thread(target=_t_keepalive, args=(ws,), daemon=True).start()


def _t_keepalive(ws):
    n = 0
    while running and trader['ws'] is ws and trader['ready']:
        time.sleep(30)
        if not (running and trader['ws'] is ws and trader['ready']):
            break
        n += 1
        try:
            _t_send(ws, {"ping": 1, "req_id": next(req_counter)})
            if n % 2 == 0:                       # every ~60 s re-check what is really open
                _t_send(ws, {"portfolio": 1, "req_id": next(req_counter)})
        except Exception:
            break


def _t_on_error(ws, error):
    print(f"[{get_ts()}] Trading socket error: {error}")


def _t_on_close(ws, code, msg):
    trader['ready'] = False
    with trade_lock:
        lost = len(pending_buys)
        pending_buys.clear()
    print(f"[{get_ts()}] Trading socket closed: {code} {msg}"
          + (f"  ({lost} order(s) had no answer yet — the next portfolio check will show if they filled)" if lost else ""))


def _t_on_message(ws, message):
    try:
        data = json.loads(message)
    except Exception:
        return
    rid = data.get('req_id')

    if 'error' in data:
        err  = data['error']
        text = f"{err.get('code', '')}: {err.get('message', err)}" if isinstance(err, dict) else str(err)
        with trade_lock:
            p = pending_buys.pop(rid, None)
            if p and p.get('recovery'):
                recovery_state['pending'] = True   # the recovery turn was not used
        if p:
            trader['last_error'] = text
            print(f"[{get_ts()}] [{p['symbol']}] ❌ TRADE REJECTED ({p['direction']}): {text}")
            _trade_csv("REJECTED", p['symbol'], p['direction'], "", text)
            _trade_notify("REJECTED", p['symbol'], p['direction'], f"Reason: {text}")
        else:
            print(f"[{get_ts()}] Trading socket error response: {text}")
        return

    try:
        if isinstance(data.get('buy'), dict):
            _on_buy(ws, rid, data['buy'])
        elif isinstance(data.get('proposal_open_contract'), dict):
            _on_poc(data['proposal_open_contract'])
        elif isinstance(data.get('balance'), dict):
            cur = data['balance'].get('currency')
            if cur and not DERIV_CURRENCY and trader['currency'] != cur:
                trader['currency'] = cur
                print(f"[{get_ts()}] Account currency: {cur}   balance: {data['balance'].get('balance')}")
        elif isinstance(data.get('portfolio'), dict):
            _on_portfolio(data['portfolio'])
        elif isinstance(data.get('sell'), dict):
            print(f"[{get_ts()}] Sell accepted for contract {data['sell'].get('contract_id')}")
    except Exception as e:
        print(f"[{get_ts()}] ⚠ trading message error: {type(e).__name__}: {e}")


def _on_buy(ws, rid, b):
    cid = b.get('contract_id')
    with trade_lock:
        p = pending_buys.pop(rid, None) or {'symbol': '?', 'direction': '?'}
        p.setdefault('recovery', False)
        p.setdefault('tp', TAKE_PROFIT)
        p.setdefault('sl', STOP_LOSS)
        if cid is not None:
            open_trades[cid] = {'symbol': p['symbol'], 'direction': p['direction'],
                                'stake': b.get('buy_price', BASE_STAKE), 'opened': time.time(),
                                'recovery': p['recovery']}
    if cid is None:
        print(f"[{get_ts()}] ⚠ buy response without a contract id: {b}")
        return
    _t_send(ws, {"proposal_open_contract": 1, "contract_id": cid, "subscribe": 1, "req_id": next(req_counter)})
    kind = "RECOVERY" if p['recovery'] else "NORMAL"
    print(f"[{get_ts()}] [{p['symbol']}] ✅ TRADE OPENED ({kind}) {TRADE_CONTRACT.get(p['direction'], '?')}  "
          f"contract={cid}  price={b.get('buy_price')}")
    _trade_csv("OPENED", p['symbol'], p['direction'], cid, f"{kind} buy_price={b.get('buy_price')}")
    _trade_notify("OPENED" + (" (RECOVERY)" if p['recovery'] else ""), p['symbol'], p['direction'],
                  f"Contract: {TRADE_CONTRACT.get(p['direction'], '?')}  #{cid}\n"
                  f"Stake: {b.get('buy_price', p['stake'] if 'stake' in p else BASE_STAKE)}\nTP: {p['tp']}   SL: {p['sl']}")


def _on_poc(c):
    cid = c.get('contract_id')
    if cid is None:
        return
    if not (c.get('is_sold') or c.get('status') in ('sold', 'won', 'lost')):
        return
    with trade_lock:
        t = open_trades.pop(cid, None)
    if t is None:
        return
    profit = c.get('profit')
    print(f"[{get_ts()}] [{t['symbol']}] 🏁 TRADE CLOSED {t['direction']}  contract={cid}  profit={profit}")
    _trade_csv("CLOSED", t['symbol'], t['direction'], cid, f"status={c.get('status')}", profit if profit is not None else "")
    extra = ""
    try:
        was_recovery = bool(t.get('recovery')) or float(t.get('stake') or 0) >= RECOVERY_STAKE
        if RECOVERY_ENABLED and profit is not None and float(profit) < 0 and not was_recovery:
            recovery_state['pending'] = True
            extra = f"\n⚠ Loss on a normal trade — the NEXT trade will be a RECOVERY trade (stake {RECOVERY_STAKE}, TP {RECOVERY_TP}, SL {RECOVERY_SL})."
            print(f"[{get_ts()}] Recovery armed: next trade = stake {RECOVERY_STAKE}, TP {RECOVERY_TP}, SL {RECOVERY_SL}")
    except (TypeError, ValueError):
        pass
    _trade_notify("CLOSED" + (" (RECOVERY)" if t.get('recovery') else ""), t['symbol'], t['direction'],
                  f"Contract: #{cid}\nProfit: {profit}{extra}")


def _on_portfolio(pf):
    """Keep the open-trade count honest: adopt open multiplier contracts, drop ones that are gone."""
    contracts = pf.get('contracts')
    if not isinstance(contracts, list):
        return
    live = {}
    for c in contracts:
        if isinstance(c, dict) and c.get('contract_id') is not None \
                and c.get('contract_type') in ('MULTUP', 'MULTDOWN'):
            live[c['contract_id']] = c
    now = time.time()
    with trade_lock:
        for cid, c in live.items():
            if cid not in open_trades:
                open_trades[cid] = {'symbol': c.get('underlying_symbol') or c.get('symbol') or '?',
                                    'direction': 'BUY' if c.get('contract_type') == 'MULTUP' else 'SELL',
                                    'stake': c.get('buy_price', ''), 'opened': now}
        for cid in [k for k, t in open_trades.items() if k not in live and now - t['opened'] > 30]:
            t = open_trades.pop(cid)
            print(f"[{get_ts()}] [{t['symbol']}] trade {cid} is no longer open (portfolio check)")
            _trade_csv("CLOSED", t['symbol'], t['direction'], cid, "no longer in portfolio")


def _run_trade_ws():
    backoff = 3
    while running:
        try:
            url = _get_otp_url()
        except Exception as e:
            trader['last_error'] = str(e)
            print(f"[{get_ts()}] ❌ Could not get a trading session: {e}  (retrying in {backoff}s)")
            if _notified['error'] != str(e)[:80]:
                _notified['error'] = str(e)[:80]
                _notify_status("TRADING NOT CONNECTED ❌", f"{str(e)[:300]}\nThe bot keeps retrying; signals still run.")
            time.sleep(backoff)
            backoff = min(backoff * 2, 60)
            continue
        backoff = 3
        trader['mode'] = 'DEMO' if '/ws/demo' in url else 'REAL'
        if trader['mode'] == 'REAL' and not ALLOW_REAL_TRADING:
            trader['enabled'] = False
            print(f"[{get_ts()}] ⛔ The trading account is a REAL account. Trading is OFF. "
                  f"Set ALLOW_REAL_TRADING=1 to allow real-money trades.")
            _notify_status("TRADING OFF ⛔", "The account is a REAL account and ALLOW_REAL_TRADING is not set to 1.")
            return
        ws = websocket.WebSocketApp(url, on_open=_t_on_open, on_message=_t_on_message,
                                    on_error=_t_on_error, on_close=_t_on_close)
        trader['ws'] = ws
        ws.run_forever(ping_interval=30, ping_timeout=10)
        trader['ready'] = False
        if running:
            print(f"[{get_ts()}] Trading socket down — reconnecting in 3s ...")
            time.sleep(3)


def start_trader():
    if not trader['enabled']:
        print("  ⚠ Auto-trading is OFF — set DERIV_PAT and DERIV_APP_ID to turn it on.\n"
              "    Signals still run exactly as before.\n")
        _notify_status("STARTED (signals only)", "Auto-trading is OFF: DERIV_PAT is not set. Signals still run.")
        return
    print(f"  Auto-trading: stake {BASE_STAKE}, TP {TAKE_PROFIT}, SL {STOP_LOSS}, max {MAX_OPEN_TRADES} open, "
          f"close on EXIT: {CLOSE_ON_EXIT}")
    print(f"  Recovery after a loss: {'ON' if RECOVERY_ENABLED else 'OFF'}  stake {RECOVERY_STAKE}, TP {RECOVERY_TP}, SL {RECOVERY_SL}\n")
    threading.Thread(target=_trade_worker, daemon=True).start()
    threading.Thread(target=_run_trade_ws, daemon=True).start()


# ============================================================
# PER-SYMBOL STATE
# ============================================================

def init_symbol(symbol):
    if symbol in symbol_data:
        return
    symbol_data[symbol] = {
        'tf':                    _make_tf_state('1M'),
        'closed':                deque(maxlen=3000),   # closed candles, oldest -> newest
        'pending_check':         [],      # live signals waiting to be confirmed / repainted away
        'forming':               None,    # bar 0: candle still being built
        'closed5':               deque(maxlen=6000),  # 5-tick candles, closed, oldest -> newest
        'forming5':              None,    # 5-tick bar 0
        'last_closed_open_time': None,
        'active':                None,    # 'BUY' / 'SELL' until its exit cross
        'last_dir':              None,    # last accepted signal (BUY/SELL alternation)
        'csv_ready':             False,
        'live_candles':          0,
    }
    dashboard_data['scratch'][symbol]       = deque(maxlen=1)
    dashboard_data['signals'][symbol]       = deque(maxlen=300)
    dashboard_data['sym_decisions'][symbol] = deque(maxlen=200)
    # the 5-tick series: same strategy, its own state, signals and logs
    k5 = symbol + T5
    symbol_data5[symbol] = {
        'tf':                    _make_tf_state('5T'),
        'closed':                symbol_data[symbol]['closed5'],   # the very same deque of 5-tick candles
        'pending_check':         [],
        'forming':               None,    # kept in step with symbol_data[symbol]['forming5']
        'last_closed_open_time': None,
        'active':                None,
        'last_dir':              None,
        'csv_ready':             False,
        'live_candles':          0,
    }
    dashboard_data['scratch'][k5]       = deque(maxlen=1)
    dashboard_data['signals'][k5]       = deque(maxlen=300)
    dashboard_data['sym_decisions'][k5] = deque(maxlen=200)


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


_csv_warned = set()
diag_rows = {}      # symbol -> rows of the signal diagnostic (kept in memory, so the dashboard download always works)


def _csv_safe(path, mode, rows, enc="utf-8"):
    """Write rows; if the file is locked (e.g. open in Excel) warn ONCE and carry on instead of crashing."""
    try:
        with open(path, mode, newline="", encoding=enc) as f:
            w = csv.writer(f)
            for r in rows:
                w.writerow(r)
        return True
    except OSError as e:
        if path not in _csv_warned:
            _csv_warned.add(path)
            print(f"[{get_ts()}] WARNING: cannot write {path} ({type(e).__name__}) - is it open in Excel? "
                  f"Close it. The dashboard keeps running.")
        return False


def _init_csv(symbol):
    os.makedirs(LOG_DIR, exist_ok=True)
    with csv_lock:
        _csv_safe(_csv_path(f"{symbol}_candles.csv"), "w", [
            ["time", "open_time_epoch", "open", "high", "low", "close", "map", "signal",
             "intbb_up", "intbb_dn", "extbb_up", "extbb_mid", "extbb_dn", "events", "historical"]])
        diag_rows[symbol] = []
        _csv_safe(_diag_path(symbol), "w", [DIAG_COLS], enc="utf-8-sig")
        sig_path = _csv_path("signals.csv")
        if not os.path.exists(sig_path):
            _csv_safe(sig_path, "w", [
                ["time", "symbol", "event", "close", "map", "signal", "intbb_up", "intbb_dn",
                 "extbb_up", "extbb_dn", "note", "historical"]])


def _write_candle_csv(symbol, c, ts, vals, kinds, historical):
    eu, ed = vals.get('ext_up'), vals.get('ext_dn')
    mid = ((eu + ed) / 2) if eu is not None and ed is not None else None
    with csv_lock:
        _csv_safe(_csv_path(f"{symbol}_candles.csv"), "a", [[
            _fmt_t(ts), c['open_time'], _fnum(c['open']), _fnum(c['high']), _fnum(c['low']),
            _fnum(c['close']), _fnum(vals.get('map')), _fnum(vals.get('sig')),
            _fnum(vals.get('bb_up')), _fnum(vals.get('bb_dn')),
            _fnum(eu), _fnum(mid), _fnum(ed), " | ".join(kinds), 1 if historical else 0]])


def _write_signal_csv(ev):
    with csv_lock:
        _csv_safe(_csv_path("signals.csv"), "a", [[
            _fmt_t(ev['ts']), ev['symbol'], ev['kind'], _fnum(ev['close']), _fnum(ev['map']),
            _fnum(ev['sig']), _fnum(ev['bb_up']), _fnum(ev['bb_dn']),
            _fnum(ev['ext_up']), _fnum(ev['ext_dn']), ev['note'], 1 if ev['historical'] else 0]])


def _diag_path(symbol):
    return _csv_path(f"{symbol}_signal_diagnostic.csv")


DIAG_COLS = [
    "symbol", "time", "open_time_epoch", "historical",
    "open", "high", "low", "close",
    "map", "signal", "intbb_up", "intbb_dn", "band_width", "min_depth_5pct",
    "extbb_up", "extbb_dn",
    # where MAP / SIGNAL are relative to the internal bands on THIS candle
    "map_above_up", "sig_above_up", "map_below_dn", "sig_below_dn",
    "prev_map", "map_rising", "map_falling",
    "close_above_extbb_up", "close_below_extbb_dn",
    # the excursion state machine (before / after this candle)
    "exc_state_before", "exc_state_after",
    "exc_candles_after", "exc_extreme_after", "exc_depth_after",
    "exc_curved_after", "exc_both_out_after",
    # outcome
    "strategy_result",      # BUY / SELL / REJECT BUY / REJECT SELL / blank
    "decision_detail",      # the program's own FIRE / REJECT explanation
    "cross_event", "detected",          # MAP/SIGNAL cross outside the band (used for EXIT)
    "last_dir_before", "last_signal_time", "active_before",
    "final_events",         # BUY / SELL / IGNORED x / EXIT x actually recorded
    "why_ignored",
    "last_dir_after", "active_after",
]


def _tf_snap(tf):
    return {k: tf.get(k) for k in ('excursion_state', 'excursion_candles', 'excursion_extreme',
                                    'excursion_curved', 'excursion_both_out', 'prev_map')}


def _b(x):
    return "" if x is None else (1 if x else 0)


def _write_diag(symbol, sd, c, ts, o, kinds, last_dir_before, active_before, historical):
    """One row per closed candle: every value and condition the strategy used, and what came out."""
    v, pre, post = o['vals'], o['pre'], o['post']
    mp, sg, up, dn = v.get('map'), v.get('sig'), v.get('bb_up'), v.get('bb_dn')
    eu, ed = v.get('ext_up'), v.get('ext_dn')
    width  = (up - dn) if (up is not None and dn is not None) else None
    pm     = pre.get('prev_map')
    ext    = post.get('excursion_extreme')
    state  = post.get('excursion_state')
    depth  = None
    if ext is not None and up is not None and dn is not None:
        depth = (ext - up) if state == 'above' else ((dn - ext) if state == 'below' else None)
    decs   = o.get('decs') or []
    result = ""
    for d in decs:
        if d.startswith('FIRE'):
            result = o['fire'] or ""
        elif d.startswith('REJECT'):
            result = "REJECT " + ("SELL" if pre.get('excursion_state') == 'above' else "BUY")
    if o['fire']:
        result = o['fire']
    late = any(k.startswith('LATE') for k in kinds)
    if late:
        result = "LATE " + str(o['fire'])
    is_sig = any(k in ('BUY', 'SELL') or k.startswith(('IGNORED', 'BLOCKED', 'REPAINTED', 'LATE', 'EXIT', 'INVALID')) for k in kinds)
    if not (is_sig or (DIAG_INCLUDE_REJECTS and result.startswith('REJECT'))):
        return                      # this file only records signals and IGNORED signals
    ignored = any(k.startswith('IGNORED') for k in kinds)
    last_sig_time = sd.get('last_dir_time') if ignored else sd.get('prev_dir_time')
    last_sig_time = _fmt_t(last_sig_time) if last_sig_time else ""
    why = ""
    if late:
        why = (f"On the lines as they were when this candle closed there was NO {o['fire']} (so nothing fired live). "
               f"On the settled lines (as the chart shows them now) it IS a {o['fire']}. "
               f"The indicator repaints, so a live trade would not have seen it.")
    blocked_now = any(k.startswith('BLOCKED') for k in kinds)
    if blocked_now:
        why = f"strategy fired {o['fire']} on this series but no valid {TICKS_PER_CANDLE}-tick {o['fire']} existed at that moment (see the signal note)"
    elif ignored and ONE_OPEN_SIGNAL:
        why = f"strategy fired {o['fire']} but a {active_before} signal is still open (no exit yet); a new signal never closes an open one"
    elif ignored:
        why = (f"strategy fired {o['fire']} but the last accepted signal was ALSO {last_dir_before} "
               f"(at {last_sig_time}); BUY/SELL must alternate. "
               + ("That trade had already EXITED, but the direction memory is not reset by an exit."
                  if not active_before else f"That {active_before} signal is still active (no exit yet)."))
    row = [
        symbol, _fmt_t(ts), c['open_time'], 1 if historical else 0,
        _fnum(c['open']), _fnum(c['high']), _fnum(c['low']), _fnum(c['close']),
        _fnum(mp), _fnum(sg), _fnum(up), _fnum(dn), _fnum(width),
        _fnum(width * MIN_EXCURSION_DEPTH_FRAC if width is not None else None),
        _fnum(eu), _fnum(ed),
        _b(None if mp is None or up is None else mp > up), _b(None if sg is None or up is None else sg > up),
        _b(None if mp is None or dn is None else mp < dn), _b(None if sg is None or dn is None else sg < dn),
        _fnum(pm), _b(None if mp is None or pm is None else mp > pm), _b(None if mp is None or pm is None else mp < pm),
        _b(None if eu is None else c['close'] > eu), _b(None if ed is None else c['close'] < ed),
        pre.get('excursion_state') or "", state or "",
        post.get('excursion_candles') or 0, _fnum(ext), _fnum(depth),
        _b(post.get('excursion_curved')), _b(post.get('excursion_both_out')),
        result, " || ".join(decs), o.get('cross') or "", o.get('detected', 'candle close'),
        last_dir_before or "", last_sig_time, active_before or "",
        " | ".join(kinds), why,
        sd['last_dir'] or "", sd['active'] or "",
    ]
    with csv_lock:
        diag_rows.setdefault(symbol, []).append(row)
        _csv_safe(_diag_path(symbol), "a", [row])


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

    name = get_symbol_name(symbol)
    tfl  = f"{TICKS_PER_CANDLE_2}-tick" if symbol.endswith(T5) else f"{TICKS_PER_CANDLE}-tick"
    base = kind.split()[-1]
    if kind in ('BUY', 'SELL'):
        head = f"🟢 {SIGNAL_ICON[kind]} {SIGNAL_LABEL[kind]} SIGNAL"
    elif kind.startswith('EXIT'):
        head = f"🚪 EXIT {SIGNAL_LABEL[base]}"
    elif kind.startswith('INVALID'):
        head = f"❌ {SIGNAL_LABEL[base]} signal INVALID — cancelled"
    elif kind.startswith('BLOCKED'):
        head = f"🚫 {SIGNAL_LABEL[base]} signal BLOCKED (no valid {TICKS_PER_CANDLE}-tick {SIGNAL_LABEL[base]})"
    elif kind.startswith('REPAINTED'):
        head = f"♻ {SIGNAL_LABEL[base]} signal REPAINTED AWAY"
    elif kind.startswith('CONFIRMED'):
        head = f"✅ {SIGNAL_LABEL[base]} signal CONFIRMED (lines are final)"
    else:
        head = f"⚪ {SIGNAL_LABEL[base]} ignored"
    print(f"[{get_ts()}] [{symbol}] {head}  candle={_fmt_t(ts)}  close={c['close']}  "
          f"MAP={_fnum(ev['map'])}  SIG={_fnum(ev['sig'])}  — {note}")

    # Telegram: ONE short line per 5-tick entry that passed the 15-tick gate, and one when that entry exits.
    # Nothing is sent for 15-tick signals, INVALID, BLOCKED, IGNORED, REPAINTED or CONFIRMED rows.
    if _is_ltf(symbol) and (kind in ('BUY', 'SELL') or kind.startswith('EXIT')):
        send_telegram(f"{kind} — {get_symbol_name(symbol[:-len(T5)])}",
                      on_fail=(lambda: sd.__setitem__('alert_failed', True)) if kind in ('BUY', 'SELL') else None)
        # AUTO-TRADING: same trigger as the alert above (live, accepted 5-tick entry). The trade is placed on the
        # BASE symbol (e.g. R_50), because the contract, multiplier and symbol list belong to the real market.
        _base_symbol = symbol[:-len(T5)]
        if kind in ('BUY', 'SELL'):
            trader_on_signal(_base_symbol, kind, c)
        else:
            trader_on_exit(_base_symbol, kind.split()[-1])
    return ev


def _is_ltf(symbol):
    """True for the 5-tick series (lower time frame = the entry); the 15-tick series is the higher time frame (the gate)."""
    return str(symbol).endswith(T5)


def _htf_sync_windows(sd, c):
    """15-tick only: keep a time record of when each BUY / SELL was valid (from its candle's last tick until it ended)."""
    e = c.get('end') or c.get('open_time')
    w = sd.setdefault('windows', [])
    if w and w[-1]['end'] is None and (sd['active'] != w[-1]['dir'] or sd.get('active_since') != w[-1]['since']):
        w[-1]['end'] = e
    if sd['active'] and (not w or w[-1]['end'] is not None):
        w.append({'dir': sd['active'], 'since': sd.get('active_since'), 'start': e, 'end': None})
    if len(w) > 500:
        del w[:-500]


def _htf_permits(key, direction, tc):
    """
    Is there a valid 15-tick signal in this direction at time tc (epoch of the last tick of the 5-tick candle)?
    Returns (True, window) / (False, reason).
    """
    s15 = symbol_data.get(key[:-len(T5)])
    if s15 is None or s15.get('last_closed_open_time') is None:
        return False, f"the {TICKS_PER_CANDLE}-tick candles are not loaded yet"
    ws = s15.get('windows', [])
    for w in reversed(ws):
        if w['dir'] == direction and w['start'] < tc and (w['end'] is None or tc <= w['end']):
            return True, w
    past = [w for w in ws if w['dir'] == direction and w['start'] < tc]
    if past:
        return False, (f"no valid {TICKS_PER_CANDLE}-tick {direction}: the last one (from {_fmt_t(past[-1]['since'])}) "
                       f"ended at {_fmt_t(_open_dt(past[-1]['end']))}")
    return False, f"no valid {TICKS_PER_CANDLE}-tick {direction} yet"


def _signal_update(symbol, sd, c, ts, fire, cross, historical, vals):
    """Signal bookkeeping for ONE series.

    15-tick (higher time frame, the gate): BUY / SELL by the five rules, cancelled when invalid, ends on the MAP/SIGNAL
    cross outside the far band. 5-tick (lower time frame, the entry): its BUY / SELL counts only while a 15-tick signal in
    the same direction is valid (otherwise BLOCKED); it ends only on its own cross outside the far band.

    An EXIT is only SENT (Telegram) when the trade it closes was opened by a LIVE alert that was delivered.
    A trade opened while replaying history at start-up (never alerted) or whose entry alert failed to deliver
    is still closed internally, but its exit is recorded as HIST and nothing is sent."""
    kinds = []
    act = sd['active']
    alerted    = sd.get('active_live', False) and not sd.get('alert_failed', False)   # you were TOLD about this open trade
    quiet_exit = not alerted        # an exit is only ever sent for a trade you were told about ...
    late       = historical and alerted   # ... including one whose exit cross happened while the connection was down
    sfx = ("  [found after a reconnect: this cross happened at the candle time shown, while the connection was down]"
           if late else ("" if (historical or alerted) else "  [no live entry alert for this trade — exit not sent]"))

    if act in ('BUY', 'SELL') and cross in ('INVALID_INSIDE_CROSS', 'INVALID_PULL_OUT', 'INVALID_FELL_BACK'):
        far = "upper" if act == 'BUY' else "lower"
        if cross == 'INVALID_INSIDE_CROSS':
            why = ("MAP crossed " + ("below" if act == 'BUY' else "above") + " SIGNAL inside the bands"
                   f" — {act} cancelled (lines never reached the {far} band)")
        elif cross == 'INVALID_PULL_OUT':
            why = ("MAP and SIGNAL both back " + ("below the lower" if act == 'BUY' else "above the upper") + " band"
                   f" — {act} cancelled (lines never reached the {far} band)")
        else:
            why = (f"MAP and SIGNAL reached the {far} band but fell back inside it without crossing outside the band"
                   f" — {act} cancelled")
        _emit(symbol, sd, 'INVALID ' + act, c, ts, why + sfx, quiet_exit, vals)
        kinds.append('INVALID ' + act); sd['active'] = None; sd['active_live'] = False; sd['last_dir'] = None
    elif act == 'BUY' and cross == 'CROSS_ABOVE_UPPER':
        _emit(symbol, sd, 'EXIT BUY', c, ts, "MAP/SIGNAL crossed above the upper band" + sfx, quiet_exit, vals)
        kinds.append('EXIT BUY'); sd['active'] = None; sd['active_live'] = False
    elif act == 'SELL' and cross == 'CROSS_BELOW_LOWER':
        _emit(symbol, sd, 'EXIT SELL', c, ts, "MAP/SIGNAL crossed below the lower band" + sfx, quiet_exit, vals)
        kinds.append('EXIT SELL'); sd['active'] = None; sd['active_live'] = False

    if fire:
        permit_note = ""
        blocked = False
        if ONE_OPEN_SIGNAL and sd['active'] is not None:
            # a signal ends ONLY on its own exit (15-tick: or when cancelled as invalid); a new signal never closes it
            op = sd['active']
            _emit(symbol, sd, 'IGNORED ' + fire, c, ts,
                  f"a {op} signal is still open (no exit yet: MAP/SIGNAL have not crossed outside the "
                  f"{'upper' if op == 'BUY' else 'lower'} band)", historical, vals)
            kinds.append('IGNORED ' + fire)
        elif (not ONE_OPEN_SIGNAL) and ALTERNATE_SIGNALS and fire == sd['last_dir']:
            _emit(symbol, sd, 'IGNORED ' + fire, c, ts,
                  "same direction as the last signal — waiting for the opposite", historical, vals)
            kinds.append('IGNORED ' + fire)
        else:
            if DUAL_TF_GATE and _is_ltf(symbol):
                ok, info15 = _htf_permits(symbol, fire, c.get('end') or c.get('open_time'))
                if ok:
                    permit_note = f" | {TICKS_PER_CANDLE}-tick {fire} valid since {_fmt_t(info15['since'])}"
                else:
                    blocked = True
                    _emit(symbol, sd, 'BLOCKED ' + fire, c, ts, f"{TICKS_PER_CANDLE_2}-tick {fire} blocked — {info15}",
                          historical, vals)
                    kinds.append('BLOCKED ' + fire)
            if not blocked:
                if (not ONE_OPEN_SIGNAL) and sd['active'] is not None and sd['active'] != fire:
                    _emit(symbol, sd, 'EXIT ' + sd['active'], c, ts, "opposite signal arrived" + sfx, quiet_exit, vals)
                    kinds.append('EXIT ' + sd['active'])
                sd['active'] = fire
                sd['active_since'] = ts
                sd['active_live'] = not historical      # only a LIVE entry may later send an exit
                sd['alert_failed'] = False
                sd['last_dir'] = fire
                sd['prev_dir_time'] = sd.get('last_dir_time')
                sd['last_dir_time'] = ts
                note = ("MAP & SIGNAL out, curved, both back inside, MAP "
                        + ("rising" if fire == 'BUY' else "falling")
                        + ("" if (HTF_RULES_ONLY and not symbol.endswith(T5)) else ", price beyond external BB")
                        + permit_note)
                _emit(symbol, sd, fire, c, ts, note, historical, vals)
                kinds.append(fire)
    if not _is_ltf(symbol):
        _htf_sync_windows(sd, c)
    return kinds


def _drain_decisions(symbol, ts):
    """Move the strategy's FIRE/REJECT notes into a per-symbol list, stamped with the candle time."""
    d = dashboard_data['decisions']
    fresh = list(d)
    d.clear()
    for e in reversed(fresh):
        e['time'] = _fmt_t(ts)
        dashboard_data['sym_decisions'][symbol].appendleft(e)


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


def mt5_series(c, keys=None, cache=None, settled=-1):
    """
    MAP, SIGNAL and the two IntBB bands for every candle, as MT5 draws them now.
    MAP    = (TMA22-TMA34) + (TMA33-TMA18) + (TMA14-TMA29)
    SIGNAL = SMA(5) of MAP
    bands  = Bollinger(89, 1.0) on SIGNAL (BB_ON_SIGNAL) or on MAP; MT5 draws none on bar 0.

    Speed-up (the numbers are identical, nothing is approximated): a bar whose MAP already has all the
    NEWER candles it will ever use (index <= `settled`) can never change again. Those final values are kept
    in `cache` (keyed by the candle's open time `keys[t]`) so only the last ~35 bars are recalculated.
    """
    n         = len(c)
    first_map = max(PERIOD1, PERIOD2, PERIOD3, PERIOD4, PERIOD5, PERIOD6) - 1
    use_cache = cache is not None and keys is not None
    cm = cache['mp'] if use_cache else None
    cs = cache['sg'] if use_cache else None
    cb = cache['bb'] if use_cache else None
    mp = [None] * n
    sg = [None] * n
    up = [None] * n
    dn = [None] * n
    for t in range(first_map, n):
        if use_cache and t <= settled and keys[t] in cm:
            mp[t] = cm[keys[t]]
            continue
        mp[t] = (_tma_mt5(c, t, PERIOD2) - _tma_mt5(c, t, PERIOD1)
                 + _tma_mt5(c, t, PERIOD4) - _tma_mt5(c, t, PERIOD3)
                 + _tma_mt5(c, t, PERIOD6) - _tma_mt5(c, t, PERIOD5))
        if use_cache and t <= settled:
            cm[keys[t]] = mp[t]
    first_sig = first_map + SIGNAL_PERIOD - 1
    for t in range(first_sig, n):
        if use_cache and t <= settled and keys[t] in cs:
            sg[t] = cs[keys[t]]
            continue
        sg[t] = sum(mp[t - SIGNAL_PERIOD + 1:t + 1]) / SIGNAL_PERIOD
        if use_cache and t <= settled:
            cs[keys[t]] = sg[t]
    src      = sg if BB_ON_SIGNAL else mp
    first_bb = (first_sig if BB_ON_SIGNAL else first_map) + BB_PERIOD - 1
    for t in range(first_bb, n - 1):
        if use_cache and t <= settled and keys[t] in cb:
            up[t], dn[t] = cb[keys[t]]
            continue
        seg  = src[t - BB_PERIOD + 1:t + 1]
        mean = sum(seg) / BB_PERIOD
        std  = math.sqrt(sum((x - mean) ** 2 for x in seg) / BB_PERIOD)
        up[t] = mean + BB_DEVIATION * std
        dn[t] = mean - BB_DEVIATION * std
        if use_cache and t <= settled:
            cb[keys[t]] = (up[t], dn[t])
    return mp, sg, up, dn


def _tail_len():
    """Candles needed to judge the last MT5_REPLAY_BARS bars (MAP 33 + SIGNAL 4 + bands 88 + margin)."""
    return MT5_REPLAY_BARS + 130


def _mt5_eval(symbol, closed_list, forming, keep_from, print_last, with_forming=False):
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
    cache  = ind_cache.setdefault(symbol, {'mp': {}, 'sg': {}, 'bb': {}})
    if len(cache['mp']) > 6000:                       # keep it bounded; it simply refills
        for part in cache.values():
            part.clear()
    keys    = [b['open_time'] for b in bars]
    span    = max(PERIOD1, PERIOD2, PERIOD3, PERIOD4, PERIOD5, PERIOD6) - 1   # newest candle a bar's MAP can look at
    settled = n_closed - 1 - span                     # bars up to here have all their newer candles: final
    mp, sg, up, dn = mt5_series(closes, keys, cache, settled)
    dashboard_data['scratch'].setdefault(symbol, deque(maxlen=1))
    dashboard_data['decisions'].clear()

    for t in range(n_closed):
        b      = bars[t]
        candle = {'open': b['open'], 'high': b['high'], 'low': b['low'], 'close': b['close']}
        ts     = _open_dt(b['open_time'])
        inject = {'map': mp[t], 'sig': sg[t], 'bb_up': up[t], 'bb_dn': dn[t]}
        pre = _tf_snap(tf)
        if print_last and t == n_closed - 1:
            fire, cross = _process_candle(tf, candle, symbol, 'scratch', ts, inject)
        else:
            with contextlib.redirect_stdout(io.StringIO()):
                fire, cross = _process_candle(tf, candle, symbol, 'scratch', ts, inject)
        out.append({
            'open_time': b['open_time'], 'fire': fire, 'cross': cross,
            'pre': pre, 'post': _tf_snap(tf),
            'decs': [f"{e['decision']}: {e['detail']}" for e in reversed(dashboard_data['decisions'])],
            'vals': {'map': tf['last_map'], 'sig': tf['last_sig'],
                     'bb_up': tf['last_bb_up'], 'bb_dn': tf['last_bb_dn'],
                     'ext_up': tf.get('last_ext_up'), 'ext_dn': tf.get('last_ext_dn')},
        })
        if t >= keep_from:
            _drain_decisions(symbol, ts)
        else:
            dashboard_data['decisions'].clear()

    if with_forming and forming:
        # The forming candle is judged too: its close is the CURRENT price (no need to wait for it to close).
        # MT5 draws no IntBB on bar 0, so it uses the band of the last closed candle.
        t      = n_closed
        b      = bars[t]
        candle = {'open': b['open'], 'high': b['high'], 'low': b['low'], 'close': b['close']}
        ts     = _open_dt(b['open_time'])
        bu = up[t] if up[t] is not None else up[t - 1]
        bd = dn[t] if dn[t] is not None else dn[t - 1]
        inject = {'map': mp[t], 'sig': sg[t], 'bb_up': bu, 'bb_dn': bd}
        pre = _tf_snap(tf)
        with contextlib.redirect_stdout(io.StringIO()):
            fire, cross = _process_candle(tf, candle, symbol, 'scratch', ts, inject)
        out.append({
            'open_time': b['open_time'], 'fire': fire, 'cross': cross,
            'pre': pre, 'post': _tf_snap(tf),
            'decs': [f"{e['decision']}: {e['detail']}" for e in reversed(dashboard_data['decisions'])],
            'vals': {'map': tf['last_map'], 'sig': tf['last_sig'],
                     'bb_up': tf['last_bb_up'], 'bb_dn': tf['last_bb_dn'],
                     'ext_up': tf.get('last_ext_up'), 'ext_dn': tf.get('last_ext_dn')},
        })
        dashboard_data['decisions'].clear()
    return tf, out


def _history_pass(symbol, sd, n_new):
    """Judge newly received past candles on the final (repainted) lines, like MT5's history chart."""
    closed = list(sd['closed'])
    use    = closed[-(n_new + _tail_len()):]
    tf, out = _mt5_eval(symbol, use, sd['forming'], keep_from=len(use) - n_new, print_last=False)
    sd['tf'] = tf
    fk = sd.setdefault('fired_keys', set())
    for o in out:                                   # history signals must not be signalled a second time by the live scan
        if o['fire']:
            fk.add((o['open_time'], o['fire']))
            _remember_fired(sd, o['fire'], o['open_time'])
    for o, c in zip(out[-n_new:], use[-n_new:]):
        ts    = _open_dt(c['open_time'])
        ld, ac = sd['last_dir'], sd['active']
        kinds = _signal_update(symbol, sd, c, ts, o['fire'], o['cross'], True, o['vals'])
        _write_candle_csv(symbol, c, ts, o['vals'], kinds, True)
        _write_diag(symbol, sd, c, ts, o, kinds, ld, ac, True)


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


def _near_fired(sd, direction, open_time, order):
    """True if this direction was already signalled on a candle within SIGNAL_CLUSTER_CANDLES of this one."""
    pos = order.get(open_time)
    if pos is None:
        return False
    for ot in sd.setdefault('fired_dir', {}).get(direction, ()):
        p2 = order.get(ot)
        if p2 is not None and abs(p2 - pos) <= SIGNAL_CLUSTER_CANDLES:
            return True
    return False


def _remember_fired(sd, direction, open_time):
    dq = sd.setdefault('fired_dir', {}).setdefault(direction, deque(maxlen=40))
    dq.append(open_time)


def _scan_signals(symbol, sd):
    """
    Judge the trading rules on the lines as they are RIGHT NOW, including the forming candle (no close needed).
    Only the forming candle (bar 0) is judged here - older candles are never scanned for signals.
    A setup on the forming candle is signalled once (BUY/SELL alternation still applies).
    """
    closed  = list(sd['closed'])[-_tail_len():]
    forming = dict(sd['forming']) if sd['forming'] else None
    if len(closed) < 5 or forming is None:
        return
    _, out = _mt5_eval(symbol, closed, forming, keep_from=10 ** 9, print_last=False, with_forming=True)
    n = len(out)
    if n < 2:
        return
    cands = closed + [forming]
    order = {c['open_time']: i for i, c in enumerate(cands)}
    fired = sd.setdefault('fired_keys', set())
    if len(fired) > 3000:
        fired.clear()
    idx = n - 1                                     # the forming candle, nothing older
    o = out[idx]
    if o['cross'] and not o['fire'] and sd['active'] is not None:
        # EXIT is judged on EVERY tick as well (not only when a candle closes): the MAP/SIGNAL cross outside
        # the band is caught the moment the live lines show it, instead of waiting for a close that may
        # never show it (the lines repaint, so a cross seen on the final chart may not exist at close time)
        cnd0 = cands[idx]
        ts0  = _open_dt(cnd0['open_time'])
        ld0, ac0 = sd['last_dir'], sd['active']
        kinds0 = _signal_update(symbol, sd, cnd0, ts0, None, o['cross'], False, o['vals'])
        if kinds0:
            o['detected'] = "intrabar: forming candle, no close needed"
            _write_diag(symbol, sd, cnd0, ts0, o, kinds0, ld0, ac0, False)
    if not o['fire']:
        return
    key = (o['open_time'], o['fire'])
    if key in fired:
        return
    fired.add(key)
    if _near_fired(sd, o['fire'], o['open_time'], order):
        return                                      # same setup, already signalled on a neighbouring candle
    _remember_fired(sd, o['fire'], o['open_time'])
    sd.setdefault('live_fired', set()).add(o['open_time'])
    cnd  = cands[idx]
    ts   = _open_dt(cnd['open_time'])
    o['detected'] = "intrabar: forming candle, no close needed"
    ld, ac = sd['last_dir'], sd['active']
    kinds = _signal_update(symbol, sd, cnd, ts, o['fire'], None, False, o['vals'])
    print(f"[{get_ts()}] [{symbol}] {o['fire']} detected - {o['detected']}  (candle {_fmt_t(ts)})")
    _write_diag(symbol, sd, cnd, ts, o, kinds, ld, ac, False)
    if o['fire'] in kinds:
        sd['pending_check'].append({'open_time': cnd['open_time'], 'kind': o['fire'], 'born': len(sd['closed']),
                                    'candle': dict(cnd), 'ts': ts, 'vals': o['vals']})


def _late_check(symbol, sd, tail, out):
    """Hindsight: a candle that nothing fired on when it closed, but that the settled lines now show as a signal."""
    live_times = sd.setdefault('live_times', set())
    fired      = sd.setdefault('live_fired', set())
    logged     = sd.setdefault('late_logged', set())
    n = len(tail)
    if n <= LATE_SETTLE_CANDLES or len(out) < n:
        return
    for o, cnd in zip(out[-n:-LATE_SETTLE_CANDLES], tail[:-LATE_SETTLE_CANDLES]):
        ot = cnd['open_time']
        if not o['fire'] or ot not in live_times or ot in fired or ot in logged:
            continue
        logged.add(ot)
        ts = _open_dt(ot)
        print(f"[{get_ts()}] [{symbol}] LATE {o['fire']} at {_fmt_t(ts)}: not seen live, visible only after the lines repainted")
        _write_diag(symbol, sd, cnd, ts, o, [f"LATE {o['fire']}"], sd['last_dir'], sd['active'], False)


def _live_eval(symbol, sd, c):
    """A candle has just closed: judge it on the lines MT5 shows right now (bar 0 = the new candle)."""
    tail = list(sd['closed'])[-_tail_len():]
    tf, out = _mt5_eval(symbol, tail, sd['forming'], keep_from=len(tail) - 1, print_last=True)
    sd['tf'] = tf
    if not out:
        return
    last  = out[-1]
    ts    = _open_dt(c['open_time'])
    ld, ac = sd['last_dir'], sd['active']
    fire_now = last['fire']
    if fire_now:                                    # already signalled intrabar / by the scan? then don't repeat it
        fk = sd.setdefault('fired_keys', set())
        order = {x['open_time']: i for i, x in enumerate(tail)}
        if (last['open_time'], fire_now) in fk:
            fire_now = None
        else:
            fk.add((last['open_time'], fire_now))
            if _near_fired(sd, fire_now, last['open_time'], order):
                fire_now = None
            else:
                _remember_fired(sd, fire_now, last['open_time'])
    kinds = _signal_update(symbol, sd, c, ts, fire_now, last['cross'], False, last['vals'])
    _write_candle_csv(symbol, c, ts, last['vals'], kinds, False)
    _write_diag(symbol, sd, c, ts, last, kinds, ld, ac, False)
    sd['live_candles'] += 1
    sd.setdefault('live_times', set()).add(c['open_time'])
    if last['fire']:
        sd.setdefault('live_fired', set()).add(c['open_time'])
    if last['fire'] and last['fire'] in kinds:
        sd['pending_check'].append({'open_time': c['open_time'], 'kind': last['fire'], 'born': len(sd['closed']),
                                    'candle': dict(c), 'ts': ts, 'vals': last['vals']})
    _repaint_check(symbol, sd, {o['open_time']: o['fire'] for o in out})
    _late_check(symbol, sd, tail, out)


# ============================================================
# CANDLE STREAM (history + live updates)
# ============================================================

def _new_candle(epoch, price):
    """Start a tick candle. open_time = epoch of its first tick, end = epoch of its latest tick, n = ticks so far."""
    return {'open_time': int(epoch), 'open': price, 'high': price, 'low': price, 'close': price,
            'n': 1, 'end': int(epoch)}


def _add_to_candle(c, epoch, price):
    c['high']  = max(c['high'], price)
    c['low']   = min(c['low'], price)
    c['close'] = price
    c['n']    += 1
    c['end']   = int(epoch)


def _last_end(sd):
    """Epoch of the newest tick already used (forming candle first, else the last closed candle)."""
    if sd['forming'] is not None:
        return sd['forming']['end']
    if sd['closed']:
        return sd['closed'][-1]['end']
    return None


def _ticks_to_candles(ticks, cutoff, tpc=None):
    """
    ticks : [(epoch, price), ...]. Ticks at or before `cutoff` (end of the last closed candle) are skipped.
    Groups the rest into candles of TICKS_PER_CANDLE ticks, oldest -> newest; the last one may be incomplete.
    """
    uniq = {}
    for e, pr in ticks:
        uniq[int(e)] = float(pr)
    tpc = tpc or TICKS_PER_CANDLE
    out, cur = [], None
    for e in sorted(uniq):
        if cutoff is not None and e <= cutoff:
            continue
        if cur is None or cur['n'] >= tpc:
            cur = _new_candle(e, uniq[e])
            out.append(cur)
        else:
            _add_to_candle(cur, e, uniq[e])
    return out


def _last_end5(sd):
    if sd['forming5'] is not None:
        return sd['forming5']['end']
    if sd['closed5']:
        return sd['closed5'][-1]['end']
    return None


def _ingest_history5(symbol, ticks):
    """Build the 5-tick candles from the same history ticks. The newest one is bar 0 (forming)."""
    sd = symbol_data[symbol]
    cutoff  = sd['closed5'][-1]['end'] if sd['closed5'] else None
    candles = _ticks_to_candles(ticks, cutoff, TICKS_PER_CANDLE_2)
    if not candles:
        return
    for c in candles[:-1]:
        sd['closed5'].append(c)
    sd['forming5'] = candles[-1]
    print(f"[{get_ts()}] [{symbol}] {TICKS_PER_CANDLE_2}-tick history: {len(sd['closed5'])} closed candles")
    sd5 = symbol_data5[symbol]
    sd5['forming'] = sd['forming5']
    k5 = symbol + T5
    if not sd5['csv_ready']:
        _init_csv(k5)
        sd5['csv_ready'] = True
    n_new = len(candles) - 1
    if n_new > 0:
        _history_pass(k5, sd5, min(n_new, 500))    # HIST signals only; marks them so the live scan never repeats them


def _ingest_tick5(symbol, sd, epoch, price):
    """Live tick for the 5-tick series: same rules as the 15-tick one (the next tick opens the new bar 0)."""
    le = _last_end5(sd)
    if le is not None and epoch <= le:
        return
    f = sd['forming5']
    just_closed = None
    if f is None:
        sd['forming5'] = _new_candle(epoch, price)
    elif f['n'] < TICKS_PER_CANDLE_2:
        _add_to_candle(f, epoch, price)
    else:
        sd['closed5'].append(f)
        sd['forming5'] = _new_candle(epoch, price)
        just_closed = f
    sd5 = symbol_data5.get(symbol)
    if sd5 is None:
        return
    sd5['forming'] = sd['forming5']
    k5 = symbol + T5
    if not sd5['csv_ready']:
        _init_csv(k5)
        sd5['csv_ready'] = True
    if just_closed is not None:
        try:
            _live_eval(k5, sd5, just_closed)
        except Exception as e:
            print(f"[{get_ts()}] [{k5}] close-eval error: {type(e).__name__}: {e}")
    sd5['tick_n'] = sd5.get('tick_n', 0) + 1
    if sd5['tick_n'] % INTRABAR_EVERY_N_TICKS == 0:
        try:
            _scan_signals(k5, sd5)
        except Exception as e:
            print(f"[{get_ts()}] [{k5}] scan error: {type(e).__name__}: {e}")


def _ingest_history(symbol, candles):
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


def _ingest_tick(symbol, epoch, price):
    """
    Live tick. It either updates bar 0 (the candle being built) or, when bar 0 already holds
    TICKS_PER_CANDLE ticks, it opens a new bar 0 and the previous candle has closed.
    """
    hl = hist_load.get(symbol)
    if hl is not None:                  # start-up history still being collected: park the tick, replay it afterwards
        hl['buf'].append((epoch, price))
        return
    sd = symbol_data[symbol]
    _ingest_tick5(symbol, sd, epoch, price)     # 5-tick series is independent of the 15-tick one
    le = _last_end(sd)
    if le is not None and epoch <= le:
        return                          # duplicate / stale tick: ignore
    f = sd['forming']
    if f is None:
        sd['forming'] = _new_candle(epoch, price)
    elif f['n'] < TICKS_PER_CANDLE:
        _add_to_candle(f, epoch, price)
    else:
        sd['forming'] = _new_candle(epoch, price)   # the new candle is bar 0 BEFORE judging, as in MT5
        lp = sd['last_closed_open_time']
        if lp is None or f['open_time'] > lp:
            sd['closed'].append(f)
            sd['last_closed_open_time'] = f['open_time']
            _live_eval(symbol, sd, f)
    sd['tick_n'] = sd.get('tick_n', 0) + 1
    if (not HTF_JUDGE_ON_CLOSE_ONLY) and sd['tick_n'] % INTRABAR_EVERY_N_TICKS == 0:
        try:
            _scan_signals(symbol, sd)
        except Exception as e:
            print(f"[{get_ts()}] [{symbol}] scan error: {type(e).__name__}: {e}")


def _symbol_for(data, rid, sub_id, extra=None):
    sym = req_map.get(rid) or sub_map.get(sub_id)
    if sym:
        return sym
    echo = data.get('echo_req') or {}
    for cand in (extra, echo.get('underlying_symbol'), echo.get('ticks_history')):
        if isinstance(cand, str) and cand in symbol_data:
            return cand
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
        if rid in older_req:
            _older_batch_failed(rid)
            print(f"[{get_ts()}] ❌ Deriv error on an older-history request for {req_map.get(rid, '?')}: {text}")
            return
        if probe['req_id'] is not None and rid == probe['req_id']:
            probe['error'] = text
            probe['event'].set()
        else:
            print(f"[{get_ts()}] ❌ Deriv error for {req_map.get(rid, '?')}: {text}")
        return

    try:
        if isinstance(data.get('history'), dict):
            if rid in older_req:                 # answer to an older-batch request
                _on_older_batch(rid, data['history'])
                return
            sub_id = (data.get('subscription') or {}).get('id')
            sym    = _symbol_for(data, rid, sub_id)
            if sym and sub_id:
                sub_map[sub_id] = sym
            if probe['req_id'] is not None and rid == probe['req_id']:
                probe['ok'] = True
                probe['event'].set()
            if sym:
                h     = data['history']
                ticks = list(zip(h.get('times') or [], h.get('prices') or []))
                with data_lock:
                    sd = symbol_data[sym]
                    if EXTRA_HISTORY_BATCHES > 0 and hist_state['open'] and not sd['closed']:
                        # first load: keep the ticks, older batches are added before candles are built
                        hl = hist_load.setdefault(sym, {'ticks': {}, 'buf': [], 'exhausted': False})
                        for e, pr in ticks:
                            hl['ticks'][int(e)] = float(pr)
                    else:
                        # continue exactly after the last CLOSED candle (a reconnect re-sends old ticks)
                        cutoff  = sd['closed'][-1]['end'] if sd['closed'] else None
                        candles = _ticks_to_candles(ticks, cutoff)
                        _ingest_history(sym, candles)
                        _ingest_history5(sym, ticks)

        elif isinstance(data.get('tick'), dict):
            t      = data['tick']
            sub_id = t.get('id') or (data.get('subscription') or {}).get('id')
            sym    = _symbol_for(data, rid, sub_id, t.get('symbol') or t.get('underlying_symbol'))
            if sym:
                if sub_id:
                    sub_map[sub_id] = sym
                with data_lock:
                    _ingest_tick(sym, int(t['epoch']), float(t['quote']))
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


def _build_request(symbol, fmt, req_id):
    req = {
        "style":       "ticks",
        "end":         "latest",
        "count":       min(HISTORY_COUNT * TICKS_PER_CANDLE, 5000),
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


def _send_sub(symbol, fmt):
    rid = next(req_counter)
    req_map[rid] = symbol
    ws_app.send(json.dumps(_build_request(symbol, fmt, rid)))
    return rid


# ------------------------------------------------------------
# OLDER HISTORY (start-up only): fetch extra batches of older ticks, join them, then build candles
# ------------------------------------------------------------

def _build_older_request(symbol, fmt, req_id, end_epoch):
    """Same request as the first one, but ending at `end_epoch`, a fixed size, and no live subscription."""
    req = _build_request(symbol, fmt, req_id)
    req["end"]   = int(end_epoch)
    req["count"] = OLDER_BATCH_TICKS
    req.pop("subscribe", None)
    return req


def _on_older_batch(rid, h):
    """An older batch arrived: add its ticks to that symbol's collection."""
    with data_lock:
        sym = older_req.pop(rid, None)
        older_pending.discard(rid)
        hl = hist_load.get(sym)
        if hl is None:
            return                      # loading already finished (late answer): ignore
        added = 0
        for e, pr in zip(h.get('times') or [], h.get('prices') or []):
            e = int(e)
            if e not in hl['ticks']:
                hl['ticks'][e] = float(pr)
                added += 1
        if added == 0:
            hl['exhausted'] = True      # nothing older available: stop asking for this symbol


def _older_batch_failed(rid):
    with data_lock:
        older_req.pop(rid, None)
        older_pending.discard(rid)


def _finish_history(sym):
    """Build the candles from ALL collected ticks, then replay the live ticks that arrived meanwhile."""
    with data_lock:
        hl = hist_load.pop(sym, None)       # removed first, so replayed ticks are processed normally
        if hl is None:
            return
        ticks   = sorted(hl['ticks'].items())
        candles = _ticks_to_candles(ticks, None)
        print(f"[{get_ts()}] [{sym}] {len(ticks)} ticks joined -> {len(candles)} candles")
        _ingest_history(sym, candles)
        _ingest_history5(sym, ticks)
        for e, pr in hl['buf']:
            _ingest_tick(sym, e, pr)


def _load_older_history(my_conn):
    """Runs after the first requests were sent. Fetches older ticks in rounds, then builds all candles."""
    def alive():
        return running and conn['connected'] and conn['connects'] == my_conn
    try:
        syms = monitored_symbols()
        # wait (at most 20 s) for the first answers
        t0 = time.time()
        while time.time() - t0 < 20:
            if not alive():
                return
            with data_lock:
                missing = [s for s in syms if s not in hist_load]
            if not missing:
                break
            time.sleep(0.3)
        for rnd in range(1, EXTRA_HISTORY_BATCHES + 1):
            with data_lock:
                older_pending.clear()
            sent = 0
            for s in syms:
                if not alive():
                    return
                with data_lock:
                    hl = hist_load.get(s)
                    if not hl or hl['exhausted'] or not hl['ticks']:
                        continue
                    oldest = min(hl['ticks'])
                    rid = next(req_counter)
                    req_map[rid]  = s
                    older_req[rid] = s
                    older_pending.add(rid)
                ws_app.send(json.dumps(_build_older_request(s, conn['fmt'], rid, oldest - 1)))
                sent += 1
                time.sleep(OLDER_REQUEST_GAP)
            t1 = time.time()
            while time.time() - t1 < OLDER_WAIT_SECONDS:
                if not alive():
                    return
                with data_lock:
                    if not older_pending:
                        break
                time.sleep(0.2)
            print(f"[{get_ts()}] Older history round {rnd}/{EXTRA_HISTORY_BATCHES}: asked {sent} symbols")
        with data_lock:
            names = list(hist_load)
        for s in names:
            _finish_history(s)
        print(f"[{get_ts()}] History ready for {len(names)} symbols")
    finally:
        if conn['connects'] == my_conn:
            hist_state['open'] = False


def _subscribe_all():
    """Runs in its own thread after the socket opens."""
    my_conn = conn['connects']
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
        for s in syms:
            if not running or not conn['connected']:
                return
            _send_sub(s, conn['fmt'])
            time.sleep(0.25)
        print(f"[{get_ts()}] Subscribed to candles for {len(monitored_symbols())} symbols")
        if EXTRA_HISTORY_BATCHES > 0:
            print(f"[{get_ts()}] Fetching older history ({EXTRA_HISTORY_BATCHES} extra batches per symbol) - this takes about a minute ...")
            _load_older_history(my_conn)
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
        hist_load.clear(); older_req.clear(); older_pending.clear()
        hist_state['open'] = True
        for sd in symbol_data.values():
            sd['forming'] = None      # history will be re-sent and fills any gap
            sd['forming5'] = None
        for sd5 in symbol_data5.values():
            sd5['forming'] = None
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
            init_symbol(s)
    threading.Thread(target=_run_ws, daemon=True).start()
    threading.Thread(target=_watchdog, daemon=True).start()


# ============================================================
# DASH DASHBOARD
# ============================================================

app = dash.Dash(__name__, external_stylesheets=[dbc.themes.DARKLY])

_sym_options = [{"label": f"{s['name']}  ({s['symbol']})", "value": s['symbol']} for s in TRADING_SYMBOLS]

app.layout = dbc.Container([
    dbc.Row(dbc.Col(html.H1(
        f"XERO AI SOFTWARE  ·  {TICKS_PER_CANDLE}-TICK + {TICKS_PER_CANDLE_2}-TICK SIGNAL MONITOR  ·  signals only (no trading)",
        className="text-center text-primary mb-1",
        style={"fontSize": "1.3rem", "letterSpacing": "2px"}))),
    dbc.Row(dbc.Col(html.H6(
        f"{TICKS_PER_CANDLE}-tick candles built from Deriv ticks  |  MT5-exact lines (repainting included)  |  IntBB({BB_PERIOD},{BB_DEVIATION}) on {'SIGNAL' if BB_ON_SIGNAL else 'MAP'}  |  "
        f"ExtBB({EXT_BB_PERIOD},{EXT_BB_DEVIATION}) on price  |  times = UTC{TIME_OFFSET_HOURS:+d}h",
        className="text-center text-secondary mb-2", style={"fontSize": "0.75rem"}))),
    dbc.Row(dbc.Col(html.H4(id='live-time', className="text-center text-warning mb-2"))),
    dbc.Row(dbc.Col(html.Div(id='status-bar', className="mb-2"))),
    dbc.Row(dbc.Col(html.Div(id='map-readout', className="mb-2"))),

    dbc.Row([
        dbc.Col([html.Label("Symbol:", className="text-white fw-bold"),
                 dcc.Dropdown(id='sym-dd', options=_sym_options,
                              value=monitored_symbols()[0], clearable=False,
                              style={"color": "#000"})], md=3),
        dbc.Col([html.Label("Why signals fired / exited / were IGNORED:", className="text-white fw-bold"),
                 html.Div([dbc.Button(f"⬇ {TICKS_PER_CANDLE}-tick diagnostic CSV", id='dl-btn', color='info', size='sm', className="me-2"),
                           dbc.Button(f"⬇ {TICKS_PER_CANDLE_2}-tick diagnostic CSV", id='dl-btn5', color='info', size='sm'),
                           dcc.Download(id='dl-csv'), dcc.Download(id='dl-csv5')])], md=3),
        dbc.Col([html.Label(f"{TICKS_PER_CANDLE}-tick candles to display:", className="text-white fw-bold"),
                 dcc.Slider(id='candle-window', min=20, max=300, step=10, value=100,
                            marks={20: '20', 100: '100', 200: '200', 300: '300'})], md=3),
        dbc.Col([html.Label(f"{TICKS_PER_CANDLE_2}-tick candles to display:", className="text-white fw-bold"),
                 dcc.Slider(id='candle-window-5', min=30, max=600, step=10, value=200,
                            marks={30: '30', 200: '200', 400: '400', 600: '600'})], md=3),
    ], className="mb-2"),

    dcc.Graph(id='main-chart', style={'height': '980px', 'width': '100%'}, config={'responsive': True}),

    dbc.Row([
        dbc.Col([html.H6("Signals for this symbol (newest first)", className="text-info mt-3"),
                 html.Div(id='signals-table')], md=7),
        dbc.Col([html.H6("Why setups fired or were rejected", className="text-info mt-3"),
                 html.Div(id='decisions-table')], md=5),
    ]),

    dcc.Interval(id='interval', interval=1000, n_intervals=0),
], fluid=True, className="bg-dark p-3")


def _draw_panel(fig, col, closed, forming, candle_win, tpc, events, show_legend):
    """
    Draws ONE tick-candle panel into column `col`: price + ExtBB on row 1, MAP / SIGNAL / IntBB on row 2.
    MAP, SIGNAL and the bands are calculated from THIS panel's own candles (MT5-exact, repainting included).
    Returns an info dict for the readout (empty if there are no candles yet).
    """
    if not closed:
        return {}
    bars     = closed + ([forming] if forming else [])
    closes   = [b['close'] for b in bars]
    mp, sg, up, dn = mt5_series(closes)
    n        = len(bars)
    n_closed = len(closed)
    times    = [_open_dt(b['open_time']) for b in bars]
    lo       = max(0, n_closed - candle_win)
    t0       = times[lo]
    idx_all  = range(lo, n)
    sl       = show_legend

    fig.add_trace(go.Candlestick(
        x=[times[i] for i in range(lo, n_closed)],
        open=[bars[i]['open'] for i in range(lo, n_closed)], high=[bars[i]['high'] for i in range(lo, n_closed)],
        low=[bars[i]['low'] for i in range(lo, n_closed)], close=[bars[i]['close'] for i in range(lo, n_closed)],
        name=f'{tpc}-tick candles', showlegend=sl,
        increasing_line_color='#26a69a', decreasing_line_color='#ef5350'), row=1, col=col)
    if forming:
        fig.add_trace(go.Candlestick(
            x=[times[n_closed]], open=[forming['open']], high=[forming['high']], low=[forming['low']],
            close=[forming['close']], name=f'{tpc}t bar 0 (forming)', showlegend=sl,
            increasing=dict(line=dict(color='#ffd54f', width=2), fillcolor='rgba(255,213,79,0.15)'),
            decreasing=dict(line=dict(color='#ffd54f', width=2), fillcolor='rgba(255,213,79,0.15)')),
            row=1, col=col)

    # external Bollinger on price
    ex_t, ex_u, ex_m, ex_d = [], [], [], []
    hide_ext = HTF_RULES_ONLY and tpc == TICKS_PER_CANDLE and tpc != TICKS_PER_CANDLE_2
    for i in ([] if hide_ext else idx_all):
        if i >= EXT_BB_PERIOD - 1:
            u_, d_ = calc_bb(closes[i - EXT_BB_PERIOD + 1:i + 1], EXT_BB_PERIOD, EXT_BB_DEVIATION)
            ex_t.append(times[i]); ex_u.append(u_); ex_d.append(d_); ex_m.append((u_ + d_) / 2)
    if ex_t:
        nm = f'ExtBB({EXT_BB_PERIOD},{EXT_BB_DEVIATION})'
        fig.add_trace(go.Scatter(x=ex_t, y=ex_u, mode='lines', name=nm + ' upper', showlegend=sl,
            line=dict(color='#4caf50', width=1.2)), row=1, col=col)
        fig.add_trace(go.Scatter(x=ex_t, y=ex_m, mode='lines', name=nm + ' mid', showlegend=sl,
            line=dict(color='#4caf50', width=1, dash='dot')), row=1, col=col)
        fig.add_trace(go.Scatter(x=ex_t, y=ex_d, mode='lines', name=nm + ' lower', showlegend=sl,
            line=dict(color='#4caf50', width=1.2)), row=1, col=col)

    # signal markers (each panel shows the signals of its own series)
    if events:
        for kind, (sym_, colr, label) in {'BUY': ('triangle-up', '#00e676', 'BUY signal'),
                                          'SELL': ('triangle-down', '#ff5252', 'SELL signal')}.items():
            ev = [e for e in events if e['kind'] == kind and e['ts'] >= t0]
            if ev:
                fig.add_trace(go.Scatter(x=[e['ts'] for e in ev], y=[e['close'] for e in ev], mode='markers',
                    name=label, showlegend=sl, marker=dict(symbol=sym_, size=15, color=colr,
                                            line=dict(color='white', width=1))), row=1, col=col)
        for pref, nm, mk in (('EXIT', 'EXIT', dict(symbol='x', size=12, color='#ffffff')),
                             ('INVALID', 'invalid (cancelled)', dict(symbol='x-thin-open', size=16, color='#ff1744')),
                             ('BLOCKED', 'blocked (no 15-tick)', dict(symbol='square-open', size=11, color='#ff9800')),
                             ('IGNORED', 'ignored', dict(symbol='circle-open', size=11, color='#9e9e9e')),
                             ('REPAINTED', 'repainted away', dict(symbol='x', size=18, color='#ff9800')),
                             ('CONFIRMED', 'confirmed', dict(symbol='diamond-open', size=14, color='#00e5ff'))):
            ev = [e for e in events if e['kind'].startswith(pref) and e['ts'] >= t0]
            if ev:
                fig.add_trace(go.Scatter(x=[e['ts'] for e in ev], y=[e['close'] for e in ev], mode='markers',
                    name=nm, showlegend=sl, marker=mk), row=1, col=col)

    def line(vals, nm, **kw):
        pts = [(times[i], vals[i]) for i in idx_all if vals[i] is not None]
        if pts:
            fig.add_trace(go.Scatter(x=[p[0] for p in pts], y=[p[1] for p in pts],
                                     mode='lines', name=nm, showlegend=sl, **kw), row=2, col=col)
    line(mp, 'MAP',    line=dict(color='#ffd700', width=2))
    line(sg, 'Signal', line=dict(color='#42a5f5', width=1.5, dash='dot'))
    bb_src = 'SIGNAL' if BB_ON_SIGNAL else 'MAP'
    line(up, f'IntBB↑({BB_PERIOD},{BB_DEVIATION}) on {bb_src}', line=dict(color='#26a69a', width=1, dash='dash'))
    line(dn, f'IntBB↓({BB_PERIOD},{BB_DEVIATION}) on {bb_src}', line=dict(color='#ef5350', width=1, dash='dash'))
    fig.add_hline(y=0, line=dict(color='rgba(255,255,255,0.15)', width=1, dash='dash'), row=2, col=col)

    # y axes: fit the visible candles (price) and the visible indicator lines (MAP row) with some air
    pv = [bars[i]['low'] for i in idx_all] + [bars[i]['high'] for i in idx_all] + ex_u + ex_d
    if pv:
        lo_p, hi_p = min(pv), max(pv)
        pad_p = (hi_p - lo_p) * 0.08 or 0.01
        fig.update_yaxes(range=[lo_p - pad_p, hi_p + pad_p], autorange=False, row=1, col=col)
    ind = [v[i] for v in (mp, sg, up, dn) for i in idx_all if v[i] is not None]
    if ind:
        lo_, hi_ = min(ind), max(ind)
        rng = (hi_ - lo_) or 1.0
        fig.update_yaxes(range=[lo_ - rng * 0.15, hi_ + rng * 0.15], autorange=False, row=2, col=col)

    # x axis: average candle spacing (tick candles are not equally long) + a little room on the right
    gap = (times[-1] - times[lo]) / max(1, n - 1 - lo)
    if gap.total_seconds() <= 0:
        gap = timedelta(seconds=10)
    shown = n_closed - lo
    pad = max(4, int(shown * 0.08))
    fig.update_xaxes(range=[times[lo] - gap, times[-1] + gap * pad], row=1, col=col)
    fig.update_xaxes(range=[times[lo] - gap, times[-1] + gap * pad], row=2, col=col)

    ext_last = (ex_u[-1], ex_d[-1]) if ex_t else (None, None)
    i1, i0 = n_closed - 1, (n_closed if forming else None)
    return {'bar1_time': times[i1], 'bar1': bars[i1], 'bar1_vals': (mp[i1], sg[i1], up[i1], dn[i1]),
            'bar0_time': times[i0] if i0 is not None else None,
            'bar0': forming, 'bar0_vals': (mp[i0], sg[i0]) if i0 is not None else None,
            'ext': ext_last, 'tpc': tpc}


def _build_chart(sel_sym, candle_win, candle_win5):
    """
    Returns (figure, info15, info5).
    Left half  = 15-tick candles + their own MAP/SIGNAL/IntBB.
    Right half = 5-tick candles  + their own MAP/SIGNAL/IntBB (calculated from the 5-tick closes).
    """
    from plotly.subplots import make_subplots
    with data_lock:
        sd       = symbol_data.get(sel_sym)
        closed   = list(sd['closed'])[-(candle_win + _tail_len()):] if sd else []
        forming  = dict(sd['forming']) if sd and sd['forming'] else None
        closed5  = list(sd['closed5'])[-(candle_win5 + _tail_len()):] if sd else []
        forming5 = dict(sd['forming5']) if sd and sd['forming5'] else None
        events   = list(dashboard_data['signals'].get(sel_sym, []))
        events5  = list(dashboard_data['signals'].get(sel_sym + T5, []))

    fig = make_subplots(rows=2, cols=2, shared_xaxes=True,
                        column_widths=[0.5, 0.5], row_heights=[0.62, 0.38],
                        horizontal_spacing=0.035, vertical_spacing=0.05)
    info  = _draw_panel(fig, 1, closed,  forming,  candle_win,  TICKS_PER_CANDLE,   events, True)
    info5 = _draw_panel(fig, 2, closed5, forming5, candle_win5, TICKS_PER_CANDLE_2, events5, False)

    if not info and not info5:
        fig.add_annotation(text="Waiting for candles from Deriv ...", xref="paper", yref="paper",
                           x=0.5, y=0.5, showarrow=False, font=dict(size=14, color="orange"))
    for x_, txt, colr in ((0.24, f"{TICKS_PER_CANDLE}-TICK CANDLES", "#42a5f5"),
                          (0.76, f"{TICKS_PER_CANDLE_2}-TICK CANDLES", "#80deea")):
        fig.add_annotation(text=f"<b>{txt}</b>", xref="paper", yref="paper", x=x_, y=1.035,
                           showarrow=False, font=dict(size=13, color=colr), xanchor="center", yanchor="bottom")

    fig.update_layout(template='plotly_dark', hovermode='x unified', height=980,
                      margin=dict(l=55, r=20, t=45, b=85), plot_bgcolor='#0d1117', paper_bgcolor='#080c10',
                      showlegend=True,
                      legend=dict(orientation='h', y=-0.07, x=0.5, xanchor='center', font=dict(size=10)),
                      uirevision=f"{sel_sym}-{candle_win}-{candle_win5}")
    fig.update_xaxes(gridcolor='#161e28', rangeslider_visible=False)
    fig.update_yaxes(gridcolor='#161e28')
    return fig, info, info5


def _table(header, body_rows):
    return dbc.Table([html.Thead(html.Tr([html.Th(h) for h in header])), html.Tbody(body_rows)],
                     bordered=True, color="dark", hover=True, size='sm', className="table-dark",
                     style={"fontSize": "0.75rem"})


def _diag_csv_text(key):
    """The signal diagnostic of one series (key = symbol, or symbol + T5), built from memory so it is never locked."""
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(DIAG_COLS)
    with csv_lock:
        for r in diag_rows.get(key, []):
            w.writerow(r)
    return "\ufeff" + buf.getvalue()


@app.callback(Output('dl-csv', 'data'), Input('dl-btn', 'n_clicks'),
              State('sym-dd', 'value'), prevent_initial_call=True)
def download_diag(n_clicks, sel_sym):
    """15-tick series: signals, exits, IGNORED and rejected setups."""
    return dcc.send_string(_diag_csv_text(sel_sym), f"{sel_sym}_signal_diagnostic.csv")


@app.callback(Output('dl-csv5', 'data'), Input('dl-btn5', 'n_clicks'),
              State('sym-dd', 'value'), prevent_initial_call=True)
def download_diag5(n_clicks, sel_sym):
    """5-tick series: signals, exits, IGNORED and rejected setups."""
    return dcc.send_string(_diag_csv_text(sel_sym + T5), f"{sel_sym}{T5}_signal_diagnostic.csv")


@app.callback(
    [Output('live-time', 'children'), Output('status-bar', 'children'), Output('map-readout', 'children'),
     Output('main-chart', 'figure'), Output('signals-table', 'children'), Output('decisions-table', 'children')],
    [Input('interval', 'n_intervals'), Input('sym-dd', 'value'), Input('candle-window', 'value'),
     Input('candle-window-5', 'value')])
def refresh(n, sel_sym, cw, cw5):
    with data_lock:
        sd      = symbol_data.get(sel_sym)
        events  = sorted(list(dashboard_data['signals'].get(sel_sym, []))[:60]
                         + list(dashboard_data['signals'].get(sel_sym + T5, []))[:60],
                         key=lambda e: e['ts'], reverse=True)[:80]
        decs    = sorted(list(dashboard_data['sym_decisions'].get(sel_sym, []))[:40]
                         + [dict(e, direction=e['direction'] + f" ({TICKS_PER_CANDLE_2}t)")
                            for e in list(dashboard_data['sym_decisions'].get(sel_sym + T5, []))[:40]],
                         key=lambda e: e['ts'], reverse=True)[:60]
        sd5     = symbol_data5.get(sel_sym)
        n_ready = sum(1 for s in symbol_data.values() if not s['tf']['warming_up'])
        n_syms  = len(symbol_data)
        live    = sum(s['live_candles'] for s in symbol_data.values())
    tf = sd['tf'] if sd else {}

    status = html.Div([
        html.Span("● CONNECTED" if conn['connected'] else "● DISCONNECTED",
                  className=("text-success" if conn['connected'] else "text-danger") + " fw-bold me-4"),
        html.Span(f"Request layout: {conn['fmt'] if conn['fmt'] is not None else 'negotiating'}", className="text-secondary me-4"),
        html.Span(f"Symbols ready: {n_ready}/{n_syms}", className="text-info me-4"),
        html.Span(f"Live candles closed: {live}", className="text-info me-4"),
        html.Span(f"Last data: {int(time.time() - conn['last_msg'])}s ago" if conn['last_msg'] else "No data yet",
                  className="text-secondary me-4"),
        html.Span(f"Last error: {conn['last_error']}" if conn['last_error'] else "", className="text-danger"),
    ], className="d-flex flex-wrap p-2", style={"backgroundColor": "#0a0f16", "border": "1px solid #1e2d3d",
                                                 "borderRadius": "4px", "fontSize": "0.8rem"})

    fig, info, info5 = _build_chart(sel_sym, cw, cw5)

    def f5(x):
        return "—" if x is None else f"{x:.5f}"
    if info:
        b1, b0 = info['bar1'], info['bar0']
        m1, s1, u1, d1 = info['bar1_vals']
        lines = [html.Div(f"Bar 1 (last closed, {_fmt_t(info['bar1_time'])})   "
                          f"O {b1['open']}  H {b1['high']}  L {b1['low']}  C {b1['close']}   |   "
                          f"MAP {f5(m1)}   SIGNAL {f5(s1)}   IntBB↑ {f5(u1)}   IntBB↓ {f5(d1)}", className="text-warning")]
        if b0:
            m0, s0 = info['bar0_vals']
            lines.append(html.Div(f"Bar 0 (forming, {_fmt_t(info['bar0_time'])})   "
                                  f"O {b0['open']}  H {b0['high']}  L {b0['low']}  C {b0['close']}   |   "
                                  f"MAP {f5(m0)}   SIGNAL {f5(s0)}   (changes with every tick, as in MT5)",
                                  style={"color": "#ffd54f"}))
        mid = (f"ExtBB↑ {tf.get('last_ext_up'):.5f}  ExtBB↓ {tf.get('last_ext_dn'):.5f}"
               if tf.get('last_ext_up') is not None
               else ("ExtBB removed on the 15-tick series" if HTF_RULES_ONLY else "ExtBB loading"))
        lines.append(html.Div(mid, style={"color": "#4caf50"}))
    else:
        lines = [html.Div("no data yet", className="text-secondary")]
    if info5:
        b1, b0 = info5['bar1'], info5['bar0']
        m1, s1, u1, d1 = info5['bar1_vals']
        t5 = info5['tpc']
        lines.append(html.Div(f"[{t5}-tick] Bar 1 ({_fmt_t(info5['bar1_time'])})   "
                              f"O {b1['open']}  H {b1['high']}  L {b1['low']}  C {b1['close']}   |   "
                              f"MAP {f5(m1)}   SIGNAL {f5(s1)}   IntBB↑ {f5(u1)}   IntBB↓ {f5(d1)}",
                              style={"color": "#80deea"}))
        if b0:
            m0, s0 = info5['bar0_vals']
            lines.append(html.Div(f"[{t5}-tick] Bar 0 (forming)   C {b0['close']}   |   MAP {f5(m0)}   SIGNAL {f5(s0)}",
                                  style={"color": "#b2ebf2"}))
    state = (f"Active: {sd['active'] or 'none'}   Last signal: {sd['last_dir'] or 'none'}   "
             f"Excursion: {tf.get('excursion_state') or 'none'}   "
             f"Bands on: {'SIGNAL' if BB_ON_SIGNAL else 'MAP'}") if sd else ""
    lines.append(html.Div(state, className="text-info"))
    if sd and DUAL_TF_GATE:
        w15 = (sd.get('windows') or [None])[-1]
        w15 = w15 if (w15 and w15['end'] is None) else None
        lines.append(html.Div(f"{TICKS_PER_CANDLE}-tick permission: "
                              + (f"{w15['dir']} valid since {_fmt_t(w15['since'])}" if w15
                                 else f"none ({TICKS_PER_CANDLE_2}-tick signals are BLOCKED)"),
                              style={"color": "#ff9800"}))
    if sd5:
        tf5s = sd5['tf']
        lines.append(html.Div(f"[{TICKS_PER_CANDLE_2}-tick] Active: {sd5['active'] or 'none'}   Last signal: {sd5['last_dir'] or 'none'}   "
                              f"Excursion: {tf5s.get('excursion_state') or 'none'}", style={"color": "#80deea"}))
    readout = html.Div(lines, className="p-2", style={"backgroundColor": "#0a0f16", "border": "1px solid #1e2d3d",
                                                      "borderRadius": "4px", "fontSize": "0.8rem"})

    kind_cls = {'BUY': 'text-success', 'SELL': 'text-danger'}
    sig_rows = [html.Tr([
        html.Td(_fmt_t(e['ts'])),
        html.Td(e['kind'], className=kind_cls.get(e['kind'], 'text-secondary' if e['kind'].startswith('IGN')
                                                     else 'text-warning' if e['kind'].startswith('BLOCKED') else 'text-white')),
        html.Td(f"{e['close']}"), html.Td(f"{e['map']:.4f}" if e['map'] is not None else ""),
        html.Td(f"{e['sig']:.4f}" if e['sig'] is not None else ""),
        html.Td("HIST" if e['historical'] else "LIVE", className="text-secondary"),
        html.Td((f"[{TICKS_PER_CANDLE_2}-tick] " if e['symbol'].endswith(T5) else f"[{TICKS_PER_CANDLE}-tick] ") + e['note'],
                className="text-secondary"),
    ]) for e in events] or [html.Tr([html.Td("No signals yet", colSpan=7, className="text-secondary")])]
    dec_rows = [html.Tr([
        html.Td(e['time']), html.Td(e['direction'], className=kind_cls.get(e['direction'], '')),
        html.Td(e['decision'], className="text-success" if e['decision'] == 'FIRE' else "text-warning"),
        html.Td(e['detail'], className="text-secondary"),
    ]) for e in decs] or [html.Tr([html.Td("Nothing yet", colSpan=4, className="text-secondary")])]

    return (datetime.now().strftime("%Y-%m-%d %H:%M:%S"), status, readout,
            fig,
            _table(["Candle", "Event", "Close", "MAP", "SIGNAL", "", "Note"], sig_rows),
            _table(["Candle", "Dir", "Result", "Detail"], dec_rows))


def run_dashboard():
    print(f"\n{'='*70}\n[{get_ts()}] Dashboard → http://localhost:8050\n{'='*70}\n")
    app.run(debug=False, host='0.0.0.0', port=8050)


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    print("\n" + "=" * 70)
    print(f"XERO AI SOFTWARE — {TICKS_PER_CANDLE}-TICK SIGNAL MONITOR  ({trade_banner()})")
    print("=" * 70)
    print(f"  Candles     : {TICKS_PER_CANDLE}-tick candles built from real Deriv ticks (public, no login)")
    print(f"  Endpoint    : {WS_URL}")
    print(f"  Symbols     : {len(monitored_symbols())}")
    print(f"  Indicator   : MT5-exact (repainting included), IntBB({BB_PERIOD},{BB_DEVIATION}) on {'SIGNAL' if BB_ON_SIGNAL else 'MAP'},"
          f"  ExtBB({EXT_BB_PERIOD},{EXT_BB_DEVIATION}) on price")
    print(f"  Signals: both the {TICKS_PER_CANDLE}-tick and the {TICKS_PER_CANDLE_2}-tick series are judged on every tick of the forming candle (no close needed) and again when it closes;")
    print("  later you are told if a signal was REPAINTED AWAY or CONFIRMED.")
    print(f"  Times shown : UTC{TIME_OFFSET_HOURS:+d}h   Logs: ./{LOG_DIR}/")
    print(f"  Diagnostics : ./{LOG_DIR}/<symbol>_signal_diagnostic.csv  (candles where a signal fired, EXITED or was IGNORED, plus rejected setups; <symbol>_5t_... is the 5-tick series; both downloadable from the dashboard)")
    print("  15-tick BUY  : MAP & SIGNAL both below IntBB lower, MAP curves up (>=5% band width), both back in, MAP rising  (no ExtBB)")
    print("  15-tick SELL : MAP & SIGNAL both above IntBB upper, MAP curves down (>=5% band width), both back in, MAP falling  (no ExtBB)")
    print("  5-tick  BUY/SELL : same, plus close > ExtBB upper (BUY) / close < ExtBB lower (SELL)")
    print("  EXIT : BUY  -> MAP/SIGNAL cross while both above the upper band")
    print("         SELL -> MAP/SIGNAL cross while both below the lower band")
    print("=" * 70 + "\n")
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        print("  ⚠ Telegram not configured — alerts are printed only\n")

    start_ws()
    start_trader()
    threading.Thread(target=run_dashboard, daemon=True).start()
    time.sleep(2)
    try:
        while running:
            time.sleep(30)
    except KeyboardInterrupt:
        running = False
        if os.environ.get("GITHUB_ACTIONS") == "true":
            _notify_status("RUN ENDED ⏹", "The 5h50m run is finished. A new run starts at the next scheduled time (about 10 minutes).\n"
                                           "Any open trade keeps its TP / SL on Deriv.")
            time.sleep(4)   # give the Telegram message time to leave before the process exits
        try:
            ws_app.close()
        except Exception:
            pass
