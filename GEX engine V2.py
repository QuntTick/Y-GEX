# --- START OF FILE GEX engine V3.py ---

import pandas as pd
import yfinance as yf
import time
from datetime import datetime
from zoneinfo import ZoneInfo
import socket
import math
import numpy as np
import threading
import warnings
from concurrent.futures import ThreadPoolExecutor, as_completed
from scipy.optimize import brentq
import tkinter as tk
from tkinter import ttk
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

# Suppress pandas SettingWithCopyWarning for clean terminal
warnings.filterwarnings('ignore', category=pd.errors.SettingWithCopyWarning)

# --- CONFIGURATION ---
TICKER = "^SPX"
SPY_TICKER = "SPY"
FUTURES_TICKER = "ES=F"
VIX_TICKER = "^VIX"
UDP_IP = "127.0.0.1"
UDP_PORT = 9000

# Constants
RISK_FREE_RATE = 0.053 # r = 5.3%
NY_TZ = ZoneInfo("America/New_York")
TRADING_MINS_PER_YEAR = 98280.0  # 252 days * 390 trading minutes per day

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
history_state = {} 

# --- ROBUST DATA FETCHER ---
def get_latest_price(symbol):
    try:
        t = yf.Ticker(symbol)
        hist = t.history(period="1d", interval="1m")
        if not hist.empty: return float(hist['Close'].iloc[-1])
        info = t.fast_info
        if 'last_price' in info and info['last_price'] is not None: return float(info['last_price'])
        hist_d = t.history(period="5d", interval="1d")
        if not hist_d.empty: return float(hist_d['Close'].iloc[-1])
    except:
        pass
    return 0.0

# --- TRADING-TIME FRACTION CALCULATOR ---
def calc_trading_T(exp_date, now_ny):
    total_secs = (exp_date - now_ny).total_seconds()
    if total_secs <= 0: return 1e-5
    
    calendar_days = total_secs / 86400.0
    
    if calendar_days <= 1.0:
        target_close = exp_date.replace(hour=16, minute=0, second=0, microsecond=0)
        secs_to_close = (target_close - now_ny).total_seconds()
        if secs_to_close <= 0: return 1e-5
        
        trading_mins_left = min(secs_to_close / 60.0, 390.0)
        return max(1e-5, trading_mins_left / TRADING_MINS_PER_YEAR)
    
    approx_trading_days = calendar_days * (5.0 / 7.0)
    return max(1e-5, approx_trading_days / 252.0)

# --- UNIFIED GENERALIZED BSM FRAMEWORK ---
def norm_cdf_fast(x):
    return (1.0 + math.erf(x / 1.4142135623730951)) / 2.0 

def bs_price_scalar(S, K, T, v, r, b, is_call):
    if T <= 0 or v <= 0: return max(0.0, S - K) if is_call else max(0.0, K - S)
    d1 = (math.log(S / K) + (b + 0.5 * v**2) * T) / (v * math.sqrt(T))
    d2 = d1 - v * math.sqrt(T)
    if is_call:
        return S * math.exp((b - r) * T) * norm_cdf_fast(d1) - K * math.exp(-r * T) * norm_cdf_fast(d2)
    else:
        return K * math.exp(-r * T) * norm_cdf_fast(-d2) - S * math.exp((b - r) * T) * norm_cdf_fast(-d1)

def calculate_implied_iv_brent(S, K, T, r, b, market_price, is_call, fallback_iv=0.20):
    if market_price <= 0 or T <= 1e-5: return fallback_iv
    
    def objective_func(sigma):
        return bs_price_scalar(S, K, T, sigma, r, b, is_call) - market_price

    try:
        return brentq(objective_func, 1e-3, 5.0, xtol=1e-4, maxiter=50)
    except (ValueError, RuntimeError):
        return fallback_iv 

def fetch_chain_concurrently(ticker_obj, exp):
    try:
        return exp, ticker_obj.option_chain(exp)
    except Exception:
        return exp, None

def prune_history_state():
    global history_state
    today_str = datetime.now(NY_TZ).strftime('%Y-%m-%d')
    stale_keys = [k for k in history_state.keys() if k.split('_')[0] < today_str]
    for k in stale_keys:
        history_state.pop(k, None)

# --- SKEW / VOLATILITY SMILE SMOOTHING (FIXED: ROLLING MEDIAN) ---
def smooth_volatility_smile(strikes, ivs):
    # Median filter aggressively kills data spikes from YF without warping the curve
    if len(ivs) < 5:
        return ivs
    s = pd.Series(ivs)
    smoothed = s.rolling(window=5, center=True, min_periods=1).median()
    return np.clip(smoothed.values, 0.05, 3.0).tolist()

# --- DECOUPLED UDP TRANSMISSION SERVER ---
def transmit_udp_payload(spot, basis_ratio, vix, cost_of_carry, options_list):
    try:
        timestamp = datetime.now(NY_TZ).timestamp()
        header = f"{timestamp},{basis_ratio:.6f},{vix:.4f},{spot:.2f},{cost_of_carry:.6f}"
        
        opt_payloads = []
        for opt in options_list:
            opt_payloads.append(
                f"{opt['dte']:.6f},{opt['type']},{opt['strike']},{opt['oi']},"
                f"{opt['iv']:.4f},{opt['flow_dir']},{opt['b']:.6f},{opt['ticker']}"
            )
        
        payload = header + "|" + "|".join(opt_payloads)
        chunk_size = 50000 
        for i in range(0, len(payload), chunk_size):
            sock.sendto(payload[i:i+chunk_size].encode(), (UDP_IP, UDP_PORT))
            
    except Exception as e:
        print(f"UDP Transmission Failure: {e}")

# --- DATA AGGREGATION PIPELINE ---
def fetch_and_send_data(tier='fast'):
    global history_state
    try:
        prune_history_state()
        now_ny = datetime.now(NY_TZ)
        timestamp = now_ny.strftime('%H:%M:%S')
        print(f"[{timestamp}] Executing {tier.upper()} scan...")
        
        spot = get_latest_price(TICKER)
        spy_spot = get_latest_price(SPY_TICKER)
        fut = get_latest_price(FUTURES_TICKER)
        vix = get_latest_price(VIX_TICKER)
        if spot == 0 or spy_spot == 0: return None, None

        basis_ratio = fut / spot if (spot > 0 and fut > 0) else 1.0
        
        ticker_spx = yf.Ticker(TICKER)
        ticker_spy = yf.Ticker(SPY_TICKER)
        expirations = ticker_spx.options
        if not expirations: return None, None

        selected_exps = []
        for exp in expirations:
            exp_date = datetime.strptime(exp, '%Y-%m-%d').replace(hour=16, minute=0, second=0, tzinfo=NY_TZ)
            days = (exp_date - now_ny).total_seconds() / 86400.0
            if tier == 'fast' and days <= 1.5: selected_exps.append(exp)
            elif tier == 'medium' and 1 < days <= 14: selected_exps.append(exp)
            elif tier == 'slow' and days > 14: selected_exps.append(exp)
            elif tier == 'ui' and days <= 35: selected_exps.append(exp) 

        chains_spx = {}
        chains_spy = {}
        with ThreadPoolExecutor(max_workers=10) as executor:
            futures_spx = {executor.submit(fetch_chain_concurrently, ticker_spx, exp): exp for exp in selected_exps}
            futures_spy = {executor.submit(fetch_chain_concurrently, ticker_spy, exp): exp for exp in selected_exps}
            
            for future in as_completed(futures_spx):
                exp_key, chain = future.result()
                if chain: chains_spx[exp_key] = chain
            for future in as_completed(futures_spy):
                exp_key, chain = future.result()
                if chain: chains_spy[exp_key] = chain

        last_valid_coc_spx = RISK_FREE_RATE - 0.014 # Fallback
        parsed_for_ui = [] 

        # Process chains
        for exp in sorted(selected_exps):
            T = calc_trading_T(datetime.strptime(exp, '%Y-%m-%d').replace(hour=16, minute=0, second=0, tzinfo=NY_TZ), now_ny)
            
            # SPX Processing
            if exp in chains_spx:
                chain = chains_spx[exp]
                
                # FIXED: Hardcode structural carry (Risk Free Rate - Dividend Yield)
                # SPX dividend yield is ~1.4%
                dividend_yield = 0.014
                b_exp = RISK_FREE_RATE - dividend_yield 
                last_valid_coc_spx = b_exp

                for opt_type, df in [('1', chain.calls), ('0', chain.puts)]:
                    if 'openInterest' in df.columns:
                        df = df[df['openInterest'] > 0]
                    else: continue
                    df = df[(df['strike'] > spot * 0.85) & (df['strike'] < spot * 1.15)]
                    is_call = (opt_type == '1')
                    if df.empty: continue
                    
                    bids, asks, lasts = df['bid'].values, df['ask'].values, df['lastPrice'].values
                    prices = np.where((bids > 0) & (asks > 0), (bids + asks) / 2.0, lasts)
                    df['price'] = np.nan_to_num(prices)
                    
                    strikes = df['strike'].values
                    prices_arr = df['price'].values
                    vols = df.get('volume', pd.Series(0.0, index=df.index)).fillna(0.0).values
                    ois = df['openInterest'].values
                    yf_ivs = df.get('impliedVolatility', pd.Series(0.20, index=df.index)).fillna(0.20).values
                    yf_ivs = np.where(yf_ivs == 0, 0.20, yf_ivs)

                    # FIXED: Trust YF's exchange IV first. Only use Brent Solver as fallback.
                    final_ivs = []
                    for k, p, fb in zip(strikes, prices_arr, yf_ivs):
                        if 0.01 < fb < 3.0:
                            final_ivs.append(fb) # Trust exchange IV
                        else:
                            calc_iv = calculate_implied_iv_brent(spot, k, T, RISK_FREE_RATE, b_exp, p, is_call, fallback_iv=0.20)
                            final_ivs.append(calc_iv)

                    # Apply Median Filter
                    exact_ivs = smooth_volatility_smile(strikes, final_ivs)

                    # Dynamic flow calculation
                    flow_dirs = []
                    for strike, price, vol in zip(strikes, prices_arr, vols):
                        uid = f"{exp}_{opt_type}_{strike}"
                        flow_dir = 0
                        if uid in history_state:
                            prev_price, prev_vol = history_state[uid]
                            if vol > prev_vol:
                                if price > prev_price: flow_dir = 1
                                elif price < prev_price: flow_dir = -1
                        history_state[uid] = (price, vol)
                        flow_dirs.append(flow_dir)

                    for strike, price, vol, oi, exact_iv, flow_dir in zip(strikes, prices_arr, vols, ois, exact_ivs, flow_dirs):
                        parsed_for_ui.append({
                            'exp': exp, 'dte': T, 'type': opt_type, 
                            'strike': strike, 'oi': oi, 'iv': exact_iv, 'vol': vol,
                            'b': b_exp, 'ticker': 'SPX', 'flow_dir': flow_dir
                        })

            # SPY Processing
            if exp in chains_spy:
                chain = chains_spy[exp]
                
                # FIXED: Hardcode structural carry for SPY (~1.2% div yield)
                dividend_yield = 0.012
                b_exp = RISK_FREE_RATE - dividend_yield

                for opt_type, df in [('1', chain.calls), ('0', chain.puts)]:
                    if 'openInterest' in df.columns:
                        df = df[df['openInterest'] > 0]
                    else: continue
                    df = df[(df['strike'] > spy_spot * 0.85) & (df['strike'] < spy_spot * 1.15)]
                    is_call = (opt_type == '1')
                    if df.empty: continue
                    
                    bids, asks, lasts = df['bid'].values, df['ask'].values, df['lastPrice'].values
                    prices = np.where((bids > 0) & (asks > 0), (bids + asks) / 2.0, lasts)
                    df['price'] = np.nan_to_num(prices)
                    
                    strikes = df['strike'].values
                    prices_arr = df['price'].values
                    vols = df.get('volume', pd.Series(0.0, index=df.index)).fillna(0.0).values
                    ois = df['openInterest'].values
                    yf_ivs = df.get('impliedVolatility', pd.Series(0.20, index=df.index)).fillna(0.20).values
                    yf_ivs = np.where(yf_ivs == 0, 0.20, yf_ivs)

                    # FIXED: Trust YF's exchange IV first.
                    final_ivs = []
                    for k, p, fb in zip(strikes, prices_arr, yf_ivs):
                        if 0.01 < fb < 3.0:
                            final_ivs.append(fb) 
                        else:
                            calc_iv = calculate_implied_iv_brent(spy_spot, k, T, RISK_FREE_RATE, b_exp, p, is_call, fallback_iv=0.20)
                            final_ivs.append(calc_iv)

                    # Apply Median Filter
                    exact_ivs = smooth_volatility_smile(strikes, final_ivs)

                    flow_dirs = []
                    for strike, price, vol in zip(strikes, prices_arr, vols):
                        uid = f"{exp}_{opt_type}_{strike}"
                        flow_dir = 0
                        if uid in history_state:
                            prev_price, prev_vol = history_state[uid]
                            if vol > prev_vol:
                                if price > prev_price: flow_dir = 1
                                elif price < prev_price: flow_dir = -1
                        history_state[uid] = (price, vol)
                        flow_dirs.append(flow_dir)

                    for strike, price, vol, oi, exact_iv, flow_dir in zip(strikes, prices_arr, vols, ois, exact_ivs, flow_dirs):
                        parsed_for_ui.append({
                            'exp': exp, 'dte': T, 'type': opt_type, 
                            'strike': strike, 'oi': oi, 'iv': exact_iv, 'vol': vol,
                            'b': b_exp, 'ticker': 'SPY', 'flow_dir': flow_dir
                        })

        if not parsed_for_ui: return None, None

        # BROADCAST DATA OVER SOCKET IN DEDICATED FUNCTION
        header_coc = last_valid_coc_spx if last_valid_coc_spx is not None else 0.0
        transmit_udp_payload(spot, basis_ratio, vix, header_coc, parsed_for_ui)
        
        print(f"[{datetime.now().strftime('%H:%M:%S')}] UDP Broadcast Completed.")
        return {'time': timestamp, 'spot': spot}, parsed_for_ui

    except Exception as e:
        print(f"Error in fetcher: {e}")
        return None, None

# =========================================================================================
# ========================= HIGH-PERFORMANCE DEV UI BLOCK =================================
# =========================================================================================

def calc_gamma_vectorized(S, K_array, T_array, v_array, b_array, r=RISK_FREE_RATE):
    T_safe = np.clip(T_array, 1e-5, None)
    v_safe = np.clip(v_array, 1e-3, None)
    
    d1 = (np.log(S / K_array) + (b_array + 0.5 * v_safe**2) * T_safe) / (v_safe * np.sqrt(T_safe))
    norm_pdf = np.exp(-d1**2 / 2.0) / np.sqrt(2.0 * np.pi)
    
    gamma = (np.exp((b_array - r) * T_safe) * norm_pdf) / (S * v_safe * np.sqrt(T_safe))
    return np.nan_to_num(gamma, nan=0.0)

class DebugGEXUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Institutional Live GEX Viewer")
        self.root.geometry("1300x850")
        self.root.configure(bg='#1c1c1c')
        plt.style.use('dark_background')

        self.history = {} 
        self.timestamps = []
        self.current_idx = 0
        
        self.include_0dte = True
        self.show_walls = False
        self.show_abs_gex = False
        self.show_profiles = False
        self.show_combo = True 

        self.custom_xlim = None
        self.custom_ylim = None
        self.is_dragging = False
        self.last_mouse_x = None
        self.last_mouse_y = None

        self.setup_ui()
        self.root.after(1000, self.fetch_loop)

    def setup_ui(self):
        self.fig, self.ax = plt.subplots(figsize=(12, 7))
        self.fig.subplots_adjust(left=0.08, right=0.95, top=0.92, bottom=0.08)
        self.fig.patch.set_facecolor('#1c1c1c')
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.root)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.canvas.mpl_connect('scroll_event', self.on_scroll)
        self.canvas.mpl_connect('button_press_event', self.on_press)
        self.canvas.mpl_connect('button_release_event', self.on_release)
        self.canvas.mpl_connect('motion_notify_event', self.on_motion)

        btm_frame = tk.Frame(self.root, bg='#2d2d2d')
        btm_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=5) 

        self.slider_var = tk.IntVar()
        self.slider = ttk.Scale(btm_frame, from_=0, to=0, variable=self.slider_var, command=self.on_slider)
        self.slider.pack(fill=tk.X, padx=20, pady=5)

        ctrl_box = tk.Frame(btm_frame, bg='#2d2d2d')
        ctrl_box.pack(pady=5)

        tk.Button(ctrl_box, text="⏮", command=self.prev_frame, bg="#444", fg="white").pack(side=tk.LEFT, padx=5)
        self.lbl_time = tk.Label(ctrl_box, text="Waiting for data...", bg='#2d2d2d', fg="cyan", font=("Consolas", 12))
        self.lbl_time.pack(side=tk.LEFT, padx=15)
        tk.Button(ctrl_box, text="⏭", command=self.next_frame, bg="#444", fg="white").pack(side=tk.LEFT, padx=5)

        self.btn_filter = tk.Button(ctrl_box, text="✅ 0DTE Included", command=self.toggle_0dte, bg="#006600", fg="white")
        self.btn_filter.pack(side=tk.LEFT, padx=10)

        self.btn_combo = tk.Button(ctrl_box, text="🍔 Combo GEX (SPX+SPY): ON", command=self.toggle_combo, bg="#006600", fg="white")
        self.btn_combo.pack(side=tk.LEFT, padx=10)

        self.btn_walls = tk.Button(ctrl_box, text="🧱 Walls: OFF", command=self.toggle_walls, bg="#444", fg="white")
        self.btn_walls.pack(side=tk.LEFT, padx=5)

        self.btn_abs = tk.Button(ctrl_box, text="📈 Abs GEX: OFF", command=self.toggle_abs_gex, bg="#444", fg="white")
        self.btn_abs.pack(side=tk.LEFT, padx=5)

        self.btn_profiles = tk.Button(ctrl_box, text="🏔️ Profiles: OFF", command=self.toggle_profiles, bg="#444", fg="white")
        self.btn_profiles.pack(side=tk.LEFT, padx=5)

        self.btn_reset = tk.Button(ctrl_box, text="🔄 Reset View", command=self.reset_view, bg="#0055aa", fg="white")
        self.btn_reset.pack(side=tk.LEFT, padx=20)

        stats_frame = tk.Frame(btm_frame, bg='#1a1a1a', bd=1, relief="ridge")
        stats_frame.pack(fill=tk.X, padx=20, pady=5)
        self.lbl_stats = tk.Label(stats_frame, text="📊 Statistics Calculating...", bg='#1a1a1a', fg="gold", font=("Arial", 11, "bold"))
        self.lbl_stats.pack(pady=2)

    def on_scroll(self, event):
        if event.inaxes == self.ax:
            scale_factor = 0.9 if event.button == 'up' else 1.1 
            xdata, ydata = event.xdata, event.ydata
            if xdata is None or ydata is None: return
            xlim, ylim = self.ax.get_xlim(), self.ax.get_ylim()
            new_width = (xlim[1] - xlim[0]) * scale_factor
            new_height = (ylim[1] - ylim[0]) * scale_factor
            relx = (xlim[1] - xdata) / (xlim[1] - xlim[0])
            rely = (ylim[1] - ydata) / (ylim[1] - ylim[0])
            self.custom_xlim = [xdata - new_width * (1 - relx), xdata + new_width * relx]
            self.custom_ylim = [ydata - new_height * (1 - rely), ydata + new_height * rely]
            self.ax.set_xlim(self.custom_xlim)
            self.ax.set_ylim(self.custom_ylim)
            self.canvas.draw_idle()

    def on_press(self, event):
        if event.button == 1 and event.inaxes == self.ax:
            self.is_dragging = True
            self.last_mouse_x, self.last_mouse_y = event.x, event.y

    def on_motion(self, event):
        if self.is_dragging and event.inaxes == self.ax:
            inv = self.ax.transData.inverted()
            p1 = inv.transform((self.last_mouse_x, self.last_mouse_y))
            p2 = inv.transform((event.x, event.y))
            dx_data, dy_data = p2[0] - p1[0], p2[1] - p1[1]
            xlim, ylim = self.ax.get_xlim(), self.ax.get_ylim()
            self.custom_xlim = [xlim[0] - dx_data, xlim[1] - dx_data]
            self.custom_ylim = [ylim[0] - dy_data, ylim[1] - dy_data]
            self.ax.set_xlim(self.custom_xlim)
            self.ax.set_ylim(self.custom_ylim)
            self.last_mouse_x, self.last_mouse_y = event.x, event.y
            self.canvas.draw_idle()

    def on_release(self, event):
        self.is_dragging = False

    def reset_view(self):
        self.custom_xlim, self.custom_ylim = None, None
        self.render_plot()

    def toggle_0dte(self):
        self.include_0dte = not self.include_0dte
        self.btn_filter.config(text="✅ 0DTE Included" if self.include_0dte else "❌ 0DTE Excluded", bg="#006600" if self.include_0dte else "#660000")
        if self.timestamps: self.render_plot()

    def toggle_combo(self):
        self.show_combo = not self.show_combo
        self.btn_combo.config(
            text="🍔 Combo GEX (SPX+SPY): ON" if self.show_combo else "🍔 Combo GEX (SPX+SPY): OFF",
            bg="#006600" if self.show_combo else "#660000"
        )
        if self.timestamps: self.render_plot()

    def toggle_walls(self):
        self.show_walls = not self.show_walls
        self.btn_walls.config(text="🧱 Walls: ON" if self.show_walls else "🧱 Walls: OFF", bg="#006600" if self.show_walls else "#444")
        if self.timestamps: self.render_plot()

    def toggle_abs_gex(self):
        self.show_abs_gex = not self.show_abs_gex
        self.btn_abs.config(text="📈 Abs GEX: ON" if self.show_abs_gex else "📈 Abs GEX: OFF", bg="#006600" if self.show_abs_gex else "#444")
        if self.timestamps: self.render_plot()

    def toggle_profiles(self):
        self.show_profiles = not self.show_profiles
        self.btn_profiles.config(text="🏔️ Profiles: ON" if self.show_profiles else "🏔️ Profiles: OFF", bg="#006600" if self.show_profiles else "#444")
        if self.timestamps: self.render_plot()

    def fetch_loop(self):
        threading.Thread(target=self.run_engine_and_process, daemon=True).start()
        self.root.after(60000, self.fetch_loop)

    def run_engine_and_process(self):
        header, options = fetch_and_send_data('ui') 
        if not header or not options: return
        ts = header['time']
        self.history[ts] = {'spot': header['spot'], 'options': options}
        if ts not in self.timestamps: self.timestamps.append(ts)
        self.root.after(0, self.sync_ui_state)

    def sync_ui_state(self):
        self.slider.config(to=max(0, len(self.timestamps)-1))
        if self.current_idx >= len(self.timestamps) - 2:
            self.current_idx = len(self.timestamps) - 1
            self.slider_var.set(self.current_idx)
        self.render_plot()

    def on_slider(self, val):
        self.current_idx = int(float(val))
        self.render_plot()

    def prev_frame(self):
        if self.current_idx > 0:
            self.current_idx -= 1
            self.slider_var.set(self.current_idx)
            self.render_plot()

    def next_frame(self):
        if self.current_idx < len(self.timestamps) - 1:
            self.current_idx += 1
            self.slider_var.set(self.current_idx)
            self.render_plot()

    def render_plot(self):
        if not self.timestamps: return
        
        ts = self.timestamps[self.current_idx]
        data = self.history[ts]
        spot = data['spot']
        
        df = pd.DataFrame(data['options'])
        if df.empty: return
        
        if not self.show_combo:
            df = df[df['ticker'] == 'SPX']
            
        today_str = datetime.now(NY_TZ).strftime('%Y-%m-%d')
        df['is_0dte'] = df['exp'] == today_str
        
        if not self.include_0dte:
            df = df[~df['is_0dte']]
            if df.empty:
                self.ax.clear()
                self.canvas.draw()
                return

        is_spy = df['ticker'] == 'SPY'
        df['spot_val'] = np.where(is_spy, spot / 10.0, spot)
        df['strike_val'] = df['strike'].values
        
        df['gamma'] = calc_gamma_vectorized(
            df['spot_val'].values, 
            df['strike_val'].values, 
            df['dte'].values, 
            df['iv'].values, 
            df['b'].values
        )
        
        df['base_gex'] = df['gamma'] * df['oi'] * (df['spot_val'] ** 2)
        df['scaled_gex'] = np.where(is_spy, df['base_gex'] / 10.0, df['base_gex'])
        df['plot_strike'] = np.where(is_spy, df['strike_val'] * 10.0, df['strike_val'])

        df['actual_gex'] = np.where(df['type'] == '1', df['scaled_gex'], -df['scaled_gex'])
        df['abs_actual_gex'] = np.abs(df['actual_gex'])

        # Aggregate Statistics
        vol_0dte = df[df['is_0dte']]['vol'].sum()
        vol_other = df[~df['is_0dte']]['vol'].sum()
        abs_gex_0dte = df[df['is_0dte']]['abs_actual_gex'].sum()
        abs_gex_other = df[~df['is_0dte']]['abs_actual_gex'].sum()

        total_vol = vol_0dte + vol_other
        pct_0dte = (vol_0dte / total_vol * 100) if total_vol > 0 else 0
        
        stats_msg = (
            f"📊 Range Exposure (per 1% move):   "
            f"0DTE Vol: {pct_0dte:.1f}%   |   "
            f"0DTE Size: ${abs_gex_0dte / 1e9:.2f}B   |   "
            f">0DTE Size: ${abs_gex_other / 1e9:.2f}B"
        )
        self.lbl_stats.config(text=stats_msg)

        # STABLE NON-LAMBDA GROUPBY AGGREGATIONS
        net_gex = df.groupby('plot_strike')['actual_gex'].sum()
        abs_gex = df.groupby('plot_strike')['abs_actual_gex'].sum()
        call_gex = df[df['type'] == '1'].groupby('plot_strike')['abs_actual_gex'].sum()
        put_gex = df[df['type'] == '0'].groupby('plot_strike')['abs_actual_gex'].sum()

        agg_df = pd.DataFrame({
            'net_gex': net_gex, 
            'abs_gex': abs_gex,
            'call_gex': call_gex, 
            'put_gex': put_gex
        }).fillna(0).reset_index()

        self.ax.clear()

        strikes = agg_df['plot_strike'].values
        net_gex_vals = agg_df['net_gex'].values / 1e9
        abs_gex_vals = agg_df['abs_gex'].values / 1e9

        colors = ['#ff4c4c' if val < 0 else '#4cff4c' for val in net_gex_vals]
        self.ax.barh(strikes, net_gex_vals, color=colors, height=4.0, alpha=0.8, label="Net GEX")
        
        if self.show_profiles:
            call_vals = agg_df['call_gex'].values / 1e9
            put_vals = agg_df['put_gex'].values / 1e9
            
            self.ax.plot(call_vals, strikes, color='#00ff00', linewidth=1.5, alpha=0.7)
            self.ax.fill_betweenx(strikes, 0, call_vals, color='#00ff00', alpha=0.2, label='Call Profile (Abs)')
            
            self.ax.plot(put_vals, strikes, color='#ff0000', linewidth=1.5, alpha=0.7)
            self.ax.fill_betweenx(strikes, 0, put_vals, color='#ff0000', alpha=0.2, label='Put Profile (Abs)')

        if self.show_abs_gex:
            self.ax.plot(abs_gex_vals, strikes, color='#ff00ff', linewidth=2.0, linestyle='-', label='Absolute Net Gamma')

        self.ax.axhline(y=spot, color='gray', linestyle='-', linewidth=0.8, label=f'Spot: {spot:.2f}')

        if self.show_walls and not agg_df.empty:
            call_wall_strike = agg_df.loc[agg_df['net_gex'].idxmax(), 'plot_strike']
            put_wall_strike = agg_df.loc[agg_df['net_gex'].idxmin(), 'plot_strike']
            
            if agg_df['net_gex'].max() > 0:
                self.ax.axhline(y=call_wall_strike, color='#00ff00', linestyle=':', linewidth=2, label=f'Call Wall: {call_wall_strike}')
            if agg_df['net_gex'].min() < 0:
                self.ax.axhline(y=put_wall_strike, color='#ff0000', linestyle=':', linewidth=2, label=f'Put Wall: {put_wall_strike}')

        title_text = f"S&P 500 Gamma Exposure - Time: {ts}"
        if not self.include_0dte: title_text += " [0DTE EXCLUDED]"
        if self.show_combo: title_text += " [SPX + SPY CONSOLIDATED]"
        
        self.ax.set_title(title_text, color='white', fontweight='bold')
        self.ax.set_xlabel("Dealer Exposure per 1% Move ($ Billions)", color='white')
        self.ax.set_ylabel("S&P 500 Strike Scale", color='white')
        self.ax.tick_params(colors='white')
        self.ax.grid(True, color='#444', alpha=0.3)
        self.ax.legend(loc="upper right", facecolor='#333', labelcolor='white')
        
        if self.custom_xlim and self.custom_ylim:
            self.ax.set_xlim(self.custom_xlim)
            self.ax.set_ylim(self.custom_ylim)

        self.lbl_time.config(text=f"Time: {ts}")
        self.canvas.draw()

def launch_system():
    root = tk.Tk()
    app = DebugGEXUI(root)
    print("--- Institutional UDP GEX Engine V3 + UI Started ---")
    root.mainloop()

if __name__ == "__main__":
    launch_system()
