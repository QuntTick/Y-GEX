#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Windows.Media;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using NinjaTrader.Cbi;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript;
using NinjaTrader.NinjaScript.DrawingTools;
using SharpDX.Direct2D1;
#endregion

public enum GexDisplayMode { NetGex, CallGexOnly, PutGexOnly }

namespace NinjaTrader.NinjaScript.Indicators
{
    public class GexHeatmapTCP_Precision : Indicator
    {
        #region Classes & Variables
        public class OptionData
        {
            public double DTE; 
            public bool IsCall;
            public double Strike; 
            public int OI;
            public double IV;
            public int FlowDir;
            public string Ticker;
        }

        public class GexSnapshot
        {
            public double Timestamp;
            public double BasisRatio;  
            public double RiskFreeRate; 
            public double DividendYield; 
            public double SnapshotSpot; 
            public List<OptionData> Options = new List<OptionData>();
        }

        public class GexRenderSnapshot
        {
            public int StartBar;
            public int EndBar; 
            public double BasisRatio;
            public double MaxGex;
            public Dictionary<double, double> Profile;
        }

        private TcpListener tcpListener;
        private Task tcpTask;
        private bool isListening = false;
        
        private readonly object dataLock = new object();
        private GexSnapshot latestSnapshot = null;

        private readonly object historyLock = new object();
        private List<GexRenderSnapshot> gexHistory = new List<GexRenderSnapshot>();

        private double lastCalcPrice = 0;
        private DateTime lastCalcTime = DateTime.MinValue;
        
        // --- NEW: Anchored Basis to prevent visual wiggling ---
        private double anchoredBasis = 0;

        private SharpDX.Direct2D1.SolidColorBrush[] positiveBrushes; 
        private SharpDX.Direct2D1.SolidColorBrush[] negativeBrushes;
        #endregion

        #region Parameters
        [NinjaScriptProperty]
        [Display(Name="Display Mode", Order=1, GroupName="1. Visuals")]
        public GexDisplayMode DisplayMode { get; set; }

        [NinjaScriptProperty]
        [Range(0, 100)]
        [Display(Name="Filter Cutoff %", Order=2, GroupName="1. Visuals")]
        public double CutoffPercent { get; set; }

        [NinjaScriptProperty]
        [Display(Name="Skew Sensitivity", Order=3, GroupName="1. Visuals")]
        public double SkewSensitivity { get; set; }

        [NinjaScriptProperty]
        [Range(100, 5000)]
        [Display(Name="History Limit (Bars)", Order=4, GroupName="1. Visuals")]
        public int HistoryLimit { get; set; }

        [NinjaScriptProperty]
        [Display(Name="TCP Port", Order=1, GroupName="2. System")]
        public int TcpPort { get; set; } 
        #endregion

        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description = "TCP GEX Engine V3 (Anchored Heatmap).";
                Name = "GEX Engine V3 (TCP Heatmap)";
                Calculate = Calculate.OnEachTick;
                IsOverlay = true;
                DrawOnPricePanel = true;
                CutoffPercent = 2.0;
                SkewSensitivity = 1.5; 
                HistoryLimit = 1000;
                TcpPort = 9000;
                DisplayMode = GexDisplayMode.NetGex;
            }
            else if (State == State.Configure)
            {
                ZOrder = -1;
            }
            else if (State == State.DataLoaded)
            {
                anchoredBasis = 0; // Reset anchor on load
                positiveBrushes = new SharpDX.Direct2D1.SolidColorBrush[256];
                negativeBrushes = new SharpDX.Direct2D1.SolidColorBrush[256];

                isListening = true;
                tcpTask = Task.Run(() => StartTcpServer());
            }
            else if (State == State.Terminated)
            {
                isListening = false;
                if (tcpListener != null) tcpListener.Stop();
                DisposeBrushes();
            }
        }

        #region TCP Telemetry System
        private async Task StartTcpServer()
        {
            try 
            {
                tcpListener = new TcpListener(IPAddress.Any, TcpPort);
                tcpListener.Start();

                while (isListening)
                {
                    TcpClient client = await tcpListener.AcceptTcpClientAsync();
                    Task.Run(() => HandleClient(client));
                }
            }
            catch (Exception ex)
            {
                Print("TCP Server Error: " + ex.Message);
            }
        }

        private void HandleClient(TcpClient client)
        {
            try
            {
                using (NetworkStream stream = client.GetStream())
                using (StreamReader reader = new StreamReader(stream, Encoding.UTF8))
                {
                    string payload = reader.ReadToEnd();
                    ProcessPayload(payload);
                }
            }
            catch { }
            finally { client.Close(); }
        }

        private void ProcessPayload(string payload)
        {
            try
            {
                string[] parts = payload.Split('|');
                if (parts.Length < 2) return;

                string[] header = parts[0].Split(',');
                GexSnapshot newSnap = new GexSnapshot
                {
                    Timestamp = double.Parse(header[0]),
                    BasisRatio = double.Parse(header[1]),
                    RiskFreeRate = double.Parse(header[2]),
                    DividendYield = double.Parse(header[3]),
                    SnapshotSpot = double.Parse(header[4])
                };

                for (int i = 1; i < parts.Length; i++)
                {
                    string[] row = parts[i].Split(',');
                    if (row.Length < 7) continue;

                    newSnap.Options.Add(new OptionData
                    {
                        DTE = double.Parse(row[0]),
                        IsCall = row[1] == "1",
                        Strike = double.Parse(row[2]),
                        OI = (int)double.Parse(row[3]),
                        IV = double.Parse(row[4]),
                        FlowDir = (int)double.Parse(row[5]),
                        Ticker = row[6]
                    });
                }

                lock (dataLock) { latestSnapshot = newSnap; }
                
                if (ChartControl != null)
                    ChartControl.Dispatcher.InvokeAsync(() => ChartControl.InvalidateVisual());
            }
            catch { }
        }
        #endregion

        #region Precision Math Engine with Skew Shifting
        private static double NormPDF(double x) { return Math.Exp(-x * x / 2.0) / Math.Sqrt(2.0 * Math.PI); }

        private double GetShiftedIV(double baseIV, double currentSpot, double referenceSpot)
        {
            if (referenceSpot <= 0) return baseIV;
            double priceShiftPercent = (currentSpot - referenceSpot) / referenceSpot;
            double shiftedIV = baseIV * (1.0 - (priceShiftPercent * SkewSensitivity));
            return Math.Max(0.01, Math.Min(2.5, shiftedIV));
        }

        private double CalculateExactGamma(double S, double K, double T, double v, double r, double q) {
            if (T <= 0 || v <= 0 || S <= 0 || K <= 0) return 0.0;
            double d1 = (Math.Log(S / K) + (r - q + v * v / 2.0) * T) / (v * Math.Sqrt(T));
            return (Math.Exp(-q * T) * NormPDF(d1)) / (S * v * Math.Sqrt(T));
        }
        #endregion

        protected override void OnBarUpdate()
        {
            if (CurrentBars[0] < 0 || latestSnapshot == null) return;
            
            double liveEsPrice = Close[0];
            
            if (Math.Abs(liveEsPrice - lastCalcPrice) < 0.25 && (DateTime.Now - lastCalcTime).TotalMilliseconds < 250)
                return;
                
            lastCalcPrice = liveEsPrice;
            lastCalcTime = DateTime.Now;

            GexSnapshot snap;
            lock (dataLock) { snap = latestSnapshot; }

            // Lock the visual basis permanently to the very first snapshot received
            if (anchoredBasis == 0 && snap.BasisRatio > 0)
                anchoredBasis = snap.BasisRatio;

            // Use the live basis for accurate mathematical moneyness
            double mathBasis = snap.BasisRatio > 0 ? snap.BasisRatio : 1.0;
            double nativeSpxSpot = liveEsPrice / mathBasis;
            double r = snap.RiskFreeRate;
            double q = snap.DividendYield;
            
            Dictionary<double, double> tempNetGex = new Dictionary<double, double>();

            foreach (var opt in snap.Options)
            {
                if (DisplayMode == GexDisplayMode.CallGexOnly && !opt.IsCall) continue;
                if (DisplayMode == GexDisplayMode.PutGexOnly && opt.IsCall) continue;

                double equivalentStrike = opt.Ticker == "SPY" ? opt.Strike * 10.0 : opt.Strike;
                
                // USE ANCHORED BASIS: Ensures visually flat lines on the ES chart
                double chartStrike = equivalentStrike * (anchoredBasis > 0 ? anchoredBasis : 1.0);
                
                if (opt.DTE <= 0.0001) continue; 

                double adjustedIV = GetShiftedIV(opt.IV, nativeSpxSpot, snap.SnapshotSpot);
                double gamma = CalculateExactGamma(nativeSpxSpot, equivalentStrike, opt.DTE, adjustedIV, r, q);
                double gex = gamma * opt.OI * nativeSpxSpot * nativeSpxSpot;

                if (opt.Ticker == "SPY") gex /= 10.0;

                if (!tempNetGex.ContainsKey(chartStrike)) tempNetGex[chartStrike] = 0;
                if (opt.IsCall) tempNetGex[chartStrike] += gex;
                else tempNetGex[chartStrike] -= gex;
            }

            double currentMaxGex = tempNetGex.Values.Select(Math.Abs).DefaultIfEmpty(0.0001).Max();

            lock (historyLock)
            {
                if (gexHistory.Count > 0)
                {
                    var last = gexHistory[gexHistory.Count - 1];
                    
                    if (last.StartBar == CurrentBar)
                    {
                        last.Profile = tempNetGex;
                        last.MaxGex = currentMaxGex;
                    }
                    else
                    {
                        last.EndBar = CurrentBar;
                        
                        gexHistory.Add(new GexRenderSnapshot
                        {
                            StartBar = CurrentBar,
                            EndBar = -1,
                            BasisRatio = anchoredBasis, // Use anchored basis
                            Profile = tempNetGex,
                            MaxGex = currentMaxGex
                        });
                    }
                }
                else
                {
                    gexHistory.Add(new GexRenderSnapshot
                    {
                        StartBar = CurrentBar,
                        EndBar = -1,
                        BasisRatio = anchoredBasis, // Use anchored basis
                        Profile = tempNetGex,
                        MaxGex = currentMaxGex
                    });
                }

                if (gexHistory.Count > HistoryLimit)
                    gexHistory.RemoveAt(0); 
            }
        }

        #region Rendering Logic (Hardware-Accelerated)
        public override void OnRenderTargetChanged()
        {
            DisposeBrushes();
            if (RenderTarget != null)
            {
                for (int i = 0; i < 256; i++)
                {
                    System.Windows.Media.Color pc = System.Windows.Media.Color.FromRgb((byte)(10+(0-10)*(i/255.0)), (byte)(20+(200-20)*(i/255.0)), (byte)(40+(255-40)*(i/255.0)));
                    positiveBrushes[i] = new SharpDX.Direct2D1.SolidColorBrush(RenderTarget, new SharpDX.Color(pc.R, pc.G, pc.B)) { Opacity = 0.65f };
                    System.Windows.Media.Color nc = System.Windows.Media.Color.FromRgb((byte)(40+(255-40)*(i/255.0)), (byte)(10+(100-10)*(i/255.0)), (byte)(10+(0-10)*(i/255.0)));
                    negativeBrushes[i] = new SharpDX.Direct2D1.SolidColorBrush(RenderTarget, new SharpDX.Color(nc.R, nc.G, nc.B)) { Opacity = 0.65f };
                }
            }
        }

        private void DisposeBrushes()
        {
            if (positiveBrushes != null) for (int i = 0; i < 256; i++) { if (positiveBrushes[i] != null) positiveBrushes[i].Dispose();
            if (negativeBrushes[i] != null) negativeBrushes[i].Dispose(); }
        }

        protected override void OnRender(ChartControl cc, ChartScale cs)
        {
            if (Bars == null || positiveBrushes == null || positiveBrushes[0] == null) return;
            
            List<GexRenderSnapshot> renderHistory;
            lock(historyLock) { renderHistory = new List<GexRenderSnapshot>(gexHistory); }
            if (renderHistory.Count == 0) return;

            RenderTarget.AntialiasMode = SharpDX.Direct2D1.AntialiasMode.Aliased;
            double minP = cs.MinValue, maxP = cs.MaxValue;
            
            float barWidth = (float)cc.Properties.BarDistance;

            foreach (var snap in renderHistory)
            {
                int startIdx = snap.StartBar;
                int endIdx = snap.EndBar == -1 ? ChartBars.ToIndex + 1 : snap.EndBar;

                if (endIdx < ChartBars.FromIndex || startIdx > ChartBars.ToIndex + 1) continue;

                float x1 = cc.GetXByBarIndex(ChartBars, startIdx) - (barWidth / 2f);
                float x2 = cc.GetXByBarIndex(ChartBars, endIdx) - (barWidth / 2f);
                
                if (snap.EndBar == -1) 
                    x2 = cc.CanvasRight;

                float w = x2 - x1;
                if (w <= 0) continue; 

                float strikeHalfStep = (float)(2.5 * snap.BasisRatio);

                foreach (var kvp in snap.Profile)
                {
                    if (kvp.Key > maxP + 10 || kvp.Key < minP - 10) continue;
                    
                    double ratio = Math.Abs(kvp.Value) / snap.MaxGex;
                    if (ratio < (CutoffPercent / 100.0)) continue;
                    
                    float yt = cs.GetYByValue(kvp.Key + strikeHalfStep);
                    float yb = cs.GetYByValue(kvp.Key - strikeHalfStep);
                    
                    SharpDX.RectangleF rect = new SharpDX.RectangleF(x1, Math.Min(yt, yb), w, Math.Abs(yb - yt));
                    
                    int colorIndex = Math.Max(0, Math.Min(255, (int)(ratio * 255)));
                    RenderTarget.FillRectangle(rect, kvp.Value >= 0 ? positiveBrushes[colorIndex] : negativeBrushes[colorIndex]);
                }
            }
        }
        #endregion
    }
}
