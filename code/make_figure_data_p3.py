"""Write the data files used by the figures of paper keiper-li-run-torus (data/*.dat).

Usage: python3 code/make_figure_data_p3.py [OUT_DIR]       (OUT_DIR defaults to data/ beside code/)
Standard library only. Reads only the archived files in this directory; no certified number is recomputed.

  fig1-c2-arcs.dat    phi R   the curves R(phi)=rho/cos(phi-phi0) of the 48 arcs of C2 (cert_c2_L594.json, rows),
                      phi in [0,2 pi] (arcs shifted by 2 pi m and clipped); one block per arc, blank line between blocks.
                      Each arc is the open interval of phi with R<1; the ends are the certified ends arc_lo_f, arc_hi_f.
  fig1-c2-rho.dat     idx phi0 rho_upper   (one row per arc, certified upper ends of rho)
  fig2-c1-margin.dat  j margin   F(j)+T cos(min(|j-c| theta_up, pi)) for j=0..588 in double precision from
                      inputs_c1_589.json phases (the 589 run) and z2000.json zero midpoints (a plot of a certified quantity, not a certificate)
  fig3-bracket.dat    name K value kind   the values of the bracket against K
"""
import json, math, os, sys
here = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "..", "data")
os.makedirs(out, exist_ok=True)
J = lambda f: json.load(open(os.path.join(here, f)))
def W(name, header, rows):
    with open(os.path.join(out, name), "w") as f:
        f.write("# " + header + "\n")
        for r in rows: f.write(" ".join(r) + "\n")
TP = 2 * math.pi

# ---- fig 1: C2 arcs
rows = J("cert_c2_L594.json")["result"]["rows"]
lines = []; rhos = []
for r in rows:
    lo, hi, rho = r["arc_lo_f"], r["arc_hi_f"], float(r["rho_upper"])
    p0 = (lo + hi) / 2
    rhos.append([str(r["idx"]), "%.9g" % (p0 % TP), "%.12g" % rho])
    for m in range(-1, 3):
        a, b = max(lo + m * TP, 0.0), min(hi + m * TP, TP)
        if a >= b: continue
        n = 40
        blk = []
        for i in range(n + 1):
            ph = a + (b - a) * i / n
            # the open arc ends are where the curve crosses 1 only for rho_upper; the certified arc is slightly inside
            blk.append(["%.9g" % ph, "%.9g" % (rho / math.cos(ph - m * TP - p0))])
        lines += blk + [["nan", "nan"]]
with open(os.path.join(out, "fig1-c2-arcs.dat"), "w") as f:
    f.write("# phi R  (R=rho/cos(phi-phi0) on each certified arc of C2, 48 arcs, phi in [0,2pi]; blocks separated by nan rows)\n")
    for r in lines: f.write(" ".join(r) + "\n")
W("fig1-c2-rho.dat", "idx phi0 rho_upper (C2, 48 vectors; phi0 = centre of the certified arc)", rhos)

# ---- fig 2: C1 margin
z = J("z2000.json"); I = J("inputs_c1_589.json"); K, L = I["K"], I["L"]
gam = [m * 2.0 ** e for m, e, _, _ in z["gamma_mid_man_exp_rad_man_exp"]]
w = [1.0 / (0.25 + g * g) for g in gam[:K]]
th = [2 * math.atan(1.0 / (2 * g)) for g in gam[:K]]
th_up = 2 * math.atan(1.0 / (2 * (gam[K] - 2.0 ** -20)))
x = [v / 2.0 ** I["x_den_exp"] for v in I["x_int"]]
T = I["T_used_num"] / 2.0 ** I["T_used_den_exp"]
n_, d_ = (I["c"].split("/") + ["1"])[:2]; c = int(n_) / int(d_)
rows = []
for j in range(L):
    F = sum(2 * w[k] * math.cos(j * th[k] + x[k]) for k in range(K))
    rows.append([str(j), "%.9g" % (F + T * math.cos(min(abs(j - c) * th_up, math.pi)))])
W("fig2-c1-margin.dat", "j margin  (F(j)+T cos(min(|j-c| theta_up,pi)), K=1400, double precision; certified minimum 5.472e-5 at j=246)", rows)

# ---- fig 3: bracket
c1, c2 = J("cert_c1_torus589.json")["result"], J("cert_c2_L594.json")["result"]
W("fig3-bracket.dat", "name K value kind (run lengths; kind: cert or num)", [
  ["lower_prev", "1400", "476", "cert"],
  ["lower_C1", str(c1["K"]), str(c1["L"]), "cert"],
  ["upper_C3", "1400", "533", "cert"],
  ["upper_C3", "2000", "533", "cert"],
  ["upper_C2", str(c2["zeros_used"]), str(c2["L"] - 1), "cert"],
  ["search_robust", "1400", "477", "num"],
  ["search_robust", "2000", "489", "num"]])
