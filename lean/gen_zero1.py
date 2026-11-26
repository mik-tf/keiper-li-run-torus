#!/usr/bin/env python3
"""T4 step 1 data (zero 1 ball, centres, arcs, chain) for the 21 distinct chain vectors of cert_c2_L594.json.
Run from lean/:  python3 -I gen_zero1.py [--utot]   (--utot sums the checker U over zeros 1..1999: about 2000 x 21 Horner rows)
Prints, per chain vector i: |z_i|, psi_i, eps_i, Utot_i, rho'_i, h_i (rational, cos h_i >= rho'_i by 1 - h^2/2 - 5h^4/96),
overlap check.  Output is data for N Lean module T4Zero1Data (not yet written).  Uses mpmath only to CHOOSE rationals;
Lean re-checks every inequality in Q."""
import json, sys
from fractions import Fraction as F
from math import isqrt
import mpmath as mp
mp.mp.dps = 80
CODE = "../code/"
z = json.load(open(CODE + "z2000.json")); V = json.load(open(CODE + "vectors_c2.json"))
C = json.load(open(CODE + "cert_c2_L594.json"))["result"]
CHAIN = C["cover"]["chain_vectors"]            # 22 entries, last = first shifted by 2 pi
VEC = {v["idx"]: v["a"] for v in V["vectors"]}
L = 594; VM = L - 1; H = 1025
def mid_N(i):
    man, e = z["gamma_mid_man_exp_rad_man_exp"][i][:2]
    return round(F(man) * F(2) ** e * 2 ** 30)
def horner(N, a):
    Zc = (N * N - 2 ** 58, N * 2 ** 30); D = N * N + 2 ** 58
    P = (a[VM], 0); Dp = 1
    for j in range(VM - 1, -1, -1):
        Dp *= D
        P = (P[0] * Zc[0] - P[1] * Zc[1] + a[j] * Dp, P[0] * Zc[1] + P[1] * Zc[0])
    return P, 2 ** 50 * D ** VM, D
def U_row(N, a):
    (X, Y), den, D = horner(N, a)
    s = isqrt(2 ** 80 * (X * X + Y * Y)) + 1
    rho = -(-s // den)
    Elo = (N - H) ** 2 + 2 ** 58
    num = 2 ** 61 * rho * Elo + 2 ** 81 * sum(a) * VM * H
    return -(-num // (Elo * Elo))
N0 = mid_N(0)
W = F(8847, 10 ** 7)                                   # W <= 8.847e-4 (certified upper 0.00088467899)
# zero 1: gamma in [(N0-H)/2^30, (N0+H)/2^30]; w0 >= 1/(1/4 + gmax^2); P = |zpt g||zpt m| >= 1/4+gmin^2 (as in T4Lip)
gmin = F(N0 - H, 2 ** 30); gmax = F(N0 + H, 2 ** 30)
wlo = 1 / (F(1, 4) + gmax * gmax)
Pz = F(1, 4) + gmin * gmin
mp_rows = []
uts = {}
if "--utot" in sys.argv:
    for idx in sorted(set(CHAIN)):
        a = VEC[idx]
        uts[idx] = sum(U_row(mid_N(i), a) for i in range(1, 2000))
    json.dump({str(k): v for k, v in uts.items()}, open("zero1_utot.json", "w"))
else:
    uts = {int(k): v for k, v in json.load(open("zero1_utot.json")).items()}

# ---------- rational data for Lean (T4Zero1Data.lean) ----------
SC = 2 ** 60
def sL(s): return s - s ** 3 / 6 - s ** 5 / 100
def sU(s): return s - s ** 3 / 6 + s ** 5 / 100
def cL(s): return 1 - s * s / 2 - F(5, 96) * s ** 4
def cU(s): return 1 - s * s / 2 + F(5, 96) * s ** 4
def wpart(z, z2):               # w = z2 * conj z
    return (z2[0] * z[0] + z2[1] * z[1], z2[1] * z[0] - z2[0] * z[1])
def upOK(w, s):  return w[0] > 0 and w[1] > 0 and 0 <= s <= 1 and w[1] * cU(s) < w[0] * sL(s)
def loOK(w, l):  return w[0] > 0 and w[1] > 0 and 0 <= l <= 1 and cL(l) > 0 and w[1] * cL(l) > w[0] * sU(l)
GR = 10 ** 4
def f2q(x): return F(int(mp.floor(x * GR * 10)), GR * 10)
Z = []; RHO = []; HH = []; EPS = []; NN = []
for pos, idx in enumerate(CHAIN):
    a = VEC[idx]
    (X, Y), den, D = horner(N0, a)
    c = mp.mpc(mp.mpf(X) / den, mp.mpf(Y) / den)
    cr = (int(mp.nint(c.real * SC)), int(mp.nint(c.imag * SC)))
    zq = (F(-cr[0], SC), F(cr[1], SC))
    S = F(sum(a), 2 ** 50)
    eps = S * VM * F(H, 2 ** 30) / Pz + F(3, 2 ** 60)
    Nn = F(uts[idx], 2 ** 40) + W * S
    need = Nn / (2 * wlo) + eps
    zabs = mp.sqrt(mp.mpf(zq[0].numerator) / zq[0].denominator) ** 2 if False else mp.sqrt((mp.mpf(zq[0].numerator) / zq[0].denominator) ** 2 + (mp.mpf(zq[1].numerator) / zq[1].denominator) ** 2)
    rho = F(int(mp.ceil(mp.mpf(need.numerator) / need.denominator / zabs * 10 ** 6)) + 1, 10 ** 6)
    assert rho < 1
    # largest h on a 1e-5 grid with 1 - h^2/2 - 5h^4/96 >= rho, h <= 1
    h0 = mp.acos(mp.mpf(rho.numerator) / rho.denominator)
    h = F(int(mp.floor(h0 * 10 ** 5)), 10 ** 5)
    while cL(h) < rho: h -= F(1, 10 ** 5)
    assert h <= 1 and h > 0
    Z.append(zq); RHO.append(rho); HH.append(h); EPS.append(eps); NN.append(Nn)
n = len(CHAIN)                                   # 22
# angles: psi0 = arg z0 in (lP, uP); steps d_i = arg(z_{i+1} conj z_i) in (lS_i, uS_i)
def grid_search(test, start, direction):
    x = start
    for _ in range(2000):
        if test(x): return x
        x += direction * F(1, GR)
    raise SystemExit("no angle found from %s dir %d" % (float(start), direction))
psi0 = float(mp.arg(mp.mpc(mp.mpf(Z[0][0].numerator) / Z[0][0].denominator, mp.mpf(Z[0][1].numerator) / Z[0][1].denominator)))
w0 = (Z[0][0], Z[0][1])
uP = grid_search(lambda s: upOK((Z[0][0], Z[0][1]), s), F(int(psi0 * GR), GR), 1)
lP = grid_search(lambda s: loOK((Z[0][0], Z[0][1]), s), F(int(psi0 * GR), GR), -1)
# z0 positive imag part: arg z0 test uses w = z0 itself (conj of 1)
US = []; LS = []
for i in range(n - 1):
    w = wpart(Z[i], Z[i + 1])
    d = float(mp.arg(mp.mpc(mp.mpf(w[0].numerator) / w[0].denominator, mp.mpf(w[1].numerator) / w[1].denominator)))
    US.append(grid_search(lambda s: upOK(w, s), F(int(d * GR), GR), 1))
    LS.append(grid_search(lambda s: loOK(w, s), F(int(d * GR), GR), -1))
PI_UB = F(3141593, 10 ** 6)
ok_chain = all(US[i] < HH[i] + HH[i + 1] for i in range(n - 1))
ok0 = uP < HH[0]
okend = lP + sum(LS) + HH[n - 1] >= 2 * PI_UB
print("overlap slack min", float(min(HH[i] + HH[i + 1] - US[i] for i in range(n - 1))), "a0", float(HH[0] - uP), "end", float(lP + sum(LS) + HH[n - 1] - 2 * PI_UB))
assert ok_chain and ok0 and okend and Z[0] == Z[n - 1]
def ql(x):
    x = F(x); return "(%d / %d : ℚ)" % (x.numerator, x.denominator)
def lst(name, xs, ty="ℚ"):
    return "def %s : List %s := [\n  %s]\n" % (name, ty, ",\n  ".join(xs))
with open("P3Lean/T4Zero1Data.lean", "w") as f:
    f.write("import Mathlib.Algebra.Order.Ring.Rat\nimport Mathlib.Data.Rat.Cast.Order\n\n/-!\nGenerated by gen_zero1.py (do not edit). Chain of %d positions (vectors of cert_c2_L594.json: %s).\n" % (n, CHAIN))
    f.write("z_i = -conj(c_i), c_i = Horner value at the midpoint N0 of zero 1 rounded to 2^-60 (Gaussian rational); eps_i, Nn_i, rho'_i, h_i (cos h_i >= rho'_i by 1 - h^2/2 - 5h^4/96), angle test values.\nThe Lean module T4Zero1Arc re-checks every inequality in Q (decide +kernel).\n-/\n\nnamespace P3Lean\nnamespace Z1\n\n")
    f.write("def N0 : ℕ := %d\n" % N0)
    f.write("def wlo : ℚ := %s\ndef Pz : ℚ := %s\n" % (ql(wlo), ql(Pz)))
    f.write(lst("zRe", [ql(z[0]) for z in Z])); f.write(lst("zIm", [ql(z[1]) for z in Z]))
    f.write(lst("epsL", [ql(e) for e in EPS])); f.write(lst("nnL", [ql(e) for e in NN]))
    f.write(lst("rhoL", [ql(e) for e in RHO])); f.write(lst("hL", [ql(e) for e in HH]))
    f.write(lst("uSL", [ql(e) for e in US])); f.write(lst("lSL", [ql(e) for e in LS]))
    f.write("def chainIdx : List ℕ := %s\ndef utotL : List ℕ := %s\n" % (str(CHAIN), str([uts[i] for i in CHAIN])))
    f.write("def uP : ℚ := %s\ndef lP : ℚ := %s\n\nend Z1\nend P3Lean\n" % (ql(uP), ql(lP)))
print("wrote T4Zero1Data.lean")
