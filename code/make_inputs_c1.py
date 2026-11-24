#!/usr/bin/env python3
"""Build the C1 inputs (exact integers) and the broken-input variants.
Usage: python3 make_inputs_c1.py FAVOUR.json OUTDIR
FAVOUR.json is scripts/areaC/results/out_1400_favour.json of the companion (float phases, K=1400, L=584).
x_k is rounded to the nearest multiple of 2^-40 (stored as the integer x_k * 2^40).
T_used is the lower end of T_1400 = C - 2 sum_{k<=1400} w_k (ball over the zero intervals), floored to a multiple of 2^-60."""
import sys, json
import flint
from flint import arb, ctx, fmpq
ctx.prec = 128
fav = json.load(open(sys.argv[1])); out = sys.argv[2]
K = 1400; assert fav["K"] == K and fav["L"] == 584 and len(fav["x"]) == K
xi = [int(round(v * 2**40)) for v in fav["x"]]
zj = json.load(open(__file__.rsplit("/", 1)[0] + "/z2000.json"))
eps = arb(2) ** -20; one = arb(1)
def q(m, e): return fmpq(m * 2**e, 1) if e >= 0 else fmpq(m, 2**(-e))
mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]][:K]
w = [one / (one / 4 + (g + eps * arb(-1).union(arb(1)))**2) for g in mids]
C = 2 + arb.const_euler() - (4 * arb.pi()).log()
T = C - 2 * sum(w, arb(0))
Tl = int((T.lower() * arb(2)**60).floor().unique_fmpz())
base = {"K": K, "L": 584, "c": "583/2", "x_den_exp": 40, "x_int": xi, "T_used_num": Tl, "T_used_den_exp": 60,
        "tail": "aligned", "source": "out_1400_favour.json rounded to 2^-40"}
def dump(name, d): json.dump(d, open(f"{out}/{name}", "w"))
dump("inputs_c1.json", base)
b = dict(base); b["L"] = 585; b["c"] = "292"; dump("broken_c1_L585.json", b)
b = dict(base); b["x_int"] = [xi[0] + round(1e-1 * 2**40)] + xi[1:]; dump("broken_c1_phase1.json", b)
b = dict(base); b["tail"] = "robust"; dump("broken_c1_tailsign.json", b)
b = dict(base); b["T_used_num"] = Tl + 2**50; dump("broken_c1_Traised.json", b)   # guard: T_used above certified lower end
z = json.load(open(__file__.rsplit("/", 1)[0] + "/z2000.json"))
m = z["gamma_mid_man_exp_rad_man_exp"][99]; m[0] += 2**(-m[1] - 5)   # move midpoint 100 by 2^-5 (exponent of the midpoint is negative) (outside its 2^-20 interval)
json.dump(z, open(f"{out}/broken_z2000_moved.json", "w"))
print("T_used", Tl / 2**60, "T upper", float(T.upper()), "files ok")
