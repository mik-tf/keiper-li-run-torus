#!/usr/bin/env python3
"""Inputs for C1 at a new window. Usage: make_inputs_c1_L.py PUSH.json Z2000.json OUT_inputs.json
PUSH.json: output of push.py (K=1400, L, x). c = (L-1)/2 as a string. Same rounding as make_inputs_c1.py (x to 2^-40, T_used floored to 2^-60)."""
import sys, json
import flint
from flint import arb, ctx, fmpq
ctx.prec = 128
d = json.load(open(sys.argv[1])); K = 1400; L = d["L"]; assert d["K"] == K and len(d["x"]) == K
xi = [int(round(v * 2**40)) for v in d["x"]]
zj = json.load(open(sys.argv[2]))
eps = arb(2) ** -20; one = arb(1)
def q(m, e): return fmpq(m * 2**e, 1) if e >= 0 else fmpq(m, 2**(-e))
mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]][:K]
w = [one / (one / 4 + (g + eps * arb(-1).union(arb(1)))**2) for g in mids]
T = 2 + arb.const_euler() - (4 * arb.pi()).log() - 2 * sum(w, arb(0))
Tl = int((T.lower() * arb(2)**60).floor().unique_fmpz())
c = f"{L-1}/2" if (L - 1) % 2 else str((L - 1) // 2)
json.dump({"K": K, "L": L, "c": c, "x_den_exp": 40, "x_int": xi, "T_used_num": Tl, "T_used_den_exp": 60,
           "tail": "aligned", "source": f"push.py out_{L}_A.json rounded to 2^-40"}, open(sys.argv[3], "w"))
print("L", L, "c", c)
