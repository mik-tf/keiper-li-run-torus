#!/usr/bin/env python3
"""Builds inputs_c4 files: Gamma and T_Gamma_used = the upper end of the T_Gamma bound of nt_bound.py (scale s, default 1)
rounded UP to a multiple of 2^-70, as exact integers. s <> 1 (main term scaled) builds the broken input of C4.
Usage: python3 make_inputs_c4.py GAMMA SCALE_NUM SCALE_DEN OUT.json"""
import sys, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, ctx, fmpq
import nt_bound
ctx.prec = 128
G = int(sys.argv[1]); s = fmpq(int(sys.argv[2]), int(sys.argv[3]))
u = nt_bound.tgamma_upper(arb(G), s).upper()
n = int((u * 2**70).ceil().unique_fmpz())
json.dump({"Gamma": G, "scale": f"{sys.argv[2]}/{sys.argv[3]}", "Tgamma_used_num": n, "Tgamma_used_den_exp": 70,
           "note": "scale 1 = the cited bound; scale <> 1 is a broken input (guard must refuse)"}, open(sys.argv[4], "w"), indent=1)
print(G, s, float(u), n)
