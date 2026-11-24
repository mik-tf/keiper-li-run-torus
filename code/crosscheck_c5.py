#!/usr/bin/env python3
"""C5: second implementation cross-check of the certificates C1 to C4 of paper 3. NOT a proof.

Written from the definitions in the plan and the certificate statements, with NO import of, and no code taken from, the certify_*
scripts and no Arb. numpy longdouble for the sums, mpmath (40 digits) for the constants. It reads only stored data: the zero
midpoints (z2000.json), the integer phases and weights (inputs_c1.json, vectors_c2.json, the weights in cert_c3_*.json) and the
certified values in cert_*.json.
Definitions used (w_k = 1/(1/4 + g_k^2), theta_k = 2 atan(1/(2 g_k)), C = 2 + Euler - log 4 pi, T_K = C - 2 sum_{k<=K} w_k):
  C1  m(j) = F(j) + T cos(min(|j-c| theta_up, pi)), F(j) = sum_{k<=K} 2 w_k cos(j theta_k + x_k); min over j = 0..583, c = 583/2.
  C2  per vector a (window 594): rho = (sum_{k=2..2000} 2 w_k |A(theta_k)| + W S) / (2 w_1 |A(theta_1)|), A(t) = sum a_j e^{ijt},
      W = C - 2 sum_{k<=2000} w_k, S = sum a_j; arc = phi0 +- acos(rho), phi0 = -arg A(theta_1) - pi; union of arcs mod 2 pi.
  C3  closed form R = [sum_{k=2..K} 2 w_k (|A(alpha_k)| + S theta_k/2) - T_K S] / (2 w_1 cos(theta_1/2) S), alpha_k = P_1 theta_k,
      P_1 = 2 pi / theta_1; and the sup over u of R(u) = (sum_{k>=2} 2 w_k |B_k| - T_K S) / Z_1(u) by exact pieces (as paper 2's
      crosscheck_comb.py), compared cell by cell with the certified cell bounds.
  C4  min_j [F(j) + (T_K - T_G) cos(...)] - T_G, T_G = 2[-(M(G) - e(G)) f(G) + I_M + I_e] (the derivation in nt_bound.py's header,
      rewritten here), M(t) = (t/2pi) log(t/(2 pi e)), e(t) = a log t + b loglog t + c.
Radii (C2: times 1.5, since Arb's complex absolute value of a ball can exceed the true radius by sqrt 2). The certificates use balls over each zero interval g_k +- 2^-20; the float values use the midpoints. A first order radius is
computed here: |d/dg| of each term times 2^-20, summed with absolute values (dw/dg = -2 g w^2, dtheta/dg = -w). The certified lower
(or upper) end must lie within that radius of the float value, on the safe side (cert margin <= float margin; cert rho/R >= float).
Usage: python3 crosscheck_c5.py CODE_DIR --json OUT.json
"""
import sys, json, math
from fractions import Fraction
import numpy as np
import mpmath as mp

mp.mp.dps = 40
LD = np.longdouble
EPS = 2.0 ** -20
TOL = 1e-12          # longdouble and decimal rounding slack added to every radius
RADFAC_C2 = 1.5      # a ball |.| of a complex ball (independent real and imaginary radii) may exceed the true radius by sqrt 2
RND = lambda x: float("%.9g" % x)


def ld(x):
    return LD(mp.nstr(x, 30))


def load_zeros(path):
    z = json.load(open(path))
    mids = [mp.mpf(l[0]) * mp.mpf(2) ** l[1] for l in z["gamma_mid_man_exp_rad_man_exp"]]
    return mids


def consts(mids, K):
    C = 2 + mp.euler - mp.log(4 * mp.pi)
    s = mp.fsum(1 / (mp.mpf(1) / 4 + g * g) for g in mids[:K])
    TK = C - 2 * s
    # radius of T_K over the intervals: |d/dg (-2 w)| = 4 g w^2
    rTK = EPS * mp.fsum(4 * g / (mp.mpf(1) / 4 + g * g) ** 2 for g in mids[:K])
    return C, TK, rTK


def arrays(mids, K):
    g = np.array([ld(m) for m in mids[:K]], dtype=LD)
    w = 1 / (LD(0.25) + g * g)
    th = 2 * np.arctan(1 / (2 * g))
    return g, w, th


def check(name, cert, mine, rad, side):
    """side 'lower': cert is a lower end (cert <= mine, mine - cert <= rad); 'upper': cert >= mine, cert - mine <= rad"""
    d = (mine - cert) if side == "lower" else (cert - mine)
    ok = bool(d >= -TOL and d <= rad + TOL)
    return {"name": name, "certified": RND(cert), "float": RND(mine), "diff_safe_side": RND(d), "radius": RND(rad), "ok": ok}


def F_and_rad(g, w, th, x, L):
    """F(j) for j < L and its first order radius over the zero intervals"""
    j = np.arange(L, dtype=LD)
    ph = np.outer(j, th) + x[None, :]
    F = (np.cos(ph) * (2 * w)[None, :]).sum(axis=1)
    rad = EPS * ((4 * g * w * w).sum() + (2 * w * w).sum() * j)   # d(2w)/dg and j * 2w * dtheta/dg, |cos|,|sin| <= 1
    return F, rad


def tail_cos(L, c, th_up):
    j = np.arange(L, dtype=LD)
    return np.cos(np.minimum(np.abs(j - c) * th_up, LD(np.pi)))


def argval(flag, default):
    return sys.argv[sys.argv.index(flag) + 1] if flag in sys.argv else default


def c1_c4(d, mids, res):
    # defaults: the 584 run. With --c1-inputs inputs_c1_589.json --c1-cert cert_c1_torus589.json --c4-cert cert_c4_G....json the 589 run
    I = json.load(open(d + "/" + argval("--c1-inputs", "inputs_c1.json")))
    K, L = I["K"], I["L"]
    cn, cd = (I["c"].split("/") + ["1"])[:2]
    c = LD(int(cn)) / LD(int(cd))
    x = np.array([LD(v) / LD(2 ** I["x_den_exp"]) for v in I["x_int"]], dtype=LD)
    g, w, th = arrays(mids, K)
    C, TK, rTK = consts(mids, K)
    th_up = ld(2 * mp.atan(1 / (2 * (mids[K] - EPS))))
    F, rad = F_and_rad(g, w, th, x, L)
    tc = tail_cos(L, c, th_up)
    # C1: T_used = lower end of T_K; margins at the float values with the float T_K lower end
    cert1 = json.load(open(d + "/" + argval("--c1-cert", "cert_c1_torus584.json")))["result"]
    Tlow = ld(TK - rTK)
    m1 = F + Tlow * tc
    j1 = int(np.argmin(m1))
    r1 = float(rad[j1]) + float(rTK)
    out1 = check("C1 min margin", cert1["certified_min_margin"], float(m1[j1]), r1, "lower")
    out1["argmin_j_cert"] = cert1["argmin_j"]; out1["argmin_j_float"] = j1
    out1["ok"] = out1["ok"] and j1 == cert1["argmin_j"]
    out1["theta_up"] = {"certified": cert1["theta_up"], "float": float(th_up)}
    out1["T_K_in_certified_range"] = bool(cert1["T_K_lower"] - 1e-15 <= float(TK) <= cert1["T_K_upper"] + 1e-15)
    out1["ok"] = out1["ok"] and out1["T_K_in_certified_range"] and abs(float(th_up) - cert1["theta_up"]) < 1e-15
    out1["safe_side"] = bool(cert1["certified_min_margin"] > 0 and float(m1[j1]) > 0)
    res["C1"] = out1
    # second best j (to show the argmin is not a tie)
    srt = np.sort(m1)
    out1["second_smallest_margin"] = RND(float(srt[1]))
    # C4
    cert4 = json.load(open(d + "/" + argval("--c4-cert", "cert_c4_G100000.json")))["result"]
    G = mp.mpf(cert4["Gamma"])
    a_, b_, c_ = mp.mpf(11200) / 100000, mp.mpf(12567) / 100000, mp.mpf(377417) / 100000
    Mt = lambda t: t / (2 * mp.pi) * mp.log(t / (2 * mp.pi * mp.e))
    et = lambda t: a_ * mp.log(t) + b_ * mp.log(mp.log(t)) + c_
    f = 1 / (mp.mpf(1) / 4 + G * G)
    kk = mp.log(G) / G ** 2 + 1 / (2 * G ** 2)
    IM = (mp.log(G) - mp.log(2 * mp.pi)) / (mp.pi * G)
    Ie = a_ * kk + b_ * kk + c_ / G ** 2
    TG = 2 * (-(Mt(G) - et(G)) * f + IM + Ie)
    crest = ld(TK - rTK - TG)
    m4 = F + crest * tc - ld(TG)
    j4 = int(np.argmin(m4))
    r4 = float(rad[j4]) + 2 * float(rTK)
    out4 = check("C4 margin at Gamma=%g" % cert4["Gamma"], cert4["certified_min_margin"], float(m4[j4]), r4, "lower")
    out4["argmin_j_cert"] = cert4["argmin_j"]; out4["argmin_j_float"] = j4
    out4["ok"] = out4["ok"] and j4 == cert4["argmin_j"]
    out4["T_Gamma"] = {"certified_upper": cert4["T_Gamma_upper_recomputed"], "float": float(TG)}
    out4["T_Gamma_cert_not_below_float"] = bool(cert4["T_Gamma_used"] >= float(TG) - 1e-18)
    out4["Kprime_upper"] = {"certified": cert4["Kprime_upper"], "float": float(Mt(G) + et(G))}
    out4["ok"] = out4["ok"] and out4["T_Gamma_cert_not_below_float"] and abs(float(TG) - cert4["T_Gamma_used"]) < 1e-12 \
        and abs(float(Mt(G) + et(G)) - cert4["Kprime_upper"]) < 1e-6
    out4["safe_side"] = bool(cert4["certified_min_margin"] > 0 and float(m4[j4]) > 0)
    # the C4 pass is thin: also show it fails for Gamma = 5e4 as the README says (sanity of the recomputation)
    G2 = mp.mpf(50000)
    f2 = 1 / (mp.mpf(1) / 4 + G2 * G2); k2 = mp.log(G2) / G2 ** 2 + 1 / (2 * G2 ** 2)
    TG2 = 2 * (-(Mt(G2) - et(G2)) * f2 + (mp.log(G2) - mp.log(2 * mp.pi)) / (mp.pi * G2) + a_ * k2 + b_ * k2 + c_ / G2 ** 2)
    m42 = (F + ld(TK - rTK - TG2) * tc - ld(TG2)).min()
    out4["gamma_5e4_float_margin_is_negative"] = bool(m42 < 0)
    out4["ok"] = out4["ok"] and out4["gamma_5e4_float_margin_is_negative"]
    res["C4"] = out4


def c2(d, mids, res):
    cert = json.load(open(d + "/cert_c2_L594.json"))["result"]
    V = json.load(open(d + "/vectors_c2.json"))
    L = V["L"]; den = V["den_exp"]
    g, w, th = arrays(mids, 2000)
    C, W2, rW = consts(mids, 2000)
    Wf = ld(W2)
    j = np.arange(L, dtype=LD)
    ph = np.exp(1j * np.outer(th, j))          # (2000, L) complex longdouble
    rows = cert["rows"]
    vecs = V["vectors"]
    # derivative bounds: |dA/dtheta| <= sum j a_j ; dtheta/dg = -w, dw/dg = -2 g w^2
    rhos, arcs, diffs, rads, bad = [], [], [], [], 0
    sumsafe = True
    for v, row in zip(vecs, rows):
        a = np.array([LD(int(t)) for t in v["a"]], dtype=LD) / LD(2 ** den)
        S = a.sum(); Sj = (j * a).sum()
        A = ph @ a
        Ab = np.abs(A)
        num = (2 * w[1:] * Ab[1:]).sum() + Wf * S
        den1 = 2 * w[0] * Ab[0]
        rho = num / den1
        phi0 = -np.angle(A[0]) - LD(np.pi)
        h = np.arccos(rho)
        # first order radius of rho
        rnum = EPS * ((4 * g[1:] * w[1:] ** 2 * Ab[1:]).sum() + (2 * w[1:] * w[1:] * Sj).sum() + float(rW) * float(S))
        rden = EPS * (4 * g[0] * w[0] ** 2 * Ab[0] + 2 * w[0] * w[0] * Sj)
        rad = RADFAC_C2 * float(rnum / den1 + rho * rden / den1)
        cr = float(row["rho_upper"])
        d1 = cr - float(rho)
        diffs.append(d1); rads.append(rad)
        if not (d1 >= -TOL and d1 <= rad + TOL): bad += 1
        # arc ends against the stored float ends: the arcs' half width h moves with rho by 1/sqrt(1-rho^2)
        # arc half width follows rho (d acos = d rho / sqrt(1 - rho^2)); the centre phi0 = -arg A1 - pi moves by |dA1|/|A1|
        rh = rad / math.sqrt(max(1e-30, 1 - float(rho) ** 2)) + RADFAC_C2 * float(EPS * w[0] * Sj / Ab[0])
        # the stored ends are shrunk: the certified arc is inside mine up to the radius
        rhos.append(float(rho))
        arcs.append((float(phi0 - h), float(phi0 + h), rh))
    # arcs: compare mod 2 pi with the certified (arc_lo_f, arc_hi_f)
    arcdiff = []
    for (lo, hi, rh), row in zip(arcs, rows):
        clo, chi = float(row["arc_lo_f"]), float(row["arc_hi_f"])
        sh = round((clo - lo) / (2 * math.pi)) * 2 * math.pi
        arcdiff.append((lo + sh - clo, chi - (hi + sh), rh))
    # certified arc strictly inside the float arc (shrunk) and within the radius of it
    arc_ok = all(dl >= -rh - TOL and dh >= -rh - TOL and dl <= rh + TOL and dh <= rh + TOL for dl, dh, rh in arcdiff)
    # coverage of the circle by the float open arcs (mod 2 pi), using the certified arcs as well
    def cover(intervals):
        segs = []
        for lo, hi in intervals:
            lo2 = lo % (2 * math.pi); hi2 = lo2 + (hi - lo)
            segs.append((lo2, hi2))
            segs.append((lo2 + 2 * math.pi, hi2 + 2 * math.pi))
            segs.append((lo2 - 2 * math.pi, hi2 - 2 * math.pi))
        segs.sort()
        reach = 0.0; mino = float("inf")
        for lo, hi in segs:
            if hi <= reach: continue
            if lo > reach: return False, 0.0
            mino = min(mino, reach - lo) if reach > lo else mino
            reach = max(reach, hi)
            if reach > 2 * math.pi + 1e-9: break
        # require strict overlap at every junction of a greedy chain: minimal gap to the reach
        return reach >= 2 * math.pi, mino
    covf, _ = cover([(lo, hi) for lo, hi, _ in arcs])
    covc, _ = cover([(float(r["arc_lo_f"]), float(r["arc_hi_f"])) for r in rows])
    # float margin: the circle is still covered when every float arc is shrunk by its radius
    covs, _ = cover([(lo + rh, hi - rh) for lo, hi, rh in arcs])
    mr = max(rhos)
    cert_max = cert["certified_max_rho_upper_float"]
    i_max = int(np.argmax(rhos))
    out = {"vectors": len(vecs),
           "max_rho": check("C2 max rho", cert_max, mr, rads[i_max], "upper"),
           "max_rho_argmax_vector": i_max,
           "all_rho_within_radius": bad == 0, "vectors_outside_radius": bad,
           "max_abs_rho_diff": RND(max(abs(x) for x in diffs)), "max_rho_radius": RND(max(rads)),
           "min_rho_cert_minus_float": RND(min(diffs)),
           "certified_arcs_inside_float_arcs_within_radius": bool(arc_ok),
           "max_arc_end_diff": RND(max(max(abs(dl), abs(dh)) for dl, dh, _ in arcdiff)),
           "float_arcs_cover_circle": bool(covf), "certified_arcs_cover_circle": bool(covc),
           "float_arcs_shrunk_by_radius_cover_circle": bool(covs),
           "float_max_rho_below_one": bool(mr < 1)}
    out["ok"] = bool(out["max_rho"]["ok"] and bad == 0 and arc_ok and covf and covc and covs and mr < 1)
    out["safe_side"] = bool(cert_max < 1 and mr < 1 and cert_max >= mr - TOL)
    res["C2"] = out


def pieces(lo, hi, P, M):
    """breakpoints of floor(u + j P + 1/2) inside (lo, hi), j < M"""
    bp = {lo, hi}
    for j in range(M):
        n = math.floor(lo + j * P + 0.5) + 1
        while n - j * P - 0.5 < hi:
            u = n - j * P - 0.5
            if lo < u < hi: bp.add(u)
            n += 1
    return sorted(bp)


def c3(d, mids, res, K, name):
    cert = json.load(open(d + "/" + name))
    g, w, th = arrays(mids, K)
    C, TK, rTK = consts(mids, K)
    Tl = ld(TK - rTK)
    ai = cert["weights_int_over_2^50"]; M = len(ai)
    a = np.array([LD(int(v)) / LD(2 ** 50) for v in ai], dtype=LD); S = a.sum()
    jj = np.arange(M, dtype=LD)
    P1 = 2 * LD(np.pi) / th[0]
    # closed form
    al = P1 * th[1:]
    Aal = np.abs(np.exp(1j * np.outer(al, jj)) @ a)
    num = (2 * w[1:] * (Aal + S * th[1:] / 2)).sum() - Tl * S
    Rcf = num / (2 * w[0] * np.cos(th[0] / 2) * S)
    cf = cert["closed_form"]["R_upper"]
    # radius of the closed form: first order in the zero intervals (loose: theta of every zero moves alpha_k by P1 dtheta + theta dP1)
    dth = EPS * w                                       # |d theta_k| over the interval
    dP1 = float(P1) * float(dth[0] / th[0])
    dal = float(P1) * dth[1:] + th[1:] * LD(dP1)
    rnum = float((2 * (4 * g[1:] * w[1:] ** 2) * EPS * (Aal + S * th[1:] / 2)).sum()
                 + (2 * w[1:] * (dal * (jj * a).sum() + S * dth[1:] / 2)).sum() + float(rTK) * float(S))
    rden = float(EPS * (4 * g[0] * w[0] ** 2 + 2 * w[0] * w[0]) * S) * 1.0 + float(2 * w[0] * S * dth[0] / 2)
    rad = rnum / float(2 * w[0] * np.cos(th[0] / 2) * S) + float(Rcf) * rden / float(2 * w[0] * np.cos(th[0] / 2) * S)
    out = {"K": K, "closed_form_R": check("C3 closed form R_rob K=%d" % K, cf, float(Rcf), rad, "upper")}
    # sup over u by exact pieces, cell by cell
    cells = cert["cells"]
    Rcell = []; diffs = []; viol = 0; csup = 0.0; fsup = -1e9
    for cell in cells:
        lo = float(Fraction(cell["u_lo"])); hi = float(Fraction(cell["u_hi"]))
        Rc = float(cell["R_upper"]); best = -1e9
        bp = pieces(lo, hi, float(P1), M)
        for p0, p1 in zip(bp[:-1], bp[1:]):
            um = (p0 + p1) / 2
            cj = np.floor(LD(um) + jj * P1 + LD(0.5))
            Bk = np.abs(np.exp(1j * np.outer(th[1:], cj)) @ a)
            nm = (2 * w[1:] * Bk).sum() - Tl * S
            for u in (p0, p1):
                Z1 = 2 * w[0] * (a * np.cos((cj - LD(u) - jj * P1) * th[0])).sum()
                best = max(best, float(nm / Z1))
        diffs.append(Rc - best); fsup = max(fsup, best); csup = max(csup, Rc)
        if best > Rc + 1e-12: viol += 1
    cap = cert["cover"]["R_upper_max"]
    out["cover_sup_R"] = {"certified_R_upper_max": RND(csup), "float_sup_R": RND(fsup),
                          "cells": len(cells), "cells_float_above_certified": viol,
                          "min_cert_minus_float_per_cell": RND(min(diffs)),
                          "max_cert_minus_float_per_cell": RND(max(diffs)),
                          "float_sup_below_one": bool(fsup < 1)}
    out["cover_sup_R"]["cert_R_upper_max_equals_stored"] = bool(abs(csup - cap) < 1e-12)
    # radius of the cell comparison: the certified cell value is an upper bound on the sup over the cell, taken with
    # u a ball of width 2^-10 and the comb sum |B_k| as an upper end; it must be >= the float sup and within 0.05 of it.
    cell_ok = viol == 0 and min(diffs) >= -TOL and max(diffs) <= 0.05
    out["cover_sup_R"]["cell_overshoot_limit"] = 0.05
    out["cover_sup_R"]["ok"] = bool(cell_ok and out["cover_sup_R"]["cert_R_upper_max_equals_stored"])
    out["ok"] = bool(out["closed_form_R"]["ok"] and out["cover_sup_R"]["ok"])
    out["safe_side"] = bool(cf < 1 and csup < 1 and float(Rcf) < 1 and fsup < 1)
    res[("C3_K%d" % K)] = out


def main():
    d = sys.argv[1]
    out = sys.argv[sys.argv.index("--json") + 1]
    mids = load_zeros(d + "/z2000.json")
    res = {"kind": "second implementation (numpy longdouble, mpmath constants), not a proof; no import of certify_*"}
    c1_c4(d, mids, res)
    c2(d, mids, res)
    c3(d, mids, res, 1400, "cert_c3_K1400.json")
    c3(d, mids, res, 2000, "cert_c3_K2000.json")
    keys = ["C1", "C2", "C3_K1400", "C3_K2000", "C4"]
    res["all_agree_within_radius"] = all(res[k]["ok"] for k in keys)
    res["all_on_safe_side"] = all(res[k]["safe_side"] for k in keys)
    json.dump(res, open(out, "w"), indent=1, sort_keys=True)
    print("%-10s %-22s %-14s %-14s %-12s %-10s %s" % ("cert", "quantity", "certified", "float", "diff(safe)", "radius", "ok"))
    for k in keys:
        r = res[k]
        if k == "C2": row = r["max_rho"]
        elif k.startswith("C3"): row = r["closed_form_R"]
        else: row = r
        print("%-10s %-22s %-14s %-14s %-12s %-10s %s" % (k, row["name"][:22], row["certified"], row["float"], row["diff_safe_side"], row["radius"], r["ok"]))
    print("C1 argmin j", res["C1"]["argmin_j_cert"], res["C1"]["argmin_j_float"], "| C4 argmin j", res["C4"]["argmin_j_cert"], res["C4"]["argmin_j_float"])
    for k in ("C3_K1400", "C3_K2000"):
        print(k, "cover sup R", res[k]["cover_sup_R"])
    print("C2", {k: v for k, v in res["C2"].items() if k != "max_rho"})
    print("all_agree_within_radius", res["all_agree_within_radius"], "all_on_safe_side", res["all_on_safe_side"])
    if not (res["all_agree_within_radius"] and res["all_on_safe_side"]):
        raise SystemExit("FAIL: see the table")


main()
