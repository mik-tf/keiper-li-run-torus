#!/usr/bin/env python3
"""C6: independent exact re-implementation of certificate C2 (window L = 594).

Arithmetic: Python integers and fractions.Fraction only. Every transcendental
value (arctan, cos, sin, log, pi) comes from a rational Taylor series with an
explicit remainder bound, outward rounded to dyadics. No python-flint, no
mpmath, no floating point in any decision. Written from the mathematics of
the paper (Lemma wb, certificate C2), not from certify_c2.py.

Usage: certify_c6.py z2000.json L vectors_c2.json OUT.json [--jobs N]

It recomputes, from the zero intervals I_k = [mid - r, mid + r]
(r = 2^eps_exp plus the stored radius):
  theta_k = 2 arctan(1/(2 g)), w_k = 1/(1/4 + g^2), enclosed over g in I_k
  W_up = C - 2 sum_k w_k(lower end), C = 2 + gamma_E - log(4 pi)
  per vector beta: B(theta) = sum_j beta_j e^{i j theta}; |B(theta_k)| upper
  end (k >= 2), |B(theta_1)| lower end, arg B(theta_1) enclosure,
  H = sum_{k=2}^{2000} 2 w_k |B(theta_k)| + W S, rho = H / (2 w_1 |B_1|),
  arc (phi0 - arccos rho, phi0 + arccos rho), phi0 = -arg B_1 - pi,
  and the coverage of [0, 2 pi] by the open arcs and their shifts by 2 pi m.
NOT rechecked here: part (a) of the zero list (Z changes sign on every I_k);
that is step 1 of C2 and needs zeta evaluation.
"""
import sys, json, time, hashlib, resource, datetime, argparse
from fractions import Fraction as Fr
from math import isqrt
from multiprocessing import Pool

XP = 170          # dyadic grid 2^-XP for arguments and angle bounds
P = 160           # fixed-point scale of the unit vectors e^{i j theta}
WP = 150          # grid of the weights w_k
TINY = Fr(1, 2 ** 90)   # extra shrink of every arc end

# gamma_E, 37 decimals, a trusted constant with 1e-36 slack
GAMMA_LO = Fr(5772156649015328606065120900824024, 10 ** 34)
GAMMA_HI = GAMMA_LO + Fr(1, 10 ** 33)


def fl(x, p):  # floor of Fraction x to the grid 2^-p
    return Fr((x.numerator << p) // x.denominator, 1 << p)


def cl(x, p):
    return -fl(-x, p)


# ---------------------------------------------------------------- series
def atan_enc(x):
    """enclosure (lo, hi) of arctan(x), x Fraction in [0, 1/2]."""
    assert 0 <= x <= Fr(1, 2)
    lo_x, hi_x = fl(x, XP), cl(x, XP)

    def ser(t):
        n, s, t2, pw = 0, Fr(0), t * t, t
        while True:
            term = pw / (2 * n + 1)
            s += term if n % 2 == 0 else -term
            n += 1
            pw *= t2
            nxt = pw / (2 * n + 1)
            if nxt < Fr(1, 2 ** (XP + 4)):
                break
        nxt_s = s + (nxt if n % 2 == 0 else -nxt)   # s_{n+1}
        return min(s, nxt_s), max(s, nxt_s)         # alternating, decreasing

    return fl(ser(lo_x)[0], XP), cl(ser(hi_x)[1], XP)


def pi_enc():  # Machin
    a5, a239 = atan_enc(Fr(1, 5)), atan_enc(Fr(1, 239))
    return 16 * a5[0] - 4 * a239[1], 16 * a5[1] - 4 * a239[0]


PI_LO, PI_HI = pi_enc()


def atan01_enc(t):
    """arctan of exact Fraction t in [0, 1]."""
    if t <= Fr(1, 2):
        return atan_enc(t)
    u = (1 - t) / (1 + t)          # in [0, 1/3]
    ul, uh = atan_enc(u)
    return PI_LO / 4 - uh, PI_HI / 4 - ul


def atan2_enc(y, x):
    """arg of the nonzero Gaussian rational x + i y, in (-pi, pi]."""
    ax, ay = abs(x), abs(y)
    assert ax or ay
    if ay <= ax:
        a = atan01_enc(Fr(ay) / Fr(ax))
    else:
        b = atan01_enc(Fr(ax) / Fr(ay))
        a = (PI_LO / 2 - b[1], PI_HI / 2 - b[0])
    if x > 0 and y >= 0:
        return a
    if x <= 0 and y >= 0:
        return (PI_LO - a[1], PI_HI - a[0])
    if x < 0 and y < 0:
        return (-(PI_HI - a[0]), -(PI_LO - a[1]))
    return (-a[1], -a[0])


def atanh_enc(u):
    """artanh(u), u Fraction in [0, 1/2]."""
    lo_u, hi_u = fl(u, XP), cl(u, XP)

    def ser(t):
        s, n, t2, pw = Fr(0), 0, t * t, t
        while pw / (2 * n + 1) >= Fr(1, 2 ** (XP + 4)):
            s += pw / (2 * n + 1)
            n += 1
            pw *= t2
        return s, s + pw / (1 - t2)   # tail <= pw / (1 - t^2)

    return fl(ser(lo_u)[0], XP), cl(ser(hi_u)[1], XP)


def log_enc(x):
    """log of Fraction x in [1, 2.5] as 2 artanh((x-1)/(x+1))."""
    a, b = atanh_enc((x - 1) / (x + 1))
    return 2 * a, 2 * b


def log4pi_enc():
    a, b = atanh_enc(Fr(1, 3))      # log 2 = 2 artanh(1/3)
    l2 = (2 * a, 2 * b)
    # log(4 pi) = 3 log 2 + log(pi / 2), pi/2 in [1.57, 1.58]
    return (3 * l2[0] + log_enc(PI_LO / 2)[0], 3 * l2[1] + log_enc(PI_HI / 2)[1])


# ---------------------------------------------------------------- zeros
def load_zeros(path):
    z = json.load(open(path))
    eps = Fr(2) ** z["eps_exp"]
    out = []
    for mm, me, rm, re_ in z["gamma_mid_man_exp_rad_man_exp"]:
        mid = Fr(mm) * Fr(2) ** me
        rad = abs(Fr(rm) * Fr(2) ** re_)
        out.append((mid, eps + rad))
    return out, z


def zero_data(mid, e):
    glo, ghi = mid - e, mid + e
    assert glo > 1
    th_lo = fl(2 * atan_enc(1 / (2 * ghi))[0], XP)   # theta decreases in g
    th_hi = cl(2 * atan_enc(1 / (2 * glo))[1], XP)
    w_hi = cl(1 / (Fr(1, 4) + glo * glo), WP)         # w decreases in g
    w_lo = fl(1 / (Fr(1, 4) + ghi * ghi), WP)
    return th_lo, th_hi, w_lo, w_hi


def unit_table(th_m, L):
    """fixed point (units 2^-P) of e^{i j th_m}, j < L, error <= 8 j units."""
    t2 = th_m * th_m
    c, s = Fr(0), Fr(0)
    term_c, term_s = Fr(1), th_m
    n = 0
    tol = Fr(1, 2 ** (P + 10))
    while True:   # th_m < 1: alternating, decreasing terms
        c += term_c if n % 2 == 0 else -term_c
        s += term_s if n % 2 == 0 else -term_s
        term_c = term_c * t2 / ((2 * n + 1) * (2 * n + 2))
        term_s = term_s * t2 / ((2 * n + 2) * (2 * n + 3))
        n += 1
        if term_c < tol and term_s < tol:
            break
    one = 1 << P
    ur = (c.numerator * one + c.denominator // 2) // c.denominator
    ui = (s.numerator * one + s.denominator // 2) // s.denominator
    zr, zi = [one], [0]
    for _ in range(1, L):
        a, b = zr[-1], zi[-1]
        zr.append((a * ur - b * ui) >> P)    # floor: error < 1 per component
        zi.append((a * ui + b * ur) >> P)
    return zr, zi


def process_chunk(args):
    idxs, zeros, nz, jsum, L = args
    sum_wlo = 0
    nvec = len(nz)
    hacc = [0] * nvec
    first = None
    for k in idxs:
        mid, e = zeros[k]
        th_lo, th_hi, w_lo, w_hi = zero_data(mid, e)
        wlo_int = int(w_lo * (1 << WP))
        whi_int = int(w_hi * (1 << WP))
        sum_wlo += wlo_int
        th_m = fl((th_lo + th_hi) / 2, XP)
        r = max(th_hi - th_m, th_m - th_lo)
        r_units = -((-r.numerator << P) // r.denominator)
        zr, zi = unit_table(th_m, L)
        for i in range(nvec):
            br = sum(b * zr[j] for j, b in nz[i])
            bi = sum(b * zi[j] for j, b in nz[i])
            err = jsum[i] * (8 + r_units)          # units 2^-(P+50)
            if k == 0:
                if first is None:
                    first = {}
                first[i] = (br, bi, err, wlo_int, whi_int)
            else:
                up = isqrt(br * br + bi * bi) + 1 + err
                hacc[i] += 2 * whi_int * up
    return sum_wlo, hacc, first


# ---------------------------------------------------------------- main
def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def fdec(x, nd=12):
    x = Fr(x)
    sgn = "-" if x < 0 else ""
    x = abs(x)
    n = (x.numerator * 10 ** nd) // x.denominator
    s = str(n).rjust(nd + 1, "0")
    return sgn + s[:-nd] + "." + s[-nd:]


def run(zpath, L, vpath, outpath, jobs):
    t0 = time.time()
    zeros, zraw = load_zeros(zpath)
    K = len(zeros)
    if K != 2000:
        print("REFUSED: need 2000 zeros")
        return 2
    vj = json.load(open(vpath))
    if vj["den_exp"] != 50:
        print("REFUSED: den_exp != 50")
        return 2
    vecs = vj["vectors"]
    for v in vecs:
        if len(v["a"]) != L:
            print(f"REFUSED: vector {v['idx']} has {len(v['a'])} weights, need L={L}")
            return 2
        if min(v["a"]) < 0:
            print(f"REFUSED: vector {v['idx']} has a negative weight")
            return 2
    if L != 594:
        print("REFUSED: this certificate is for L=594")
        return 2
    nvec = len(vecs)
    nz = [[(j, b) for j, b in enumerate(v["a"]) if b] for v in vecs]
    jsum = [sum(j * b for j, b in n) for n in nz]
    S = [Fr(sum(v["a"]), 1 << 50) for v in vecs]

    l4 = log4pi_enc()
    C_up = 2 + GAMMA_HI - l4[0]
    chunks = [[0]] + [list(range(1 + c, K, jobs * 8)) for c in range(jobs * 8)]
    chunks = [c for c in chunks if c]
    tasks = [(c, zeros, nz, jsum, L) for c in chunks]
    with Pool(jobs) as pool:
        res = pool.map(process_chunk, tasks, chunksize=1)
    t_sums = time.time() - t0
    sum_wlo = sum(r[0] for r in res)
    first = [r[2] for r in res if r[2]][0]
    W_up = C_up - 2 * Fr(sum_wlo, 1 << WP)
    if not (0 < W_up < Fr(1, 1000)):
        print("REFUSED: W upper end implausible", float(W_up))
        return 2
    Hk = [sum(r[1][i] for r in res) for i in range(nvec)]

    P2 = 2 * PI_HI
    arcs, rows = [], []
    max_rho = Fr(0)
    ok = True
    scale = Fr(1, 1 << (WP + P + 50))
    unit = Fr(1, 1 << (P + 50))
    for i, v in enumerate(vecs):
        br, bi, err, w1lo, w1hi = first[i]
        H = Hk[i] * scale + W_up * S[i]
        errq = err * unit
        mod_mid_lo = Fr(isqrt(br * br + bi * bi)) * unit
        mod_lo = mod_mid_lo - errq
        if mod_lo <= 0:
            rows.append({"idx": v["idx"], "rho_upper": None, "fail": "B1 lower end not positive"})
            ok = False
            continue
        rho_up = cl(H / (2 * Fr(w1lo, 1 << WP) * mod_lo), 100)
        rows.append({"idx": v["idx"], "rho_upper": fdec(rho_up, 15)})
        max_rho = max(max_rho, rho_up)
        if rho_up >= 1:
            rows[-1]["fail"] = "rho >= 1"
            ok = False
            continue
        al, ah = atan2_enc(Fr(bi), Fr(br))          # arg of the disk centre
        s_up = cl(errq / mod_lo, 100)                # sin(angle error) <= s_up
        delta = 2 * s_up                             # asin(s) <= (pi/2) s <= 2 s
        phi_lo, phi_hi = -ah - PI_HI, -al - PI_LO    # phi0 = -arg B - pi
        s2 = 1 - rho_up * rho_up
        sq_lo = Fr(isqrt((s2.numerator << (2 * XP)) // s2.denominator), 1 << XP)
        a_lo = atan2_enc(sq_lo, rho_up)[0]           # arccos(rho) >= arccos(rho_up)
        left = phi_hi + delta - a_lo + TINY
        right = phi_lo - delta + a_lo - TINY
        if right <= left:
            rows[-1]["fail"] = "empty arc"
            ok = False
            continue
        arcs.append((left, right, v["idx"]))
        rows[-1]["arc_lo"] = fdec(left, 15)
        rows[-1]["arc_hi"] = fdec(right, 15)
    t_arcs = time.time() - t0

    cover_ok, chain, min_overlap, gap_at = False, [], None, None
    if ok:
        shifts = [(l + m * P2, r + m * P2, idx) for (l, r, idx) in arcs for m in range(-1, 3)]
        cur, prev_r, cover_ok = Fr(0), None, True
        while cur <= P2:
            cand = [s for s in shifts if s[0] < cur < s[1]]
            if not cand:
                cover_ok, gap_at = False, cur
                break
            best = max(cand, key=lambda s: s[1])
            if prev_r is not None:
                ov = prev_r - best[0]
                min_overlap = ov if min_overlap is None else min(min_overlap, ov)
            chain.append(best[2])
            cur = prev_r = best[1]
    ok = ok and cover_ok
    t_total = time.time() - t0
    rec = {
        "purpose": "proof",
        "certificate": "C6",
        "status": "PASS" if ok else "FAIL",
        "run_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "script_sha256": sha(__file__),
        "inputs_sha256": {"zeros": sha(zpath), "vectors": sha(vpath)},
        "claim": "independent exact recheck of C2: under RH every window of 594 consecutive indices n >= 1 has both signs of c_n (T4); part (a) of the zero list is not rechecked here",
        "result": {
            "L": L, "vectors": nvec, "zeros_used": K,
            "arithmetic": "python int and fractions.Fraction, rational Taylor with explicit remainder, dyadic outward rounding",
            "zero_interval": "mid +- (2^eps_exp + stored radius)",
            "W_upper": fdec(W_up, 15), "W_upper_float": float(W_up),
            "certified_max_rho_upper": fdec(max_rho, 15),
            "c2_certified_max_rho_upper": "0.995073671447413",
            "cover": {"ok": cover_ok, "arcs_in_chain": len(chain), "chain_vectors": chain,
                      "min_strict_overlap": None if min_overlap is None else fdec(min_overlap, 12),
                      "gap_at": None if gap_at is None else fdec(gap_at, 12),
                      "open_arcs": True, "shifts_of_2pi": "-1..2"},
            "rows": rows,
        },
        "time_sums_s": round(t_sums, 2), "time_arcs_s": round(t_arcs - t_sums, 2),
        "time_total_s": round(t_total, 2), "jobs": jobs,
        "peak_rss_kb_self": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "peak_rss_kb_children": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
        "python_version": sys.version.split()[0],
        "argv": sys.argv[1:],
    }
    json.dump(rec, open(outpath, "w"), indent=1)
    if ok:
        print(f"PASS  max rho upper {fdec(max_rho, 10)}  (C2: 0.9950736714)  W_up {float(W_up):.10e}  "
              f"chain {len(chain)} arcs  {t_total:.1f}s")
        return 0
    why = [r for r in rows if r.get("fail")]
    print("FAIL", (why[0]["idx"], why[0]["fail"]) if why else f"coverage gap at {fdec(gap_at, 6) if gap_at is not None else '?'}",
          f"max rho {fdec(max_rho, 6)}")
    return 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("zeros")
    ap.add_argument("L", type=int)
    ap.add_argument("vectors")
    ap.add_argument("out")
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    sys.exit(run(a.zeros, a.L, a.vectors, a.out, min(a.jobs, 4)))
