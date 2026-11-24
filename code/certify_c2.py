#!/usr/bin/env python3
"""Certificate C2 (paper keiper-li-run-torus, theorem T4): full-window dual, arc cover of the phase circle.

Claim certified (CONDITIONAL ON RH, Lemma zeros part (a) of paper keiper-li-sign-runs): every window of L consecutive
indices n >= 1 contains an n with c_n > 0 and an n with c_n < 0, so every run of one sign has length <= L - 1.

Proof (README.md has the assumptions). Window n0 .. n0 + L - 1, weights a_j >= 0 (j = 0..L-1, not all 0), A(t) = sum a_j e^{i j t}.
c_n = sum_k 2 w_k (zero k term, amplitude 2 w_k) + tail, |tail| <= W = C - 2 sum_{k<=2000} w_k.  Zero-1 term at n0 + j is
2 w_1 cos(j theta_1 + phi), phi = n0 theta_1 + const (mod 2 pi) is unknown, so ALL phi in the circle are covered.
  sum a_j c_{n0+j} <= 2 w_1 Re(e^{i phi} A1) + N,   N = sum_{k=2..2000} 2 w_k |A(theta_k)| + W S,  A1 = A(theta_1), S = sum a_j.
If no c is < 0 the left side is >= 0; if no c is > 0, the same holds for -c, i.e. phi + pi.  With rho = N / (2 w_1 |A1|) and
phi0 = -arg(A1) - pi:  -2 w_1 Re(e^{i phi} A1) = 2 w_1 |A1| cos(phi - phi0) > N exactly when |phi - phi0| < arccos(rho).
So on that open arc the window is impossible.  Arcs of several vectors that cover the whole circle exclude every phi, hence
both all-nonnegative and all-nonpositive windows (phi and phi + pi both covered).
Everything is ball arithmetic at 128 bits (no float): theta_k, w_k are balls over the whole zero interval I_k (not midpoints);
every |A(theta_k)| is replaced by the upper end of its ball; |A1| by the lower end; rho by its upper end; the arc is
(phi0 - h, phi0 + h) with h = arccos(rho upper) in ball arithmetic, and the stored ends are shrunk (upper end of the left end,
lower end of the right end).  Cover: arcs and their shifts by 2 pi m are exact rationals; the open arcs must contain every point
of [0, upper end of 2 pi] (a chain in which each next arc strictly overlaps the previous right end).
Guards: Hardy Z sign change at both ends of every zero interval (128 bits); W_used >= upper end of the certified W (a lower W is
refused); weights integers >= 0 over 2^50, every vector has exactly L entries (window = support); |A1| ball excludes 0; rho upper < 1 for
every vector (a vector that fails is refused, not skipped).
Usage: python3 certify_c2.py ZEROS.json L VECTORS.json OUT.json [--jobs 4] [--wused P/Q] [--cache DIR]
All failures raise SystemExit("FAIL ..."); no assert.
"""
import sys, json, time, resource, hashlib, datetime, os
from fractions import Fraction
from multiprocessing import Pool
import flint
from flint import arb, acb, ctx, fmpq, arb_mat

EPS_EXP = -20
DEN_EXP = 50
PREC = 128
NCHUNK = 16          # fixed, so the result does not depend on --jobs
CODE_TAG = "c2-v1"
FZ = Fraction


def fail(msg):
    raise SystemExit("FAIL: " + msg)


def sg(x):
    return 1 if x > 0 else (-1 if x < 0 else 0)


def Zf(t):
    s = acb(arb(1) / 2, t)
    thv = acb(arb(1) / 4, t / 2).lgamma().imag - t / 2 * arb.pi().log()
    return (acb(0, thv).exp() * s.zeta()).real


def q(man, e):
    return fmpq(man * 2 ** e, 1) if e >= 0 else fmpq(man, 2 ** (-e))


def mk(t):
    """ball from (mid man, mid exp, rad man, rad exp), all exact integers"""
    m, e, rm, re_ = t
    return arb(m) * arb(2) ** e + (arb(rm) * arb(2) ** re_) * arb(-1).union(arb(1))


def ex(x):
    m, e = x.mid().man_exp(); r, re_ = x.rad().man_exp()
    return (int(m), int(e), int(r), int(re_))


def frac(x):
    """exact arb (radius 0) -> Fraction"""
    if x.rad() != 0:
        fail("internal: endpoint is not exact")
    m, e = x.man_exp()
    return FZ(int(m)) * FZ(2) ** int(e)


def fstr(f):
    return f"{f.numerator}/{f.denominator}"


# ---------------------------------------------------------------- globals filled before the Pool forks
G = {}


def setup_globals(zfile):
    ctx.prec = PREC
    zj = json.load(open(zfile))
    N = zj["N"]
    if not (zj["count_NT"] == N == 2000 and zj["sign_changes"] == N and zj["eps_exp"] == EPS_EXP):
        fail("z2000.json header is not N = 2000, 2000 sign changes, eps 2^-20")
    mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
    if len(mids) != N:
        fail("number of midpoints")
    eps = arb(2) ** EPS_EXP
    pm1 = arb(-1).union(arb(1))
    G["N"] = N; G["mids"] = mids; G["eps"] = eps
    G["T"] = arb(fmpq(*zj["T"]))
    gam = [g + eps * pm1 for g in mids]
    one = arb(1)
    G["w"] = [one / (one / 4 + g * g) for g in gam]
    G["th"] = [2 * (one / (2 * g)).atan() for g in gam]


def zero_task(rng):
    ctx.prec = PREC
    mids, eps, N, T = G["mids"], G["eps"], G["N"], G["T"]
    for i in rng:
        g = mids[i]
        if not (g - eps) > 0:
            return f"zero {i+1} interval not positive"
        if not sg(Zf(g - eps)) * sg(Zf(g + eps)) == -1:
            return f"no Hardy Z sign change at the endpoints of interval {i+1}"
        nxt = mids[i + 1] - eps if i + 1 < N else T
        if not (g + eps) < nxt:
            return f"interval {i+1} overlaps the next one (or exceeds T)"
    return None


def sum_task(args):
    """k indices ks (0-based), vectors as lists of ints.  Returns per-vector partial N0 (k >= 1) and, if 0 in ks, A1."""
    ks, vecs = args
    ctx.prec = PREC
    nv = len(vecs); L = len(vecs[0])
    two50 = arb(2) ** DEN_EXP
    ent = []
    for j in range(L):
        for v in range(nv):
            ent.append(arb(vecs[v][j]) / two50)       # exact
    Am = arb_mat(L, nv, ent)
    w, th = G["w"], G["th"]
    part = [arb(0)] * nv
    A1 = None
    for k in ks:
        cr = []; sr = []
        for j in range(L):
            e = acb(0, th[k] * j).exp()     # direct exp (repeated multiplication blows up the boxes)
            cr.append(e.real); sr.append(e.imag)
        Re = arb_mat(1, L, cr) * Am
        Im = arb_mat(1, L, sr) * Am
        if k == 0:
            A1 = [ex(Re[0, v]) + ex(Im[0, v]) for v in range(nv)]
        else:
            for v in range(nv):
                part[v] = part[v] + 2 * w[k] * acb(Re[0, v], Im[0, v]).abs_upper()
    return [ex(p) for p in part], A1


def main():
    args = sys.argv[1:]
    opt = {"--jobs": "4", "--wused": None, "--cache": None}
    pos = []
    i = 0
    while i < len(args):
        if args[i] in opt:
            opt[args[i]] = args[i + 1]; i += 2
        else:
            pos.append(args[i]); i += 1
    if len(pos) != 4:
        raise SystemExit(__doc__)
    zfile, Ls, vfile, out = pos
    L = int(Ls); jobs = int(opt["--jobs"]); cache = opt["--cache"]
    t_start = time.time()
    ctx.prec = PREC
    if L < 2:
        fail("bad L")
    def sha(p):
        return hashlib.sha256(open(p, "rb").read()).hexdigest()
    setup_globals(zfile)
    N = G["N"]; w = G["w"]; th = G["th"]
    # ---- inputs
    V = json.load(open(vfile))
    if V["den_exp"] != DEN_EXP:
        fail("weights den_exp must be 50")
    vecs = [[int(x) if type(x) is int else fail("weight is not an integer") for x in v["a"]] for v in V["vectors"]]
    vidx = [v["idx"] for v in V["vectors"]]
    if not vecs:
        fail("no vectors")
    for n_, a in zip(vidx, vecs):
        if len(a) != L:
            fail(f"vector {n_} has {len(a)} weights, the window is L = {L}: refused (window = support of the weights)")
        if not all(x >= 0 for x in a) or not sum(a) > 0:
            fail(f"vector {n_}: weights must be >= 0 with positive sum")
    # ---- constants
    C = 2 + arb.const_euler() - (4 * arb.pi()).log()
    W = C - 2 * sum(w, arb(0))
    if not W > 0:
        fail("W not positive")
    Wu = W.upper()
    if opt["--wused"] is None:
        Wused_u = Wu
    else:
        p_, q_ = opt["--wused"].split("/")
        wb = arb(fmpq(int(p_), int(q_)))
        if not wb.lower() >= Wu:
            fail(f"guard refuses: W_used {opt['--wused']} is below the certified upper end of W = {float(Wu)}")
        Wused_u = wb.upper()
    # ---- zero intervals: Z sign recheck (parallel, fixed chunks)
    t0 = time.time()
    with Pool(jobs) as pool:
        zres = pool.map(zero_task, [range(c, N, NCHUNK) for c in range(NCHUNK)])
    for r in zres:
        if r:
            fail(r)
    t_zeros = time.time() - t0
    # ---- per-vector sums (cache optional, keyed by zeros, L and the integers)
    t0 = time.time()
    zsha = sha(zfile)
    keys = [hashlib.sha256((CODE_TAG + zsha + str(L) + ",".join(map(str, a))).encode()).hexdigest() for a in vecs]
    got = {}
    cache_hits = 0
    if cache:
        for n_, kx in enumerate(keys):
            p = os.path.join(cache, kx + ".json")
            if os.path.exists(p):
                got[n_] = json.load(open(p)); cache_hits += 1
    todo = [n_ for n_ in range(len(vecs)) if n_ not in got]
    if todo:
        tv = [vecs[n_] for n_ in todo]
        tasks = [([0], tv)] + [([k for k in range(1, N) if k % NCHUNK == c], tv) for c in range(NCHUNK)]
        with Pool(jobs) as pool:
            res = pool.map(sum_task, tasks, chunksize=1)
        A1s = res[0][1]
        for pos_, n_ in enumerate(todo):
            tot = arb(0)
            for c in range(1, NCHUNK + 1):
                tot = tot + mk(tuple(res[c][0][pos_]))
            got[n_] = {"N0": list(ex(tot)), "A1": list(A1s[pos_])}
            if cache:
                os.makedirs(cache, exist_ok=True)
                json.dump(got[n_], open(os.path.join(cache, keys[n_] + ".json"), "w"))
    t_sums = time.time() - t0
    # ---- arcs
    twopi = 2 * arb.pi()
    twopi_up = twopi.upper()
    rows = []; segs = []
    rho_max = None
    for n_ in range(len(vecs)):
        N0 = mk(tuple(got[n_]["N0"]))
        t = got[n_]["A1"]
        A1 = acb(mk(tuple(t[:4])), mk(tuple(t[4:])))
        S = sum((arb(x) / arb(2) ** DEN_EXP for x in vecs[n_]), arb(0))
        absl = A1.abs_lower()
        if not absl > 0:
            fail(f"vector {vidx[n_]}: |A1| ball contains 0: refused")
        rho = (N0 + Wused_u * S) / (2 * w[0] * absl)
        rho_up = rho.upper()
        if not rho_up < 1:
            fail(f"vector {vidx[n_]}: rho upper end {float(rho_up)} >= 1: refused")
        phi0 = -A1.arg() - arb.pi()
        h = rho_up.acos()
        lo = (phi0 - h).upper(); hi = (phi0 + h).lower()
        if not hi > lo:
            fail(f"vector {vidx[n_]}: empty arc")
        rows.append({"idx": vidx[n_], "rho_upper": rho_up.str(15, radius=False), "arc_lo": fstr(frac(lo)), "arc_hi": fstr(frac(hi)),
                     "arc_lo_f": float(lo), "arc_hi_f": float(hi)})
        if rho_max is None or rho_up > rho_max:
            rho_max = rho_up
        for m in range(-1, 3):                         # shifts by 2 pi m (outward rounded to shrink the arc)
            sh = twopi * m
            segs.append((frac((lo + sh).upper()), frac((hi + sh).lower()), vidx[n_]))
    # ---- certified coverage of [0, 2 pi upper] by open arcs, strict overlaps
    target = frac(twopi_up)
    segs = [s for s in segs if s[1] > s[0]]
    cur = FZ(0); chain = []; min_ov = None
    while cur <= target:
        best = None
        for lo_, hi_, ix in segs:
            if lo_ < cur < hi_ and (best is None or hi_ > best[1]):
                best = (lo_, hi_, ix)
        if best is None:
            fail(f"coverage gap at phi = {float(cur)} (no arc contains the point; arcs open, an end shared is a gap)")
        if chain:
            ov = float(cur - best[0])
            min_ov = ov if min_ov is None else min(min_ov, ov)
        chain.append(best[2]); cur = best[1]
    # ---- record
    peak_self = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    peak_child = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    res = {
        "purpose": "proof", "certificate": "C2", "status": "PASS",
        "run_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "script_sha256": sha(sys.argv[0]),
        "inputs_sha256": {"zeros": zsha, "vectors": sha(vfile)},
        "claim": f"under RH every window of {L} consecutive indices n >= 1 has both signs of c_n; runs of c_n have length at most {L-1} (T4)",
        "result": {
            "L": L, "conditional_on": "RH, Lemma zeros part (a)", "vectors": len(vecs), "den_exp": DEN_EXP,
            "zeros_used": N, "zeros_Z_rechecked": N, "zero_interval_eps": "2^-20",
            "W_upper": float(Wu), "W_used_upper": float(Wused_u), "W_used_is_certified_upper": bool(Wused_u == Wu),
            "certified_max_rho_upper": rho_max.str(15, radius=False), "certified_max_rho_upper_float": float(rho_max),
            "cover": {"circle_target_upper_2pi": float(target), "arcs_in_chain": len(chain), "chain_vectors": chain,
                      "min_strict_overlap": min_ov, "shifts_of_2pi": "-1..2", "open_arcs": True},
            "rows": rows,
        },
        "prec_bits": PREC, "python_flint_version": flint.__version__, "python_version": sys.version, "argv": " ".join(sys.argv),
        "time_zeros_s": t_zeros, "time_sums_s": t_sums, "time_total_s": time.time() - t_start,
        "cache_hits": cache_hits, "jobs": jobs,
        "peak_rss_kb_self": peak_self, "peak_rss_kb_children": peak_child,
    }
    json.dump(res, open(out, "w"), indent=1)
    print(f"PASS C2 L={L}: {len(vecs)} arcs cover the circle, certified max rho {rho_max.str(10, radius=False)}, "
          f"chain of {len(chain)} arcs, min strict overlap {min_ov}")


main()
