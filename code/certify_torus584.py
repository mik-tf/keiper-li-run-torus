#!/usr/bin/env python3
"""C1: certificate that the torus has a strict window of L = 584 (paper 3, T3).

Claim certified: for the stored phases x_1..x_K (K = 1400, exact integers over 2^40) and every j = 0..L-1,
  F(j) + T cos(min(|j - c| theta_up, pi)) > 0,   F(j) = sum_{k<=K} 2 w_k cos(j theta_k + x_k),
where theta_k and w_k are balls over the interval gamma_k in [mid_k -+ 2^-20] (Hardy Z rechecked: strict sign change at both
endpoints, 128 bits), theta_up = theta at the lower end of I_{K+1}, T = T_used <= the lower end of T_K = C - 2 sum_{k<=K} w_k.
Aligned tail: unlisted zeros (all with gamma >= lower end of I_{K+1}, by Lemma zeros (b), cited and not re-run) get phases
x_k = -c theta_k; their term is >= (sum of their 2 m w = T_K) cos(min(|j-c| theta_k, pi)) >= T cos(min(|j-c| theta_up, pi)).
Then F_x(j) > 0 for j = 0..L-1 at that x of the infinite torus: L*_strict >= L.
Mode 'robust' (broken input): the term is -T instead (constant tail, adversarial phases).
Guards: T_used <= lower end of T_K, else refuse; zero intervals ordered and disjoint; every check raises SystemExit('FAIL ...').
Usage: python3 certify_torus584.py ZEROS.json INPUTS.json OUT.json
"""
import sys, json, time, resource, hashlib, datetime
import flint
from flint import arb, acb, ctx, fmpq

def fail(m): raise SystemExit("FAIL: " + m)
def sg(x): return 1 if x > 0 else (-1 if x < 0 else 0)
def Zf(t):
    s = acb(arb(1) / 2, t)
    thv = acb(arb(1) / 4, t / 2).lgamma().imag - t / 2 * arb.pi().log()
    return (acb(0, thv).exp() * s.zeta()).real
def sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()
def q(m, e): return fmpq(m * 2**e, 1) if e >= 0 else fmpq(m, 2**(-e))

def main():
    if len(sys.argv) != 4: raise SystemExit(__doc__)
    zfile, ifile, out = sys.argv[1:]
    t_start = time.time(); ctx.prec = 128
    zj = json.load(open(zfile)); I = json.load(open(ifile))
    N = zj["N"]; K = I["K"]; L = I["L"]
    if not (zj["count_NT"] == N == 2000 and zj["sign_changes"] == N and zj["eps_exp"] == -20): fail("z2000.json header")
    if not (1 <= K < N and len(I["x_int"]) == K and I["tail"] in ("aligned", "robust")): fail("inputs shape")
    cn, cd = (I["c"].split("/") + ["1"])[:2]; c = arb(fmpq(int(cn), int(cd)))
    mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
    eps = arb(2) ** -20; pm1 = arb(-1).union(arb(1)); T0 = arb(fmpq(*zj["T"]))
    t0 = time.time()
    for i in range(K + 1):                       # zeros 1..K and the interval I_{K+1} (its lower end gives theta_up)
        g = mids[i]
        if not (g - eps) > 0: fail(f"zero {i+1} interval not positive")
        if not sg(Zf(g - eps)) * sg(Zf(g + eps)) == -1: fail(f"no Hardy Z sign change at the endpoints of interval {i+1}")
        nxt = mids[i + 1] - eps if i + 1 < N else T0
        if not (g + eps) < nxt: fail(f"interval {i+1} overlaps the next one")
    t_zeros = time.time() - t0
    one = arb(1)
    gam = [g + eps * pm1 for g in mids[:K]]
    w = [one / (one / 4 + g * g) for g in gam]
    th = [2 * (one / (2 * g)).atan() for g in gam]
    th_up = 2 * (one / (2 * (mids[K] - eps))).atan()          # theta of the lower end of I_{K+1}: bounds every unlisted zero
    C = 2 + arb.const_euler() - (4 * arb.pi()).log()
    TK = C - 2 * sum(w, arb(0))
    Tused = arb(fmpq(I["T_used_num"], 2 ** I["T_used_den_exp"]))
    if not TK.lower() > 0: fail("T_K lower end not positive")
    if not Tused <= TK.lower(): fail("GUARD REFUSES: T_used exceeds the certified lower end of T_K")
    if not Tused > 0: fail("T_used not positive")
    x = [arb(fmpq(v, 2 ** I["x_den_exp"])) for v in I["x_int"]]
    a = [2 * wk for wk in w]
    t0 = time.time()
    pi = arb.pi(); margins = []; worst = None
    for j in range(L):
        s = arb(0)
        for k in range(K):
            s += a[k] * (j * th[k] + x[k]).cos()
        d = abs(j - c) * th_up
        arg = d if d.upper() <= pi.lower() else (pi if d.lower() >= pi.upper() else None)
        if arg is None: fail(f"min(|j-c| theta_up, pi) undecided at j={j}")
        tail = Tused * arg.cos() if I["tail"] == "aligned" else -Tused
        lo = (s + tail).lower()
        margins.append(float(lo))
        if worst is None or lo < worst[0]: worst = (lo, j)
    t_sums = time.time() - t0
    ok = bool(worst[0] > 0)
    res = {"purpose": "proof", "certificate": "C1", "status": "PASS" if ok else "FAIL",
           "run_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
           "script_sha256": sha(sys.argv[0]), "inputs_sha256": {"zeros": sha(zfile), "inputs": sha(ifile)},
           "claim": f"L*_strict >= {L} (strict window of {L} at phases x of the infinite torus, aligned tail)" if ok else "NOT certified",
           "result": {"K": K, "L": L, "c": I["c"], "tail": I["tail"], "certified_min_margin": float(worst[0]), "argmin_j": worst[1],
                      "min_margin_str": worst[0].str(10, radius=False) if hasattr(worst[0], "str") else None,
                      "T_used": float(Tused), "T_K_lower": float(TK.lower()), "T_K_upper": float(TK.upper()),
                      "theta_up": float(th_up.mid()), "zeros_Z_rechecked": K + 1},
           "prec_bits": 128, "python_flint_version": flint.__version__, "python_version": sys.version, "argv": " ".join(sys.argv),
           "time_zeros_s": t_zeros, "time_sums_s": t_sums, "time_total_s": time.time() - t_start,
           "peak_rss_kb_self": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps(res))
    if not ok: fail(f"min margin {float(worst[0])} at j={worst[1]} is not positive")
main()
