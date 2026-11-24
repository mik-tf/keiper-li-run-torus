#!/usr/bin/env python3
"""C4: certificate for T6 (paper 3): runs of 584 under RH and LI_theta up to Gamma, with the zeros beyond 1400 handled by an
explicit N(T) bound (Bellotti-Wong arXiv:2412.15470 v2, Theorem 1.1, second estimate; see nt_bound.py, constants exact rationals).

Claim certified: for the stored phases x_1..x_1400 of C1 (inputs_c1.json) and every j = 0..L-1,
  m := min_j [ F(j) + (T_K - T_G) cos(min(|j - c| theta_up, pi)) ] - T_G > 0,
F, theta_up, T_K as in C1 (K = 1400, 128 bits, Hardy Z rechecked). T_G >= sum_{gamma > G} 2/(1/4 + gamma^2) is the tail mass beyond Gamma.
Zeros with gamma in (gamma_1400, G] (K' - 1400 of them, K' = N(G)) are placed at crest x_k = -c theta_k: their total weight is
T_K - (mass of zeros beyond G) >= T_K - T_G and each cos(min(|j-c| theta_k, pi)) >= cos(min(|j-c| theta_up, pi)) because
theta_k <= theta_up (gamma_k >= lower end of I_1401, Lemma zeros (b)); zeros beyond G are adversarial: contribute >= -T_G.
Needs G > upper end of I_1400 (indeed G > lower end of I_1401), checked.
Box and density (Lemma box, Lemma weyl of paper 2): moving all K' phases by at most r changes the sum by at most r * sum 2 w_k <= r * C,
C = 2 + Euler - log 4 pi = sum over ALL zeros of 2 w; so r = m_lower / C works (conservative: uses C instead of the partial sum).
Under LI_theta up to G the density of the set of M with a run of L positive values is >= (r/pi)^K', K' <= upper bound of N(G).
Guard: T_G_used must be >= the upper end of the T_G recomputed from the cited constants, else refuse ("GUARD REFUSES").
Usage: python3 certify_tail_c4.py ZEROS.json INPUTS_C1.json INPUTS_C4.json OUT.json
"""
import sys, json, time, resource, hashlib, datetime, os
import flint
from flint import arb, acb, ctx, fmpq
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nt_bound

def fail(m): raise SystemExit("FAIL: " + m)
def sg(x): return 1 if x > 0 else (-1 if x < 0 else 0)
def Zf(t):
    s = acb(arb(1) / 2, t)
    thv = acb(arb(1) / 4, t / 2).lgamma().imag - t / 2 * arb.pi().log()
    return (acb(0, thv).exp() * s.zeta()).real
def sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()
def q(m, e): return fmpq(m * 2**e, 1) if e >= 0 else fmpq(m, 2**(-e))

def main():
    if len(sys.argv) != 5: raise SystemExit(__doc__)
    zfile, ifile, jfile, out = sys.argv[1:]
    t_start = time.time(); ctx.prec = 128
    zj = json.load(open(zfile)); I = json.load(open(ifile)); J = json.load(open(jfile))
    N = zj["N"]; K = I["K"]; L = I["L"]
    if not (zj["count_NT"] == N == 2000 and zj["sign_changes"] == N and zj["eps_exp"] == -20): fail("z2000.json header")
    if not (1 <= K < N and len(I["x_int"]) == K and I["tail"] == "aligned"): fail("inputs_c1 shape")
    G = arb(int(J["Gamma"]))
    cn, cd = (I["c"].split("/") + ["1"])[:2]; c = arb(fmpq(int(cn), int(cd)))
    mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
    eps = arb(2) ** -20; pm1 = arb(-1).union(arb(1)); T0 = arb(fmpq(*zj["T"]))
    t0 = time.time()
    for i in range(K + 1):
        g = mids[i]
        if not (g - eps) > 0: fail(f"zero {i+1} interval not positive")
        if not sg(Zf(g - eps)) * sg(Zf(g + eps)) == -1: fail(f"no Hardy Z sign change at the endpoints of interval {i+1}")
        nxt = mids[i + 1] - eps if i + 1 < N else T0
        if not (g + eps) < nxt: fail(f"interval {i+1} overlaps the next one")
    t_zeros = time.time() - t0
    if not (G > mids[K] - eps): fail("Gamma not above the lower end of I_1401")
    if not G > 3: fail("Gamma < e")
    one = arb(1)
    gam = [g + eps * pm1 for g in mids[:K]]
    w = [one / (one / 4 + g * g) for g in gam]
    th = [2 * (one / (2 * g)).atan() for g in gam]
    th_up = 2 * (one / (2 * (mids[K] - eps))).atan()
    C = 2 + arb.const_euler() - (4 * arb.pi()).log()
    TK = C - 2 * sum(w, arb(0))
    if not TK.lower() > 0: fail("T_K lower end not positive")
    TGu = nt_bound.tgamma_upper(G)
    Tg = arb(fmpq(J["Tgamma_used_num"], 2 ** J["Tgamma_used_den_exp"]))
    if not Tg >= TGu.upper(): fail("GUARD REFUSES: T_Gamma_used is below the upper bound recomputed from the cited N(T) constants")
    crest = TK.lower() - Tg
    if not crest > 0: fail("T_K - T_Gamma not positive")
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
        lo = (s + crest * arg.cos() - Tg).lower()
        margins.append(float(lo))
        if worst is None or lo < worst[0]: worst = (lo, j)
    t_sums = time.time() - t0
    ok = bool(worst[0] > 0)
    Kp = nt_bound.kprime_upper(G)
    res = {"purpose": "proof", "certificate": "C4", "status": "PASS" if ok else "FAIL",
           "run_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
           "script_sha256": sha(sys.argv[0]), "nt_bound_sha256": sha(os.path.join(os.path.dirname(os.path.abspath(__file__)), "nt_bound.py")),
           "inputs_sha256": {"zeros": sha(zfile), "inputs_c1": sha(ifile), "inputs_c4": sha(jfile)},
           "nt_source": nt_bound.CITE,
           "claim": (f"T6 numerics: at Gamma = {J['Gamma']} the torus run of {L} survives the zeros beyond 1400 (crest) and the tail beyond Gamma (adversarial)" if ok else "NOT certified"),
           "result": {"K": K, "L": L, "Gamma": J["Gamma"], "certified_min_margin": float(worst[0]), "argmin_j": worst[1],
                      "min_margin_str": worst[0].str(10, radius=False),
                      "T_Gamma_upper_recomputed": float(TGu.upper()), "T_Gamma_used": float(Tg), "T_K_lower": float(TK.lower()),
                      "two_T_Gamma": float(2 * Tg), "theta_up": float(th_up.mid()), "zeros_Z_rechecked": K + 1,
                      "Kprime_upper": float(Kp.upper())}}
    if ok:
        r_low = (worst[0] / C).lower()
        Ku = Kp.upper()
        dens = (Ku * (arb(r_low) / pi).log() / arb(10).log())
        res["result"].update({"box_radius_r_lower": float(r_low), "r_formula": "m_lower / C, C = 2 + Euler - log 4pi",
                              "density_log10_lower": float(dens.lower()),
                              "density_constant": f"(r/pi)^K' >= 10^({float(dens.lower()):.6g}), r >= {float(r_low):.6g}, K' <= {float(Ku):.0f}"})
    res.update({"prec_bits": 128, "python_flint_version": flint.__version__, "python_version": sys.version, "argv": " ".join(sys.argv),
                "time_zeros_s": t_zeros, "time_sums_s": t_sums, "time_total_s": time.time() - t_start,
                "peak_rss_kb_self": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps(res))
    if not ok: fail(f"min margin {float(worst[0])} at j={worst[1]} is not positive")
main()
