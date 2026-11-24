"""Explicit N(T) bound used by C4 (paper 3, T6), in ball arithmetic with exact rational constants.

Source: C. Bellotti and P.-J. Wong (appendix by A. Fiori), "Improved estimates for the argument and zero-counting function
of the Riemann zeta-function", arXiv:2412.15470 (v2), Theorem 1.1, second estimate. For every T >= e,
  | N(T) - (T/(2 pi)) log(T/(2 pi e)) | <= 0.11200 log T + 0.12567 log log T + 3.77417,
N(T) = #{rho = beta + i gamma : zeta(rho) = 0, 0 < beta < 1, 0 < gamma <= T}; unconditional (no RH). The constants below are
exactly these decimals as rationals. (The first estimate, 0.10076, 0.24460, 8.08344, is sharper only for T >= exp(447.981).)
Not re-proved here; the paper's proofs were not read.

Tail mass T_G = sum_{gamma > G} 2/(1/4 + gamma^2). With f(t) = 1/(1/4 + t^2) decreasing and N(t) f(t) -> 0,
  T_G/2 = -f(G) N(G) + int_G^inf N(t) (-f'(t)) dt,   -f'(t) = 2t/(1/4 + t^2)^2 <= 2/t^3,
so with N(G) >= M(G) - e(G) (boundary term) and 0 <= N(t) <= M(t) + e(t), t >= G (integral), M(t) = (t/2pi) log(t/(2 pi e)):
  T_G <= 2 [ -(s M(G) - e(G)) f(G) + I_M + I_e ],
  I_M = s (1/pi) (log G - log 2pi) / G                       (= int_G^inf M(t) 2/t^3 dt, times s),
  I_e = a (log G/G^2 + 1/(2G^2)) + b (same, using loglog t <= log t) + c/G^2,   e(t) = a log t + b loglog t + c.
s = 1 is the cited bound; s <> 1 scales the N(T) main term and is used ONLY to build the broken input of C4.
"""
from flint import arb, fmpq

A_CONST = fmpq(11200, 100000)
B_CONST = fmpq(12567, 100000)
C_CONST = fmpq(377417, 100000)
CITE = "Bellotti-Wong arXiv:2412.15470 v2, Theorem 1.1, second estimate (T >= e)"

def err(t):
    return arb(A_CONST) * t.log() + arb(B_CONST) * t.log().log() + arb(C_CONST)

def main_term(t):
    pi2 = 2 * arb.pi()
    return t / pi2 * (t / (pi2 * arb(1).exp())).log()

def tgamma_upper(G, s=fmpq(1)):
    """G: arb >= e (an exact integer here). Returns a ball containing an upper bound of T_G."""
    one = arb(1); s = arb(s)
    f = one / (one / 4 + G * G)
    lg = G.log()
    I_M = s / arb.pi() * (lg - (2 * arb.pi()).log()) / G
    k = lg / (G * G) + one / (2 * G * G)
    I_e = arb(A_CONST) * k + arb(B_CONST) * k + arb(C_CONST) / (G * G)
    return 2 * (-(s * main_term(G) - err(G)) * f + I_M + I_e)

def kprime_upper(G):
    """Upper bound of K' = N(G)."""
    return main_term(G) + err(G)
