/-! Pilot checker for the T4 arc cover (paper 3): exact Gaussian-integer arithmetic, dense weights.
Plain Lean, no Mathlib, so the kernel cost is measured alone.  Adapted from the paper 2 checker
(`checkZero` of its Numerics modules); the comb exponents are replaced by the dense window 0..593.
Soundness glue (Lipschitz transfer, arc cover) is NOT written in this pilot. -/
namespace P3Lean

def gmul (a b : Int × Int) : Int × Int := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def Hw : Nat := 1025   -- half-width in units 2^-30
def VM : Nat := 593    -- window 594, highest exponent

/-- `bsRev` = weights beta_593, ..., beta_0.  Returns `sum_j beta_j Zc^j D^(593-j)` by Horner. -/
def hornerStep (Zc : Int × Int) (D : Int) (st : (Int × Int) × Int) (b : Nat) : (Int × Int) × Int :=
  let Dp := st.2 * D
  let P := st.1
  let m := gmul P Zc
  ((m.1 + (b : Int) * Dp, m.2), Dp)

def bval (bsRev : List Nat) (Zc : Int × Int) (D : Int) : Int × Int :=
  match bsRev with
  | [] => (0, 0)
  | b0 :: rest => (rest.foldl (hornerStep Zc D) (((b0 : Int), 0), 1)).1

/-- One zero, one vector: witness `rho >= 2^40 |B|` and the Lipschitz-transfer bound `U` (units 2^-40). -/
def checkZeroVec (bsRev : List Nat) (N rho U : Nat) : Bool :=
  let Zc : Int × Int := ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30)
  let D : Int := (N : Int) * N + 2 ^ 58
  let SA : Nat := bsRev.foldl (· + ·) 0
  let (X, Y) := bval bsRev Zc D
  let den : Int := 2 ^ 50 * D ^ VM
  let Elo : Int := ((N : Int) - Hw) ^ 2 + 2 ^ 58
  decide (2 ^ 80 * (X * X + Y * Y) ≤ ((rho : Int) * den) ^ 2) &&
  decide (2 ^ 61 * (rho : Int) * Elo + 2 ^ 81 * (SA : Int) * VM * Hw ≤ (U : Int) * Elo ^ 2)

def checkZero (ws : List (List Nat)) (r : Nat × List (Nat × Nat)) : Bool :=
  (ws.zip r.2).all fun p => checkZeroVec p.1 r.1 p.2.1 p.2.2

def checkChunk (ws : List (List Nat)) (rs : List (Nat × List (Nat × Nat))) : Bool :=
  rs.all (checkZero ws)

end P3Lean
