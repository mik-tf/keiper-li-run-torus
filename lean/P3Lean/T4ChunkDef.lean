import P3Lean.T4Harc

/-!
# T4, step 3: definitions shared by the chunk modules `T4C00` to `T4C19`

A chunk holds the grid ordinates `ns` of its zeros (`Ns k = round (gamma_k 2^30)`, the zero lies in
`[(Ns k - 1025)/2^30, (Ns k + 1025)/2^30]` by the `ZeroIntervals` hypothesis), and, per zero and chain
position `i < 22`, the witnesses `rhoL` and the Lipschitz-transfer bounds `uL` (units `2^-40`).
-/

namespace P3Lean

/-- every zero of the list, chain position `i`: the checker `checkZeroVec` accepts the witnesses -/
abbrev GoodC (i : ℕ) (ns : List ℕ) (rhoL uL : List (List ℕ)) : Prop :=
  ∀ idx, idx < ns.length →
    checkZeroVec (bsv i) (ns.getD idx 0) ((rhoL.getD idx []).getD i 0) ((uL.getD idx []).getD i 0) = true

/-- the sum over the zeros of the chunk of `U i` -/
def sumU (i : ℕ) (uL : List (List ℕ)) : ℕ := (uL.map (fun r => r.getD i 0)).sum

end P3Lean
