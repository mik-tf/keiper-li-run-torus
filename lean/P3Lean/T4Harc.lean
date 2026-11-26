import P3Lean.T4Zero1Arc
import P3Lean.T4Horner
import P3Lean.Weights

/-!
# T4, step 2a: the rational facts and the grid lemmas for the harc discharge

Chain vectors `bsv i` (`i < 22`; `weightsRev` entries `chainIdx`), Horner value `hv i` at the zero-1 midpoint `N0`,
and the kernel-checked facts (all in `ℚ`/`ℤ`): `linkOK` (`hv i / den` is within `3/2^60` of `-conj z_i`),
`smallOK` (`eps_i`, `Nn_i`, `rho'_i`, `utotL`), `paramOK` (`wlo`, `Pz` from `N0`).
Generic lemmas: `lip_diff` (Lipschitz of the difference), `sum_grid` (Horner closed form at a grid point),
`gcc_div_sub_le`, `sum_betaR`.  `T4Chain.lean` assembles `T4_chain`.
-/

open Complex Finset

namespace P3Lean

noncomputable section

open Z1

/-- reversed weights of chain position `i` -/
def bsv (i : ℕ) : List ℕ := weightsRev.getD (chainIdx.getD i 0) []

def betaR (i j : ℕ) : ℝ := (((bsv i).getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50

/-- the sum of the weights of position `i`, as a rational -/
def sS (i : ℕ) : ℚ := (((bsv i).foldl (· + ·) 0 : ℕ) : ℚ) / 2 ^ 50

/-- Horner value of `bsv i` at the zero-1 midpoint `N0` -/
def hv (i : ℕ) : (ℤ × ℤ) :=
  bval (bsv i) ((N0 : Int) * N0 - 2 ^ 58, (N0 : Int) * 2 ^ 30) ((N0 : Int) * N0 + 2 ^ 58)

abbrev linkOK (i : ℕ) : Prop :=
  (bsv i).length = 594 ∧
  ((((hv i).1 : ℤ) : ℚ) - (-zr i) * (((2 ^ 50 * ((N0 : Int) * N0 + 2 ^ 58) ^ 593 : Int)) : ℚ)) ^ 2
    + ((((hv i).2 : ℤ) : ℚ) - zi i * (((2 ^ 50 * ((N0 : Int) * N0 + 2 ^ 58) ^ 593 : Int)) : ℚ)) ^ 2
  ≤ ((3 / 2 ^ 60 : ℚ) * (((2 ^ 50 * ((N0 : Int) * N0 + 2 ^ 58) ^ 593 : Int)) : ℚ)) ^ 2

abbrev smallOK (i : ℕ) : Prop :=
  sS i * 593 * ((1025 / 2 ^ 30 : ℚ) / Pz) + 3 / 2 ^ 60 ≤ epsL.getD i 0 ∧
  (utotL.getD i 0 : ℚ) / 2 ^ 40 + 8847 / 10 ^ 7 * sS i ≤ nnL.getD i 0 ∧
  0 ≤ nnL.getD i 0 ∧ 0 ≤ rq i ∧
  (nnL.getD i 0 / (2 * wlo) + epsL.getD i 0) ^ 2 ≤ (rq i) ^ 2 * (zr i ^ 2 + zi i ^ 2)

abbrev paramOK : Prop :=
  0 < wlo ∧ wlo = 1 / (1 / 4 + ((N0 : ℚ) + 1025) ^ 2 / 2 ^ 60) ∧
  Pz = 1 / 4 + ((N0 : ℚ) - 1025) ^ 2 / 2 ^ 60 ∧ 1025 ≤ N0

theorem smallOK_true : ∀ i, i < 22 → smallOK i := by decide +kernel
theorem paramOK_true : paramOK := by decide +kernel
theorem linkOK_true : ∀ i, i < 22 → linkOK i := by decide +kernel

/-! ### Lipschitz difference -/

lemma lip_diff (β : ℕ → ℝ) (L : ℕ) (hβ : ∀ j, 0 ≤ β j) (g m P δ : ℝ)
    (hP : 0 < P) (hPle : P ≤ ‖zpt g‖ * ‖zpt m‖) (hδ : |g - m| ≤ δ) :
    ‖∑ j ∈ range L, (β j : ℂ) * (qOf g) ^ j - ∑ j ∈ range L, (β j : ℂ) * (qOf m) ^ j‖
      ≤ (∑ j ∈ range L, β j) * ((L - 1 : ℕ) : ℝ) * (δ / P) := by
  have hq := norm_qOf_sub_le g m P hP hPle
  have hqd : |g - m| / P ≤ δ / P := div_le_div_of_nonneg_right hδ hP.le
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ range L, ‖(β j : ℂ) * (qOf g) ^ j - (β j : ℂ) * (qOf m) ^ j‖
      ≤ β j * ((L - 1 : ℕ) : ℝ) * (δ / P) := by
    intro j hj
    have hj' : j ≤ L - 1 := by have := Finset.mem_range.mp hj; omega
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ j)]
    have h1 := norm_pow_sub_pow_le (a := qOf g) (b := qOf m) (le_of_eq (norm_qOf g))
      (le_of_eq (norm_qOf m)) j
    have hvj : (j : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast hj'
    have h4 : (j : ℝ) * ‖qOf g - qOf m‖ ≤ ((L - 1 : ℕ) : ℝ) * (δ / P) :=
      mul_le_mul hvj (hq.trans hqd) (norm_nonneg _) (Nat.cast_nonneg _)
    have h5 := mul_le_mul_of_nonneg_left (h1.trans h4) (hβ j)
    linarith
  calc _ ≤ ∑ j ∈ range L, ‖(β j : ℂ) * (qOf g) ^ j - (β j : ℂ) * (qOf m) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range L, β j * ((L - 1 : ℕ) : ℝ) * (δ / P) := Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

/-! ### the Horner sum at a grid point, and its closeness to a rational centre -/

set_option maxRecDepth 100000 in
lemma sum_grid (bs : List ℕ) (hlen : bs.length = 594) (N : ℕ) :
    ∑ j ∈ range 594, ((((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf ((N : ℝ) / 2 ^ 30)) ^ j
      = gcc (bval bs ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30) ((N : Int) * N + 2 ^ 58))
          / ((2 ^ 50 * ((N : Int) * N + 2 ^ 58) ^ 593 : Int) : ℂ) := by
  obtain ⟨b0, rest, hbs⟩ : ∃ b0 rest, bs = b0 :: rest := by
    cases bs with
    | nil => simp at hlen
    | cons b r => exact ⟨b, r, rfl⟩
  have hrl : rest.length = 593 := by simpa [hbs] using hlen
  have hcl := (horner_closed ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30) ((N : Int) * N + 2 ^ 58) b0 rest).1
  rw [hrl] at hcl
  set Zc : Int × Int := ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30) with hZc
  set D : Int := (N : Int) * N + 2 ^ 58 with hD
  have hDpos : (0 : ℝ) < D := by rw [hD]; push_cast; positivity
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hXY : bval bs Zc D = (rest.foldl (hornerStep Zc D) (((b0 : Int), 0), 1)).1 := by rw [hbs]; rfl
  set XY := bval bs Zc D with hXYd
  have hrefl : ∑ j ∈ range 594, ((bs.getD (593 - j) 0 : ℕ) : ℂ) * (gcc Zc / D) ^ j
      = gcc XY / (D : ℂ) ^ 593 := by
    rw [hXY, hcl, eq_div_iff (pow_ne_zero _ hD0), Finset.sum_mul]
    rw [show (593 + 1 : ℕ) = 594 from rfl, ← Finset.sum_range_reflect _ 594]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have e1 : 594 - 1 - j = 593 - j := by omega
    have e2 : 593 - (593 - j) = j := by omega
    rw [e1, e2, hbs, div_pow]
    have e4 : (D : ℂ) ^ 593 = (D : ℂ) ^ j * (D : ℂ) ^ (593 - j) := by rw [← pow_add]; congr 1; omega
    rw [e4]
    have e5 : (D : ℂ) ^ j ≠ 0 := pow_ne_zero _ hD0
    field_simp
  have hq := qOf_grid N
  rw [← hZc, ← hD] at hq
  rw [hq]
  have : ∀ j ∈ range 594, ((((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (gcc Zc / D) ^ j
      = (((bs.getD (593 - j) 0 : ℕ) : ℂ) * (gcc Zc / D) ^ j) / 2 ^ 50 := fun j _ => by push_cast; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_div, hrefl]
  push_cast
  field_simp <;> norm_num

lemma gcc_div_sub_le (X Y den : ℤ) (cr ci r : ℚ) (hden : 0 < den) (hr : 0 ≤ r)
    (h : ((X : ℚ) - cr * den) ^ 2 + ((Y : ℚ) - ci * den) ^ 2 ≤ (r * den) ^ 2) :
    ‖gcc (X, Y) / (den : ℂ) - ⟨(cr : ℝ), (ci : ℝ)⟩‖ ≤ r := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have hh : ((X : ℝ) - cr * den) ^ 2 + ((Y : ℝ) - ci * den) ^ 2 ≤ (r * den) ^ 2 := by exact_mod_cast h
  have hd0 : (den : ℂ) ≠ 0 := by exact_mod_cast hdR.ne'
  set w : ℂ := gcc (X, Y) - (den : ℂ) * ⟨(cr : ℝ), (ci : ℝ)⟩ with hw
  have hre : w.re = (X : ℝ) - cr * den := by simp [hw, gcc]; ring
  have him : w.im = (Y : ℝ) - ci * den := by simp [hw, gcc]; ring
  have hsq : ‖w‖ ^ 2 = ((X : ℝ) - cr * den) ^ 2 + ((Y : ℝ) - ci * den) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  have hwn : ‖w‖ ≤ r * den := by
    have : ‖w‖ ^ 2 ≤ (r * den) ^ 2 := by rw [hsq]; exact hh
    have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  have e : gcc (X, Y) / (den : ℂ) - ⟨(cr : ℝ), (ci : ℝ)⟩ = w / (den : ℂ) := by
    rw [hw]; field_simp
  rw [e, norm_div]
  have hdn : ‖(den : ℂ)‖ = den := by
    rw [show (den : ℂ) = ((den : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdR]
  rw [hdn, div_le_iff₀ hdR]
  exact hwn

lemma sum_betaR (bs : List ℕ) (hlen : bs.length = 594) :
    ((bs.foldl (· + ·) 0 : Nat) : ℝ)
      = 2 ^ 50 * ∑ j ∈ range 594, (((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) := by
  rw [foldl_sum, hlen, ← Finset.sum_range_reflect _ 594]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e1 : 594 - 1 - j = 593 - j := by have := Finset.mem_range.mp hj; omega
  rw [e1]; ring

end

end P3Lean
#print axioms P3Lean.linkOK_true
#print axioms P3Lean.smallOK_true
#print axioms P3Lean.paramOK_true
#print axioms P3Lean.sum_grid
#print axioms P3Lean.lip_diff
