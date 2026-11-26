import P3Lean.Core
import P3Lean.T4Lip

/-!
# T4 glue, step 4: the Horner evaluation of `Core.lean` computes `B(q(N/2^30))`

`checkZeroVec bs N rho U = true` (with `bs` = the reversed weight list, `beta_593` first) implies the two grid
hypotheses `hgrid` and `h2` of `transfer_dense`; so one checker row bounds `2 w(γ) ‖B(γ)‖` on the whole zero interval.
No hypothesis beyond `Hw ≤ N`.
-/

open Complex Finset

namespace P3Lean

def gcc (z : Int × Int) : ℂ := ⟨z.1, z.2⟩

lemma gcc_eq (a b : Int) : gcc (a, b) = (a : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [gcc]

lemma gcc_mul (a b : Int × Int) : gcc (gmul a b) = gcc a * gcc b := by
  apply Complex.ext <;> simp [gcc, gmul] <;> ring

lemma step_gcc (Zc : Int × Int) (D : Int) (st : (Int × Int) × Int) (b : Nat) :
    gcc (hornerStep Zc D st b).1 = gcc st.1 * gcc Zc + (b : ℂ) * ((st.2 * D : Int) : ℂ) := by
  apply Complex.ext <;> simp [hornerStep, gcc, gmul] <;> ring

lemma step_snd (Zc : Int × Int) (D : Int) (st : (Int × Int) × Int) (b : Nat) :
    (hornerStep Zc D st b).2 = st.2 * D := rfl

lemma horner_closed (Zc : Int × Int) (D : Int) (b0 : Nat) (rest : List Nat) :
    gcc (rest.foldl (hornerStep Zc D) (((b0 : Int), 0), 1)).1
        = ∑ i ∈ range (rest.length + 1), (((b0 :: rest).getD i 0 : Nat) : ℂ) * (gcc Zc) ^ (rest.length - i) * (D : ℂ) ^ i
      ∧ (rest.foldl (hornerStep Zc D) (((b0 : Int), 0), 1)).2 = D ^ rest.length := by
  induction rest using List.reverseRecOn with
  | nil => simp [gcc]; apply Complex.ext <;> simp
  | append_singleton l x ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, step_gcc, step_snd, ih1, ih2]
    refine ⟨?_, by simp [pow_succ]⟩
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ _ (l.length + 1), Finset.sum_mul]
    have hx : ((b0 :: (l ++ [x])).getD (l.length + 1) 0) = x := by simp
    have hy : ∀ i ∈ range (l.length + 1), (b0 :: (l ++ [x])).getD i 0 = (b0 :: l).getD i 0 := by
      intro i hi
      have := Finset.mem_range.mp hi
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.getD_cons_succ]
        rw [List.getD_append _ _ _ _ (by simpa using this)]
    rw [hx]
    have : ∀ i ∈ range (l.length + 1), (((b0 :: (l ++ [x])).getD i 0 : Nat) : ℂ) * gcc Zc ^ (l.length + 1 - i) * (D : ℂ) ^ i
        = (((b0 :: l).getD i 0 : Nat) : ℂ) * gcc Zc ^ (l.length - i) * (D : ℂ) ^ i * gcc Zc := by
      intro i hi
      rw [hy i hi, show l.length + 1 - i = (l.length - i) + 1 by have := Finset.mem_range.mp hi; omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    simp only [Nat.sub_self, pow_zero, mul_one]
    push_cast
    ring

set_option maxRecDepth 100000 in
lemma qOf_grid (N : ℕ) :
    qOf ((N : ℝ) / 2 ^ 30) = gcc ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30) / (((N : Int) * N + 2 ^ 58 : Int) : ℂ) := by
  have hz : zpt ((N : ℝ) / 2 ^ 30) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [zpt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.zero_re] at this
    norm_num at this
  have hDc : (((N : Int) * N + 2 ^ 58 : Int) : ℂ) = (N : ℂ) * N + 2 ^ 58 := by push_cast; ring
  have hD : (((N : Int) * N + 2 ^ 58 : Int) : ℂ) ≠ 0 := by
    apply Int.cast_ne_zero.mpr
    have : (0 : ℤ) < (N : Int) * N + 2 ^ 58 := by positivity
    exact this.ne'
  have hg : gcc ((N : Int) * N - 2 ^ 58, (N : Int) * 2 ^ 30) = ((N : ℂ) * N - 2 ^ 58) + ((N : ℂ) * 2 ^ 30) * Complex.I := by
    rw [gcc_eq]; push_cast; ring
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have key : (zpt ((N : ℝ) / 2 ^ 30) - 1) * ((N : ℂ) * N + 2 ^ 58)
      = zpt ((N : ℝ) / 2 ^ 30) * (((N : ℂ) * N - 2 ^ 58) + ((N : ℂ) * 2 ^ 30) * Complex.I) := by
    unfold zpt; push_cast
    linear_combination (-((N : ℂ) ^ 2)) * hI
  rw [eq_div_iff hD, hg, hDc]
  unfold qOf
  have e : (1 - 1 / zpt ((N : ℝ) / 2 ^ 30)) = (zpt ((N : ℝ) / 2 ^ 30) - 1) / zpt ((N : ℝ) / 2 ^ 30) := by
    field_simp
  rw [e, div_mul_eq_mul_div, div_eq_iff hz, key]
  exact mul_comm _ _

lemma foldl_sum (bs : List Nat) : bs.foldl (· + ·) 0 = ∑ i ∈ range bs.length, bs.getD i 0 := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.foldl_append, ih, List.length_append, List.length_singleton, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    have : ∀ i ∈ range l.length, (l ++ [x]).getD i 0 = l.getD i 0 := fun i hi => by
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
    rw [Finset.sum_congr rfl this]
    simp

lemma norm_le_aux (z : ℂ) (X P r : ℝ) (hP : 0 < P) (hr : 0 ≤ r) (hsq : ‖z‖ ^ 2 = X)
    (h : 2 ^ 80 * X ≤ (r * P) ^ 2) : ‖z‖ ≤ r / 2 ^ 40 * P := by
  have h1 : ‖z‖ ^ 2 ≤ (r / 2 ^ 40 * P) ^ 2 := by
    have e : (r / 2 ^ 40 * P) ^ 2 = (r * P) ^ 2 / 2 ^ 80 := by ring
    rw [hsq, e, le_div_iff₀ (by norm_num)]
    linarith
  exact (abs_le_of_sq_le_sq' h1 (by positivity)).2

set_option maxRecDepth 100000 in
/-- The checker row is sound for the whole zero interval: one `checkZeroVec` bounds `2 w(γ) ‖B(γ)‖`. -/
theorem row_sound (bs : List Nat) (hlen : bs.length = 594) (N rho U : Nat) (hN : 1025 ≤ N)
    (h : checkZeroVec bs N rho U = true) (γ : ℝ)
    (hγ1 : (((N : ℝ) - 1025) / 2 ^ 30) ≤ γ) (hγ2 : γ ≤ (((N : ℝ) + 1025) / 2 ^ 30)) :
    2 * wOf γ * ‖∑ j ∈ range 594, ((((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf γ) ^ j‖
      ≤ (U : ℝ) / 2 ^ 40 := by
  obtain ⟨b0, rest, hbs⟩ : ∃ b0 rest, bs = b0 :: rest := by
    cases bs with
    | nil => simp at hlen
    | cons b r => exact ⟨b, r, rfl⟩
  have hrl : rest.length = 593 := by simpa [hbs] using hlen
  have hh := h
  unfold checkZeroVec at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨h1, h2⟩ := hh
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
  have hnorm : ‖∑ j ∈ range 594, ((((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf ((N : ℝ) / 2 ^ 30)) ^ j‖
      ≤ (rho : ℝ) / 2 ^ 40 := by
    have e : ∑ j ∈ range 594, ((((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (qOf ((N : ℝ) / 2 ^ 30)) ^ j
        = gcc XY / ((2 ^ 50 * D ^ 593 : Int) : ℂ) := by
      rw [hq]
      have : ∀ j ∈ range 594, ((((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) : ℂ) * (gcc Zc / D) ^ j
          = (((bs.getD (593 - j) 0 : ℕ) : ℂ) * (gcc Zc / D) ^ j) / 2 ^ 50 := fun j _ => by push_cast; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, hrefl]
      push_cast
      field_simp <;> norm_num
    rw [e, norm_div]
    have hden : (0 : ℝ) < ((2 ^ 50 * D ^ 593 : Int) : ℝ) := by push_cast; positivity
    have hcast : ((2 ^ 50 * D ^ 593 : Int) : ℂ) = (((2 ^ 50 * D ^ 593 : Int) : ℝ) : ℂ) := by push_cast; rfl
    have hnc : ‖((((2 ^ 50 * D ^ 593 : Int) : ℝ)) : ℂ)‖ = ((2 ^ 50 * D ^ 593 : Int) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
    rw [hcast, hnc, div_le_iff₀ hden]
    have hsq : ‖gcc XY‖ ^ 2 = ((XY.1 * XY.1 + XY.2 * XY.2 : Int) : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [gcc]
    have h1' : (2 : ℝ) ^ 80 * ((XY.1 * XY.1 + XY.2 * XY.2 : Int) : ℝ)
        ≤ ((rho : ℝ) * ((2 ^ 50 * D ^ 593 : Int) : ℝ)) ^ 2 := by exact_mod_cast h1
    have := norm_le_aux (gcc XY) _ ((2 ^ 50 * D ^ 593 : Int) : ℝ) (rho : ℝ) hden (Nat.cast_nonneg _) hsq h1'
    calc ‖gcc XY‖ ≤ _ := this
      _ = (rho : ℝ) / 2 ^ 40 * ((2 ^ 50 * D ^ 593 : Int) : ℝ) := by ring
  have hSA : ((bs.foldl (· + ·) 0 : Nat) : ℝ)
      = 2 ^ 50 * ∑ j ∈ range 594, (((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50 : ℝ) := by
    rw [foldl_sum, hlen, ← Finset.sum_range_reflect _ 594]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have e1 : 594 - 1 - j = 593 - j := by omega
    rw [e1]; ring
  have h2r : 2 ^ 61 * (rho : ℝ) * (((N : ℝ) - 1025) ^ 2 + 2 ^ 58)
      + 2 ^ 81 * ((bs.foldl (· + ·) 0 : Nat) : ℝ) * ((594 - 1 : ℕ) : ℝ) * 1025
      ≤ (U : ℝ) * (((N : ℝ) - 1025) ^ 2 + 2 ^ 58) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).2 h2
    simp only [Hw, VM] at this
    push_cast at this
    have e : ((594 - 1 : ℕ) : ℝ) = 593 := by norm_num
    rw [e]
    linarith
  exact transfer_dense (fun j => ((bs.getD (593 - j) 0 : ℕ) : ℝ) / 2 ^ 50) 594
    (fun j => by positivity) N 1025 hN rho U _ hSA hnorm h2r γ hγ1 hγ2

end P3Lean
