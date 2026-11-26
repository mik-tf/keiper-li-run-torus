import P3Lean.Prelim

/-!
# T4 glue, step 1: Lemma wb (paper 3, Section 5, "weighted bound")

Model: `F : ℕ → ℝ` is the window `F_x(j)`, `x` the phase vector, and the only analytic input is the displayed
bound of the paper ("Notation for the listed zeros"):
`|F_x(j) - ∑_{k<K} 2 w_k cos (j θ_k + x_k)| ≤ W` for `j < L`.  It is a HYPOTHESIS `hF` here (it comes from the
zero formula, RH and part (a) of the zero list, see paper.md); everything after it is proved from Mathlib.
Index `0` is the first zero `γ*_1` of the paper.
-/

open Complex Finset

namespace P3Lean

noncomputable section

/-- `B(θ) = ∑_{j<L} β_j e^{ijθ}`. -/
def Bd (β : ℕ → ℝ) (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ range L, (β j : ℂ) * Complex.exp (((j : ℝ) * θ : ℝ) * I)

/-- `∑_j β_j cos (j θ + y) = Re (e^{iy} B(θ))`. -/
lemma sum_cos_eq_re (β : ℕ → ℝ) (L : ℕ) (θ y : ℝ) :
    ∑ j ∈ range L, β j * Real.cos ((j : ℝ) * θ + y) =
      (Complex.exp ((y : ℝ) * I) * Bd β L θ).re := by
  unfold Bd
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Complex.exp ((y : ℝ) * I) * ((β j : ℂ) * Complex.exp (((j : ℝ) * θ : ℝ) * I))
      = (β j : ℂ) * Complex.exp ((((j : ℝ) * θ + y : ℝ)) * I) := by
    have : Complex.exp ((((j : ℝ) * θ + y : ℝ)) * I)
        = Complex.exp ((y : ℝ) * I) * Complex.exp (((j : ℝ) * θ : ℝ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma re_le_norm_Bd (β : ℕ → ℝ) (L : ℕ) (θ y : ℝ) :
    ∑ j ∈ range L, β j * Real.cos ((j : ℝ) * θ + y) ≤ ‖Bd β L θ‖ := by
  rw [sum_cos_eq_re]
  calc (Complex.exp ((y : ℝ) * I) * Bd β L θ).re
      ≤ ‖Complex.exp ((y : ℝ) * I) * Bd β L θ‖ := Complex.re_le_norm _
    _ = ‖Bd β L θ‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Lemma wb of the paper (inequality part). `H(β) = ∑_{k≥1} 2 w_k |B(θ_k)| + W S`. -/
theorem wb {K L : ℕ} {w θ x β F : ℕ → ℝ} {W : ℝ} (hK : 1 ≤ K)
    (hw : ∀ k, k < K → 0 ≤ w k) (hβ : ∀ j, j < L → 0 ≤ β j)
    (hF : ∀ j, j < L → |F j - ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k)| ≤ W) :
    ∑ j ∈ range L, β j * F j ≤
      2 * w 0 * (Complex.exp ((x 0 : ℝ) * I) * Bd β L (θ 0)).re +
      (∑ k ∈ Ico 1 K, 2 * w k * ‖Bd β L (θ k)‖ + W * ∑ j ∈ range L, β j) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have h1 : ∑ j ∈ range L, β j * F j ≤
      ∑ j ∈ range L, β j * (∑ k ∈ range (K' + 1), 2 * w k * Real.cos ((j : ℝ) * θ k + x k) + W) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have := (abs_le.mp (hF j (Finset.mem_range.mp hj))).2
    exact mul_le_mul_of_nonneg_left (by linarith) (hβ j (Finset.mem_range.mp hj))
  refine h1.trans ?_
  have h2 : ∑ j ∈ range L, β j * (∑ k ∈ range (K' + 1), 2 * w k * Real.cos ((j : ℝ) * θ k + x k) + W)
      = ∑ k ∈ range (K' + 1), 2 * w k * ∑ j ∈ range L, β j * Real.cos ((j : ℝ) * θ k + x k)
        + W * ∑ j ∈ range L, β j := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun j _ => by ring
  rw [h2, Finset.sum_range_succ', add_assoc]
  have hIco : ∑ k ∈ Ico 1 (K' + 1), 2 * w k * ‖Bd β L (θ k)‖ =
      ∑ k ∈ range K', 2 * w (k + 1) * ‖Bd β L (θ (k + 1))‖ := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun k _ => by rw [add_comm 1 k]
  rw [hIco, sum_cos_eq_re β L (θ 0) (x 0)]
  have : ∑ k ∈ range K', 2 * w (k + 1) * ∑ j ∈ range L, β j * Real.cos ((j : ℝ) * θ (k + 1) + x (k + 1))
      ≤ ∑ k ∈ range K', 2 * w (k + 1) * ‖Bd β L (θ (k + 1))‖ := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_left (re_le_norm_Bd β L _ _)
      (by have := hw (k + 1) (by have := Finset.mem_range.mp hk; omega); linarith)
  linarith

/-- `Re (e^{ix} B) = -|B| cos (x - φ₀)` with `φ₀ = -arg B - π`. -/
lemma re_eq_neg_cos (B : ℂ) (x : ℝ) :
    (Complex.exp ((x : ℝ) * I) * B).re = -(‖B‖ * Real.cos (x - (-(B.arg) - Real.pi))) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I B]
  have : Complex.exp ((x : ℝ) * I) * ((‖B‖ : ℂ) * Complex.exp ((B.arg : ℝ) * I))
      = (‖B‖ : ℂ) * Complex.exp (((x + B.arg : ℝ)) * I) := by
    have : Complex.exp (((x + B.arg : ℝ)) * I)
        = Complex.exp ((x : ℝ) * I) * Complex.exp ((B.arg : ℝ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have e : x - (-(B.arg) - Real.pi) = (x + B.arg) + Real.pi := by ring
  rw [e, Real.cos_add_pi]; ring

/-- Lemma wb, the "in particular" part: if `H(β) < 2 w_1 |B(θ_1)| cos (x_1 - φ₀)` then some `F j`, `j < L`, is
negative.  (With `ρ = H / (2 w_1 |B_1|)` this is `cos (x_1 - φ₀) > ρ`.) -/
theorem wb_neg {K L : ℕ} {w θ x β F : ℕ → ℝ} {W : ℝ} (hK : 1 ≤ K)
    (hw : ∀ k, k < K → 0 ≤ w k) (hβ : ∀ j, j < L → 0 ≤ β j)
    (hF : ∀ j, j < L → |F j - ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k)| ≤ W)
    (hρ : (∑ k ∈ Ico 1 K, 2 * w k * ‖Bd β L (θ k)‖ + W * ∑ j ∈ range L, β j) <
      2 * w 0 * ‖Bd β L (θ 0)‖ * Real.cos (x 0 - (-((Bd β L (θ 0)).arg) - Real.pi))) :
    ∃ j, j < L ∧ F j < 0 := by
  by_contra hcon
  push_neg at hcon
  have h0 : 0 ≤ ∑ j ∈ range L, β j * F j :=
    Finset.sum_nonneg fun j hj => mul_nonneg (hβ j (Finset.mem_range.mp hj)) (hcon j (Finset.mem_range.mp hj))
  have := wb hK hw hβ hF
  rw [re_eq_neg_cos] at this
  nlinarith

end
end P3Lean
