import P3Lean.Defs

/-!
# The robust-tail comb for general phases (paper 3, T7: no window of 534), logic only

Model: `F_x(j) = ∑_{k<K} 2 w_k cos (j θ_k + x_k)` for arbitrary phases `x`, window `j = 0, ..., L-1`.
Claim: if the comb numerics `Nbound K M w θ a (-T) v < 2 w_0 S cos (θ_0/2)` hold on a set `V` containing every
integer vector `cvec P u` (`P = 2π/θ_0`), then no `x` has `F_x(j) > T` on the whole window.
Adapted from `comb_sign` of paper 2 (`KeiperComb.Comb`), with the phase `x` in place of `n θ_k`,
one sign only (troughs of zero 1) and the window starting at `0`.  No zeta, no RH, no hypothesis beyond
the numerics `hN`.
-/

open Complex Finset

namespace P3Lean

lemma exists_phase (x : ℝ) (b : ℤ) : ∃ q : ℤ, x ≤ ((2 * q + b : ℤ) : ℝ) ∧ ((2 * q + b : ℤ) : ℝ) < x + 2 := by
  refine ⟨⌈(x - b) / 2⌉, ?_, ?_⟩
  · have h := Int.le_ceil ((x - b) / 2)
    push_cast
    linarith
  · have h := Int.ceil_lt_add_one ((x - b) / 2)
    push_cast
    linarith

lemma cos_shift' (y : ℝ) (q : ℤ) :
    Real.cos (y + ((2 * q + 1 : ℤ) : ℝ) * Real.pi) = - Real.cos y := by
  have := Real.cos_add_int_mul_two_pi (y + Real.pi) q
  have e : y + ((2 * q + 1 : ℤ) : ℝ) * Real.pi = (y + Real.pi) + (q : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [e, this, Real.cos_add_pi]

/-- `|∑ a_j cos ((N + v_j) θ + x)| ≤ |B(v)|`, for every phase `x`. -/
lemma re_bound' (a : ℕ → ℝ) (M : ℕ) (θ : ℝ) (N : ℤ) (x : ℝ) (v : ℕ → ℤ) :
    |∑ j ∈ range M, a j * Real.cos (((N + v j : ℤ) : ℝ) * θ + x)| ≤ ‖Bk a M θ v‖ := by
  have key : (∑ j ∈ range M, a j * Real.cos (((N + v j : ℤ) : ℝ) * θ + x)) =
      (Complex.exp (((N : ℝ) * θ + x : ℝ) * I) * Bk a M θ v).re := by
    unfold Bk
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Complex.exp (((N : ℝ) * θ + x : ℝ) * I) * ((a j : ℂ) * Complex.exp (((v j : ℝ) * θ : ℝ) * I))
        = (a j : ℂ) * Complex.exp ((((N + v j : ℤ) : ℝ) * θ + x : ℝ) * I) := by
      have : Complex.exp ((((N + v j : ℤ) : ℝ) * θ + x : ℝ) * I)
          = Complex.exp (((N : ℝ) * θ + x : ℝ) * I) * Complex.exp (((v j : ℝ) * θ : ℝ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [key]
  calc |(Complex.exp (((N : ℝ) * θ + x : ℝ) * I) * Bk a M θ v).re|
      ≤ ‖Complex.exp (((N : ℝ) * θ + x : ℝ) * I) * Bk a M θ v‖ := Complex.abs_re_le_norm _
    _ = ‖Bk a M θ v‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- No window of `L` consecutive `j ≥ 0` has `F_x(j) > T` throughout. -/
theorem comb_rob {K M L : ℕ} {w θ x a : ℕ → ℝ} {T : ℝ} {V : Set (ℕ → ℤ)}
    (hK : 1 ≤ K) (hw : ∀ k, k < K → 0 ≤ w k) (hw0 : 0 < w 0)
    (ha : ∀ j, j < M → 0 ≤ a j) (hS : 0 < ∑ j ∈ range M, a j)
    (hθ0 : 0 < θ 0) (hθ1 : θ 0 < Real.pi / 2)
    (hML : (M : ℝ) * (2 * Real.pi / θ 0) ≤ L)
    (hV : ∀ u ∈ Set.Ico (0 : ℝ) 1, cvec (2 * Real.pi / θ 0) u ∈ V)
    (hN : ∀ v ∈ V, Nbound K M w θ a (-T) v <
      2 * w 0 * (∑ j ∈ range M, a j) * Real.cos (θ 0 / 2)) :
    ¬ ∀ j, j < L → T < ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k) := by
  intro hwin
  set S := ∑ j ∈ range M, a j with hSdef
  set P : ℝ := 2 * Real.pi / θ 0 with hPdef
  have hπ := Real.pi_pos
  have hP : 0 < P := by positivity
  have hPθ : P * θ 0 = 2 * Real.pi := by rw [hPdef]; field_simp
  obtain ⟨q, hq1, hq2⟩ := exists_phase ((x 0 - θ 0 / 2) / Real.pi) 1
  set m : ℤ := 2 * q + 1 with hm
  set τ : ℝ := ((m : ℝ) * Real.pi - x 0) / θ 0 with hτ
  have hτθ : τ * θ 0 + x 0 = (m : ℝ) * Real.pi := by rw [hτ]; field_simp; ring
  have hτ1 : -(1 / 2 : ℝ) ≤ τ := by
    have h1 : x 0 - θ 0 / 2 ≤ (m : ℝ) * Real.pi := by
      have := mul_le_mul_of_nonneg_right hq1 hπ.le
      rwa [div_mul_cancel₀ _ hπ.ne'] at this
    rw [hτ, le_div_iff₀ hθ0]; linarith
  have hτ2 : τ < -(1 / 2 : ℝ) + P := by
    have h1 : (m : ℝ) * Real.pi < x 0 - θ 0 / 2 + 2 * Real.pi := by
      have := mul_lt_mul_of_pos_right hq2 hπ
      have e : ((x 0 - θ 0 / 2) / Real.pi + 2) * Real.pi = x 0 - θ 0 / 2 + 2 * Real.pi := by
        field_simp
      linarith
    have : τ * θ 0 < (-(1 / 2 : ℝ) + P) * θ 0 := by nlinarith
    exact lt_of_mul_lt_mul_right this hθ0.le
  set N0 : ℤ := ⌊τ⌋ with hN0
  set u : ℝ := τ - N0 with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith [Int.floor_le τ]
  have hu1 : u < 1 := by rw [hu]; linarith [Int.lt_floor_add_one τ]
  set v : ℕ → ℤ := cvec P u with hv
  have hvV : v ∈ V := hV u ⟨hu0, hu1⟩
  have hNv := hN v hvV
  have hv1 : ∀ j : ℕ, (v j : ℝ) ≤ u + j * P + 1 / 2 := fun j => Int.floor_le _
  have hv2 : ∀ j : ℕ, u + j * P + 1 / 2 < (v j : ℝ) + 1 := fun j => Int.lt_floor_add_one _
  have hge : ∀ j : ℕ, 0 ≤ N0 + v j := by
    intro j
    have h1 := hv2 j
    have hj : (0 : ℝ) ≤ j * P := by positivity
    have : (-1 : ℝ) < ((N0 + v j : ℤ) : ℝ) := by push_cast; linarith
    have : (-1 : ℤ) < N0 + v j := by exact_mod_cast this
    omega
  have hlt : ∀ j : ℕ, j < M → N0 + v j < L := by
    intro j hj
    have h1 := hv1 j
    have hjM : (j : ℝ) + 1 ≤ M := by exact_mod_cast hj
    have : (j : ℝ) * P + P ≤ M * P := by nlinarith
    have : ((N0 + v j : ℤ) : ℝ) < ((L : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  set nn : ℕ → ℕ := fun j => (N0 + v j).toNat with hnn
  have hnnZ : ∀ j, ((nn j : ℕ) : ℤ) = N0 + v j := by
    intro j; rw [hnn]; simp only; exact Int.toNat_of_nonneg (hge j)
  have hnnR : ∀ j, ((nn j : ℕ) : ℝ) = ((N0 + v j : ℤ) : ℝ) := by
    intro j; rw [← hnnZ j]; simp
  set δ : ℕ → ℝ := fun j => (v j : ℝ) - u - j * P with hδ
  have hδ1 : ∀ j, |δ j| ≤ 1 / 2 := by
    intro j; rw [abs_le]; have := hv1 j; have := hv2 j; constructor <;> simp only [hδ] <;> linarith
  have hnδ : ∀ j : ℕ, ((nn j : ℕ) : ℝ) * θ 0 + x 0
      = δ j * θ 0 + ((2 * (q + j) + 1 : ℤ) : ℝ) * Real.pi := by
    intro j
    rw [hnnR]
    have h0 : ((N0 + v j : ℤ) : ℝ) = δ j + τ + j * P := by
      simp only [hδ, hu]; push_cast; ring
    rw [h0]
    have h4 : (j : ℝ) * P * θ 0 = 2 * j * Real.pi := by rw [mul_assoc, hPθ]; ring
    have : (δ j + τ + j * P) * θ 0 + x 0 = δ j * θ 0 + (τ * θ 0 + x 0) + j * P * θ 0 := by ring
    rw [this, hτθ, h4]; push_cast [hm]; ring
  have hcos0 : ∀ j : ℕ, Real.cos (((nn j : ℕ) : ℝ) * θ 0 + x 0) = - Real.cos (δ j * θ 0) := by
    intro j
    rw [hnδ j]
    have := cos_shift' (δ j * θ 0) (q + j)
    simpa using this
  have hδcos : ∀ j : ℕ, Real.cos (θ 0 / 2) ≤ Real.cos (δ j * θ 0) := by
    intro j
    rw [← Real.cos_abs (δ j * θ 0)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
    rw [abs_mul, abs_of_pos hθ0]
    nlinarith [hδ1 j]
  -- comb sum
  set F : ℕ → ℝ := fun n => ∑ k ∈ range K, 2 * w k * Real.cos ((n : ℝ) * θ k + x k) with hF
  set G : ℝ := ∑ j ∈ range M, a j * F (nn j) with hG
  have hG1 : T * S ≤ G := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have h1 := ha j (Finset.mem_range.mp hj)
    have h2 := hwin (nn j) (by have := hlt j (Finset.mem_range.mp hj); have := hnnZ j; omega)
    have := mul_le_mul_of_nonneg_left h2.le h1
    linarith
  have hGexp : G = ∑ k ∈ range K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k)) := by
    simp only [hG, hF]
    have : ∀ j ∈ range M, a j * (∑ k ∈ range K, 2 * w k * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k))
        = ∑ k ∈ range K, 2 * w k * (a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k)) := by
      intro j _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
  have hsplit : ∑ k ∈ range K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k))
      = 2 * w 0 * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0 + x 0)) +
        ∑ k ∈ Ico 1 K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot (show 0 < K by omega)
      (fun k => 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k)))
  rw [hsplit] at hGexp
  have hA0 : ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0 + x 0)
      ≤ -(S * Real.cos (θ 0 / 2)) := by
    have : ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0 + x 0)
        = -∑ j ∈ range M, a j * Real.cos (δ j * θ 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hcos0 j]; ring
    rw [this, hSdef, Finset.sum_mul, neg_le_neg_iff]
    exact Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hδcos j) (ha j (Finset.mem_range.mp hj))
  have hrest : ∀ k ∈ Ico 1 K,
      2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k))
        ≤ 2 * w k * ‖Bk a M (θ k) v‖ := by
    intro k hk
    have hk' : k < K := (Finset.mem_Ico.mp hk).2
    apply mul_le_mul_of_nonneg_left _ (by have := hw k hk'; positivity)
    have := re_bound' a M (θ k) N0 (x k) v
    have heq : ∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k)
        = ∑ j ∈ range M, a j * Real.cos (((N0 + v j : ℤ) : ℝ) * θ k + x k) :=
      Finset.sum_congr rfl fun j _ => by rw [hnnR]
    rw [heq]; exact (le_abs_self _).trans this
  have hsumrest : ∑ k ∈ Ico 1 K, 2 * w k * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ k + x k))
      ≤ ∑ k ∈ Ico 1 K, 2 * w k * ‖Bk a M (θ k) v‖ := Finset.sum_le_sum hrest
  have hw0' : 2 * w 0 * (∑ j ∈ range M, a j * Real.cos (((nn j : ℕ) : ℝ) * θ 0 + x 0))
      ≤ 2 * w 0 * (-(S * Real.cos (θ 0 / 2))) :=
    mul_le_mul_of_nonneg_left hA0 (by positivity)
  have hNv' : -T * S + ∑ k ∈ Ico 1 K, 2 * w k * ‖Bk a M (θ k) v‖
      < 2 * w 0 * S * Real.cos (θ 0 / 2) := hNv
  nlinarith

end P3Lean
