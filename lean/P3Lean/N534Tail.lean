import P3Lean.Prelim

/-! T7, the tail `T_K = Cconst - 2 ∑ w_k` bounded BELOW (the comb needs `-T_K` bounded above).

* `Cconst_ge : 0.046188 ≤ Cconst`.  A lower bound on Euler's constant is not in Mathlib at this precision
  (Mathlib has only `1/2 < γ < 2/3`).  Proved here from Mathlib's sequence definitions: `a_n = H_n - log (n + 1/2)`
  decreases to `γ` (paper 2), and `b_m = a_(m+127) - 1/(20 (m + 127.5)^2)` increases to `γ`
  (`a_n - a_(n+1) ≤ 1/20 (1/(n+1/2)^2 - 1/(n+3/2)^2)` from the log series), so `γ ≥ b_0`.  No hypothesis.
* `Wtail_ge`: `Wtail K γ ≥ 0.046188 - 2 T / 2^100`, `T = ∑ (⌊2^160 / E_k⌋ + 1)`, `E_k = (N_k - 1025)^2 + 2^58`,
  for any `γ k ≥ (N_k - 1025)/2^30`. -/

open Finset Real Filter Topology

namespace P3Lean.N534

noncomputable section

def aseq (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2)

lemma aseq_step (n : ℕ) : aseq (n + 1) ≤ aseq n := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  set x : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [hx]; apply (div_lt_one (by positivity)).2; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hxa : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hxa
  have h0 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * x ^ (2 * 0 + 1) ≤ Real.log (1 + x) - Real.log (1 - x) :=
    le_hasSum hs 0 (fun k _ => by positivity)
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, mul_one] at h0
  have e1 : (n : ℝ) + 1 + 1 / 2 = ((n : ℝ) + 1) * (1 + x) := by rw [hx]; field_simp; try ring
  have e2 : (n : ℝ) + 1 / 2 = ((n : ℝ) + 1) * (1 - x) := by rw [hx]; field_simp; try ring
  have hx1' : 0 < 1 - x := by linarith
  have l1 : Real.log ((n : ℝ) + 1 + 1 / 2) = Real.log ((n : ℝ) + 1) + Real.log (1 + x) := by
    rw [e1, Real.log_mul hn.ne' (by linarith)]
  have l2 : Real.log ((n : ℝ) + 1 / 2) = Real.log ((n : ℝ) + 1) + Real.log (1 - x) := by
    rw [e2, Real.log_mul hn.ne' hx1'.ne']
  have h2x : 2 * x = 1 / ((n : ℝ) + 1) := by rw [hx]; field_simp
  unfold aseq
  rw [harmonic_succ]
  push_cast
  have : ((n : ℝ) + 1)⁻¹ = 2 * x := by rw [h2x]; simp
  rw [this]
  have e3 : ((n : ℝ) + 1 + 1 / 2) = (n : ℝ) + 1 + 1 / 2 := rfl
  linarith


lemma aseq_tendsto : Tendsto (fun m : ℕ => aseq (m + 1)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h1 := (tendsto_add_atTop_iff_nat 1).2 Real.tendsto_harmonic_sub_log
    have h2 : Tendsto (fun m : ℕ => Real.log (1 + 1 / (2 * ((m : ℝ) + 1)))) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => 1 + 1 / (2 * ((m : ℝ) + 1))) atTop (𝓝 1) := by
        have h3 : Tendsto (fun m : ℕ => 1 / (2 * ((m : ℝ) + 1))) atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
          simp only [mul_zero] at this
          refine this.congr (fun m => ?_)
          field_simp
        simpa using h3.const_add 1
      simpa using this.log (by norm_num)
    have h4 := h1.sub h2
    simp only [sub_zero] at h4
    refine h4.congr (fun m => ?_)
    unfold aseq
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have e : (((m + 1 : ℕ) : ℝ) + 1 / 2) = ((m : ℝ) + 1) * (1 + 1 / (2 * ((m : ℝ) + 1))) := by
      push_cast; field_simp; try ring
    rw [e, Real.log_mul hm.ne' (by positivity)]
    push_cast
    ring

lemma aseq_diff_le (n : ℕ) (hn : 127 ≤ n) :
    aseq n - aseq (n + 1) ≤ (1 / 20) * (1 / ((n : ℝ) + 1 / 2) ^ 2 - 1 / ((n : ℝ) + 3 / 2) ^ 2) := by
  have hn' : (127 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm0 : (128 : ℝ) ≤ m := by rw [hm]; linarith
  have hmpos : 0 < m := by linarith
  set x : ℝ := 1 / (2 * m) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 256 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hxa : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hxb : |-x| < 1 := by rw [abs_neg]; exact hxa
  have hA := Real.abs_log_sub_add_sum_range_le hxb 3
  have hB := Real.abs_log_sub_add_sum_range_le hxa 3
  rw [abs_neg, abs_of_pos hx0] at hA
  rw [abs_of_pos hx0] at hB
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at hA hB
  norm_num at hA hB
  have hA1 := (abs_le.mp hA).2
  have hB1 := (abs_le.mp hB).1
  have hq : x ^ 4 / (1 - x) ≤ x ^ 3 / 200 := by
    rw [div_le_iff₀ (by linarith)]
    have : x ^ 4 = x ^ 3 * x := by ring
    have h3 : 0 < x ^ 3 := by positivity
    rw [this]; nlinarith
  have e1 : (n : ℝ) + 1 + 1 / 2 = m * (1 + x) := by rw [hx, hm]; field_simp; try ring
  have e2 : (n : ℝ) + 1 / 2 = m * (1 - x) := by rw [hx, hm]; field_simp; try ring
  have hx1' : 0 < 1 - x := by linarith
  have l1 : Real.log ((n : ℝ) + 1 + 1 / 2) = Real.log m + Real.log (1 + x) := by
    rw [e1, Real.log_mul hmpos.ne' (by linarith)]
  have l2 : Real.log ((n : ℝ) + 1 / 2) = Real.log m + Real.log (1 - x) := by
    rw [e2, Real.log_mul hmpos.ne' hx1'.ne']
  have h2x : 2 * x = 1 / m := by rw [hx]; field_simp
  have hstep : aseq n - aseq (n + 1) = Real.log (1 + x) - Real.log (1 - x) - 2 * x := by
    unfold aseq
    rw [harmonic_succ]
    push_cast
    have : ((n : ℝ) + 1)⁻¹ = 2 * x := by rw [h2x, ← hm]; simp
    rw [this, l1, l2]
    ring_nf
  have hx3 : x ^ 3 = 1 / (8 * m ^ 3) := by rw [hx]; field_simp; ring
  have hR : 1 / ((n : ℝ) + 1 / 2) ^ 2 - 1 / ((n : ℝ) + 3 / 2) ^ 2 ≥ 2 / m ^ 3 := by
    have a1 : (n : ℝ) + 1 / 2 = m - 1 / 2 := by rw [hm]; ring
    have a2 : (n : ℝ) + 3 / 2 = m + 1 / 2 := by rw [hm]; ring
    rw [a1, a2]
    have hp : 0 < m - 1 / 2 := by linarith
    have hp2 : 0 < m + 1 / 2 := by linarith
    have key : 1 / (m - 1 / 2) ^ 2 - 1 / (m + 1 / 2) ^ 2 = 2 * m / ((m - 1 / 2) * (m + 1 / 2)) ^ 2 := by
      rw [div_sub_div _ _ (by positivity) (by positivity), mul_pow]
      congr 1
      ring
    rw [key, ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : ((m - 1 / 2) * (m + 1 / 2)) ^ 2 ≤ m ^ 4 := by
      have e : (m - 1 / 2) * (m + 1 / 2) = m ^ 2 - 1 / 4 := by ring
      rw [e]; nlinarith [sq_nonneg m, pow_pos hmpos 2]
    have h5 : 0 < m ^ 3 := pow_pos hmpos 3
    have h6 : 2 * m ^ 3 * ((m - 1 / 2) * (m + 1 / 2)) ^ 2 ≤ 2 * m ^ 3 * m ^ 4 := by
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have h7 : 2 * m ^ 3 * m ^ 4 = 2 * m * m ^ 6 := by ring
    nlinarith [h6, h7]
  have hu : 0 < 1 / m ^ 3 := by positivity
  have hx3' : x ^ 3 = (1 / m ^ 3) / 8 := by rw [hx3]; field_simp
  have hR' : 2 * (1 / m ^ 3) ≤ 1 / ((n : ℝ) + 1 / 2) ^ 2 - 1 / ((n : ℝ) + 3 / 2) ^ 2 := by
    have : 2 / m ^ 3 = 2 * (1 / m ^ 3) := by ring
    linarith
  rw [hstep]
  linarith [hx3', hq, hA1, hB1, hR', hu]

def bseq (m : ℕ) : ℝ := aseq (m + 127) - (1 / 20) / (((m + 127 : ℕ) : ℝ) + 1 / 2) ^ 2

lemma bseq_mono : Monotone bseq := by
  refine monotone_nat_of_le_succ fun m => ?_
  have h := aseq_diff_le (m + 127) (by omega)
  have e : m + 1 + 127 = m + 127 + 1 := by omega
  unfold bseq
  rw [e]
  have c1 : (((m + 127 + 1 : ℕ) : ℝ) + 1 / 2) = ((m + 127 : ℕ) : ℝ) + 3 / 2 := by push_cast; ring
  rw [c1]
  have : (1 / 20 : ℝ) / (((m + 127 : ℕ) : ℝ) + 1 / 2) ^ 2 = (1 / 20) * (1 / (((m + 127 : ℕ) : ℝ) + 1 / 2) ^ 2) := by ring
  have h2 : (1 / 20 : ℝ) / (((m + 127 : ℕ) : ℝ) + 3 / 2) ^ 2 = (1 / 20) * (1 / (((m + 127 : ℕ) : ℝ) + 3 / 2) ^ 2) := by ring
  rw [this, h2]
  linarith

lemma bseq_tendsto : Tendsto bseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h1 : Tendsto (fun m : ℕ => aseq (m + 127)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine ((tendsto_add_atTop_iff_nat 126).2 aseq_tendsto).congr (fun m => ?_)
    rw [show m + 126 + 1 = m + 127 by omega]
  have h2 : Tendsto (fun m : ℕ => (1 / 20 : ℝ) / (((m + 127 : ℕ) : ℝ) + 1 / 2) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => by positivity) (fun m => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have hy : (m : ℝ) + 1 ≤ ((m + 127 : ℕ) : ℝ) + 1 / 2 := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hy1 : 1 ≤ ((m + 127 : ℕ) : ℝ) + 1 / 2 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hmp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ (by positivity) hmp]
    nlinarith
  have := h1.sub h2
  simp only [sub_zero] at this
  exact this

theorem gamma_ge : bseq 0 ≤ Real.eulerMascheroniConstant := bseq_mono.ge_of_tendsto bseq_tendsto 0

lemma harmonic_127_ge : (54253345925 : ℚ) / 10 ^ 10 ≤ (harmonic 127 : ℚ) := by decide +kernel

lemma log_127_5_le : Real.log (127.5) ≤ (48481164 : ℝ) / 10 ^ 7 := by
  have hx : |(1 : ℝ) / 256| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 3
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 256)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h1 := (abs_le.mp h).2
  have e : (127.5 : ℝ) = 2 ^ 7 * (1 - 1 / 256) := by norm_num
  have l2 := Real.log_two_lt_d9
  rw [e, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num at h1 l2 ⊢
  linarith

lemma log_pi4_le : Real.log (Real.pi / 4) ≤ (-2415640 : ℝ) / 10 ^ 7 := by
  have hp := Real.pi_lt_d6
  have h0 : Real.pi / 4 ≤ (0.78539825 : ℝ) := by norm_num at hp ⊢; linarith
  have hx : |(1 - 0.78539825 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 - 0.78539825)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h1 := (abs_le.mp h).2
  have h2 : Real.log (Real.pi / 4) ≤ Real.log (0.78539825) :=
    Real.log_le_log (by positivity) h0
  norm_num at h1 h2 ⊢
  linarith

lemma log_4pi_le : Real.log (4 * Real.pi) ≤ (25310248 : ℝ) / 10 ^ 7 := by
  have e : 4 * Real.pi = 2 ^ 4 * (Real.pi / 4) := by ring
  have l2 := Real.log_two_lt_d9
  have h := log_pi4_le
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  norm_num at l2 h ⊢
  linarith

/-- `C = 2 + γ_E - log 4π ≥ 0.046188`. -/
theorem Cconst_ge : (461880 : ℝ) / 10 ^ 7 ≤ Cconst := by
  have h1 := gamma_ge
  have h2 : (54253345925 : ℝ) / 10 ^ 10 ≤ (harmonic 127 : ℝ) := by
    rw [show ((54253345925 : ℝ) / 10 ^ 10) = ((54253345925 / 10 ^ 10 : ℚ) : ℝ) by push_cast; ring]
    exact_mod_cast harmonic_127_ge
  have h3 := log_127_5_le
  have h4 := log_4pi_le
  unfold bseq aseq at h1
  unfold Cconst
  norm_num at h1 h2 h3 h4 ⊢
  linarith

/-- One zero: `γ ≥ (N - 1025)/2^30` gives `wOf γ ≤ (⌊2^160 / E⌋ + 1) / 2^100`. -/
theorem w_le (N : ℕ) (hN : 1025 ≤ N) (γ : ℝ) (h : ((N : ℝ) - 1025) / 2 ^ 30 ≤ γ) :
    wOf γ ≤ ((((2 ^ 160 / ((N - 1025) ^ 2 + 2 ^ 58) : ℕ) + 1 : ℕ) : ℝ)) / 2 ^ 100 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 ^ 100 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 ^ 60 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : (2 : ℝ) ^ 160 = a * b := by rw [ha, hb, ← pow_add]
  have h30 : ((2 : ℝ) ^ 30) ^ 2 = b := by rw [hb, ← pow_mul]
  have h58 : (1 / 4 : ℝ) = 2 ^ 58 / b := by rw [hb]; norm_num
  rw [← ha]
  set E : ℕ := (N - 1025) ^ 2 + 2 ^ 58 with hE
  clear_value E
  have hEp : 0 < E := by rw [hE]; positivity
  have hq : (2 ^ 160 : ℕ) < E * (2 ^ 160 / E + 1) := Nat.lt_mul_div_succ _ hEp
  have hq' : a * b < (E : ℝ) * (((2 ^ 160 / E : ℕ) : ℝ) + 1) := by
    have h160 : ((2 ^ 160 : ℕ) : ℝ) = a * b := by rw [← hab]; norm_num
    have : ((2 ^ 160 : ℕ) : ℝ) < ((E * (2 ^ 160 / E + 1) : ℕ) : ℝ) := by exact_mod_cast hq
    have h2 : ((E * (2 ^ 160 / E + 1) : ℕ) : ℝ) = (E : ℝ) * (((2 ^ 160 / E : ℕ) : ℝ) + 1) := by
      push_cast; ring
    rw [h160, h2] at this
    exact this
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((2 ^ 160 / E : ℕ) : ℝ) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  rw [← hQ] at hq'
  have hcast : (((2 ^ 160 / E + 1 : ℕ)) : ℝ) = Q + 1 := by rw [hQ]; push_cast; ring
  rw [hcast]
  have hnn : 0 ≤ ((N : ℝ) - 1025) / 2 ^ 30 := by
    apply div_nonneg _ (by positivity)
    have : (1025 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hg2 : (((N : ℝ) - 1025) / 2 ^ 30) ^ 2 ≤ γ ^ 2 := by gcongr
  have hden : (E : ℝ) / b ≤ (1 / 4 : ℝ) + γ ^ 2 := by
    have : (E : ℝ) = ((N : ℝ) - 1025) ^ 2 + 2 ^ 58 := by
      rw [hE]; push_cast [Nat.cast_sub hN]; ring
    rw [this, add_div, ← h58]
    rw [div_pow, h30] at hg2
    linarith
  unfold wOf
  have hpos : (0 : ℝ) < 1 / 4 + γ ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos ha0]
  have h5 : a < (Q + 1) * (1 / 4 + γ ^ 2) := by
    calc a = a * b / b := by field_simp
      _ < (E : ℝ) * (Q + 1) / b := by gcongr
      _ = (Q + 1) * ((E : ℝ) / b) := by ring
      _ ≤ (Q + 1) * (1 / 4 + γ ^ 2) := mul_le_mul_of_nonneg_left hden (by linarith)
  linarith

/-- The tail bound: `Wtail K γ ≥ 0.046188 - 2 T / 2^100`, `T = ∑ (⌊2^160 / E_k⌋ + 1)`. -/
theorem Wtail_ge (K : ℕ) (γ : ℕ → ℝ) (ns : ℕ → ℕ)
    (h : ∀ k, k < K → 1025 ≤ ns k ∧ ((ns k : ℝ) - 1025) / 2 ^ 30 ≤ γ k) :
    (461880 : ℝ) / 10 ^ 7
      - 2 * ((∑ k ∈ range K, ((2 ^ 160 / ((ns k - 1025) ^ 2 + 2 ^ 58) : ℕ) + 1) : ℕ) : ℝ) / 2 ^ 100
      ≤ Wtail K γ := by
  have hs : ∑ k ∈ range K, wOf (γ k)
      ≤ ((∑ k ∈ range K, ((2 ^ 160 / ((ns k - 1025) ^ 2 + 2 ^ 58) : ℕ) + 1) : ℕ) : ℝ) / 2 ^ 100 := by
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum (fun k hk => w_le (ns k) (h k (Finset.mem_range.mp hk)).1 (γ k)
      (h k (Finset.mem_range.mp hk)).2)
  unfold Wtail
  have := Cconst_ge
  linarith

end

end P3Lean.N534
