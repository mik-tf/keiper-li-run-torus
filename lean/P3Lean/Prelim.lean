import P3Lean.Defs

/-! Small facts about the critical-line zero point, copied from paper 2 (`KeiperComb.Tail`, first part). -/

open Complex Finset ComplexConjugate

namespace P3Lean

section lemmas

lemma zpt_re (γ : ℝ) : (zpt γ).re = 1 / 2 := by simp [zpt]

lemma zpt_im (γ : ℝ) : (zpt γ).im = γ := by simp [zpt]

lemma one_sub_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : 1 - ρ = conj ρ := by
  apply Complex.ext <;> simp [h] <;> norm_num

lemma ne_zero_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : ρ ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

lemma mul_one_sub_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : ρ * (1 - ρ) = ((‖ρ‖ ^ 2 : ℝ) : ℂ) := by
  rw [one_sub_of_re h, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma norm_q_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : ‖1 - 1 / ρ‖ = 1 := by
  have h0 := ne_zero_of_re h
  have : 1 - 1 / ρ = -(conj ρ / ρ) := by
    rw [← one_sub_of_re h]; field_simp; ring
  rw [this, norm_neg, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr h0)]

lemma sq_norm_zpt (γ : ℝ) : ‖zpt γ‖ ^ 2 = 1 / 4 + γ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, zpt_re, zpt_im]; ring

lemma wOf_eq (γ : ℝ) : wOf γ = 1 / ‖zpt γ‖ ^ 2 := by
  rw [sq_norm_zpt]; rfl

lemma norm_conj_sq (ρ : ℂ) : ‖conj ρ‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [Complex.norm_conj]

/-- `1/ρ² = -w q` on the line. -/
lemma inv_sq_zpt (γ : ℝ) : 1 / (zpt γ) ^ 2 = -((wOf γ : ℝ) * qOf γ) := by
  have h0 : zpt γ ≠ 0 := ne_zero_of_re (zpt_re γ)
  have hq : qOf γ * (zpt γ) ^ 2 = -(((1 / 4 + γ ^ 2 : ℝ)) : ℂ) := by
    have := mul_one_sub_of_re (zpt_re γ)
    rw [← sq_norm_zpt γ]
    unfold qOf
    rw [← this]; field_simp; ring
  have hpos : (1 / 4 + γ ^ 2 : ℝ) ≠ 0 := by positivity
  have hw : ((wOf γ : ℝ) : ℂ) * (((1 / 4 + γ ^ 2 : ℝ)) : ℂ) = 1 := by
    unfold wOf
    have : ((1 / 4 + γ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
    push_cast at this ⊢
    field_simp
    exact div_self (fun h => this (by linear_combination h / 4))
  have hz2 : (zpt γ) ^ 2 ≠ 0 := pow_ne_zero 2 h0
  field_simp
  calc (1 : ℂ) = ((wOf γ : ℝ) : ℂ) * (((1 / 4 + γ ^ 2 : ℝ)) : ℂ) := hw.symm
    _ = _ := by rw [show (((1 / 4 + γ ^ 2 : ℝ)) : ℂ) = -(qOf γ * (zpt γ) ^ 2) by rw [hq]; ring]; ring

lemma norm_qOf (γ : ℝ) : ‖qOf γ‖ = 1 := norm_q_of_re (zpt_re γ)

lemma qOf_eq_exp (γ : ℝ) : qOf γ = Complex.exp ((thetaOf γ : ℝ) * I) := by
  have h := Complex.norm_mul_exp_arg_mul_I (qOf γ)
  rw [norm_qOf] at h
  simpa [thetaOf] using h.symm

end lemmas
end P3Lean
