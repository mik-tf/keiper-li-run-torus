import P3Lean.T4Cover

/-!
# T4, step 1 (zero 1): one arc, from a rational centre, with no arccos and no arg of the true value

`Bt = Bd β L θ_1` is the true zero-1 sum; `c` is a Gaussian rational with `‖Bt - c‖ ≤ eps` (from `lip_dense`
type bounds, rounding included); the arc centre is `z = -conj c`, with polar angle `ψ` (`z = ‖z‖ e^{iψ}`).
`zero1_good`: if `Nn ≤ 2 wlo (rho' ‖z‖ - eps)`, `rho' ≤ cos h`, `h ≤ π`, and `|y - ψ - 2π m| < h`, then
`Nn < 2 w_1 ‖Bt‖ cos (y - φ₀)` with `φ₀ = -arg Bt - π`: exactly the `harc` conclusion of `T4_glue`, with `Nn`
the displayed sum `∑_{k≥1} 2 w_k ‖B(θ_k)‖ + W S` (bounded above by the checker rows and `W ≤ 8.847e-4`).
Hypothesis free, uses only Mathlib.
-/

open Complex Finset

namespace P3Lean

noncomputable section

lemma re_conj_polar (z : ℂ) (ψ y : ℝ) (hψ : z = (‖z‖ : ℂ) * Complex.exp ((ψ : ℝ) * I)) :
    (Complex.exp ((y : ℝ) * I) * (starRingEnd ℂ) z).re = ‖z‖ * Real.cos (y - ψ) := by
  have h1 : (starRingEnd ℂ) z = (‖z‖ : ℂ) * Complex.exp ((-ψ : ℝ) * I) := by
    conv_lhs => rw [hψ]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  rw [h1]
  have : Complex.exp ((y : ℝ) * I) * ((‖z‖ : ℂ) * Complex.exp ((-ψ : ℝ) * I))
      = (‖z‖ : ℂ) * Complex.exp (((y - ψ : ℝ)) * I) := by
    have e : Complex.exp (((y - ψ : ℝ)) * I)
        = Complex.exp ((y : ℝ) * I) * Complex.exp ((-ψ : ℝ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma cos_gt_of_arc (ρ ψ y h : ℝ) (m : ℤ) (hh : h ≤ Real.pi) (hρ : ρ ≤ Real.cos h)
    (hy : |y - ψ - 2 * Real.pi * m| < h) : ρ < Real.cos (y - ψ) := by
  have e : Real.cos (y - ψ) = Real.cos (|y - ψ - 2 * Real.pi * m|) := by
    rw [Real.cos_abs]
    have := Real.cos_sub_int_mul_two_pi (y - ψ) m
    rw [← this]; congr 1; ring
  rw [e]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hh hy
  linarith

theorem zero1_good (Bt c z : ℂ) (eps w0 wlo Nn rho' ψ h y : ℝ) (m : ℤ)
    (hB : ‖Bt - c‖ ≤ eps) (hz : z = -(starRingEnd ℂ) c)
    (hψ : z = (‖z‖ : ℂ) * Complex.exp ((ψ : ℝ) * I))
    (hzp : 0 < ‖z‖) (hw : 0 < wlo) (hwl : wlo ≤ w0) (hN : 0 ≤ Nn)
    (hrho : Nn ≤ 2 * wlo * (rho' * ‖z‖ - eps))
    (hh : h ≤ Real.pi) (hcos : rho' ≤ Real.cos h) (hy : |y - ψ - 2 * Real.pi * m| < h) :
    Nn < 2 * w0 * ‖Bt‖ * Real.cos (y - (-(Bt.arg) - Real.pi)) := by
  have hc := cos_gt_of_arc rho' ψ y h m hh hcos hy
  have hre := re_conj_polar z ψ y hψ
  have hzn : 0 ≤ ‖z‖ := norm_nonneg _
  -- Re (e^{iy} Bt) >= Re (e^{iy} c) - eps
  have hdiff : |(Complex.exp ((y : ℝ) * I) * (Bt - c)).re| ≤ eps := by
    calc _ ≤ ‖Complex.exp ((y : ℝ) * I) * (Bt - c)‖ := Complex.abs_re_le_norm _
      _ = ‖Bt - c‖ := by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      _ ≤ eps := hB
  have hcz : Complex.exp ((y : ℝ) * I) * (starRingEnd ℂ) z = -(Complex.exp ((y : ℝ) * I) * c) := by
    rw [hz, map_neg, Complex.conj_conj]; ring
  have hrc : (Complex.exp ((y : ℝ) * I) * (starRingEnd ℂ) z).re = -(Complex.exp ((y : ℝ) * I) * c).re := by
    rw [hcz]; simp
  have hsplit : (Complex.exp ((y : ℝ) * I) * Bt).re
      = (Complex.exp ((y : ℝ) * I) * c).re + (Complex.exp ((y : ℝ) * I) * (Bt - c)).re := by
    rw [← Complex.add_re]; congr 1; ring
  have hX : ‖Bt‖ * Real.cos (y - (-(Bt.arg) - Real.pi)) ≥ ‖z‖ * Real.cos (y - ψ) - eps := by
    have := re_eq_neg_cos Bt y
    have h3 := (abs_le.mp hdiff).2
    linarith
  have hpos : rho' * ‖z‖ - eps < ‖z‖ * Real.cos (y - ψ) - eps := by nlinarith
  have hXpos : 0 ≤ ‖z‖ * Real.cos (y - ψ) - eps := by
    by_contra hneg
    push_neg at hneg
    have : 2 * wlo * (rho' * ‖z‖ - eps) < 0 := by nlinarith
    linarith
  calc Nn ≤ 2 * wlo * (rho' * ‖z‖ - eps) := hrho
    _ < 2 * wlo * (‖z‖ * Real.cos (y - ψ) - eps) := by nlinarith
    _ ≤ 2 * w0 * (‖z‖ * Real.cos (y - ψ) - eps) := by nlinarith
    _ ≤ 2 * w0 * (‖Bt‖ * Real.cos (y - (-(Bt.arg) - Real.pi))) := by
        have : 0 ≤ w0 := hw.le.trans hwl
        nlinarith
    _ = _ := by ring

end

end P3Lean
#print axioms P3Lean.zero1_good
