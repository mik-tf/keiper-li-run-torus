import P3Lean.N534Real
import P3Lean.T4Wb

/-!
# T4 glue, step 2: the Lipschitz transfer from a grid point to a whole zero interval (dense window)

* `Bd_eq_qpow`: `B(θ(γ)) = ∑ β_j q(γ)^j` (the exponential form of lemma wb is the power form of the checker).
* `lip_dense`: `‖∑ β_j q(g)^j‖ ≤ r + S (L-1) δ/P` from the grid bound at `m`, from paper 2's `Bnorm_bound`
  (`norm_qOf_sub_le`, Lipschitz of `q`, in `P3Lean.N534Real`) with exponents `v j = j`, `vm = L-1`.
* `transfer_dense`: the shape of one T4 check (`checkZeroVec` of `Core.lean`): from the integer facts
  `‖B(q(N/2^30))‖ ≤ rho/2^40` and `2^61 rho E + 2^81 SA (L-1) Hw ≤ U E^2` it follows that
  `2 w(γ) ‖B(γ)‖ ≤ U/2^40` for EVERY `γ` in `[(N-Hw)/2^30, (N+Hw)/2^30]`.
No hypothesis; the Horner evaluation that produces `rho` is a separate soundness step (`Core.lean`).
-/

open Complex Finset

namespace P3Lean

noncomputable section

lemma Bd_eq_qpow (β : ℕ → ℝ) (L : ℕ) (γ : ℝ) :
    Bd β L (thetaOf γ) = ∑ j ∈ range L, (β j : ℂ) * (qOf γ) ^ j := by
  unfold Bd
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qOf_eq_exp, ← Complex.exp_nat_mul]
  congr 2
  push_cast; ring

lemma lip_dense (β : ℕ → ℝ) (L : ℕ) (hβ : ∀ j, 0 ≤ β j) (g m r P δ : ℝ)
    (hB : ‖∑ j ∈ range L, (β j : ℂ) * (qOf m) ^ j‖ ≤ r)
    (hP : 0 < P) (hPle : P ≤ ‖zpt g‖ * ‖zpt m‖) (hδ : |g - m| ≤ δ) :
    ‖∑ j ∈ range L, (β j : ℂ) * (qOf g) ^ j‖ ≤ r + (∑ j ∈ range L, β j) * ((L - 1 : ℕ) : ℝ) * (δ / P) :=
  Bnorm_bound β L (fun j => j) g m r P δ (L - 1) hβ hB hP hPle hδ (fun j hj => by
    have := Finset.mem_range.mp (Finset.mem_range.mpr hj); omega)

/-- One T4 check is sound for the whole zero interval.  `a = β / 2^50` (weights), `SA = 2^50 ∑ a`
(an integer in the checker), `E = (N - Hw)^2 + 2^58`. -/
theorem transfer_dense (a : ℕ → ℝ) (L : ℕ) (ha : ∀ j, 0 ≤ a j) (N Hw : ℕ) (hN : Hw ≤ N)
    (rho U : ℝ) (SA : ℝ) (hSA : SA = 2 ^ 50 * ∑ j ∈ range L, a j)
    (hgrid : ‖∑ j ∈ range L, (a j : ℂ) * (qOf ((N : ℝ) / 2 ^ 30)) ^ j‖ ≤ rho / 2 ^ 40)
    (h2 : 2 ^ 61 * rho * (((N : ℝ) - Hw) ^ 2 + 2 ^ 58) + 2 ^ 81 * SA * ((L - 1 : ℕ) : ℝ) * Hw
      ≤ U * (((N : ℝ) - Hw) ^ 2 + 2 ^ 58) ^ 2)
    (γ : ℝ) (hγ1 : ((N : ℝ) - Hw) / 2 ^ 30 ≤ γ) (hγ2 : γ ≤ ((N : ℝ) + Hw) / 2 ^ 30) :
    2 * wOf γ * ‖∑ j ∈ range L, (a j : ℂ) * (qOf γ) ^ j‖ ≤ U / 2 ^ 40 := by
  set E : ℝ := ((N : ℝ) - Hw) ^ 2 + 2 ^ 58 with hE
  have hE0 : (0 : ℝ) < E := by rw [hE]; positivity
  have hNH : (Hw : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : (0 : ℝ) ≤ Hw := Nat.cast_nonneg _
  set m : ℝ := (N : ℝ) / 2 ^ 30 with hm
  set g0 : ℝ := ((N : ℝ) - Hw) / 2 ^ 30 with hg0
  have hg0nn : 0 ≤ g0 := by rw [hg0]; exact div_nonneg (sub_nonneg.2 hNH) (by positivity)
  have hmg : g0 ≤ m := by rw [hg0, hm]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hEg : E / 2 ^ 60 = 1 / 4 + g0 ^ 2 := by rw [hE, hg0]; field_simp; ring
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = E / 2 ^ 60 := ⟨_, rfl⟩
  have hPe : P = 1 / 4 + g0 ^ 2 := hPd.trans hEg
  have hzs : ∀ x : ℝ, g0 ≤ x → P ≤ ‖zpt x‖ ^ 2 := by
    intro x hx
    rw [sq_norm_zpt, hPe]
    have := pow_le_pow_left₀ hg0nn hx 2
    linarith
  have hP : (0 : ℝ) < P := by rw [hPe]; positivity
  have hPle : P ≤ ‖zpt γ‖ * ‖zpt m‖ := by
    have h1 := hzs γ hγ1
    have h2' := hzs m hmg
    have : P ^ 2 ≤ (‖zpt γ‖ * ‖zpt m‖) ^ 2 := by
      rw [mul_pow, sq]
      exact mul_le_mul h1 h2' hP.le (le_trans hP.le h1)
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  have hδ : |γ - m| ≤ (Hw : ℝ) / 2 ^ 30 := by
    have e1 : g0 = m - (Hw : ℝ) / 2 ^ 30 := by rw [hg0, hm]; ring
    have e2 : ((N : ℝ) + Hw) / 2 ^ 30 = m + (Hw : ℝ) / 2 ^ 30 := by rw [hm]; ring
    rw [abs_le]; constructor <;> linarith
  have hBn := lip_dense a L ha γ m (rho / 2 ^ 40) P ((Hw : ℝ) / 2 ^ 30) hgrid hP hPle hδ
  have hw : wOf γ ≤ 2 ^ 60 / E := by
    rw [wOf_eq]
    have := one_div_le_one_div_of_le hP (hzs γ hγ1)
    calc 1 / ‖zpt γ‖ ^ 2 ≤ 1 / P := this
      _ = 2 ^ 60 / E := by rw [hPd, one_div_div]
  have hw0 : 0 ≤ wOf γ := by unfold wOf; positivity
  have hS : (∑ j ∈ range L, a j) = SA / 2 ^ 50 := by rw [hSA]; field_simp
  rw [hS] at hBn
  calc 2 * wOf γ * ‖∑ j ∈ range L, (a j : ℂ) * (qOf γ) ^ j‖
      ≤ 2 * (2 ^ 60 / E) * (rho / 2 ^ 40 + (SA / 2 ^ 50) * ((L - 1 : ℕ) : ℝ) *
          (((Hw : ℝ) / 2 ^ 30) / P)) := by
        apply mul_le_mul (by linarith) hBn (norm_nonneg _) (by positivity)
    _ = (2 ^ 61 * rho * E + 2 ^ 81 * SA * ((L - 1 : ℕ) : ℝ) * Hw) / (2 ^ 40 * E ^ 2) := by
        rw [hPd]; field_simp
    _ ≤ U / 2 ^ 40 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 ^ 40)
        nlinarith

end
end P3Lean
