import P3Lean.T4Wb

/-!
# T4 glue, step 3: the arc cover of the first-zero phase, and the assembly of Lemma wb with it

* `arc_cos`: `|y - φ - 2π m| < arccos ρ` gives `cos (y - φ) > ρ` (the open arc of lemma wb).
* `chain_cover`: a chain of open intervals (`a (i+1) < b i`) from below `0` to above `2π` covers `[0, 2π]`.
* `cover_all`: if every point of each interval `(a i, b i)` is good for vector `i` (`G i y`, `2π`-periodic),
  then every real phase `x` is good for some vector.  This is exactly the "48 arcs cover the circle" step; the data
  (the 48 pairs `(a i, b i)`, rational, from `vectors_c2.json` and the zero-1 ball) is an INPUT of the final
  theorem, to be discharged by the arithmetic.
* `T4_glue`: lemma wb plus the cover (plus the shift `x -> x + π` for the other sign) gives both signs in
  every window.  No `sorry`; the only hypotheses are the displayed tail bound `hF` and the arithmetic
  facts `harc` and the chain conditions.
-/

open Complex Finset

namespace P3Lean

lemma arc_cos (ρ φ y : ℝ) (m : ℤ) (h : |y - φ - 2 * Real.pi * m| < Real.arccos ρ) : ρ < Real.cos (y - φ) := by
  have e : Real.cos (y - φ) = Real.cos (|y - φ - 2 * Real.pi * m|) := by
    rw [Real.cos_abs]
    have := Real.cos_sub_int_mul_two_pi (y - φ) m
    rw [← this]; congr 1; ring
  rw [e]
  by_cases hρ : ρ < -1
  · have := Real.neg_one_le_cos |y - φ - 2 * Real.pi * m|; linarith
  · push_neg at hρ
    by_cases hρ1 : 1 < ρ
    · have : Real.arccos ρ = 0 := Real.arccos_eq_zero.mpr hρ1.le
      rw [this] at h; exact absurd h (not_lt.mpr (abs_nonneg _))
    · push_neg at hρ1
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (Real.arccos_le_pi ρ) h
      rwa [Real.cos_arccos hρ hρ1] at this

lemma chain_cover (n : ℕ) (a b : ℕ → ℝ) (hchain : ∀ i, i + 1 < n → a (i + 1) < b i) :
    ∀ m, m < n → ∀ t, a 0 < t → t < b m → ∃ i, i ≤ m ∧ a i < t ∧ t < b i := by
  intro m
  induction m with
  | zero => intro _ t h1 h2; exact ⟨0, le_rfl, h1, h2⟩
  | succ m ih =>
    intro hm t h1 h2
    by_cases ht : t < b m
    · obtain ⟨i, hi, h3, h4⟩ := ih (by omega) t h1 ht
      exact ⟨i, by omega, h3, h4⟩
    · push_neg at ht
      exact ⟨m + 1, le_rfl, lt_of_lt_of_le (hchain m hm) ht, h2⟩

/-- Every real phase is covered by some arc, if the intervals chain from below `0` to above `2π`.
`G i y` ("`y` is good for vector `i`") must be `2π`-periodic. -/
theorem cover_all (n : ℕ) (hn : 0 < n) (a b : ℕ → ℝ) (G : ℕ → ℝ → Prop)
    (harc : ∀ i, i < n → ∀ y, a i < y → y < b i → G i y)
    (hper : ∀ i y (k : ℤ), G i y → G i (y + 2 * Real.pi * k))
    (hchain : ∀ i, i + 1 < n → a (i + 1) < b i)
    (h0 : a 0 < 0) (hend : 2 * Real.pi < b (n - 1)) :
    ∀ x : ℝ, ∃ i, i < n ∧ G i x := by
  intro x
  set k : ℤ := ⌊x / (2 * Real.pi)⌋ with hk
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : (k : ℝ) ≤ x / (2 * Real.pi) := Int.floor_le _
  have h2 : x / (2 * Real.pi) < k + 1 := Int.lt_floor_add_one _
  set y : ℝ := x - 2 * Real.pi * k with hy
  have hy0 : 0 ≤ y := by
    rw [hy]; have := (le_div_iff₀ hpi).mp h1; linarith
  have hy1 : y < 2 * Real.pi := by
    rw [hy]; have := (div_lt_iff₀ hpi).mp h2; linarith
  obtain ⟨i, hi, hai, hib⟩ := chain_cover n a b hchain (n - 1) (by omega) y (by linarith) (by linarith)
  refine ⟨i, by omega, ?_⟩
  have := hper i y k (harc i (by omega) y hai hib)
  have e : y + 2 * Real.pi * k = x := by rw [hy]; ring
  rwa [e] at this

lemma cos_per (c y : ℝ) (k : ℤ) : Real.cos (y + 2 * Real.pi * k - c) = Real.cos (y - c) := by
  rw [← Real.cos_add_int_mul_two_pi (y - c) k]; congr 1; ring

/-- One sign: some window entry is negative, for every phase vector `x`. -/
theorem T4_neg {K L n : ℕ} (hK : 1 ≤ K) (hn : 0 < n) {w θ : ℕ → ℝ} {W : ℝ} (βs : ℕ → ℕ → ℝ)
    (hw : ∀ k, k < K → 0 ≤ w k) (hβ : ∀ i, i < n → ∀ j, j < L → 0 ≤ βs i j)
    (a b : ℕ → ℝ)
    (harc : ∀ i, i < n → ∀ y, a i < y → y < b i →
      (∑ k ∈ Ico 1 K, 2 * w k * ‖Bd (βs i) L (θ k)‖ + W * ∑ j ∈ range L, βs i j) <
        2 * w 0 * ‖Bd (βs i) L (θ 0)‖ * Real.cos (y - (-((Bd (βs i) L (θ 0)).arg) - Real.pi)))
    (hchain : ∀ i, i + 1 < n → a (i + 1) < b i) (h0 : a 0 < 0) (hend : 2 * Real.pi < b (n - 1))
    (x F : ℕ → ℝ)
    (hF : ∀ j, j < L → |F j - ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k)| ≤ W) :
    ∃ j, j < L ∧ F j < 0 := by
  have cov := cover_all n hn a b
    (fun i y => (∑ k ∈ Ico 1 K, 2 * w k * ‖Bd (βs i) L (θ k)‖ + W * ∑ j ∈ range L, βs i j) <
        2 * w 0 * ‖Bd (βs i) L (θ 0)‖ * Real.cos (y - (-((Bd (βs i) L (θ 0)).arg) - Real.pi)))
    harc (fun i y k hy => by simpa only [cos_per] using hy) hchain h0 hend (x 0)
  obtain ⟨i, hi, hgood⟩ := cov
  exact wb_neg hK hw (hβ i hi) hF hgood

/-- T4, glue: both signs occur in every window (the second sign by the shift `x -> x + π`, `F -> -F`;
the cover is the same, since it is a cover of the whole circle). -/
theorem T4_glue {K L n : ℕ} (hK : 1 ≤ K) (hn : 0 < n) {w θ : ℕ → ℝ} {W : ℝ} (βs : ℕ → ℕ → ℝ)
    (hw : ∀ k, k < K → 0 ≤ w k) (hβ : ∀ i, i < n → ∀ j, j < L → 0 ≤ βs i j)
    (a b : ℕ → ℝ)
    -- arithmetic input: each point of `(a i, b i)` is good for vector `i` (`rho < 1` on the arc)
    (harc : ∀ i, i < n → ∀ y, a i < y → y < b i →
      (∑ k ∈ Ico 1 K, 2 * w k * ‖Bd (βs i) L (θ k)‖ + W * ∑ j ∈ range L, βs i j) <
        2 * w 0 * ‖Bd (βs i) L (θ 0)‖ * Real.cos (y - (-((Bd (βs i) L (θ 0)).arg) - Real.pi)))
    (hchain : ∀ i, i + 1 < n → a (i + 1) < b i) (h0 : a 0 < 0) (hend : 2 * Real.pi < b (n - 1))
    (x F : ℕ → ℝ)
    (hF : ∀ j, j < L → |F j - ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k)| ≤ W) :
    (∃ j, j < L ∧ F j < 0) ∧ (∃ j, j < L ∧ 0 < F j) := by
  refine ⟨T4_neg hK hn βs hw hβ a b harc hchain h0 hend x F hF, ?_⟩
  have hF' : ∀ j, j < L → |(-F) j - ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + (x k + Real.pi))| ≤ W := by
    intro j hj
    have := hF j hj
    have e : ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + (x k + Real.pi))
        = -∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← add_assoc, Real.cos_add_pi]; ring
    rw [e, Pi.neg_apply, show -F j - -∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k)
      = -(F j - ∑ k ∈ range K, 2 * w k * Real.cos ((j : ℝ) * θ k + x k)) by ring, abs_neg]
    exact this
  obtain ⟨j, hj, hneg⟩ := T4_neg hK hn βs hw hβ a b harc hchain h0 hend (fun k => x k + Real.pi) (-F) hF'
  exact ⟨j, hj, by simpa using hneg⟩

end P3Lean
