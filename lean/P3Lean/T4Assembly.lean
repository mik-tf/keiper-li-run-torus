import P3Lean.T4Chunks
import P3Lean.T4Wup

/-!
# T4, final assembly: no window of 594 in the torus problem at `K = 2000` (paper 3, Theorem T4)

Statement (`T4`): for ordinates `γ_k` in the 2000 certified zero intervals (grid `Lw k`, half-width `1025/2^30`),
every window `F : ℕ → ℝ` that satisfies the paper's displayed tail bound at the phase vector `x`

  `hF : ∀ j < 594, |F j - ∑_{k<2000} 2 w_k cos (j θ_k + x_k)| ≤ W`,   `W = Wtail 2000 γ = C - 2 ∑ w_k`,

takes a strictly negative and a strictly positive value among `F 0, ..., F 593`.  With `F j = c_{n_0+j}`
and `x_k = n_0 θ_k` this is the paper's T4; there are two hypotheses, `hγ` (the boxes, part (a) of the zero list)
and `hF` (the tail bound; it is where RH and the zero formula enter).  Everything else is proved here: lemma wb (`T4Wb`), the cover by the 22 arcs
(`T4Cover`, `T4Zero1`, `T4Zero1Arc`), the Lipschitz transfer and the Horner link (`T4Lip`, `T4Horner`, `T4Harc`),
the 1999 row checks (`T4Chunks`, 20 `native_decide` chunks), and `W ≤ 8847/10^7` (`T4Wup`).
-/

open Complex Finset

namespace P3Lean

noncomputable section

open Z1

/-- grid ordinate of zero `k` (`k < 2000`): `N0` for the first zero, then `NsAll`. -/
def Lw (k : ℕ) : ℕ := N534.L0w.getD k 0

lemma L0w_eq : N534.L0w = 15177045555 :: NsAll := by
  unfold N534.L0w NsAll
  decide +kernel

lemma Lw_zero : Lw 0 = Z1.N0 := by
  unfold Lw; rw [L0w_eq]; rfl

lemma Lw_succ (k : ℕ) : Lw (k + 1) = Ns (k + 1) := by
  unfold Lw Ns; rw [L0w_eq]; simp

/-- the grid facts for one zero, symbolic in the grid ordinate `N` -/
lemma grid_facts (N : ℕ) (P wl : ℚ) (hP : P = 1 / 4 + ((N : ℚ) - 1025) ^ 2 / 2 ^ 60)
    (hwl : wl = 1 / (1 / 4 + ((N : ℚ) + 1025) ^ 2 / 2 ^ 60)) (hN : 1025 ≤ N) (g : ℝ)
    (hg1 : ((N : ℝ) - 1025) / 2 ^ 30 ≤ g) (hg2 : g ≤ ((N : ℝ) + 1025) / 2 ^ 30) :
    ((P : ℚ) : ℝ) ≤ ‖zpt g‖ * ‖zpt ((N : ℝ) / 2 ^ 30)‖ ∧ |g - (N : ℝ) / 2 ^ 30| ≤ (1025 : ℝ) / 2 ^ 30 ∧
      ((wl : ℚ) : ℝ) ≤ wOf g := by
  have hNH : (1025 : ℝ) ≤ N := by exact_mod_cast hN
  set m : ℝ := (N : ℝ) / 2 ^ 30 with hm
  set g0 : ℝ := ((N : ℝ) - 1025) / 2 ^ 30 with hg0
  have hg0nn : 0 ≤ g0 := by rw [hg0]; exact div_nonneg (by linarith) (by positivity)
  have hmg : g0 ≤ m := by rw [hg0, hm]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hPr : ((P : ℚ) : ℝ) = 1 / 4 + g0 ^ 2 := by
    rw [hP, hg0]; push_cast; field_simp
  have hzs : ∀ x : ℝ, g0 ≤ x → ((P : ℚ) : ℝ) ≤ ‖zpt x‖ ^ 2 := by
    intro x hx
    rw [sq_norm_zpt, hPr]
    have := pow_le_pow_left₀ hg0nn hx 2
    linarith
  have hP0 : (0 : ℝ) < ((P : ℚ) : ℝ) := by rw [hPr]; positivity
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hzs g hg1
    have h2' := hzs m hmg
    have : ((P : ℚ) : ℝ) ^ 2 ≤ (‖zpt g‖ * ‖zpt m‖) ^ 2 := by
      rw [mul_pow, sq]
      exact mul_le_mul h1 h2' hP0.le (le_trans hP0.le h1)
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  · have e2 : ((N : ℝ) + 1025) / 2 ^ 30 = m + (1025 : ℝ) / 2 ^ 30 := by rw [hm]; ring
    have e1 : g0 = m - (1025 : ℝ) / 2 ^ 30 := by rw [hg0, hm]; ring
    rw [abs_le]; constructor <;> linarith
  · have hwr : ((wl : ℚ) : ℝ) = 1 / (1 / 4 + (((N : ℝ) + 1025) / 2 ^ 30) ^ 2) := by
      rw [hwl]; push_cast; field_simp
    have hgn : 0 ≤ g := le_trans hg0nn hg1
    rw [hwr]; unfold wOf
    apply one_div_le_one_div_of_le (by positivity)
    have := pow_le_pow_left₀ hgn hg2 2
    linarith

lemma betaR_nonneg (i j : ℕ) : 0 ≤ betaR i j := by unfold betaR; positivity

lemma sS_cast (i : ℕ) (hlen : (bsv i).length = 594) :
    ((sS i : ℚ) : ℝ) = ∑ j ∈ range 594, betaR i j := by
  have h := sum_betaR (bsv i) hlen
  have e : ((sS i : ℚ) : ℝ) = (((bsv i).foldl (· + ·) 0 : ℕ) : ℝ) / 2 ^ 50 := by
    unfold sS; push_cast; ring
  rw [e, h]; unfold betaR; field_simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- one arc: every `y` of `(Ψ_i - h_i, Ψ_i + h_i)` is good for chain vector `i` -/
theorem harc_pos (γ : ℕ → ℝ)
    (hγ : ∀ k, k < 2000 → (((Lw k : ℕ) : ℝ) - 1025) / 2 ^ 30 ≤ γ k ∧ γ k ≤ (((Lw k : ℕ) : ℝ) + 1025) / 2 ^ 30)
    (hW : Wtail 2000 γ ≤ 8847 / 10 ^ 7) (i : ℕ) (hi : i < 22) (Ψ : ℝ)
    (hψ : zc i = (‖zc i‖ : ℂ) * Complex.exp ((Ψ : ℝ) * I)) (hzp : 0 < ‖zc i‖) (y : ℝ)
    (hy1 : Ψ - (hq i : ℝ) < y) (hy2 : y < Ψ + (hq i : ℝ)) :
    (∑ k ∈ Ico 1 2000, 2 * wOf (γ k) * ‖Bd (betaR i) 594 (thetaOf (γ k))‖ +
        Wtail 2000 γ * ∑ j ∈ range 594, betaR i j) <
      2 * wOf (γ 0) * ‖Bd (betaR i) 594 (thetaOf (γ 0))‖ *
        Real.cos (y - (-((Bd (betaR i) 594 (thetaOf (γ 0))).arg) - Real.pi)) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := smallOK_true i hi
  obtain ⟨hlen, hlink⟩ := linkOK_true i hi
  obtain ⟨hw0, hwlo, hPz, hN0⟩ := paramOK_true
  obtain ⟨hrcos, hh0, hh1⟩ := rho_cos i hi
  have hSs : ((sS i : ℚ) : ℝ) = ∑ j ∈ range 594, betaR i j := sS_cast i hlen
  have hS0 : 0 ≤ ∑ j ∈ range 594, betaR i j := Finset.sum_nonneg fun j _ => betaR_nonneg i j
  -- the zero-1 grid facts
  obtain ⟨hPle, hδ, hwl⟩ := grid_facts Z1.N0 Z1.Pz Z1.wlo hPz hwlo hN0 (γ 0)
    (by have := (hγ 0 (by norm_num)).1; rwa [Lw_zero] at this)
    (by have := (hγ 0 (by norm_num)).2; rwa [Lw_zero] at this)
  have hPpos : (0 : ℝ) < ((Z1.Pz : ℚ) : ℝ) := by
    have : (0 : ℚ) < Z1.Pz := by rw [hPz]; positivity
    exact_mod_cast this
  -- the centre
  set c : ℂ := ⟨((-zr i : ℚ) : ℝ), ((zi i : ℚ) : ℝ)⟩ with hc
  have hz : zc i = -(starRingEnd ℂ) c := by
    apply Complex.ext <;> simp [hc, zc]
  -- grid value close to the centre
  have hgrid := sum_grid (bsv i) hlen Z1.N0
  have hlk := gcc_div_sub_le (hv i).1 (hv i).2 (2 ^ 50 * ((Z1.N0 : Int) * Z1.N0 + 2 ^ 58) ^ 593)
    (-zr i) (zi i) (3 / 2 ^ 60) (by positivity) (by norm_num) hlink
  have hsg : ‖∑ j ∈ range 594, (betaR i j : ℂ) * (qOf ((Z1.N0 : ℝ) / 2 ^ 30)) ^ j - c‖ ≤
      ((3 / 2 ^ 60 : ℚ) : ℝ) := by
    have e : ∑ j ∈ range 594, (betaR i j : ℂ) * (qOf ((Z1.N0 : ℝ) / 2 ^ 30)) ^ j
        = gcc ((hv i).1, (hv i).2) / (((2 ^ 50 * ((Z1.N0 : Int) * Z1.N0 + 2 ^ 58) ^ 593 : Int)) : ℂ) := hgrid
    rw [e]; exact hlk
  have hlip := lip_diff (betaR i) 594 (betaR_nonneg i) (γ 0) ((Z1.N0 : ℝ) / 2 ^ 30) ((Z1.Pz : ℚ) : ℝ)
    ((1025 : ℝ) / 2 ^ 30) hPpos hPle hδ
  have hBt : Bd (betaR i) 594 (thetaOf (γ 0)) = ∑ j ∈ range 594, (betaR i j : ℂ) * (qOf (γ 0)) ^ j :=
    Bd_eq_qpow _ _ _
  have hB : ‖Bd (betaR i) 594 (thetaOf (γ 0)) - c‖ ≤ ((epsL.getD i 0 : ℚ) : ℝ) := by
    have h1 : ((sS i * 593 * ((1025 / 2 ^ 30 : ℚ) / Z1.Pz) + 3 / 2 ^ 60 : ℚ) : ℝ) ≤ ((epsL.getD i 0 : ℚ) : ℝ) := by
      exact_mod_cast hs1
    have h2 : (((sS i * 593 * ((1025 / 2 ^ 30 : ℚ) / Z1.Pz) + 3 / 2 ^ 60 : ℚ)) : ℝ)
        = (∑ j ∈ range 594, betaR i j) * ((594 - 1 : ℕ) : ℝ) * ((1025 : ℝ) / 2 ^ 30 / ((Z1.Pz : ℚ) : ℝ))
          + ((3 / 2 ^ 60 : ℚ) : ℝ) := by
      push_cast; rw [← hSs]
    rw [hBt]
    generalize (∑ j ∈ range 594, (betaR i j : ℂ) * (qOf (γ 0)) ^ j) = A at hlip ⊢
    generalize (∑ j ∈ range 594, (betaR i j : ℂ) * (qOf ((Z1.N0 : ℝ) / 2 ^ 30)) ^ j) = B at hlip hsg
    generalize (∑ j ∈ range 594, betaR i j) = S at hlip h2
    have h3 : ‖A - c‖ ≤ ‖A - B‖ + ‖B - c‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le (A - B) (B - c)
    linarith [h1, h2, hlip, hsg, h3]
  -- Nn bound
  have hnn0 : (0 : ℝ) ≤ ((nnL.getD i 0 : ℚ) : ℝ) := by exact_mod_cast hs3
  have hzn : ‖zc i‖ ^ 2 = ((zr i : ℚ) : ℝ) ^ 2 + ((zi i : ℚ) : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [zc]; ring
  have hwlpos : (0 : ℝ) < ((Z1.wlo : ℚ) : ℝ) := by exact_mod_cast hw0
  have hrq0 : (0 : ℝ) ≤ ((rq i : ℚ) : ℝ) := by exact_mod_cast hs4
  have hsq : (((nnL.getD i 0 : ℚ) : ℝ) / (2 * ((Z1.wlo : ℚ) : ℝ)) + ((epsL.getD i 0 : ℚ) : ℝ)) ^ 2
      ≤ (((rq i : ℚ) : ℝ) * ‖zc i‖) ^ 2 := by
    rw [mul_pow, hzn]
    exact_mod_cast hs5
  have hle := (abs_le_of_sq_le_sq' hsq (by positivity)).2
  have hrho : ((nnL.getD i 0 : ℚ) : ℝ) ≤
      2 * ((Z1.wlo : ℚ) : ℝ) * (((rq i : ℚ) : ℝ) * ‖zc i‖ - ((epsL.getD i 0 : ℚ) : ℝ)) := by
    have h1 : ((nnL.getD i 0 : ℚ) : ℝ) / (2 * ((Z1.wlo : ℚ) : ℝ)) ≤
        ((rq i : ℚ) : ℝ) * ‖zc i‖ - ((epsL.getD i 0 : ℚ) : ℝ) := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at h1
  have hq1 : ((hq i : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hh1
  have hmain := zero1_good (Bd (betaR i) 594 (thetaOf (γ 0))) c (zc i) ((epsL.getD i 0 : ℚ) : ℝ) (wOf (γ 0))
    ((Z1.wlo : ℚ) : ℝ) ((nnL.getD i 0 : ℚ) : ℝ) ((rq i : ℚ) : ℝ) Ψ (hq i : ℝ) y 0 hB hz hψ hzp hwlpos hwl hnn0
    hrho (by linarith [Real.pi_gt_three, hq1]) hrcos
    (by rw [abs_lt]; constructor <;> push_cast <;> linarith)
  -- the displayed sum is at most Nn
  have hrows : ∀ k ∈ range 1999, 2 * wOf (γ (1 + k)) * ‖Bd (betaR i) 594 (thetaOf (γ (1 + k)))‖
      ≤ (U i (k + 1) : ℝ) / 2 ^ 40 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hk1 : 1 + k = k + 1 := by omega
    rw [hk1]
    obtain ⟨hge, hchk⟩ := T4_chunks.1 i hi (k + 1) (by omega) (by omega)
    have hb := hγ (k + 1) (by omega)
    rw [Lw_succ] at hb
    rw [Bd_eq_qpow]
    exact row_sound (bsv i) hlen (Ns (k + 1)) (rho i (k + 1)) (U i (k + 1)) hge hchk (γ (k + 1)) hb.1 hb.2
  have hsum : ∑ k ∈ Ico 1 2000, 2 * wOf (γ k) * ‖Bd (betaR i) 594 (thetaOf (γ k))‖
      ≤ ((utotL.getD i 0 : ℕ) : ℝ) / 2 ^ 40 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have e : (2000 - 1 : ℕ) = 1999 := rfl
    rw [e]
    calc _ ≤ ∑ k ∈ range 1999, (U i (k + 1) : ℝ) / 2 ^ 40 := Finset.sum_le_sum hrows
      _ = ((∑ k ∈ range 1999, U i (k + 1) : ℕ) : ℝ) / 2 ^ 40 := by
          rw [← Finset.sum_div]; push_cast; rfl
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast T4_chunks.2 i hi
  have hnn : ((utotL.getD i 0 : ℕ) : ℝ) / 2 ^ 40 + 8847 / 10 ^ 7 * ((sS i : ℚ) : ℝ)
      ≤ ((nnL.getD i 0 : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hs2
    push_cast at h
    linarith
  have hWS : Wtail 2000 γ * ∑ j ∈ range 594, betaR i j ≤ 8847 / 10 ^ 7 * ((sS i : ℚ) : ℝ) := by
    rw [hSs]; exact mul_le_mul_of_nonneg_right hW hS0
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **T4.**  See the header: two hypotheses, `hγ` (the boxes) and `hF` (the displayed tail bound). -/
theorem T4 (γ x F : ℕ → ℝ)
    (hγ : ∀ k, k < 2000 → (((Lw k : ℕ) : ℝ) - 1025) / 2 ^ 30 ≤ γ k ∧ γ k ≤ (((Lw k : ℕ) : ℝ) + 1025) / 2 ^ 30)
    (hF : ∀ j, j < 594 → |F j - ∑ k ∈ range 2000, 2 * wOf (γ k) * Real.cos ((j : ℝ) * thetaOf (γ k) + x k)|
      ≤ Wtail 2000 γ) :
    (∃ j, j < 594 ∧ F j < 0) ∧ (∃ j, j < 594 ∧ 0 < F j) := by
  have hL : ∀ k, k < 2000 → 1025 ≤ Lw k := by
    intro k hk
    rcases k with _ | k
    · rw [Lw_zero]; exact paramOK_true.2.2.2
    · rw [Lw_succ]; exact (T4_chunks.1 0 (by norm_num) (k + 1) (by omega) (by omega)).1
  have hγ' : ∀ k, k < 2000 → 0 ≤ γ k ∧ γ k ≤ (((N534.L0w.getD k 0 : ℕ) : ℝ) + 1025) / 2 ^ 30 := by
    intro k hk
    have h := hγ k hk
    have hLk : (1025 : ℝ) ≤ ((Lw k : ℕ) : ℝ) := by exact_mod_cast hL k hk
    exact ⟨le_trans (div_nonneg (by linarith) (by positivity)) h.1, h.2⟩
  have hW := N534.Wtail_le_T4 γ hγ'
  obtain ⟨Ψ, hpol, hchain, h0, hend⟩ := arcs_data
  refine T4_glue (K := 2000) (L := 594) (n := 22) (by norm_num) (by norm_num)
    (w := fun k => wOf (γ k)) (θ := fun k => thetaOf (γ k)) (W := Wtail 2000 γ) betaR
    (fun k _ => by unfold wOf; positivity) (fun i _ j _ => betaR_nonneg i j)
    (fun i => Ψ i - (hq i : ℝ)) (fun i => Ψ i + (hq i : ℝ)) ?_ hchain h0 hend x F hF
  intro i hi y h1 h2
  exact harc_pos γ hγ hW i hi (Ψ i) (hpol i hi).1 (hpol i hi).2 y h1 h2

end

end P3Lean

#print axioms P3Lean.T4
