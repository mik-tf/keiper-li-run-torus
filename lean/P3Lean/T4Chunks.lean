import P3Lean.T4C00
import P3Lean.T4C01
import P3Lean.T4C02
import P3Lean.T4C03
import P3Lean.T4C04
import P3Lean.T4C05
import P3Lean.T4C06
import P3Lean.T4C07
import P3Lean.T4C08
import P3Lean.T4C09
import P3Lean.T4C10
import P3Lean.T4C11
import P3Lean.T4C12
import P3Lean.T4C13
import P3Lean.T4C14
import P3Lean.T4C15
import P3Lean.T4C16
import P3Lean.T4C17
import P3Lean.T4C18
import P3Lean.T4C19

/-!
# T4, step 3: the 20 zero chunks together

`NsAll`, `RhoAll`, `UAll`: the concatenation of the chunks (zeros 1 to 1999, 0-indexed as in `z2000.json`).
`Ns k`, `rho i k`, `U i k` read zero `k` (`1 ≤ k ≤ 1999`).  `T4_chunks`:
* for every chain position `i < 22` and zero `k`: `1025 ≤ Ns k` and `checkZeroVec (bsv i) (Ns k) (rho i k) (U i k) = true`;
* `∑ k ∈ range 1999, U i (k+1) ≤ utotL i`.
-/

open Finset

namespace P3Lean

def NsAll : List ℕ :=
  T4C00.ns ++ T4C01.ns ++ T4C02.ns ++ T4C03.ns ++ T4C04.ns ++ T4C05.ns ++ T4C06.ns ++ T4C07.ns ++ T4C08.ns ++
  T4C09.ns ++ T4C10.ns ++ T4C11.ns ++ T4C12.ns ++ T4C13.ns ++ T4C14.ns ++ T4C15.ns ++ T4C16.ns ++ T4C17.ns ++
  T4C18.ns ++ T4C19.ns

def RhoAll : List (List ℕ) :=
  T4C00.rhoL ++ T4C01.rhoL ++ T4C02.rhoL ++ T4C03.rhoL ++ T4C04.rhoL ++ T4C05.rhoL ++ T4C06.rhoL ++ T4C07.rhoL ++
  T4C08.rhoL ++ T4C09.rhoL ++ T4C10.rhoL ++ T4C11.rhoL ++ T4C12.rhoL ++ T4C13.rhoL ++ T4C14.rhoL ++ T4C15.rhoL ++
  T4C16.rhoL ++ T4C17.rhoL ++ T4C18.rhoL ++ T4C19.rhoL

def UAll : List (List ℕ) :=
  T4C00.uL ++ T4C01.uL ++ T4C02.uL ++ T4C03.uL ++ T4C04.uL ++ T4C05.uL ++ T4C06.uL ++ T4C07.uL ++
  T4C08.uL ++ T4C09.uL ++ T4C10.uL ++ T4C11.uL ++ T4C12.uL ++ T4C13.uL ++ T4C14.uL ++ T4C15.uL ++
  T4C16.uL ++ T4C17.uL ++ T4C18.uL ++ T4C19.uL

/-- grid ordinate of zero `k` (`1 ≤ k ≤ 1999`; zero `k` is in `[(Ns k - 1025)/2^30, (Ns k + 1025)/2^30]`) -/
def Ns (k : ℕ) : ℕ := NsAll.getD (k - 1) 0
def rho (i k : ℕ) : ℕ := ((RhoAll.getD (k - 1) []).getD i 0)
def U (i k : ℕ) : ℕ := ((UAll.getD (k - 1) []).getD i 0)

lemma goodC_append {i : ℕ} {n1 n2 : List ℕ} {r1 r2 u1 u2 : List (List ℕ)}
    (hn : n1.length = r1.length) (hn' : n1.length = u1.length)
    (h1 : GoodC i n1 r1 u1) (h2 : GoodC i n2 r2 u2) : GoodC i (n1 ++ n2) (r1 ++ r2) (u1 ++ u2) := by
  intro idx hidx
  rw [List.length_append] at hidx
  by_cases h : idx < n1.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hn ▸ h), List.getD_append _ _ _ _ (hn' ▸ h)]
    exact h1 idx h
  · push_neg at h
    rw [List.getD_append_right _ _ _ _ h, List.getD_append_right _ _ _ _ (hn ▸ h),
      List.getD_append_right _ _ _ _ (hn' ▸ h), ← hn, ← hn']
    exact h2 (idx - n1.length) (by omega)

theorem len_NsAll : NsAll.length = 1999 := by
  simp [NsAll, T4C00.len_ns, T4C01.len_ns, T4C02.len_ns, T4C03.len_ns, T4C04.len_ns, T4C05.len_ns, T4C06.len_ns,
    T4C07.len_ns, T4C08.len_ns, T4C09.len_ns, T4C10.len_ns, T4C11.len_ns, T4C12.len_ns, T4C13.len_ns, T4C14.len_ns,
    T4C15.len_ns, T4C16.len_ns, T4C17.len_ns, T4C18.len_ns, T4C19.len_ns]

theorem len_RhoAll : RhoAll.length = 1999 := by
  simp [RhoAll, T4C00.len_rho, T4C01.len_rho, T4C02.len_rho, T4C03.len_rho, T4C04.len_rho, T4C05.len_rho,
    T4C06.len_rho, T4C07.len_rho, T4C08.len_rho, T4C09.len_rho, T4C10.len_rho, T4C11.len_rho, T4C12.len_rho,
    T4C13.len_rho, T4C14.len_rho, T4C15.len_rho, T4C16.len_rho, T4C17.len_rho, T4C18.len_rho, T4C19.len_rho]

theorem len_UAll : UAll.length = 1999 := by
  simp [UAll, T4C00.len_u, T4C01.len_u, T4C02.len_u, T4C03.len_u, T4C04.len_u, T4C05.len_u, T4C06.len_u,
    T4C07.len_u, T4C08.len_u, T4C09.len_u, T4C10.len_u, T4C11.len_u, T4C12.len_u, T4C13.len_u, T4C14.len_u,
    T4C15.len_u, T4C16.len_u, T4C17.len_u, T4C18.len_u, T4C19.len_u]

theorem good_all (i : ℕ) (hi : i < 22) : GoodC i NsAll RhoAll UAll := by
  unfold NsAll RhoAll UAll
  simp only [List.append_assoc]
  refine goodC_append (by simp [T4C00.len_ns, T4C00.len_rho]) (by simp [T4C00.len_ns, T4C00.len_u]) (T4C00.good i hi) ?_
  refine goodC_append (by simp [T4C01.len_ns, T4C01.len_rho]) (by simp [T4C01.len_ns, T4C01.len_u]) (T4C01.good i hi) ?_
  refine goodC_append (by simp [T4C02.len_ns, T4C02.len_rho]) (by simp [T4C02.len_ns, T4C02.len_u]) (T4C02.good i hi) ?_
  refine goodC_append (by simp [T4C03.len_ns, T4C03.len_rho]) (by simp [T4C03.len_ns, T4C03.len_u]) (T4C03.good i hi) ?_
  refine goodC_append (by simp [T4C04.len_ns, T4C04.len_rho]) (by simp [T4C04.len_ns, T4C04.len_u]) (T4C04.good i hi) ?_
  refine goodC_append (by simp [T4C05.len_ns, T4C05.len_rho]) (by simp [T4C05.len_ns, T4C05.len_u]) (T4C05.good i hi) ?_
  refine goodC_append (by simp [T4C06.len_ns, T4C06.len_rho]) (by simp [T4C06.len_ns, T4C06.len_u]) (T4C06.good i hi) ?_
  refine goodC_append (by simp [T4C07.len_ns, T4C07.len_rho]) (by simp [T4C07.len_ns, T4C07.len_u]) (T4C07.good i hi) ?_
  refine goodC_append (by simp [T4C08.len_ns, T4C08.len_rho]) (by simp [T4C08.len_ns, T4C08.len_u]) (T4C08.good i hi) ?_
  refine goodC_append (by simp [T4C09.len_ns, T4C09.len_rho]) (by simp [T4C09.len_ns, T4C09.len_u]) (T4C09.good i hi) ?_
  refine goodC_append (by simp [T4C10.len_ns, T4C10.len_rho]) (by simp [T4C10.len_ns, T4C10.len_u]) (T4C10.good i hi) ?_
  refine goodC_append (by simp [T4C11.len_ns, T4C11.len_rho]) (by simp [T4C11.len_ns, T4C11.len_u]) (T4C11.good i hi) ?_
  refine goodC_append (by simp [T4C12.len_ns, T4C12.len_rho]) (by simp [T4C12.len_ns, T4C12.len_u]) (T4C12.good i hi) ?_
  refine goodC_append (by simp [T4C13.len_ns, T4C13.len_rho]) (by simp [T4C13.len_ns, T4C13.len_u]) (T4C13.good i hi) ?_
  refine goodC_append (by simp [T4C14.len_ns, T4C14.len_rho]) (by simp [T4C14.len_ns, T4C14.len_u]) (T4C14.good i hi) ?_
  refine goodC_append (by simp [T4C15.len_ns, T4C15.len_rho]) (by simp [T4C15.len_ns, T4C15.len_u]) (T4C15.good i hi) ?_
  refine goodC_append (by simp [T4C16.len_ns, T4C16.len_rho]) (by simp [T4C16.len_ns, T4C16.len_u]) (T4C16.good i hi) ?_
  refine goodC_append (by simp [T4C17.len_ns, T4C17.len_rho]) (by simp [T4C17.len_ns, T4C17.len_u]) (T4C17.good i hi) ?_
  refine goodC_append (by simp [T4C18.len_ns, T4C18.len_rho]) (by simp [T4C18.len_ns, T4C18.len_u]) (T4C18.good i hi) ?_
  exact T4C19.good i hi

theorem ge_all : ∀ n ∈ NsAll, 1025 ≤ n := by
  intro n hn
  simp only [NsAll, List.mem_append] at hn
  rcases hn with ((((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  exacts [T4C00.ge n h, T4C01.ge n h, T4C02.ge n h, T4C03.ge n h, T4C04.ge n h, T4C05.ge n h, T4C06.ge n h,
    T4C07.ge n h, T4C08.ge n h, T4C09.ge n h, T4C10.ge n h, T4C11.ge n h, T4C12.ge n h, T4C13.ge n h,
    T4C14.ge n h, T4C15.ge n h, T4C16.ge n h, T4C17.ge n h, T4C18.ge n h, T4C19.ge n h]

lemma sumU_append (i : ℕ) (a b : List (List ℕ)) : sumU i (a ++ b) = sumU i a + sumU i b := by
  simp [sumU, List.map_append, List.sum_append]

lemma sum_range_getD (i : ℕ) (l : List (List ℕ)) :
    ∑ k ∈ range l.length, (l.getD k []).getD i 0 = sumU i l := by
  induction l with
  | nil => simp [sumU]
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; simp [sumU]; omega

theorem utot_le (i : ℕ) (hi : i < 22) : sumU i UAll ≤ Z1.utotL.getD i 0 := by
  unfold UAll
  simp only [sumU_append]
  rw [T4C00.tot_eq i hi, T4C01.tot_eq i hi, T4C02.tot_eq i hi, T4C03.tot_eq i hi, T4C04.tot_eq i hi,
    T4C05.tot_eq i hi, T4C06.tot_eq i hi, T4C07.tot_eq i hi, T4C08.tot_eq i hi, T4C09.tot_eq i hi,
    T4C10.tot_eq i hi, T4C11.tot_eq i hi, T4C12.tot_eq i hi, T4C13.tot_eq i hi, T4C14.tot_eq i hi,
    T4C15.tot_eq i hi, T4C16.tot_eq i hi, T4C17.tot_eq i hi, T4C18.tot_eq i hi, T4C19.tot_eq i hi]
  have h : ∀ j, j < 22 → (T4C00.tot.getD j 0 + T4C01.tot.getD j 0 + T4C02.tot.getD j 0 + T4C03.tot.getD j 0 +
      T4C04.tot.getD j 0 + T4C05.tot.getD j 0 + T4C06.tot.getD j 0 + T4C07.tot.getD j 0 + T4C08.tot.getD j 0 +
      T4C09.tot.getD j 0 + T4C10.tot.getD j 0 + T4C11.tot.getD j 0 + T4C12.tot.getD j 0 + T4C13.tot.getD j 0 +
      T4C14.tot.getD j 0 + T4C15.tot.getD j 0 + T4C16.tot.getD j 0 + T4C17.tot.getD j 0 + T4C18.tot.getD j 0 +
      T4C19.tot.getD j 0) ≤ Z1.utotL.getD j 0 := by decide +kernel
  exact h i hi

/-- Step 3: the chunk facts for the 22 chain positions and the 1999 zeros. -/
theorem T4_chunks :
    (∀ i, i < 22 → ∀ k, 1 ≤ k → k ≤ 1999 →
      1025 ≤ Ns k ∧ checkZeroVec (bsv i) (Ns k) (rho i k) (U i k) = true) ∧
    (∀ i, i < 22 → ∑ k ∈ range 1999, U i (k + 1) ≤ Z1.utotL.getD i 0) := by
  refine ⟨fun i hi k hk1 hk2 => ⟨?_, ?_⟩, fun i hi => ?_⟩
  · have hl : k - 1 < NsAll.length := by rw [len_NsAll]; omega
    exact ge_all _ (by unfold Ns; rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
  · exact good_all i hi (k - 1) (by rw [len_NsAll]; omega)
  · have := utot_le i hi
    have h2 : ∑ k ∈ range 1999, U i (k + 1) = sumU i UAll := by
      rw [← sum_range_getD, len_UAll]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [U]
    omega

end P3Lean

#print axioms P3Lean.T4C00.good
#print axioms P3Lean.T4_chunks
