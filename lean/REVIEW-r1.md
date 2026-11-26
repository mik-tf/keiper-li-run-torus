# Review r1: paper 3 Lean formalization (T4, T7), before v1.2

Reviewed at `be53b85` (branch `lean`). Read-only review; nothing was built. Checked against `paper.md` on `origin/main`
(T4: Section "The upper side", Lemma wb, Certificate C2, Theorem window 594; T7: Theorem robust-tail problem,
window 534; the zero list in Section 2), `lean/README.md`, `lean/PAPER_SECTION.md`, `P3Lean/T4Assembly.lean`,
`P3Lean/T4Cover.lean` (`T4_glue`), `P3Lean/T4Wb.lean` (`Bd`, `wb`, `wb_neg`), `P3Lean/Defs.lean` (`zpt`, `qOf`,
`thetaOf`, `wOf`, `Cconst`, `Wtail`), `P3Lean/T4Chunks.lean` (`NsAll`, `Ns`), `P3Lean/T4Wup.lean` (`L0w`),
`P3Lean/N534Assembly.lean` (`L0`, `loQ`, `hiQ`, `T7`), `lean/gen534.py` (`mid_N`), `code/z2000.json`, and the
final build log `asm5.log`.

## Summary

The Lean statements say what the paper says, and in two places say more (the hypotheses are weaker than the
paper's). No MAJOR finding. The proof term is sound as far as the statement and `#print axioms` show. All findings
are about the accompanying text (README, PAPER_SECTION, docstrings) and are cheap to fix before the release.

Counts: MAJOR 0, MINOR 8, NIT 7.

## What was checked and holds

- **T4 conclusion.** `(∃ j < 594, F j < 0) ∧ (∃ j < 594, 0 < F j)`: strict signs on both sides, window `0..593`,
  exactly the paper's "an index with c_n < 0 and an index with c_n > 0" in every window of 594 (with
  `F j = c_(n0+j)`). The "runs at most 593" corollary is immediate.
- **hF.** `∀ j < 594, |F j - ∑_{k<2000} 2 wOf(γ k) cos(j thetaOf(γ k) + x k)| ≤ Wtail 2000 γ` is the paper's
  displayed bound (Section "The upper side", the display defining W), restricted to `j < 594` instead of all
  `j ∈ ℤ`, with `F` an arbitrary real function instead of `F_x`. Both changes weaken the hypothesis, so the Lean
  theorem is more general than the paper needs. `Wtail 2000 γ = Cconst - 2 ∑ wOf(γ k)` with
  `Cconst = 2 + γ_E - log(4π)` is the paper's `W = C - 2 ∑ w*_k`; `wOf` is the paper's `w_k`.
- **hF cannot trivially imply the conclusion.** If W were large (say W ≥ the cosine sum's amplitude) the
  conclusion fails for `F ≡ 1`; the content is in the cover and the row checks, as it should be.
- **hγ.** Universally quantified ordinates in boxes; they need not be zeros, nor distinct. This is stronger than
  the paper, which uses specific zeros of odd multiplicity in `I_k` (part (a)).
- **Intervals vs the paper's `I_k`.** I re-derived the link independently: for all 2000 entries,
  `L0w[k] = round(μ_k · 2^30)` with error ≤ 2^-31, and `[μ_k ± 2^-20] ⊆ [(L0w[k] ± 1025)/2^30]` (0 failures).
  So the Lean boxes contain the paper's intervals, and hγ is implied by part (a). The T7 grid `L0`
  (`N0 :: NSall`, from `N534C*.nsC`) and the T4 grid `L0w` are the same 2000 numbers (checked), and
  `L0w = N0 :: NsAll` is a kernel lemma (`L0w_eq`).
- **The cover.** `T4_glue` takes open arcs `(a i, b i)` with `a (i+1) < b i`, `a 0 < 0`, `2π < b (n-1)`: a strict
  chain covering `[0, 2π]`, matching C2 step 5 (a shared endpoint fails). The positive side is done by
  `x ↦ x + π`, `F ↦ -F`, as in the paper's proof step (4).
- **Axioms.** `asm5.log` prints for `P3Lean.T4`: `propext, Classical.choice, Quot.sound` and exactly 40
  `native_decide` axioms, `T4C00..T4C19` × {`good`, `tot_eq`}; no `sorryAx`. Peak memory of `T4Assembly`
  6.98 GB, 129.7 s user + 9.8 s system: the README's "130 s, about 7 GB" is right.
- **T7.** `¬ ∀ j < 534, Wtail 2000 γ < ∑_{k<2000} 2 w_k cos(j θ_k + x_k)` for all γ in the boxes and all x: this is
  `L_c(2000) ≤ 533` in the paper's robust-tail definition (strict `>` T_K, the K-zero model with amplitudes
  `2 w_k`). It has no hypothesis beyond the boxes, so it cannot be vacuous.

## MINOR

1. **README contradicts itself (release blocker for the text, not the proof).** Below the T7 sections the README
   still carries the old "T4 ... (work in progress)" block: "Not yet connected (the arithmetic input of
   `T4_glue`)", "`harc` (each of the 48 arcs ...)", "The full 2000 zeros are NOT run yet", and a "native_decide
   arithmetic" pilot paragraph about `Native.lean`/48 vectors. A reader of the public release sees both "T4 is
   proved" (trust table) and "T4 is not connected". Delete or rewrite that block; say the chain uses 22 arcs (of
   the paper's 48 vectors), and that `Native.lean`/`Core.lean`/`Data.lean` are pilots not imported by `T4`.
2. **T7 is formalized only at K = 2000.** The paper's T7 says "`L_c(K) ≤ 533` for K = 2000 (and, as a check, for
   K = 1400). Hence for every K ≤ 2000" via monotonicity (T1(a)). PAPER_SECTION says "T7 (no window of 534)"
   without K. State "at K = 2000; the extension to K < 2000 is the paper's monotonicity argument, not
   formalized; the K = 1400 check is not formalized".
3. **Say how the Lean boxes relate to `I_k`.** README and PAPER_SECTION call `[(Lw k ± 1025)/2^30]` "the certified
   interval" and "the zero list, part (a)". The paper's intervals are `[μ_k ± 2^-20]` with unrounded midpoints
   from `z2000.json`. The Lean boxes are grid-rounded supersets (1025 = 1024 + rounding slack); the containment is
   checked by the `assert` in `gen534.py` (`mid_N`), not in Lean. One sentence fixes it, and it should say this is
   a strengthening (larger boxes, any points, not necessarily zeros or distinct).
4. **Docstrings say hF is the only hypothesis.** `T4Assembly.lean` header (line 13: "`hF` is the only
   hypothesis") and the docstring of `theorem T4` (line 197: "the only hypothesis on the window is ... `hF`")
   ignore `hγ`. The second is defensible ("on the window"), the first is not. Reword to "two hypotheses: hγ (the
   boxes) and hF (the tail bound)".
5. **Non-vacuity of hF is not stated.** hF is satisfiable exactly when `Wtail 2000 γ ≥ 0` (take `F` = the finite
   sum). Mathematically W ≈ 8.8e-4 > 0, and the repo already proves a positive lower bound (`Wtail_ge`,
   `N534Tail.lean`, used at `N534Assembly.lean` line 382). A hostile referee will ask; add a two-line lemma
   (`∃ F, hF` for every γ in the boxes) or at least a sentence in PAPER_SECTION citing `Wtail_ge`.
6. **"No compiler or GMP runtime in the trust base" (README, T7 Trust).** The kernel's `Nat` literal arithmetic is
   GMP-accelerated (`N534Core.lean` line 41 says so), so GMP is in the trust base as part of the kernel. Say "no
   compiler, no `Lean.ofReduceBool`; GMP only as used by the kernel's built-in `Nat` operations".
7. **`maxHeartbeats 0` and `maxRecDepth 100000` are not disclosed.** `harc_pos` and `T4` run with
   `maxHeartbeats 0` (no timeout) and `maxRecDepth 100000`; the chunks set `maxRecDepth 100000`; T7 uses
   `maxHeartbeats 2000000`, `maxRecDepth 20000`, `Elab.async false`. None affects soundness (they bound
   elaboration effort, the kernel still checks the term), but a reproducer on a smaller machine needs to know
   there is no timeout. One line in README Build.
8. **θ is defined differently from the paper.** `thetaOf γ = arg(1 - 1/(1/2 + iγ))`, the paper's
   `θ_k = 2 arctan(1/(2γ_k))`. They agree for γ > 0 (the arg is `π - 2 arctan(2γ) ∈ (0, π)`), and γ > 0 is forced
   by hγ, but there is no Lean lemma and no sentence saying so. Add the sentence (or the lemma) so a reader can
   match the statement to the paper without unfolding definitions. Same for `wOf = 1/|ρ|^2`.

## NIT

1. README T7 times table: the per-chunk figures listed sum to 1085.7 s, not "1030 in total"; the largest is C04
   (102.9 s), not "C05 98"; the total is then about 1330 CPU s, not 1270.
2. PAPER_SECTION "T4 needs about 20 CPU minutes": chunks 1114 + `T4ChunkDef` 26 + `T4Chunks` 27 + `T4Assembly` 130
   = about 22 minutes, before `T4Wup`, `N534Tail`, `Weights` (90 s), `T4Harc` and the other dependencies. Say
   "about 22 CPU minutes for the chunks and assembly, plus dependencies" or give the full sum.
3. PAPER_SECTION "20 chunk files covering zeros 1 to 1999" is 0-based; in the paper's numbering these are zeros
   2 to 2000 (zero 1 is handled by the Horner link).
4. README T7 row: "... for all j" should be "for all j < 534".
5. PAPER_SECTION "We did not replace them by kernel evaluation, which would be much slower": unmeasured; say "not
   attempted" or give the T7 kernel cost as the comparison.
6. PAPER_SECTION "not a proof of RH-free statements": awkward; "it does not remove the RH assumption" is plainer.
7. README names the trusted primitive `Lean.ofReduceBool`; Lean v4.36 prints the axioms as
   `P3Lean.T4Cnn.{good,tot_eq}._native.native_decide.ax_1_1`. Give both names so a reader can match the output.

## Hostile-referee view

The likely objections, all answered by the fixes above: the README's "not yet connected" text (MINOR 1); "K ≤ 2000"
in the paper vs K = 2000 in Lean (MINOR 2); "where is the link from `z2000.json` to the boxes" (MINOR 3, trusted
data plus a Python assert; worth saying that the generated data files are the only unverified input besides the
40 native evaluations); "is hF ever true" (MINOR 5). The statement itself is not weaker than the paper's.

## Recommendation

Accept the formalization for v1.2 after the text fixes (MINOR 1 to 8; the NITs at the author's choice). No change
to the proof is required; the non-vacuity lemma (MINOR 5) and the θ identification lemma (MINOR 8) are optional
additions that would pre-empt referee questions.

CONVERGING: yes
