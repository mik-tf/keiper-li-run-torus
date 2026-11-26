# Response to review r1

All 15 items addressed. Only text changed, except two docstrings in `P3Lean/T4Assembly.lean` (no statement or proof touched); `P3Lean.T4Assembly` and its dependencies were rebuilt on the build server (build successful, 18325 jobs, 2:00 wall, 7.0 GB peak, axioms of `P3Lean.T4` unchanged: the three standard axioms plus the native_decide axioms).

## MINOR
1. Stale T4 work-in-progress block removed from README; replaced by a module map stating the chain is connected, uses 22 arcs, and that `Native.lean`, `Core.lean`, `Data.lean` are pilots not imported by `T4`.
2. README (T7 scope paragraph) and PAPER_SECTION say T7 is formalized at K = 2000 only; K < 2000 rests on the paper's monotonicity argument (not formalized); the K = 1400 check is not formalized.
3. README and PAPER_SECTION say the Lean boxes are grid-rounded supersets of the paper's `[mu_k +- 2^-20]`, that containment is checked by the `assert` in `gen534.py` (`mid_N`) and independently by the reviewer (2000/2000), not in Lean, and that this is a strengthening.
4. Both docstrings in `T4Assembly.lean` (header and `theorem T4`) now name the two hypotheses `hγ` and `hF`. Module rebuilt. README line on hypotheses already listed both.
5. README and PAPER_SECTION state that `hF` is satisfiable when `Wtail >= 0` and cite `Wtail_ge` (`N534Tail.lean`). No new Lean lemma added (optional per the review).
6. README Trust now reads: no compiler, no `Lean.ofReduceBool`, GMP only as used by the kernel's `Nat` literal operations. PAPER_SECTION notes kernel GMP too.
7. README Build discloses `maxHeartbeats 0`, `maxRecDepth 100000` (`harc_pos`, `T4`, chunks) and T7's `maxHeartbeats 2000000`, `maxRecDepth 20000`, `Elab.async false`, as effort limits, not soundness. PAPER_SECTION has a one-line version.
8. README and PAPER_SECTION give `thetaOf g = arg(1 - 1/(1/2 + i g)) = 2 arctan(1/(2g)) = pi - 2 arctan(2g)` for g > 0 (forced by the boxes), and `wOf`, `Cconst`, `Wtail` against the paper's `w_k`, `C`, `W`. Stated as a sentence, not proved as a lemma (optional).

## NIT
1. Times table corrected: chunks 1086 s in total (sum of the listed figures), largest C04 102.9, total about 1330 CPU s (22 minutes); the T4 build line and PAPER_SECTION use 22 minutes.
2. PAPER_SECTION: "about 22 CPU minutes for the chunks and assembly, plus dependencies", with the four figures and `Weights` about 90 s.
3. PAPER_SECTION: chunks cover zeros 2 to 2000 in the paper's numbering (0-based 1 to 1999); zero 1 by the Horner link.
4. README T7 row: "for all j < 534".
5. PAPER_SECTION: "not attempted", with the T7 kernel cost as nearest comparison.
6. PAPER_SECTION: "it does not remove the RH assumption".
7. README and PAPER_SECTION give both names: `Lean.ofReduceBool` and `P3Lean.T4Cnn.{good,tot_eq}._native.native_decide.ax_1_1`.
