# Lean 4 certificates for paper 3: T7 (L = 534) and T4 (runs at most 593)

## Trust table
| theorem | statement | axioms (`#print axioms`) | what is trusted beyond Lean kernel and Mathlib |
|---|---|---|---|
| `P3Lean.N534.T7` | no window of 534 with `Wtail 2000 gamma < sum_k 2 w_k cos(j theta_k + x_k)` for all j < 534 | `propext, Classical.choice, Quot.sound` | the generated data files (zero intervals, weights, chain vectors), regenerated and diffed by `gen534.py --all`. All numerics by kernel `decide +kernel`. |
| `P3Lean.T4` | for any window `F` obeying the displayed tail bound, `F` takes a negative and a positive value among `F 0 .. F 593` | `propext, Classical.choice, Quot.sound` plus 40 `native_decide` axioms (two per chunk, `P3Lean.T4C00 .. T4C19`: `good` and `tot_eq`) | the Lean compiler and its native evaluator (axiom `Lean.ofReduceBool`; Lean v4.36 prints it as `P3Lean.T4Cnn.{good,tot_eq}._native.native_decide.ax_1_1`) for the 1999 row checks; the generated data files. No `sorryAx`. |

Hypotheses of `T4`, in plain words:
- `hgamma`: every ordinate gamma_k (k < 2000) lies in the certified interval of half-width 1025/2^30 around the grid point `Lw k`. This is the zero-interval list (part (a) of the paper), taken as input, not proved here.
- `hF`: the paper's displayed tail bound, `|F j - sum_{k<2000} 2 w_k cos(j theta_k + x_k)| <= Wtail 2000 gamma` for all j < 594. It is where the explicit zero formula and RH enter; it is assumed, not proved. With `F j = c_(n0+j)` and `x_k = n_0 theta_k` this is the paper's setting.
Everything else is proved: the 22-arc cover, the Lipschitz transfer, the Horner link, the bound `W <= 8847/10^7` (from a proved upper bound on Euler's constant), and the arithmetic checks. The 20 chunk files carry the only compiler-trusting step, and each check is also reproduced by the python generator.

## T4 build (the build server, never the desktop)
Same sync and build command as below, module `P3Lean.T4Assembly`; it imports `T4Chunks` (chunks `T4C00 .. T4C19`) and `T4Wup`. `T4Assembly` prints `#print axioms P3Lean.T4` at its end.
CPU: chunks 1114 s in total, `T4ChunkDef` 26 s, `T4Chunks` 27 s, `T4Assembly` 130 s (about 7 GB peak). T7: about 1330 CPU s (22 minutes).


Statement (`P3Lean.N534.T7`, file `P3Lean/N534Assembly.lean`): for every choice of ordinates gamma_k in the 2000
certified intervals (`code/z2000.json`, grid N/2^30, half-width 1025) and every phase vector x, it is false that
`Wtail 2000 gamma < sum_k 2 w_k cos(j theta_k + x_k)` holds for all j < 534.

Scope of T7: formalized at K = 2000 only. The paper's statement for K < 2000 rests on its monotonicity argument (T1(a)), which is not formalized; the paper's extra check at K = 1400 is not formalized either.

Link to the paper's intervals: the Lean boxes `[(N_k -+ 1025)/2^30]` (and `[(Lw k -+ 1025)/2^30]` in T4) are grid-rounded supersets of the paper's intervals `[mu_k -+ 2^-20]` (unrounded midpoints from `code/z2000.json`); 1025 = 1024 + rounding slack. The containment is NOT checked in Lean: it is checked by the `assert` in `gen534.py` (`mid_N`: `|mu_k - N/2^30| <= 2^-31`), and independently by the reviewer for all 2000 entries (2000/2000). It is a strengthening: any points in the boxes, not necessarily zeros or distinct. Besides the 40 native evaluations (T4), the generated data files and this Python check are the only unverified inputs.

Definitions against the paper: `thetaOf g = arg(1 - 1/(1/2 + i g))` equals the paper's `theta_k = 2 arctan(1/(2 gamma_k))` for g > 0 (the argument is `pi - 2 arctan(2 g)` in (0, pi)); g > 0 is forced by the boxes. This identification is stated, not proved as a Lean lemma. `wOf g = 1/(1/4 + g^2) = 1/|rho|^2` is the paper's `w_k`; `Wtail 2000 gamma = Cconst - 2 sum w_k`, `Cconst = 2 + gamma_E - log(4 pi)`, the paper's `W = C - 2 sum w*_k`.

Non-vacuity of `hF`: it is satisfiable exactly when `Wtail 2000 gamma >= 0` (take `F` the finite sum). That holds: `Wtail_ge` (`N534Tail.lean`, used in `N534Assembly.lean`) proves a positive lower bound on every box.

## Versions
Lean v4.36.0, Mathlib v4.36.0, LeanCert v4.36.0 (see `lean-toolchain`, `lake-manifest.json`). Mathlib from the cache.

## Build
All builds run on the build server (the build user), never on the desktop. Sync with
`rsync -a -e "ssh -i <key>" --exclude .lake lean/ <user>@<build-host>:<build-dir>/`
(never `--delete-excluded`), then on the build server:
```
. ~/.elan/env; cd <build-dir>
python3 -I gen534.py --all        # optional: regenerates N534Cert, N534Chain, N534C00..C19 (about 2 min)
LEAN_NUM_THREADS=3 nice -n 19 systemd-run --user --scope -p CPUWeight=50 -p MemoryMax=12G -p MemorySwapMax=0 \
  /usr/bin/time -v lake build P3Lean.N534Tail     # repeat for N534Cert N534Chain N534AsmGen N534C00 ... N534C19 N534Assembly
```
Resources: `harc_pos` and `T4` run with `maxHeartbeats 0` (no elaboration timeout) and `maxRecDepth 100000`; the chunks set `maxRecDepth 100000`; T7 uses `maxHeartbeats 2000000`, `maxRecDepth 20000`, `Elab.async false`. These bound elaboration effort only, not soundness (the kernel still checks the term), but a reproducer on a small machine should expect no timeout.
Check `uptime` first (under 30: 3 threads, 30 to 40: 2, over 40: wait) and avoid 12:40 to 15:00 UTC. `lake exe cache get` fetches Mathlib; never build it from source.
All T7 numerics are kernel `decide +kernel`; T7 has no `native_decide`, no `sorry`. (T4 uses `native_decide` for its 20 chunks, see the trust table.)
Generated files are committed (as in paper 2), so the generator is only needed to audit them.

## Times (one thread, loaded server, user+sys CPU seconds)
| module | CPU s |
|---|---|
| N534Tail | about 90 (wall) |
| N534Cert | 7 |
| N534Chain | 61 |
| N534AsmGen | 34 |
| N534C00..C19 (20 chunks) | 1086 in total, largest C04 102.9 |
| N534Assembly | 51 |
| total | about 1330 CPU s (22 minutes) |

Per-module numbers: `logs` of the run (user+sys): Cert 7.5, Chain 60.8, AsmGen 33.7, C00 85.6, C01 66.5, C02 100.1,
C03 89.7, C04 102.9, C05 98.0, C06 72.3, C07 43.7, C08 28.8, C09 27.7, C10 43.5, C11 36.7, C12 35.4, C13 40.5,
C14 37.2, C15 38.7, C16 35.4, C17 46.4, C18 23.6, C19 33.0, Assembly 51.0.

## Axioms
`#print axioms P3Lean.N534.T7` gives `[propext, Classical.choice, Quot.sound]`. No analytic hypothesis: the lower bound
on Euler's constant is proved (`N534Tail`), not assumed.

## Trust
Lean kernel, Mathlib, and the generated data files (zeros intervals, weights, chain vectors); `gen534.py --all`
regenerates them and `git diff` shows any change. No compiler, no `Lean.ofReduceBool`; GMP only as used by the kernel's built-in `Nat` literal operations (part of the kernel).

# T4 module map (status: complete, see the trust table)

The T4 chain is fully connected: `T4Assembly` proves `P3Lean.T4` using 22 arcs (of the paper's 48 vectors), the Horner link, the 20 chunk files and `T4Wup`.
- `T4Wb`: `wb`, `wb_neg` (Lemma wb). `T4Lip`: `lip_dense`, `transfer_dense`, `Bd_eq_qpow`. `T4Cover`: `arc_cos`, `chain_cover`, `cover_all`, `T4_glue`.
- `T4Zero1`, `T4Zero1Arc`, `T4Horner`, `T4Harc`: zero 1 and the Horner link; `T4ChunkDef`, `T4C00 .. T4C19`, `T4Chunks`: the row checks; `T4Wup`: `W <= 8847/10^7`.
- `Native.lean`, `Core.lean`, `Data.lean` (and `gen_pilot.py` output) are earlier pilots; `T4` does not import `Native.lean` or `Data.lean`.
