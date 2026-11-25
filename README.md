# The longest sign run of Keiper-Li second differences: a torus problem and its dual

Author: Michaël Perreault

Let lambda_n be the Keiper-Li coefficients and c_n = lambda_(n+1) - 2 lambda_n + lambda_(n-1) their second differences. Assuming the Riemann hypothesis (RH), every run of one sign of c_n has length at most 593, improving the bound 621 of the [previous paper](https://github.com/mik-tf/keiper-li-sign-runs). The companion torus problem, where the phases of the cosines in the zero formula are free, has value between 589 and 593. Under RH and an independence hypothesis on the zero angles, the torus value equals the longest run of c_n, and runs of 589 values of each sign occur with positive lower density. A duality theorem shows that a finite certificate exists exactly above the torus value. Each result carries its hypotheses and its label (proved, certified, conditional or numerical) in the paper.

Paper: [the-longest-sign-run-of-keiper-li-second-differences-a-torus-problem-and-its-dual.pdf](the-longest-sign-run-of-keiper-li-second-differences-a-torus-problem-and-its-dual.pdf) (source: [paper.md](paper.md)). Appendix B of the paper lists every certificate and the command that reproduces it.

## Licences

- Text (`paper.md`, the PDF) and the archived certificates: CC BY 4.0, see [LICENSE-paper.md](LICENSE-paper.md).
- Code in `code/`: MIT, see [LICENSE](LICENSE).

## Rebuild the PDF

The paper was built from `paper.md` with mdtexpdf, a Markdown-to-LaTeX converter (pdfLaTeX). Rebuilding the PDF is optional; the certificate code in `code/` runs on its own.

## Re-run the certificates

Python 3.12 with python-flint 0.9.0 (Arb, 128-bit balls), numpy and mpmath (the last two only for the cross-check C5). Run from the directory `code/`; each command writes to `OUT`, never to the archived files. An archived file differs from a re-run only in timing and run-record fields.

```
cd code; mkdir -p OUT
python3 certify_torus584.py z2000.json inputs_c1_589.json OUT/cert_c1_torus589.json
python3 certify_c2.py z2000.json 594 vectors_c2.json OUT/cert_c2_L594.json --jobs 4
python3 certify_comb_rob.py z2000.json 534 6 sine 2000 robust OUT/cert_c3_K2000.json
python3 certify_comb_rob.py z2000.json 534 6 sine 1400 robust OUT/cert_c3_K1400.json
python3 certify_tail_c4.py z2000.json inputs_c1_589.json inputs_c4_200000.json OUT/cert_c4_589_G200000.json
python3 crosscheck_c5.py . --c1-inputs inputs_c1_589.json --c1-cert cert_c1_torus589.json --c4-cert cert_c4_589_G200000.json --json OUT/crosscheck_c5_589.json
python3 certify_c6.py z2000.json 594 vectors_c2.json OUT/cert_c6_L594.json --jobs 4
```

C1 certifies Theorem T3 (window 589), C2 and C6 (an independent exact rational check) Theorem T4 (window 594), C3 Theorem T7, C4 Theorem T6, and C5 is a floating point cross-check, not a certificate. Each takes from seconds to a few minutes; the exact timings, the inputs that must fail (`broken/`) and their logs (`runs/`) are listed in Appendix B. Figure data: `python3 make_figure_data_p3.py` reads only archived files.

The run records of C4 (`code/runs/res_c4_*.json`, `code/cert_c4_*.json`) carry `nt_bound_sha256` 0fb58a98b3b6a643e30dc3bd948efbc76724bae2eadd8624badde4161a1dc280, the sha256 of `code/nt_bound.py` as shipped. The C4 runs themselves used the version with sha256 cd410e339370b5a5eea79cb3531fb5cf6c11118f421646105ec64a41e1624ab7; the two differ only in one removed docstring sentence (identical syntax trees once docstrings are removed), and the records were updated to the shipped sha. `script_sha256` is unchanged.

## Cite as

Perreault, M. The longest sign run of Keiper-Li second differences: a torus problem and its dual, version 1.0.2. https://github.com/mik-tf/keiper-li-run-torus (DOI: [10.5281/zenodo.24517615](https://doi.org/10.5281/zenodo.24517615) (all versions; v1.0 is [10.5281/zenodo.24517616](https://doi.org/10.5281/zenodo.24517616))). See [CITATION.cff](CITATION.cff).
