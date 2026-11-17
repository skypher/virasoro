# Exact-arithmetic audit manifest

This manifest describes the ancillary checks for `paper.tex`.  The ordinary
suite is run with

```sh
python3 -u -m pip install -r requirements-audit.txt
make audit
```

The direct level-ten reconstruction is added with

```sh
make audit-deep
```

From the repository root,

```sh
make arxiv-bundle
```

creates `dist/virasoro-arxiv-v1.tar.gz`. The archive contains only
`paper.tex` at its root and the audit README, manifest, dependency pin,
Makefile, twelve scripts, and two shared libraries under `anc/`. It excludes
the generated PDF and TeX auxiliary files, repository metadata, and project
planning files.

The tested environment is CPython 3.12 with SymPy 1.12.  A successful run
exits with status 0.  Each completed identity is printed with a `PASS`
prefix; any failed identity raises an assertion or prints `FAIL` and exits
nonzero.  Timing and `reconstructed F_N` progress lines are informational.

The ordinary suite runs, in order:

1. `tools/audit_first_resonances.py` — level-three data, the energy crossing
   form, and the level-seven embedding diamond.
2. `tools/audit_low_levels.py` — level-four Gram data, null vectors, torus
   polynomials, and the spin crossing form.
3. `tools/audit_regular_families.py` — the eight regularity minors of the
   normalized singular-vector families at the Ising parent and child
   weights (Lemma `lem:regular-families`).
4. `tools/audit_grade10_direct.py --crossing-only` — intrinsic construction
   of the level-ten second crossing form from the exact 42-by-42 Gram matrix,
   without generic-residue or confluence input.
5. `tools/audit_grade10_confluence.py` — exact level-ten confluence and the
   displayed finite-part polynomial.
6. `tools/audit_confluent_recursion.py` — low-level collision moments from
   the shifted recursion.
7. `tools/audit_direct_principal_parts.py` — direct inverse-Shapovalov checks
   of the displayed principal parts at the exact sample external weights
   `d = 3/7` and `d = 23`.
8. `tools/audit_stocco_comparison.py` — comparison through level four with
   Stocco's formulas.
9. `tools/audit_top_layer.py` — Theorem `thm:top-layer` at the three Ising
   interior weights through level ten, at `d = 3/7`, against a direct
   inverse-Shapovalov reconstruction, with the first-layer singular vectors,
   torus norms, and crossing scalars computed directly; Lemma
   `lem:d-derivatives` at `c = 1/2` for `M <= 6`; the labels, boxes, momenta and
   first steps used in the proof of Proposition `prop:layer-coefficients`
   (`pp' <= 60`, `k <= 6`), the orders at `d = 0, 1` of the Ising torus norms, and
   the proposition against the Ising norms `gamma_7`, `gamma_10`; and the
   enumerations of Remark `rem:top-layer-beyond` (one-term windows for `k <= 3`,
   two-term windows for `k <= 6`, with the odd-layer range of Corollary
   `cor:top-layer-sharp`) for all minimal models with `pp' <= 60`.

The deep target additionally runs `tools/audit_grade10_direct.py`, which
reconstructs the inverse-Shapovalov coefficients through level ten at the
exact sample external weight `d = 3/7` and checks the second level-ten
principal part directly there.  The intrinsic crossing-form check is repeated
as part of that full run.  It then runs `tools/audit_minimal_models.py`, which
reconstructs the block coefficients at the minimal models (3,4), (2,5), (2,7),
(3,5), (4,5), (2,9), (3,7) through level 10 and (2,3) through level 11 at
`d = 11/13`, and checks that the pole order at every interior weight equals
the Jantzen depth (Remark `rem:top-layer-beyond`), and tests Proposition
`prop:layer-coefficients` with Theorem `thm:top-layer` at (2,3) against the exact
Taylor coefficients at `d = 0, 1` for `N = 7, 8, 9`.  Next,
`tools/audit_layer_coefficients.py` expands the generic recursion exactly in
Laurent series in `b^2 - b_*^2` and checks Proposition `prop:layer-coefficients`
at `d = 0` and `d = 1` for layers up to four at (2,3) and up to three at
(2,5), (3,4), (2,7).
Finally it runs `tools/audit_kl_certificate.py` (about 20 minutes), the certificate of
Corollary `cor:top-layer-sharp`: for `2 <= M <= 40`, at every minimal-model charge, the
derivatives of `H_M` at `d = 0` and `d = 1` (Lemma `lem:d-derivatives`) never vanish
together off the Kac weights of level `<= M` (resultants and Groebner reduction over Q).  Interpolation samples at levels eight through ten
are distributed among worker processes; set `VIRASORO_AUDIT_JOBS` to control
their number.  Progress lines report completed and regular samples at every
worker batch.

## SHA-256

The hashes below identify the submitted audit sources.

```text
7863bddf935cf6c2bd87a61c1edad0d46036b24707059042436261e275375ddf  Makefile
8347daed02ebf7b3c3cfa494e97049b7e0ab15b9af00a5addd843ed44381a64a  requirements-audit.txt
701649d93a313c2853a9ecd4d3106ff1957a97c2ff802e4e57612e9ed6e4c84c  tools/audit_confluent_recursion.py
240545d5e84d292f360bf8d55d18de0e4dbe28ccbf3526f551fd8db4a1a81f9e  tools/audit_direct_principal_parts.py
90218c120e892157507e9167fbc9033ba85c6c25fbf2bde3269806ffced26185  tools/audit_first_resonances.py
978df56dce0c8be9389c8fe8b3d7dfd93170b2ea7a74fec47d1cdd3a8c809d29  tools/audit_grade10_confluence.py
f788150de71658f08fe11c1512ef64254fb1ff2e7da5682adeaa6ea105c6c232  tools/audit_grade10_direct.py
a06deb403aa2becb904c9f437742206974aa2fd3fe35356e78731b4cff24f130  tools/audit_kl_certificate.py
dab3557d933399d1deced4f28983534f13730378f0c065f4f965fc11fd1822a8  tools/audit_layer_coefficients.py
440b1a744cae37788512e6db19f41c132e8d42e0a813ad9101b217bc54946c38  tools/audit_low_levels.py
0a9c8563a0da3f9d7ca9061b923e657fc7ca663f1bfaefefebdf6354ff7b4ca7  tools/audit_minimal_models.py
4c7eba13ca7b7988107a4bd4ca6191a7a07b37dc579f8a818e47bde2929b0ce1  tools/audit_regular_families.py
f979190e290b2e57649d01dc6ba0fcaf225ff21fb085e92431c370a2b4f0aeb8  tools/audit_stocco_comparison.py
29ac19d33c33a7575730e67598d74c2bc86c0fce485cb444122d535b5579e418  tools/audit_top_layer.py
34c9a27ab97bb28b78f1c2e559c8dabf4bc5a2903d362ad43222f103c7910390  tools/direct_reconstruction.py
3f69e0f5a782cf9e23037907dbf38467fa7c5550750c5faf587cbddffc75b519  tools/exact_shapovalov.py
```
