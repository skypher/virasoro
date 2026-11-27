# Exact-arithmetic audit manifest

This manifest describes the ancillary checks for `paper.tex` (Part I) and
`irreducible/paper.tex`.  The ordinary
suite is run with

```sh
python3 -u -m pip install -r requirements-audit.txt
make audit
```

The direct level-ten reconstruction is added with

```sh
make audit-deep
```

(`make check` and `make check-long`, the names used in the paper, run the same two suites.)

The examples of `irreducible/paper.tex` (irreducible traces) are replayed with

```sh
make audit-irreducible
```

which runs `irreducible/tools/audit_irreducible_torus.py`.  It imports
`tools/direct_reconstruction.py` and `tools/exact_shapovalov.py` and must be run
from the directory that contains `tools/` (the repository root, or `anc/` in
the archive).  It checks Theorem `thm:descent-regularity` on allowed,
forbidden and half-fusion weights, Theorem `thm:first-layer-ratio` from the
two-weight Ward identity, Theorem `thm:gen-rocha-caridi` against exact
quotient-Gram traces (Lee--Yang N <= 9, Ising N <= 8, tricritical Ising
N <= 7) and the tricritical Ising traces against the closed forms of
Gaberdiel--Lang (phi(q)^(1/5), phi(q)^(11/5)/phi(q^2), and the series solution
of their equation (3.40), N <= 7), and Corollary `cor:collision-free` (Ising traces against Euler's
coefficients for N <= 30; Lee--Yang traces against the coefficients of
phi(q)^(-2/5), with denominators powers of 5, for N <= 25, and against the
quotient-Gram traces for N <= 9).

From the repository root,

```sh
make arxiv-bundle
```

creates `dist/virasoro-arxiv-v1.tar.gz`. The archive contains only
`paper.tex` at its root and the audit README, manifest, dependency pin,
Makefile, thirteen scripts and two shared libraries for Part I of
`paper.tex`, and `irreducible/tools/audit_irreducible_torus.py` for
`irreducible/paper.tex`, under
`anc/`. It excludes
the generated PDF and TeX auxiliary files, repository metadata, and project
planning files.

The tested environment is CPython 3.12 with SymPy 1.12.  A successful run
exits with status 0.  Each completed identity is printed with a `PASS`
prefix; any failed identity raises an assertion or prints `FAIL` and exits
nonzero.  Timing and `reconstructed F_N` progress lines are informational.

The ordinary suite runs, in order:

1. `tools/audit_first_resonances.py` — level-three data, the energy crossing
   form, the level-seven embedding diamond, and the exact symbolic level-seven
   finite-part polynomial `Theta_7(d)` (cross-checks of the level-seven data in
   Proposition `prop:ising-double-poles`).
2. `tools/audit_low_levels.py` — level-four Gram data, null vectors, torus
   polynomials, and the spin crossing form.
3. `tools/audit_regular_families.py` — the eight regularity minors of the
   normalized singular-vector families at the Ising parent and child
   weights (a cross-check of Lemma `lem:regular-everywhere` at these weights;
   the expected determinants are stored in the script).
4. `tools/audit_grade10_direct.py --crossing-only` — intrinsic construction
   of the level-ten second crossing form from the exact 42-by-42 Gram matrix,
   without generic-residue or confluence input.
5. `tools/audit_grade10_confluence.py` — exact level-ten confluence and its
   finite-part polynomial (cross-check of the level-ten double pole in
   Proposition `prop:ising-double-poles`).
6. `tools/audit_confluent_recursion.py` — low-level collision moments from
   the shifted recursion.
7. `tools/audit_direct_principal_parts.py` — direct inverse-Shapovalov checks
   of the level-seven principal part, including its double-pole coefficient
   and `gamma_7`, at the exact sample external weights `d = 3/7` and `d = 23`.
8. `tools/audit_stocco_comparison.py` — comparison through level four with
   Stocco's formulas.
9. `tools/audit_top_layer.py` — Theorem `thm:top-layer` at the three Ising
   interior weights through level ten, at `d = 3/7`, against a direct
   inverse-Shapovalov reconstruction, with the first-layer singular vectors,
   torus norms, and crossing scalars computed directly; Lemma
   `lem:d-derivatives` at `c = 1/2` for `M <= 6`; the labels, boxes, momenta and
   first steps used in the proof of Proposition `prop:layer-coefficients`
   (`pp' <= 60`, `k <= 6`), the orders at `d = 0, 1` of the Ising torus norms, and
   the proposition (and its `d = 1` analogue) against the Ising norms `gamma_7`,
   `gamma_10`, `gamma_11` of Proposition `prop:ising-double-poles`; and
   enumerations of one-term windows for `k <= 3` and two-term windows for
   `k <= 6` for all minimal models with `pp' <= 60`.
10. `tools/audit_one_screening.py` — exact verification of Proposition
    `prop:h13-nonvanishing` (Feigin-Fuchs Fock factorization `G_M =
    B_M(q_0, 2q_0 - alpha)^T D_M B_M(q_0, alpha)` in `Z[1/2][q_0, alpha]` for
    `M <= 4`; symbolic `P_M^(1), P_M^(2) in Z[1/2][t, Y]` with
    `P_M^(2)(0, Y) = P_M^(1)(0, Y)` and `P_M^(nu)(0, 0) = 4^M` for `M <= 5`;
    collapsed `(u, 1)` recursion against direct Shapovalov inversion for
    `M <= 6` at both `d_1 = h_{1,3}` and `d_2 = h_{1,-3}`; exact `sl_2`
    commutation identities for `a', r~, b' <= 5`; `M`-polynomiality of
    `c_{i,j}^(nu)(M)` of degree `<= 2i + 2j` for `i + j <= 3`, `M <= 8`; exact
    `ell`-adic valuation at `M = 42` and Lipschitz ratio bound including
    `e = 1..3` and all 8 former valuation-tie levels of `(8,9),(3,5),k=1`) and
    Proposition `prop:two-term-criteria` (Case 1 & 3 order characterization at
    `d_1, d_2` on `pp' <= 40, k <= 4`; Case 2 valuation cancellation for both
    `ell >= 5` and `ell = 3` on `pp' <= 80, k <= 4`; Case 3 exact
    `epsilon`-telescoping formula for `T_k` and `ell`-adic separation on
    `pp' <= 80, k <= 4`).

The deep target additionally runs `tools/audit_grade10_direct.py`, which
reconstructs the inverse-Shapovalov coefficients through level ten at the
exact sample external weight `d = 3/7` and checks the second level-ten
principal part directly there.  The intrinsic crossing-form check is repeated
as part of that full run.  It then runs `tools/audit_minimal_models.py`, which
reconstructs the block coefficients at the minimal models (3,4), (2,5), (2,7),
(3,5), (4,5), (2,9), (3,7) through level 10 and (2,3) through level 11 at
`d = 11/13`, and checks that the pole order at every interior weight equals
the Jantzen depth (a direct check of Corollary `cor:top-layer-sharp`), and tests Proposition
`prop:layer-coefficients` with Theorem `thm:top-layer` at (2,3) against the exact
Taylor coefficients at `d = 0, 1` for `N = 7, 8, 9`.  Next,
`tools/audit_layer_coefficients.py` expands the generic recursion exactly in
Laurent series in `b^2 - b_*^2` and checks Proposition `prop:layer-coefficients`
at `d = 0` (and its analogue at `d = 1`) for layers up to four at (2,3) and up to three at
(2,5), (3,4), (2,7).
Finally it runs `tools/audit_kl_certificate.py` (about 20 minutes), an
independent check for `2 <= M <= 40` that at every minimal-model charge the
derivatives of `H_M` at `d = 0` and `d = 1` (Lemma `lem:d-derivatives` and its
`d = 1` analogue) never
vanish together off the Kac weights of level `<= M` (resultants and Groebner
reduction over Q).  Interpolation samples at levels eight through ten
are distributed among worker processes; set `VIRASORO_AUDIT_JOBS` to control
their number.  Progress lines report completed and regular samples at every
worker batch.

## SHA-256

The hashes below identify the submitted audit sources.

```text
7f0a728fbea288b069d2d150b5b5167444cd1a04930484320ab7ead6d348fcf9  Makefile
8347daed02ebf7b3c3cfa494e97049b7e0ab15b9af00a5addd843ed44381a64a  requirements-audit.txt
701649d93a313c2853a9ecd4d3106ff1957a97c2ff802e4e57612e9ed6e4c84c  tools/audit_confluent_recursion.py
240545d5e84d292f360bf8d55d18de0e4dbe28ccbf3526f551fd8db4a1a81f9e  tools/audit_direct_principal_parts.py
5824b2952fd75394b16bd30e9ed25cd8a191f62ce450169b0c29bb0e5ad077ac  tools/audit_first_resonances.py
978df56dce0c8be9389c8fe8b3d7dfd93170b2ea7a74fec47d1cdd3a8c809d29  tools/audit_grade10_confluence.py
f788150de71658f08fe11c1512ef64254fb1ff2e7da5682adeaa6ea105c6c232  tools/audit_grade10_direct.py
a06deb403aa2becb904c9f437742206974aa2fd3fe35356e78731b4cff24f130  tools/audit_kl_certificate.py
dab3557d933399d1deced4f28983534f13730378f0c065f4f965fc11fd1822a8  tools/audit_layer_coefficients.py
440b1a744cae37788512e6db19f41c132e8d42e0a813ad9101b217bc54946c38  tools/audit_low_levels.py
06276e2ade35ef9da04baa303216474e7b319fecf9c1e9f23f4583608a1c87c9  tools/audit_minimal_models.py
bbf9f2dd80e80dfe18f13d4abc34c052229ea7146deb00e889a0276948006d9f  tools/audit_one_screening.py
6abd73a34f2ba613ff19b847341554045822c04a231a68d0c08a05f98deac4a0  tools/audit_regular_families.py
f979190e290b2e57649d01dc6ba0fcaf225ff21fb085e92431c370a2b4f0aeb8  tools/audit_stocco_comparison.py
1151440942f319d548965bc51a2cd0baa84b940a661735981a8b2b3afe887a98  tools/audit_top_layer.py
34c9a27ab97bb28b78f1c2e559c8dabf4bc5a2903d362ad43222f103c7910390  tools/direct_reconstruction.py
3f69e0f5a782cf9e23037907dbf38467fa7c5550750c5faf587cbddffc75b519  tools/exact_shapovalov.py
678ca0d3ab7450850b56cf3bbac583e22ae6395a3cea8d6e31d4e937d62448c3  irreducible/tools/audit_irreducible_torus.py
```
