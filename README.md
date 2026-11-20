# Exact algebraic confluence for torus one-point Virasoro blocks and irreducible minimal-model traces

This repository contains two manuscripts by Leslie P. Polzer and their
exact-arithmetic audit code:

- *Exact algebraic confluence for torus one-point Virasoro blocks and
  irreducible minimal-model traces* — [`paper.tex`](paper.tex),
  **[PDF](paper.pdf)**;
- *Exact algebraic confluence and Jantzen pole orders for sphere four-point
  Virasoro blocks* — [`sphere/paper.tex`](sphere/paper.tex),
  **[PDF](sphere/paper.pdf)**.

## Torus paper

Sections 2-8 treat the meromorphic Verma-module torus one-point block. At
every fixed nonzero Coulomb-gas parameter `b_star`, the paper gives a finite
coefficientwise construction of the eta-reduced block at the corresponding
central charge. Generic Kac-recursion terms with a common limiting internal
weight are combined along the exact formal germ `b = b_star + t`; their
fixed-central-charge partial-fraction coefficients are collision moments,
constant terms of finite sums of Laurent germs. Collisions occur only when
`b_star^2` is rational.

At minimal-model charges the local Smith exponents of the Shapovalov matrix
are the dimensions of the Feigin-Fuchs embedding layers, which bounds every
pole order by the Jantzen depth `j_N(lambda)`; the top Jantzen layer gives the
leading Laurent coefficient. For an indeterminate external weight `d` (pole
orders over the field of rational functions in `d`) the bound is attained at
every minimal-model charge, interior Kac weight and level `N >= 1`; the proof
specializes to `d = h_{1,3}(b)` and `d = h_{1,-3}(b)` and uses a Feigin-Fuchs
Fock factorization with `ell`-adic valuation and ratio separation. At the
Ising charge the first double poles occur at levels seven, ten and eleven.

Sections 9-14 treat the traces over the irreducible quotient
`L(c_star, lambda)`. The normalized primary pairing descends to the irreducible
module exactly when `d` lies in the minimal-model fusion set, while the Verma
coefficients are regular at `lambda` for all levels on a larger reflected set.
For fusion insertions the irreducible trace is an alternating sum of Verma
blocks over the braided embedding diagram (a generalized Rocha-Caridi
identity) with explicit nonzero rational weights, so every coefficient of the
irreducible trace is computed exactly.

## Sphere paper

The sphere paper proves the large-internal-weight limit
`H_N(c, Delta, Delta_i) -> delta_{N,0}` of Zamolodchikov's elliptic
H-function for every central charge and external weights, the generic
Zamolodchikov recursion and fixed-`b_star` confluence for the sphere
four-point block, and the Jantzen pole-order bound, top-layer formula and
sharpness (for generic external weights) at minimal-model charges.

## Repository contents

- [`paper.tex`](paper.tex), [`paper.pdf`](paper.pdf) — torus paper.
- [`sphere/`](sphere) — sphere paper, notes, and its audit scripts
  (`sphere/tools/`).
- [`tools/`](tools) — thirteen audit scripts and two shared exact-arithmetic
  libraries for Sections 2-8 of the torus paper.
- [`irreducible/tools/`](irreducible/tools) — audit script for Sections 9-14 of
  the torus paper; `irreducible/paper.tex` is the separate draft those
  sections were merged from.
- [`lean/`](lean) — Lean 4 formalization of earlier parts of the torus paper
  (status in `lean/STATUS.md`).
- [`AUDIT_MANIFEST.md`](AUDIT_MANIFEST.md) — audit scope, commands, success
  conditions, and source hashes.
- [`ARXIV_ANCILLARY_README.md`](ARXIV_ANCILLARY_README.md) — instructions
  packaged with the arXiv ancillary files.
- [`requirements-audit.txt`](requirements-audit.txt) — pinned symbolic
  dependency.

## Reproduce the calculations

The audit environment uses CPython 3.12 and SymPy 1.12. Install the pinned
dependency with:

```sh
python3 -u -m pip install -r requirements-audit.txt
```

Torus paper, Sections 2-8 (standard suite, then the direct level-ten
inverse-Shapovalov reconstruction):

```sh
make audit
make audit-deep
```

Torus paper, Sections 9-14:

```sh
make audit-irreducible
```

Sphere paper:

```sh
make -C sphere audit
```

Set `VIRASORO_AUDIT_JOBS` to control the worker count used by the direct
level-ten reconstruction. Every successful identity is reported with a
`PASS` marker; a failed identity exits nonzero. See
[`AUDIT_MANIFEST.md`](AUDIT_MANIFEST.md) for the responsibility and
independence of each check of the torus paper. All of these are finite
checks; the proofs do not use them.

## Build the manuscripts

A PDFLaTeX installation with the standard packages is required.

```sh
make pdf
make -C sphere pdf
```

To generate the clean source archive of the torus paper prepared for arXiv:

```sh
make arxiv-bundle
```

The resulting archive is written to `dist/virasoro-arxiv-v1.tar.gz`. It
contains `paper.tex` and the audit package under `anc/`, without generated
TeX files or repository metadata.

## Contact

Leslie P. Polzer  
Independent Researcher  
[polzer@fastmail.com](mailto:polzer@fastmail.com)
