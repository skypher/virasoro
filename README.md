# Virasoro conformal blocks: large-weight limit, colliding poles, irreducible traces

This repository contains three manuscripts by Leslie P. Polzer and their
exact-arithmetic audit code:

- *Zamolodchikov's large-weight limit for sphere four-point Virasoro blocks*
  — [`sphere/paper.tex`](sphere/paper.tex), **[PDF](sphere/paper.pdf)**;
- *Colliding poles of Virasoro conformal blocks at rational central charge*
  — [`paper.tex`](paper.tex), **[PDF](paper.pdf)**;
- *A generalized Rocha--Caridi formula for torus one-point traces in minimal
  models* — [`irreducible/paper.tex`](irreducible/paper.tex),
  **[PDF](irreducible/paper.pdf)**.

## Large-weight limit

The paper proves Zamolodchikov's limit `H_N(c, Delta, Delta_i) -> delta_{N,0}`
as `Delta -> infinity` for the elliptic coefficients of the sphere four-point
block, for every central charge and all external weights.  The proof is a
saddle-point computation in a Feigin-Fuchs oscillator realization.

## Colliding poles

At rational `b^2` the poles of the residue recursions collide.  For the torus
one-point block (Part I) and the sphere four-point block (Part II), and every
fixed nonzero `b_star`, the principal part of each coefficient at each Kac
weight is a sum of constant terms of finite Laurent expansions in
`b - b_star` of the generic residue data.  At interior minimal-model weights
the pole order is bounded by the Jantzen depth, the coefficient at that order
is given by the top Jantzen layer, and the bound is attained for
indeterminate external weights.

## Irreducible traces

For a primary insertion at an interior weight of a minimal model, the torus
pairing descends to the irreducible module exactly when the insertion weight
is in the fusion set.  For those weights a generalized Rocha-Caridi identity
writes the irreducible trace as an alternating sum of Verma blocks over the
braided embedding diagram, with explicit rational weights.

## Repository contents

- [`sphere/`](sphere) — large-weight paper, notes, and the sphere audit
  scripts (`sphere/tools/`; `audit_large_delta.py` for the large-weight paper,
  the others for Part II of the colliding-poles paper).
- [`paper.tex`](paper.tex), [`paper.pdf`](paper.pdf) — colliding-poles paper.
- [`tools/`](tools) — thirteen audit scripts and two shared exact-arithmetic
  libraries for Part I of the colliding-poles paper.
- [`irreducible/`](irreducible) — traces paper and its audit script
  (`irreducible/tools/`).
- [`lean/`](lean) — Lean 4 formalization of the three papers: every numbered
  result is proved from the cited inputs (`Cited_*`); index of current paper
  numbers in `lean/PAPER_MAP.md`, review log in `lean/REVIEW.md`.
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

Colliding-poles paper, Part I (standard suite, then the direct level-ten
inverse-Shapovalov reconstruction):

```sh
make audit
make audit-deep
```

(`make check` and `make check-long`, the names used in the paper, run the same two suites.)

Traces paper:

```sh
make audit-irreducible
```

Large-weight paper and Part II of the colliding-poles paper:

```sh
make -C sphere audit
```

Set `VIRASORO_AUDIT_JOBS` to control the worker count used by the direct
level-ten reconstruction. Every successful identity is reported with a
`PASS` marker; a failed identity exits nonzero. See
[`AUDIT_MANIFEST.md`](AUDIT_MANIFEST.md) for the responsibility and
independence of each check. All of these are finite
checks; the proofs do not use them.

## Build the manuscripts

A PDFLaTeX installation with the standard packages is required.

```sh
make pdf
make -C sphere pdf
make -C irreducible pdf
```

To generate the clean source archive of the colliding-poles paper prepared for
arXiv (it also carries the traces audit):

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
