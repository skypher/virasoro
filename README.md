# Exact algebraic confluence for torus one-point Virasoro-block recursions

This repository contains the manuscript and exact-arithmetic audit code for
Leslie P. Polzer's paper *Exact algebraic confluence for torus one-point
Virasoro-block recursions*.

**[Read the current manuscript](paper.pdf)**

## Main result

At every fixed nonzero algebraic Coulomb-gas parameter, the paper gives a
finite coefficientwise construction of the eta-reduced torus one-point
Virasoro block at the corresponding central charge. Generic Kac-recursion
terms with a common limiting internal weight are combined along the exact
formal germ `b = b_star + t`. Their fixed-central-charge partial-fraction
coefficients are obtained as collision moments: constant terms of finite
sums of Laurent germs.

Separated pole sets establish classwise cancellation, while a valuation
majorant and backward precision rule give a finite Laurent-jet budget at
each level. Partial-fraction uniqueness identifies the result with the
inverse-Shapovalov definition of the meromorphic Verma-module block. The
Ising specialization includes exact level-seven and level-ten examples,
including the first double pole.

The result is coefficientwise in the nome and concerns the meromorphic
Verma-module block. It is not an intrinsic recursion in the specialized
representation category or a construction of irreducible minimal-model
traces at degenerate internal weights.

## Repository contents

- [`paper.tex`](paper.tex) — manuscript source.
- [`paper.pdf`](paper.pdf) — current compiled manuscript.
- [`tools/`](tools) — eight audit scripts and two shared exact-arithmetic
  libraries.
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

Run the standard exact suite:

```sh
make audit
```

Add the complete direct level-ten inverse-Shapovalov reconstruction:

```sh
make audit-deep
```

Set `VIRASORO_AUDIT_JOBS` to control the worker count used by the direct
level-ten reconstruction. Every successful identity is reported with a
`PASS` marker; a failed identity exits nonzero. See
[`AUDIT_MANIFEST.md`](AUDIT_MANIFEST.md) for the responsibility and
independence of each check.

## Build the manuscript

A PDFLaTeX installation with the standard packages used by `paper.tex` is
required.

```sh
make pdf
```

To generate the clean source archive prepared for arXiv:

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
