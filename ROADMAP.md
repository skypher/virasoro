# Hard-target meter

Overall theorem progress: **100 / 100**.

This meter records closure of the exact algebraic-confluence formula at
fixed `c`, all-order inverse-Shapovalov equality, and Ising consistency
check. The construction uses a formal off-critical germ; it is not an
intrinsic recursion formulated solely in the specialized category.
The earlier route made an all-depth Smith/Jantzen classification a
dependency.  The collision-moment theorem removes that dependency:
classwise rational continuation proves finiteness and equality directly,
while the local Smith analysis remains a representation-theoretic
interpretation and audit.

| Bucket | Weight | Status | Closure evidence |
|---|---:|---|---|
| Fixed-`c` analytic foundation | 15 | Closed | `paper.tex`, Proposition “Exact collision classification,” Lemma “Large internal weight,” and Theorem “Finite coefficientwise pole expansion.” |
| Finite confluent recursion | 35 | Closed | `paper.tex`, Definitions “Shifted Laurent recursion” and “Collision moments,” including exact bound `M_{n,N}`, a priori majorant `widehat M_{n,N}`, actual multiplicity `m_{n,N}`, and the backward Laurent-precision budget. |
| All-orders inverse-Shapovalov equality | 30 | Closed | `paper.tex`, Theorem “Pole-free Ising recursion and all-order equality”: classwise cancellation, finite constant-term formula, grade termination, and coefficientwise equality. |
| Higher-pole and Ising consistency checks | 20 | Closed | `paper.tex`, the grade-seven and grade-ten principal-part theorems and “The three Ising characters,” plus the exact replay scripts. |

## Main result

For a Kac label `a=(r,s)`, let `B_{a,N}(t)` be the recursively computed
shifted Laurent numerator at `b=2i/√3+t`, and let
`δ_a(t)=h_a(t)-λ_n` for its Ising collision class.  The fixed-central-charge
pole coefficient is

```text
A_{n,k,N}(d)
  = CT_t Σ_{a in C_{n,N}} B_{a,N}(t) δ_a(t)^(k-1).
```

The recursive valuation majorant and backward precision rule in `paper.tex`
supply an a priori finite jet budget.
Summing these coefficients gives

```text
H_Δ^(1/2)(d|q)
  = 1 + Σ_n Σ_k A_{n,k}(d;q)/(Δ-λ_n)^k
```

coefficientwise in `q`.

## Verification evidence

- `tools/audit_first_resonances.py`: the actual first collision at grade
  three and first embedding diamond at grade seven, including an independent
  15-by-15 fixed-`c` second crossing calculation.
- `tools/audit_low_levels.py`: exact Gram matrices, Ward matrices,
  singular vectors, crossing forms, fusion polynomials, and the grade-four
  recursive residue.
- `tools/audit_grade10_confluence.py`: exact Kac slopes, residue constants,
  grade-ten fusion factorization, generic-recursion evaluation of the second
  crossing scalar, and finite simple-pole term. It does not independently
  construct the 42-by-42 fixed-`c` crossing form.
- `tools/audit_confluent_recursion.py`: independent replay of the shifted
  Laurent recursion at grade two and the first two collision moments at
  grade four.
- `tools/audit_ising_characters.py`: the three irreducible Ising character
  expansions through grade 15.
- `paper.pdf`: clean build with no undefined references, layout
  warnings, or compilation errors.

Install the exact symbolic dependency with
`python3 -m pip install -r requirements-audit.txt`, run all checks with
`make audit`, and rebuild the manuscript with `make pdf`.

## Supplementary extension

An explicit all-depth identification of every local Smith layer with every
term of the Ising embedding diagrams would strengthen the
representation-theoretic interpretation, but it is not used as a premise
of the finite recursion or the all-order equality theorem.
