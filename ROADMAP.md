# Hard-target meter

Overall theorem progress: **100 / 100**.

This meter records closure of the user-requested fixed-`c` recursion,
all-order inverse-Shapovalov equality, and Ising consistency check.
The earlier route made an all-depth Smith/Jantzen classification a
dependency.  The collision-moment theorem removes that dependency:
classwise rational continuation proves finiteness and equality directly,
while the local Smith analysis remains a representation-theoretic
interpretation and audit.

| Bucket | Weight | Status | Closure evidence |
|---|---:|---|---|
| Fixed-`c` analytic foundation | 15 | Closed | `paper.tex`, Proposition “Exact collision classification,” Lemma “Large internal weight,” and Theorem “Finite coefficientwise pole expansion.” |
| Finite confluent recursion | 35 | Closed | `paper.tex`, Definitions “Shifted Laurent recursion” and “Collision moments,” including the valuation bound `M_{n,N}` and actual multiplicity `m_{n,N}`. |
| All-orders inverse-Shapovalov equality | 30 | Closed | `paper.tex`, Theorem “Pole-free Ising recursion and all-order equality”: classwise cancellation, finite constant-term formula, grade termination, and coefficientwise equality. |
| Higher-pole and Ising consistency checks | 20 | Closed | `paper.tex`, Theorems “Complete grade-ten principal part” and “The three Ising characters,” plus the exact replay scripts. |

## Main result

For a Kac label `a=(r,s)`, let `B_{a,N}(t)` be the recursively computed
shifted Laurent numerator at `b=2i/√3+t`, and let
`δ_a(t)=h_a(t)-λ_n` for its Ising collision class.  The fixed-central-charge
pole coefficient is

```text
A_{n,k,N}(d)
  = CT_t Σ_{a in C_{n,N}} B_{a,N}(t) δ_a(t)^(k-1).
```

The valuation bound in `paper.tex` makes this a finite jet calculation.
Summing these coefficients gives

```text
H_Δ^(1/2)(d|q)
  = 1 + Σ_n Σ_k A_{n,k}(d;q)/(Δ-λ_n)^k
```

coefficientwise in `q`.

## Verification evidence

- `tools/audit_low_levels.py`: exact Gram matrices, Ward matrices,
  singular vectors, crossing forms, fusion polynomials, and the grade-four
  recursive residue.
- `tools/audit_grade10_confluence.py`: exact Kac slopes, residue constants,
  grade-ten fusion factorization, second crossing scalar, and finite
  simple-pole term.
- `tools/audit_confluent_recursion.py`: independent replay of the shifted
  Laurent recursion at grade two and the first two collision moments at
  grade four.
- `tools/audit_ising_characters.py`: the three irreducible Ising character
  expansions through grade 15.
- `paper.pdf`: clean 18-page build with no undefined references, layout
  warnings, or compilation errors.

## Supplementary extension

An explicit all-depth identification of every local Smith layer with every
term of the Ising embedding diagrams would strengthen the
representation-theoretic interpretation, but it is not used as a premise
of the finite recursion or the all-order equality theorem.
