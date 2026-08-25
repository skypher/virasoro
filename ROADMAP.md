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
  crossing scalar, and finite simple-pole term (confluence side).
- `tools/audit_grade10_direct.py --crossing-only`: independent intrinsic
  reconstruction of the one-dimensional second Smith layer and
  `gamma_10 = -1121229484375/192` from the exact 42-by-42 Gram matrix; this
  mode uses no confluence or generic-residue data.
- `tools/audit_confluent_recursion.py`: independent replay of the shifted
  Laurent recursion at grade two and the first two collision moments at
  grade four.
- `tools/audit_direct_principal_parts.py`: definition-side checks.  Exact
  reconstruction of `H_N`, `N <= 7`, as rational functions of the internal
  weight at two sample external weights, verifying the grade-3 and grade-4
  residue theorems, the complete grade-7 principal part (including the
  explicit `Theta_7`), the pole-order claims below grade 7, the grade <= 4
  collision-moment table, closed forms of `Q_4^E`, `Q_5^E`, and the
  intrinsic `gamma_7 = -700700` from an independent engine
  (`tools/direct_reconstruction.py`).
- `tools/audit_grade10_direct.py` (run via the parallel `make audit-deep`):
  the direct 42-by-42 computation at grade ten — kernel dimension 32,
  determinant valuation 33, intrinsic second crossing form, the
  level-8/level-6 residues, closed forms of `Q_8`, `Q_6`, and the complete
  grade-ten principal part including `gamma_10 = -1121229484375/192` and the
  explicit `Theta_10`.
- `tools/audit_stocco_comparison.py`: the imported identities (6.1) and
  (6.1a) at sample points, and agreement with Stocco's pole-free
  numerators — orders 2 and 3 identically in `b`, order 4 at the Ising
  point (`--full` also checks order 4 at generic points).
- `tools/audit_ising_characters.py`: the three irreducible Ising character
  expansions through grade 30, BGG side cross-checked against an
  independent free-fermion count.
- `paper.pdf`: clean build with no undefined references, layout warnings,
  or compilation errors.

Install the exact symbolic dependency with
`python3 -u -m pip install -r requirements-audit.txt`, run the standard checks
with `make audit`, the parallel grade-ten direct check with `make audit-deep`,
and rebuild the manuscript with `make pdf`.

## Supplementary extension

An explicit all-depth identification of every local Smith layer with every
term of the Ising embedding diagrams would strengthen the
representation-theoretic interpretation, but it is not used as a premise
of the finite recursion or the all-order equality theorem.  The grade-ten
principal part is now verified directly against the inverse-Shapovalov
definition, and the grade-ten second crossing form is independently
reconstructed from the exact Gram matrix.
