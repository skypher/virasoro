# Statement review of the Lean formalization

Kept by the main session; the formalization agent does not edit this file.

## 2026-11-16T09:04Z — labelled statements against paper.tex at d823b62

Machine checks (main session, independent of the agent's logs):
- `lake build` green; no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by` in
  `Virasoro/` (log `runs/lean-resume/verify-build.log`, `runs/lean-resume/forbidden.log`).
- For each of the 11 labelled theorems, `example : Stmt_<name> := <name>` elaborates, and
  `#print axioms` gives only `[propext, Classical.choice, Quot.sound]`; the same holds for the
  seven conditional theorems (`runs/lean-check/Check.lean`, `runs/lean-check/check.log`).

Statement fidelity (each `Stmt_` read against the paper's statement):

| Paper result | Verdict | Note |
|---|---|---|
| Lemma 2.4 `lem:polynomial-entries` | faithful relative to `gram`/`torus` | `gram`, `torus` are the normal-ordering model; they are the matrices of Definition 2.2 only once `Stmt_def_matrices` is proved |
| Prop 3.2 `prop:minimal-collisions` | faithful | weight formula stated for all integer labels (stronger, harmless) |
| Cor 3.3 `cor:ising-classes` | faithful | all five clauses; "finitely many classes" read as finitely many weights |
| Lemma 5.1 `lem:smith` | faithful | Smith exponents as a multiset via `IsSmith` (U G V diagonal with unit determinants) |
| Prop 5.2 `prop:transverse-residue` | faithful | ι β⁻¹ ι* encoded by its defining property |
| Prop 5.3 `prop:two-step-residue` | faithful | all clauses, including choice-independence and symmetry of β₂ |
| Cor 5.4 `cor:det-overcounts` | faithful relative to `gram` | same caveat as Lemma 2.4 |
| Lemma 6.4 `lem:no-generic-shifted-pole` | faithful | regularity of 𝒜 read as non-vanishing of every factor p b + q b⁻¹ |
| Lemma 7.2 `lem:shifted-valuation-bound` | faithful | `SG`, `WG`, `piG`, `sigmaG` match Definition 7.1 and Lemma 7.2 term by term |
| Lemma 7.4 `lem:precision-budget` | faithful | `PrecisionRule` encodes both parts, with the a priori valuation bounds as reading convention |
| Lemma 7.5 `lem:collision-pole-support` | faithful | finiteness read as stabilization of partial sums; K⋆ realized inside ℂ(d) |

Conditional hypothesis `GenericRecursionUniform` (Statements/Sec6.lean): a correct reading of
Proposition 6.5 as an identity of rational functions of b over ℚ, valid in every field of
characteristic 0 away from finitely many polynomial roots; this is how the paper's proof of
Theorem 4.3 uses Proposition 6.5, and the germ b⋆ + t is not such a root. The conditional
theorems are therefore not vacuous.

Earlier: `Stmt_thm_jantzen_smith` checked against Theorem 5.7 (2026-11-16, before d823b62's
wording changes, which did not touch Theorem 5.7).

## 2026-11-16T10:41Z — second round, paper.tex at d823b62

Machine checks (main session): `lake build` green after the `maxSynthPendingDepth = 3` lakefile
change; no forbidden tokens (`runs/lean-check/forbidden2.log`); all 15 labelled
`example : Stmt_<name> := <name>` checks elaborate and `#print axioms` gives only
`[propext, Classical.choice, Quot.sound]` for those 15 and for `thm_general_partial_fractions`,
`singular_crossing`, `not_stmt_lem_singular_crossing` and `thm_general_confluence`
(`runs/lean-check/check2.log`).

| Paper result | Verdict | Note |
|---|---|---|
| Def 2.2 well-posedness `Stmt_def_matrices` | faithful | unique vacuum functional and primary pairing over any commutative ℚ-algebra; `gram`, `torus` are their matrix elements. This removes the caveat on Lemma 2.4 and Cor 5.4 |
| Lemma 4.1 `lem:large-weight` | faithful | limits along `Bornology.cobounded ℂ` for complex `c, d` |
| Lemma 5.6 `lem:jantzen-smith` | faithful | the submodule and radical clauses carry the hypothesis `∀ N, det ≠ 0`, which always holds (`gramPoly_det_ne_zero`) |
| Lemma 5.9 `lem:singular-factorization` | faithful | `d` complex; the paper's identity is polynomial in `d` |
| Thm 4.2 `thm:general-partial-fractions` | proved conditional on `Cited_KacDeterminant`; statement not yet reviewed | |

Paper issue found by the agent and checked by the main session: Lemma 5.10
(`lem:singular-crossing`) fails at level 0 (χ = |h₀⟩ gives β_χ = 0, while
dG₁/dh = 2), machine-checked by `not_stmt_lem_singular_crossing`. Every use in the paper has
level rs ≥ 1. The paper now states `ℓ ≥ 1` and says in the proof why the image lies in the
radical; `Stmt_lem_singular_crossing` must be re-frozen with `1 ≤ ℓ`, after which
`singular_crossing` should discharge it.

## 2026-11-16T12:55Z — third round, paper.tex at 9aa415f

Machine checks (main session): `lake build Virasoro` green; no forbidden tokens
(`runs/lean-check/forbidden3.log`); all 23 labelled `example : Stmt_<name> := <name>` checks
elaborate; `#print axioms` gives only `[propext, Classical.choice, Quot.sound]` on all 33 lines
(`runs/lean-check/check3.log`). The conditional theorems take exactly these hypotheses:
`thm_general_partial_fractions : Cited_KacDeterminant → …`;
`thm_jantzen_smith : Cited_JantzenLayers → …`;
`prop_imported_normalizations : Cited_HJSNormalizations → …`;
`prop_generic_recursion`, `genericRecursionUniform`, `thm_general_confluence_of_cited`,
`cor_ising_confluence_of_cited`, `cor_class_regular_of_cited`, `prop_identity_verma_of_cited`,
`prop_two_branch : Cited_KacDeterminant → Cited_HJSNormalizations → …`.

Re-encoded cited input. `Cited_HJSNormalizations := NormalizationIdentities` (changed since
9aa415f). It asserts, over ℚ(b): existence and uniqueness of the singular vector of level rs in
M(c(b), h_{r,s}(b)) with L_{-1}^{rs}-coefficient 1, and the identities (6.1)
`crossScalar = 𝒜_{r,s}⁻¹` and (6.2) `torusForm = 𝒫_{r,s}` for every d ∈ ℚ(b). `crossScalar` is
the h-derivative of the Shapovalov norm with fixed coordinates (Lemma 5.10's β_χ) and
`torusForm` is uᵀρ_N v. Verdict: not stronger than the paper's Proposition 6.2; the continuation
clause of Prop 6.2 is proved, not cited. Documentation point: existence and uniqueness of the
normalized vector come from Kac/Feigin–Fuchs and Iohara–Koga Prop 5.1, not from
Hadasz–Jaskólski–Suchanek; the docstring should name those sources as well.

| Paper result | Verdict | Note |
|---|---|---|
| Lemma 5.10 `lem:singular-crossing` (re-frozen with `1 ≤ ℓ`) | faithful to the corrected lemma | ω(P) L_Y and L_{-Y'} P encoded as `gramWord` on concatenated words with fixed coordinates |
| Prop 6.2 `prop:imported-normalizations` | faithful | `ImportedNormalizations` = the two identities plus the continuation clause |
| Cor 7.6 `cor:class-regular` | faithful | negative t-coefficients of `Gclass` vanish |
| Prop 7.7 `prop:two-branch` | faithful | `TwoBranchHyp` = hypotheses (i)–(iii); `Tterm` = T_i; `finitePart` is the constant Laurent coefficient, equal to the paper's Q_i whenever H has at most a simple pole at z_i, which (i) guarantees |
| Prop 11.1 `prop:identity-verma` | faithful | H₀ = 1 and H_N = 0 for N ≥ 1 at d = 0 |
| Props 5.11, 5.13, 5.14, Thms 5.12, 5.15, Lemmas 8.3, 9.3 | constants as printed | spot check of 28/9, −105/8, 140/9, 16Δ−1, 13475/648, the residue polynomial over 40425, 700700, 1121229484375, 32035128125, 320945625, the β₄ entries, E₂, P₄; the theorems are kernel-checked |

Not yet reviewed in full: Thm 4.3's complete statement (read in part on 2026-11-16), Cor 4.4,
Thm 4.2, the remaining Ising statements of Sections 8, 9, 11, and the definitions `HN`,
`Atilde`, `MhatC` beyond what the statements above use.

## 2026-11-16T13:55Z — Theorem 8.5 (main session)

`thm_level_seven_principal_part : Cited_KacDeterminant → Cited_HJSNormalizations →
Cited_JantzenLayers → Stmt_thm_level_seven_principal_part`; axioms `propext`, `Classical.choice`,
`Quot.sound` only (`runs/lean-check/ax85.log`). The proof follows the paper: Proposition 7.7 at
`b₀`, `N = 7`, `λ = 1/2`, branches `(2,1)→(1,5)` and `(1,3)→(4,1)`; the hypotheses (i)–(iii) are
checked from the Ising weights (`isingKey`) and the jets. `T_i` is computed from the 1-jets of
`𝒜_{r,s}`, `𝒫_{r,s}` and the 2-jet of `ζ` at `b₀` (`Tterm_b0`): with `ḣ_{r,s} = β D_{r,s}`,
`D_{r,s} = (7 - 16r² + 9s²)/32`, and `ζ̈/2 = e_κ - e_τ`, `e_{r,s} = ((1-r²) + 27(1-s²)/16)/4`,
`T = 𝒜_κ𝒜_τ𝒫_κ𝒫_τ((σ_κ + σ_τ)/c + 3e/(4c²))`, where `β = b₀` cancels through `β² = -4/3`.
The explicit values (`genAIndex` sets, `σ_𝒜`, `𝒫` as products of `λ_n - d`, `𝒫 σ_𝒫` as
polynomials) are generated by `lean/scripts/gen_lean.py 7` and each is proved in Lean
(`decide`, `norm_num`, `field_simp`, `ring`); the generator only writes the statements.
`scripts/theta_check.py` confirms with sympy that the same formula reproduces (A.1) and (A.2).
The pole order 2 follows from the principal part (`poleOrder_eq_two_of_PP`), since the
double-pole coefficient `-E₂ 𝒫_{1,5}/700700` is nonzero. Verdict on the statement: faithful;
`Θ₇` is defined as `T₁ + T₂` and its factored form is the first conjunct.
