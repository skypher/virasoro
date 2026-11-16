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

Not yet reviewed: every other `Stmt_`, and the definitions `HN`, `Atilde`, `MhatC` beyond what
the statements above use.
