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

## 2026-11-16T14:02Z — Theorem 9.4 (main session)

`thm_level_ten_principal_part : Cited_KacDeterminant → Cited_HJSNormalizations →
Stmt_thm_level_ten_principal_part`; axioms `propext`, `Classical.choice`, `Quot.sound` only
(`runs/lean-check/ax94.log`). Same method as Theorem 8.5: Proposition 7.7 at `b₀`, `N = 10`,
`λ = h₀ = 1/16`, branches `(1,2)→(4,2)` and `(2,2)→(1,6)`, `C⋆ = {(1,2),(2,2)}` by `isingKey`;
the explicit values are generated by `scripts/gen_lean.py 10` and proved in Lean; the
double-pole coefficient `(D_{1,2}-D_{2,2})/(D_{1,2}-D_{4,2}) 𝒜_{1,2}𝒜_{4,2} P₂𝒫_{4,2}
= -192 P₂𝒫_{4,2}/1121229484375`. Verdict on the statement: faithful.

## 2026-11-16T14:48Z — Proposition 8.1 (main session)

`prop_level_seven_smith : Cited_KacDeterminant → Cited_VermaHomInjective → Cited_SingularUnique →
Cited_JantzenLayers → Stmt_prop_level_seven_smith`; axioms `propext`, `Classical.choice`,
`Quot.sound` only (`runs/lean-check/ax81.log`).

- Normal-ordering engine (Proofs/PBWEngine, PBWState): `negIns`, `posActAff`, `actN`, `negN`,
  `posN`, `opN` are computable functions on lists of words; `toVerma_actN`, `toVerma_negN`,
  `toVerma_opN`, `toVerma_posN_posOp` prove that they compute the Virasoro action exactly in
  the Verma module over any `ℚ`-algebra, through any ring homomorphism.  Their outputs on the
  explicit vectors are checked by `decide +kernel` over `ℚ` and over `ℚ[x]/(x³)` (`T3`, with the
  truncation `K⟦X⟧ →+* T3 K`).
- φ₅, φ₄, ξ₇ singular; ξ₇ = j_{ξ₂}(φ₅) = j_{ξ₃}(φ₄) (the two products agree as lists up to
  permutation).
- γ₇: the rows of `G₇(1/2, 1/2 + x)(ξ₇ + x v₁)`, over all 15 partitions of 7 (enumerated by
  `decWords` with a completeness proof), lie in `x²`; hence `G₀ξ₇ = 0`, `G₀v₁ = -G₁ξ₇`,
  `ξ₇ ∈ K₂`, and `γ₇ = -700700` for every admissible `v₁` (`cross2_indep`).  `v₁` was found by
  `scripts/gamma7.py` from engine output; Lean checks it.
- U₂ ∩ U₃: a lowest nonzero vector is singular (`isSingular_of_lowest`), pulls back along
  `j_{ξ₂}` to a singular vector of `M(1/2,5/2)` of level `N - 2 ∈ [1,4]` (`singular_pullback`,
  using `Cited_VermaHomInjective`), and the Kac determinant there is nonzero; at level 7
  `Cited_SingularUnique` gives `ℂ ξ₇`.
- Smith exponents: Theorem 5.7 gives `#(e ≥ 2) = dim((W⁺₂ + W⁻₂)₇) = 1` (levels 17, 7) and
  `#(e ≥ 3) = 0` (levels 25, 28); `Σ e = ord det = p(5) + p(4) = 12`; 15 exponents.
Verdict on the statement: faithful.

## 2026-11-16T14:57Z — Proposition 9.1 (main session)

`prop_level_ten_smith : Cited_KacDeterminant → Cited_VermaHomInjective → Cited_SingularUnique →
Cited_JantzenLayers → Stmt_prop_level_ten_smith`; axioms `propext`, `Classical.choice`,
`Quot.sound` only (`runs/lean-check/ax91.log`). Follows the paper's proof: ψ₈ ∈ M(1/2,33/16) and
ψ₆ ∈ M(1/2,65/16) exist (`exists_singular_of_det`: a vector of `ker G_n` with `det G_m ≠ 0`
for `m < n` is singular; Kac determinant with the labels (4,2), (1,6)); `χ₁₀ = j_{χ₂}(ψ₈)` is
singular of level 10 (`exists_embedding`, `isSingular_map`) and proportional to `j_{χ₄}(ψ₆)`;
`U₂ ∩ U₄` vanishes below level 10 (pullback to `M(1/2,33/16)` below level 8); Smith exponents
from Theorem 5.7 with `(p,p') = (3,4)`, `(r,s) = (1,2)`: `#(e ≥ 2) = 1` (levels 10, 14),
`#(e ≥ 3) = 0` (levels 24, 30), `Σ e = p(8) + p(6) = 33`, 42 exponents; `dim ker G₁₀ = 32`;
`[x⁻²]G₁₀⁻¹` maps into `K₂` (dimension 1) and is nonzero (pairing with a nonzero `u ∈ K₂`).
Verdict on the statement: faithful.

## 2026-11-16T15:22Z — Lemma 8.4 (main session)

`lem_regular_families : Cited_HJSNormalizations → Stmt_lem_regular_families`; axioms `propext`,
`Classical.choice`, `Quot.sound` only (`runs/lean-check/ax84.log`).

- `S₁, S₂`: `Sfun k c h Z Y` is the affine coefficient of `Z` in the engine's `posActAff k Y`,
  evaluated at `(c, h)`; `L_neg_expand` proves `L_k L_{-Y}|h⟩ = ∑_Z S_k L_{-Z}|h⟩` for any
  coefficient ring, given that the output words lie in `lexWords (m-k)` (checked by kernel).
- Determinants: `Bmat m c h` is exactly the matrix of the statement; over `ℚ` at `(1/2, h)` it
  has a permuted LU factorization `B σ = L U` (`scripts/luB.py`, checked in exact arithmetic
  there and by `decide +kernel` here), so `det B = sign σ ∏ U_ii`; all eight values agree with
  the table.  Naturality transfers the determinant to `ℂ`.
- Regularity: a normalized singular `p` over `ℂ(b)` solves `B_m(c(b),h(b)) p = e`
  (`Bmat_mulVec_singular`); the entries of `B_m` are regular at `b₀` with value `B_m(1/2,h)`,
  whose determinant is nonzero, so Cramer's rule in the subring of functions regular at `b₀`
  (`RegEvalK`, a base-field-generic version of `RegEval`) makes `p` regular there
  (`regular_of_B`).  The specialized vector satisfies all `S₁`, `S₂` rows, hence is singular
  (`L_pos_zero_of_L12`), and is the unique normalized singular vector (`unique_of_B`).  The
  same argument over `ℚ(b)` gives regularity of the family of `NormalizationIdentities`, so
  `normalization_at` yields `crossScalar = 𝒜⁻¹` and `torusForm = 𝒫` at `b₀` for it, which is the
  same vector.
Verdict on the statement: faithful; the table entries and the regularity conclusions match.

## 2026-11-16T16:11Z — Proposition 9.5 (main session)

`thm_level_ten_leading : Cited_KacDeterminant → Cited_HJSNormalizations →
Stmt_thm_level_ten_leading`; axioms `propext`, `Classical.choice`, `Quot.sound` only
(`runs/lean-check/ax95.log`).

- ψ₈ ∈ M(1/2,33/16) and ψ₆ ∈ M(1/2,65/16) are explicit (`scripts/psi.py` solves `B_m p = e`
  from engine data); the engine checks that `L_1, …, L_8` (resp. `L_6`) annihilate them.  By
  `unique_of_B` with the determinants of Lemma 8.4, every normalized singular `q₈`, `q₆` equals
  them.
- `χ₁₀ = ψ₈ χ₂ = ψ₆ χ₄`: both engine products agree with the 42-term list `x10Q` up to
  permutation.
- Torus polynomials: `identities_at_b0` (the regularity argument of Lemma 8.4 for the
  `NormalizationIdentities` family and `normalization_at`) gives `⟨q|V_d(1)|q⟩ = 𝒫_{r,s}(b₀,d)`;
  Lemma 9.3 identifies `𝒫_{4,2}(b₀,·) = P42`, `𝒫_{1,6}(b₀,·) = P16`.
- γ₁₀: as for γ₇, the 42 rows of `G₁₀(1/2,1/16 + x)(χ₁₀ + x v₁)` lie in `x²` (engine over
  `ℚ[x]/(x³)`), so `χ₁₀ ∈ K₂`, `G₀ v₁ = -G₁ χ₁₀`, and `γ₁₀ = -1121229484375/192` for every
  admissible `v₁` (`cross2_indep`).  `v₁` from `scripts/gamma10.py`.
- The leading coefficient: Theorem 9.4's principal part has double-pole coefficient
  `-192 P₂ 𝒫_{4,2}/1121229484375 ≠ 0`, so `poleOrder = 2` and `ppCoeff 2` is that coefficient,
  which equals `P₂𝒫_{4,2}/γ₁₀ = P₄𝒫_{1,6}/γ₁₀` (Lemma 9.3: `P₂ P42 = P₄ P16`).
Note: the paper derives the value of γ₁₀ by comparing its limit formula with Theorem 9.4; the
Lean proof computes γ₁₀ directly from the Gram matrix (the paper's independent check), and takes
the leading coefficient from Theorem 9.4.  Verdict on the statement: faithful.
