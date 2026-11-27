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

## 2026-11-21T15:06Z — statements of paper.tex Sections 1–8 at 70bac53 (phase A)

Machine checks (main session): `lake build Virasoro` green (`logs/A-build-all-2.log`); no
`sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `Paper label` in the new files
(`../runs/lean2/forbidden.log`).  The 16 statements marked unchanged were compared with their
text at 803f1aa (`../runs/lean2/stmt_diff.log`); the differences are rewording and layout only
(Thm 4.3 moves `Ã = A ∈ ℚ(b⋆²)[d]` into the display; Prop 6.2 adds the level and the Iohara–Koga
citation for existence and uniqueness).  Their earlier verdicts stand.

| Paper result | Verdict | Note |
|---|---|---|
| Lemma 5.1 `V2.Stmt_lem_smith` | faithful | |
| Lemma 5.4 `Stmt_lem_top_coefficient` | faithful | (i) adds membership of `L_{-n}u`, `L_n v` in the layers, which the paper's proof states and the identity needs; (ii) `ι(B^k)⁻¹ι^*` by its defining property; (iii) `cross1 G v u = vᵀG₁u`, `cross2 G v u u₁ = vᵀ(G₂u+G₁u₁)` checked against `Smith.lean` |
| Lemma 5.7 `Stmt_lem_singular_degree` | faithful | |
| Thm 5.9 `Stmt_thm_top_layer` | faithful | every family with the properties of Thm 5.8; τ/γ is invariant under rescaling of `w`, so the choice is immaterial; the limit as pole order ≤ k plus the `(Δ-λ)^{-k}` coefficient is equivalent |
| Cor 5.10 `Stmt_cor_top_layer_sharp` | faithful | |
| Lemma 6.5 `Stmt_lem_d_derivatives` | faithful | the added clause (Gram determinants nonzero over ℚ(b)(Δ)) is what makes `H_N` defined there |
| Lemma 6.6 `Stmt_lem_regular_everywhere` | faithful | "𝒜 regular" read as no factor vanishing: every factor of 𝒜 (`genA`) is in the denominator, so this is exact |
| Prop 6.7 `Stmt_prop_layer_coefficients` | faithful | cross-multiplied by γ; equivalent since γ ≠ 0 (Thm 5.9) |
| Prop 6.8 `Stmt_prop_h13_nonvanishing` | faithful | `c⋆ = 1 - 6(p'-p)²/(pp')`, `d₁ = -1 + 2p/p'`, `d₂ = 2 + 2p/p'` checked from `t⋆ = -p'/p`; the Lipschitz clause adds that the four values are units, which the paper's proof states and the quotient needs, and is then equivalent |
| Prop 6.9 `Stmt_prop_two_term_criteria` | faithful | |
| Prop 8.1 `Stmt_prop_ising_double_poles` | faithful | the levels 7, 10, 11 are ℓ⁻₂, ℓ⁺₂, ℓ⁻₂ of the table; normalization `a_w = 1` matches the monic τ |

Approved for proving.  Docstring numbers in `Statements/Sec4`, `Sec5a`, `Sec6`, `Sec7` stay at
803f1aa until the next full rebuild (the STATUS table has the current numbers).

## 2026-11-21T15:12Z — statements of sphere/paper.tex and of paper.tex Sections 9–13 (phase A)

| Paper result | Verdict | Note |
|---|---|---|
| sphere Def 2.1 `Stmt_def_sphere_block` | faithful | `IsThreePoint` for all `u` via `L₀` is the linear extension of the homogeneous rule; `Y.word` is decreasing and `neg` applies `L_{-y₁}⋯L_{-y_r}`, matching the sphere paper's `L_{-Y}` |
| sphere Def 2.2 `Stmt_def_H_series` | faithful | θ₂⁴ = 16qψ⁴ with ψ = ∑ q^{n(n+1)}; Φ̃ factors and exponents checked (Δe 1, Δe 2 = Δ₂, Δ₃) |
| sphere Thm 3.1 `Stmt_thm_large_delta` | faithful | junk values of `RatFunc.eval` at poles are avoided along `cobounded`; the degree form at every complex `(c,Δ_i)` is equivalent to the form over ℚ[c,Δ_i] |
| sphere Lemma 4.2 `Stmt_lem_3pt_factor` | faithful | `L₀`-eigenvector of eigenvalue `h+ℓ` is the level-ℓ space |
| sphere Prop 4.3 `Stmt_prop_imported` | faithful | `fusP` checked: the (j,l)·(−j,−l) product is ((A−B+β²)²−4Aβ²)/16, the (0,0) factor Δ_b−Δ_a; half-set `j > 0 ∨ (j = 0 ∧ l > 0)` |
| sphere Prop 4.4 `Stmt_prop_generic_recursion` | faithful | the exceptional set is chosen before `b` and the `Δ_i` |
| sphere Lemma 4.6 `Stmt_lem_precision_budget` | faithful | same reading as torus Lemma 7.4 |
| sphere Thm 4.7 `Stmt_thm_confluence` | faithful | (iii) as `ℬ_N = Q + ∑ PP_λ ℬ_N`, `deg Q = N` |
| sphere Thm 5.1, 5.3, 5.4, 5.5 | faithful | `topTermSph` uses (Δ₄,Δ₃) and (Δ₁,Δ₂) as in (2.2); scale-invariant |
| sphere Lemma 5.2 `Stmt_lem_pi_factorization` | faithful, with excess | (iii) asserts the hyperplane constants are integers; the paper leaves `c` unqualified, and its proof gives `c = lp − jp'`.  The excess strength is noted; its consumer (Thm 5.4) uses only the absolute-value form |
| sphere Props 6.1, 6.2 | faithful | levels for (2,3) checked: 1, 2, 5, 7; `fusP` is even in `b` |
| Thm 9.1 `Stmt_thm_descent_regularity` | faithful | `orbitSet` is invariant under (r,s) ↦ (p−r,p'−s) (n₀ ↦ −n₀, n₁ ↦ 2pp'−n₁) |
| Thm 9.2 `Stmt_thm_first_layer_ratio` | faithful | "generic" as `b² ∉ ℚ`: both sides are rational in `b`, and at irrational `t` no Γ argument is a pole (arguments `1+R+(j±S)/t`, `1+(R+i)t±S+m`) |
| Thm 9.3 `Stmt_thm_gen_rocha_caridi` | faithful | `arrowLabel` is invariant under `n_μ ↦ −n_μ`, so starting Ω from node (+,0) is immaterial |
| Cor 9.4 `Stmt_cor_collision_free` | faithful | the last clause is the reading of "evaluated directly … by the unmodified truncated recursion" |
| Lemma 10.1, Prop 10.2, Lemma 10.3 | faithful | 10.3(i) quotient clause as simplicity of `U(Vir₋)w^±_i / J^{i+1}`; 10.3(iv) `hT` checked against (10.3) |
| Lemma 11.1, Prop 11.2, Lemma 11.3 | faithful | 11.2(i) Ward identity with `Δ₁ = Δ₂ = μ` has the factor `N₁ − N₂ + nd` |
| Prop 12.1 `Stmt_prop_bgg_cocycle` | faithful | the box ratio equals ∏_{B₁∖B₀}/∏_{B₀∖B₁} after the shift; the powers of `p` cancel since the two differences have equal size |
| Lemma 13.1 `Stmt_lem_degenerate_quotient_t` | faithful | both labellings of ν₁, ν₂ |

All approved for proving.  Sphere Lemmas 3.2–3.7 are not frozen yet; the representation choices
for them were fixed by the main session (`../runs/lean2/brief-phaseB.md`, section "Sphere §3").

Phase B1 so far: `lem_smith_v2` (Lemma 5.1) carries a label and its `example` check; Lemma 5.7
is reduced to `Stmt_sub_singular_ones_coeff` (no label).  Build `logs/B1-build-2.log` green.

## 2026-11-21T17:20Z — sphere Lemmas 3.2 and 3.5 (statements), run-4 reductions

| Paper result | Verdict | Note |
|---|---|---|
| sphere Lemma 3.5 `Stmt_lem_bergman_det` | faithful | `detInvSqrt` is the paper's trace-exponential definition (l.864–865); the truncation to `n` indices and `k ≤ n` is exact at `z^n`, since row `m` of `M(z)` has order `m`; `Bgf` is (3.4); M(z)² agrees with the proof's M₁M₂ |
| sphere Lemma 3.2 `Stmt_lem_fock_verma` | change requested | (i), (ii) faithful: operators (3.2) checked term by term; `fockBil (conj G_N) F_N` is the Hermitian pairing of the (Δ₄,Δ₃) and (Δ₁,Δ₂) solutions, as in the proof; "irreducible" read as det G_N ≠ 0 for all N.  (iii) is weaker than the paper: the paper fixes `N` in the preamble and concludes Theorem 3.1 at that `N` from the limit at that `N`; the frozen form assumes the limit for every `N`.  Restate per level: a `LargeDeltaAt N` with the body of Theorem 3.1 at `N`, a proof that `Stmt_thm_large_delta ↔ ∀ N, LargeDeltaAt N`, and (iii) as `∀ N, (limit at N) → LargeDeltaAt N` |
| `Cited_FeiginFuchsOperators` | faithful | Virasoro relations with `c = 1+24μ²` and `l_k† = l_{-k}` at real parameters, as cited at l.428, 443–444 |

Lemma 3.3 encoding (main-session decision): (iii) stays existential, as printed.  𝓘₀ and
Φ_c^raw get Lean definitions that follow the proof of Lemma 3.3 (l.694–711: 𝓘₀ the saddle value,
Φ_c^raw = 2S_c^{(2)}(σ_*) + Ψ₁).  Lemmas 3.4(iii) and 3.7 are stated for these definitions
(reading convention: "the 𝓘₀, Φ_c^raw of Lemma 3.3 are those its proof constructs").  A working
theorem proves the limit formula (3.5) for these definitions; the existential form follows.

Run 4 (no labelled theorem): reductions of Props 6.7, 6.9, Cor 5.10 and Prop 8.1 to frozen
sub-statements, plus proved supporting lemmas.  By the scaffold-depth rule of lean.md the next
run closes leaves before any further decomposition.

## 2026-11-21T18:11Z — run 5 results, Lemma 3.2(iii) restatement, label convention

- Sphere Lemma 3.2(iii) restated per level (`LargeDeltaAt N`, `Stmt_thm_large_delta` is
  `∀ N, LargeDeltaAt N` by definition): faithful.  Lemma 3.2 approved for proving.
- Checked by the main session (`../runs/lean2/checkE5.log`): frozen types and axioms
  [propext, Classical.choice, Quot.sound] of `prop_ising_double_poles_of_cited`,
  `Sphere.def_sphere_block`, `Sphere.lem_3pt_factor`, `Sphere.def_H_series`,
  `Sphere.prop_imported_of_cited`, `Sphere.lem_precision_budget`.
- Prop 8.1 route: Lean takes γ₇, γ₁₀ from the PBW computation and γ₁₁ from Prop 7.7, where the
  paper takes γ = −[d²]τ/ρ² from Prop 6.7 (paper.tex l.1768–1773).  The statement is the
  paper's; the proof differs because Prop 6.7 is not yet formalized.  When Prop 6.7 lands, a
  proof along the paper's route can replace it.
- Label convention: a theorem whose only hypotheses are `Cited_*` inputs that the paper cites
  at the corresponding step proves the full result and carries the `Paper label` line.
  Labels added to `lem_d_derivatives_of_cited`, `lem_regular_everywhere_of_cited`,
  `thm_top_layer_of_cited` (build `logs/main-build-labels.log` green).

## 2026-11-21T18:41Z — sphere Lemmas 3.3, 3.4, 3.6, 3.7 (statements); run 6 results

| Paper result | Verdict | Note |
|---|---|---|
| sphere Lemma 3.3 `Stmt_lem_lambda_expansion` | faithful | (i) via the unique Ward solution over ℂ(λ); `Slam` coefficient λ^{|α|-2}[u^α] log F matches S = λ⁻² log F(λσ); (ii) S0's off-diagonal coefficients B_{mn}+B_{nm} match the ordered double sum; the universal series are chosen before (μ,Δ); (iii) existential as printed, with Δe 0 + Δe 3 = Δ₁ + Δ₄ |
| sphere Lemma 3.4 `Stmt_lem_saddle` | faithful | `tcoef n m = binom(2m,m−n)/4^m` is [w^{−n}]((1+w)²/(4w))^m; the stationarity equations are ∂/∂σ_m and ∂/∂σ̄_m of the functional, with Ã = −A and B̃ = B; Ω's x^m coefficient defines a_m, so the claims are Ω₀ = 1 and Ω_{−m} = a_m z^m |
| sphere Lemma 3.6 `Stmt_lem_ext_exponents` | faithful | consistent with 3.4: 2 log θ₄^{−2} = −4 log θ₄ |
| sphere Lemma 3.7 `Stmt_lem_central_charge` | faithful | both printed equalities, with z/(16q) = R⁻¹ |
| `Sphere.Cited_JacobiIdentities2` | faithful | the ₂F₁ and log-derivative identities of (2.3)–(2.4) as formal series |

Definitions: `I0def` takes, at each z-coefficient, a finsum over m that is finite exactly when
ord(σ_mσ̄_m) ≥ 2m, which holds at every saddle point (both stationarity equations make σ_m and
σ̄_m divisible by z^m); it is used only at saddle points.  `Psi1` is ½ Var of the linear
exponent with the covariance blocks of Q(z)⁻¹ (paper l.656–661, 698–706): Cov(U,U) =
z^{m+n}·½K₂₁M₂D⁻¹, Cov(U,V) = z^m·½K₂₁D⁻¹, Cov(V,V) = ½K₁₂M₁D⁻¹; its leading term z^m/(2m)
agrees with the paper's Cov(U_m,V_m).  The N×N truncation is exact at z^N.
`IsExpansionData` determines S̃^{(1)}, S_c^{(2)}, S_j^{(2)} uniquely, and Lemma 3.3 asserts that
such data exist, so Lemmas 3.6 and 3.7 are not vacuous.

All four approved for proving.  Run 6 results checked (`../runs/lean2/checkR6.log`): sphere
Thm 5.1 `thm_jantzen_bound_of_cited` (labelled) and the reduction `thm_top_layer_of_sub`.

## 2026-11-21T19:07Z — run 7 results

Checked by the main session (`../runs/lean2/checkR7.log`): sphere Thm 5.3
`thm_top_layer_of_cited` and sphere Lemma 5.2 `lem_pi_factorization_of_cited` have their
frozen types and the axioms [propext, Classical.choice, Quot.sound].  Lemma 5.2's hypotheses are
the cited inputs of Prop 4.3 and Iohara–Koga Prop 5.1 (sphere l.1529), so it is labelled under the
convention.  In 5.2(ii) the Lean proof checks that the push-forward is normalized, by reading the
L₋₁-coefficient off the top Δ_b-coefficient of the three-point scalar; the paper's "yields
w^±_k" leaves this check to the reader.  The proof does not need injectivity of the embedding.

## 2026-11-21T19:41Z — run 8 result

Sphere Lemma 3.2 `lem_fock_verma_of_cited` checked (`../runs/lean2/checkR8.log`): frozen type,
axioms [propext, Classical.choice, Quot.sound].  Hypotheses: the Feigin–Fuchs operators (cited at
sphere l.428, 443–444) and the Kac determinant.  The sphere paper uses the Kac determinant at
l.472–480 and l.495 but cites it nowhere (grep).  This is a citation gap in the paper; the
mathematics is unaffected.  Labelled, with the paper fix recorded in receipt.md: cite the Kac
determinant (Iohara–Koga Thm 4.2, as the torus paper does) at those lines in the prose-edit pass.

## 2026-11-21T21:04Z — run 10 results

Sphere Lemma 3.4 `lem_saddle_of_cited` checked (`../runs/lean2/checkR10.log`): frozen type,
axioms [propext, Classical.choice, Quot.sound]; frozen statements and cited inputs unchanged
since 5cdc8e6; no forbidden tokens in the new modules; full build green (`logs/D2-build-all.log`).
Hypotheses: `Cited_JacobiIdentities` and `Cited_JacobiIdentities2`, the identities (2.3)–(2.5)
cited at sphere l.348.  The proof uses (2.4) at l.802 by reference and (2.3) at l.821–822
without one (H(1) = (₂F₁√(1−z))⁻¹ = θ₄⁻², H(−1) = ₂F₁⁻¹ = θ₃⁻²).  The citation is in the paper,
so the label stands under the convention; the missing `\eqref{eq:jacobi-1}` at l.822 goes to
the prose-edit pass (receipt.md).

Route differences in Lemma 3.4(iii), with the paper as authority (lean.md "Paper first"):
- the saddle-point equations are checked from the closed form B(p,q) = −q∂_q(√(1−q)D(p,q)),
  where the paper derives them from the Wiener–Hopf identity (3.6) (l.766–800);
- 1 − g_*(±1) come from closed forms of ∑nψ_n and ∑n(−1)ⁿψ_n, where the paper continues (3.6)
  to an annulus and evaluates at w = ±1 (l.812–822).
The formal setting does not force either difference: at each order in z, 1 − g_*(w) is a
polynomial in w (t_{*,n} = O(zⁿ)) and H(w) is a Laurent polynomial in w, so (3.6) and its
evaluation at w = ±1 can be stated and proved coefficientwise in z.  The statement-level result
is accepted; replacing these two sub-proofs by the paper's argument is queued as a route repair
together with the Prop 8.1 repair (brief, order of work).

Sphere Lemma 3.5: `lem_bergman_det_of_first` derives the second equality from the first and
(2.3); no label.  The first equality is open in Lean.  The paper's proof (l.835–970) is
coefficientwise complex analysis in x₁, x₂ (Cauchy bounds, normal convergence, continuation to
ℙ¹, Liouville, contour integrals); Mathlib has Liouville, circle integrals, Cauchy estimates and
removable singularities, so that route is the one to translate.

## 2026-11-21T22:15Z — run 11 results (sphere Lemma 3.5)

Checked by the main session (`../runs/lean2/checkR11.log`): `sub_bergman_residue :
Stmt_sub_bergman_residue` and the reduction `lem_bergman_det_of_liouville_zero_mode (hJ2) (hL :
Stmt_sub_bergman_liouville) (hZ : Stmt_sub_bergman_zero_mode) : Stmt_lem_bergman_det`, axioms
[propext, Classical.choice, Quot.sound]; frozen statements and cited inputs unchanged since
28ad362; no forbidden tokens; build green (`logs/H6-build-all.log`, 3615 jobs).  No label.

Sub-statements, checked against sphere/paper.tex:
- `IsWFormula Cz` (l.925–929): on 0 < |x₁|, |x₂| < 1, x₁ ≠ x₂, each z-coefficient of W_no
  converges and W = S/(Y₁Y₂(x₁−x₂)²) + 2C/(Y₁Y₂).  S matches l.921 term by term.
  1/(Y₁Y₂) = −(x₁x₂√(1−x₁)√(1−x₂))⁻¹(1−z/x₁)^{−1/2}(1−z/x₂)^{−1/2}, from
  Y = x√(1−z/x)√(x−1) with one branch of √(x−1) = ±i√(1−x) for both factors; the principal
  branch of √(1−x) is the analytic one on the unit disc.  Order z⁰ test by hand: M₁ = O(z), so
  [z⁰]W = (x₁−x₂)⁻² − B(x₁,x₂)/(x₁x₂), and regularity at x₁ = 0 forces C(0) = 0; the formula then
  gives (2−x₁−x₂)/(2√(1−x₁)√(1−x₂)(x₁−x₂)²), which is the Step 1 twist identity (l.883–885).
- `Stmt_sub_bergman_liouville` = ∃ C, IsWFormula C (Steps 1–2): faithful.
- `Stmt_sub_bergman_zero_mode`: 4C = 2z(1−z)F₀′/F₀ − z, l.941 times 2: faithful.
- `Stmt_sub_bergman_residue`: 8(z−1)Tr(DM²(I−M²)⁻¹) = z + 8C, l.963–964 times 8(z−1):
  faithful.  With the zero-mode value it gives Tr = z/(8(1−z)) − ½zF₀′/F₀ = `Stmt_sub_bergman_trace`.

Route notes (paper is the authority):
- |B_{m,n}| ≤ 2n(n+1) from the explicit coefficients in place of Cauchy's inequality (l.845–847):
  the same estimate with a stronger bound; allowed by the brief.
- The coincidence limit (l.946–949) is derived through S(x₁,x₂)² − P(x₁)P(x₂) =
  ¼(x₁−x₂)²(x₁x₂−z)² and continuity of each z-coefficient; on the diagonal this is the paper's
  identity 4P(−2x+1+z) + P′² = (x²−z)².  The paper states the limit without derivation; this
  fills it in.
- The residue sum (l.950–963) is computed as Laurent coefficients on |x| = ½, the brief's
  reading of "summing the residues inside |x| = r".
- P_n is stated in the reversed form pⁿP_n(1/p) (l.887–889): packaging only.

## 2026-11-21T23:26Z — run 12 results (sphere Lemma 3.5 proved)

Checked by the main session (`../runs/lean2/checkR12.log`): `Sphere.lem_bergman_det_of_cited
(hJ2 : Cited_JacobiIdentities2) : Stmt_lem_bergman_det`, `sub_bergman_liouville`,
`sub_bergman_zero_mode` have their frozen types; axioms [propext, Classical.choice, Quot.sound];
frozen statements, cited inputs and the run 11 sub-statements unchanged since ab8d2e8; no
forbidden tokens; build green (`logs/L18-build-all.log`, 3636 jobs).  The hypothesis is (2.3),
used at l.969 with its reference, so the label stands.  The new sub-statements
`Stmt_sub_bergman_holo`, `_inner`, `_outer`, `_const` are proved and used only inside the proof
of the approved `Stmt_sub_bergman_liouville`; they need no approval.  Also proved:
`L0_unique` (l.572–584, 606–611).

Route notes (paper is the authority):
- l.892–910: Lean works with Dv, Dw (the Laurent coefficients of [z^i]W in x₁) instead of v, w;
  the relations used are those of l.891 and their transposes.  Same argument.
- l.914–920: "holomorphic at ∞" encoded as holomorphic on |x₁| > |x₂| and bounded on |x₁| ≥ 1,
  glued to one bounded entire function before Liouville; forced by ℂ in place of ℙ¹.
- l.933–935: "leading term as x₂ → ∞" via the polynomial in w = 1/x₂ that the x₁-integral is at
  each z-order; it vanishes on 1 < |w| < 2, and its value at w = 0 is the paper's leading term.
  The paper's step at each order in z.
- l.888, l.936: the binomial series of (1−x)^{−1/2} on the disc proved from h²(1−x) = 1; the
  paper uses the series without proof.  Not a route question.
- l.918–924, double pole at x₁ = x₂: the paper uses S(x,x) = Y², ∂₁S(x,x) = YY′; Lean uses
  S² − P₁P₂ = ¼(x₁−x₂)²(x₁x₂−z)² and a limit of coefficients.  Not forced by the formal setting:
  queued for route repair.

Lemma 3.6 stall assessed: `IsExpansionData` quantifies over Ward solutions F, so it holds
vacuously when none exists; pinning S₁^{(2)}, S₂^{(2)} needs the existence and uniqueness of F
and the equations L0 k S₂^{(2)} = k, L0 k S₁^{(2)} = −1, which are Lemma 3.3's content.  The
paper's proof of 3.6 uses Lemma 3.3(ii) the same way.  Lemma 3.3 goes first; 3.6 and 3.7 follow
from it.

## 2026-11-22T00:20Z — run 13 results (sphere Lemma 3.3 (i)–(ii), Lemma 3.6 reduction)

Checked by the main session (`../runs/lean2/checkR13.log`): `lem_lambda_expansion_of_limit (hF)
(hK) (hJ2) (h5 : Stmt_sub_lam_limit) : Stmt_lem_lambda_expansion` and
`lem_ext_exponents_of_linear (hF) (hK) (hJ1) (hJ2) (hlin : Stmt_sub_ext_linear) :
Stmt_lem_ext_exponents`; `sub_lam_regular`, `sub_lam_order_zero`, `sub_lam_orders hF hK` at
their types; axioms [propext, Classical.choice, Quot.sound]; frozen statements, cited inputs,
`Saddle.lean` and `Fock.lean` unchanged since 31a4d61; no forbidden tokens; build green
(`logs/N20-build-all.log`, 3653 jobs).  No label.

Sub-statements (`Sphere/Proofs/Sec3LamSubs.lean`, `Sec3ExtExp.lean`):
- `Stmt_sub_lam_ward`, `_regular`, `_order_zero`, `_orders`: the clauses of the frozen 3.3(i)–(ii),
  split by proof step; all proved.
- `Stmt_sub_lam_limit` (l.637–711): 3.3(iii) with 𝓘₀ = `I0def`, Φ_c^raw = `PhiCraw`,
  Φ_j = S_j^{(2)}(σ) (the reading approved in the run 6 entry), for every expansion datum and
  every saddle point; both are unique (`expansionData_unique`, Lemma 3.4), so the quantifiers
  add nothing.  The limit is the frozen one verbatim.  Faithful, approved.
- `Stmt_sub_ext_linear` (l.991–994): L0 k g(1) = −(k/2)(1−g(1)), L0 k g(−1) = ½(1−g(−1)), k ≥ 1,
  as printed.  Approved.

Route notes (paper is the authority):
- l.513–514: rationality in λ of the Ward solution, which the paper states, is proved by
  Cramer's rule over ℂ[λ] from Lemma 3.2(ii).  It fills in the paper's claim.
- l.612–635: the universal series are defined as values at reference parameters, then the
  paper's uniqueness argument gives the general formulas; `IsExpansionData` needs explicit
  witnesses.  Same argument.
- l.569–600, uniqueness and regularity: the paper uses injectivity of 𝒟_m(∞) on the lowest
  polynomial degree and an invertible square minor with a left inverse regular in λ⁻¹; Lean
  uses the top λ-power killed by every ∂_{u_k} and a descent on the t-order.  The agent's reason
  (no chosen basis of the level spaces) does not hold: the monomials are a basis.  Queued for
  route repair.

## 2026-11-22T01:23Z — run 14 results (sphere Lemma 3.6 proved; Lemma 3.3(iii) reduced)

Checked by the main session (`../runs/lean2/checkR14.log`): `lem_ext_exponents_of_cited (hF) (hK)
(hJ1) (hJ2) : Stmt_lem_ext_exponents`, `lem_lambda_expansion_of_gauss (hF) (hK) (hJ1) (hJ2) (hc :
Stmt_sub_lam_rational_c) (hg : Stmt_sub_lam_gauss) : Stmt_lem_lambda_expansion`,
`sub_lam_limit_of_gauss`; axioms [propext, Classical.choice, Quot.sound]; frozen statements, cited
inputs and the run 13 sub-statements unchanged since 7d0f63c; no forbidden tokens; build green
(`logs/R2-build-all.log`, 3667 jobs).  Lemma 3.6 uses Lemma 3.3(i)–(ii) (proved) and Lemma 3.4;
its hypotheses are the cited inputs of those, so it is labelled (Kac citation gap: run 8 entry).

Sub-statements (`Sec3GaussSubs.lean`, `Sec3GaussRational.lean`):
- `Stmt_sub_lam_gauss` (l.637–711): each z-coefficient of e^{−λ²𝓘₀}ℬ(z), a rational function of λ
  (`gaussCoeff`, with ℬ_n as the Fock pairing `pairK` over ℂ(λ), equal to ℬ_n(λ²+μ²) at real λ by
  Lemma 3.2(ii), `pairK_eval`), is regular at λ = ∞ with the coefficient of the limit (3.5) as its
  value.  For a rational function, a finite limit along real λ → ∞ is the same as regularity at ∞
  with that value, so this is the frozen limit, restated.  Faithful, approved.
- `Stmt_sub_lam_rational`, `Stmt_sub_lam_rational_c`: the zℚ[[z]] clauses of 3.3(iii), as printed
  (l.541–545).  Approved.  Φ₁, Φ₂ are done (from Lemma 3.6); Φ_c^raw is open.

Paper: Lemma 3.3(iii) asserts 𝓘₀, Φ_c^raw, Φ₁, Φ₂ ∈ zℚ[[z]], and the proof asserts Ψ₁ ∈ zℚ[[z]]
(l.705–706), with no argument for S_c^{(2)}(σ_*), S_j^{(2)}(σ_*) or Ψ₁ being rational.  They
follow from Lemmas 3.4, 3.6 and 3.7 (closed forms; those lemmas use only 3.3(i)–(ii) and the
limit).  Recorded for the prose-edit pass (receipt.md).

Route notes:
- l.546–553, 680–682: the Tendsto is obtained from regularity at ∞ of a rational function;
  forced (the paper's λ⁻¹ extractions are algebraic, the frozen statement is a limit).
- l.637–661: the paper's "algebraic Gaussian expectation" is undefined there; Lean defines it as
  the linear functional determined by the Wick rule (uniqueness proved) over a ring with
  z^{K+1} = 0.  Fills in the paper.
- l.652–655: the Gaussian determinant formula, which the paper quotes, is proved from
  θZ = Tr(DM²(I−M²)⁻¹)Z and `theta_detInvSqrt`.  Fills in the paper.
- l.981–990 (Lemma 3.6, coefficients of g(±1)): Lean uses the closed forms `sum_n_psi`,
  `sum_n_alt_psi`; the paper changes variable p = p(w) in the contour representation.  Queued
  for route repair with the Lemma 3.4(iii) item.
- l.1000–1004 (Lemma 3.6, σ¹ generating functions): Lean derives the coefficient identities
  from the Lemma 3.4(i) identity `sum_halfBinom_Bcoef` and a binomial recursion; the paper checks
  the generating-function identity directly as a rational identity in (s₁, s₂).  Not forced;
  queued for route repair.

## 2026-11-22T02:25Z — run 15 results (Lemma 3.3(iii): steps l.637–706 proved, one sub-statement left)

Checked by the main session (`../runs/lean2/checkR15.log`): `sub_lam_gauss_of_cov (hF) (hK) (h :
Stmt_sub_gauss_cov) : Stmt_sub_lam_gauss`, `sub_lam_gauss_of_expect (hF) (hK) (h :
Stmt_sub_gauss_expect)`, `EInf_gaussCoeff (hF) (hK)`, `gauss_expect_abstract (hF) (hK)`; axioms
[propext, Classical.choice, Quot.sound]; no committed file changed except one import line in
`Virasoro/Sphere.lean` (`../runs/lean2/r15-stmtdiff.log` empty); no forbidden tokens in the 17 new
modules; build green (`logs/T1-build-all.log`, 3684 jobs).  No paper result moved: 19 of 44.

Sub-statements:
- `Stmt_sub_gauss_expect` (`Sec3GaussReduce.lean`, l.684–708): the z^n coefficient of the centered
  expectation of the shifted factor is a power series in t = 1/λ with the (3.5) coefficient at
  t = 0.  Now a theorem from `Stmt_sub_gauss_cov`.  Approved as an intermediate.
- `Stmt_sub_gauss_cov` (`Sec3GaussStepThree.lean`, l.703–708).  Checked against the paper:
  `constC` = S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*); with `IsExpansionData` for F = ward(Δ₁, Δ₂) and
  F′ = ward(Δ₄, Δ₃) and ι-evenness of S⁽²⁾ (l.706, last clause of `sub_lam_orders`) it is
  2μ²S_c⁽²⁾(σ_*) + (Δ₁+Δ₄−1/8)S₁⁽²⁾(σ_*) + (Δ₂+Δ₃−1/8)S₂⁽²⁾(σ_*); `gradL` = μ·∇S̃⁽¹⁾ at the
  saddle, so ½ gradL·covN·gradL is μ²Ψ₁ (l.703–705); Φ_c^raw = 2S_c⁽²⁾(σ_*) + Ψ₁ (l.707).  The
  coefficients match `Stmt_sub_lam_gauss`.  Faithful, approved.  Its proof needs hF, hK (the Ward
  solutions exist and fix the expansion data).

Route notes:
- l.637–702: Lean works in ℂ((t))[[z]]/(z^(n+1)), t = 1/λ, and lifts to ℂ[[t]][[z]]/(z^(n+1)).
  Forced: the frozen statement is regularity at ∞ of rational functions of λ.
- l.632–661: Lean's pairing `fockP` (run 14) has Cov(u_m, ū_m) = z^m/(2m), i.e. it is the
  Gaussian in the variables (z^m u_m, ū_m).  These are the paper's own variables after the
  rescaling by Z (l.652–654) and in U_m = z^m ξ_m (l.663), and the covariance is the paper's
  displayed Cov(U_m, V_n) at l.671–673.  Same functional, same steps; accepted, no repair.
- l.663–668: the saddle point is σ_* of Lemma 3.4 (`IsSaddle.eq_sigmaStar`); CJ = λ(σ_*, σ̄_*) by
  uniqueness from nilpotency of Q₀⁻¹(Q − Q₀), the paper's argument.
- l.684: the paper says the λ² saddle value "factors out"; Lean proves ½J·CJ = λ²𝓘₀ through
  the truncation `PhiK N` and the truncated saddle equation.  Fills in the paper.
- l.684–706 (λ¹ cancellation by ι-oddness, value at t = 0, expectation of the linear
  exponential): follow the paper.

## 2026-11-22T03:19Z — run 16 results (Lemma 3.3(iii) Gaussian evaluation proved; Lemma 3.7 Step 4 and Theorem 3.1 from Lemma 3.7)

Checked by the main session (`../runs/lean2/checkR16.log`): `sub_gauss_cov (hF) (hK) :
Stmt_sub_gauss_cov`, `sub_lam_gauss (hF) (hK) : Stmt_sub_lam_gauss`,
`sub_lam_rational_c_of_central (hF) (hK) (hJ2) (h37)`, `lem_lambda_expansion_of_central (hF) (hK)
(hJ1) (hJ2) (h37) : Stmt_lem_lambda_expansion`, `lem_central_charge_of_c2 (hF) (hK) (hJ1) (hJ2) (h :
Stmt_sub_c2_decomp) : Stmt_lem_central_charge`, `thm_large_delta_of_central`, `thm_large_delta_of_c2`;
axioms [propext, Classical.choice, Quot.sound]; no committed file changed except imports in
`Virasoro/Sphere.lean` (`../runs/lean2/r16-stmtdiff.log` empty); no forbidden tokens in the ten new
modules; build green (`logs/V4-build-all.log`, 3694 jobs).  No paper result has a labelled theorem
yet; Lemmas 3.3, 3.7 and Theorem 3.1 now rest on `Stmt_sub_c2_decomp` alone.  19 of 44.

Non-circularity: `Stmt_sub_lam_rational_c` is proved only from `Stmt_lem_central_charge`, and
`lem_central_charge_of_c2` takes only the cited inputs and `Stmt_sub_c2_decomp`, so Lemma 3.7 does
not use the rationality of Φ_c^raw.

Sub-statement `Stmt_sub_c2_decomp` (`Sec3CentralSubs.lean`, Steps 1–3 of the proof of Lemma 3.7,
paper l.1029–1156).  Checked against the paper:
- (3.8) coefficientwise: coeff_N(det^{−1/2} e^{λ²𝓘₀} det^{−1/2}) = ∑_{n≤N} c_n(λ) ℬ_{N−n}(2, λ²+n,
  1/8), G_charged and G_neutral entered by their values (l.1037–1045), (16q/z)^{λ²} = e^{λ²𝓘₀} by
  Lemma 3.4(iii).  The paper has every λ > 0; the sub-statement asks for all large λ at each N, which
  is what Step 4 uses (λ → ∞ at fixed order, l.1158–1161).  Consumer strength; accepted.
- c_n(λ) → c_n^∞ (l.1105–1108).  As printed.
- (∑ 16ⁿ c_n^∞ qⁿ)² ∏(1 − q^{2m}) = 1 in place of ∑ 16ⁿ c_n^∞ qⁿ = ∏(1 − q^{2m})^{−1/2}
  (l.1148–1155).  Step 4 then takes the 12th power of a square where the paper takes the 24th power
  of a square root; the proof of the sub-statement still has to compute the series as the paper
  does.  Accepted.
Approved.  Its docstring line numbers are two to five lines off the paper at 5040b6d (e.g. Step 4
starts at l.1158, not l.1156); correct them when the file is next edited.

Route notes:
- l.669–675: the stabilization uses the row bound O(z^m) for Cov(U_m, ·), weaker than the paper's
  displayed O(z^{m+n}) and all the paper's argument needs.  Same argument; accepted.
- l.703–706: symmetry of the Neumann covariance (from B_{m,n} = B_{n,m}), implicit in the paper.
  Fills in.
- l.1174–1176: Lean proves exp((Φ₁+Φ₂)/8) = det(I − M²)^{−1/2} by comparing 8th powers of
  series with constant term 1 (`exp_Phi_eighth`); the paper takes logs.  Not forced (`exp_smul_log`
  now exists); queued for route repair (brief, order of work item 5).
- l.1186–1198 (Theorem 3.1): the paper's composition, done in log form (`Linf_subst`).  Follows the
  paper.

Representation choices for ℋ_λ and the Step 1–3 objects: fixed by the main session in the brief
(`../runs/lean2/brief-phaseB.md`, "Sphere §3: representation choices", item 11): ℋ_λ = Fock ⊗[ℂ]
Fock as printed, L^tot by `TensorProduct.map`, the product form, `MvPolynomial.tensorEquivSum`
for products of the two variable sets, U(W) levelwise, α(x) coefficientwise in x, ∮ as the formal
residue.

## 2026-11-22T04:46Z — run 17 results (Lemma 3.7 Steps 1 and 2 proved; Step 3 reduced)

Checked by the main session (`../runs/lean2/checkR17.log`): `sub_c2_step1 (hF) (hK) :
Stmt_sub_c2_step1`, `sub_c2_primaries (hF) (hK)`, `sub_c2_wick`, `sub_c2_step2_of (hF)`,
`sub_c2_step2 (hF) (hK) : Stmt_sub_c2_step2`, `sub_c2_step3_of`, `sub_c2_decomp_of_steps`,
`sub_c2_decomp_of_step3 (hF) (hK)`, `sub_c2_decomp_of_diag (hF) (hK) (h1 : Stmt_sub_c2_diag)
(h2 : Stmt_sub_c2_diag_norm) : Stmt_sub_c2_decomp`, and `thm_large_delta_of_c2` composed with it;
axioms [propext, Classical.choice, Quot.sound].  Committed files changed: imports in
`Virasoro/Sphere.lean` and docstring line numbers in `Sec3CentralSubs.lean`, `Sec3CentralFinal.lean`
(diff read; the text of `Stmt_sub_c2_decomp` is unchanged).  No forbidden tokens in the 20 new
modules (`../runs/lean2/r17-forbidden.log` empty); build green (`logs/Z1-build-all.log`, 3714 jobs).
No paper result has a new labelled theorem; Lemmas 3.3, 3.7 and Theorem 3.1 now rest on
`Stmt_sub_c2_diag` and `Stmt_sub_c2_diag_norm`.  19 of 44.

Objects (`Sec3C2Defs.lean`), checked against the paper: `HH`, `Ltot`, `hhForm` (tensor of the forms
(3.1), l.425–428), `hhLevel`, `primSpace` (l.1058; conditions k ≤ n suffice by the grading),
`gaussExpo`/`gaussF` (F₁ = exp(λ∑A_m v_m + ∑B v v), F₂ = exp(∑B u u), l.1034–1035), `Ftot`
(level N of F₁F₂), `primGram`, `primCoef` (l.1068–1071), `Dop` (D_k of l.1076), `evAt`,
`IsDiffeoU` ((D_k + l_k⁽²⁾)U = 0, U(0) = id, l.1091–1093; U w a polynomial in W, which is the
paper's "acts finitely on each homogeneous component", total level being preserved), `Wstar`
(binom(2m,m)/(m 4^m), l.1101), `UdagF` (⟨w, y⟩ = ⟨U(W_*)w, F₂⟩ for w of level n, the adjoint in
real W specialized at W_*, l.1102–1105), `diagExpo`, `diagF` (l.1148).

Sub-statements, checked against the paper:
- `Stmt_sub_c2_step1` (l.1029–1071): every λ > 0; dim 𝒫_n(λ) = p(n); (3.8) coefficientwise with the
  left side by its value as in `Stmt_sub_c2_decomp`; for every basis of 𝒫_n(λ) the Gram matrix is
  invertible and c_n = `primCoef`.  As printed.  Approved.
- `Stmt_sub_c2_step2` (l.1073–1109): some U with `IsDiffeoU`, and every function that is c_n(λ²) in
  some basis for large λ tends to ‖(U(W_*)†F₂)_n‖².  As printed (c_n does not depend on the basis).
  Approved.
- `Stmt_sub_c2_primaries` (l.1074–1093): the P_w form a basis for large λ and P_w(iλW,u) → U(W)w
  coefficientwise.  The paper has + O(λ⁻²); `Stmt_sub_c2_wick` and Step 4 use only the limit.
  Consumer strength; approved.
- `Stmt_sub_c2_wick` (l.1095–1109): from those two facts, c_n(λ²) → ‖(U(W_*)†F₂)_n‖².  Approved.
- `Stmt_sub_c2_step3`, `Stmt_sub_c2_diag` (l.1111–1149), `Stmt_sub_c2_diag_norm` (l.1150–1156):
  for every U with `IsDiffeoU`, (U(W_*)†F₂)_n = level n of exp(−∑ (m/16^m) u_m²), and the squared
  generating function as in `Stmt_sub_c2_decomp`.  "Every U" is the paper's strength: U is unique by
  the paper's own W-filtration argument (lowest positive W-weight of a difference lies in ∩ ker D_k,
  zero by `Dop_injective_level`).  Approved.

Route notes:
- l.1030–1035: Lean shows the Gaussians solve the Ward equations from Lemma 3.4(i) and a direct
  check of (3.3) at μ = 0, without Lemma 3.3(ii).  Forced: Lemma 3.3 is stated for μ > 0 (paper
  l.507–509) and Step 1 works at μ = 0.  The paper's citation of Lemma 3.3(ii) there is outside that
  lemma's hypothesis; recorded as a paper fix for the prose-edit pass (receipt.md).
- l.1053–1067: the decomposition as an induction on the level with the projection to 𝒫_n, as item
  11 of the brief prescribes.  The paper's argument written out; accepted.
- l.1084–1086: a left inverse at λ⁻² = 0 and det(L·S) → 1 in place of a nonzero square minor.  The
  paper pairs the two itself in the same argument for Lemma 3.3(i) ("an invertible square minor …
  supplying a left inverse", l.596–597).  Same mechanism; accepted.
- l.1089–1093: U(W)w obtained as the limit of P_w(iλW,u), uniqueness from the stacked system.
  Follows the paper.
- l.1098–1102: Wick's theorem as the coefficient of v^β in exp(λA·v + vBv).  Follows the paper.

## 2026-11-22T05:55Z — run 18 results (Lemma 3.7 Step 3 proved; labelled Lemma 3.7, Lemma 3.3, Theorem 3.1)

Checked by the main session (`../runs/lean2/checkR18.log`): `sub_c2_diag (hF) : Stmt_sub_c2_diag`,
`sub_c2_diag_norm : Stmt_sub_c2_diag_norm`, `sub_c2_decomp (hF) (hK) : Stmt_sub_c2_decomp`, the
seven part theorems below, and the labelled
- `lem_central_charge_of_cited (hF) (hK) (hJ1) (hJ2) : Stmt_lem_central_charge` (lem:central-charge),
- `lem_lambda_expansion_of_cited (hF) (hK) (hJ1) (hJ2) : Stmt_lem_lambda_expansion`
  (lem:lambda-expansion),
- `thm_large_delta_of_cited (hF) (hK) (hJ1) (hJ2) : Stmt_thm_large_delta` (thm:large-delta),

all in `Sec3Headline.lean`; axioms [propext, Classical.choice, Quot.sound].  Their only hypotheses
are the cited inputs the paper uses (Feigin–Fuchs operators, Kac determinant, Jacobi identities).
Committed files changed: imports in `Virasoro/Sphere.lean` only (`../runs/lean2/r18-stmtdiff.log`
empty).  No forbidden tokens in the 12 new modules (3332 lines); build green
(`logs/W1-build-all.log`, 3732 jobs).  The sphere paper's headline theorem is proved.  22 of 44.

Part statements of Step 3 (`Sec3C2Step3Parts.lean`), checked against the paper and the objects
(`Ucf`, `Udg` the coefficientwise adjoint with ⟨U_β†a, b⟩ = ⟨a, U_β b⟩, `DkF`, `alphaOp` =
(i/√2)∂_{u_n}, −i√2 n u_n, `thc` = (N/M) M^{deg β}/β! with M = N − wt β, `Est`, `Yz`, `cst`, `sk`):
- `Stmt_sub_c2_adj` (l.1111–1114), `Stmt_sub_c2_current` (l.1114–1118), `Stmt_sub_c2_conj`
  (l.1119–1127, with a two-sided inverse series), `Stmt_sub_c2_fstar` (l.1128–1131, in t = 1/x:
  g + t/2 + t²/(16g) = 1 and √(1−t) = g − t²/(16g), i.e. x(X) = X + ½ + 1/(16X) and
  √(x(x−1)) = X − 1/(16X)), `Stmt_sub_c2_input` (l.1131–1134, the residue at each level as a
  finite sum), `Stmt_sub_c2_cov` (l.1134–1139), `Stmt_sub_c2_modes` (l.1140–1145).  As printed,
  level by level.  Approved.

Route notes:
- l.1128–1131: Lean proves exp(−∑ W_{*,m} t^m) = ((1+√(1−t))/2)² by comparing logarithmic
  derivatives and constant terms.  The paper's log(4(1−√(1−y))/(y(1+√(1−y)))) is −2 log((1+√(1−y))/2),
  and its integral identity is checked by the same derivative.  Same argument in exponentiated form;
  accepted.
- l.1134–1139: the change of variables as the formal residue statement of brief item 12
  (`res_hS`: res f^p f′ = δ_{p,−1}).  As fixed by the main session.
- l.1140–1143: the span from x(X)·(X^m − 16^{−m}X^{−m}) = D_{m+1} + ½D_m + (1/16)D_{m−1}
  (D_m = X^m − 16^{−m}X^{−m}), giving a triangular expansion with leading coefficient 1.  This
  writes out the paper's invariance-and-leading-term sentence; accepted.
- l.1091–1093: U_β lowers the level by wt β is derived from `IsDiffeoU` (`Ucf_graded`), since the
  frozen statement quantifies over every such U.  Fills in.
- l.1145–1149: the Gaussian identified through ∂_iΦ = Φ·∂_i g (`ext_of_pderiv`).  Fills in.
- Adjoint, Ψ = U†α(U†)⁻¹ with the inverse series, uniqueness on matrix entries: follow the paper.

## 2026-11-22T05:56Z — Part II run 1 results (second agent; Lemmas 10.1, 10.3, 11.1, Props 10.2, 12.1 proved)

Checked by the main session (`../runs/lean2/checkP2R1.log`), all labelled, hypotheses only the
inputs the paper cites at the step: `lem_fusion_injective : Stmt_lem_fusion_injective` (none);
`lem_two_weight_ward_of_cited (hE : Cited_TwoWeightPairingExists)` (HJS 2010, l.2081–2085);
`prop_fusion_poly_of_cited (hH) (hL : Cited_SingularFamilyLaurent) (hF : Cited_FusionPolynomial)`
(Astashkevich, Prop. imported-normalizations, Zamolodchikov; l.2149–2155);
`lem_bgg_arrows_of_cited (hJ : Cited_JantzenLayersOrbit) (hH)` (l.2232–2239, l.2261);
`prop_bgg_cocycle : Stmt_prop_bgg_cocycle` (none).  Also `thm_first_layer_ratio_of_box`,
`thm_descent_regularity_of_subs`, `descent_iff_of_cited`; axioms [propext, Classical.choice,
Quot.sound].  No committed statement or cited file changed; no forbidden tokens in the 13 new
modules (`../runs/lean2/p2r1-forbidden.log` empty).  `Virasoro.PartII` is now imported by
`Virasoro.lean`; `lake build Virasoro` green with it (`../runs/lean2/p2r1-fullbuild.log`, 3760
jobs).  With run 18: 27 of 44.

Sub-statements, checked against the paper:
- `Stmt_sub_first_layer_box` (l.2630–2715): the first three clauses of the frozen Theorem 9.2
  after `boxDen ≠ 0`, same quantifiers.  Approved.
- `Stmt_sub_irr_trace_unique` (l.1857–1858): descent gives a unique `IsIrrTrace` coefficient at
  every N, the parenthesis of Theorem 9.1(i).  Approved.
- `Stmt_sub_pole_outside` (l.2578–2606): some level with a pole at λ when d ∉ ℱ^±.  The paper
  names N ∈ {ℓ_min, ℓ_max}; Theorem 9.1(ii) uses existence.  Consumer strength; approved.
- `Stmt_sub_orbit_regular` (l.2570–2574): pole order 0 at every orbit weight for d ∈ ℱ^±, the
  "hence" step from Lemma 11.3.  Approved.
- `Stmt_sub_joint_denominator` (l.2508–2540): F_N · b^e ∏_{𝒦_N}(Δ − h_{R,S}(b)) is a polynomial
  in (b, Δ), 𝒦_N = {RS ≤ N, R ≤ k or S ≤ m}, over ℂ.  The paper's denominator statement in
  ℚ[b,b⁻¹,Δ]; e existential.  Approved.
- `Stmt_sub_vertex_radical_zero` (l.2412–2421): J¹(c⋆,μ) in the radical of every primary pairing
  of weight d, both slots.  The paper says ρ_{c⋆,μ,d}; a primary pairing on M(c⋆,μ) is determined
  by its value at (v_μ, v_μ) through the Ward identity, so this is the same strength.  Approved.
- `Stmt_sub_generic_tau_split` (l.2883–2913): (13.2) at generic b (b ≠ 0, b² ∉ ℚ) for every
  N, multiplied by `boxDen`, with the regularity of F_N at h_{R,S}(b) and of F_{N−RS} at
  h_{R,−S}(b) that the paper's values presuppose.  Approved.

Route notes:
- l.2089–2095 (Lemma 10.1, (10.3)): contravariance at n = 0 in place of B(u,v) = 0 for N₁ ≠ N₂.
  Forced by the frozen `IsTwoWeightPairing` (Ward identity with L₀).  Accepted.
- l.2149–2152 (Prop 10.2(i)): existence and uniqueness of the normalized family from
  `Cited_HJSNormalizations`; the paper cites Prop. imported-normalizations there.  Follows the
  paper's citations.
- l.2250–2262 (Lemma 10.3(iii)): Lean lists the eight consecutive-layer labels and reads
  (10.11)–(10.13) from them; the paper reduces p′R − pS = σn_μ mod p and p′ and uses
  0 < n_ν − |n_μ| < 2pp′.  Not forced; queued for route repair (brief item 5).
- l.2244–2247 (Lemma 10.3(ii), uniqueness): p′ ∤ S in place of p ∤ n_μ, p′ ∤ n_μ.  Not forced;
  queued.
- l.2799–2809 (Prop 12.1, Ψ(ϖ_μ; b⋆) ≠ 0): R ≡ ±r, S ≡ ±s in place of n_μ mod p and p′.  Not
  forced; queued.
- l.2810–2832 (Prop 12.1(ii)): telescoping of 1/Γ and the reduced value through ℚ[t].  Forced by
  the frozen `PsiPot` (through 1/Γ) and the reduced `cMM`.  Accepted.
- l.2563–2567 (Theorem 9.1(i)): w^±₁ identified with the normalized χ_{r,s}(b⋆),
  χ_{p−r,p′−s}(b⋆) up to scalars through `Cited_SingularUnique`, which the paper uses without
  saying so (recorded for the prose-edit pass, receipt.md); the unlabelled case by
  (r,s) ↦ (p−r,p′−s), forced by `MinimalSetting` in `Cited_JantzenLayersOrbit`.

## 2026-11-22T06:39Z — run 19 results (sphere Prop 4.4 and Theorem 4.7 proved, labelled)

Checked by the main session (`../runs/lean2/checkR19.log`): `Sphere.prop_generic_recursion_of_cited
(hF) (hK) (hJ1) (hJ2) (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) :
Sphere.Stmt_prop_generic_recursion` (prop:generic-recursion, `Sec4GenericFinal.lean`) and
`Sphere.thm_confluence_of_cited (same hypotheses) : Sphere.Stmt_thm_confluence` (thm:confluence,
`Sec4PolyPart.lean`), and `sub_confluence_poly_part (hF) (hK) (hJ1) (hJ2)`; axioms [propext,
Classical.choice, Quot.sound].  The hypotheses are the cited inputs of the results the proofs use
(Theorem 3.1, Prop 4.3).  Committed files changed: imports in `Virasoro/Sphere.lean` only
(`../runs/lean2/r19-stmtdiff.log` empty); no forbidden tokens in the 12 new modules; build green
(`logs/R4-build-all.log`, 3772 jobs).  29 of 44.

Sub-statement `Stmt_sub_confluence_poly_part` (`Sec4ConflFinal.lean`, l.1385–1388, 1421–1422): the
third clause of the frozen `Stmt_thm_confluence`, character for character (compared).  Approved.

Route notes:
- sphere l.1300–1307 (Prop 4.4): the residue through `residue_inverse` (kernel = image of ι,
  determinant order p(M), first crossing form), as the landed proof of torus Prop 6.4 does; the
  sphere paper takes it from torus Lemma 5.4 (l.1306–1308), and the torus paper's Prop 6.4 now
  does the same with k = 1.  Not forced (`lem_top_coefficient` is proved); queued for route repair
  for both propositions (brief item 5).
- sphere l.1317–1318: the degree form deg P_N < deg det G_N in place of lim H_N = 0.  Both are
  clauses of Theorem 3.1 as printed (l.411–414), which the paper cites here.  Accepted.
- sphere l.1392–1393 (Theorem 4.7): Prop 4.4 re-run over any field at a transcendental b, since
  the frozen Prop 4.4 quantifies over complex b only.  Forced; accepted.
- sphere l.1405–1411: the t⁰ coefficient extracted directly (`pole_support`); the paper first
  shows each C_{λ,k}(t) holomorphic by uniqueness of partial fractions.  Not forced; queued.
- sphere l.386–397 (Theorem 4.7(iii)): only deg ψ_{N−m}(Δ+m) ≤ N − m is proved, which is what the
  degree count uses; the top coefficient of ψ_N from [q¹](16q/z) = 8 and [z¹]q(z) = 1/16, the same
  number as the paper's 16q/z = 1 + z/2 + O(z²).  Accepted.

## 2026-11-22T06:41Z — Part II run 2 results (Lemma 11.3 and Theorem 9.1 proved, labelled)

Checked by the main session (`../runs/lean2/checkP2R2.log`, a file importing `Virasoro` and
`Virasoro.PartIIWork` together, so no name clash with the sphere tree):
- `lem_joint_holomorphicity_of_cited (hK) (hH) : Stmt_lem_joint_holomorphicity`
  (lem:joint-holomorphicity); the paper cites the Kac determinant (l.2509) and Prop 6.4 (l.2522),
  which is proved from those two inputs;
- `thm_descent_regularity_of_cited (hJ) (hH) (hU) (hF) (hK) (hI : Cited_VermaHomInjective) :
  Stmt_thm_descent_regularity` (thm:descent-regularity), the cited inputs of Lemmas 10.3, 11.1,
  11.3, Prop 10.2, Theorem 5.9 and `Cited_SingularUnique` (the silent step at l.2563–2567, paper
  fix queued after Part II run 1);
- the sub-statements `sub_joint_denominator`, `sub_orbit_regular`, `sub_pole_outside`,
  `sub_irr_trace_unique`, `sub_vertex_radical_zero`, and the reductions `vertex_part_i_of_step`,
  `cor_collision_free_of_trunc`.
Axioms [propext, Classical.choice, Quot.sound].  No committed file changed; no forbidden tokens in
the 11 new modules; `lake build Virasoro.PartIIWork` green (`logs/II-build-work3.log`, 3480 jobs).
`PartIIWork.lean` is committed and is not yet imported by `Virasoro.lean`, to keep the other
agent's whole-project builds unaffected; it moves into `PartII.lean` when no agent is building.
31 of 44.

Sub-statements, checked against the paper:
- `Stmt_sub_vertex_step` (l.2423–2459): the induction step of Prop 11.2(i), from the four clauses at
  i for all J^{(i)} families to the clauses at i + 1; `VertexClausesAt` is checked by an `example`
  to be the body of part (i) of the frozen `Stmt_prop_jantzen_vertex`.  The paper's induction;
  approved.
- `Stmt_sub_truncated_recursion` (l.1975–1978, l.3153–3157): `TruncRecAt` is the fourth clause of
  the frozen `CollisionFree`, compared character for character.  Approved.

Route notes:
- l.2510–2515 (Lemma 11.3): the Δ-leading coefficient of det G_N(c(b),Δ) is shown to be a unit of
  ℂ[b,b⁻¹] (`kacLead_unit`), since `Cited_KacDeterminant` gives a nonzero constant for each b
  without its dependence on b.  Forced; it is what the paper's step uses.
- l.2525–2527: the finiteness of the shifted coefficient (Lemma 6.3) is already part of the Lean form
  of the generic recursion.  Accepted.
- l.2587–2603 (Theorem 9.1(ii)): the top-layer residue formula for F_N at a complex d, re-proved by
  the steps of Theorem 5.9's proof (l.871–886), because the frozen Theorem 5.9 is over ℂ(d).
  Forced; accepted.
- Theorem 9.1(ii) relabelling (r,s) ↦ (p−r,p′−s) (l.2163–2165): forced by n₁ < pp′ in the frozen
  Theorems 5.8–5.9.  Accepted.
- l.1857–1858: T^irr well defined, by the Gram-matrix change of family modulo ker G_N.  The paper's
  parenthesis (the form descends, so V_d(1) is an operator on L and its trace is defined) is enough
  for a reader; Lean fills in.
- Cor 9.4, the dual case through h_{r,s}(b) = h_{s,r}(b⁻¹): the paper's p ↔ p′ duality (l.3124).

## 2026-11-22T07:39Z — run 20 results (torus Prop 6.8 reduced to two steps; Prop 6.9 first step)

Checked by the main session (`../runs/lean2/checkR20.log`): `sub_h13_polynomial (hK) (hH) :
Stmt_sub_h13_polynomial` (l.1224–1261), `sub_h13_values` (l.1248–1256), `sub_h13_valuation (hK)`
(l.1380–1392), `sub_h13_lipschitz` (l.1392–1416), `prop_h13_nonvanishing_of_two (hK) (hH)
(h1 : Stmt_sub_h13_integral) (h2 : Stmt_sub_h13_degree) : Stmt_prop_h13_nonvanishing`,
`sub_tau_factorization (hH) (hU)` (l.1433–1446; the paper cites Iohara–Koga Prop. 5.1 there, which
is `Cited_SingularUnique`); axioms [propext, Classical.choice, Quot.sound].  Committed files
changed: two import lines in `Virasoro.lean`; no statement or cited file changed; no forbidden
tokens in the 11 new modules; build green (`logs/H15-build-all.log`, 3784 jobs).  No new labelled
result: 31 of 44.

Sub-statements, checked against the frozen `Stmt_prop_h13_nonvanishing` (`Statements/Sec6c.lean`)
and the paper:
- `Stmt_sub_h13_values`, `Stmt_sub_h13_integral`, `Stmt_sub_h13_degree`: the conjuncts of clauses
  (i) and (ii), compared clause by clause, for every family P with P(t, t²Δ) = `clearedH`, which
  determines P.  Approved.
- `Stmt_sub_h13_valuation`, `Stmt_sub_h13_lipschitz`: clause (iii)'s two parts, compared, with
  clauses (i) (and (ii) for the bound) as hypotheses, which is how the proof uses them
  (l.1385–1387, l.1393–1396).  Approved.
- `Stmt_sub_tau_factorization` (l.1433–1446): the four factorizations, k odd with j = ⌊k/2⌋ and k
  even with j − 1 = k/2 − 1, 2j − 1 = k − 1, checked against the printed indices.  Approved.

Route notes:
- l.1232–1248 (mode count): Lean proves G̃ = t^{ℓ(λ)+ℓ(μ)}G as an identity from rescaled
  operators (L̃_k = τL_k, L̃_0 = τ²L_0) and reads D₀ at τ = 0.  This is the paper's count of modes
  written as a grading identity; accepted.
- l.1232–1235, 1257–1261: ℚ[t,t⁻¹] in place of ℤ[1/2][t,t⁻¹], since this step claims only ℚ[t,Y];
  the ℤ[1/2] claim is `Stmt_sub_h13_integral`, proved by the paper separately (l.1261–1291).
  Consumer strength; accepted.
- l.1257–1258: K_M read off the top Δ-coefficient of det G_M.  Forced by `Cited_KacDeterminant`.
- l.1224–1231: the recursion over ℚ(b) through t ↦ b², back by monic division.  Forced by
  `GenericRecursionAt` (b must lie in the field).
- l.1248–1253, l.1380–1384: the t = 0 value and the specialization at (t⋆, t⋆²μ) read from the
  polynomial identity P·∏det G̃ = prefactor·numerator, which is the expansion the paper uses at
  t = 0 and its value at the point.  Same content; accepted.
- l.1393–1397: Newton's forward-difference formula with ℓ-integral β_u (|β_u|_ℓ ≤ 1) in place of
  β_u ∈ ℤ[1/2]; (6.4) uses only |β_u|_ℓ ≤ 1 for odd ℓ.  Accepted.
- l.1433–1446, even k: the L₋₁-coefficient of the composite vector up to sign from Lemma 5.7;
  the sign does not matter because τ is quadratic.  Fills in.

## 2026-11-22T08:04Z — Part II run 3 results (Prop 11.2 proved, labelled)

Checked by the main session (`../runs/lean2/checkP2R3.log`, importing `Virasoro` and
`Virasoro.PartIIWork` together): `prop_jantzen_vertex_of_cited (hJ) (hH) (hU) (hF) (hI) :
Stmt_prop_jantzen_vertex` (prop:jantzen-vertex) and `sub_vertex_step`; axioms [propext,
Classical.choice, Quot.sound].  The seven new sub-statements of part (ii) are proved and consumed
by the labelled theorem, whose type is the frozen one.  No committed file changed except the
appended imports of `PartIIWork.lean`; no forbidden tokens in the 18 new modules.  32 of 44.

Name clash found at landing: `Virasoro.ev0` was defined in run 20's `Sec6H13Reg.lean` and in
`P2Sec11Lattice.lean`.  The main session renamed the Part II one to `latEv0` (three files) and
rebuilt `Virasoro.PartIIWork` (green, 3528 jobs, `../runs/lean2/p2r3-rebuild.log`).  New Part II
declarations go in the namespace `Virasoro.P2` (brief-partII.md).

Route notes:
- l.2423–2437: lattices over ℂ[x] (`InLat`).  Forced by the frozen statement's polynomial
  families.
- l.2439–2453: M(μ^ε_{k₀+i}) ⊂ J^i through the embedding j_χ and `Cited_VermaHomInjective`,
  since `Cited_JantzenLayersOrbit` gives these submodules as U(Vir₋)w.  Forced; the labelled
  theorem carries hI.
- l.2443–2447: `ward_eq_smul_pairing`, the uniqueness induction of Lemma 10.1 for an
  unnormalized Ward form (σ may be 0).  Forced by the normalized frozen Lemma 10.1.
- l.2466–2480: the adapted basis through S = Uᵀ·diag(x^{m−e_a}u_a⁻¹)·U with G·S = x^m and
  truncation to polynomial families.  Forced by the representation of F_N and of part (i).
- l.2472, 2486–2495: traces on J^i_N/J^{i+1}_N by families of representatives with proved basis
  independence.  Forced: no quotient-module objects in the tree.
- l.2487–2490: the orthogonality and independence of the two summands are derived from
  contravariance, the levels of w^± and the nondegeneracy of B̄^{(i)}, without the clause
  J^i/J^{i+1} ≅ L ⊕ L of Lemma 10.3(i).  Not forced; queued for route repair (brief item 5).

## 2026-11-22T08:33Z — run 21 results (Prop 6.8(i) integrality reduced to two counting facts)

Checked by the main session (`../runs/lean2/checkR21.log`, with `Virasoro.PartIIWork` loaded as
well): `sub_h13_integral_of (hK) (hL : Stmt_sub_h13_lagrange) (hS : Stmt_sub_h13_detD) :
Stmt_sub_h13_integral`, `prop_h13_nonvanishing_of_comb (hK) (hH) (hL) (hS) (h2 :
Stmt_sub_h13_degree) : Stmt_prop_h13_nonvanishing`, and the free-field pieces `TFock.LOp_vir`
(Virasoro relations with c = 1 − 12q₀², proved), `TFock.pair_L` (L_n† = L_{−n}),
`TFock.gram_factor` (G = B(2q₀−α) D Bᵀ(α)); axioms [propext, Classical.choice, Quot.sound].
Committed files changed: one import line in `Virasoro.lean`; no forbidden tokens in the 10 new
modules; build green (`logs/I1-build-all.log`, 3798 jobs).  No new labelled result.

Sub-statements (`Sec6H13IntA.lean`), checked against the paper:
- `Stmt_sub_h13_lagrange` (l.1283–1285): D_λ = (−1)^{ℓ(λ)}∏ m_n! n^{m_n} divides N! in ℤ.
  Approved.
- `Stmt_sub_h13_detD` (l.1270–1271): K_N = 2^{∑ℓ(λ)}·|∏_λ D_λ|, the paper's
  |det D_M| = 2^{−∑ℓ(λ)}K_M.  Approved.

Route notes:
- l.1275–1291, the local ring.  The paper uses R = ℤ_(ℓ)[b,b⁻¹,α]_(ℓ), 𝒪 = R[q₀], a prime 𝔭
  above ℓ and the DVR 𝒪_𝔭.  Lean parametrizes the conic q₀² = −(t+1)²/(2t) by
  t = −s²/2, q₀ = 1/s − s/2, works with ℤ[1/2][s,s⁻¹,α] and reduction mod ℓ, and writes
  "x ∈ 𝒪_𝔭" as x·δ = N with δ of nonzero reduction.  The steps of l.1270–1291 (unit
  determinants, M!D⁻¹ integral, intersection with ℚ[t,Y]) are followed one to one inside that
  ring.  Not forced: the paper's 𝒪_𝔭 can be stated in Mathlib, but the fact that the localization
  of this finite étale extension at a prime above ℓ is a DVR with uniformizer ℓ is not in Mathlib.
  Queued for route repair (brief item 5), with that missing fact as its cost.
- l.1287–1290: the intersection by clearing denominators and `evbar_injective`; part of the
  previous note.
- l.1270–1275: each factor Δ − h_{u,v} has nonzero reduction, the paper's leading-coefficient
  argument in the same coordinates.  Accepted.
- l.1285–1286: adjugates in place of G⁻¹ (adj = det·inverse).  Same content; accepted.
- l.1266–1267: L_n† = L_{−n} by induction on monomials from [L_n, a_m]; forced by the encoding of
  the mixed part of L_n as a derivation.  Accepted.
- l.1263–1264: the Virasoro action, stated in the paper without proof, is proved.  Fills in.
- `Bm` has rows λ (transpose of the paper's B_M).  Notation.
- `kac_det_T`: b with b² = t from the algebraic closure.  Forced by `Cited_KacDeterminant`.

## 2026-11-22T08:33Z — Part II run 4 results (Theorem 9.2 and Cor 9.4 proved, labelled)

Checked by the main session (`../runs/lean2/checkP2R4.log`, importing `Virasoro` and
`Virasoro.PartIIWork`): `P2.thm_first_layer_ratio_of_cited (hE) (hH) (hU) (hF) :
Stmt_thm_first_layer_ratio` (thm:first-layer-ratio) and `P2.cor_collision_free_of_cited (hK) (hH)
: Stmt_cor_collision_free` (cor:collision-free), both labelled; `P2.sub_generic_tau_split_of_subs`
(Lemma 13.1 Step 1, reduced); axioms [propext, Classical.choice, Quot.sound].  No committed file
changed except `PartIIWork.lean`'s imports; no forbidden tokens in the 10 new modules, all in
namespace `Virasoro.P2`; `lake build Virasoro.PartIIWork` green (3557 jobs).  34 of 44.

Sub-statements (`P2Sec13Split.lean`), checked against l.2884–2903:
- `Stmt_sub_generic_layers`: at generic b, J¹ = U(Vir₋)χ and J^i_N = 0 for i ≥ 2, the content of
  "a unique proper nonzero submodule, generated by χ" that the two-layer decomposition uses.
  Approved.
- `Stmt_sub_generic_vertex`: part (i) of Prop 11.2 at (c(b), h_{R,S}(b), h_{2k+1,2m+1}(b)).
  Approved.
- `Stmt_sub_generic_layer_one`: the layer-1 trace equals c_{R,S}·F_{N−RS}(c(b),h_{R,−S}(b),d),
  cross-multiplied by `boxDen`.  Approved.

Route notes:
- l.2646–2651 (Theorem 9.2): only the homomorphism v ↦ χ is used, not U(Vir₋)χ ≅ M(c,h_{R,−S});
  the argument needs no more.  Accepted.
- l.2652–2663: uniqueness of Lemma 10.1 applied to W + (1 − W(v,v))ρ; forced by the normalized
  frozen Lemma 10.1.  l.2133–2138, 2691: `fusP` shown equal to (10.9) first; forced by the frozen
  definition.  l.2683–2685: cross-multiplied; forced.
- l.2686–2690: λ₁ kept in place of L₁ = bλ₁; same computation with another normalization of the
  momentum.  Accepted.
- l.3153–3157 (Cor 9.4): the specialization of the recursion to b⋆ is written out, as the frozen
  clause asks for the identity.  Fills in.  The dual case from the same general theorem in place
  of p ↔ p′ duality: same argument applied twice.  Accepted.

## 2026-11-22T09:02Z — Part II run 5 results (Lemma 13.1 Step 1 proved; Lemma 13.1 reduced to Steps 2–4)

Checked by the main session (`../runs/lean2/checkP2R5.log`, importing `Virasoro` and
`Virasoro.PartIIWork`): `P2.sub_generic_tau_split_of_cited (hK) (hE) (hH) (hU) (hF) (hI) :
Stmt_sub_generic_tau_split` (13.2), with the three Step 1 sub-statements;
`P2.sub_tau_verma_limit_of_cited (hK) (hH)`, `P2.sub_tau_box_limit`;
`P2.lem_degenerate_quotient_t_of_trace (…) (hT : P2.Stmt_sub_tau_trace_limit) :
Stmt_lem_degenerate_quotient_t`; axioms [propext, Classical.choice, Quot.sound].  No committed
file changed except `PartIIWork.lean`'s imports; no forbidden tokens in the 8 new modules;
`lake build Virasoro.PartIIWork` green (3569 jobs).  No new labelled result: 34 of 44.

Sub-statements (`P2Sec13Limit.lean`), checked against the paper:
- `Stmt_sub_tau_verma_limit` (l.3029–3034): the Verma terms of (13.2) are values of rational
  functions of b regular at b⋆ (Lemma 11.3).  Approved.
- `Stmt_sub_tau_box_limit` (l.3018–3023, 3031–3033): the box ratio is the value of a rational
  function of b regular at b⋆ with value Ω (Prop 12.1(i)), cross-multiplied with `boxDen`.
  Approved.
- `Stmt_sub_tau_trace_limit` (l.2906–3028): the trace on V_{R₁,S₁}(b)_N at generic b (outside a
  finite set) is the value of a rational function of b regular at b⋆ whose value is
  T^irr_N(c⋆,μ,d⋆) + Ω(μ→ν₂)T^irr_{N−R₂S₂}(c⋆,ν₂,d⋆).  This is the paper's "lim_{τ→0}" in the
  reading of brief-partII.md (the limit is the value of the regular extension).  Approved.

Decision on the deformation parameter (the agent asked): the parameter is b itself, with b − b⋆
as the uniformizer, in place of t = t₀ + τ fixed in brief-partII.md.  Since b⋆ ≠ 0,
τ = b² − b⋆² = (b − b⋆)(b + b⋆) with b + b⋆ a unit at b⋆, so the local rings and all τ-adic orders
agree, and the frozen Lemma 11.3, Lemma 6.6, `kacC`, `kacH` and the `EvToK` tools are in b.
Confirmed; the brief is updated.

Route notes:
- l.2884–2887: "a unique proper nonzero submodule, generated by χ" is stated in the paper without
  proof or citation; Lean proves the two facts used (J¹ = U(Vir₋)χ, J^i = 0 for i ≥ 2) from the
  Kac determinant, Lemma 5.6 and Theorem 9.2.  Fills in.
- l.2899–2903: the two-layer analogue of Prop 11.2(ii) for one summand in the basis {L_{−Z}χ},
  with G_M(c(b),h_{R,−S}(b)) invertible.  The paper's argument specialized; accepted.

## 2026-11-22T09:10Z — run 22 results (Prop 6.8(i) proved; Prop 6.8(ii) reduced; Prop 6.9 reduced to the odd case)

Checked by the main session (`../runs/lean2/checkR22.log`, with `Virasoro.PartIIWork` loaded):
`sub_h13_lagrange`, `sub_h13_detD`, `sub_h13_integral (hK) : Stmt_sub_h13_integral` (all of
clause (i) of Prop 6.8 now proved), `sub_h13_degree_of_chain`, `prop_h13_nonvanishing_of_chain
(hK) (hH) (h : Stmt_sub_h13_degree_chain)`, `sub_two_term_nonzero_of_odd`; axioms [propext,
Classical.choice, Quot.sound].  Committed files changed: import lines in `Virasoro.lean`; no
forbidden tokens in the 6 new modules; build green (`logs/J2-build-all.log`, 3858 jobs).  No new
labelled result: 34 of 44.

Sub-statements, checked against the paper:
- `Stmt_sub_h13_degree_chain` (l.1304–1378): for every r, [t^i Y^j] of the r-th term
  (M!/2^M) Y^M Tr(D₀⁻¹(1 − G̃D₀⁻¹)^r ρ̃) is a polynomial in M of degree ≤ 2i + 2j for all M ≥ 0
  (zero when 2i + 2j < 0); the consumer sums r ≤ i (l.1305–1306).  Approved.
- `Stmt_sub_two_term_nonzero_odd` (l.1430–1565): the frozen statement with an odd prime ℓ ∣ p′,
  the paper's reduction by b ↦ b⁻¹.  Approved.

Route notes:
- l.1299–1306: ℚ[Y,Y⁻¹][[t]] in place of ℚ(Y)[[t]]; the expansion lies there since D₀ is
  invertible in it, and [t^i Y^j] with j ∈ ℤ is needed as a function.  Accepted.
- l.1304–1305: (−t)^r D₀⁻¹(G₁D₀⁻¹)^r written D₀⁻¹(1 − G̃D₀⁻¹)^r, the paper's identity at l.1313.
  Accepted.
- l.1296–1299: all power sums by Faulhaber and the product coefficients by Newton's identities, the
  tools the paper names at l.1352.  Accepted.
- Main-session note on the stall: the agent wrote that the project has no operator algebra for
  ad(L₁)^p(L_μL_{−μ′}).  `VirEnv R c` (`Virasoro/Algebra.lean`) is that algebra (the enveloping
  algebra with c specialized, an associative R-algebra with `L_mul_L`); brief item 14 fixes its use.

## 2026-11-22T09:50Z — hand-overs of run 23 and Part II run 6 (agents wound down on the user's instruction)

The user asked the agents to wind down and hand over; both did.  Checked by the main session
(`../runs/lean2/checkR23.log`, `../runs/lean2/checkP2R6.log`, each importing `Virasoro` and
`Virasoro.PartIIWork`); axioms [propext, Classical.choice, Quot.sound] throughout; no forbidden
tokens in the 16 new modules; no statement or cited file changed.  All Part II staging imports were
moved into `PartII.lean`; `lake build Virasoro` green with everything landed
(`../runs/lean2/land2-build.log`, 3882 jobs).  No new labelled result: 34 of 44.

Run 23 (torus): Prop 6.8(ii) steps in namespace `H13C` (`pow_mul_eq_sum_ad` l.1316,
`L1_pow_Lm1_pow` l.1317–1318, `gramWord_ones` l.1313–1322, `locBr_polyVal` l.1322–1332,
`ward_pow` l.1337–1341, `L1_pow_mul_Lm1_pow` l.1342–1343, `mul_pow_eq_sum_nad` l.1334–1335);
Prop 6.7 steps in namespace `ChainEval` (`moment_limit` l.1162–1164, `coeff_chainTN`
l.1139–1141, the colliding chains l.1150–1156).  Its half-done `scratch/t3/Sec6ChainSlopes.lean`
was fixed by the main session (three declarations) and compiles.  Route notes: l.1342–1343, products
of the commuting factors 2L₀ + s as values of a polynomial at 2L₀ (forced: `VirEnv` is not
commutative); l.1329–1332 and l.1162–1164, the paper's inductions and moment argument written out
or in polynomial form.  Accepted.

Part II run 6: Lemma 13.1 Steps 2 and 3 proved (`sub_tau_kernel_lift_of_cited`,
`sub_tau_lattice_of_cited`, `orbit_length_two`, `tau_first_order_gram`,
`sub_tau_depth_one_of_cited`); Lemma 13.1 reduced to Step 4,
`P2.lem_degenerate_quotient_t_of_diag (…) (h4 : Stmt_sub_tau_diag_limit)`.  Sub-statements
approved: `Stmt_sub_tau_kernel_lift`, `Stmt_sub_tau_deriv_chain`, `Stmt_sub_tau_depth_one`,
`Stmt_sub_tau_lattice` (proved); `Stmt_sub_tau_diag_limit` (Step 4 for the lattice family) and
`Stmt_sub_tau_ratio` ((13.3), second line, with the ratio Ω, l.2972–3023; the coefficient does not
depend on the lift because χ_{R₂,S₂}(b⋆) is singular at μ) (open).  Route notes: l.2910–2913,
independence of the descendants through `Cited_VermaHomInjective` in place of freeness of M over
U(Vir₋); not forced, queued for route repair with the earlier `layer_kernel` instance.  The other
differences (lattices in the Verma module over ℂ⟦X⟧, kernel identities over ℂ[b,b⁻¹] from infinitely
many b, the simple-quotient clause of Lemma 10.3(i), division by the monic Δ − h_{R₂,S₂}) are forced
or the paper's argument in the uniformizer X = b − b⋆.  Accepted.

## 2026-11-22T10:28Z — main session: Prop 6.7, Stmt_sub_layer_chain_eval proved

Proved by the main session after the wind-down (`../runs/lean2/checkMe1.log`, `checkMe2.log`):
`sub_layer_chain_eval : Stmt_sub_layer_chain_eval` (paper.tex l.1150–1173), from
`Setup.eval_plus_odd`, `Setup.eval_minus_odd` (k = 2j+1) and `Setup.eval_even` (k = 2q+2, both
signs), in `Sec6ChainOddPlus`, `Sec6ChainOddMinus`, `Sec6ChainEvenBase`, `Sec6ChainEvenSteps`,
`Sec6ChainEvenTail`, `Sec6ChainEven`, `Sec6ChainEvalFinal`, with the run 23 hand-over
(`moment_limit`, `coeff_chainTN`, `gL`, `firstSteps_sub`) and the fixed `Sec6ChainSlopes`.
Prop 6.7 is `prop_layer_coefficients_of_limit (hI) (h1 : Stmt_sub_layer_chain_limit)`.  Axioms
[propext, Classical.choice, Quot.sound]; no forbidden tokens; `lake build Virasoro` green (3890 jobs).
No new labelled result: 34 of 44.

Route: the paper's (l.1157–1169).  The first steps are the g_i of l.1157–1160 (for ℓ⁻ odd one more
first step, g_j, whose chains are shown dead, matching the paper's index range −j−1 ≤ i ≤ j−1); κ
is the paper's (the endpoint step for odd k, n₁ + (j−1)N₀ followed by the step of l.1167–1168 for
even k, whose other continuations are shown dead or not to reach the endpoint); C_κ, the slope
product and ρ_g/(ḣ_κ − ḣ_g) are the paper's values.  The moment step uses `moment_limit` (the
numerator of ∑C_θ/(w − a_θ) is the constant a), as run 23 recorded.  The injectivity of i ↦ g_i
uses 2n₁ ≠ N₀, which holds because n₁ = pp′ would give p ∣ p′r.

## 2026-11-22T11:56Z — main session: Prop 6.7 labelled (Stmt_sub_layer_chain_limit proved)

Proved by the main session (`../runs/lean2/checkP67.log`):
`ChainLim.sub_layer_chain_limit (hrec : GenericRecursionUniform) (hK : Cited_KacDeterminant) :
Stmt_sub_layer_chain_limit` (paper.tex l.1135–1148), in `Sec6LimGr` … `Sec6LimGr10` on top of the
germ computation `germ_chain` (`Sec6LimPhi` … `Sec6LimChain`).  Then
`prop_layer_coefficients_of_cited (hI) (hK) (hH) : Stmt_prop_layer_coefficients`
(`Sec6LayerFinal`, Paper label: prop:layer-coefficients), with `hrec = genericRecursionUniform hK hH`.
Axioms [propext, Classical.choice, Quot.sound]; no forbidden tokens in `Sec6Lim*`; statement files
unchanged; `lake build Virasoro` green (3907 jobs).  Labelled: 35 of 44.

Route: the paper's (l.1141–1146), its lowest-homogeneous-part argument written with power series in
`t` over `ℂ[S,W,Y]` whose `t^i` coefficient is homogeneous of degree `i` (the line
`(b⋆ + St, λ + Wt, Yt)`).  On `S = 1` the germ computation and the Kac formula give `P_i(1,·,·) = 0`
for `i < e` and `P_e(1, 2b⋆w, 2b⋆y) = T_N(w,y) D_e(1, 2b⋆w)`; homogeneity gives `P_i = 0`; on `S = 0`
the coefficients `[u^a d^n] P(c⋆, λ+u, d) = [W^a Y^n] P_{a+n}` give `[d^n]A = 0` (n < k) and
`[d^k]A = [W^{e−k}Y^k]P_e / T₁(0)`; the limit `w → ∞` of `w^k [y^k] T_N` is read off from the
`w`-degrees (both `e`) of numerator and denominator.  The order `e` of the denominator on both lines
comes from the Kac formula (the paper's "D_e(0,W,Y) = W^e·unit").  Differences: (1) the paper's
`b`-scaling of the chain sum is realised by evaluating the germ at `(2b⋆w, 2b⋆y)` (paper l.1139:
`T^b = T_N(W/(2b⋆), Y/(2b⋆))`); (2) the lemma is proved for every level `N`, the statement uses it at
`ℓ^±_k`.  Both are the paper's argument in coordinates.  Accepted.

## 2026-11-22T13:50Z — main session: Prop 6.8 labelled (Stmt_sub_h13_degree_chain proved)

Proved by the main session (`../runs/lean2/checkP68.log`):
`H13T.sub_h13_degree_chain : Stmt_sub_h13_degree_chain` (paper.tex l.1304–1378), in
`Sec6H13TGood`, `Sec6H13TProd`, `Sec6H13TGram`, `Sec6H13TTorus`, `Sec6H13TBr`, `Sec6H13TRho`,
`Sec6H13TGF`, `Sec6H13TPart`, `Sec6H13TStep`, `Sec6H13TChain`, `Sec6H13TRhoEnd`, `Sec6H13TFinal`.
Then `prop_h13_nonvanishing_of_cited (hK) (hH) : Stmt_prop_h13_nonvanishing` (`Sec6H13Label`,
Paper label: prop:h13-nonvanishing), via `prop_h13_nonvanishing_of_chain`.  Axioms [propext,
Classical.choice, Quot.sound]; no forbidden tokens in the new modules; statement files unchanged;
`lake build Virasoro` green (3920 jobs).  Labelled: 36 of 44.

Route: the paper's (l.1306–1378) in `ℚ[Y,Y⁻¹]⸨t⸩` with `c = 6/t + 13 + 6t`, `Δ = Y/t²`,
`d = −2/t + ζ`.  A family is good (`Good G D V`) when every `[t^iY^j]` is a polynomial in `M` of
degree ≤ `2(i+j) − D` and vanishes for `2(i+j) < V`; products add `(D, V)`.  Partitions are
`(1^{M−|μ|}, μ)` with all parts of `μ` at least 2 (l.1306–1309).  The E-step (l.1313–1332, `gram_step`) is
good from `|μ'|` with valuation `max(0, |μ|−|μ'|)`, the binomial `C(M−|μ'|, p)` vanishing on
`[|μ'|, |μ'|+p)` (root sets, l.1374–1378); the chain entries `K̂_s` follow by induction on `s`.  The
ρ̃ end (l.1333–1352) is the adjoint-Ward expansion `torus_ones` with the bracket of degree
`ℓ_b + ℓ_k` in `(c, Δ, d)` (`torBr_deg`).  Differences: (1) the factor `M^{\underline{w₀}}` is
taken out of the ρ̃ end and the two descending factorials `(M−w_b)^{\underline{p₁+r}}`,
`(M−w_k)^{\underline{k+q+s}}` serve as the root polynomial below the level where the three products
have polynomial coefficients; (2) the paper's "finitely many chains contribute" is the lemma
`GF.of_sum_sz`: the valuation of a term is at least its size, so each coefficient sees the terms of
size ≤ `2(i+j)` (+`w₀` in the chain step); (3) the terms of `torus_ones` with `k > a₀` vanish on
both sides (`a₀^{\underline{k}} = 0`) and are treated separately.  All three are the paper's
argument in coordinates.  Accepted.

## 2026-11-22T15:20Z — main session: Prop 6.9 and Cor 5.10 labelled

Proved by the main session (`../runs/lean2/checkP69.log`):
`prop_two_term_criteria_of_cited (hI) (hK) (hH) (hU) : Stmt_prop_two_term_criteria` (paper.tex
l.1419–1565, Paper label: prop:two-term-criteria) and
`cor_top_layer_sharp_of_cited (hJ) (hI) (hK) (hH) (hU) : Stmt_cor_top_layer_sharp` (l.892–917,
Paper label: cor:top-layer-sharp), in `Sec6TTFrame` … `Sec6TTCase3`, `Sec6TTLabel`.  Axioms
[propext, Classical.choice, Quot.sound]; no forbidden tokens; statement files unchanged;
`lake build Virasoro` green (3934 jobs).  Labelled: 38 of 44.

Route: the paper's (l.1428–1565).  `two_term_odd_of_core`: normalize `w^±_k` (`x = a·x̃`,
`a = x(1^ℓ) ≠ 0`, Lemma 5.7), the factorization of `τ^±_k` into `𝒫_{R,S}`, the rational model at
`b⋆` (`d_x = (x²−(p'−p)²)/(4pp')`) and `γ^±_k = [d^k]τ^±_k/(c_k(±ρ)^k)` (Prop 6.7) reduce `P_N ≢ 0`
to `coreP = τ⁺/[d^k]τ⁺·H⁺ + (−1)^kτ⁻/[d^k]τ⁻·H⁻ ≠ 0` over `ℚ`.  Case 1 (`s ∈ {1,p'−1}`): the
paper's solutions of `|p'a'±pl| = |p'−3p|` give `e_±`, `e₊ ≠ e₋`, and `H(d₁) ≠ 0` (Prop 6.8(iii)).
Case 2: the pairing `(2jℓ+3ε, 2jℓ+ε)` for `ℓ ≥ 5` and the triples `{6j+1,6j+3,6j+5}` for `ℓ = 3`
give the sign-independent `W`; the last sum vanishes (`m^±_k ≡ ±ps`); `M⁺ ≠ M⁻`.  Case 3: the
`ε`-identity `∏(x²−x₁(ε)²)·G(−2R) = ∏(x²−x₂(ε)²)·G(2R)` (the `A ↦ −A` cancellation, exact in
`ε`), cancelled by `ε^e` and evaluated at `ε = 0`, with the `v ↦ −v` cancellation, gives
`ord_{d₂} = ord_{d₁}` per factor and `T_k = −m⁻((m⁻)²−p²)/(m⁺((m⁺)²−p²))`; (6.4) at `t₀ = −p'/p`,
`Y^± = t₀²μ^±_k`, `e = v_ℓ(k)` gives `H_rat`.  Differences: (1) the paper's limit `ε → 0` is
the polynomial identity in `ε` divided by `ε^e` and evaluated at `0` (same cancellations);
(2) the `d₂`-order `k` follows from that identity rather than from a second count; (3) the
convention `v_ℓ(0) = 0` replaces "skipping" vanishing factors in Case 2 (the paper's
"both vanish" pairs contribute `0` on both sides).  All three are the paper's argument in
coordinates.  Accepted.

## 2026-11-22T15:56Z — main session: sphere Props 6.1 and 6.2 labelled

Proved by the main session (`../runs/lean2/checkS61.log`):
`Sphere.prop_c0_example_of_cited (hJ) (hI) (hK) (hH) (hF) (hU) : Sphere.Stmt_prop_c0_example`
(sphere/paper.tex l.1792–1810, Paper label: prop:c0-example) and
`Sphere.prop_ising_example_of_cited (hJ) (hI) (hK) (hH) (hF) (hU) : Sphere.Stmt_prop_ising_example`
(l.1812–1832, Paper label: prop:ising-example), proof l.1834–1849, in `Sphere/Proofs/Sec6Examples`
and `Sphere/Proofs/Sec6ExLabel`.  Axioms [propext, Classical.choice, Quot.sound]; no forbidden
tokens; statement files unchanged; `lake build Virasoro` green (3936 jobs).  Labelled: 40 of 44.

Route: the paper's.  At `N = ℓ₂ = ℓ^small_2` (`ellMin3`: `ℓ^ε_2 < ℓ₃`) the sphere top-layer theorem
(`thm:top-layer`, through `top_two`) leaves the single term `M = 0`; `small_value` evaluates it with
Lemma 5.2(ii) at `j = 1` and the second Jantzen norm, and Lemma 5.2(iii) at `(1/2, 0)` gives
`π ≠ 0`; levels below `ℓ₂` have Jantzen depth `≤ 1` (`jDepth_le_one`, Theorem 5.8 bound).  The
norms: `(2,3)`, `λ = 0`: `jform_norm_minus` is the torus Prop 6.7 for the normalized `w⁻_2`,
`τ⁻_2 = 𝒫_{1,1}𝒫_{1,4}` (the torus factorization `tau_min`), `[d²]τ⁻_2 = 2800/3` (`tau_c0`: the
double root `d = 0` from `x = 1` twice, times the product `1·1/3·10/3·2·7·5·12` of the other
roots), `c₂ρ² = −1/4`, so `γ₅ = −11200/3`.  Ising: the three norms of the torus Prop 8.1
(`prop_ising_double_poles_of_cited`), transported to `M(c⋆, h_{r,s}(b⋆))` by the uniqueness of the
normalized singular vector (`normalized_eq`, `gamma_transfer`; the paper's "the same second Jantzen
norm as on the torus", l.1838–1840).  Differences: (1) the Lean computes the identification of the
sphere's and the torus's normalized vectors explicitly from Cited_SingularUnique, which the paper
uses without comment; (2) `[d²]τ⁻_2` is read off the split `τ = d²·Q`, `Q(0) = ∏ d_x` over the
remaining roots, which is the paper's product.  Accepted.

## 2026-11-22T16:58Z — main session: Part II Lemma 13.1 labelled

Proved by the main session (`../runs/lean2/checkL131.log`):
`P2.lem_degenerate_quotient_t_of_cited (hK) (hE) (hH) (hU) (hF) (hLau) (hJ) (hI) :
Stmt_lem_degenerate_quotient_t` (paper.tex l.2851–3038, Paper label: lem:degenerate-quotient-t),
from Step 4 `P2.sub_tau_diag_limit_of_cited` (P2Sec13DiagRat, P2Sec13DiagOrth, P2Sec13DiagForms,
P2Sec13DiagTools, P2Sec13DiagFinal, P2Sec13DiagMain) and the second line of (13.3)
`P2.sub_tau_ratio_of_cited` (P2Sec13TauRatio).  Axioms [propext, Classical.choice, Quot.sound];
no forbidden tokens; statement files unchanged; `lake build Virasoro` green (3943 jobs).
Labelled: 41 of 44.

Route: the paper's Step 4 (l.2990–3028).  The trace in the basis `E` is the rational function
`trNum/det G_E` over `ℂ[b,b⁻¹]` (generic value = the trace, by uniqueness of `T^irr`).  Its
expansion at `b⋆` (`b = b⋆ + X`) through an orthogonal basis of `G_E` over `ℂ⟦X⟧` is
`∑_a ρ_X(v_a,v_a)/(X^{e_a}u_a)`; `e_a ≤ 1` by Step 3 and the exact kernel lifts of Step 2;
`e_a = 1` puts `v_a(0)` in `J¹ ⊂ rad ρ₀` (Prop 11.2(i) base case), so the expansion is a power
series.  `e_a = 0`: the `v_a(0)` are an orthogonal complement of `J¹_N`, giving
`T^irr_N(μ)`.  `e_a = 1`: `[X¹]B` and `[X¹]ρ` on lifts are well defined on `J¹`
(`J¹ ⊂ rad B₀ ∩ rad ρ₀`), satisfy the Ward identities with `d = 0` and `d⋆` (`[X¹]` of the
`n d(X)` term drops), so on `j₂(M(c⋆,ν₂))` they are `β·Shap_{ν₂}` and `β'·ρ_{ν₂,d⋆}`
(`ward_eq_smul_pairing`); `β' = Ω_{u,v}(μ→ν₂) β`, `β ≠ 0` is (13.3) (Thm 9.2 at `b⋆`
through `ℂ[b,b⁻¹]` and the reduced box fraction, Prop 12.1(i)); `v_a(0) = n_a + j₂(z_a)`
with `n_a ∈ M(ν₁)` (Lemma 10.3(i)), where `n_a` drops out by its kernel lift; the `z_a` are an
orthogonal complement of the radical of `M(c⋆,ν₂)_{N-R₂S₂}`, giving `Ω T^irr_{N-R₂S₂}(ν₂)`;
for `N < R₂S₂` there is no `e_a = 1`.  Differences: (1) the paper's congruence
diagonalization `Uᵀ B̄ U = diag(τ^{e_a}u_a)` is `exists_orth_basis` on the Gram matrix of `E`;
(2) the complement property of the `z_a` in `M(c⋆,ν₂)` is derived from `R_B = β·Shap_{ν₂}`
with `β ≠ 0` (the paper reads it off "a basis of `L(c⋆,ν₂)_{N-R₂S₂}`", l.2995–2996); (3) the
Ward identity is proved on `J¹(c⋆,μ)` and pulled back along `j₂` rather than stated on the
quotient `L(c⋆,ν₂)`, which carries the same content.  Accepted.

## 2026-11-22T17:21Z — main session: Part II Thm 9.3 labelled

Proved by the main session (`../runs/lean2/checkT93.log`):
`P2.thm_gen_rocha_caridi_of_cited (hK) (hE) (hH) (hU) (hF) (hLau) (hJ) (hI) :
Stmt_thm_gen_rocha_caridi` (paper.tex l.1926–1960, proof l.3040–3105, Paper label:
thm:gen-rocha-caridi), in P2Sec9GenRC … P2Sec9GenRC5.  Axioms [propext, Classical.choice,
Quot.sound]; no forbidden tokens; statement files unchanged; `lake build Virasoro` green
(3948 jobs).  Labelled: 42 of 44.

Route: the paper's.  (9.3): Lemma 13.1 at a node, multiplied by `Ω(λ→μ)q^{μ-λ}`, with the
cocycle `Ω(λ→μ)c(μ→ν) = Ω(λ→ν)` (Prop 12.1(ii) path independence; `pathProd_append_single`)
gives `T̃(μ)+T̃(ν₂) = F̃(μ)-F̃(ν₁)` (`scaled_step`); along the alternating chain `σ_j = (j even)`
the two sides telescope (`telescope_left`, `telescope_right`, `K = N`, layer `N+1` absent).
Regularity at the orbit: Thm 9.1.  (a): `d = 0`, `cMM = 1` at `k = m = 0`, `F_N(c,Δ,0) = p(N)`
(`torus_zero`).  (b): (9.3) with `Ω ∈ ℚ` and `F_M(c⋆,μ,d) ∈ ℚ` (`Fnum_map`: the coefficients
come from `ℚ`; `Fval_rat`: at the rational regular point `μ` the value is
`[e'=e]A(μ)/B(μ)` from the root-multiplicity factorizations).  (c): the inverse form
`F̃(μ) = ∑_{ν⪰μ} T̃(ν)` (`inv_formula`), compared with Prop 11.2(ii) by strong induction on the
pairwise distinct levels `ℓ^±_j` (`ellOrb_inj`: monotone across layers, `ℓ⁺_j ≠ ℓ⁻_j`), with
`T^irr_0 = 1` (Lemma 13.1 at level 0); the family of Theorem 5.8 is transported to the orbit
setting at `μ⁺_0 = λ`.  Differences: (1) the inverse form is derived by downward induction on the
layer from the scaled two-term identities, where the paper inverts the unitriangular zeta matrix
of the braided poset (l.3091–3100); the identity is the same; (2) for (b) the paper computes
`T^irr_N` through Theorem 4.3 (general confluence); the Lean uses (9.3) and the rationality of
`F_M` at rational regular points, which is what (b) claims (`T^irr_N ∈ ℚ`).  Accepted.

## 2026-11-22T18:01Z — main session: sphere Thm 5.4 labelled

Proved by the main session (`../runs/lean2/checkT54.log`):
`Sphere.thm_sharp_B_of_cited (hJ) (hI) (hH) (hF) (hU) (hBPZ) (hK) : Stmt_thm_sharp_B`
(sphere/paper.tex l.1607–1615, proof l.1617–1691, Paper label: thm:sharp-B), in
Sphere/CitedBPZ, Sphere/Proofs/Sec5SharpLam, Sec5SharpPoint, Sec5SharpB.  Axioms [propext,
Classical.choice, Quot.sound]; no forbidden tokens; statement files unchanged; `lake build
Virasoro` green.  Labelled: 43 of 44.

Route: the paper's.  `k = j_N(λ) = 0`: Thm 5.1.  `k ≥ 1`: Thm 5.3 gives pole order at most `k`
and the coefficient of `(Δ-λ)^{-k}` as the sum of the two summands; each summand is the image
in `K4 = ℂ(Δ₁,…,Δ₄)` of a polynomial in `Δ₁,…,Δ₄` (`topR`, `topTermSph_eq_topR`, through
`evalBsph_K4` and `piScalar_K4`), and the sum of the two polynomials is evaluated at the
rational point of l.1621–1628 (`bpzWeights b (-m/p) (a₃/p) (β4of …)`, `bpzWeights_min`):
(a) `π^big(Δ₄,Δ₃) = 0` by Lemma 5.2(iii), since `a₄ - a₃ = -(m^big - p' - p)`; (b) the two
lower-branch factors are nonzero by Lemma 5.2(iii), applied to the normalized vector
(`pi_iii_any`); (c) `ℬ_M = (-1)^M binom(κ,M)` (`block_point`) with `κ = (kp-1)p'/(2p) ∉ ℕ`
(`kappa_ne_nat`).  Differences: (1) for (c) the paper writes `ℬ_m = [z^m]((1-z)^κ ₂F₁(A,B;C;z))`
as an identity of rational functions; the Lean takes the BPZ equation coefficientwise at
generic `b` (`b ≠ 0`, `b² ∉ ℚ`, every `G_m(c(b),μ)` invertible), carries it to `b⋆` through
`ℂ[b,b⁻¹]` (identity principle, `Sec5SharpLam`), and at `b⋆` checks that `(-1)^n binom(κ,n)`
satisfies the same recursion (`gSeq_rec`, `B = 0`) with `P₀(s+n) = n(n-1+C)/b² ≠ 0` for
`n ≤ M`; the paper's item 1 (`C = 1-u` forces `μ = h_{1,u}`, `det G_M = 0`) is the argument for
`P₀ ≠ 0`.  The `₂F₁` closed form itself is not formalized; at `B = 0` it is `(1-z)^κ`, which is
what is checked.  (2) In (b) the Lean uses `c₀ ≤ |c₀|` and `m^small < m^big` (from
`ℓ^small < ℓ^big` and `m^small + m^big = 2kpp'`); the paper's `m^small - p' - p ≥ 0` is not needed.
Accepted.

New cited input `Sphere.Cited_BPZEquation` (Belavin–Polyakov–Zamolodchikov 1984, eqs (5.2),
(5.17), (5.19); sphere l.1651–1661): the coefficient of `z^{s+n}` of the displayed equation times
`z²(z-1)²`, `s = μ - Δ₁ - Δ₂`.  Checks of the transcription: at `n = 1` the recursion gives
`ℬ₁ = -u(s+D)/C`, the level-1 block (hand check); at `B = 0` the coefficients of `(1-z)^κ`
satisfy the encoded recursion for all `n` (`gSeq_rec`, machine-checked).

## 2026-11-22T18:46Z — main session: sphere Thm 5.5 labelled; all 44 results labelled

Proved by the main session (`../runs/lean2/checkT55.log`):
`Sphere.thm_sharp_H_of_cited (hJ) (hI) (hH) (hF) (hU) (hS) : Stmt_thm_sharp_H`
(sphere/paper.tex l.1693–1701, proof l.1703–1787, Paper label: thm:sharp-H), in Sphere/CitedSchur
and Sphere/Proofs/Sec5SharpHRep, Sec5SharpHHerm, Sec5SharpHSym, Sec5SharpHLog, Sec5SharpH.
Axioms [propext, Classical.choice, Quot.sound]; no forbidden tokens; statement files unchanged;
`lake build Virasoro` green.  Labelled: 44 of 44.

Route: the paper's.  `k = 0`: Thm 5.1.  `k ≥ 1`: the H clause of Thm 5.3; each summand is the image
in `K4` of a polynomial in `Δ₁,…,Δ₄` (`topRH`; `HR` from the universal polynomials of `Φ̃⁻¹`,
`isPolyFamU_PhiTilde_inv`).  Specialization `ψ : (Δ₁,Δ₂,Δ₃,Δ₄) ↦ (μ, 0, wt((w+X)/2), wt((w−X)/2))`
(the paper's line with `w = √(pp')·v`).  (1) `π^big(Δ₄,Δ₃) ≡ 0` in `w` (Lemma 5.2(iii)); (2)
`π^small(Δ₄,Δ₃) ≢ 0` (nonzero at `w = 1/2`) and `π^small(μ,0) ≠ 0`; (3) `ℬ_m = δ_{m0}` at
`(μ,0)` (`gammaY_self_zero`), so `H_M = [q^M]Φ̃⁻¹/16^M`; over `ℂ`, `Φ̃⁻¹ = exp(S)`
(`exp_smul_log`), on the line `S = s₀ + w s₁ + w² s₂` with `s₂ = O(q²)`; the filtration
`deg_w [q^n] ≤ n` (`Fil`, `sym`) gives `[w^M][q^M] exp(S) = [t^M] exp(−bt − gt²)`,
`b = 2X/(pp')`, `g = 1/(pp')`; (4) `k_M = M![t^M]exp(−bt − gt²)` satisfies the Hermite
recurrence, `k_{2m} = g^m E_m(r)`, `k_{2m+1} = −(b/2)g^m O_m(r)`, `H_{2m} = E_m(x²)`,
`H_{2m+1} = x O_m(x²)`, `r = X²/(pp') = α²`; `M ≤ 3` explicit, `M ≥ 4` Schur.
Differences: (1) the variable `w = √(pp')·v` makes every coefficient rational; the leading
coefficient is `k_M/(16^M M!)` in place of `(−1)^M H_M(α)/(16^M M!)`, a nonzero multiple of it.
(2) The paper's rewriting of the `v`-dependent factor as `(θ₃θ₄)^{v²/4}(θ₄/θ₃)^{αv/2}` through
`1 − z = (θ₄/θ₃)⁴` is not used: the Lean reads `[q]`, `[q²]` of `log(1−z)` and `log θ₃` off
`z = 16q − 128q² + …` and `θ₃ = 1 + 2q + 0q² + …` (`coeff_zq_one'`, `logS_coeffs`), so no Jacobi
input is needed.  (3) For `M = 3` the paper's monotonicity of `(x−1)²/x` is replaced by a case
split on `p, p'` (`X_arith`); for `{p,p'} = {2,3}` the momenta are odd, so `X ≠ 3`
(`X_ne_three_exc`), where the paper computes `X = 2` and `X ≥ 8`.  (4) For `M ≥ 4` the paper
argues in `t = x²`; the Lean argues in `x`: a rational root `r` of `E_m` gives the factor
`x² − r` of `H_{2m}`, impossible for degree `2m ≥ 4` (`no_root_of_irreducible`), the same
argument.  Accepted.

New cited input `Sphere.Cited_SchurHermite` (Schur 1929, Schur 1931; sphere l.1775–1778): for
`m ≥ 1`, `H_{2m}` and `H_{2m+1}/x` are irreducible over `ℚ`, with `H_n` the physicists' Hermite
polynomials by the three-term recurrence (DLMF 18.9.1); `H₂ = 4x² − 2` and `H₃ = 8x³ − 12x` are
machine-checked (`hermH_two`, `hermH_three`).

State after this entry: every result of paper.tex and sphere/paper.tex at 70bac53 has a labelled
Lean theorem from `Cited_*` inputs only (author-side check by the main session, not a reviewer
PASS).  Still open on the Lean side: the route repairs queued in the entries above (brief-phaseB.md
item 5), where a Lean proof differs from the paper's argument without being forced to.

## 2026-11-22T19:20Z — main session: route repairs RR1–RR3 (Part II, brief-phaseB.md item 5)

Checked by the main session (`../runs/lean2/checkRR1.log`): `lem_bgg_arrows_of_cited`,
`prop_bgg_cocycle`, `P2.thm_gen_rocha_caridi_of_cited` keep axioms [propext, Classical.choice,
Quot.sound]; statement files unchanged; `lake build Virasoro` and `lake build Virasoro.PartIIWork`
green.  The proofs now follow the paper at three places queued above:
- RR1, Lemma 10.3(ii) uniqueness (l.2241–2247): `nOrb_not_dvd` (p ∤ n_μ, p′ ∤ n_μ from (10.5)),
  `arrowLabel_eq_of_not_dvd` (if both signs made `n_ν ± n_μ` divisible by `2p′`, then
  `p′ ∣ n_μ`), and the uniqueness step reduces to `p′ ∣ n_μ`; `p′ ∤ S` is no longer used there.
- RR2, Lemma 10.3(iii) (l.2249–2262): (10.11)–(10.12) by reducing `p′R − pS = ±n_μ` modulo `p`
  and `p′` (`nOrb_mod`, `congr_of_reduce`); (10.13) from `0 < n_ν − |n_μ| < 2pp′` for every
  consecutive pair (`nOrb_gap`, the paper's eight differences) and `small_of_gap`.  The label
  table `arrow_data` now supplies only existence with `R, S ≥ 1`, as in the paper (l.2246–2247).
- RR3, Prop 12.1(ii) (l.2803–2822): `psiNode_ne_zero` evaluates the Gamma potential at `ϖ_μ`
  directly; the arguments `1 + (±n_μ − jp)/p′` and `1 + m + (±n_μ − ip′)/p` are not integers
  because `n_μ ≡ ±ps (mod p′)`, `n_μ ≡ ±p′r (mod p)` and `1 ≤ j ≤ m < min(s,p′−s)`,
  `1 ≤ i ≤ k < min(r,p−r)`; the label `(R,S)` is no longer used there.

## 2026-11-22T19:29Z — main session: route repair RR4 (sphere Lemma 3.7, Step 4)

Checked by the main session (`../runs/lean2/checkRR4.log`): `Sphere.lem_central_charge_of_cited`,
`Sphere.thm_large_delta_of_cited` keep axioms [propext, Classical.choice, Quot.sound]; statement
files unchanged; `lake build Virasoro` green.  `exp_Phi_eighth` (sphere l.1174–1176) now follows
the paper: `(Φ₁+Φ₂)/8 = −½ log θ₃ − ½ log θ₄ = −⅛ log(1−z) − log θ₃` (Lemma 3.6's closed forms,
`log(fg) = log f + log g`, `log f^k = k log f`, and `(1−z)θ₃⁴ = θ₄⁴`), so
`exp((Φ₁+Φ₂)/8) = (1−z)^{−1/8} θ₃^{−1}`, which is `det(I−M²)^{−1/2}` by Lemma 3.5 in its
`fpow` form.  The comparison of 8th powers (`detInvSqrt_pow_eight`, `eq_of_pow_eq`) is gone from
this step.  `Sec3FpowExp` now imports only `Sec3ExtExp`, `Sec3ExpLog`, `FpowBinom`, and
`Sec3CentralFinal` imports it.

## 2026-11-22T19:49Z — main session: route repair RR5 (Prop 8.1) and the status of the other queued repairs

Checked by the main session (`../runs/lean2/checkRR5.log`): `prop_ising_double_poles_of_cited`,
`Sphere.prop_c0_example_of_cited`, `Sphere.prop_ising_example_of_cited` keep axioms [propext,
Classical.choice, Quot.sound]; statement files unchanged; `lake build Virasoro` green.

RR5, Prop 8.1 (paper.tex l.1755–1771): the three rows now follow the paper (new file
`Proofs/Sec8IsingTop.lean`).  At `N = min(ℓ⁺₂, ℓ⁻₂)` (7, 10, 11) equation (5.1) of Theorem 5.9
has the single term `τ/γ` with `M = 0` (`top_two_single`, `top_two_single_plus`); Proposition 6.7
with `c₂ = -1` applied to the same family gives `[d²]τ = -γρ²`, `ρ = -(4r-3s)/2`
(`core_single`); the pole order `2` is Corollary 5.10.  `γ` is computed from `[d²]τ`:
`[d²](𝒫_{2,1}𝒫_{1,5}) = 4379375`, `[d²](𝒫_{1,2}𝒫_{4,2}) = 1121229484375/192`,
`[d²](𝒫_{1,1}𝒫_{2,5}) = 9911668641875000/104976` (`coeff_E2_P15`, `coeff_P2_P42`,
`coeff_P11_P25`), giving `γ = -700700, -1121229484375/192, -2477917160468750/6561` as printed.
The earlier route (the double pole read off Theorems 8.5 and 9.4 or Proposition 7.7, and `γ`
from the PBW evaluation of Lemma 5.4(iii)) is no longer used for Prop 8.1; the PBW values remain
in the tree (`x7_ker2_gamma`, used by `Sec8Smith7`) and agree, as the paper's remark after the
proof says.

Status of the other items of brief-phaseB.md item 5, re-examined against the formal setting:
- Forced.  Torus Prop 6.4 and sphere Prop 4.4, residue from Lemma 5.4 with `k = 1`: the frozen
  Lemma 5.4 quantifies over complex `c, h`, while the residue is needed over every field of
  characteristic zero (`GenericRecursionUniform`, the field re-run in sphere Theorem 4.7);
  `residue_inverse` is Lemma 5.4(iii) at `k = 1` over such a field.  Lemma 13.1 Step 2 and
  Prop 11.2 `layer_kernel`, freeness of `M(c,h)` over `U(Vir₋)`: the argument needs that
  `U(Vir₋)` has no zero divisors (PBW leading terms), which the tree does not have; the Lean uses
  the injectivity of singular embeddings that the paper cites for the same step in Part I
  (l.855, 1038, 1761).  Prop 11.2, `J^i/J^{i+1} ≅ L ⊕ L` and the orthogonality of non-isomorphic
  irreducibles: needs quotient and contragredient modules, which the tree does not have (the same
  reason as the forced trace item of Part II run 3).  Torus Prop 6.8(i), the local ring `𝒪_𝔭`:
  needs that the localization is a DVR with uniformizer `ℓ`, not in Mathlib.  Sphere Lemma 3.6,
  the change of variables `p = p(w)` in the contour representations of `g(±1)`: the formal
  setting has no contour integrals; the Lean computes the same coefficients `c^±_m` from their
  closed forms.
- Not needed in the formal setting.  Sphere Theorem 4.7, holomorphy of `C_{λ,k}(t)` before
  taking `t⁰` (l.1405–1417): the paper's holomorphy step justifies evaluating at `t = 0`; the Lean
  takes the coefficient of `t⁰` of the Laurent identity, which needs no holomorphy, and obtains
  the same `Ã = [t⁰]C_{λ,k}`.
- Still queued (not forced): sphere Lemma 3.4(iii) through (3.6) coefficientwise in `z`;
  Lemma 3.5, the double pole at `x₁ = x₂` through `S(x,x) = Y²`, `∂₁S(x,x) = YY'`; Lemma 3.3,
  uniqueness and regularity through the injectivity of `𝒟_m(∞)` (lowest degree) and an
  invertible square minor; Lemma 3.6, the `σ¹` generating-function identity as a rational
  identity in `(s₁, s₂)`.

## 2026-11-22T20:15Z — main session: Cited_SchurHermite restated to Schur's own statement

Trigger: yang2's review of packet virasoro-20261122T195905Z-prose-fixes-lean-citations, Item 3b
(PASS of the statement and its use, with the request to document the normalization bridge).
The main session read Schur 1931 pp. 52–54 (GDZ scans): p. 52 defines `H_m(x) = (-1)^m
e^{x²/2} d^m/dx^m e^{-x²/2}`, the monic `He_m`; Hilfssatz D on p. 54 states that `x⁻¹H₃, H₄,
x⁻¹H₅, H₆, …` are irreducible over `ℚ`, quoting the 1929 paper (footnote 5, p. 53).  The old
`Cited_SchurHermite` asserted irreducibility of the physicists' `H_{2m}`, `H_{2m+1}/x` (`m ≥ 1`),
which is not the source's statement (the rescaling `x ↦ √2 x` is not rational).

Change.  `Cited_SchurHermite` now states Hilfssatz D for `He_{2m}` and `He_{2m+1}/x` with `m ≥ 2`
(the range the consumer uses: `hermEO_no_root`, case `M ≥ 4`).  New in Sec5SharpHHerm:
`hermHe_two` (definition check, `He₂ = x² − 1`), `schurE`, `schurO` (Schur's `K⁰_m`, `K¹_m`),
`hermHe_K` (`He_{2m} = K⁰_m(x²)`, `He_{2m+1} = x K¹_m(x²)`), `hermEO_scaled` (`E_m(t) = 2^m
K⁰_m(2t)`, `O_m(t) = 2^{m+1} K¹_m(2t)`), `natDegree_schurEO`; `hermEO_no_root` now evaluates at
`2r`.  `hermH` moved from CitedSchur to Sec5SharpHHerm.  The paper's proof of Theorem 5.5, case
`M ≥ 4` (sphere l.1788–1807), was rewritten the same way first; the Lean mirrors it.
Checked by the main session (`../runs/lean2/checkSCH1.log`): `thm_sharp_H_of_cited`,
`thm_sharp_B_of_cited`, `hermEO_no_root` keep axioms [propext, Classical.choice, Quot.sound];
full build exit 0; no forbidden tokens.  Author-side check, not a reviewer PASS.

## 2026-11-22T20:23Z — main session: Jander's Item 3a note (stale doc pointers in CitedBPZ)

Jander's review of packet virasoro-20261122T195905Z-prose-fixes-lean-citations, Item 3a: PASS of
`Cited_BPZEquation` and its use (Sec5SharpLam, Sec5SharpPoint, Sec5SharpB), with the request to
refresh the stale line pointers in Sphere/CitedBPZ.lean.  The pointers now name the proof of
Theorem 5.4 (Paper label: thm:sharp-B), step (c), and the opening of §4 (sec:confluence) instead
of line numbers.  Doc comments only; full build exit 0.

Item 1, A1: the Iohara–Koga locators were checked in the book (Pdfs2 copy): Theorem 4.2 is the
Kac determinant formula (4.16) on pp. 137–138; (4.21) is its form with the roots `h^±_{r,s}(c)` in
the proof (§4.4.2); Proposition 5.1 (§5.2.1) states `dim {M(c,h)_{h+n}}^{Vir+} ≤ 1`.  No paper
change was needed for A1.

## 2026-11-22T20:48Z — main session: route repair RR6 (sphere Lemma 3.6, the `σ¹` generating functions)

Queued item "Lemma 3.6, the `σ¹` generating-function identity as a rational identity in
`(s₁, s₂)`" (2026-11-22T19:20Z entry, "Still queued").  The Lean now follows the paper's proof of
Lemma 3.6: the `σ¹`-part generating function
`q∂_q((pC(q) − qC(p))/(q−p) − p/(1−p) C(q)) − B(p,q)C(p)` equals `p/(2(1−p)²) C_+(q)` for `g(1)`
and `−p/(2(1−p)) C_−(q)` for `g(−1)`, proved as rational identities in `s₁ = √(1−p)`,
`s₂ = √(1−q)` (`alg_ext_plus`, `alg_ext_minus`, new file Sphere/Proofs/Sec3ExtSigma1.lean),
transported to series in `(p,q)` through the fraction field as for Lemma 3.4(i)
(`ext_sigma1_plus`, `ext_sigma1_minus`), and read off at `p^k q^m` (`sigma1_plus_Icc`,
`sigma1_minus_Icc`), which are the `σ_m`-coefficients of `L_k^{(0)} g(±1)` used by `L0_gAt_one`,
`L0_gAt_neg_one`.  The factor `i` of `C_±` is carried outside the series.  The earlier route
(`sum_weighted_hB`, `sum_weighted_hB_Icc`, `sum_hB_Icc`, from `sum_halfBinom_Bcoef` and a binomial
recursion) is deleted; `hb_rec` moved to the new file.  Before writing the Lean, both identities
were checked symbolically (sympy, `../runs/route36/check_sigma1.py`, difference 0).

Checked by the main session (`../runs/lean2/checkRR6.log`): `lem_ext_exponents_of_cited`,
`lem_central_charge_of_cited`, `thm_large_delta_of_cited` keep axioms [propext,
Classical.choice, Quot.sound]; full build exit 0; no forbidden tokens; Statements files
unchanged.  Author-side check, not a reviewer PASS.

Still queued: sphere Lemma 3.4(iii) through (3.6) coefficientwise in `z` (with the Lemma 3.6
coefficients of `g(±1)`, which the Lean takes from closed forms); Lemma 3.5, the double pole at
`x₁ = x₂` through `S(x,x) = Y²`, `∂₁S(x,x) = YY'`; Lemma 3.3, uniqueness and regularity through
the injectivity of `𝒟_m(∞)` and an invertible square minor.

## 2026-11-22T21:05Z — main session: route repair RR7 (sphere Lemma 3.5, the double pole at `x₁ = x₂`)

Queued item "Lemma 3.5, the double pole at `x₁ = x₂` through `S(x,x) = Y²`, `∂₁S(x,x) = YY'`".
The Lean now follows Step 2 of the paper's proof: the numerator
`N(x) = [z^j](Y(x) + g(x₂)S(x,x₂))` is holomorphic near `x₂`; `N(x₂) = 0` by `S(x,x) = P(x) = −Y(x)²`
(`pole_num_zero`) and `N'(x₂) = 0` by `∂₁S(x,x) = ½P'(x) = −Y(x)Y'(x)` (`dser_Sser_diag`,
`Yser_dser`, `dser_pole_num`), in the branch `Y = x√(1−x)√(1−z/x)` of the formal setting (`Y² = −P`;
the paper's `Y` differs by the constant factor `±i`).  Two divided differences give the bounded
quotient (`bddNear_of_double_zero`, via `Complex.differentiableOn_dslope`), and `bddNear_pole` is
what `sub_bergman_const_of_patches` consumes.  The coefficientwise derivative in `x` is `dser`,
with the product rule `dser_mul`.  New file Sphere/Proofs/Sec3BergmanPole.lean.  The earlier route
(`pole_identity` through `S² − P₁P₂ = ¼(x₁−x₂)²(x₁x₂−z)²` and `tendsto_coeff_of_mul`) is deleted;
`Sser_sq` stays, as the coincidence limit of the zero-mode step (accepted fill-in, run 11) uses it.

Checked by the main session (`../runs/lean2/checkRR7.log`): `lem_bergman_det_of_cited`,
`lem_central_charge_of_cited`, `thm_large_delta_of_cited` keep axioms [propext,
Classical.choice, Quot.sound]; full build exit 0; no forbidden tokens; Statements unchanged.
Author-side check, not a reviewer PASS.

Still queued: sphere Lemma 3.4(iii) through (3.6) coefficientwise in `z`; Lemma 3.3, uniqueness
and regularity through the injectivity of `𝒟_m(∞)` and an invertible square minor.

## 2026-11-22T21:31Z — main session: route repair RR8 (sphere Lemma 3.3(i), regularity through a square minor)

Queued item "Lemma 3.3, uniqueness and regularity through the injectivity of `𝒟_m(∞)` and an
invertible square minor".  `regular_of_pde` (Sec3LamRegular.lean; consumer `SL_regular`,
unchanged statement) now follows the paper: by induction on the level `m`, the level-`m`
equations of (3.3) form the rectangular system `𝒟_m(λ)S_m = R_m` (`linLamL`, `coeff_linLam_level`:
the coefficient of `σ^β`, `lvl β + k = m`, of `D_k(λ)T` reads only the level-`m` coefficients of
`T`), with `R_m` regular by the induction hypothesis; its value at `λ⁻¹ = 0` is `𝒟_m(∞)`,
injective by the lowest-degree argument (`Dinf_injective`); an invertible square minor of the
value (`exists_square_minor`) gives a left inverse regular in `λ⁻¹` (`regular_of_rect_system`).
New files Sphere/Proofs/Sec3LamMinor.lean, Sec3LamLevelSys.lean.  The earlier route (the order
in `t` raised one step at a time by an induction on the polynomial degree) is deleted.  The
linearity lemmas `pdA_add`, `pdA_sub`, `pdA_smul`, `pdA_C`, `shiftA_add`, `shiftA_smul`,
`levelA_add`, `levelA_smul` moved from Sec3LamOrderZero.lean to Sec3LamOps.lean (import order).
Uniqueness of `S` is unchanged: it comes from the unique Ward solution (Lemma 3.2(ii)), as the
paper's "its unique solution" refers to the solution of the Ward equations.

Checked by the main session (`../runs/lean2/checkRR8.log`): `lem_lambda_expansion_of_cited`,
`thm_large_delta_of_cited` keep axioms [propext, Classical.choice, Quot.sound]; full build
exit 0; no forbidden tokens; Statements unchanged.  Author-side check, not a reviewer PASS.

Still queued: sphere Lemma 3.4(iii) through the Wiener–Hopf identity (3.6), coefficientwise in `z`.

## 2026-11-22T22:27Z — main session: route repair RR9 (sphere Lemma 3.4(iii) through (3.6); Lemma 3.6 coefficients)

Queued item "sphere Lemma 3.4(iii) through (3.6) coefficientwise in `z` (with the Lemma 3.6
coefficients of `g(±1)`)".  The Lean now follows the paper's proof of Lemma 3.4(iii) at each order
`z^K`, with `p(w) = 4w/(1+w)²`, `s(w) = (1−w)/(1+w)`, and `p(w)^{-m}` carried as
`P_m = (1+w)^{2m} = 4^m w^m p^{-m}` (new files Sphere/Proofs/Sec3WHSeries.lean,
Sec3WHIdentity.lean, Sec3WHSaddle.lean, Sec3WHValues.lean):
- `s² = 1 − p`, `(1−p(w))^{-1/2} s(w) = 1`; `w∂_w p^{-m} = −m s p^{-m}` (`X_deriv_Pm`, via
  `PowerSeries.derivative`); the change of variables `[w^0](s p^{-m} G(p(w))) = [x^m]G`
  (`coeff_change_var`).
- `x^K Ω(x) = (∑_l c_l x^{K−l})(1−x)^{-1/2}` (`laurent_OmP`, from `OmegaCoef`); substituting
  `x = p(w)`: `H(w) = s Ω(p) = ∑_l c_l p^{-l}` and `= sΩ_+(p) + ∑_m [z^{K−m}]a_m s p^{-m}`
  (`H_two_ways`); `H` is even in `w ↔ w⁻¹`; comparing `[w^{∓n}]` gives (3.6):
  `[w^n](sΩ_+(p)) = 2nτ_n` (`n ≥ 1`), `δ_{K0}` (`n = 0`), with `t_{*,n} = iτ_n`
  (`WH_identity`, `WH_identity_zero`).
- Saddle-point equations: `∂_{σ_m}S^{(0)}(σ_*) = [w^0]p^{-m}(−4iw/(1+w) + 2ig_*(w))` from
  part (ii) (`Bcoef_eq_sum_psi`, `alt_sum_psi`), then (3.6) and the change of variables give
  `−2i a_m` (`Dd_eq`, `sum_psi_Dd`, `coeff_aSer_WH`); `coeff_aSer` now has this proof.
- Values: by (3.6), `1 − g_*(w)` is a polynomial at each order, and `H_two_ways` becomes a
  polynomial identity (`Hpoly_eq`); evaluating at `w = 1` and `w = −1` (where `s p^{-m}` vanishes)
  gives `1 − g_*(1) = (₂F₁√(1−z))⁻¹`, `1 − g_*(−1) = ₂F₁⁻¹` (`one_sub_gAt_one_WH`,
  `one_sub_gAt_neg_one_WH`); `gStar_one`, `gStar_neg_one` now use them.
- Lemma 3.6: the coefficients of `g(±1)` by the change of variables in the contour representation
  (`nSer_eq`: `w/(1−w)² = s G₊(p)`, `G₊ = (x/4)(1−x)^{-3/2}`; `nAltSer_eq`: `−w/(1+w)² = s G₋(p)`,
  `G₋ = −(x/4)(1−x)^{-1/2}`), giving `sum_n_psi`, `sum_n_alt_psi`.  The 2026-11-22T19:20Z entry had
  classed this item as forced ("no contour integrals"); with `coeff_change_var` it is not forced, and
  it now follows the paper.
Deleted: Sec3SaddleSt.lean (`B = −q∂_q(√(1−q)D)` route: `alg_saddle`, `Bgf_eq_pderiv`,
`halfBinom_add`); in Sec3SaddleVal.lean the closed-form `ψ_n` sums (`trunc_sum2`,
`coeff_natCast_mul_sum`), `ySer`, `ySer_one`, `ySer_two`, `coeff_conv_F`, `two_mul_coeff_sOne`,
`sum_sOne_hser`; in Sec3SaddleValC.lean `one_sub_subst_lin`, `one_sub_gAt_one`,
`one_sub_gAt_neg_one`, `gAt_neg_one_coeff`.

Checked by the main session (`../runs/lean2/checkRR9.log`): `lem_saddle_of_cited`,
`lem_ext_exponents_of_cited`, `lem_central_charge_of_cited`, `thm_large_delta_of_cited` keep axioms
[propext, Classical.choice, Quot.sound]; full build exit 0; no forbidden tokens; Statements
unchanged.  Author-side check, not a reviewer PASS.

State after this entry: the queued sphere §3 route repairs are done (RR6–RR9).  The remaining route
differences are the ones classed as forced in the 2026-11-22T19:20Z entry (residue via Lemma 5.4
over general fields; freeness over `U(Vir₋)`; `J^i/J^{i+1} ≅ L⊕L`; the DVR in Prop 6.8(i)) and
the fill-ins recorded in the run entries.

## 2026-11-24T03:52Z — main session: mirror check against the papers of 2026-11-24

User request (tmp terminal, 2026-11-24 about 11:2x Taiwan), after the note that the presentation
passes had repackaged results: "yes i want it" (have the Lean statements checked against the
current papers).

Compared: every theorem-type environment of paper.tex and sphere/paper.tex at c3035e0 against
70bac53 (the freeze), by label, with word diffs of the statement texts (45 changed statements: 27
torus, 18 sphere; new labels lem:ward-induction and prop:gaussian-limit; none removed).
Findings, each against the frozen `Stmt_`:
- Wording, notation and renumbering only (no Lean change): all changed statements except the four
  below.  Prop 6.8 (`prop:h13-nonvanishing`) now numbers its last clause (iv) and spells out the
  quantifiers of (iii); Thm 10.1 (`thm:descent-regularity`) numbers its extra conclusions (iii),
  (iv): the frozen statements already contain these clauses as conjuncts.
- Torus Lemma 11.2 (`lem:ward-induction`), new: `Stmt_lem_ward_induction` at the minimal-model
  charge, proved as `lem_ward_induction` by `Verma.ward_induction` (the paper's two inductions,
  already used for Prop 11.3); no cited input.
- Torus Theorem 7.6 (`thm:general-confluence`), restated without the precision rule and the
  power-series form: `Stmt_thm_general_confluence_paper`, proved from the 70bac53 form
  (`thm_general_confluence_paper_of_cited`).
- Sphere Lemma 3.3 / Proposition 3.4 (`lem:lambda-expansion`, `prop:gaussian-limit`): the old
  part (iii) is now Prop 3.4.  `Stmt_lem_lambda_expansion_paper` (parts (i), (ii)) and
  `Stmt_prop_gaussian_limit`, both proved by dropping conjuncts of the 70bac53 form.
- Sphere Lemma 5.2(iii) (`lem:pi-factorization`) now says the zero locus is a union of lines,
  adds the nonvanishing clause and the symmetry under `(x_a,x_b) ↦ (-x_a,-x_b)`.
  `Stmt_lem_pi_factorization_paper` states all of it; the new part, that each zero lies on a whole
  line of the zero locus, is proved from the linear factors of `P_{R,S}` (`fusP_zero_line`,
  `line_of_factor`) with the paper's case split on the parity of `k` and the sign.
New files: Statements/Rev20261124.lean, Proofs/Rev20261124.lean, Sphere/Statements/Rev20261124.lean,
Sphere/Proofs/Rev20261124.lean, imported in Virasoro.lean.  Frozen statement files unchanged.
Index of current paper numbers: PAPER_MAP.md (59 numbered theorems, lemmas, propositions and
corollaries, all with a labelled theorem; 11 definitions).

Checked by the main session: `lake build Virasoro` exit 0, 4157 jobs (../runs/lean2/rev-build3.log);
the five new labelled theorems and all 63 theorems of PAPER_MAP.md depend only on
[propext, Classical.choice, Quot.sound] (../runs/lean2/checkREV.log, checkMAP.log); no
sorry/admit/axiom in the new files.  Author-side check, not a reviewer PASS.

## 2026-11-25: three-paper split (main session)

The manuscripts were split into three on the user's decision (tmp terminal, 2026-11-25, time not
recorded, "three papers. fix gaps,commit,push."): `sphere/paper.tex` keeps the large-weight
limit (old sphere Sections 2-3, Appendix A; numbers unchanged), `paper.tex` holds the torus Verma
results (Part I, old Sections 2-8 reordered) and the old sphere Sections 4-6 (Part II, clashing
labels with suffix `-sph`), and `irreducible/paper.tex` holds the old torus Sections 9-14, whose
Section 2 quotes statements of `paper.tex` verbatim.  Statement bodies were compared by label
with the sources at da2889e (runs/split3/stmtdiff.py).  Restated:
- Torus Theorem 7.3 (`thm:general-confluence`) without the a priori bound `M̂⋆`: `A⋆ = Ã⋆` for all
  `k ≥ 1`, finitely many nonzero moments, `∑_{k ≥ 1}`, and for `b⋆² ∉ ℚ` singleton classes and
  vanishing moments for `k ≥ 2`.  `Stmt_thm_general_confluence_rev25`, proved from the form of
  2026-11-24 and `Atilde_eq_zero` (`thm_general_confluence_rev25_of_cited`).
- Torus Corollary 7.6 (`cor:pole-bound`), new: `Ã⋆ = 0` for `k > M̂⋆` and `m⋆ ≤ M̂⋆`.
  `Stmt_cor_pole_bound`, proved the same way (`cor_pole_bound_of_cited`).
- Sphere confluence theorem (`thm:confluence`, now Theorem 12.6 of `paper.tex`) without `M̂⋆`:
  part (i) for every `k ≥ 1` with finitely many nonzero moments, part (ii) with `∑_{k ≥ 1}`.
  `Stmt_thm_confluence_rev25`, proved from the 70bac53 form and `Atildeg_eq_zero`.
- Sphere Lemma 4.6 (`lem:precision-budget`) is no longer a numbered statement of any paper; Remark
  12.7 says the torus Lemmas 7.5, 7.7 and Corollary 7.6 hold for the sphere recursion.  Its Lean
  theorem stays.
New files: Statements/Rev20261125.lean, Proofs/Rev20261125.lean, Sphere/Statements/Rev20261125.lean,
Sphere/Proofs/Rev20261125.lean, imported in Virasoro.lean.  Frozen statement files unchanged.
PAPER_MAP.md regenerated for the three papers (scripts/papermap.py).

Checked by the main session: `lake build Virasoro` exit 0 (../runs/split3/lean-build.log); all 63
theorems of PAPER_MAP.md depend only on [propext, Classical.choice, Quot.sound]
(../runs/lean2/checkMAP.log, 2026-11-25T02:48Z); no sorry/admit/axiom in the new files.
Author-side check, not a reviewer PASS.

## 2026-11-25: statements of Appendix A, Lemmas A.1-A.3 (main session)

On the user's request (tmp terminal, 2026-11-25 ~14:1x Taiwan, "do the lean statements for
A.1-A.3"), after the pass e50db7c/086b33a split the proof of Proposition 9.2(i)-(ii) into
Lemmas A.1 (`lem:mode-count`), A.2 (`lem:odd-primes`) and A.3 (`lem:level-poly`):
`Virasoro/Statements/AppA20261125.lean` freezes `Stmt_lem_mode_count`, `Stmt_lem_odd_primes`,
`Stmt_lem_level_poly`, with demand sheets and the reading conventions in the module docstring
(ℤ[1/2] coefficients; identities in ℚ(t,Y,ζ); algebraic independence over 𝔽_ϖ in the residue
field read through lifts f ∈ ℤ[X₀,X₁] with a coefficient prime to ϖ; "contains ℤ_(ϖ)[b,b⁻¹]";
inverse only with the determinant stated nonzero; R_M as the t-expansion `IsTExpansion` in
ℚ[Y,Y⁻¹][[t]]).  The file compiles (logs/appA_stmt1.log, logs/appA_build1.log); PAPER_MAP.md
lists the three statements with no labelled theorem yet.

Where the existing proof of Proposition 9.2 stands relative to the lemmas: A.3's degree claim is
`degFam_R_of_chain` for `Rfam`, which still has to be tied to `IsTExpansion`; A.1 exists only over
ℚ and for ζ ∈ {−1, 2} (`GsM`, `RsM`, `GsM_ev0`), so the ℤ[1/2] coefficients and ζ indeterminate
are new; A.2 is proved in the Lean by a different local device (ℤ[1/2][s,s⁻¹,α] with reduction
modulo ℓ, Sec6H13Local), so the discrete valuation ring of the paper has to be constructed.
Statement check by an independent reviewer requested before proving (lean.md, "Freeze the
statement first").
Statement check: Jander PASS on all three statements at 1f1c71b against paper.tex at 086b33a
(packet 37, verdict relayed by yang2, yang2-20261125T070452Z-virasoro-appa-statement-forward-result,
2026-11-25T07:04:52Z): A.1 and A.2 and A.3 match the paper knob by knob; the determinant conjunct
guards the inverse in A.2; the coefficient-vanishing encoding forces f = 0 for a negative bound
in A.3; IsTExpansion admits no totalized division.  No labelled theorems yet.

## 2026-11-25: proofs of Lemmas A.1 and A.3 (main session)

On the user's request (tmp terminal, 2026-11-25, "do those." after the proof outlook for A.1-A.3):
- `lem_level_poly : Stmt_lem_level_poly` (Virasoro/Proofs/AppALevelPoly.lean, paper label
  `lem:level-poly`).  R_M is `Rfam`; `IsTExpansion` holds with p = (M!/2^M) Y^M numS and
  q = det G̃_M (`Frat_psi`, `iM_numS`, `isUnit_det_GL`); the degree bound is
  `degFam_R_of_chain sub_h13_degree_chain`, the paper's expansion argument.  No cited hypothesis.
- `lem_mode_count : Stmt_lem_mode_count` (Virasoro/Proofs/AppAModeCount.lean, paper label
  `lem:mode-count`).  G̃ and ρ̃ are the rescaled procedure `gramT`/`torusWordT` over ℚ[t,Y] and
  ℚ[t,Y,ζ] with c̃ = 6+13t+6t², d̃ = −2+tζ; ℤ[1/2] coefficients by induction over the procedure
  (`dAct_mem`, coefficients 1, Y, integers, (k³−k)/12 ∈ ½ℤ); G̃(0,Y) = diag(K_Z Y^ℓ(Z)) by
  `gramT_zero` and `topNat_word_eq_appKZ`, so t ∣ G̃ − D₀ (`X0_dvd_sub_aeval`); ρ̃(0,Y;ζ) is
  ρ̃ with d̃ = −2.  No cited hypothesis.
Checked by the main session: `lake build Virasoro` exit 0 (logs/appA_root_build1.log); both
theorems depend only on [propext, Classical.choice, Quot.sound] (logs/appA_ax2.log); no
sorry/admit/axiom in the two files.  Author-side check, not a reviewer PASS.

## 2026-11-25: proof of Lemma A.2 (main session)

- `AppA2.lem_odd_primes_of_cited (hK : Cited_KacDeterminant) : Stmt_lem_odd_primes`
  (Virasoro/Proofs/AppAOddPrimes.lean, paper label `lem:odd-primes`).  The Kac determinant
  formula is the only hypothesis, as in the paper's proof and in `prop_h13_nonvanishing_of_cited`.
- Construction (the paper's, with the base ring ℤ[√−2] adjoined first): A = ℤ[√−2][b][α]
  (`Zsqrtd (-2)`), reduction A → k[b][α] with k an algebraic closure of 𝔽_ϖ and √−2 ↦ r̄, r̄² = −2;
  𝔓 its kernel, 𝒮_𝔭 = A_𝔓 ⊂ Frac(A) (`Localization.subalgebra`).  Maximal ideal = (ϖ) by the norm
  argument on ℤ[√−2] (`kerRho0_mem`: c̄ a unit gives c = N(c)/c̄ with ϖ ∣ N(c); c̄ ∈ 𝔓 gives ϖ ∣ 2 Re c
  and ϖ ∣ 2√−2 Im c), so `IsDiscreteValuationRing.TFAE` gives a DVR with uniformizer ϖ.
  q₀ = −√−2 (b + b⁻¹)/2, c(b) = 1 − 12q₀² (`cT_eq`).  Algebraic independence through the residue
  map 𝒮_𝔭 → Frac(k[b][α]) and the injectivity of k[t,Y] → k[b][α], t ↦ b², Y ↦ Ȳ (`evb_injective`,
  the argument of `evbar_injective`).  Integrality: G = B(q₀,2q₀−α) D Bᵀ(q₀,α) (`TFock.gram_factor`),
  det B det B' = ±2^{Σℓ} ∏(Δ − h_{u,v})^{p(n−uv)} with each factor a unit (8b²(Δ − h_{u,v}) ∈ A has
  α²-coefficient 4b² mod 𝔓, `isSU_factor`), and n!D⁻¹ integral (`sub_h13_lagrange`), so
  M!G_{M−s}⁻¹ = (M!/n!) δ⁻¹ adj(Bᵀ) diag(n!/D_Z) adj(B') (`entry_mem_aux`).
Checked by the main session: `lake build Virasoro` exit 0 (logs/appA_root_build2.log); all three
Appendix A theorems depend only on [propext, Classical.choice, Quot.sound] (logs/appA_ax4.log);
no sorry/admit/axiom in the three files.  PAPER_MAP.md lists a theorem for Lemmas A.1, A.2, A.3.
Author-side check, not a reviewer PASS.  The Lean proof of Proposition 9.2 still goes through
its own route (Sec6H13Local/Integral, Sec6H13DegRed) and does not consume the three lemmas.

## 2026-11-25: Proposition 9.2 through Lemmas A.1–A.3 (main session)

User request "fix" (21:0x Taiwan), after the report that the Lean proof of Proposition 9.2 did not
consume the three Appendix A lemmas the way the paper's proof (paper.tex l.3104–3161) does.
- New module Virasoro/Proofs/Prop92AppA.lean: `prop_h13_nonvanishing_of_appA (hK) (hH)
  (hA1 : Stmt_lem_mode_count) (hA2 : Stmt_lem_odd_primes) (hA3 : Stmt_lem_level_poly) :
  Stmt_prop_h13_nonvanishing`.  `prop_h13_nonvanishing_of_cited` (Sec6H13Label.lean, paper label
  `prop:h13-nonvanishing`) is now this theorem applied to `lem_mode_count`,
  `AppA2.lem_odd_primes_of_cited hK` and `lem_level_poly`.  Frozen statement and hypotheses
  (hK, hH) unchanged; the old route `prop_h13_nonvanishing_of_chain` stays, no declaration dropped.
- (i), polynomiality: regular at t = 0 because G̃(0,Y) = D₀(Y) from A.1 (`GsM_ev0_of_modeCount`),
  a Laurent polynomial in t from the Kac determinant (`laurent_clearedH`) (l.3113–3118, 3125–3129).
- (i), values: P^(2)(0,Y) = P^(1)(0,Y) from A.1's ζ-independence (`RsM_ev0_of_modeCount`); the
  formula for P(0,Y) from G̃(0) = D₀; ρ̃(0,0)_{(1^M),(1^M)} = 4^M computed directly
  (`eval_rr0_ones`), where the paper cites the proof of Lemma 5.7 (l.3113–3123).
  A.1's matrices are tied to `GsM`/`RsM` by the injectivity of ℚ[t,Y,ζ] → ℚ(t,Y,ζ)
  (`evtYz_Gt2`, `evtYz_rhot3`).
- (i), integrality from A.2: in A.2's field at t₀ = b², Δ = α(α − 2q₀)/2, `specK` gives
  P(t₀,Y) = ∏_u t₀²(2Δ − 2h_{u,1}) ∑_s η_s Tr(M! G_{M−s}⁻¹ ρ_{M−s}) with every factor in 𝒮_𝔭
  (`coeff_local_of_dvr`); A.2's residue-field clause gives 𝒮_𝔭 ∩ ℚ[t,Y] = ℤ_(ϖ)[t,Y]
  (`coeff_local_of_mem`) (l.3129–3142).
- (ii) from A.3: the t-expansion is unique (`IsTExpansion.unique`), so A.3's R_M is `Rfam`; then
  the sum over s and the normalized prefactor (`DegFam.S`, `N_mul`) (l.3144–3160).
- (iii), (iv) unchanged (`sub_h13_valuation`, `sub_h13_lipschitz`).
Checked by the main session: `lake build Virasoro` exit 0 (logs/prop92_build1.log);
`prop_h13_nonvanishing_of_cited` and `prop_h13_nonvanishing_of_appA` depend only on
[propext, Classical.choice, Quot.sound] (logs/prop92_ax5.log), and the printed body of
`prop_h13_nonvanishing_of_cited` is the application to the three lemmas; no sorry/admit/axiom in
the new file; PAPER_MAP.md unchanged (66 theorems).  Author-side check, not a reviewer PASS;
route review requested from Jander in packet 38.  Remaining departure from the paper: the Lean
proof of Lemma A.3 takes G̃ = D₀ + tG₁ from internal lemmas (`cc_GL`, `Em_dvd`), not from
`lem_mode_count`.

Verdict on packet 38 (Jander, 2026-11-25T13:24:44Z, relayed by yang2 13:25:24Z), static review at
5ec3882 against paper.tex at 086b33a: ITEM 1 (Proposition 9.2 through Lemmas A.1–A.3) PASS;
order changes (monic division before P, degree function early, integrality before values)
"preserve the paper's dependencies"; the 4^M entry uses the computation from the proof of
Lemma 5.7.  ITEM 2 (proofs of A.1, A.2, A.3) PASS for the mathematical route, with one
citation-edge departure: in A.3, `isUnit_det_GL` and `Em_dvd` reach the diagonal through
`cc_GL`/`GsM_ev0`, not through `lem_mode_count` ("expose the t=0 bridge below the A.3 module and
thread its A.1 projection to these two helpers").  No Lean execution, build or axiom audit on
the reviewer's side.

## 2026-11-25: Lemma A.3 through Lemma A.1 (main session)

Follow-up to the previous entry, removing the departure it listed.  The paper's proof of Lemma A.3
(l.3010–3016) works in the notation of Lemma A.1 (G̃ = D₀ + tG₁) for the expansion
R_M = (M!/2^M)Y^M ∑_r (−t)^r Tr(D₀⁻¹(G₁D₀⁻¹)^r ρ̃).  `lem_level_poly` (AppALevelPoly.lean) now
takes G̃(0,Y) = D₀(Y) from `lem_mode_count` (`GsM_ev0_of_modeCount`) for the two places it is
used: det G̃ a unit of ℚ[Y,Y⁻¹][[t]] (`isUnit_det_GL_of`, in `isTExpansion_Rfam`) and t ∣ tG₁D₀⁻¹
for the expansion (`Em_dvd_of`, `pow_Em_dvd_of`, `neumann_of`, `cf_Rfam_eq_of`), in place of
`cc_GL`/`Em_dvd`/`cf_Rfam_eq` (which stay in Sec6H13DegRed.lean).  The A.1 bridge lemmas moved
verbatim from Prop92AppA.lean to the new module AppABridge.lean, imported by AppALevelPoly.lean.
Statements unchanged.  Checked by the main session: `lake build Virasoro` exit 0
(logs/prop92_build2.log, no warnings in the three files); `lem_level_poly`,
`prop_h13_nonvanishing_of_cited`, `lem_mode_count`, `AppA2.lem_odd_primes_of_cited` depend only
on [propext, Classical.choice, Quot.sound] (logs/prop92_ax6.log); no sorry/admit/axiom.  This is
the change Jander's packet-38 ITEM 2 named; author-side check, confirmation requested in packet 39.

Verdict on packet 39 (Jander, relayed by yang2 2026-11-25T13:44:17Z), static review at 61b187b
against paper.tex l.3010–3016 at 086b33a: ITEM 1 PASS.  `AppABridge.lean` takes the frozen A.1
statement and identifies the constant Gram matrix through the rational-function bridge;
`AppALevelPoly.lean` passes `GsM_ev0_of_modeCount lem_mode_count` to the determinant-unit step
and through `Em_dvd_of`/`pow_Em_dvd_of`/`neumann_of`/`cf_Rfam_eq_of`; the bridge declarations
moved unchanged and the Proposition 9.2 label theorem is unchanged; "the previous citation-edge
departure is closed".  With packet 38 ITEM 1 (Proposition 9.2) and ITEM 2 (routes of A.1, A.2),
the Lean proofs of Lemmas A.1–A.3 and of Proposition 9.2 through them have reviewer PASS on
route fidelity (Jander); the kernel side (build, axioms) is the main session's check.

## 2026-11-26: traces paper, BGG weight as a Gamma quotient (main session)

Readability pass 6 of `irreducible/paper.tex` (a13dc17, 4c60a91; reviewer PASS at 98f1430)
defines `Ψ⋆_{2k+1,2m+1}(μ)` (display `eq:psi-star`) and the BGG weight
`Ω(μ → ξ) = Ψ⋆(ξ)/Ψ⋆(μ)`, and restates Proposition 6.1(ii) as the arrow identity with
`Ω ∈ ℚ^×` for all orbit pairs.  New `Statements/Rev20261126.lean`: `psiStar`, `OmegaPsi`,
`Stmt_prop_bgg_cocycle_rev26` (part (i) copied from `Stmt_prop_bgg_cocycle`),
`Stmt_thm_gen_rocha_caridi_rev26` and `Stmt_lem_degenerate_quotient_t_rev26` (the earlier
statements with `Omega` from λ and `cArrow` replaced by `OmegaPsi`).  New
`Proofs/Rev20261126.lean`: from `cArrow_psi`, `pathProd_psi`, `psiNode_ne_zero` (the existing
route of the paper's proof of 6.1(ii)) and from the earlier forms of Theorem 4.3 and Lemma 7.1.
`scripts/papermap.py` prefers `_rev26`; PAPER_MAP regenerated (66 theorems).  Checked by the main
session: `lake build Virasoro` exit 0 (runs/prose6/lean_root.log; no warnings in the two new
files), the three label theorems depend only on [propext, Classical.choice, Quot.sound]
(runs/prose6/lean_rev26_axioms.log), no sorry/admit/axiom.  Author-side check; statement and
route review requested from Jander (packet 42).

Verdict on packet 42 (Jander, agent-messages 2026-11-26T01:54:04Z), static review at 54535b1:
ITEM 1 PASS (statement fidelity: the substitution ϖ = n b/(2p') gives the four Gamma factors of
`eq:psi-star`; `(false, 0)` adds no distinct weight; Theorem 4.3 changes only the five `Omega`
occurrences and Lemma 7.1 only the two `cArrow` occurrences), ITEM 2 PASS (proof route: division
of the old identities by the nonzero source value, witnesses through the `+` nodes, quotient of
two λ-path weights for arbitrary pairs; the `_of_cited` exports keep the eight cited inputs as
hypotheses).  Build and axioms are the main session's check.

## 2026-11-26: colliding-poles paper Section 7.2, recursion at the fixed charge (main session)

New `FixedCharge.lean` (chains and chain functions, Definition 7.9, by recursion on the level;
full moments; `phiRem`), `Statements/Sec7FixedCharge.lean` (`Stmt_lem_full_moments`,
`Stmt_lem_cutting`, `Stmt_lem_regular_remainder`, `Stmt_lem_chain_expansion`,
`Stmt_lem_chain_regular`, `Stmt_thm_fixed_charge`, `Stmt_cor_fixed_charge_generic`) and proofs
`Proofs/Sec7{Cut,Moments,Binom,Remainder,RemainderReg2,Expansion,FixedCharge,Generic}.lean`.
Lemma 7.10 takes no cited input; the other six take `Cited_KacDeterminant` and
`Cited_HJSNormalizations` (through Proposition 6.4 and Theorem 4.2).  Checked by the main
session: `lake build Virasoro` 4180 jobs, no errors; axiom audit of the 73 mapped theorems
(runs/lean2/checkMAP.log) all [propext, Classical.choice, Quot.sound]; no sorry/admit/axiom.

Packet 46 (at 6186ddf): yang2 Item 1 FIX on three statements (Lemma 7.11 must state the
two-variable regularity at `(b⋆, μ)` literally with the restriction (7.6); Lemma 7.12 must state
`t`-adic convergence per end point; Theorem 7.14 must state eventual vanishing of
`c^{(k)}_{λ→μ,j}(b⋆)` per end point); definitions and Lemmas 7.8, 7.10, 7.13, Corollary 7.15 PASS.
Jander Item 2 PASS (source audit of the seven labelled proofs).  Fixed at a6f7403: Lemma 7.11 as
`Reg = P/E` over `K[[t]]` with `E(0, μ) ≠ 0` (paper's common denominator, `reg_two`); Lemma 7.12
with per-end-point tail valuations (finite-chain estimate `chainFn_ord`); Theorem 7.14 with the
per-end-point vanishing clause.

Packet 47 (at a6f7403): yang2 Item 1 PASS (statement re-check of 7.11, 7.12, 7.14,
2026-11-26T11:55:24Z; prose note on the reading conventions applied at 0e37fcc); Jander Item 2
PASS (source audit of the three changed proofs, 2026-11-26T12:03:58Z).  Build and axioms are the
main session's check.

## 2026-11-27: colliding-poles paper Corollary 7.16 and Section 8.1, coefficients on the diagonal (main session)

New `Statements/Sec7ChainValues.lean` (`Stmt_cor_chain_values`) and `Statements/Sec8Diagonal.lean`
(nodes, signed momenta, positions, node labels, first steps, node chains, chain products and
weights; `Stmt_lem_node_labels`, `Stmt_lem_node_poles`, `Stmt_lem_node_leading`,
`Stmt_prop_top_ratios`, `Stmt_lem_diagonal_values`, `Stmt_thm_diagonal`,
`Stmt_cor_diagonal_lambda`), proofs `Proofs/Sec7ChainValues.lean` and
`Proofs/Sec8Diag{Jets,Nodes,Labels,Labels3,BridgeAux,Bridge,Poles,Lead,Chains,LeadSums,Leading,
Top,Values,Ell,Moments,Rec,Kappa,Thm,Lambda,Cor}.lean`.  Lemmas 8.3 and 8.4 take no cited input;
Corollary 7.16 and 8.5–8.8 take `Cited_KacDeterminant` and `Cited_HJSNormalizations`; Corollary 8.9
adds `Cited_VermaHomInjective` and `Cited_SingularUnique`.  Checked by the main session: each
module builds; axiom audits `runs/ribault/ax_83.log`, `ax_c716.log`, `ax_85.log`–`ax_89.log` give
[propext, Classical.choice, Quot.sound]; no sorry.  Packet 56 (at 991fa96, 2026-11-27T01:34:53Z):
yang2 Item 1 PASS (statement fidelity, 2026-11-27T01:36:21Z), Jander Item 2 PASS (source audit,
proof routing and declared inputs), both with one scope note: the paper's Theorem 8.8 also displays
the equivalent terminating `₂F₁(-n, -n-l; 1-D-l; x)` form, which `Stmt_thm_diagonal` did not state.
Fixed: `Stmt_thm_diagonal` gets the second clause `∑_i f_{2i}(l,D) xⁱ = hyp2F1Poly (-n) (-n-l)
(1-D-l) n` (`hyp2F1Poly`, the terminating series with explicit Pochhammer products, in
`Statements/Sec8Diagonal.lean`), proved by `diag_hyp` (`prod_neg_shift`) in
`Proofs/Sec8DiagThm.lean`; axioms unchanged (`runs/ribault/ax_88b.log`, `ax_89b.log`).  Recheck of
the new clause: packet 57 (at 583e921): yang2 Item 1 PASS (2026-11-27T01:53:51Z) with one FIX,
the PAPER_MAP row of Theorem 8.8 pointed to `prod_neg_shift` because the new lemmas had been
inserted between the `Paper label` docstring and `thm_diagonal_of_cited`; fixed by moving the
docstring back (row restored to `Virasoro.thm_diagonal_of_cited`, 7805fc1).  Jander Item 2 PASS
(2026-11-27T02:01:12Z, source audit of `diag_hyp`, `prod_neg_shift`) with the same PAPER_MAP FIX,
applied at 7805fc1.

## 2026-11-27: colliding-poles paper Section 8.2, boundary weights (main session)

New `Statements/Sec8Boundary.lean` (the setting, `ε`, `π_k`, `T_k`, `M_k`, `μ_k`, the levels, the
label from `μ_i` to `μ_k`, the chain values, `Top`, `R_g`, `ρ_g`, `h_{aθ}`;
`Stmt_lem_boundary_labels`, `Stmt_thm_boundary`), proofs
`Proofs/Sec8B{Nodes,Labels,Labels2,Labels3,Bridge,Lead,Top,Vals,Ell,Moments,Rec,Spec,Pole}.lean`.
Lemma 8.10 takes no cited input; Theorem 8.11 takes `Cited_KacDeterminant` and
`Cited_HJSNormalizations` (through Theorem 7.14, Lemma 7.13, Corollary 7.16 and Proposition 9.2).
Checked by the main session: each module builds; full build exit 0
(`runs/ribault/lean_full_811.log`, 4218 jobs); axiom audits `runs/ribault/ax_810.log`,
`ax_811.log` give [propext, Classical.choice, Quot.sound]; no sorry; PAPER_MAP 83 rows.
Author-side check, not a reviewer PASS.
