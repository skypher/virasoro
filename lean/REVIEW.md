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
