# Referee report: presentation, organization, wording

Manuscript: *Exact algebraic confluence for torus one-point Virasoro blocks and
irreducible minimal-model traces* (40 pp., dated November 23, 2026; repository
commit 36a9532). Scope of this report: presentation, organization and wording
only. Mathematical correctness was not re-checked.

## Summary

The paper studies the coefficients H_N of the eta-reduced torus one-point
Virasoro block at central charges with rational b², where the generic
Poghossian/HJS recursion breaks down. It proves:

1. a finite formula for every coefficient at every fixed b⋆ ≠ 0 (Theorems 4.2,
   4.3 and Section 7);
2. at interior minimal-model weights, the bound "pole order ≤ Jantzen depth",
   the coefficient at that order (Theorems 5.8, 5.9), and sharpness over Q(d)
   (Corollary 5.10, Section 6);
3. the first Ising double poles (Section 8);
4. a descent criterion, Verma regularity, the generic first-layer vertex ratio
   and a generalized Rocha–Caridi identity for irreducible traces (Sections
   9–14).

## Assessment

The citations are precise and most proofs are short. The presentation is the
main obstacle for a reader:

- the manuscript reads as two papers with two setup sections;
- several theorem statements use objects defined sections later;
- a large number of symbols carry two or three meanings, often inside a single
  proof;
- the longest proofs (Propositions 6.7–6.9, pp. 11–18) are written as running
  inline formulas with almost no displays (p. 17 has none).

Recommendation: major revision of the presentation.

## Major comments

### 1. Two papers in one manuscript

Sections 2–8 (confluence, Jantzen pole order, sharpness, Ising) and Sections
9–14 (irreducible traces) each have their own setup. Section 10 introduces
again:

- c(b), h_{r,s} and the minimal-model weight formula: (10.1)–(10.2) repeat
  Definition 3.1 and Proposition 3.2;
- the layer levels ℓ^±_k: (10.9)–(10.10) repeat Theorem 5.8;
- the three-point form: Lemma 10.1 gives the rigorous definition of what
  Definition 2.2 wrote as a matrix element, and the paragraph after Lemma 10.1
  reconciles the two;
- the variable t, which changes from b − b⋆ (Section 7) to b² (Sections 9–14).

The introduction gives Part B one paragraph (the one starting "For fixed d and
an interior minimal-model weight"). There are two options. The first is to
split off Sections 9–14 as a separate paper. The second is to keep one
manuscript with Part I and Part II headings, one shared setup section and an
introduction that presents both parts with equal care. With either option,
each object should be defined once.

### 2. Statements that come before their definitions

- Theorem 4.3 (Section 4) uses Definitions 7.1–7.3, Lemma 7.4 and Proposition
  6.4, so it cannot be read where it stands.
- The proof of Corollary 5.10 rests on Lemma 6.5 and Propositions 6.7, 6.8 and
  6.9.
- Theorems 9.1–9.3 use:
  - the orbit 𝒪_{p,p'}(r,s), ρ_{Δ,d} and B_Δ from Section 10;
  - σ^±_j and γ^±_j from Proposition 11.2;
  - Ω from Proposition 12.1.
- Proposition 8.1 says 𝒫_{R,S} is "defined in the proof of Proposition 6.9".
  It is Definition 6.1 at b = b⋆ (monic of degree 2RS in d); cite the
  definition.
- The proof of Lemma 11.1(iii) says "Section 12 proves the factorization
  𝒫_{R,S} = C_{R,S}² P_{R,S}(h_{R,S}) P_{R,S}(h_{R,−S})". Section 12 never
  states this identity. It can be read off f_d(0,0) in the proof of Theorem
  9.2. The same proof then notes that the roots also follow from Proposition
  6.2, so the forward reference can be dropped. Otherwise state the
  factorization as a lemma.

A possible order:

1. setup: §2 together with Lemma 10.1 and the contravariant form;
2. generic residue data and the generic recursion: Definition 6.1 to Lemma 6.6;
3. collision classes, partial fractions and confluence: §3, §4, §7;
4. Jantzen layers and the top pole: §5 without Corollary 5.10;
5. sharpness: Propositions 6.7–6.9 and Corollary 5.10;
6. Ising;
7. Part II, with §10 before the statements of §9.

### 3. Notation

The clashes below each occur within one section, and often within one proof.

| Symbol | Meanings | Where they collide |
|---|---|---|
| n₁ | p'r + ps (§10.2, before (10.9)); p'R₁ + pS₁ (Lemma 10.3(iv)) | Both appear in the proof of 10.3(iv). Step 3 of Lemma 13.1 cites α = (m₂n₂ − m₁n₁)/(4p'²) "in the notation of Lemma 10.3" |
| m^±_k | Coulomb momentum (Prop. 6.7); multiplicity function m^±_k(x) of the root d_x in τ^±_k (proof of Prop. 6.9) | The proof of Prop. 6.9 later uses R^±p' + S^±p = m^±_k as a momentum |
| τ | torus norm τ^±_k(d); blow-up parameter; deformation b² = b⋆² + τ (§13); τ_mod (§14) | The proof of Prop. 6.7 uses τ as blow-up parameter while its statement contains τ^±_k |
| w | singular vectors w^±_k; blow-up variable (Prop. 6.7); family w(x); w_m = \|μ_m\| (Prop. 6.8) | Prop. 6.7 |
| t | b − b⋆ (§7); b² (Prop. 6.8, §§9–14) | The remark at the start of §10 acknowledges this. Renaming is better |
| p' | minimal-model integer; summation index p' ∈ {1−R, …, R−1} in (10.7) and in the proof of Thm 9.2 | §§10–12, where b⋆² = −p'/p is in force |
| (p, q) | dummy indices in Def. 6.1 and Lemma 6.5 | Prop. 6.7 uses the same boxes with the real p, p' |
| λ, μ | weights; partitions λ, μ ⊢ M (proof of Prop. 6.8); momenta λᵢ (Prop. 10.2) | Prop. 6.8(iii) uses μ as a weight |
| 𝒪 | orbit 𝒪_{p,p'}(r,s); ring 𝒪 = R[q₀] (Prop. 6.8); PBW operator 𝒪_{R,S} (proof of Thm 9.2) | |
| 𝓕 | block 𝓕^{(c)}_Δ; 𝓕^Verma; Fock module 𝓕(α); fusion sets 𝓕_{p,p'}, 𝓕^± | |
| u, m | (u, v) = (2k+1, 2m+1); Step 4 of Lemma 13.1 writes diag(τ^{e₁}u₁, …, τ^{e_m}u_m) | Lemma 13.1 |
| ℓ | level ℓ_a; prime ℓ; partition length ℓ(Y); level of a vector ℓ(w) (proof of Thm 5.9) | |
| j | depth j_N(λ); embedding j_{w^±_k} (proof of Thm 5.9) | |
| B | Shapovalov form B_Δ; Jantzen forms (spelled B^i in §5 and B^{(i)} in §11); germs B_{a,N}(t); boxes B, B₀, B₁, B_g; Fock matrix B_M(q₀, α) | |
| 𝒫 vs P | 𝒫_{r,s}(b,d), the torus norm (Def. 6.1); P_{R,S}(b;Δ₁,Δ₂), the fusion polynomial (Prop. 10.2) | They differ only in font and appear together in Lemma 11.1 |
| k | layer index (§5); fusion index in d = h_{2k+1,2m+1} (§§9–13, where the layer is renamed k₀); odd index in Def. 6.1 | |

Several objects also have more than one name:

- ρ is called "torus matrix", "torus form", "Verma three-point form" and
  "vertex form";
- the generic recursion is called "Poghossian's generic recursion", "generic
  eta-reduced recursion" and "Poghossian–HJS recursion";
- the block appears as 𝓕^{(c)}_Δ(d|q), 𝓕^Verma_{c,Δ,d}(q) and H^{(c)}_Δ;
- the radical appears as J(c,λ) and as J¹(c,λ);
- module classes are named in Iohara–Koga's scheme (Class R⁺, Case 1+) in §5
  and in Feigin–Fuchs/Astashkevich's (Class III₋) in §10;
- the diagram is called "Feigin–Fuchs embedding diagram", "braided diagram",
  "braided BGG diagram" and "braided poset".

Recommendation: rename where the table shows a clash, pick one name per
object, and add a notation table after §2.

### 4. The proofs of Propositions 6.7–6.9 (pp. 11–18)

- **Proposition 6.7.** Split the proof into three lemmas, each with displayed
  formulas:
  1. the blow-up limit along (ν⋆+τ, λ+τw, τy);
  2. the description of the colliding chains;
  3. the moment evaluation.

  Sentences such as "consecutive slopes differ, as shown below" and "the
  colliding chains from λ are the sequences n₀ = x₀, x₁, …, |xᵢ| increasing,
  alternately in n₁ + N₀Z and n₀ + N₀Z" need several displayed lines each.
- **Proposition 6.8.** State in the main text only what later proofs use: the
  valuation formula (6.3) and the two-level estimate (6.4). Move the
  integrality and level-polynomiality proofs (about 3 pp.) to an appendix.
  Add one sentence explaining why polynomiality in M is needed (it feeds the
  ℓ-adic comparison of two levels). The unnumbered "For the comparison of two
  levels" paragraph inside part (iii) should be part (iv).
- **Proposition 6.9.**
  - Give a table of the multiplicities e_± in each case.
  - Display the pairing of factors in Case 2 and the ratio T_k in Case 3.
  - In Case 1, e₊ = 2j − 1 − 𝟙_{s=1} + 𝟙_{s≤p'−2} + 𝟙_{s=1} has two
    cancelling terms. Write 2j − 1 + 𝟙_{s≤p'−2}.
- **Theorem 5.9.** The proof opens with eight level differences in one
  sentence ("for the upper and lower signs respectively"). A small table would
  be clearer.

### 5. Abstract and introduction

- **"Confluence" is undefined.** The word appears in the title, in Theorems
  4.3 and 9.3 and in §15, and the paper never defines it. Say in the
  introduction what it means here: the limit of the generic recursion as its
  poles collide at b → b⋆.
- **First paragraph.** The introduction opens with a list of the literature.
  A first paragraph should say what H_N is, why rational b² is the case of
  interest (minimal models), and what fails in the generic recursion there
  (coinciding Kac weights and poles of the residues).
- **Positioning against Ribault.** The introduction cites Ribault's open
  problem [Rib26, §4.3.3] just before stating the results, while §15 says the
  paper gives no recursion intrinsic to the specialized module. State in the
  introduction which part of that problem the paper settles and which part
  stays open.
- **Script path.** The literature paragraph contains the path
  `tools/audit_stocco_comparison.py`. Move it to the code availability
  section.
- **Proof detail.** The paragraph on d = h_{1,±3} (coefficients in Z[½],
  Taylor coefficients polynomial in the level) is proof detail. One sentence
  saying that sharpness is proved by ℓ-adic comparison at two special values
  of d is enough there.
- **Roadmap.** With 15 sections, the paper needs a paragraph on its
  organization.
- **Abstract wording.** The abstract uses many terms without definition:
  "eta-reduced", "Kac collisions", "generic residues", "Jantzen depth", "top
  layer", "strict two-vector levels", "labels (u,1)", "braided diagram",
  "first-layer Jantzen vertex ratios", "Gamma-potential ratios" and "reflected
  set".
- **Abstract content.** The abstract also carries proof technique (ℓ-adic
  comparisons, swapping b with b⁻¹, labels (u,1)). One or two plain sentences
  per result would read better.
- **Ising weights.** "Energy, spin and identity weights" occur only in the
  abstract. Name them in §8 as well.

### 6. Theorem statements that carry other material

- **Theorem 4.3** introduces Ã only to state Ã = A. It also contains
  algorithmic remarks (the sums are finite, the recursion terminates, Lemma 7.4
  supplies truncation orders). It further says the series "agrees
  coefficientwise in q with the inverse-Shapovalov meromorphic Verma-module
  block", which is H_N by Definition 2.3. Suggested statement: A⋆ equals the
  collision moment (7.1), m⋆ ≤ M̂⋆, and the special case b⋆² ∉ Q. The rest
  can go in a remark.
- **Theorem 5.8** contains six definitions: n₀, n₁, ℓ^±_k, w^±_k, W^±_k and
  j_N. Put them in a definition before the theorem, and cite it in §10 in
  place of (10.9)–(10.10).
- **Theorem 9.1** adds two conclusions after items (i) and (ii): regularity on
  the whole orbit, and joint regularity in (b, Δ). Number them (iii) and (iv).
- **Definition 7.3** contains a claim with its proof (vanishing for
  k > M̂⋆). Make this a remark.
- **Remark 2.5** mixes notation with a result (rationality of F_N and H_N).
  Move the result into Lemma 2.4.
- **Lemma 10.3.**
  - Item (iii) defines γ_{R,S} and proves that it does not vanish. That is a
    separate topic from the item's arithmetic.
  - Item (iv) ends with max(ℓ⁺₁, ℓ⁻₁) < min(ℓ⁺₂, ℓ⁻₂). The proof of Theorem
    5.9 already shows this for all k.
- **The "Ward-induction fact".** It opens the proof of Proposition 11.2, and
  the proofs of Theorem 9.1 and Lemma 13.1 cite it. State it as a lemma.

### 7. A figure

Sections 5 and 10–13 rely on the braided embedding diagram: layers, ±
branches, diamonds, and the alternating chain μ₀, μ⁻₁, μ⁺₂, … used in the
proof of Theorem 9.3. A figure with the levels ℓ^±_k would help readers
considerably. `tikz` is already loaded, but no figure uses it.

## Specific comments by section

### §2

- Definition 2.2 uses ⟨Δ| and the contravariant form before they are defined.
  The anti-involution ω(L_n) = L₋ₙ first appears in Lemma 5.6. Define the form
  in Definition 2.1.
- Move Lemma 10.1 here and define ρ_N through it.
- Definition 2.3: η₃ = η₄ = 0 is never used.
- Remark 2.5 hides an important convention: d is an indeterminate and pole
  orders are taken over Q(c,d). Put it in a conventions paragraph. Also name Δ
  the internal weight and d the external weight here; the titles of Lemmas 4.1
  and 6.5 already use these words.

### §3

- The section has one definition and one proposition. Merge it with §4.

### §4

- Lemma 4.1: a_Y = ℓ(Y) adds a symbol; use ℓ(Y).
- Theorem 4.2: "(or 0)" should read "(or 0 if all vanish)".
- Theorems 4.2 and 4.3 give coefficients in Q(b⋆²)[d], §7 works over
  K⋆ = Q(b⋆, d), and Corollary 5.10 over Q(b⋆, d). Align these.

### §5

- The paragraph before Theorem 5.8 relates Definition 5.2 to [IK, (5.49)] and
  to Astashkevich. Make it a remark after Definition 5.2.
- Proof of Theorem 5.8: "their levels above λ are ℓ^∓_k" swaps the sign
  relative to ξ_{±k}. Say so explicitly.
- Proposition 11.2 redefines the Jantzen filtration through x-adic lattices in
  C[[x]], while Definition 5.2 uses polynomial families. State once that the
  two agree; the truncation argument is already in the proof of Lemma 5.3.

### §6

- The title "Generic residue data" covers only the first half of the section.
- The proof of Proposition 6.2 ends with "Their (9) is the eta-reduced
  recursion.", which connects to nothing.
- Lemma 6.5: "The external weight d = 0" could read "Vanishing at d = 0 and
  the first d-derivative".
- Proposition 6.8(iii): put "using the symmetry p ↔ p' when p' has no odd
  prime factor" into the hypotheses.

### §7

- Lemma 7.4: "Suppose S_{a,M} is required through t^U" reads better as "is
  needed modulo t^{U+1}".
- Proof of Theorem 4.3: "The Kac exponents p(m − rs) are nondecreasing"
  should read "nondecreasing in m".
- The sphere companion proves the same structural theorem by a shorter
  argument (sphere Theorem 4.7): uniqueness of partial fractions forces the
  negative t-coefficients of the grouped numerators to vanish. Use one
  argument in both papers.

### §8

- b₀ here, b⋆ elsewhere.
- The two tables list the weights in different orders: (0, 1/2, 1/16) and
  (1/2, 1/16, 0).
- The "colliding labels" column should say for which N it holds.
- The paragraph after Proposition 8.1:
  - it writes γ₇ and γ₁₀, indexed by level, while γ^±_k is indexed by layer;
  - "They do not reconstruct level 11" belongs in the code availability
    section.

### §9

- `\sloppy` … `\fussy` around §§9–14 loosens spacing over 19 pages. Fix the
  problem lines individually.
- The Ising discrepancy paragraph:
  - should say which value is which (F₂ = 8/7 and T^irr₂ = −1);
  - should say what is computed along the ray (Δ, d) = (λ + x, d⋆ + αx), and
    where.
- "the same endpoint weight Ω" (after Theorem 9.2): Ω is not a weight in the
  paper's sense. §14 calls the same numbers "signed cocycle coefficients" and
  "first-layer BGG weights". Use one term.
- The Felder and Felder–Silvotti sentence belongs in the introduction.
- Terms that are never defined:
  - "truncated recursion" (Corollary 9.4, §14);
  - "single-index" and "two-index";
  - "off-orbit" (§14.3);
  - "half-fusion weights" (§14.4);
  - "first Jantzen window" (proof of Theorem 9.1).
- Theorem 9.2:
  - "positive integers R, S ≥ 1" is redundant;
  - the parenthesis "(with constant PBW coefficients lifted to
    M(c(b), h_{R,S}(b) + x))" carries the convention that Δ-derivatives are
    taken at fixed PBW coefficients, which deserves its own sentence;
  - c_{R,S} reuses the letter c.
- The sentence after Corollary 9.4 is the only roadmap for the proofs of Part
  II. Move it to the start of §9 and expand it.
- "Exact" appears 20 times: "exact finite formula", "exact Verma regularity",
  "Exact intersection", "exact V_d(1) Ward identity", "Exact depth-one",
  "exact algebraic calculation", "exact confluence". Keep it only where it
  distinguishes one statement from another.

### §§10–13

- §10: the proof of Lemma 10.3(i) uses Class III₋, while §5 uses Class R⁺,
  Case 1+ (see the notation comment above).
- Lemma 11.1: the title does not need "Exact".
- §12 opens directly with a proof. Add a sentence saying what the section
  does.
- Lemma 13.1, Step 3: the comment on [Ast97, Theorem C(e)] is a remark. Move
  it out of the proof.

### §14

- §14.1 says the BGG sum "agrees with the Euler pentagonal series φ(q), hence
  has integer coefficients". The logic runs the other way: it agrees with φ,
  which has integer coefficients.
- §14.1 also gives the identity q^{1/16 − 1/48} φ(q) = η(τ_mod), a striking
  identity for the irreducible trace with the energy insertion in the spin
  module. Say whether it is checked through level 30 only or is known (with a
  reference).

### §15

- The section titled "Scope and outlook" contains no outlook.
- The last sentence would read better as a plain statement that a recursion
  intrinsic to the specialized module (Ribault's question) remains open.

## Minor and typographical

- The redefined `\eqref` prints equation numbers in old-style figures, while
  theorem numbers use lining figures. The two look inconsistent in the text.
- `\thickmuskip=8mu` widens relation spacing noticeably in long inline
  formulas.
- The `lineno` line is commented out. A referee copy should have line numbers.
