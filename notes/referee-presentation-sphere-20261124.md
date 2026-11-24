# Referee report: presentation, organization, wording

Manuscript: *Exact algebraic confluence and Jantzen pole orders for sphere
four-point Virasoro blocks* (25 pp., dated November 23, 2026; repository commit
36a9532). Scope of this report: presentation, organization and wording only.
Mathematical correctness was not re-checked.

## Summary

The paper does four things:

1. It proves Zamolodchikov's large-internal-weight limit H_N → δ_{N,0} for the
   sphere four-point block, for all complex c and external weights (§3).
2. It gives the fixed-b⋆ confluence formula for H_N and for the cross-ratio
   coefficients 𝓑_N (§4).
3. At interior minimal-model weights it proves the Jantzen pole-order bound,
   the coefficient at that order, and sharpness over Q(Δ₁, …, Δ₄). For 𝓑_N
   the sharpness proof uses a BPZ specialization; for H_N it uses Hermite
   values (§5).
4. It works out the c = 0 and Ising examples (§6).

## Assessment

This manuscript is shorter and better organized than its torus companion:

- the introduction defines the block in its first paragraph;
- the long proofs of §3 are divided into steps.

The remaining presentation problems are:

- the title and abstract do not reflect where the paper's weight lies;
- §3 names several constructions without explaining them;
- symbols are reused between §3 and §§4–5;
- §5 depends on the companion through twenty citations by theorem number.

Recommendation: minor-to-major revision of the presentation.

## Major comments

### 1. Title and abstract

The proof of the large-Δ limit (§3) takes pp. 4–16, half the paper. The
introduction presents it as filling a gap noted in [Rib26, §4.3.4]. The title
does not mention it; a title naming it would match the content.

The abstract calls the proof "self-contained algebraic". Neither word fits:

- the proof uses analysis: Cauchy estimates, Liouville's theorem on P¹,
  Fredholm determinants, and a real limit λ → +∞ followed by a
  Zariski-density argument;
- it imports the Feigin–Fuchs oscillator operators from [BDK20].

Drop "algebraic", and drop "self-contained" unless it is qualified.

Other wording in the abstract:

- "half-pillow Wiener–Hopf saddle point" (see comment 2);
- "both pole orders": say of H_N and 𝓑_N;
- "using the torus Jantzen norms": the norms belong to the Verma module and
  were computed in the torus paper. As written, a reader expects a torus
  quantity in a sphere formula.

### 2. Terms in §3 that are named but never explained

- **"Half-pillow"** appears in the abstract, in the title of subsection 3.2
  and in the title of Lemma 3.4. The text never explains it. Either explain it
  (presumably the map p(w) = 4w/(1+w)² and the pillow geometry) or drop it.
- **"Wiener–Hopf"** (Lemma 3.4 and its identity (3.7)) and **"Bergman
  kernel"** (Lemma 3.5) are also left unexplained. W(x₁, x₂) appears to be
  the Bergman bidifferential of the elliptic curve Y² = x(x − 1)(x − z).
  Identity (3.7) appears to be a Wiener–Hopf splitting of Ξ. One sentence each
  would tell the reader what is being computed and why the answer is a theta
  function.
- **"Virasoro diffeomorphism"** (Step 2 of Lemma 3.7): say that U(W)
  implements the conformal map f(x; W) = x exp(−Σ W_m x^{−m}).
- **"Algebraic Gaussian expectation"** and **"graded z-filtration"** (proof of
  Lemma 3.3(iii)) need a definition, for instance the formal Wick rule.
- **Ψ₁**, defined as "half the covariance contraction of the gradient of
  S^{(1)}_c", needs a formula.

### 3. Structure of §3

**Lemma 3.3** is the central statement of the section. Its part (iii) is the
limit formula (3.4) with a two-page proof. Its part (ii) defines the operator
L^{(0)}_k inside a bullet point. Suggested split:

1. a lemma on the regularity of the λ⁻¹ expansion;
2. a lemma on the structure of S^{(0)}, S^{(1)} and S^{(2)};
3. a proposition for the Gaussian and saddle-point evaluation.

**Lemma 3.2(ii)** defines the pairing in words ("pair the coefficients of
matching monomials … using the tilde coefficients as written"). Write the
bilinear pairing as a formula.

**The notation ⟨f̄, g⟩** for the Hermitian product in (3.1) suggests a
bilinear pairing of f̄ with g. Write ⟨f, g⟩ for the sesquilinear product, or
define the bilinear pairing explicitly.

### 4. Notation

| Symbol | Meanings | Where they collide |
|---|---|---|
| λ, μ | in §3, c = 1 + 24μ² and Δ = λ² + μ²; in §§4–5, λ is a Kac weight and μ = μ^small_k a weight | The proof of Theorem 5.5 sets Δ₁ = μ |
| q | the nome q(z); the generating-function variable in A(p), B(p,q), C_±(p) | The text has to add "(only q(z) denotes the nome)" |
| Φ | prefactor Φ; Φ̃; series Φ_c^raw, Φ₁, Φ₂; primary field Φ_{Δ_b}(1) | |
| γ | three-point polynomial γ_Y (Def. 2.1); Jantzen norms γ^±_k | Both appear in the proof of Theorem 5.5 |
| π | π^±_k (three-point polynomials); π_g (pole-order bound, Def. 4.5) | |
| Λ | external momenta Λ_j; the set Λ_N(b⋆) of Kac weights | Both in §4 |
| P | numerator P_N (Thm 3.1); fusion polynomial P_{r,s}; P_n(X) (Lemma 3.5); P(x) = x(x−1)(x−z); primaries P_a, P_w; Ribault's momenta P_j | Prop. 6.1 uses P_j in a display next to P_{1,1} and P_{1,4} |
| c | central charge; c_n(λ²); a constant c in Lemma 5.2(iii), "lines a_a ± a_b = c" | |
| X | X = 1/p (Lemma 3.5); X = f(x; W_*) (Lemma 3.7); X = m^big_k − p' − p (Thm 5.5) | |
| t | b − b⋆ (§4); grading variable and integration variable (Lemma 3.7); the variable of K^{(ε)}_m ∈ Q[t] | |
| (p, q) | dummy indices in 𝒜_{r,s} (Def. 4.1) | p is the minimal-model integer in §5 |
| a | a_a and a_b (double subscripts); ã_j | Theorem 5.4 then sets a₃ := −ã₃ and a₄ := −ã₄, while Theorem 5.5 uses a₁, a₂ without tildes |

S, W, U, B, M, F, K and C each have three or more meanings as well. For
example, S stands for the action S(σ; λ), the polynomial S(x₁, x₂), the
shifted blocks S_{a,M}(t) and the Kac label S.

Suggested renamings:

- the §3 momentum parameters, for example c = 1 + 24κ² and Δ = P² + κ²;
- the local generating-function variables in §3;
- the dummy box indices in Definition 4.1.

### 5. Dependence on the companion

The paper cites the torus manuscript 20 times by statement number. The cited
statements come from its Sections 5, 6 and 8, and the companion itself is
cited as "companion manuscript in github.com/skypher/virasoro". The following
rest on those citations:

- Proposition 4.3 (the regularity of normalized singular vectors);
- the proof of Proposition 4.4;
- Theorem 5.1;
- Theorem 5.3;
- the proof of Propositions 6.1–6.2.

Those numbers stay valid only while the companion is frozen. There are two
remedies:

- cite a fixed arXiv version of the companion;
- reproduce the few short lemmas actually used, with proofs. Each is under
  half a page: the top coefficient of the inverse Gram matrix (Lemma 5.4), the
  absence of shifted self-poles (Lemma 6.3), and regular normalized singular
  vectors (Lemma 6.6).

The proof of Propositions 6.1–6.2 computes the Shapovalov quantity γ₅
through torus objects:

- the torus matrix element τ⁻₂(d);
- "V_d the torus insertion";
- the d-expansion of the companion's Proposition 6.7.

A sphere reader has to learn torus notation to obtain one number. The
companion's Lemma 5.4(iii) gives the second Jantzen form directly. The other
option is to state the value and name the script that computes it.

Notation and conventions also differ between the two papers:

- sphere P_{r,s}(b, Δ_a, Δ_b) and torus P_{R,S}(b; Δ₁, Δ₂) use different
  argument conventions, and the torus norm is 𝒫 there;
- for even k, Lemma 5.2(ii) factors the singular vector through χ_{r,s}, while
  the companion's Proposition 6.9 factors it through the layer-(2j−1) vector.
  Both factorizations are valid, and a reader of both papers should be told
  that they agree;
- Theorem 4.7 places the coefficients in Q(b⋆)[Δ₁, …, Δ₄], while the
  companion's Theorem 4.2 uses Q(b⋆²)[d]. Since all inputs depend on b², use
  Q(b⋆²) in both;
- unlike the companion's Theorem 4.3, Theorem 4.7 states no bound on the
  actual pole order (m ≤ M̂⋆).

### 6. Introduction

The paragraph starting "At interior minimal-model Kac weights" (lines
193–208) mixes four things:

- results of the companion;
- a list of theorem labels ("For the sphere see Theorems 5.1, 5.3, 5.4
  and 5.5");
- a fact about the polynomial part of 𝓑_N;
- a lemma-by-lemma outline of §3.

No sphere result is stated in the introduction; it only points to theorem
labels. Suggested order: the results, displayed as in the torus introduction;
then the proof outline; then a paragraph on the organization of the paper.

## Specific comments by section

### §2

- Definition 2.2 defines both Φ and Φ̃, and only Φ̃ is used afterwards.
  Define Φ̃, and relate it to Zamolodchikov's Φ in a remark.
- After Definition 2.2: "Proposition 4.4 and its fixed-b⋆ extension give the
  pure-pole recursion" should name Theorem 4.7.
- The Whittaker–Watson citation "§§21.2–21.61, 22.3–22.302" should give the
  section or equation for each of the five identities.

### §3

- Lemma 3.2 is titled "… polynomial extension". Its part (iii) is a
  density reduction from real to complex parameters, so a title saying that
  would be more accurate.
- Lemma 3.5, opening paragraph of the proof: "this follows from the symmetry
  of B and the same trace expansion" is too brief for the identification of
  the formal determinant with the Fredholm determinant.
- Lemma 3.7, Step 1: "the Verma Gram matrix is singular at (c, Δ) = (1, 0)"
  is left hanging. Say why it matters (G_neutral is computed in the Fock
  module).

### §4

- The sign of Λ_j is never fixed. Say that P_{r,s} is even in Λ_a and in Λ_b,
  so the choice does not matter; that is what "pairing (j,l) with (−j,−l)"
  shows.
- Definition 4.5 contains an inductive claim ("Induction on M gives
  ord_t S_{a,M} ≥ −W_{a,M}"). State it as a lemma.

### §5

- "A pole of order zero means regularity." sits inside the paragraph that
  defines the levels. Move it to the statement of Theorem 5.1 or to the
  conventions.
- Theorem 5.4, step (c): the proof switches between generic b and b⋆. Say
  plainly that the BPZ identity holds as an identity of rational functions and
  is then specialized; the text says this, but only in the middle of item 1.
- Theorem 5.5, case M = 3: "(x−1)²/x increases strictly on x ≥ 1. Hence … α² ≥
  min(16/10, 36/12)" is compressed. Write
  α² ≥ ((p−1)²/p)·((p'−1)²/p') and evaluate.

### §6

- Proposition 6.1 writes γ₅, indexing the norm by level, while γ^±_k is
  indexed by layer.
- Proof of Propositions 6.1–6.2:
  - the product [d²]τ⁻₂ = ⅓ · 10/3 · 2 · 7 · 5 · 12 = 2800/3 is given
    without explanation;
  - the root list "x = 1, 5 and for x = 1, 5, 3, 9, 7, 13, 11, 17" should
    say which roots belong to which factor.

### §7

- The section titled "Scope and outlook" contains no outlook.

### Bibliography

- [GRSS22] points to a personal web page (guillaumeremy92.github.io). A quick
  search found the PDF on a Columbia page and no arXiv identifier. If a
  stable version exists, cite it.
