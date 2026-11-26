# A fixed-charge recursion at rational b² (Ribault's question): first attempt

Started 2026-11-26 (user, tmp terminal, about 16:0x Taiwan: "try it", after the
question whether Ribault's rational-b² recursion is hard; then /goal "finish
ribault question proof.").

**Update 2026-11-26 (about 17:00 Taiwan): general proof written, awaiting
review.** notes/ribault/fixed_charge_recursion.tex (PDF next to it) proves the
chain-function regularity for all layers, all Kac weights and every
b⋆ ∈ ℂ^× (torus and sphere blocks), and the resulting fixed-charge recursion
(Theorem 9 there; definitions and lemmas share one counter). The missing step listed below under "What is open" is
supplied by a cutting identity (Lemma 5 there):
j·c^(k)_{λ→μ,j} = c^(k+1)_{λ→μ,j−1} − Σ_ν c^(k)_{λ→ν,0}·c^(1)_{ν→μ,j−1},
which reduces j ≥ 1 to chain functions of smaller level, and an induction on
the level μ − λ (Lemma 8). End-to-end checks of the recursion as an algorithm
(fixed_charge_recursion.py, logs fcr_c0.log, fcr_sweep.log): 99 levels, every
Kac weight, torus at c = 0, 1/2, −22/5, 1, 25, 26 and sphere at c = 0, 1/2, 1,
pole orders up to 5; Shapovalov inversion agrees where run. The sections below
are the record of the first attempt.

## The question

Ribault, *Exactly solvable CFTs* (arXiv:2411.17262v4), §4.3.3: the terms of
Zamolodchikov's recursion "have Δ-independent poles at rational values of β².
As a result, the recursion is only valid if β² ∉ ℚ. Finding a recursion for
β² ∈ ℚ is an open problem, whose simplest incarnation is in the case of
1-point Virasoro blocks on the torus."

paper.tex (Theorem 7.3) computes every principal-part coefficient
A_{λ,k,N} of the eta-reduced torus coefficient H_N(c⋆, Δ, d) at a fixed b⋆ as
CT_t of collision moments. That formula needs the shifted blocks
S_{a,M}(t) = H_M(c(b⋆+t), z_a(t), d) as Laurent series in t, i.e. Taylor data
of blocks in b away from c⋆. The question here: can the principal parts be
written with blocks at c = c⋆ only (values, Δ-derivatives, finite parts at
shifted weights), with coefficients that do not depend on N?

Notation as in paper.tex §§6–7; u = b² − b⋆² (the constant terms below do not
depend on the choice of local coordinate because the quantities involved are
regular). R_a(u), h_a(u), z_a(u) = h_a(u) + ℓ_a are the generic residue,
Kac weight and shifted weight of the label a.

## Result 1: the second Jantzen layer (derivation)

Let λ be an interior weight at a minimal-model charge and ℓ₂ ≤ N < ℓ₃. For a
label a in the collision class C_λ put μ_a = z_a(0). For a label g with
h_g(0) = μ_a and ℓ_g ≤ N − ℓ_a put ν = z_g(0), M′ = N − ℓ_a − ℓ_g,

    e_{ag}(u) = z_a(u) − h_g(u) = σ u + τ u² + …,   R_a R_g = P₀ + P₁ u + …,
    K_{ag} = P₁/σ − P₀ τ/σ²,   M_{ag} = P₀ z_g′(0)/σ.

Candidate formula:

    A_{λ,1,N} = Σ_{a∈C_λ} R_a(0) · FP_{Δ=μ_a} H_{N−ℓ_a}(c⋆, Δ)
              + Σ_{(a,g)} [ K_{ag} H_{M′}(c⋆, ν) + M_{ag} ∂_Δ H_{M′}(c⋆, ν) ],
    A_{λ,2,N} = Σ_{(a,g)} (P₀ h_a′(0)/σ) H_{M′}(c⋆, ν)      (= Theorem 8.2).

Only blocks at c⋆ enter; the coefficients are N-independent numbers computed
from the closed-form R and h.

Derivation. (1) Split H_{N−ℓ_a}(b, Δ) near (b⋆, μ_a) into the colliding
group at μ_a (labels g above) and a remainder Reg. Every other group is
regular in t at Δ ≠ its own weight (moment regularity, proof of Thm 7.3), so
Reg is jointly regular at (b⋆, μ_a), and Reg(b⋆, μ_a) = FP_{μ_a} H_{N−ℓ_a}(c⋆, ·)
because the group at μ_a is purely principal at c⋆. (2) In the group term
R_a R_g H_{M′}(b, z_g(t)) / e_{ag}(t), the deeper block is jointly regular at
(b⋆, ν) for N < ℓ₃ (det G_{M′}(c⋆, ν) ≠ 0, Thm 8.2). Expanding to first order,
∂_b H_{M′}(b⋆, ν) appears with the coefficient Σ_{(a,g)→ν} P₀/σ. (3) That sum
is the [t⁻¹] coefficient of the first moment at the level N = ν − λ, where the
deepest block is H₀ = 1 (for the higher second-layer weight, use the lower
one's identity first); the first moment is regular (Thm 7.3), so the sum is 0.
Only c⋆ data remain. To be written out in full and reviewed.

Checks (runs/ribault/layer2_recursion.py, exact rationals):

| case | levels | external weight | result |
|---|---|---|---|
| (2,3), λ = 0 | 1–11 (layer 2: 5–11) | 3/7 | formula = Theorem 7.3; Gram inversion agrees for N ≤ 7 |
| (3,4), λ = 1/2 | 6–10 (layer 2 from 7) | 2/9 | formula = Theorem 7.3; Gram agrees for N ≤ 7 |
| (2,5), λ = −1/5 | 8–11 (layer 2 from 9) | −4/13 | formula = Theorem 7.3 |

At (2,3), level 12 (third layer) the formula stops applying: H₇(c⋆, ·) has a
pole at the second-layer weight 5.

## Result 2: all layers, observed

runs/ribault/jet_expansion.py expands every shifted block recursively along
collision chains and keeps the jets J[(M, μ), i, j] = ∂_u^i ∂_Δ^j Reg(b⋆, μ)
of the regular remainders as formal unknowns. Jets with i = 0 are c⋆ data;
jets with i ≥ 1 are b-derivatives. The coefficient of J[(M, μ), i, j] is
CT(c_{μ,j}(u) u^i)/i!, where the chain sum

    c^{(k)}_{μ,j}(u) = Σ_{chains λ → … → μ} (Π R/e)(u) · R_a δ_a(u)^{k−1} · (z_last(u) − μ)^j / j!

depends only on the generic residue data, not on N or on the blocks.

Observation: in every case tested, every chain sum c_{μ,j}(u) is regular at
u = 0. Then every b-derivative drops out and

    A_{λ,k,N} = Σ_μ Σ_j c^{(k)}_{μ,j}(0) · ∂_Δ^j [H_{N−(μ−λ)}(c⋆, Δ) − PP_μ](Δ = μ),

a recursion in fixed-charge blocks with N-independent coefficients
(PP_μ = principal part at μ). For generic b⋆ the chains have length one and
this is Zamolodchikov's recursion.

| case | levels, orders k | max pole order seen | b-jets surviving | chain sums | c⋆ part = A |
|---|---|---|---|---|---|
| (2,3), λ = 0 | N ≤ 24, k ≤ 4 | 4 (from N = 22) | none | regular | checked N ≤ 14 |
| (3,4), λ = 1/2 | N = 24–27, k ≤ 4 | 3 (from N = 25) | none | regular | — |
| (2,5), λ = −1/5 | N = 20–23, k ≤ 4 | 3 (from N = 21) | none | regular | — |
| (2,3), boundary λ = 1/3 | N ≤ 20, k ≤ 5 | 3 (from N = 18) | none | regular | checked N = 18, 19 |
| c = 1 (b² = −1), λ = 0 | N ≤ 12, k ≤ 5 | 3 (from N = 9) | none | regular | checked N = 8–12 (jet order up to 9) |
| c = 25 (b² = 1), λ = −5/4 | N ≤ 14, k ≤ 5 | 2 | none | regular | — |
| b² = 3/2 (c = 26), λ = −4 | N ≤ 16, k ≤ 5 | 2 | none | regular | checked N = 5–10 |

Negative control (runs/ribault/negative_control.py): rescaling R_{1,4} by a
constant 1 + ε breaks the identity of step (3), and ∂_u H_{N−5}(·, 5) then
survives at every N ≥ 6. Rescaling by 1 + εu leaves P₀ unchanged and nothing
survives, as the derivation predicts.

## What is open

- **Chain-sum regularity in general** (the hard step): for every chain end μ,
  every k and j, c^{(k)}_{μ,j}(u) is regular at u = 0. For j = 0 it follows by
  induction on μ from moment regularity at the level N = μ − λ, provided the
  chain sums of all lower nodes are regular for all j. For j ≥ 1 there is no
  argument yet. At layer 2 the cases j ≥ 1 are automatic (the factor
  (z − μ)^j cancels the single pole); from layer 3 on they are not (example:
  the ∂_b∂_Δ jet at layer 3 needs Σ_{3-chains} R R R z′/(σσ) = 0).
  Routes to try: (a) the polar parts satisfy linear equations at the levels
  N = μ − λ + m with the jets of H_m(c⋆, ·) at μ as coefficients, so a
  Wronskian nondegeneracy of H₀, H₁, … at μ would finish the induction;
  (b) the same expansion for the matrix G_N(b, Δ)⁻¹, where the deep blocks
  are matrices and moment regularity gives matrix identities.
- **Coefficients intrinsic to the module**: the c_{μ,j}(0) are computed from
  Taylor data in b of the closed-form residues and Kac weights. They are
  finite at b⋆, but only the top coefficient (Thm 8.2) has a module meaning
  (𝒩/γ). Whether the others are higher Jantzen data is not known.
- **Identity in d**: each run uses one rational d. The layer-2 derivation holds
  for indeterminate d; the observations at deeper layers are tested at single
  values only.
- **Sphere block**: not tested; the jet expansion applies verbatim with the
  sphere residues.

## Files

notes/ribault/: layer2_recursion.py, jet_expansion.py, negative_control.py
(exact rational arithmetic; -h for usage; layer2_recursion.py uses
tools/direct_reconstruction.py for the Gram cross-check) and the logs cited
above (calib_c0_n7, c0_n12, other_models, jets_c0_values, jets_c0_deep,
chainsums_c0, jets_other2, jets_layer3_rerun, negative_control,
negative_control_const, values_other, jets_c1_jmax9). The runs were made
from the local folder runs/ribault/ before the copy.
