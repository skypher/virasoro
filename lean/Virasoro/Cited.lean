import Virasoro.Statements.Sec5a
import Virasoro.Statements.Sec6
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Results cited from the literature

Each `Cited_*` proposition records a result that the paper uses without proof.  Theorems that
depend on one of them take it as an explicit hypothesis.
-/

namespace Virasoro

open Polynomial

/-- The Kac determinant formula.
Source: V. G. Kac (1979), B. L. Feigin and D. B. Fuchs (1982), in the form of K. Iohara and
Y. Koga, *Representation Theory of the Virasoro Algebra* (2011), Theorem 4.2 and equations
(4.16)–(4.21), as quoted in the proof of Theorem 4.2 of the paper: up to a nonzero factor
independent of `Δ`,
`det G_N(c,Δ) = C_N ∏_{r,s>0, rs≤N} (Δ - Δ_{r,s}(c))^{p(N-rs)}`.
The central charge is parametrised as `c = c(b)`, for which `Δ_{r,s}(c(b)) = h_{r,s}(b)`. -/
def Cited_KacDeterminant : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, ∃ C₀ : ℂ, C₀ ≠ 0 ∧
    (gramPoly (kacC b) N).det =
      C C₀ * ∏ a ∈ labels N, (X - C (kacHL a b)) ^ Fintype.card (Nat.Partition (N - a.lvl))

/-- Uniqueness, up to a scalar, of a singular vector at a fixed level of a Verma module.
Source: Iohara–Koga (2011), Proposition 5.1. -/
def Cited_SingularUnique : Prop :=
  ∀ (c h : ℂ) (n : ℕ) (χ χ' : Verma ℂ c h),
    Verma.IsSingular χ n → Verma.IsSingular χ' n → ∃ a : ℂ, χ' = a • χ

/-- Every nonzero homomorphism between Verma modules over the Virasoro algebra is injective.
Source: Iohara–Koga (2011), the paragraph preceding Corollary 5.2. -/
def Cited_VermaHomInjective : Prop :=
  ∀ (c h h' : ℂ) (f : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c h),
    (∀ (n : ℤ) (v : Verma ℂ c h'), f (Verma.L n v) = Verma.L n (f v)) → f ≠ 0 →
      Function.Injective f

/-- The Jantzen layers at a minimal-model charge and an interior weight.
Sources: Iohara–Koga (2011), Theorem 6.3(i) with equation (6.3), Proposition 5.4 and equations
(5.4), (5.22), (5.49) (Class `R⁺`, Case `1+`); independently A. Astashkevich (1997),
Theorem B(e), case `III₋`.  In the notation of Theorem 5.7 of the paper: for coprime
`p, p' ≥ 2`, `b⋆² = -p'/p`, `λ = h_{r,s}(b⋆)` with `0 < r < p`, `0 < s < p'` and
`p' r + p s < p p'`, the Verma module `M(c⋆,λ)` has for every `k ≥ 1` singular vectors `w^±_k`
of levels `ℓ^±_k`, and the `i`-th layer of the Jantzen filtration along `h ↦ h + x` at fixed
central charge is `U(Vir_-) w⁺_i + U(Vir_-) w⁻_i`. -/
def Cited_JantzenLayers : Prop :=
  ∀ p p' r s : ℕ, 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → 0 < r → r < p → 0 < s → s < p' →
    p' * r + p * s < p * p' →
    ∀ b : ℂ, b ^ 2 = -(p' : ℂ) / p →
      ∃ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b),
        (∀ k : ℕ, 1 ≤ k →
          Verma.IsSingular (wp k) (ellPlus p p' r s k) ∧
          Verma.IsSingular (wm k) (ellMinus p p' r s k)) ∧
        (∀ i : ℕ, 1 ≤ i →
          jantzen (kacC b) (kacH r s b) i = Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i))

/-- The Bernstein–Gelfand–Gelfand resolution at a minimal-model charge and an interior weight,
in the form of its Euler–Poincaré character.
Source: Iohara–Koga (2011), Theorem 6.9 (Class `R⁺`, Case `1+`): the complex
`⋯ → M(ξ_{-2}) ⊕ M(ξ_2) → M(ξ_{-1}) ⊕ M(ξ_1) → M(ξ_0) → L(ξ_0) → 0` of Verma modules is exact,
where `ξ_{±k}` lies `ℓ^∓_k` levels above `ξ_0 = λ`.  Taking dimensions level by level gives
`dim L(c⋆,λ)_N = p(N) + ∑_{k≥1} (-1)^k (p(N - ℓ⁺_k) + p(N - ℓ⁻_k))`, with `p(n) = 0` for
`n < 0`; the level-`N` space of the irreducible quotient has dimension `rank G_N(c⋆,λ)`, and
`ℓ^±_k ≥ k`, so the sum stops at `k = N`. -/
def Cited_BGGCharacter : Prop :=
  ∀ p p' r s : ℕ, 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → 0 < r → r < p → 0 < s → s < p' →
    p' * r + p * s < p * p' →
    ∀ b : ℂ, b ^ 2 = -(p' : ℂ) / p → ∀ N : ℕ,
      ((gram (kacC b) (kacH r s b) N).rank : ℤ) =
        (Fintype.card (Nat.Partition N) : ℤ) +
          ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ) ^ k *
            ((if ellPlus p p' r s k ≤ N then
                (Fintype.card (Nat.Partition (N - ellPlus p p' r s k)) : ℤ) else 0) +
              (if ellMinus p p' r s k ≤ N then
                (Fintype.card (Nat.Partition (N - ellMinus p p' r s k)) : ℤ) else 0))

/-- The generic normalization identities for the torus recursion.
Source: L. Hadasz, Z. Jaskólski and P. Suchanek, JHEP 01 (2010) 063, Section 3: equation (7)
and the paragraph following it (the inverse norm derivative `A_{r,s}(c)` in the normalization
with `L_{-1}^{rs}`-coefficient `1`) and equation (8) (the product of the two torus fusion
polynomials), translated to the conventions of the paper as in the proof of its
Proposition 6.2: `d = ((b + b⁻¹)² - λ_HJS²)/4`, `λ_HJS² = Λ²`.  The cited statement consists of
the two identities for the normalized singular vector over `ℚ(b)`, `NormalizationIdentities`;
their continuation to specializations is not part of it.
`NormalizationIdentities` also asserts that the normalized singular vector exists and is unique.
These two clauses are not from Hadasz–Jaskólski–Suchanek.  Existence of a singular vector of
level `r s` in `M(c(b), h_{r,s}(b))` with nonzero `L_{-1}^{rs}`-coefficient: V. G. Kac (1979) and
B. L. Feigin and D. B. Fuchs (1982), in the form of Iohara–Koga (2011).  Uniqueness up to a
scalar: Iohara–Koga (2011), Proposition 5.1. -/
def Cited_HJSNormalizations : Prop := NormalizationIdentities

end Virasoro
