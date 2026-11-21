import Virasoro.Statements.Prelude
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Disjoint

/-!
# Two-weight pairings, fusion polynomials and irreducible traces (paper Sections 9, 10)
-/

namespace Virasoro

open Polynomial

section Pairing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h₁ h₂ : R}

/-- The two-weight pairing `ρ_{Δ₁,Δ₂;d}` of paper Lemma 10.1: `ρ(v_{Δ₁}, v_{Δ₂}) = 1` and the
Ward identity (10.1).  For homogeneous `u`, `v` of levels `N₁`, `N₂`,
`((Δ₁+N₁) - (Δ₂+N₂)) ρ(u,v) = ρ(L₀u, v) - ρ(u, L₀v)`, which is the form used here. -/
def Verma.IsTwoWeightPairing (d : R) (T : Verma R c h₁ →ₗ[R] Verma R c h₂ →ₗ[R] R) : Prop :=
  T Verma.hw Verma.hw = 1 ∧ ∀ (n : ℤ) (u : Verma R c h₁) (v : Verma R c h₂),
    T (Verma.L (-n) u) v - T u (Verma.L n v) =
      T (Verma.L 0 u) v - T u (Verma.L 0 v) + (n : R) * d * T u v

end Pairing

section Fusion

variable {𝔽 : Type*} [Field 𝔽]

/-- The index set `{1-r, 3-r, …, r-1}`. -/
def stepRange (r : ℕ) : Finset ℤ := (Finset.range r).image fun i : ℕ => 2 * (i : ℤ) + 1 - r

/-- The fusion polynomial `P_{r,s}(b;Δ_a,Δ_b)` (torus paper equation (10.9), sphere paper
equation (4.2)):
`∏_{j,l} (Λ_a+Λ_b+jb+lb⁻¹)/2 · (Λ_a-Λ_b+jb+lb⁻¹)/2`, `Λ² = (b+b⁻¹)² - 4Δ`, over
`j ∈ {1-r,3-r,…,r-1}`, `l ∈ {1-s,3-s,…,s-1}`.  The factors of `(j,l)` and `(-j,-l)` are
multiplied together, which removes the square roots: with `A = Λ_a²`, `B = Λ_b²`,
`β = jb + lb⁻¹`, their product is `((A - B + β²)² - 4Aβ²)/16`, and the factor of
`(j,l) = (0,0)` is `(A - B)/4 = Δ_b - Δ_a`.  One pair `(j,l)` of each `±` class is kept:
`j > 0`, or `j = 0` and `l > 0`. -/
def fusP (r s : ℕ) (b Δa Δb : 𝔽) : 𝔽 :=
  let A : 𝔽 := (b + b⁻¹) ^ 2 - 4 * Δa
  let B : 𝔽 := (b + b⁻¹) ^ 2 - 4 * Δb
  (if (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s then (A - B) / 4 else 1) *
    ∏ x ∈ (stepRange r ×ˢ stepRange s).filter fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
      ((A - B + ((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) ^ 2) ^ 2
        - 4 * A * ((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) ^ 2) / 16

end Fusion

/-- The Verma form `ρ(c,h,d)` descends to the irreducible quotient `L(c,h) × L(c,h)`: it
vanishes when either argument lies in the radical of the Shapovalov form (paper
Theorem 9.1(i)). -/
def TorusDescends (c h d : ℂ) : Prop :=
  ∀ T : Verma ℂ c h →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ, Verma.IsPrimaryPairing d T →
    ∀ B : Verma ℂ c h →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ, Verma.IsShapovalov B →
      ∀ u : Verma ℂ c h, (∀ v, B v u = 0) → ∀ v, T u v = 0 ∧ T v u = 0

/-- `T` is the level-`N` coefficient `T^irr_N(c,h,d)` of the irreducible trace
`Tr_{L(c,h)} q^{L₀-h} V_d(1)` (paper equation (9.1)).  The level-`N` space of `L(c,h)` is
`M(c,h)_N / ker G_N(c,h)`; `E` is a family of vectors of `M(c,h)_N` (in coordinates) whose
classes form a basis of it.  With `A = (B(E_i,E_j))`, which is then invertible, and
`Rm = (ρ(E_i,E_j))`, the operator induced by `V_d(1)` has matrix `A⁻¹ Rm`, and `T` is its trace.
When `ρ` descends to `L(c,h)` the value does not depend on `E`. -/
def IsIrrTrace (c h d : ℂ) (N : ℕ) (T : ℂ) : Prop :=
  ∃ (n : ℕ) (E : Fin n → (Nat.Partition N → ℂ)),
    LinearIndependent ℂ E ∧
    IsCompl (Submodule.span ℂ (Set.range E)) (LinearMap.ker (gram c h N).mulVecLin) ∧
    (Matrix.of fun i j => gramForm c h N (E i) (E j)).det ≠ 0 ∧
    T = ∑ i, ∑ j, (Matrix.of fun i j => gramForm c h N (E i) (E j))⁻¹ i j *
      torusForm c h d N (E j) (E i)

/-- A rational function `f` of `(b, Δ)` (inner variable `b`, outer variable `Δ`) is regular at
the point `(b₁, μ)`: `f = P/Q` with polynomials `P, Q ∈ ℂ[b][Δ]` and `Q(b₁, μ) ≠ 0`. -/
def JointRegular (f : RatFunc (RatFunc ℂ)) (b₁ μ : ℂ) : Prop :=
  ∃ P Q : Polynomial (Polynomial ℂ), (Q.eval (C μ)).eval b₁ ≠ 0 ∧
    f * algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (Q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) =
      algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))

end Virasoro
