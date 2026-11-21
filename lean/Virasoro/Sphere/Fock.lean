import Virasoro.Sphere.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Complex.Basic

/-!
# The polynomial Fock space and the Feigin–Fuchs operators (sphere paper, Section 3.1)

`sphere/paper.tex` l.419–444: the Fock space `ℂ[u₁,u₂,…]` graded by `deg u_m = m`, the Hermitian
form (3.1), and the differential operators (3.2) with parameters `μ, λ`.

The operators are defined over any field `K` containing `ℂ`, with `μ, λ ∈ K`: `K = ℂ` for
Lemma 3.2, and `K = ℂ(λ)` for the `λ⁻¹`-expansion of Lemma 3.3.
-/

namespace Virasoro.Sphere

open MvPolynomial

/-- The polynomial Fock space `ℂ[u₁, u₂, …]`. -/
abbrev Fock : Type := MvPolynomial ℕ+ ℂ

/-- The grading `deg u_m = m` (sphere/paper.tex l.423–424).  The level-`m` part of the Fock
space consists of the `f` with `IsWeightedHomogeneous fockWeight f m`. -/
def fockWeight : ℕ+ → ℕ := fun m => (m : ℕ)

/-- The weight `∏_m α_m!/(2m)^{α_m}` of the monomial `u^α` in (3.1). -/
noncomputable def fockNorm (α : ℕ+ →₀ ℕ) : ℂ :=
  α.prod fun m a => (a.factorial : ℂ) / (2 * (m : ℂ)) ^ a

/-- The Hermitian form (3.1): `⟨f̄, g⟩ = ∑_α conj(f_α) g_α ∏_m α_m!/(2m)^{α_m}`. -/
noncomputable def fockForm (f g : Fock) : ℂ :=
  ∑ α ∈ g.support, (starRingEnd ℂ) (coeff α f) * coeff α g * fockNorm α

/-- The bilinear version of (3.1), without the conjugation (Lemma 3.2(ii)):
`∑_α f_α g_α ∏_m α_m!/(2m)^{α_m}`. -/
noncomputable def fockBil (f g : Fock) : ℂ :=
  ∑ α ∈ g.support, coeff α f * coeff α g * fockNorm α

section Operators

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- The variable `u_n` for a natural number `n ≥ 1`. -/
noncomputable def uVar (n : ℕ) : MvPolynomial ℕ+ K := X n.toPNat'

/-- `∂/∂u_n` for a natural number `n ≥ 1`. -/
noncomputable def dVar (n : ℕ) : MvPolynomial ℕ+ K →ₗ[K] MvPolynomial ℕ+ K :=
  (pderiv n.toPNat').toLinearMap

/-- The operator `l_k` of (3.2) on the monomial `u^α`.  The sums over `n ≥ 1` run up to the
largest index of a variable of `u^α`; the further terms vanish. -/
noncomputable def ffOpMono (μ lam : K) (k : ℤ) (α : ℕ+ →₀ ℕ) : MvPolynomial ℕ+ K :=
  let f : MvPolynomial ℕ+ K := monomial α 1
  let B : ℕ := α.support.sup fun m => (m : ℕ)
  let i : K := algebraMap ℂ K Complex.I
  if k = 0 then
    ∑ n ∈ Finset.Icc 1 B, (n : K) • (uVar n * dVar n f) + C (lam ^ 2 + μ ^ 2) * f
  else if 0 < k then
    ∑ n ∈ Finset.Icc 1 B, (n : K) • (uVar n * dVar (n + k.toNat) f)
      - (1 / 4 : K) • ∑ n ∈ Finset.Icc 1 (k.toNat - 1), dVar n (dVar (k.toNat - n) f)
      + C (μ * (k.toNat : K) + i * lam) * dVar k.toNat f
  else
    ∑ n ∈ Finset.Icc 1 B, ((n + (-k).toNat : ℕ) : K) • (uVar (n + (-k).toNat) * dVar n f)
      - (∑ n ∈ Finset.Icc 1 ((-k).toNat - 1),
          ((n * ((-k).toNat - n) : ℕ) : K) • (uVar n * uVar ((-k).toNat - n))) * f
      + C (2 * ((-k).toNat : K) * (μ * ((-k).toNat : K) - i * lam)) * uVar (-k).toNat * f

/-- The Feigin–Fuchs operator `l_k`, `k ∈ ℤ`, of (3.2) with parameters `μ, λ`: the linear map
with the values `ffOpMono` on the monomials. -/
noncomputable def ffOp (μ lam : K) (k : ℤ) : MvPolynomial ℕ+ K →ₗ[K] MvPolynomial ℕ+ K :=
  (basisMonomials ℕ+ K).constr K (ffOpMono μ lam k)

/-- `l_{-Y} 1 = l_{-y₁} ⋯ l_{-y_r} 1` for a word `Y = [y₁, …, y_r]`. -/
noncomputable def fockWord (μ lam : K) : List ℕ → MvPolynomial ℕ+ K
  | [] => 1
  | y :: w => ffOp μ lam (-(y : ℤ)) (fockWord μ lam w)

/-- A solution `F = ∑_m F_m` of the Ward equations `l_k F = (l_0 + kΔ_b - Δ_a) F`, `k ≥ 1`, with
`F_0 = 1` and `F_m` of level `m` (Lemma 3.2(ii)).  At level `m` the equation for `k` reads
`l_k F_{m+k} = (l_0 + kΔ_b - Δ_a) F_m`. -/
def IsWardSeries (μ lam Δa Δb : K) (F : ℕ → MvPolynomial ℕ+ K) : Prop :=
  F 0 = 1 ∧ (∀ m : ℕ, IsWeightedHomogeneous fockWeight (F m) m) ∧
  ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ,
    ffOp μ lam k (F (m + k)) = ffOp μ lam 0 (F m) + C ((k : K) * Δb - Δa) * F m

end Operators

end Virasoro.Sphere
