import Virasoro.Block
import Virasoro.Local
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Basic

/-!
# Sphere four-point blocks and the elliptic `H`-series (sphere paper Definitions 2.1, 2.2)

External weights are a function `Δe : Fin 4 → 𝔽`, with `Δe 0, …, Δe 3` the paper's
`Δ₁, …, Δ₄`.
-/

namespace Virasoro.Sphere

open Polynomial

section ThreePoint

variable {R : Type*} [CommRing R]

/-- The three-point polynomial `γ_Y(Δ;Δ_a,Δ_b) = ∏_j (Δ + ∑_{i>j} y_i + y_j Δ_b - Δ_a)` of
sphere paper equation (2.1), for the word `Y = [y₁, …, y_r]`. -/
def gammaY (Δ Δa Δb : R) : List ℕ → R
  | [] => 1
  | y :: w => (Δ + ((w.sum : ℕ) : R) + (y : R) * Δb - Δa) * gammaY Δ Δa Δb w

/-- `φ = ⟨ · |Φ_b(1)|Δ_a⟩` (sphere paper Definition 2.1): `φ(v_Δ) = 1` and
`φ(L_{-n}u) = (h(u) + nΔ_b - Δ_a) φ(u)` for homogeneous `u` and `n ≥ 1`, where
`h(u) φ(u) = φ(L₀u)`. -/
def IsThreePoint [Algebra ℚ R] {c h : R} (Δa Δb : R) (φ : Verma R c h →ₗ[R] R) : Prop :=
  φ Verma.hw = 1 ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : Verma R c h,
    φ (Verma.L (-(n : ℤ)) u) = φ (Verma.L 0 u) + ((n : R) * Δb - Δa) * φ u

end ThreePoint

section Block

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `γ_Y(Δ;Δ_a,Δ_b)` as a polynomial in the internal weight `Δ`, for a partition `Y` of `N`. -/
noncomputable def gammaPoly (Δa Δb : 𝔽) (N : ℕ) (Y : Nat.Partition N) : 𝔽[X] :=
  gammaY (X : 𝔽[X]) (C Δa) (C Δb) Y.word

/-- The numerator `∑ γ_Y(Δ;Δ₄,Δ₃) adj(G_N)_{Y,Z} γ_Z(Δ;Δ₁,Δ₂)` of `ℬ_N`. -/
noncomputable def Bnum (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) : 𝔽[X] :=
  ∑ Y : Nat.Partition N, ∑ Z : Nat.Partition N,
    gammaPoly (Δe 3) (Δe 2) N Y * (gramPoly c N).adjugate Y Z * gammaPoly (Δe 0) (Δe 1) N Z

/-- The sphere block coefficient
`ℬ_N(c,Δ,Δ_i) = ∑_{|Y|=|Z|=N} γ_Y(Δ;Δ₄,Δ₃) (G_N(c,Δ)⁻¹)_{Y,Z} γ_Z(Δ;Δ₁,Δ₂)`
(sphere paper equation (2.2)) as a rational function of `Δ`, by Cramer's rule; `ℬ_0 = 1`. -/
noncomputable def Bsph (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) : RatFunc 𝔽 :=
  algebraMap 𝔽[X] (RatFunc 𝔽) (Bnum c Δe N) / algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det

end Block

section Theta

/-- `θ₃(q) = ∑_{n∈ℤ} q^{n²}` with integer coefficients. -/
noncomputable def theta3Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else if Nat.sqrt n ^ 2 = n then 2 else 0

/-- `θ₄(q) = ∑_{n∈ℤ} (-1)^n q^{n²}` with integer coefficients. -/
noncomputable def theta4Z : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    if n = 0 then 1 else if Nat.sqrt n ^ 2 = n then 2 * (-1) ^ Nat.sqrt n else 0

/-- `ψ(q) = ∑_{n≥0} q^{n(n+1)}`, so that `θ₂(q) = ∑_{n∈ℤ} q^{(n+1/2)²} = 2 q^{1/4} ψ(q)` and
`θ₂(q)⁴ = 16 q ψ(q)⁴`. -/
noncomputable def thetaPsiZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if Nat.sqrt n * (Nat.sqrt n + 1) = n then 1 else 0

variable (A : Type*) [Field A]

/-- `θ₃(q)` over the field `A`. -/
noncomputable def th3 : PowerSeries A := theta3Z.map (Int.castRingHom A)

/-- `θ₄(q)` over the field `A`. -/
noncomputable def th4 : PowerSeries A := theta4Z.map (Int.castRingHom A)

/-- `ψ(q)` over the field `A`. -/
noncomputable def thPsi : PowerSeries A := thetaPsiZ.map (Int.castRingHom A)

/-- The cross-ratio `z(q) = θ₂(q)⁴/θ₃(q)⁴ = 16 q ψ(q)⁴/θ₃(q)⁴` as a power series in `q`. -/
noncomputable def zq : PowerSeries A := 16 * PowerSeries.X * thPsi A ^ 4 * (th3 A ^ 4)⁻¹

/-- `16q/z(q) = θ₃(q)⁴/ψ(q)⁴`, a power series with constant term `1`. -/
noncomputable def nomeRatio : PowerSeries A := th3 A ^ 4 * (thPsi A ^ 4)⁻¹

variable {A}

/-- The generalized binomial coefficient `a(a-1)⋯(a-k+1)/k!`. -/
noncomputable def gbinom (a : A) (k : ℕ) : A :=
  (∏ i ∈ Finset.range k, (a - (i : A))) / (k.factorial : A)

/-- The power `f^a = ∑_k binom(a,k) (f-1)^k` of a power series `f` with constant term `1`, for
an exponent `a` in the coefficient field.  The coefficient of `q^n` only involves `k ≤ n`. -/
noncomputable def fpow (f : PowerSeries A) (a : A) : PowerSeries A :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), gbinom a k * PowerSeries.coeff n ((f - 1) ^ k)

end Theta

section HSeries

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- The prefactor `Φ̃(c,Δ,Δ_i;q) = (16q/z(q))^{Δ-(c-1)/24} (1-z(q))^{(c-1)/24-Δ₂-Δ₃}
θ₃(q)^{(c-1)/2-4∑Δ_j}` of sphere paper Definition 2.2, a power series in `q` over `𝔽(Δ)`. -/
noncomputable def PhiTilde (c : 𝔽) (Δe : Fin 4 → 𝔽) : PowerSeries (RatFunc 𝔽) :=
  fpow (nomeRatio (RatFunc 𝔽)) (RatFunc.X - (RatFunc.C c - 1) / 24) *
    fpow (1 - zq (RatFunc 𝔽)) ((RatFunc.C c - 1) / 24 - RatFunc.C (Δe 1) - RatFunc.C (Δe 2)) *
    fpow (th3 (RatFunc 𝔽))
      ((RatFunc.C c - 1) / 2 - 4 * RatFunc.C (Δe 0 + Δe 1 + Δe 2 + Δe 3))

/-- `∑_m ℬ_m(c,Δ,Δ_i) z(q)^m` as a power series in `q`; the coefficient of `q^n` only involves
`m ≤ n`. -/
noncomputable def BzSeries (c : 𝔽) (Δe : Fin 4 → 𝔽) : PowerSeries (RatFunc 𝔽) :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.range (n + 1), Bsph c Δe m * PowerSeries.coeff n (zq (RatFunc 𝔽) ^ m)

/-- The elliptic series `H(c,Δ,Δ_i;q) = Φ̃(c,Δ,Δ_i;q)⁻¹ ∑_m ℬ_m z(q)^m`, sphere paper
equation (2.7), as a power series in `q`. -/
noncomputable def Hseries (c : 𝔽) (Δe : Fin 4 → 𝔽) : PowerSeries (RatFunc 𝔽) :=
  (PhiTilde c Δe)⁻¹ * BzSeries c Δe

/-- The coefficient `H_N(c,Δ,Δ_i)` of `(16q)^N` in the elliptic series. -/
noncomputable def Hsph (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) : RatFunc 𝔽 :=
  PowerSeries.coeff N (Hseries c Δe) / 16 ^ N

end HSeries

/-- The field `ℂ(Δ₁,Δ₂,Δ₃,Δ₄)` of rational functions of the external weights. -/
abbrev K4 : Type := FractionRing (MvPolynomial (Fin 4) ℂ)

/-- The indeterminate external weights `Δ₁, …, Δ₄` as elements of `ℂ(Δ₁,…,Δ₄)`. -/
noncomputable def ΔK : Fin 4 → K4 := fun i => algebraMap (MvPolynomial (Fin 4) ℂ) K4 (MvPolynomial.X i)

/-- A complex number as an element of `ℂ(Δ₁,…,Δ₄)`. -/
noncomputable abbrev cK (x : ℂ) : K4 := algebraMap ℂ K4 x

end Virasoro.Sphere
