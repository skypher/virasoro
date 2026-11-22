import Virasoro.Sphere.Proofs.Sec3CentralSubs
import Virasoro.Sphere.Proofs.Sec3LamRegular
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Lemma 3.7, Steps 1–3: the two-boson space and its objects (sphere paper)

sphere/paper.tex l.1023–1027: `ℋ_λ = ℱ^{(1)}_{0,λ} ⊗ ℱ^{(2)}_{0,0}`, two `c = 1` Fock modules
(oscillators `v_m` of weight `λ²` in the first factor, `u_m` of weight `0` in the second), with
the diagonal `c = 2` action `L_k^tot = l_k^{(1)} + l_k^{(2)}`.  This file defines the objects of
Steps 1–3 of the proof of Lemma 3.7 (l.1029–1156).
-/

namespace Virasoro.Sphere

open MvPolynomial TensorProduct

/-- `ℋ_λ = ℱ^{(1)}_{0,λ} ⊗ ℱ^{(2)}_{0,0}` (sphere/paper.tex l.1023–1027). -/
abbrev HH : Type := Fock ⊗[ℂ] Fock

/-- `L_k^tot = l_k^{(1)} + l_k^{(2)}`, with `l_k^{(1)}` the operator (3.2) at `(μ,λ) = (0,λ)` on
the first factor and `l_k^{(2)}` the operator (3.2) at `(0,0)` on the second. -/
noncomputable def Ltot (lam : ℂ) (k : ℤ) : HH →ₗ[ℂ] HH :=
  TensorProduct.map (ffOp 0 lam k) LinearMap.id + TensorProduct.map LinearMap.id (ffOp 0 0 k)

/-- The basis `v^α ⊗ u^β` of `ℋ_λ`. -/
noncomputable def hhBasis : Module.Basis ((ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) ℂ HH :=
  (basisMonomials ℕ+ ℂ).tensorProduct (basisMonomials ℕ+ ℂ)

/-- The Hermitian form of `ℋ_λ`, the tensor product of the forms (3.1):
`⟨x, y⟩ = ∑_{α,β} conj(x_{αβ}) y_{αβ} ∏_m α_m!/(2m)^{α_m} ∏_m β_m!/(2m)^{β_m}`. -/
noncomputable def hhForm (x y : HH) : ℂ :=
  ∑ p ∈ (hhBasis.repr y).support,
    (starRingEnd ℂ) (hhBasis.repr x p) * hhBasis.repr y p * (fockNorm p.1 * fockNorm p.2)

/-- Level `n` of `ℋ_λ`: the span of the `v^α ⊗ u^β` with `|α| + |β| = n`. -/
noncomputable def hhLevel (n : ℕ) : Submodule ℂ HH :=
  Submodule.span ℂ (hhBasis '' {p | lvl p.1 + lvl p.2 = n})

/-- The primary space `𝒫_n(λ) = {P ∈ (ℋ_λ)_n : L_k^tot P = 0 for all k ≥ 1}`
(sphere/paper.tex l.1058–1060).  On level `n` the conditions with `k > n` hold by the grading. -/
noncomputable def primSpace (lam : ℂ) (n : ℕ) : Submodule ℂ HH :=
  hhLevel n ⊓ ⨅ k ∈ Finset.Icc 1 n, LinearMap.ker (Ltot lam (k : ℤ))

/-- The exponent `λ∑_m A_m u_m + ∑_{m,n} B_{m,n} u_m u_n` of the pure Gaussians of l.1034–1035
(`λ² S^{(0)}(u/λ)`; at `λ = 0` the exponent of `F_2`). -/
noncomputable def gaussExpo (lam : ℂ) : MvPowerSeries ℕ+ ℂ :=
  fun α => if α.degree = 1 then lam * S0 α else S0 α

/-- The level-`N` part of the pure Gaussian `exp(λ∑_m A_m u_m + ∑_{m,n} B_{m,n} u_m u_n)`:
`F_1 = gaussF λ` and `F_2 = gaussF 0` (sphere/paper.tex l.1034–1035). -/
noncomputable def gaussF (lam : ℂ) (N : ℕ) : Fock :=
  ∑ α ∈ (finite_level N).toFinset,
    monomial α (MvPowerSeries.coeff α ((PowerSeries.exp ℂ).subst (gaussExpo lam)))

/-- The level-`N` part of `F_tot = F_1 F_2` (sphere/paper.tex l.1047):
`∑_{a+b=N} F_{1,a} ⊗ F_{2,b}`. -/
noncomputable def Ftot (lam : ℂ) (N : ℕ) : HH :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, gaussF lam p.1 ⊗ₜ[ℂ] gaussF 0 p.2

/-- The Gram matrix `G_{a,b} = ⟨P_a, P_b⟩` of a family of vectors of `ℋ_λ`. -/
noncomputable def primGram {ι : Type*} (P : ι → HH) : Matrix ι ι ℂ :=
  Matrix.of fun a b => hhForm (P a) (P b)

/-- `∑_{a,b} conj⟨P_a, F⟩ (G⁻¹)_{a,b} ⟨P_b, F⟩` for a family `(P_a)` with Gram matrix `G`
(sphere/paper.tex l.1068–1071). -/
noncomputable def primCoef {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → HH) (F : HH) : ℂ :=
  ∑ a, ∑ b, (starRingEnd ℂ) (hhForm (P a) F) * (primGram P)⁻¹ a b * hhForm (P b) F

/-! ### Step 2: the operators `D_k`, the map `U(W)` and its adjoint -/

/-- `D_k = ∂_{W_k} + ∑_{m≥1} m W_m ∂_{W_{m+k}}` on the monomial `W^α`
(sphere/paper.tex l.1075–1076).  The sum over `m` runs up to the largest index of a variable of
`W^α`; the further terms vanish. -/
noncomputable def DopMono (k : ℕ) (α : ℕ+ →₀ ℕ) : Fock :=
  let f : Fock := monomial α 1
  dVar k f + ∑ n ∈ Finset.Icc 1 (α.support.sup fun m => (m : ℕ)), (n : ℂ) • (uVar n * dVar (n + k) f)

/-- `D_k`, `k ≥ 1`, on polynomials in the `W_m`. -/
noncomputable def Dop (k : ℕ) : Fock →ₗ[ℂ] Fock :=
  (basisMonomials ℕ+ ℂ).constr ℂ (DopMono k)

/-- Evaluation of the first factor at `W = a`: `P(W,u) ↦ P(a,u)`. -/
noncomputable def evAt (a : ℕ+ → ℂ) : HH →ₗ[ℂ] Fock :=
  (TensorProduct.lid ℂ Fock).toLinearMap ∘ₗ
    TensorProduct.map (MvPolynomial.aeval a : Fock →ₐ[ℂ] ℂ).toLinearMap LinearMap.id

/-- `U(W) : ℱ^{(2)} → ℱ^{(2)}[W]` solves `(D_k + l_k^{(2)}) U(W) = 0` for all `k ≥ 1` with
`U(0) = id` (sphere/paper.tex l.1091–1093).  `U(W)w` is a polynomial in `W` with coefficients in
`ℱ^{(2)}`, an element of `ℋ` with `W` in the first factor. -/
def IsDiffeoU (U : Fock →ₗ[ℂ] HH) : Prop :=
  (∀ k : ℕ, 1 ≤ k → ∀ w : Fock,
    TensorProduct.map (Dop k) LinearMap.id (U w) +
      TensorProduct.map LinearMap.id (ffOp (0 : ℂ) 0 (k : ℤ)) (U w) = 0) ∧
  ∀ w : Fock, evAt 0 (U w) = w

/-- The saddle means `W_{*,m} = iA_m/(2m) = binom(2m,m)/(m 4^m)` (sphere/paper.tex l.1101). -/
noncomputable def Wstar (m : ℕ+) : ℂ :=
  (Nat.choose (2 * (m : ℕ)) (m : ℕ) : ℂ) / (((m : ℕ) : ℂ) * 4 ^ (m : ℕ))

/-- `(U(W_*)^† F_2)_n` (sphere/paper.tex l.1102–1109): the level-`n` vector `y` with
`⟨w, y⟩ = ⟨U(W_*)w, F_2⟩` for every `w` of level `n`, the adjoint taken in the real variables
`W` and then specialized to the real point `W_*`.  Its coefficient of `u^α` is
`⟨U(W_*)u^α, F_2⟩ / ∏_m α_m!/(2m)^{α_m}`; `U(W_*)u^α` has no component of level above `n`. -/
noncomputable def UdagF (U : Fock →ₗ[ℂ] HH) (n : ℕ) : Fock :=
  ∑ α ∈ (finite_level n).toFinset,
    (fockForm (evAt Wstar (U (monomial α 1))) (∑ j ∈ Finset.range (n + 1), gaussF 0 j) /
      fockNorm α) • monomial α 1

/-- The exponent `-∑_{m≥1} (m/16^m) u_m²` of l.1148. -/
noncomputable def diagExpo : MvPowerSeries ℕ+ ℂ :=
  fun α => ∑ m ∈ α.support,
    if α = Finsupp.single m 2 then -(((m : ℕ) : ℂ) / 16 ^ (m : ℕ)) else 0

/-! ### Finite dimension of the levels -/

theorem finite_level_le (n : ℕ) : {α : ℕ+ →₀ ℕ | lvl α ≤ n}.Finite := by
  have h : {α : ℕ+ →₀ ℕ | lvl α ≤ n} = ⋃ a ∈ Set.Iic n, {α : ℕ+ →₀ ℕ | lvl α = a} := by
    ext α
    simp
  rw [h]
  exact (Set.finite_Iic n).biUnion fun a _ => finite_level a

theorem finite_level_pair (n : ℕ) :
    {p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) | lvl p.1 + lvl p.2 = n}.Finite := by
  refine ((finite_level_le n).prod (finite_level_le n)).subset ?_
  rintro ⟨α, β⟩ h
  simp only [Set.mem_setOf_eq] at h
  exact ⟨by simp only [Set.mem_setOf_eq]; omega, by simp only [Set.mem_setOf_eq]; omega⟩

instance hhLevel_finite (n : ℕ) : Module.Finite ℂ (hhLevel n) :=
  FiniteDimensional.span_of_finite ℂ ((finite_level_pair n).image _)

instance primSpace_finite (lam : ℂ) (n : ℕ) : Module.Finite ℂ (primSpace lam n) :=
  Submodule.finiteDimensional_of_le (inf_le_left : primSpace lam n ≤ hhLevel n)

end Virasoro.Sphere
