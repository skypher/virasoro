import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Local Smith exponents and crossing forms (paper Section 5)

`G` is a square matrix over `K⟦X⟧` (the paper's `ℂ[[x]]`).  Its local Smith exponents are
recorded as a multiset: `IsSmith G s` says that `U G V = diag(x^{e_i})` for unimodular `U`, `V`
and that `s` is the multiset of the exponents `e_i`.  The paper's ordered tuple
`0 ≤ e₁ ≤ ⋯ ≤ e_m` is the sorted form of this multiset.
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `s` is the multiset of local Smith exponents of `G`: there are `U, V ∈ GL(K⟦X⟧)` with
`U G V = diag(x^{e_i})`, and `s = {e_i}`. -/
def IsSmith (G : Matrix ι ι K⟦X⟧) (s : Multiset ℕ) : Prop :=
  ∃ (e : ι → ℕ) (U V : Matrix ι ι K⟦X⟧), IsUnit U.det ∧ IsUnit V.det ∧
    U * G * V = Matrix.diagonal (fun i => (PowerSeries.X : K⟦X⟧) ^ e i) ∧
    s = Finset.univ.val.map e

/-- The coefficient matrix `G_n` in `G(x) = G₀ + x G₁ + x² G₂ + ⋯`. -/
noncomputable def coeffMat (n : ℕ) (G : Matrix ι ι K⟦X⟧) : Matrix ι ι K :=
  G.map (PowerSeries.coeff n)

/-- The inverse matrix `G(x)⁻¹` over the field of Laurent series. -/
noncomputable def invLaurent (G : Matrix ι ι K⟦X⟧) : Matrix ι ι K⸨X⸩ :=
  (G.map (HahnSeries.ofPowerSeries ℤ K))⁻¹

/-- The pole order of `G(x)⁻¹` at `x = 0`: the largest pole order of its entries. -/
noncomputable def poleOrderInv (G : Matrix ι ι K⟦X⟧) : ℕ :=
  Finset.univ.sup fun p : ι × ι => (-(invLaurent G p.1 p.2).order).toNat

/-- The coefficient matrix `[x^n] G(x)⁻¹`; `invCoeff G (-1) = Res_{x=0} G(x)⁻¹`. -/
noncomputable def invCoeff (G : Matrix ι ι K⟦X⟧) (n : ℤ) : Matrix ι ι K :=
  Matrix.of fun i j => (invLaurent G i j).coeff n

/-- `K₁ = ker G(0)`. -/
noncomputable def ker0 (G : Matrix ι ι K⟦X⟧) : Submodule K (ι → K) :=
  LinearMap.ker (coeffMat 0 G).mulVecLin

/-- The first crossing form `β₁(u, v) = uᵀ G₁ v` (evaluated on vectors of `ι → K`; the paper
restricts it to `K₁ = ker G(0)`). -/
noncomputable def cross1 (G : Matrix ι ι K⟦X⟧) (u v : ι → K) : K :=
  u ⬝ᵥ (coeffMat 1 G).mulVec v

/-- `K₂ = ker (β₁ : K₁ → K₁^*)`: the vectors of `K₁` that are `β₁`-orthogonal to `K₁`. -/
noncomputable def ker2 (G : Matrix ι ι K⟦X⟧) : Submodule K (ι → K) where
  carrier := {v | v ∈ ker0 G ∧ ∀ u ∈ ker0 G, cross1 G u v = 0}
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨add_mem hv hw, fun u hu => ?_⟩
    simp [cross1, Matrix.mulVec_add, dotProduct_add] at *
    rw [hv' u hu, hw' u hu, add_zero]
  zero_mem' := ⟨zero_mem _, fun u _ => by simp [cross1]⟩
  smul_mem' := by
    rintro a v ⟨hv, hv'⟩
    refine ⟨Submodule.smul_mem _ a hv, fun u hu => ?_⟩
    simp [cross1, Matrix.mulVec_smul, dotProduct_smul] at *
    exact Or.inr (hv' u hu)

/-- The second crossing form `β₂(u, v) = uᵀ (G₂ v + G₁ v₁)`, where `v₁` is a chosen solution of
`G₀ v₁ = - G₁ v`. -/
noncomputable def cross2 (G : Matrix ι ι K⟦X⟧) (u v v₁ : ι → K) : K :=
  u ⬝ᵥ ((coeffMat 2 G).mulVec v + (coeffMat 1 G).mulVec v₁)

end Virasoro
