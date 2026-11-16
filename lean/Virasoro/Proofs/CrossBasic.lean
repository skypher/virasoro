import Virasoro.Proofs.SmithLayers

/-!
# Coefficient identities for `G(x) · x^p G(x)⁻¹ = x^p` and vectors of power series
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_ker0 {G : Matrix ι ι K⟦X⟧} {v : ι → K} :
    v ∈ ker0 G ↔ (coeffMat 0 G).mulVec v = 0 := by
  simp [ker0]

/-- The coefficient vectors of `G v` for a vector `v` of power series. -/
theorem coeff_mulVec (G : Matrix ι ι K⟦X⟧) (V : ι → K⟦X⟧) (n : ℕ) :
    (fun j => PowerSeries.coeff n (G.mulVec V j)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (coeffMat p.1 G).mulVec fun j => PowerSeries.coeff p.2 (V j) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, map_sum, PowerSeries.coeff_mul, coeffMat,
    Matrix.map_apply, Finset.sum_apply]
  rw [Finset.sum_comm]

theorem coeff_zero_mulVec (G : Matrix ι ι K⟦X⟧) (V : ι → K⟦X⟧) :
    (fun j => PowerSeries.coeff 0 (G.mulVec V j)) =
      (coeffMat 0 G).mulVec fun j => PowerSeries.coeff 0 (V j) := by
  rw [coeff_mulVec]; simp

theorem coeff_one_mulVec (G : Matrix ι ι K⟦X⟧) (V : ι → K⟦X⟧) :
    (fun j => PowerSeries.coeff 1 (G.mulVec V j)) =
      ((coeffMat 0 G).mulVec fun j => PowerSeries.coeff 1 (V j)) +
        (coeffMat 1 G).mulVec fun j => PowerSeries.coeff 0 (V j) := by
  rw [coeff_mulVec]
  simp [Finset.Nat.antidiagonal_succ]

theorem coeff_two_mulVec (G : Matrix ι ι K⟦X⟧) (V : ι → K⟦X⟧) :
    (fun j => PowerSeries.coeff 2 (G.mulVec V j)) =
      ((coeffMat 0 G).mulVec fun j => PowerSeries.coeff 2 (V j)) +
        ((coeffMat 1 G).mulVec fun j => PowerSeries.coeff 1 (V j)) +
        (coeffMat 2 G).mulVec fun j => PowerSeries.coeff 0 (V j) := by
  rw [coeff_mulVec]
  simp [Finset.Nat.antidiagonal_succ, add_assoc]

/-- The lift `v₀ + x v₁ + x² v₂` of three constant vectors. -/
noncomputable def lift3 (v₀ v₁ v₂ : ι → K) : ι → K⟦X⟧ := fun j =>
  PowerSeries.C (v₀ j) + PowerSeries.X * PowerSeries.C (v₁ j) +
    PowerSeries.X ^ 2 * PowerSeries.C (v₂ j)

theorem lift3_coeff_zero (v₀ v₁ v₂ : ι → K) :
    (fun j => PowerSeries.coeff 0 (lift3 v₀ v₁ v₂ j)) = v₀ := by
  funext j
  simp [lift3]

theorem lift3_coeff_one (v₀ v₁ v₂ : ι → K) :
    (fun j => PowerSeries.coeff 1 (lift3 v₀ v₁ v₂ j)) = v₁ := by
  funext j
  simp only [lift3, map_add, PowerSeries.coeff_C]
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * PowerSeries.C (v₁ j)) = v₁ j := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]; simp
  have h2 : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * PowerSeries.C (v₂ j)) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul']; simp
  rw [h1, h2]; simp

theorem lift3_coeff_two (v₀ v₁ v₂ : ι → K) :
    (fun j => PowerSeries.coeff 2 (lift3 v₀ v₁ v₂ j)) = v₂ := by
  funext j
  simp only [lift3, map_add, PowerSeries.coeff_C]
  have h1 : PowerSeries.coeff 2 (PowerSeries.X * PowerSeries.C (v₁ j)) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, PowerSeries.coeff_succ_X_mul]; simp
  have h2 : PowerSeries.coeff 2 (PowerSeries.X ^ 2 * PowerSeries.C (v₂ j)) = v₂ j := by
    rw [PowerSeries.coeff_X_pow_mul']; simp
  rw [h1, h2]; simp

theorem lift3_constantCoeff (v₀ v₁ v₂ : ι → K) (j : ι) :
    PowerSeries.constantCoeff (lift3 v₀ v₁ v₂ j) = v₀ j := by
  have := congrFun (lift3_coeff_zero v₀ v₁ v₂) j
  rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this

/-- If the pole order `p` of `G⁻¹` is positive, the leading coefficient matrix of
`x^p G(x)⁻¹` is nonzero. -/
theorem coeffMat_zero_scaledInv_ne_zero (G : Matrix ι ι K⟦X⟧) (hp : 1 ≤ poleOrderInv G) :
    coeffMat 0 (scaledInv G (poleOrderInv G)) ≠ 0 := by
  have hne : (Finset.univ : Finset (ι × ι)).Nonempty := by
    by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty] at hem
    rw [poleOrderInv_eq, hem, Finset.sup_empty] at hp
    exact absurd hp (by simp)
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup _ hne (entryPole G)
  rw [← poleOrderInv_eq] at hq
  intro h0
  have hentry := congrFun (congrFun h0 q.1) q.2
  rw [coeffMat_scaledInv] at hentry
  simp only [invCoeff, Matrix.of_apply, Matrix.zero_apply] at hentry
  set x := invLaurent G q.1 q.2 with hx
  have hpole : (-x.order).toNat = poleOrderInv G := hq.symm
  have hord : x.order = -(poleOrderInv G : ℤ) := by
    have : 0 < (-x.order).toNat := by omega
    have h2 : ((-x.order).toNat : ℤ) = -x.order := Int.toNat_of_nonneg (by
      by_contra hneg
      push Not at hneg
      rw [Int.toNat_of_nonpos hneg.le] at this
      exact absurd this (by simp))
    rw [hpole] at h2
    linarith
  have hxne : x ≠ 0 := by
    intro hx0
    rw [hx0, HahnSeries.order_zero] at hord
    have : (poleOrderInv G : ℤ) = 0 := by linarith
    have : poleOrderInv G = 0 := by exact_mod_cast this
    omega
  have hc : x.coeff x.order ≠ 0 := fun h => hxne (HahnSeries.coeff_order_eq_zero.mp h)
  rw [hord] at hc
  apply hc
  simpa using hentry

/-- A matrix all of whose products with vectors vanish is zero. -/
theorem matrix_eq_zero_of_mulVec {A : Matrix ι ι K} (h : ∀ w : ι → K, A.mulVec w = 0) : A = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

end Virasoro
