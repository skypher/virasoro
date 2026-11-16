import Virasoro.Smith
import Virasoro.Proofs.LaurentLemmas
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Power-series matrices and their Laurent inverses

Infrastructure for Section 5: coefficient matrices of products, the inverse over Laurent series,
its pole order, and the scaled inverse `x^p G(x)⁻¹` as a power-series matrix.
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A power-series matrix regarded as a matrix of Laurent series. -/
noncomputable abbrev toL (G : Matrix ι ι K⟦X⟧) : Matrix ι ι K⸨X⸩ :=
  G.map (HahnSeries.ofPowerSeries ℤ K)

theorem toL_mul (A B : Matrix ι ι K⟦X⟧) : toL (A * B) = toL A * toL B :=
  Matrix.map_mul (f := HahnSeries.ofPowerSeries ℤ K)

theorem toL_one : toL (1 : Matrix ι ι K⟦X⟧) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [toL, Matrix.one_apply, h]

theorem toL_injective : Function.Injective (toL : Matrix ι ι K⟦X⟧ → Matrix ι ι K⸨X⸩) := by
  intro A B h
  ext i j : 1
  have := congrFun (congrFun h i) j
  exact HahnSeries.ofPowerSeries_injective this

theorem det_toL (G : Matrix ι ι K⟦X⟧) : (toL G).det = HahnSeries.ofPowerSeries ℤ K G.det :=
  (RingHom.map_det (HahnSeries.ofPowerSeries ℤ K) G).symm

theorem toL_mul_inv {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) : toL G * invLaurent G = 1 := by
  have hu : IsUnit (toL G).det := by
    rw [det_toL, isUnit_iff_ne_zero]
    intro h
    exact hdet (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  exact Matrix.mul_nonsing_inv _ hu

theorem inv_mul_toL {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) : invLaurent G * toL G = 1 := by
  have hu : IsUnit (toL G).det := by
    rw [det_toL, isUnit_iff_ne_zero]
    intro h
    exact hdet (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  exact Matrix.nonsing_inv_mul _ hu

/-- All entries have valuation at least `n`. -/
def MatOrdGE (M : Matrix ι ι K⸨X⸩) (n : ℤ) : Prop := ∀ i j, OrdGE (M i j) n

theorem MatOrdGE.mul {A B : Matrix ι ι K⸨X⸩} {a b : ℤ} (hA : MatOrdGE A a) (hB : MatOrdGE B b) :
    MatOrdGE (A * B) (a + b) := by
  intro i j
  rw [Matrix.mul_apply]
  exact OrdGE.sum fun l _ => (hA i l).mul (hB l j)

theorem MatOrdGE.mono {A : Matrix ι ι K⸨X⸩} {a b : ℤ} (hA : MatOrdGE A a) (h : b ≤ a) :
    MatOrdGE A b := fun i j => (hA i j).mono h

theorem ordGE_ofPowerSeries (f : K⟦X⟧) : OrdGE (HahnSeries.ofPowerSeries ℤ K f) 0 :=
  ordGE_iff.2 fun m hm => by
    have := PowerSeries.coeff_coe (f := f) m
    rw [if_pos hm] at this
    exact this

theorem matOrdGE_toL (G : Matrix ι ι K⟦X⟧) : MatOrdGE (toL G) 0 := fun i j =>
  ordGE_ofPowerSeries (G i j)

/-- The entrywise pole orders whose supremum is `poleOrderInv`. -/
noncomputable def entryPole (G : Matrix ι ι K⟦X⟧) (p : ι × ι) : ℕ :=
  (-(invLaurent G p.1 p.2).order).toNat

theorem poleOrderInv_eq (G : Matrix ι ι K⟦X⟧) :
    poleOrderInv G = Finset.univ.sup (entryPole G) := rfl

theorem matOrdGE_inv (G : Matrix ι ι K⟦X⟧) : MatOrdGE (invLaurent G) (-(poleOrderInv G : ℤ)) := by
  intro i j
  refine (ordGE_order _).mono ?_
  have h1 : entryPole G (i, j) ≤ poleOrderInv G := by
    rw [poleOrderInv_eq]
    exact Finset.le_sup (Finset.mem_univ _)
  have h2 := Int.self_le_toNat (-(invLaurent G i j).order)
  have h3 : ((-(invLaurent G i j).order).toNat : ℤ) ≤ poleOrderInv G := by
    have : entryPole G (i, j) = (-(invLaurent G i j).order).toNat := rfl
    rw [← this]
    exact_mod_cast h1
  linarith

theorem poleOrderInv_le {G : Matrix ι ι K⟦X⟧} {p : ℕ} (h : MatOrdGE (invLaurent G) (-(p : ℤ))) :
    poleOrderInv G ≤ p := by
  rw [poleOrderInv_eq]
  refine Finset.sup_le fun q _ => ?_
  unfold entryPole
  by_cases h0 : invLaurent G q.1 q.2 = 0
  · rw [h0]; simp
  · have hq := h q.1 q.2
    unfold OrdGE at hq
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at hq
    have : -(p : ℤ) ≤ (invLaurent G q.1 q.2).order := by exact_mod_cast hq
    omega

/-- If some entry of `G⁻¹` has a nonzero coefficient at `t^{-p}`, the pole order is at least
`p`. -/
theorem le_poleOrderInv {G : Matrix ι ι K⟦X⟧} {p : ℕ} {i j : ι}
    (h : (invLaurent G i j).coeff (-(p : ℤ)) ≠ 0) : p ≤ poleOrderInv G := by
  by_contra hlt
  push Not at hlt
  have := (matOrdGE_inv G i j).coeff_eq_zero (m := -(p : ℤ)) (by
    have : (poleOrderInv G : ℤ) < p := by exact_mod_cast hlt
    linarith)
  exact h this

/-- The power-series matrix `x^p G(x)⁻¹`, for `p` at least the pole order. -/
noncomputable def scaledInv (G : Matrix ι ι K⟦X⟧) (p : ℕ) : Matrix ι ι K⟦X⟧ :=
  Matrix.of fun i j => PowerSeries.mk fun l => (invLaurent G i j).coeff ((l : ℤ) - p)

theorem coeffMat_scaledInv (G : Matrix ι ι K⟦X⟧) (p t : ℕ) :
    coeffMat t (scaledInv G p) = invCoeff G ((t : ℤ) - p) := by
  ext i j
  simp [coeffMat, scaledInv, invCoeff]

theorem toL_scaledInv {G : Matrix ι ι K⟦X⟧} {p : ℕ} (hp : MatOrdGE (invLaurent G) (-(p : ℤ))) :
    toL (scaledInv G p) = (HahnSeries.single (p : ℤ) (1 : K) : K⸨X⸩) • invLaurent G := by
  ext i j : 1
  ext m
  simp only [toL, Matrix.map_apply, scaledInv, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [PowerSeries.coeff_coe]
  have hsm : ((HahnSeries.single (p : ℤ) (1 : K) : K⸨X⸩) * invLaurent G i j).coeff m =
      (invLaurent G i j).coeff (m - p) := by
    have := HahnSeries.coeff_single_mul_add (r := (1 : K)) (x := invLaurent G i j)
      (a := m - p) (b := (p : ℤ))
    rw [sub_add_cancel, one_mul] at this
    exact this
  rw [hsm]
  split_ifs with hm
  · exact ((hp i j).coeff_eq_zero (by linarith)).symm
  · rw [PowerSeries.coeff_mk]
    congr 1
    have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (by linarith)
    rw [this]

theorem mul_scaledInv {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) {p : ℕ}
    (hp : MatOrdGE (invLaurent G) (-(p : ℤ))) :
    G * scaledInv G p = (PowerSeries.X : K⟦X⟧) ^ p • (1 : Matrix ι ι K⟦X⟧) := by
  apply toL_injective
  rw [toL_mul, toL_scaledInv hp, Matrix.mul_smul, toL_mul_inv hdet]
  ext i j
  by_cases h : i = j <;>
    simp [toL, Matrix.one_apply, h, HahnSeries.ofPowerSeries_X_pow]

theorem scaledInv_mul {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) {p : ℕ}
    (hp : MatOrdGE (invLaurent G) (-(p : ℤ))) :
    scaledInv G p * G = (PowerSeries.X : K⟦X⟧) ^ p • (1 : Matrix ι ι K⟦X⟧) := by
  apply toL_injective
  rw [toL_mul, toL_scaledInv hp, Matrix.smul_mul, inv_mul_toL hdet]
  ext i j
  by_cases h : i = j <;>
    simp [toL, Matrix.one_apply, h, HahnSeries.ofPowerSeries_X_pow]

/-! ### Coefficient matrices of a product -/

theorem coeffMat_mul (A B : Matrix ι ι K⟦X⟧) (n : ℕ) :
    coeffMat n (A * B) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeffMat p.1 A * coeffMat p.2 B := by
  ext i j
  simp only [coeffMat, Matrix.map_apply, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul,
    Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem coeffMat_zero_mul (A B : Matrix ι ι K⟦X⟧) :
    coeffMat 0 (A * B) = coeffMat 0 A * coeffMat 0 B := by
  rw [coeffMat_mul]; simp

theorem coeffMat_one_mul (A B : Matrix ι ι K⟦X⟧) :
    coeffMat 1 (A * B) = coeffMat 0 A * coeffMat 1 B + coeffMat 1 A * coeffMat 0 B := by
  rw [coeffMat_mul]
  simp [Finset.Nat.antidiagonal_succ]

theorem coeffMat_two_mul (A B : Matrix ι ι K⟦X⟧) :
    coeffMat 2 (A * B) =
      coeffMat 0 A * coeffMat 2 B + coeffMat 1 A * coeffMat 1 B + coeffMat 2 A * coeffMat 0 B := by
  rw [coeffMat_mul]
  simp [Finset.Nat.antidiagonal_succ, add_assoc]

theorem coeffMat_X_pow_smul_one (p t : ℕ) :
    coeffMat t ((PowerSeries.X : K⟦X⟧) ^ p • (1 : Matrix ι ι K⟦X⟧)) =
      if t = p then (1 : Matrix ι ι K) else 0 := by
  ext i j
  simp only [coeffMat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · simp only [hij, if_true, mul_one, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  · simp only [hij, if_false, mul_zero, map_zero]
    split_ifs <;> simp [hij]

theorem coeffMat_isSymm {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (n : ℕ) : (coeffMat n G).IsSymm := by
  ext i j
  simp only [coeffMat, Matrix.transpose_apply, Matrix.map_apply]
  rw [← hG.apply i j]

/-- For a symmetric matrix, `u · (A v) = (A u) · v`. -/
theorem dot_mulVec_symm {A : Matrix ι ι K} (hA : A.IsSymm) (u v : ι → K) :
    u ⬝ᵥ A.mulVec v = A.mulVec u ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]

end Virasoro
