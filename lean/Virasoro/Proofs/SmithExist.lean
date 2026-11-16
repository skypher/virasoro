import Virasoro.Smith
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Existence of the local Smith form over `K⟦X⟧`

Since `K⟦X⟧` is a discrete valuation ring, every square matrix `G` with nonzero determinant
satisfies `U G V = diag(x^{e_i})` for unimodular `U`, `V`.  The proof uses the Smith normal form
of a full-rank submodule of a free module over a principal ideal domain.
-/

namespace Virasoro

open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_isSmith {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) : ∃ s : Multiset ℕ, IsSmith G s := by
  classical
  have hinj : Function.Injective G.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hdet
  have hrank : finrank K⟦X⟧ (LinearMap.range G.mulVecLin) = finrank K⟦X⟧ (ι → K⟦X⟧) :=
    LinearMap.finrank_range_of_inj hinj
  obtain ⟨b', a, ab', hab⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun K⟦X⟧ ι) hrank
  let eqv : (ι → K⟦X⟧) ≃ₗ[K⟦X⟧] LinearMap.range G.mulVecLin := LinearEquiv.ofInjective _ hinj
  let c : Basis ι K⟦X⟧ (ι → K⟦X⟧) := ab'.map eqv.symm
  have hc : ∀ i, G.mulVec (c i) = a i • b' i := by
    intro i
    have h1 : (eqv (c i) : ι → K⟦X⟧) = G.mulVec (c i) := rfl
    have h2 : eqv (c i) = ab' i := by
      simp [c]
    rw [← h1, h2, hab]
  let P : Matrix ι ι K⟦X⟧ := (Pi.basisFun K⟦X⟧ ι).toMatrix b'
  let Q : Matrix ι ι K⟦X⟧ := (Pi.basisFun K⟦X⟧ ι).toMatrix c
  let U : Matrix ι ι K⟦X⟧ := b'.toMatrix (Pi.basisFun K⟦X⟧ ι)
  have hGQ : G * Q = P * Matrix.diagonal a := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (hc j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Q, P, Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this, mul_comm]
  have hUP : U * P = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hUGQ : U * G * Q = Matrix.diagonal a := by
    rw [Matrix.mul_assoc, hGQ, ← Matrix.mul_assoc, hUP, Matrix.one_mul]
  have hUdet : IsUnit U.det := Matrix.isUnit_det_of_right_inverse hUP
  have hQdet : IsUnit Q.det :=
    Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun K⟦X⟧ ι) c)
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := congrArg Matrix.det hUGQ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ i) hi] at h
    exact (mul_ne_zero (mul_ne_zero hUdet.ne_zero hdet) hQdet.ne_zero) h
  have hu : ∀ i, IsUnit (divXPowOrder (a i)) := fun i => isUnit_divided_by_X_pow_order (ha i)
  have hu0 : ∀ i, PowerSeries.constantCoeff (divXPowOrder (a i)) ≠ 0 := fun i =>
    (PowerSeries.isUnit_iff_constantCoeff.mp (hu i)).ne_zero
  let D : Matrix ι ι K⟦X⟧ := Matrix.diagonal fun i => (divXPowOrder (a i))⁻¹
  refine ⟨Finset.univ.val.map fun i => (a i).order.toNat, fun i => (a i).order.toNat,
    U, Q * D, hUdet, ?_, ?_, rfl⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    refine hQdet.mul ?_
    rw [IsUnit.prod_univ_iff]
    intro i
    exact IsUnit.of_mul_eq_one _ (PowerSeries.inv_mul_cancel _ (hu0 i))
  · rw [← Matrix.mul_assoc, hUGQ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    calc a i * (divXPowOrder (a i))⁻¹
        = (X ^ (a i).order.toNat * divXPowOrder (a i)) * (divXPowOrder (a i))⁻¹ := by
          rw [X_pow_order_mul_divXPowOrder]
      _ = X ^ (a i).order.toNat := by
          rw [mul_assoc, PowerSeries.mul_inv_cancel _ (hu0 i), mul_one]

end Virasoro
