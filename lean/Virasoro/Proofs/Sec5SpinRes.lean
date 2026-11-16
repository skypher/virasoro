import Virasoro.Proofs.Ising4Ker
import Virasoro.Proofs.Sec5FirstRes

/-!
# Residues at the first spin-module collision

`Res_{Δ=1/16} F_2 = -4/7 P_2`, `Res_{Δ=1/16} F_3 = -4/7 P_2 F_1(1/2,33/16,d)` from the singular
vector `χ₂`, and `Res_{Δ=1/16} F_4` from the transverse residue in the basis
`(L_{-2}χ₂, L_{-1}²χ₂, χ₄)` with Lemma 5.9.
-/

namespace Virasoro

open Polynomial Module

variable (K : Type) [Field K] [CharZero K]

theorem card_partition_one : Fintype.card (Nat.Partition 1) = 1 := by
  rw [Fintype.card_congr e1, Fintype.card_fin]

theorem chi2_singular_coords :
    Verma.IsSingular (Verma.pbwCoord (c := (1 / 2 : K)) (h := (1 / 16 : K)) 2
      (St.coords 2 (chi2K K))) 2 := by
  rw [← toVerma_eq_pbwCoord _ (isLevel_chi2 K)]
  exact chi2_singular K

theorem crossScalar_chi2_ne : crossScalar (1 / 2 : K) (1 / 16) (St.coords 2 (chi2K K)) ≠ 0 := by
  rw [crossScalar_chi2]
  norm_num

/-- `Res_{Δ=1/16} F_2(1/2,Δ,d) = -4/7 P_2(d)`. -/
theorem res_F2_sixteenth (d : K) :
    poleOrderInv (gramLocal (1 / 2 : K) (1 / 16) 2) ≤ 1 ∧
      ppCoeff (Frat (1 / 2 : K) d 2) (1 / 16) 1 = -(4 / 7) * (P2K K).eval d := by
  have hg : (gram (1 / 2 : K) (1 / 16 + ((2 : ℕ) : K)) 0).det ≠ 0 := by
    rw [gram_zero, Matrix.det_one]
    exact one_ne_zero
  have hord : (gramLocal (1 / 2 : K) (1 / 16) (2 + 0)).det.order
      = ((Fintype.card (Nat.Partition 0) : ℕ) : ℕ∞) := by
    rw [gramLocal_det_order, card_partition_zero]
    exact congrArg _ (gramPoly2_rootMultiplicity_sixteenth K)
  have h1 := residue_inverse (1 / 2 : K) (1 / 16) 2 0 (St.coords 2 (chi2K K)) (by norm_num)
    (chi2_singular_coords K) (crossScalar_chi2_ne K) hg hord
  have h2 := residue_Frat (1 / 2 : K) (1 / 16) 2 0 (St.coords 2 (chi2K K)) d (by norm_num)
    (chi2_singular_coords K) (crossScalar_chi2_ne K) hg hord
  refine ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [Fval_zero, torus_chi2, crossScalar_chi2] at h3
  have h4 : ppCoeff (Frat (1 / 2 : K) d 2) (1 / 16) 1
      = ppCoeff (Frat (1 / 2 : K) d (2 + 0)) (1 / 16) 1 := rfl
  rw [h4, h3]
  ring

/-- `Res_{Δ=1/16} F_3(1/2,Δ,d) = -4/7 P_2(d) F_1(1/2,33/16,d)`. -/
theorem res_F3_sixteenth (d : K) :
    poleOrderInv (gramLocal (1 / 2 : K) (1 / 16) 3) ≤ 1 ∧
      ppCoeff (Frat (1 / 2 : K) d 3) (1 / 16) 1
        = -(4 / 7) * (P2K K).eval d * Fval (1 / 2 : K) d (33 / 16) 1 := by
  have hz : (1 / 16 : K) + ((2 : ℕ) : K) = 33 / 16 := by norm_num
  have hg : (gram (1 / 2 : K) (1 / 16 + ((2 : ℕ) : K)) 1).det ≠ 0 := by
    rw [gram_one_det, hz]
    norm_num
  have hord : (gramLocal (1 / 2 : K) (1 / 16) (2 + 1)).det.order
      = ((Fintype.card (Nat.Partition 1) : ℕ) : ℕ∞) := by
    rw [gramLocal_det_order, card_partition_one]
    exact congrArg _ (gramPoly3_rootMultiplicity_sixteenth K)
  have h1 := residue_inverse (1 / 2 : K) (1 / 16) 2 1 (St.coords 2 (chi2K K)) (by norm_num)
    (chi2_singular_coords K) (crossScalar_chi2_ne K) hg hord
  have h2 := residue_Frat (1 / 2 : K) (1 / 16) 2 1 (St.coords 2 (chi2K K)) d (by norm_num)
    (chi2_singular_coords K) (crossScalar_chi2_ne K) hg hord
  refine ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [torus_chi2, crossScalar_chi2, hz] at h3
  have h4 : ppCoeff (Frat (1 / 2 : K) d 3) (1 / 16) 1
      = ppCoeff (Frat (1 / 2 : K) d (2 + 1)) (1 / 16) 1 := rfl
  rw [h4, h3]
  ring

/-- `F_2(c,z,d)` through the ordered basis `(L_{-2}, L_{-1}^2)`. -/
theorem Fval_two (c d z : K) :
    Fval c d z 2 = (∑ i : Fin 2, ∑ j : Fin 2,
        ((gram c z 2).submatrix e2.symm e2.symm).adjugate i j
          * torusWord c z d (![[2], [1, 1]] i) (![[2], [1, 1]] j))
      / ((gram c z 2).submatrix e2.symm e2.symm).det := by
  unfold Fval
  rw [Matrix.det_submatrix_equiv_self, Matrix.adjugate_submatrix_equiv_self,
    ← Equiv.sum_comp e2.symm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e2.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.submatrix_apply, torus, Matrix.of_apply, e2_symm_word]

end Virasoro
