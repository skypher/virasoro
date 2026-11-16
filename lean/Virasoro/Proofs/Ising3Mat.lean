import Virasoro.Proofs.Ising3
import Virasoro.Proofs.GramDet
import Virasoro.Proofs.Family
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.VecSimp

/-!
# The earliest Ising collision: the level-three Shapovalov matrix

In the ordered basis `(L_{-3}, L_{-2}L_{-1}, L_{-1}^3)`,
`det G_3(1/2,Δ) = 12 Δ² (2Δ-1)² (3Δ-5) (16Δ-1)`; at `Δ = 1/2` the matrix has rank one, its
kernel is spanned by `L_{-1}ξ₂` and `ξ₃`, and the determinant valuation and the nullity are both
two.
-/

namespace Virasoro

open Polynomial Module

variable (K : Type) [Field K] [CharZero K]

/-- The partitions of `3` in the order `(3), (2,1), (1,1,1)`. -/
noncomputable def e3 : Nat.Partition 3 ≃ Fin 3 := isEnum_three.equiv

theorem e3_symm_word (i : Fin 3) : (e3.symm i).word = ![[3], [2, 1], [1, 1, 1]] i := by
  fin_cases i <;> exact isEnum_three.word_symm _

omit [CharZero K] in
theorem mulVec_e3 (M : Matrix (Nat.Partition 3) (Nat.Partition 3) K) (v : Nat.Partition 3 → K)
    (i : Fin 3) :
    (M.mulVec v) (e3.symm i) = ∑ j : Fin 3, M (e3.symm i) (e3.symm j) * v (e3.symm j) := by
  rw [Matrix.mulVec, dotProduct, ← Equiv.sum_comp e3.symm]

/-- `G_3(1/2, x)` in the ordered basis `(L_{-3}, L_{-2}L_{-1}, L_{-1}^3)`. -/
theorem gram3 (x : K) : (gram (1 / 2 : K) x 3).submatrix e3.symm e3.symm =
    !![6 * x + 1, 10 * x, 24 * x;
       10 * x, 8 * x ^ 2 + 17 / 2 * x, 36 * x ^ 2 + 12 * x;
       24 * x, 36 * x ^ 2 + 12 * x, 24 * x * (x + 1) * (2 * x + 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, e3_symm_word, gramWord, actSt, actWord, vac, centralTerm] <;> ring

theorem gram3_det (x : K) :
    (gram (1 / 2 : K) x 3).det = 12 * x ^ 2 * (2 * x - 1) ^ 2 * (3 * x - 5) * (16 * x - 1) := by
  rw [← Matrix.det_submatrix_equiv_self e3.symm, gram3, Matrix.det_fin_three]
  vec_simp
  ring

/-- `det G_3(1/2,Δ) = 12 Δ² (2Δ-1)² (3Δ-5) (16Δ-1)`. -/
theorem gramPoly3_det : (gramPoly (1 / 2 : K) 3).det =
    12 * X ^ 2 * (2 * X - 1) ^ 2 * (3 * X - 5) * (16 * X - 1) := by
  refine Polynomial.funext fun x => ?_
  rw [gramPoly_det_eval, gram3_det]
  simp

theorem two_mul_C_half : (2 : K[X]) * C (1 / 2) = 1 := by
  rw [← map_ofNat C 2, ← C_mul]
  norm_num

theorem gramPoly3_rootMultiplicity : (gramPoly (1 / 2 : K) 3).det.rootMultiplicity (1 / 2) = 2 := by
  have hfac : (gramPoly (1 / 2 : K) 3).det =
      (X - C (1 / 2)) ^ 2 * (48 * X ^ 2 * (3 * X - 5) * (16 * X - 1)) := by
    rw [gramPoly3_det]
    have e : (2 * X - 1 : K[X]) = 2 * (X - C (1 / 2)) := by linear_combination two_mul_C_half K
    rw [e]
    ring
  have hne : (X - C (1 / 2 : K)) ^ 2 * (48 * X ^ 2 * (3 * X - 5) * (16 * X - 1)) ≠ 0 := by
    rw [← hfac]
    exact gramPoly_det_ne_zero _ _
  have hnr : ¬ IsRoot (48 * X ^ 2 * (3 * X - 5) * (16 * X - 1) : K[X]) (1 / 2) := by
    simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_ofNat, eval_X]
    norm_num
  rw [hfac, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hnr]

omit [CharZero K] in
theorem coords_L1xi2 (i : Fin 3) : St.coords 3 (L1xi2K K) (e3.symm i) = ![-4 / 3, -4 / 3, 1] i := by
  fin_cases i <;> simp [St.coords, L1xi2K, e3_symm_word]

omit [CharZero K] in
theorem coords_xi3 (i : Fin 3) : St.coords 3 (xi3K K) (e3.symm i) = ![3 / 4, -3, 1] i := by
  fin_cases i <;> simp [St.coords, xi3K, e3_symm_word]

theorem gram3_half (i j : Fin 3) : gram (1 / 2 : K) (1 / 2) 3 (e3.symm i) (e3.symm j) =
    !![4, 5, 12; 5, 25 / 4, 15; 12, 15, 36] i j := by
  have h := congrFun (congrFun (gram3 K (1 / 2)) i) j
  rw [Matrix.submatrix_apply] at h
  rw [h]
  fin_cases i <;> fin_cases j <;> norm_num

/-- `ker G_3(1/2,1/2) = span{L_{-1}ξ₂, ξ₃}`. -/
theorem ker_gram3 : LinearMap.ker (gram (1 / 2 : K) (1 / 2) 3).mulVecLin =
    Submodule.span K {St.coords 3 (L1xi2K K), St.coords 3 (xi3K K)} := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    have h0 := congrFun hv (e3.symm 0)
    rw [mulVec_e3, Fin.sum_univ_three, gram3_half, gram3_half, gram3_half, Pi.zero_apply] at h0
    vec_simp at h0
    rw [Submodule.mem_span_pair]
    refine ⟨(3 * v (e3.symm 1) + 9 * v (e3.symm 2)) / 5,
      -(3 * v (e3.symm 1) + 4 * v (e3.symm 2)) / 5, ?_⟩
    funext Y
    obtain ⟨i, rfl⟩ := e3.symm.surjective Y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coords_L1xi2, coords_xi3]
    fin_cases i
    · vec_simp
      linear_combination (-1 / 4 : K) * h0
    · vec_simp
      ring
    · vec_simp
      ring
  · rw [Submodule.span_le]
    intro v hv
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext Y
    obtain ⟨i, rfl⟩ := e3.symm.surjective Y
    rw [mulVec_e3, Fin.sum_univ_three, gram3_half, gram3_half, gram3_half]
    rcases hv with rfl | hv
    · simp only [coords_L1xi2]
      fin_cases i <;> vec_simp <;> norm_num
    · rw [Set.mem_singleton_iff.1 hv]
      simp only [coords_xi3]
      fin_cases i <;> vec_simp <;> norm_num

theorem finrank_ker0_gram3 : finrank K (ker0 (gramLocal (1 / 2 : K) (1 / 2) 3)) = 2 := by
  have hk : ker0 (gramLocal (1 / 2 : K) (1 / 2) 3) =
      Submodule.span K (Set.range ![St.coords 3 (L1xi2K K), St.coords 3 (xi3K K)]) := by
    unfold ker0
    rw [coeffMat_zero_gramLocal, ker_gram3]
    congr 1
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton]
    exact or_comm
  have hli : LinearIndependent K ![St.coords 3 (L1xi2K K), St.coords 3 (xi3K K)] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrFun hab (e3.symm 1)
    have h2 := congrFun hab (e3.symm 2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coords_L1xi2, coords_xi3,
      Pi.zero_apply] at h1 h2
    vec_simp at h1 h2
    constructor
    · linear_combination (3 / 5 : K) * h1 + (9 / 5 : K) * h2
    · linear_combination (-3 / 5 : K) * h1 - (4 / 5 : K) * h2
  rw [hk, finrank_span_eq_card hli]
  simp

/-- The local Smith exponents of `G_3(1/2, 1/2 + x)` are `(0,1,1)`: the determinant valuation
and the nullity are both two. -/
theorem isSmith_gram3 : IsSmith (gramLocal (1 / 2 : K) (1 / 2) 3) {0, 1, 1} := by
  have h := isSmith_of_order_eq_nullity (gramLocal_det_ne_zero (1 / 2 : K) (1 / 2) 3) (k := 2)
    (by rw [gramLocal_det_order, gramPoly3_rootMultiplicity]) (finrank_ker0_gram3 K)
  have hc : Fintype.card (Nat.Partition 3) = 3 := by rw [Fintype.card_congr e3, Fintype.card_fin]
  rw [hc] at h
  exact h

end Virasoro
