import Virasoro.Proofs.Ising4Forms

/-!
# The first spin-module collision: the level-four Shapovalov matrix

In the ordered basis `(L_{-4}, L_{-3}L_{-1}, L_{-2}^2, L_{-2}L_{-1}^2, L_{-1}^4)`,
`det G_4(1/2,Δ) = 12 Δ³ (2Δ-7) (2Δ-1)³ (3Δ-5) (16Δ-21) (16Δ-1)³`.  At `Δ = 1/16` the upper-left
`2 × 2` minor is invertible and three independent vectors lie in the kernel, so the rank is two
and the nullity three; the determinant has order three there.
-/

namespace Virasoro

open Polynomial Module

set_option maxRecDepth 20000

variable (K : Type) [Field K] [CharZero K]

/-- The partitions of `4` in the order `(4), (3,1), (2,2), (2,1,1), (1,1,1,1)`. -/
noncomputable def e4 : Nat.Partition 4 ≃ Fin 5 := isEnum_four.equiv

theorem e4_symm_word (i : Fin 5) :
    (e4.symm i).word = ![[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]] i := by
  fin_cases i <;> exact isEnum_four.word_symm _

omit [CharZero K] in
theorem mulVec_e4 (M : Matrix (Nat.Partition 4) (Nat.Partition 4) K) (v : Nat.Partition 4 → K)
    (i : Fin 5) :
    (M.mulVec v) (e4.symm i) = ∑ j : Fin 5, M (e4.symm i) (e4.symm j) * v (e4.symm j) := by
  rw [Matrix.mulVec, dotProduct, ← Equiv.sum_comp e4.symm]

/-- `G_4(1/2, x)` in the ordered basis. -/
noncomputable def G4 (x : K) : Matrix (Fin 5) (Fin 5) K :=
  !![8 * x + 5 / 2, 14 * x, 24 * x + 3 / 2, 36 * x, 120 * x;
     14 * x, 12 * x ^ 2 + 14 * x, 30 * x, 40 * x ^ 2 + 20 * x, 192 * x ^ 2 + 48 * x;
     24 * x + 3 / 2, 30 * x, 32 * x ^ 2 + 36 * x + 17 / 8, 48 * x ^ 2 + 51 * x,
       216 * x ^ 2 + 144 * x;
     36 * x, 40 * x ^ 2 + 20 * x, 48 * x ^ 2 + 51 * x, 32 * x ^ 3 + 118 * x ^ 2 + 33 * x,
       288 * x ^ 3 + 336 * x ^ 2 + 96 * x;
     120 * x, 192 * x ^ 2 + 48 * x, 216 * x ^ 2 + 144 * x,
       288 * x ^ 3 + 336 * x ^ 2 + 96 * x,
       384 * x ^ 4 + 1152 * x ^ 3 + 1056 * x ^ 2 + 288 * x]

theorem gram4 (x : K) : (gram (1 / 2 : K) x 4).submatrix e4.symm e4.symm = G4 K x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G4, gram, e4_symm_word, gramWord, actSt, actWord, vac, centralTerm] <;> ring

theorem gram4_entry (x : K) (i j : Fin 5) :
    gram (1 / 2 : K) x 4 (e4.symm i) (e4.symm j) = G4 K x i j := by
  have h := congrFun (congrFun (gram4 K x) i) j
  rwa [Matrix.submatrix_apply] at h

theorem gram4_det (x : K) : (gram (1 / 2 : K) x 4).det =
    12 * x ^ 3 * (2 * x - 7) * (2 * x - 1) ^ 3 * (3 * x - 5) * (16 * x - 21)
      * (16 * x - 1) ^ 3 := by
  rw [← Matrix.det_submatrix_equiv_self e4.symm, gram4, G4]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `det G_4(1/2,Δ) = 12 Δ³ (2Δ-7) (2Δ-1)³ (3Δ-5) (16Δ-21) (16Δ-1)³`. -/
theorem gramPoly4_det : (gramPoly (1 / 2 : K) 4).det =
    12 * X ^ 3 * (2 * X - 7) * (2 * X - 1) ^ 3 * (3 * X - 5) * (16 * X - 21)
      * (16 * X - 1) ^ 3 := by
  refine Polynomial.funext fun x => ?_
  rw [gramPoly_det_eval, gram4_det]
  simp

theorem gramPoly4_rootMultiplicity :
    (gramPoly (1 / 2 : K) 4).det.rootMultiplicity (1 / 16) = 3 := by
  refine rootMultiplicity_of_factor
    (q := 49152 * X ^ 3 * (2 * X - 7) * (2 * X - 1) ^ 3 * (3 * X - 5) * (16 * X - 21)) ?_ ?_
  · rw [gramPoly4_det]
    have e : (16 * X - 1 : K[X]) = 16 * (X - C (1 / 16)) := by
      linear_combination sixteen_mul_C K
    rw [e]
    ring
  · simp only [eval_mul, eval_sub, eval_ofNat, eval_X, eval_one, eval_pow]
    norm_num

omit [CharZero K] in
theorem coords_L2chi2 (i : Fin 5) :
    St.coords 4 (L2chi2K K) (e4.symm i) = ![0, 0, -3 / 4, 1, 0] i := by
  fin_cases i <;> simp [St.coords, L2chi2K, e4_symm_word]

omit [CharZero K] in
theorem coords_L11chi2 (i : Fin 5) :
    St.coords 4 (L11chi2K K) (e4.symm i) = ![-3 / 2, -3 / 2, 0, -3 / 4, 1] i := by
  fin_cases i <;> simp [St.coords, L11chi2K, e4_symm_word]

omit [CharZero K] in
theorem coords_chi4 (i : Fin 5) :
    St.coords 4 (chi4K K) (e4.symm i) = ![-1 / 4, 11 / 6, 49 / 144, -25 / 6, 1] i := by
  fin_cases i <;> simp [St.coords, chi4K, e4_symm_word]

end Virasoro
