import Virasoro.Proofs.Ising3Mat
import Virasoro.Proofs.IsingAux

/-!
# The level-two Shapovalov matrix at `c = 1/2`

In the ordered basis `(L_{-2}, L_{-1}^2)`, `det G_2(1/2,Δ) = Δ (2Δ-1) (16Δ-1)`; its roots
`Δ = 1/2` and `Δ = 1/16` are simple, and `Δ = 1/16` is a simple root of `det G_3(1/2,Δ)`.
-/

namespace Virasoro

open Polynomial Module

variable (K : Type) [Field K] [CharZero K]

/-- The partitions of `2` in the order `(2), (1,1)`. -/
noncomputable def e2 : Nat.Partition 2 ≃ Fin 2 := isEnum_two.equiv

theorem e2_symm_word (i : Fin 2) : (e2.symm i).word = ![[2], [1, 1]] i := by
  fin_cases i <;> exact isEnum_two.word_symm _

/-- `G_2(1/2, x)` in the ordered basis `(L_{-2}, L_{-1}^2)`. -/
theorem gram2 (x : K) : (gram (1 / 2 : K) x 2).submatrix e2.symm e2.symm =
    !![4 * x + 1 / 4, 6 * x; 6 * x, 8 * x ^ 2 + 4 * x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, e2_symm_word, gramWord, actSt, actWord, vac, centralTerm] <;> ring

theorem gram2_det (x : K) :
    (gram (1 / 2 : K) x 2).det = x * (2 * x - 1) * (16 * x - 1) := by
  rw [← Matrix.det_submatrix_equiv_self e2.symm, gram2, Matrix.det_fin_two_of]
  ring

theorem gramPoly2_det : (gramPoly (1 / 2 : K) 2).det = X * (2 * X - 1) * (16 * X - 1) := by
  refine Polynomial.funext fun x => ?_
  rw [gramPoly_det_eval, gram2_det]
  simp

theorem sixteen_mul_C : (16 : K[X]) * C (1 / 16) = 1 := by
  rw [← map_ofNat C 16, ← C_mul]
  norm_num

theorem gramPoly2_rootMultiplicity_half :
    (gramPoly (1 / 2 : K) 2).det.rootMultiplicity (1 / 2) = 1 := by
  refine rootMultiplicity_of_factor (q := 2 * X * (16 * X - 1)) ?_ ?_
  · rw [gramPoly2_det]
    have e : (2 * X - 1 : K[X]) = 2 * (X - C (1 / 2)) := by linear_combination two_mul_C_half K
    rw [e]
    ring
  · simp only [eval_mul, eval_sub, eval_ofNat, eval_X, eval_one]
    norm_num

theorem gramPoly2_rootMultiplicity_sixteenth :
    (gramPoly (1 / 2 : K) 2).det.rootMultiplicity (1 / 16) = 1 := by
  refine rootMultiplicity_of_factor (q := 16 * X * (2 * X - 1)) ?_ ?_
  · rw [gramPoly2_det]
    have e : (16 * X - 1 : K[X]) = 16 * (X - C (1 / 16)) := by
      linear_combination sixteen_mul_C K
    rw [e]
    ring
  · simp only [eval_mul, eval_sub, eval_ofNat, eval_X, eval_one]
    norm_num

theorem gramPoly3_rootMultiplicity_sixteenth :
    (gramPoly (1 / 2 : K) 3).det.rootMultiplicity (1 / 16) = 1 := by
  refine rootMultiplicity_of_factor (q := 192 * X ^ 2 * (2 * X - 1) ^ 2 * (3 * X - 5)) ?_ ?_
  · rw [gramPoly3_det]
    have e : (16 * X - 1 : K[X]) = 16 * (X - C (1 / 16)) := by
      linear_combination sixteen_mul_C K
    rw [e]
    ring
  · simp only [eval_mul, eval_sub, eval_ofNat, eval_X, eval_one, eval_pow]
    norm_num

end Virasoro
