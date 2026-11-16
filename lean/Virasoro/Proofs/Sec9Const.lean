import Virasoro.Proofs.Sec8Const
import Virasoro.Statements.Sec9

/-!
# Lemma 9.3: the level-ten constants at `b₀ = 2i/√3`
-/

namespace Virasoro

open Polynomial

theorem genA_12 : genA 1 2 b0 = -4 / 7 := by
  rw [genA_b0, show (genAIndex 1 2).card = 6 from by decide,
    show b0⁻¹ ^ 6 = (b0⁻¹ ^ 2) ^ 3 from by ring, b0_inv_sq, genAIndex, Finset.prod_filter,
    Finset.prod_product,
    show Finset.Icc (1 - ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {0, 1} from by decide,
    show Finset.Icc (1 - ((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-1, 0, 1, 2} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genA_22 : genA 2 2 b0 = 648 / 13475 := by
  rw [genA_b0, show (genAIndex 2 2).card = 14 from by decide,
    show b0⁻¹ ^ 14 = (b0⁻¹ ^ 2) ^ 7 from by ring, b0_inv_sq, genAIndex, Finset.prod_filter,
    Finset.prod_product,
    show Finset.Icc (1 - ((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-1, 0, 1, 2} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genA_42 : genA 4 2 b0 = 48 / 32035128125 := by
  rw [genA_b0, show (genAIndex 4 2).card = 30 from by decide,
    show b0⁻¹ ^ 30 = (b0⁻¹ ^ 2) ^ 15 from by ring, b0_inv_sq, genAIndex, Finset.prod_filter,
    Finset.prod_product,
    show Finset.Icc (1 - ((4 : ℕ) : ℤ)) ((4 : ℕ) : ℤ) = {-3, -2, -1, 0, 1, 2, 3, 4}
      from by decide,
    show Finset.Icc (1 - ((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-1, 0, 1, 2} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genA_16 : genA 1 6 b0 = -8 / 320945625 := by
  rw [genA_b0, show (genAIndex 1 6).card = 22 from by decide,
    show b0⁻¹ ^ 22 = (b0⁻¹ ^ 2) ^ 11 from by ring, b0_inv_sq, genAIndex, Finset.prod_filter,
    Finset.prod_product,
    show Finset.Icc (1 - ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {0, 1} from by decide,
    show Finset.Icc (1 - ((6 : ℕ) : ℤ)) ((6 : ℕ) : ℤ)
      = {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genP_12 (d : ℂ) : genP 1 2 b0 d = P2.eval d := by
  rw [genP_b0, show oddsBelow 2 = {1, 3} from by decide, show oddsBelow 1 = {1} from by decide]
  simp [Finset.prod_insert, P2]
  ring

theorem genP_22 (d : ℂ) : genP 2 2 b0 d = P4.eval d := by
  rw [genP_b0, show oddsBelow 2 = {1, 3} from by decide]
  simp [Finset.prod_insert, P4]
  ring

theorem genP_42 (d : ℂ) : genP 4 2 b0 d = P42.eval d := by
  rw [genP_b0, show oddsBelow 4 = {1, 3, 5, 7} from by decide,
    show oddsBelow 2 = {1, 3} from by decide]
  simp [Finset.prod_insert, P42]
  ring

theorem genP_16 (d : ℂ) : genP 1 6 b0 d = P16.eval d := by
  rw [genP_b0, show oddsBelow 6 = {1, 3, 5, 7, 9, 11} from by decide,
    show oddsBelow 1 = {1} from by decide]
  simp [Finset.prod_insert, P16]
  ring

/-- The level-ten constants at `b₀`.

Paper label: lem:level-ten-constants -/
theorem lem_level_ten_constants : Stmt_lem_level_ten_constants := by
  have hb := b0_ne_zero
  refine ⟨⟨genA_12, genA_22, genA_42, genA_16⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun d => ⟨genP_12 d, genP_22 d, genP_42 d, genP_16 d⟩, ?_⟩
  · rw [hdot0_scaled]
    norm_num
  · rw [hdot0_scaled]
    norm_num
  · rw [hdot0_scaled]
    norm_num
  · rw [hdot0_scaled]
    norm_num
  · rw [hdot0_eq, hdot0_eq, hdot0_eq]
    field_simp
    norm_num
  · rw [hdot0_eq, hdot0_eq, hdot0_eq]
    field_simp
    norm_num
  · rw [genA_12, genA_42]
    norm_num
  · rw [genA_22, genA_16]
    norm_num
  · refine Polynomial.funext fun d => ?_
    simp only [P2, P4, P42, P16, eval_mul, eval_sub, eval_C, eval_X, eval_ofNat, eval_one]
    ring

example : Stmt_lem_level_ten_constants := lem_level_ten_constants

end Virasoro
