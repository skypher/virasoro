import Virasoro.Proofs.Sec3
import Virasoro.Statements.Sec8
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Lemma 8.3: the level-seven constants at `b₀ = 2i/√3`

With `b₀² = -4/3` and `b₀⁻¹ = -3/4 b₀`, every factor `p b₀ + q b₀⁻¹` is `(4p - 3q)/4 · b₀`, every
fusion factor is `λ_{|4k ∓ 3l|} - d`, and `ḣ_{r,s}(b₀) = b₀ (7 - 16 r² + 9 s²)/32`.
-/

namespace Virasoro

open Polynomial

theorem b0_inv : b0⁻¹ = -(3 / 4) * b0 := by
  have h : b0 * (-(3 / 4) * b0) = 1 := by linear_combination (-(3 / 4) : ℂ) * b0_sq
  exact inv_eq_of_mul_eq_one_right h

theorem b0_inv_sq : b0⁻¹ ^ 2 = -3 / 4 := by
  rw [inv_pow, b0_sq]
  norm_num

theorem genA_b0 (r s : ℕ) : genA r s b0
    = 2⁻¹ * ((∏ pq ∈ genAIndex r s, ((4 * (pq.1 : ℂ) - 3 * (pq.2 : ℂ)) / 4)⁻¹)
        * b0⁻¹ ^ (genAIndex r s).card) := by
  unfold genA
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun pq _ => ?_
  have e : (pq.1 : ℂ) * b0 + (pq.2 : ℂ) * b0⁻¹ = (4 * (pq.1 : ℂ) - 3 * (pq.2 : ℂ)) / 4 * b0 := by
    rw [b0_inv]
    ring
  rw [e, mul_inv]

theorem genA_21 : genA 2 1 b0 = 9 / 28 := by
  rw [genA_b0, show (genAIndex 2 1).card = 6 from by decide,
    show b0⁻¹ ^ 6 = (b0⁻¹ ^ 2) ^ 3 from by ring, b0_inv_sq,
    show genAIndex 2 1 = {(-1, 0), (1, 0), (2, 0), (-1, 1), (0, 1), (1, 1)} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genA_13 : genA 1 3 b0 = -8 / 105 := by
  rw [genA_b0, show (genAIndex 1 3).card = 10 from by decide,
    show b0⁻¹ ^ 10 = (b0⁻¹ ^ 2) ^ 5 from by ring, b0_inv_sq,
    show genAIndex 1 3 = {(0, -2), (0, -1), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0),
      (1, 1), (1, 2)} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genA_15 : genA 1 5 b0 = -1 / 102375 := by
  rw [genA_b0, show (genAIndex 1 5).card = 18 from by decide,
    show b0⁻¹ ^ 18 = (b0⁻¹ ^ 2) ^ 9 from by ring, b0_inv_sq,
    show genAIndex 1 5 = {(0, -4), (0, -3), (0, -2), (0, -1), (0, 1), (0, 2), (0, 3), (0, 4),
      (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)}
      from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genA_41 : genA 4 1 b0 = 3 / 61600 := by
  rw [genA_b0, show (genAIndex 4 1).card = 14 from by decide,
    show b0⁻¹ ^ 14 = (b0⁻¹ ^ 2) ^ 7 from by ring, b0_inv_sq,
    show genAIndex 4 1 = {(-3, 0), (-2, 0), (-1, 0), (1, 0), (2, 0), (3, 0), (4, 0), (-3, 1),
      (-2, 1), (-1, 1), (0, 1), (1, 1), (2, 1), (3, 1)} from by decide]
  simp [Finset.prod_insert]
  norm_num

theorem genP_b0 (r s : ℕ) (d : ℂ) : genP r s b0 d
    = ∏ k ∈ oddsBelow r, ∏ l ∈ oddsBelow s,
        (((4 * (k : ℂ) - 3 * (l : ℂ)) ^ 2 - 1) / 48 - d)
          * (((4 * (k : ℂ) + 3 * (l : ℂ)) ^ 2 - 1) / 48 - d) := by
  unfold genP
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => ?_
  congr 1
  · unfold lamSq
    rw [b0_inv]
    linear_combination ((1 / 16 - ((k : ℂ) - 3 * (l : ℂ) / 4) ^ 2) / 4) * b0_sq
  · unfold lamSq
    rw [b0_inv]
    linear_combination ((1 / 16 - ((k : ℂ) + 3 * (l : ℂ) / 4) ^ 2) / 4) * b0_sq

theorem genP_21 (d : ℂ) : genP 2 1 b0 d = E2.eval d := by
  rw [genP_b0, show oddsBelow 2 = {1, 3} from by decide, show oddsBelow 1 = {1} from by decide]
  simp [Finset.prod_insert, E2]
  ring

theorem genP_13 (d : ℂ) : genP 1 3 b0 d = E3.eval d := by
  rw [genP_b0, show oddsBelow 3 = {1, 3, 5} from by decide, show oddsBelow 1 = {1} from by decide]
  simp [Finset.prod_insert, E3]
  ring

theorem genP_15 (d : ℂ) : genP 1 5 b0 d = P15.eval d := by
  rw [genP_b0, show oddsBelow 5 = {1, 3, 5, 7, 9} from by decide,
    show oddsBelow 1 = {1} from by decide]
  simp [Finset.prod_insert, P15]
  ring

theorem genP_41 (d : ℂ) : genP 4 1 b0 d = P41.eval d := by
  rw [genP_b0, show oddsBelow 4 = {1, 3, 5, 7} from by decide,
    show oddsBelow 1 = {1} from by decide]
  simp [Finset.prod_insert, P41]
  ring

theorem hasDerivAt_kacH (r s : ℤ) {b : ℂ} (hb : b ≠ 0) :
    HasDerivAt (fun b : ℂ => kacH r s b)
      ((2 * (b + b⁻¹) * (1 - (b ^ 2)⁻¹)
        - 2 * ((r : ℂ) * b + (s : ℂ) * b⁻¹) * ((r : ℂ) - (s : ℂ) * (b ^ 2)⁻¹)) / 4) b := by
  have h1 : HasDerivAt (fun b : ℂ => b⁻¹) (-(b ^ 2)⁻¹) b := hasDerivAt_inv hb
  have h2 := ((hasDerivAt_id b).add h1).pow 2
  have h3 := (((hasDerivAt_id b).const_mul (r : ℂ)).add (h1.const_mul (s : ℂ))).pow 2
  have h4 := (h2.sub h3).div_const 4
  refine h4.congr_deriv ?_
  simp only [id, Pi.add_apply, Nat.cast_ofNat]
  ring

theorem hdot0_eq (r s : ℤ) :
    hdot0 r s = b0 * (7 - 16 * (r : ℂ) ^ 2 + 9 * (s : ℂ) ^ 2) / 32 := by
  have h := (hasDerivAt_kacH r s b0_ne_zero).deriv
  have h2 : (b0 ^ 2)⁻¹ = -3 / 4 := by
    rw [b0_sq]
    norm_num
  rw [hdot0, h, h2, b0_inv]
  ring

theorem b0_div : b0 / (Complex.I * (Real.sqrt 3 : ℂ)) = 2 / 3 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h30 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  rw [b0, div_div, div_eq_div_iff (mul_ne_zero h30 (mul_ne_zero Complex.I_ne_zero h30))
    (by norm_num)]
  linear_combination (-2 * Complex.I) * h3

theorem hdot0_scaled (r s : ℤ) : 16 * hdot0 r s / (Complex.I * (Real.sqrt 3 : ℂ))
    = (7 - 16 * (r : ℂ) ^ 2 + 9 * (s : ℂ) ^ 2) / 3 := by
  have e : 16 * (b0 * (7 - 16 * (r : ℂ) ^ 2 + 9 * (s : ℂ) ^ 2) / 32)
        / (Complex.I * (Real.sqrt 3 : ℂ))
      = b0 / (Complex.I * (Real.sqrt 3 : ℂ)) * ((7 - 16 * (r : ℂ) ^ 2 + 9 * (s : ℂ) ^ 2) / 2) := by
    ring
  rw [hdot0_eq, e, b0_div]
  ring

/-- The level-seven constants at `b₀`.

Paper label: lem:level-seven-constants -/
theorem lem_level_seven_constants : Stmt_lem_level_seven_constants := by
  have hb := b0_ne_zero
  refine ⟨⟨genA_21, genA_13, genA_15, genA_41⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun d => ⟨genP_21 d, genP_13 d, genP_15 d, genP_41 d⟩, ?_⟩
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
  · rw [genA_21, genA_15]
    norm_num
  · rw [genA_13, genA_41]
    norm_num
  · simp only [E2, E3, P15, P41]
    ring

example : Stmt_lem_level_seven_constants := lem_level_seven_constants

end Virasoro
