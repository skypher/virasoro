import Virasoro.Proofs.Ising4

/-!
# The first spin-module collision: crossing form and torus polynomials

The crossing scalar of `χ₂`, the level-four crossing form in the basis
`(L_{-2}χ₂, L_{-1}²χ₂, χ₄)`, and the torus polynomials `P₂`, `P₄` by the Ward recursion.
-/

namespace Virasoro

open Polynomial

set_option maxRecDepth 20000

variable (K : Type) [Field K] [CharZero K]

theorem crossScalar_chi2 : crossScalar (1 / 2 : K) (1 / 16) (St.coords 2 (chi2K K)) = -7 / 4 := by
  rw [crossScalar_eq (gramForm_chi2 K)]
  simp [Qchi2]
  norm_num

theorem crossScalar_chi4 :
    crossScalar (1 / 2 : K) (1 / 16) (St.coords 4 (chi4K K)) = 13475 / 648 := by
  rw [crossScalar_eq (gramFormR33 K)]
  simp [R33]
  norm_num

theorem crossR11 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (L2chi2K K))
    (St.coords 4 (L2chi2K K)) = -119 / 8 := by
  rw [cross1_gramLocal_eq (gramFormR11 K)]
  simp [R11]
  norm_num

theorem crossR12 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (L2chi2K K))
    (St.coords 4 (L11chi2K K)) = -693 / 32 := by
  rw [cross1_gramLocal_eq (gramFormR12 K)]
  simp [R12]
  norm_num

theorem crossR13 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (L2chi2K K))
    (St.coords 4 (chi4K K)) = 0 := by
  rw [cross1_gramLocal_eq (gramFormR13 K)]
  simp [R13]
  norm_num

theorem crossR21 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (L11chi2K K))
    (St.coords 4 (L2chi2K K)) = -693 / 32 := by
  rw [cross1_gramLocal_eq (gramFormR21 K)]
  simp [R12]
  norm_num

theorem crossR22 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (L11chi2K K))
    (St.coords 4 (L11chi2K K)) = -9471 / 128 := by
  rw [cross1_gramLocal_eq (gramFormR22 K)]
  simp [R22]
  norm_num

theorem crossR23 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (L11chi2K K))
    (St.coords 4 (chi4K K)) = 0 := by
  rw [cross1_gramLocal_eq (gramFormR23 K)]
  simp [R23]
  norm_num

theorem crossR31 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (chi4K K))
    (St.coords 4 (L2chi2K K)) = 0 := by
  rw [cross1_gramLocal_eq (gramFormR31 K)]
  simp [R13]
  norm_num

theorem crossR32 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (chi4K K))
    (St.coords 4 (L11chi2K K)) = 0 := by
  rw [cross1_gramLocal_eq (gramFormR32 K)]
  simp [R23]
  norm_num

theorem crossR33 : cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (St.coords 4 (chi4K K))
    (St.coords 4 (chi4K K)) = 13475 / 648 := by
  rw [cross1_gramLocal_eq (gramFormR33 K)]
  simp [R33]
  norm_num

/-- `⟨χ₂|V_d(1)|χ₂⟩ = P₂(d)` by the Ward recursion. -/
theorem torus_chi2 (d : K) :
    torusForm (1 / 2 : K) (1 / 16) d 2 (St.coords 2 (chi2K K)) (St.coords 2 (chi2K K))
      = (P2K K).eval d := by
  rw [torusForm_coords _ _ _ _ _ (isLevel_chi2 K) (isLevel_chi2 K)]
  simp [chi2K, P2K, torusWord, phi, actWord, centralTerm]
  ring

/-- `⟨χ₄|V_d(1)|χ₄⟩ = P₄(d)` by the Ward recursion. -/
theorem torus_chi4 (d : K) :
    torusForm (1 / 2 : K) (1 / 16) d 4 (St.coords 4 (chi4K K)) (St.coords 4 (chi4K K))
      = (P4K K).eval d := by
  rw [torusForm_coords _ _ _ _ _ (isLevel_chi4 K) (isLevel_chi4 K)]
  simp [chi4K, P4K, torusWord, phi, actWord, centralTerm]
  ring

end Virasoro
