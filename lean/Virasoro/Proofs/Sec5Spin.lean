import Virasoro.Proofs.Sec5SpinRes2

/-!
# Propositions 5.13, 5.14 and Theorem 5.15: the first spin-module collision
-/

namespace Virasoro

open Polynomial Module

theorem word_eq_of_parts {N : ℕ} (Y : Nat.Partition N) (w : List ℕ) (hw : w.Pairwise (· ≥ ·))
    (hp : Y.parts = (w : Multiset ℕ)) : Y.word = w :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hba hab) (word_pairwise Y) hw
    (Multiset.coe_eq_coe.1 ((Verma.word_coe Y).trans hp))

theorem word_indiscrete_two : (Nat.Partition.indiscrete 2).word = [2] :=
  word_eq_of_parts _ _ (by simp) (by decide)

theorem word_ones_two : (onesPartition 2).word = [1, 1] :=
  word_eq_of_parts _ _ (by simp) (by decide)

/-- At level `4` the labels `(1,2)` and `(2,2)` collide at `Δ = 1/16`; the Shapovalov
determinant at `c = 1/2`; the Smith exponents `(0,0,1,1,1)`; at most simple poles of
`G_4⁻¹`, `F_4`, `H_4` at `Δ = 1/16`.

Paper label: prop:spin-collision -/
theorem prop_spin_collision : Stmt_prop_spin_collision := by
  have hpole : poleOrderInv (gramLocal (1 / 2 : ℂ) (1 / 16) 4) ≤ 1 := by
    rw [(smith_main (isSmith_gram4 ℂ)).2.2]
    decide
  refine ⟨⟨by norm_num [isingDelta], by norm_num [isingDelta]⟩, gramPoly4_det ℂ, isSmith_gram4 ℂ,
    hpole, (poleOrder_FN_le (1 / 2) (1 / 16) 4).trans hpole, ?_⟩
  refine poleOrder_HN_le (1 / 2) (1 / 16) 4 1 fun M hM => ?_
  interval_cases M
  · exact poleOrderInv_le_one_of_det_ne _ _ _
      (by rw [gram_zero, Matrix.det_one]; exact one_ne_zero)
  · exact poleOrderInv_le_one_of_det_ne _ _ _ (by rw [gram_one_det]; norm_num)
  · exact (res_F2_sixteenth ℂ 0).1
  · exact (res_F3_sixteenth ℂ 0).1
  · exact hpole

example : Stmt_prop_spin_collision := prop_spin_collision

/-- The singular data at the first spin collision: `χ₂`, `χ₄` are singular in `M(1/2,1/16)`;
`ker G_4(1/2,1/16) = span{L_{-2}χ₂, L_{-1}²χ₂, χ₄}`; the crossing form
`diag(-7/4 G_2(1/2,33/16), 13475/648)`; the torus polynomials `P₂`, `P₄`.

Paper label: prop:spin-singular-data -/
theorem prop_spin_singular_data : Stmt_prop_spin_singular_data := by
  refine ⟨chi2_singular ℂ, chi4_singular ℂ, toVerma_L2chi2 ℂ, toVerma_L11chi2 ℂ, ker_gram4 ℂ,
    ⟨crossR11 ℂ, crossR12 ℂ, crossR13 ℂ, crossR21 ℂ, crossR22 ℂ, crossR23 ℂ, crossR31 ℂ,
      crossR32 ℂ, crossR33 ℂ⟩, ?_, torusForm_poly_eq (torus_chi2 ℂ),
    torusForm_poly_eq (torus_chi4 ℂ)⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [gram, word_indiscrete_two, word_ones_two, gramWord, actSt, actWord, vac,
      centralTerm] <;> norm_num

example : Stmt_prop_spin_singular_data := prop_spin_singular_data

theorem pt_eq_div (a b : ℕ) [a.AtLeastTwo] [b.AtLeastTwo] :
    pt ((OfNat.ofNat a : ℂ) / (OfNat.ofNat b : ℂ))
      = (OfNat.ofNat a : Kd) / (OfNat.ofNat b : Kd) := by
  show RatFunc.C ((OfNat.ofNat a : ℂ) / (OfNat.ofNat b : ℂ)) = _
  rw [map_div₀, map_ofNat, map_ofNat]

/-- `Res_{Δ=1/16} H_4(1/2,Δ,d) = -4/7 P_2(d) H_2(1/2,33/16,d) + 648/13475 P_4(d)`, and this
residue is `d (d-1) (2d-7) (2d-1) (248 d⁴ - 5752 d³ + 25274 d² - 33630 d + 5775) / 40425`.

Paper label: thm:spin-recursive-residue -/
theorem thm_spin_recursive_residue : Stmt_thm_spin_recursive_residue := by
  have hC16 : pt (1 / 16) = (1 / 16 : Kd) := by
    show RatFunc.C (1 / 16 : ℂ) = _
    rw [map_div₀, map_one, map_ofNat]
  have hP2 : algebraMap ℂ[X] Kd P2 = (P2K Kd).eval dvar := by
    simp [P2, P2K]
    simp only [map_ofNat]
  have hP4 : algebraMap ℂ[X] Kd P4 = (P4K Kd).eval dvar := by
    simp [P4, P4K]
    simp only [map_ofNat]
  have hH : RatFunc.eval (RingHom.id Kd) (pt (33 / 16)) (HN (1 / 2) 2)
      = Hval (1 / 2 : Kd) dvar (33 / 16) 2 := by
    rw [HN, ratC_half, pt_eq_div 33 16]
    refine evalAt_Hrat fun M hM => ?_
    interval_cases M
    · rw [gram_zero, Matrix.det_one]
      exact one_ne_zero
    · rw [gram_one_det]
      norm_num
    · rw [gram2_det]
      norm_num
  have key := spin_recursive_residue Kd dvar
  constructor
  · rw [hP2, hP4, hH, HN, ratC_half, hC16]
    exact key
  · rw [HN, ratC_half, hC16, key, spin_residue_explicit]
    simp only [map_mul, map_sub, map_add, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_ofNat, map_one, map_div₀]

example : Stmt_thm_spin_recursive_residue := thm_spin_recursive_residue

end Virasoro
