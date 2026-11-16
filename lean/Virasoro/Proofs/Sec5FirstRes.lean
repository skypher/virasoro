import Virasoro.Proofs.Ising2
import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.PairingConstr

/-!
# Theorem 5.12: the first fixed-`c` recursive residue

The block-diagonal crossing form of Proposition 5.11 has highest-weight inverse scalars `9/28`
and `-8/105`.  Proposition 5.2 and Lemma 5.9 give
`Res_{Δ=1/2} F_2 = 9/28 E_2` and `Res_{Δ=1/2} F_3 = 9/28 E_2 F_1(1/2,5/2,d) - 8/105 E_3`;
`H_3 = F_3 - F_2 - F_1` and `F_1` is regular at `Δ = 1/2`.
-/

namespace Virasoro

open Polynomial Module

variable (K : Type) [Field K] [CharZero K]

theorem card_partition_zero : Fintype.card (Nat.Partition 0) = 1 :=
  Fintype.card_eq_one_iff.2 ⟨default, fun _ => Subsingleton.elim _ _⟩

theorem xi2_singular_coords :
    Verma.IsSingular (Verma.pbwCoord (c := (1 / 2 : K)) (h := (1 / 2 : K)) 2
      (St.coords 2 (xi2K K))) 2 := by
  rw [← toVerma_eq_pbwCoord _ (isLevel_xi2 K)]
  exact xi2_singular K

/-- `Res_{Δ=1/2} F_2(1/2,Δ,d) = 9/28 E_2(d)`. -/
theorem res_F2_half (d : K) :
    poleOrderInv (gramLocal (1 / 2 : K) (1 / 2) 2) ≤ 1 ∧
      ppCoeff (Frat (1 / 2 : K) d 2) (1 / 2) 1 = 9 / 28 * (E2K K).eval d := by
  have hβ : crossScalar (1 / 2 : K) (1 / 2) (St.coords 2 (xi2K K)) ≠ 0 := by
    rw [crossScalar_xi2]
    norm_num
  have hg : (gram (1 / 2 : K) (1 / 2 + ((2 : ℕ) : K)) 0).det ≠ 0 := by
    rw [gram_zero, Matrix.det_one]
    exact one_ne_zero
  have hord : (gramLocal (1 / 2 : K) (1 / 2) (2 + 0)).det.order
      = ((Fintype.card (Nat.Partition 0) : ℕ) : ℕ∞) := by
    rw [gramLocal_det_order, card_partition_zero]
    exact congrArg _ (gramPoly2_rootMultiplicity_half K)
  have h1 := residue_inverse (1 / 2 : K) (1 / 2) 2 0 (St.coords 2 (xi2K K)) (by norm_num)
    (xi2_singular_coords K) hβ hg hord
  have h2 := residue_Frat (1 / 2 : K) (1 / 2) 2 0 (St.coords 2 (xi2K K)) d (by norm_num)
    (xi2_singular_coords K) hβ hg hord
  refine ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [Fval_zero, torus_xi2, crossScalar_xi2] at h3
  rw [show (2 : ℕ) = 2 + 0 from rfl, h3]
  ring

/-- The kernel basis `(L_{-1}ξ₂, ξ₃)` of `G_3(1/2,1/2)` as the columns of a matrix. -/
noncomputable def U3 : Matrix (Nat.Partition 3) (Fin 2) K :=
  Matrix.of fun Y a => ![St.coords 3 (L1xi2K K) Y, St.coords 3 (xi3K K) Y] a

omit [CharZero K] in
theorem U3_col_zero : (fun Y => U3 K Y 0) = St.coords 3 (L1xi2K K) := by
  funext Y
  simp [U3]

omit [CharZero K] in
theorem U3_col_one : (fun Y => U3 K Y 1) = St.coords 3 (xi3K K) := by
  funext Y
  simp [U3]

/-- `⟨L_{-1}ξ₂|V_d(1)|L_{-1}ξ₂⟩ = E_2(d) ρ_1(1/2,5/2,d)` (Lemma 5.9). -/
theorem torus_L1xi2 (d : K) :
    torusForm (1 / 2 : K) (1 / 2) d 3 (St.coords 3 (L1xi2K K)) (St.coords 3 (L1xi2K K))
      = (E2K K).eval d * torusWord (1 / 2 : K) (5 / 2) d [1] [1] := by
  have hT := Verma.isPrimaryPairing_pairing (c := (1 / 2 : K)) (h := (1 / 2 : K)) d
  obtain ⟨-, h0, hpos⟩ := xi2_singular K
  have hY := Verma.singular_factorization hT h0 hpos 1 (e1.symm 0) (e1.symm 0)
  rw [word_one', Verma.negOp_cons_smul, Verma.negOp_nil_smul] at hY
  have e : Verma.L (-((1 : ℕ) : ℤ)) (St.toVerma (c := (1 / 2 : K)) (h := (1 / 2 : K)) (xi2K K))
      = St.toVerma (L1xi2K K) := by
    rw [toVerma_L1xi2]
    norm_num
  rw [e, toVerma_eq_pbwCoord _ (isLevel_L1xi2 K), toVerma_eq_pbwCoord _ (isLevel_xi2 K),
    Verma.primary_pbwCoord hT, Verma.primary_pbwCoord hT, torus_xi2] at hY
  rw [hY]
  simp only [torus, Matrix.of_apply, word_one']
  norm_num

/-- `Res_{Δ=1/2} F_3(1/2,Δ,d)` from the transverse residue in the basis `(L_{-1}ξ₂, ξ₃)`. -/
theorem res_F3_half (d : K) :
    poleOrderInv (gramLocal (1 / 2 : K) (1 / 2) 3) ≤ 1 ∧
      ppCoeff (Frat (1 / 2 : K) d 3) (1 / 2) 1
        = 9 / 140 * ((E2K K).eval d * torusWord (1 / 2 : K) (5 / 2) d [1] [1])
          - 8 / 105 * (E3K K).eval d := by
  have hU : ∀ a, (gram (1 / 2 : K) (1 / 2) 3).mulVec (fun Y => U3 K Y a) = 0 := by
    intro a
    have hk : ∀ v ∈ ({St.coords 3 (L1xi2K K), St.coords 3 (xi3K K)} : Set _),
        (gram (1 / 2 : K) (1 / 2) 3).mulVec v = 0 := by
      intro v hv
      have := (ker_gram3 K).ge (Submodule.subset_span hv)
      exact LinearMap.mem_ker.1 this
    fin_cases a
    · exact (U3_col_zero K) ▸ hk _ (by simp)
    · exact (U3_col_one K) ▸ hk _ (by simp)
  have hBdef : ∀ a b, (!![140 / 9, 0; 0, -105 / 8] : Matrix (Fin 2) (Fin 2) K) a b
      = cross1 (gramLocal (1 / 2 : K) (1 / 2) 3) (fun Y => U3 K Y a) (fun Y => U3 K Y b) := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, U3_col_zero, U3_col_one, cross1_11,
        cross1_12, cross1_21, cross1_22] <;> vec_simp
  have hB : (!![140 / 9, 0; 0, -105 / 8] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    norm_num
  have hord : (gramLocal (1 / 2 : K) (1 / 2) 3).det.order
      = ((Fintype.card (Fin 2) : ℕ) : ℕ∞) := by
    rw [gramLocal_det_order, Fintype.card_fin]
    exact congrArg _ (gramPoly3_rootMultiplicity K)
  obtain ⟨h1, -, h3⟩ := ppCoeff_Frat_of_basis (1 / 2 : K) (1 / 2) d 3 (U3 K) hU _ hBdef hB hord
  refine ⟨h1, ?_⟩
  have hinv : (!![140 / 9, 0; 0, -105 / 8] : Matrix (Fin 2) (Fin 2) K)⁻¹
      = !![9 / 140, 0; 0, -8 / 105] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)
  rw [h3, hinv, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, U3_col_zero, U3_col_one,
    torus_L1xi2, torus_xi3]
  vec_simp
  ring

/-- Theorem 5.12 over a field of characteristic zero. -/
theorem first_recursive_residue (d : K) :
    ppCoeff (Hrat (1 / 2 : K) d 3) (1 / 2) 1
      = 9 / 28 * (E2K K).eval d * Hval (1 / 2 : K) d (5 / 2) 1 - 8 / 105 * (E3K K).eval d := by
  have hreg : RegAt (1 / 2 : K) (Frat (1 / 2 : K) d 1) :=
    regAt_Frat (by rw [gram_one_det]; norm_num)
  have hg : gramWord (1 / 2 : K) (5 / 2) [1] [1] = 5 := by
    simp [gramWord, actSt, actWord, vac]
    norm_num
  rw [Hrat_three, ppCoeff_sub, ppCoeff_sub, (res_F3_half K d).2, (res_F2_half K d).2,
    ppCoeff_eq_zero_of_regAt hreg le_rfl, Hval_one, Fval_one, hg]
  ring

theorem ratC_half : (RatFunc.C (1 / 2 : ℂ) : Kd) = 1 / 2 := by
  rw [map_div₀, map_one, map_ofNat]

/-- At `c = 1/2` the earliest collided coefficient has the simple principal part
`Res_{Δ=1/2} H_3(1/2,Δ,d) = 9/28 E_2(d) H_1(1/2,5/2,d) - 8/105 E_3(d)`.

Paper label: thm:first-recursive-residue -/
theorem thm_first_recursive_residue : Stmt_thm_first_recursive_residue := by
  constructor
  · refine poleOrder_HN_le (1 / 2) (1 / 2) 3 1 fun M hM => ?_
    interval_cases M
    · exact poleOrderInv_le_one_of_det_ne _ _ _
        (by rw [gram_zero, Matrix.det_one]; exact one_ne_zero)
    · exact poleOrderInv_le_one_of_det_ne _ _ _ (by rw [gram_one_det]; norm_num)
    · exact (res_F2_half ℂ 0).1
    · exact (res_F3_half ℂ 0).1
  · have hE2 : algebraMap ℂ[X] Kd E2 = (E2K Kd).eval dvar := by
      simp [E2, E2K]
      simp only [map_ofNat]
    have hE3 : algebraMap ℂ[X] Kd E3 = (E3K Kd).eval dvar := by
      simp [E3, E3K]
      simp only [map_ofNat]
    have hH : RatFunc.eval (RingHom.id Kd) (pt (5 / 2)) (HN (1 / 2) 1)
        = Hval (1 / 2 : Kd) dvar (5 / 2) 1 := by
      have h52 : pt (5 / 2) = (5 / 2 : Kd) := by
        show RatFunc.C (5 / 2 : ℂ) = (5 / 2 : Kd)
        rw [map_div₀, map_ofNat, map_ofNat]
      rw [HN, ratC_half, h52]
      refine evalAt_Hrat fun M hM => ?_
      interval_cases M
      · rw [gram_zero, Matrix.det_one]
        exact one_ne_zero
      · rw [gram_one_det]
        norm_num
    rw [hE2, hE3, hH, HN, ratC_half, show pt (1 / 2) = (1 / 2 : Kd) from ratC_half]
    exact first_recursive_residue Kd dvar

example : Stmt_thm_first_recursive_residue := thm_first_recursive_residue

end Virasoro
