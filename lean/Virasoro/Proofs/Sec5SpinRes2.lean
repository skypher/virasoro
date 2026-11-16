import Virasoro.Proofs.Sec5SpinRes

/-!
# Theorem 5.15 over a field of characteristic zero

`Res_{Δ=1/16} H_4(1/2,Δ,d) = -4/7 P_2(d) H_2(1/2,33/16,d) + 648/13475 P_4(d)`, from
`H_4 = F_4 - F_3 - F_2`, the transverse residue of `F_4` in the basis
`(L_{-2}χ₂, L_{-1}²χ₂, χ₄)` and the factorization of Lemma 5.9.
-/

namespace Virasoro

open Polynomial Module

set_option maxRecDepth 20000

variable (K : Type) [Field K] [CharZero K]

/-- The kernel basis `(L_{-2}χ₂, L_{-1}²χ₂, χ₄)` of `G_4(1/2,1/16)` as the columns of a
matrix. -/
noncomputable def U4 : Matrix (Nat.Partition 4) (Fin 3) K :=
  Matrix.of fun Y a =>
    ![St.coords 4 (L2chi2K K) Y, St.coords 4 (L11chi2K K) Y, St.coords 4 (chi4K K) Y] a

omit [CharZero K] in
theorem U4_col_zero : (fun Y => U4 K Y 0) = St.coords 4 (L2chi2K K) := by
  funext Y
  simp [U4]

omit [CharZero K] in
theorem U4_col_one : (fun Y => U4 K Y 1) = St.coords 4 (L11chi2K K) := by
  funext Y
  simp [U4]

omit [CharZero K] in
theorem U4_col_two : (fun Y => U4 K Y 2) = St.coords 4 (chi4K K) := by
  funext Y
  simp [U4]

theorem negOp_chi2 (i : Fin 2) :
    VirEnv.negOp (1 / 2 : K) (![[2], [1, 1]] i)
        • St.toVerma (c := (1 / 2 : K)) (h := (1 / 16 : K)) (chi2K K)
      = Verma.pbwCoord 4 (![St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K)] i) := by
  fin_cases i
  · show VirEnv.negOp (1 / 2 : K) [2] • _ = Verma.pbwCoord 4 (St.coords 4 (L2chi2K K))
    rw [Verma.negOp_cons_smul, Verma.negOp_nil_smul, ← toVerma_eq_pbwCoord _ (isLevel_L2chi2 K),
      toVerma_L2chi2]
    norm_num
  · show VirEnv.negOp (1 / 2 : K) [1, 1] • _ = Verma.pbwCoord 4 (St.coords 4 (L11chi2K K))
    rw [Verma.negOp_cons_smul, Verma.negOp_cons_smul, Verma.negOp_nil_smul,
      ← toVerma_eq_pbwCoord _ (isLevel_L11chi2 K), toVerma_L11chi2]
    norm_num

/-- `⟨L_{-Y}χ₂|V_d(1)|L_{-Y'}χ₂⟩ = P_2(d) ρ_2(1/2,33/16,d)_{Y,Y'}` (Lemma 5.9). -/
theorem torus_chi2_desc (d : K) (i j : Fin 2) :
    torusForm (1 / 2 : K) (1 / 16) d 4
        (![St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K)] i)
        (![St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K)] j)
      = (P2K K).eval d
        * torusWord (1 / 2 : K) (33 / 16) d (![[2], [1, 1]] i) (![[2], [1, 1]] j) := by
  have hT := Verma.isPrimaryPairing_pairing (c := (1 / 2 : K)) (h := (1 / 16 : K)) d
  obtain ⟨-, h0, hpos⟩ := chi2_singular K
  have hY := Verma.singular_factorization hT h0 hpos 2 (e2.symm i) (e2.symm j)
  rw [e2_symm_word, e2_symm_word, negOp_chi2, negOp_chi2, toVerma_eq_pbwCoord _ (isLevel_chi2 K),
    Verma.primary_pbwCoord hT, Verma.primary_pbwCoord hT, torus_chi2] at hY
  rw [hY]
  simp only [torus, Matrix.of_apply, e2_symm_word]
  norm_num

/-- `Res_{Δ=1/16} F_4(1/2,Δ,d)` from the transverse residue in the basis
`(L_{-2}χ₂, L_{-1}²χ₂, χ₄)`. -/
theorem res_F4_sixteenth (d : K) :
    poleOrderInv (gramLocal (1 / 2 : K) (1 / 16) 4) ≤ 1 ∧
      ppCoeff (Frat (1 / 2 : K) d 4) (1 / 16) 1
        = (P2K K).eval d * (-41 / 350 * torusWord (1 / 2 : K) (33 / 16) d [2] [2]
            + 6 / 175 * (torusWord (1 / 2 : K) (33 / 16) d [2] [1, 1]
              + torusWord (1 / 2 : K) (33 / 16) d [1, 1] [2])
            - 136 / 5775 * torusWord (1 / 2 : K) (33 / 16) d [1, 1] [1, 1])
          + 648 / 13475 * (P4K K).eval d := by
  have hU : ∀ a, (gram (1 / 2 : K) (1 / 16) 4).mulVec (fun Y => U4 K Y a) = 0 := by
    intro a
    have hk : ∀ v ∈ ({St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K),
        St.coords 4 (chi4K K)} : Set _), (gram (1 / 2 : K) (1 / 16) 4).mulVec v = 0 := by
      intro v hv
      have := (ker_gram4 K).ge (Submodule.subset_span hv)
      exact LinearMap.mem_ker.1 this
    fin_cases a
    · exact (U4_col_zero K) ▸ hk _ (by simp)
    · exact (U4_col_one K) ▸ hk _ (by simp)
    · exact (U4_col_two K) ▸ hk _ (by simp)
  have hBdef : ∀ a b, (!![-119 / 8, -693 / 32, 0; -693 / 32, -9471 / 128, 0;
        0, 0, 13475 / 648] : Matrix (Fin 3) (Fin 3) K) a b
      = cross1 (gramLocal (1 / 2 : K) (1 / 16) 4) (fun Y => U4 K Y a) (fun Y => U4 K Y b) := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, U4_col_zero, U4_col_one,
        U4_col_two, crossR11, crossR12, crossR13, crossR21, crossR22, crossR23, crossR31,
        crossR32, crossR33] <;> vec_simp
  have hB : (!![-119 / 8, -693 / 32, 0; -693 / 32, -9471 / 128, 0;
      0, 0, 13475 / 648] : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [Matrix.det_fin_three]
    vec_simp
    norm_num
  have hord : (gramLocal (1 / 2 : K) (1 / 16) 4).det.order
      = ((Fintype.card (Fin 3) : ℕ) : ℕ∞) := by
    rw [gramLocal_det_order, Fintype.card_fin]
    exact congrArg _ (gramPoly4_rootMultiplicity K)
  obtain ⟨h1, -, h3⟩ := ppCoeff_Frat_of_basis (1 / 2 : K) (1 / 16) d 4 (U4 K) hU _ hBdef hB hord
  refine ⟨h1, ?_⟩
  have hinv : (!![-119 / 8, -693 / 32, 0; -693 / 32, -9471 / 128, 0;
      0, 0, 13475 / 648] : Matrix (Fin 3) (Fin 3) K)⁻¹
      = !![-41 / 350, 6 / 175, 0; 6 / 175, -136 / 5775, 0; 0, 0, 648 / 13475] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)
  have t00 := torus_chi2_desc K d 0 0
  have t01 := torus_chi2_desc K d 0 1
  have t10 := torus_chi2_desc K d 1 0
  have t11 := torus_chi2_desc K d 1 1
  vec_simp at t00 t01 t10 t11
  rw [h3, hinv]
  simp only [Fin.sum_univ_three, U4_col_zero, U4_col_one, U4_col_two, t00, t01, t10, t11,
    torus_chi4]
  vec_simp
  ring

/-- Theorem 5.15 over a field of characteristic zero. -/
theorem spin_recursive_residue (d : K) :
    ppCoeff (Hrat (1 / 2 : K) d 4) (1 / 16) 1
      = -(4 / 7) * (P2K K).eval d * Hval (1 / 2 : K) d (33 / 16) 2
        + 648 / 13475 * (P4K K).eval d := by
  rw [Hrat_four, ppCoeff_sub, ppCoeff_sub, (res_F4_sixteenth K d).2, (res_F3_sixteenth K d).2,
    (res_F2_sixteenth K d).2, Hval_two, Fval_two, gram2, Matrix.adjugate_fin_two_of,
    Matrix.det_fin_two_of]
  simp only [Fin.sum_univ_two]
  vec_simp
  ring

/-- The residue of Theorem 5.15 as an explicit polynomial in `d`. -/
theorem spin_residue_explicit (d : K) :
    -(4 / 7) * (P2K K).eval d * Hval (1 / 2 : K) d (33 / 16) 2 + 648 / 13475 * (P4K K).eval d
      = 1 / 40425 * d * (d - 1) * (2 * d - 7) * (2 * d - 1)
        * (248 * d ^ 4 - 5752 * d ^ 3 + 25274 * d ^ 2 - 33630 * d + 5775) := by
  rw [Hval_two, Fval_two, Fval_one, gram2, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of]
  simp only [Fin.sum_univ_two]
  vec_simp
  simp [P2K, P4K, torusWord, phi, actWord, gramWord, actSt, vac, centralTerm]
  field_simp
  ring

end Virasoro
