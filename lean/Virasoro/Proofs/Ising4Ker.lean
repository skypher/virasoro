import Virasoro.Proofs.Ising4Mat

/-!
# The first spin-module collision: kernel and Smith exponents at level four

`ker G_4(1/2,1/16) = span{L_{-2}χ₂, L_{-1}²χ₂, χ₄}`: the three vectors are independent and lie
in the kernel, and the invertible upper-left `2 × 2` minor bounds the nullity by three.  With
the determinant of order three, Lemma 5.1 gives the Smith exponents `(0,0,1,1,1)`.
-/

namespace Virasoro

open Polynomial Module

variable (K : Type) [Field K] [CharZero K]

theorem gram4_mulVec_eq_zero {v : Nat.Partition 4 → K} {w : Fin 5 → K}
    (hv : ∀ i, v (e4.symm i) = w i) (hw : ∀ i, ∑ j, G4 K (1 / 16) i j * w j = 0) :
    (gram (1 / 2 : K) (1 / 16) 4).mulVec v = 0 := by
  funext Y
  obtain ⟨i, rfl⟩ := e4.symm.surjective Y
  rw [mulVec_e4]
  simp only [gram4_entry, hv]
  exact hw i

theorem linearIndependent_ker4 : LinearIndependent K
    ![St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K), St.coords 4 (chi4K K)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  vec_simp at hg
  have h2 := congrFun hg (e4.symm 2)
  have h3 := congrFun hg (e4.symm 3)
  have h4 := congrFun hg (e4.symm 4)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coords_L2chi2, coords_L11chi2,
    coords_chi4, Pi.zero_apply] at h2 h3 h4
  vec_simp at h2 h3 h4
  intro i
  fin_cases i
  · show g 0 = 0
    linear_combination h3 + (3 / 4 : K) * h4
      - (123 / 80 : K) * (h2 + (3 / 4 : K) * h3 + (9 / 16 : K) * h4)
  · show g 1 = 0
    linear_combination h4 + (9 / 20 : K) * (h2 + (3 / 4 : K) * h3 + (9 / 16 : K) * h4)
  · show g 2 = 0
    linear_combination (-9 / 20 : K) * (h2 + (3 / 4 : K) * h3 + (9 / 16 : K) * h4)

omit [CharZero K] in
theorem range_ker4 : Set.range
    ![St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K), St.coords 4 (chi4K K)]
    = {St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K), St.coords 4 (chi4K K)} := by
  ext w
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]

/-- `ker G_4(1/2,1/16) = span{L_{-2}χ₂, L_{-1}²χ₂, χ₄}`. -/
theorem ker_gram4 : LinearMap.ker (gram (1 / 2 : K) (1 / 16) 4).mulVecLin =
    Submodule.span K
      {St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K), St.coords 4 (chi4K K)} := by
  have hle : Submodule.span K
      {St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K), St.coords 4 (chi4K K)}
        ≤ LinearMap.ker (gram (1 / 2 : K) (1 / 16) 4).mulVecLin := by
    rw [Submodule.span_le]
    intro v hv
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rcases hv with rfl | rfl | hv
    · refine gram4_mulVec_eq_zero K (coords_L2chi2 K) fun i => ?_
      fin_cases i <;> (simp only [Fin.sum_univ_five, G4]; vec_simp; norm_num)
    · refine gram4_mulVec_eq_zero K (coords_L11chi2 K) fun i => ?_
      fin_cases i <;> (simp only [Fin.sum_univ_five, G4]; vec_simp; norm_num)
    · rw [Set.mem_singleton_iff.1 hv]
      refine gram4_mulVec_eq_zero K (coords_chi4 K) fun i => ?_
      fin_cases i <;> (simp only [Fin.sum_univ_five, G4]; vec_simp; norm_num)
  have hspan : finrank K (Submodule.span K
      {St.coords 4 (L2chi2K K), St.coords 4 (L11chi2K K), St.coords 4 (chi4K K)}) = 3 := by
    rw [← range_ker4, finrank_span_eq_card (linearIndependent_ker4 K)]
    simp
  have hker : finrank K (LinearMap.ker (gram (1 / 2 : K) (1 / 16) 4).mulVecLin) ≤ 3 := by
    let φ : (Nat.Partition 4 → K) →ₗ[K] (Fin 3 → K) :=
      LinearMap.funLeft K K ![e4.symm 2, e4.symm 3, e4.symm 4]
    have hinj : Function.Injective
        (φ.comp (LinearMap.ker (gram (1 / 2 : K) (1 / 16) 4).mulVecLin).subtype) := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨v, hv⟩ h0
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      have h2 : v (e4.symm 2) = 0 := congrFun h0 0
      have h3 : v (e4.symm 3) = 0 := congrFun h0 1
      have h4 : v (e4.symm 4) = 0 := congrFun h0 2
      have r0 := congrFun hv (e4.symm 0)
      have r1 := congrFun hv (e4.symm 1)
      rw [mulVec_e4, Fin.sum_univ_five, h2, h3, h4, Pi.zero_apply] at r0 r1
      simp only [gram4_entry, G4] at r0 r1
      vec_simp at r0 r1
      have hv0 : v (e4.symm 0) = 0 := by
        linear_combination (59 / 128 : K) * r0 - (7 / 16 : K) * r1
      have hv1 : v (e4.symm 1) = 0 := by
        linear_combination (3 / 2 : K) * r1 - (7 / 16 : K) * r0
      apply Subtype.ext
      funext Y
      obtain ⟨i, rfl⟩ := e4.symm.surjective Y
      fin_cases i
      · exact hv0
      · exact hv1
      · exact h2
      · exact h3
      · exact h4
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hspan]; exact hker)).symm

theorem finrank_ker0_gram4 : finrank K (ker0 (gramLocal (1 / 2 : K) (1 / 16) 4)) = 3 := by
  unfold ker0
  rw [coeffMat_zero_gramLocal, ker_gram4, ← range_ker4,
    finrank_span_eq_card (linearIndependent_ker4 K)]
  simp

/-- The local Smith exponents of `G_4(1/2, 1/16 + x)` are `(0,0,1,1,1)`. -/
theorem isSmith_gram4 : IsSmith (gramLocal (1 / 2 : K) (1 / 16) 4) {0, 0, 1, 1, 1} := by
  have h := isSmith_of_order_eq_nullity (gramLocal_det_ne_zero (1 / 2 : K) (1 / 16) 4) (k := 3)
    (by rw [gramLocal_det_order, gramPoly4_rootMultiplicity]) (finrank_ker0_gram4 K)
  have hc : Fintype.card (Nat.Partition 4) = 5 := by rw [Fintype.card_congr e4, Fintype.card_fin]
  rw [hc] at h
  exact h

end Virasoro
