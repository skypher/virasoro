import Virasoro.Proofs.TorusDegree
import Virasoro.Proofs.GramDet
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The large-weight comparison of the torus and Shapovalov matrices (paper Lemma 4.1)

With `D = ∑_Y ℓ(Y)`: the cofactors of `G_N` have degree at most `D - (ℓ(Y) + ℓ(Y'))/2` in the
internal weight, the entries of `ρ_N - G_N` have degree below `min(ℓ(Y), ℓ(Y'))`, and
`det G_N` has degree `D`.  Hence the numerator of `F_N - p(N)` has smaller degree than its
denominator `det G_N`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem word_sum {N : ℕ} (Y : Nat.Partition N) : Y.word.sum = N := by
  have h : ((Y.word : List ℕ) : Multiset ℕ).sum = N := by
    rw [Nat.Partition.word, Multiset.sort_eq, Y.parts_sum]
  rwa [Multiset.sum_coe] at h

theorem gramPoly_symm (c : 𝔽) (N : ℕ) (Y Y' : Nat.Partition N) :
    gramPoly c N Y Y' = gramPoly c N Y' Y :=
  gramWord_symm _ _ (word_pos Y) (word_pos Y')

theorem gramPoly_natDegree_le (c : 𝔽) (N : ℕ) (Y Y' : Nat.Partition N) :
    (gramPoly c N Y Y').natDegree ≤ min Y.word.length Y'.word.length :=
  natDegree_gramWord_le c Y.word Y'.word (word_pos Y)

/-- `∑ adj(G)_{Y,Y'} G_{Y,Y'} = p(N) det G`. -/
theorem sum_adjugate_gram (c : 𝔽) (N : ℕ) :
    ∑ Y, ∑ Y', (gramPoly c N).adjugate Y Y' * gramPoly c N Y Y'
      = (Fintype.card (Nat.Partition N) : 𝔽[X]) * (gramPoly c N).det := by
  have h : ∀ Y, ∑ Y', (gramPoly c N).adjugate Y Y' * gramPoly c N Y Y' = (gramPoly c N).det := by
    intro Y
    have := congrFun (congrFun (Matrix.adjugate_mul (gramPoly c N)) Y) Y
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun Y' _ => by rw [gramPoly_symm c N Y Y']
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The cofactors of `G_N` have degree at most `D - (ℓ(Y) + ℓ(Y'))/2`. -/
theorem adjugate_natDegree (c : 𝔽) (N : ℕ) (Y Y' : Nat.Partition N) :
    2 * ((gramPoly c N).adjugate Y Y').natDegree + Y.word.length + Y'.word.length
      ≤ 2 * ∑ Z : Nat.Partition N, Z.word.length := by
  classical
  set D := ∑ Z : Nat.Partition N, Z.word.length with hD
  have hY : Y.word.length ≤ D :=
    Finset.single_le_sum (f := fun Z : Nat.Partition N => Z.word.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ Y)
  have hY' : Y'.word.length ≤ D :=
    Finset.single_le_sum (f := fun Z : Nat.Partition N => Z.word.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ Y')
  set n := (2 * D - Y.word.length - Y'.word.length) / 2 with hn
  have hn2 : 2 * n ≤ 2 * D - Y.word.length - Y'.word.length := by
    rw [hn, mul_comm]; exact Nat.div_mul_le_self _ _
  suffices hdeg : ((gramPoly c N).adjugate Y Y').natDegree ≤ n by omega
  rw [Matrix.adjugate_apply, Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [← C_eq_intCast]
  refine le_trans (natDegree_C_mul_le _ _) ?_
  by_cases hσ : σ Y = Y'
  · set β : Nat.Partition N → ℕ := fun i =>
      if i = Y then 0 else min (σ i).word.length i.word.length with hβ
    have h1 : ∀ i, ((gramPoly c N).updateRow Y' (Pi.single Y 1) (σ i) i).natDegree ≤ β i := by
      intro i
      by_cases hi : i = Y
      · subst hi
        rw [hσ, Matrix.updateRow_self, Pi.single_eq_same, natDegree_one]
        exact Nat.zero_le _
      · have hne : σ i ≠ Y' := fun h => hi (σ.injective (h.trans hσ.symm))
        rw [Matrix.updateRow_ne hne, hβ]
        simp only [if_neg hi]
        exact gramPoly_natDegree_le c N (σ i) i
    have h2 : ∑ i, (2 * β i + (if i = Y then (σ i).word.length + i.word.length else 0))
        ≤ ∑ i, ((σ i).word.length + i.word.length) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i = Y
      · simp [hβ, hi]
      · simp only [hβ, if_neg hi, add_zero]
        have := Nat.min_le_left (σ i).word.length i.word.length
        have := Nat.min_le_right (σ i).word.length i.word.length
        omega
    have h3 : ∑ i : Nat.Partition N, (σ i).word.length = D :=
      Equiv.sum_comp σ fun Z : Nat.Partition N => Z.word.length
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ Y,
      if_pos (Finset.mem_univ Y), ← Finset.mul_sum, h3, hσ] at h2
    refine le_trans (natDegree_prod_le _ _) (le_trans (Finset.sum_le_sum fun i _ => h1 i) ?_)
    rw [hn, Nat.le_div_iff_mul_le (by norm_num)]
    omega
  · have hne : σ.symm Y' ≠ Y := fun h => hσ (by rw [← h, Equiv.apply_symm_apply])
    have hz : (gramPoly c N).updateRow Y' (Pi.single Y 1) (σ (σ.symm Y')) (σ.symm Y') = 0 := by
      rw [Equiv.apply_symm_apply, Matrix.updateRow_self, Pi.single_eq_of_ne hne]
    have hprod : ∏ i, (gramPoly c N).updateRow Y' (Pi.single Y 1) (σ i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (σ.symm Y')) hz
    rw [hprod, natDegree_zero]
    exact Nat.zero_le _

theorem Fnum_sub_eq (c d : 𝔽) (N : ℕ) :
    Fnum c d N - (Fintype.card (Nat.Partition N) : 𝔽[X]) * (gramPoly c N).det
      = ∑ Y, ∑ Y', (gramPoly c N).adjugate Y Y' * (torusPoly c d N Y Y' - gramPoly c N Y Y') := by
  rw [← sum_adjugate_gram, Fnum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun Y' _ => by ring

/-- The numerator of `F_N - p(N)` has degree below `D = ∑_Y ℓ(Y)`. -/
theorem dlt_Fnum_sub (c d : 𝔽) (N : ℕ) :
    DLt (Fnum c d N - (Fintype.card (Nat.Partition N) : 𝔽[X]) * (gramPoly c N).det)
      (∑ Z : Nat.Partition N, Z.word.length) := by
  rw [Fnum_sub_eq]
  refine dlt_finset_sum _ _ fun Y _ => dlt_finset_sum _ _ fun Y' _ => ?_
  have hδ : DLt (torusPoly c d N Y Y' - gramPoly c N Y Y')
      (min Y.word.length Y'.word.length) :=
    dlt_torusWord_sub_gramWord c d Y.word (word_pos Y) Y'.word (word_pos Y')
      (by rw [word_sum, word_sum])
  by_cases h0 : torusPoly c d N Y Y' - gramPoly c N Y Y' = 0
  · rw [h0, mul_zero]; exact dlt_zero _
  · have h1 := hδ.natDegree_lt h0
    have h2 := adjugate_natDegree c N Y Y'
    have h3 := natDegree_mul_le (p := (gramPoly c N).adjugate Y Y')
      (q := torusPoly c d N Y Y' - gramPoly c N Y Y')
    have h4 := Nat.min_le_left Y.word.length Y'.word.length
    have h5 := Nat.min_le_right Y.word.length Y'.word.length
    exact dlt_of_natDegree_lt (by omega)

/-- The numerator of `F_N - p(N)` has smaller degree than `det G_N`. -/
theorem degree_Fnum_sub_lt (c d : 𝔽) (N : ℕ) :
    (Fnum c d N - (Fintype.card (Nat.Partition N) : 𝔽[X]) * (gramPoly c N).det).degree
      < (gramPoly c N).det.degree :=
  lt_of_lt_of_le (dlt_Fnum_sub c d N) (le_degree_of_ne_zero (gramPoly_det_coeff_ne_zero c N))

end Virasoro
