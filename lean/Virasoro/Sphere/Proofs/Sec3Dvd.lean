import Virasoro.Cited
import Virasoro.Proofs.Sec4PFKac
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# `det G_m ∣ det G_N` for `m ≤ N` (sphere paper Lemma 3.2(iii))

sphere/paper.tex l.495: by the Kac determinant formula, `det G_m(c,Δ)` divides `det G_N(c,Δ)` in
`ℂ[Δ]` for `m ≤ N`: the labels of level `≤ m` are among those of level `≤ N`, and
`p(m - rs) ≤ p(N - rs)`.
-/

namespace Virasoro.Sphere

open Polynomial

theorem card_partition_succ_le (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ Fintype.card (Nat.Partition (n + 1)) := by
  let f : Nat.Partition n → Nat.Partition (n + 1) := fun Y =>
    { parts := 1 ::ₘ Y.parts
      parts_pos := by
        intro i hi
        rcases Multiset.mem_cons.mp hi with rfl | h
        · exact one_pos
        · exact Y.parts_pos h
      parts_sum := by rw [Multiset.sum_cons, Y.parts_sum, add_comm] }
  refine Fintype.card_le_of_injective f fun Y Y' h => ?_
  have h1 : 1 ::ₘ Y.parts = 1 ::ₘ Y'.parts := congrArg Nat.Partition.parts h
  exact Nat.Partition.ext ((Multiset.cons_inj_right 1).mp h1)

theorem card_partition_mono {m n : ℕ} (h : m ≤ n) :
    Fintype.card (Nat.Partition m) ≤ Fintype.card (Nat.Partition n) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (card_partition_succ_le _)

/-- Every central charge is `c(b)` for some `b ≠ 0`. -/
theorem exists_kacC (c : ℂ) : ∃ b : ℂ, b ≠ 0 ∧ kacC b = c := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((c - 1) / 6) (n := 2) (by norm_num)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4) (n := 2) (by norm_num)
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ, b = (s + w) / 2 := ⟨_, rfl⟩
  have hquad : b ^ 2 + 1 = s * b := by
    rw [hbdef]
    linear_combination (1 / 4 : ℂ) * hw
  have hb : b ≠ 0 := by
    intro h0
    rw [h0] at hquad
    norm_num at hquad
  refine ⟨b, hb, ?_⟩
  have hsum : b + b⁻¹ = s := by
    have h1 : b + b⁻¹ = (b ^ 2 + 1) / b := by
      field_simp
    rw [h1, hquad, mul_div_assoc, div_self hb, mul_one]
  rw [kacC, hsum, hs]
  ring

theorem gramPoly_det_dvd (hK : Cited_KacDeterminant) (c : ℂ) {m N : ℕ} (h : m ≤ N) :
    (gramPoly c m).det ∣ (gramPoly c N).det := by
  obtain ⟨b, hb, rfl⟩ := exists_kacC c
  obtain ⟨C1, hC1, h1⟩ := hK b hb m
  obtain ⟨C2, hC2, h2⟩ := hK b hb N
  rw [h1, h2]
  have hunit : IsUnit (C C1 : ℂ[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hC1)
  refine hunit.mul_left_dvd.mpr (Dvd.dvd.mul_left ?_ _)
  exact (Finset.prod_dvd_prod_of_dvd _ _ fun a _ =>
    pow_dvd_pow _ (card_partition_mono (Nat.sub_le_sub_right h _))).trans
    (Finset.prod_dvd_prod_of_subset _ _ _ (labels_mono h))

end Virasoro.Sphere
