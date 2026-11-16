import Virasoro.Proofs.Sec7Class
import Virasoro.Proofs.Sec3
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Corollary 4.4 (Ising specialization) from Theorem 4.3
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

theorem ppCoeff_eq_zero_of_gt {K : Type*} [Field K] (f : RatFunc K) (a : K) {k : ℕ}
    (hk : poleOrder f a < k) : ppCoeff f a k = 0 := by
  unfold ppCoeff lcoeff
  unfold poleOrder at hk
  apply (ordGE_order (expandAt f a)).coeff_eq_zero
  have := Int.self_le_toNat (-(expandAt f a).order)
  have h2 : ((-(expandAt f a).order).toNat : ℤ) < k := by exact_mod_cast hk
  linarith

theorem ratFunc_zero_div {K : Type*} [Field K] (x : RatFunc K) : (0 : RatFunc K) / x = 0 :=
  zero_div x

/-- `H_N(c⋆,Δ,d)` is the sum of its principal parts at the points of `Λ_N(b⋆)`. -/
theorem HN_eq_sum_PP (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) {N : ℕ}
    (hN : 1 ≤ N) :
    HN (kacC b) N = ∑ lam ∈ Lam N b, PP (HN (kacC b) N) (pt lam) := by
  conv_lhs => rw [confluence_eq hrec hb hN]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  obtain ⟨hA, hm⟩ := confluence_moments hrec hb hN hlam
  unfold PP
  have hsub : Finset.Icc 1 (poleOrder (HN (kacC b) N) (pt lam)) ⊆ Finset.Icc 1 (MhatC b N lam) :=
    Finset.Icc_subset_Icc_right hm
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [← show Astar b N lam k = ppCoeff (HN (kacC b) N) (pt lam) k from rfl,
      ← hA k (Finset.mem_Icc.1 hk).1]
    rfl
  · intro k hk hk'
    have hgt : poleOrder (HN (kacC b) N) (pt lam) < k := by
      simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
      exact hk' hk.1
    have h1 := hA k (Finset.mem_Icc.1 hk).1
    have h2 : Astar b N lam k = 0 := ppCoeff_eq_zero_of_gt _ _ hgt
    rw [h2] at h1
    unfold poleTerm
    rw [h1, map_zero]
    exact ratFunc_zero_div _

theorem isingLam_cast_injective : Function.Injective fun n : ℕ => ((isingLam n : ℚ) : ℂ) := by
  intro m n h
  have h0 : ((isingLam m : ℚ) : ℂ) = ((isingLam n : ℚ) : ℂ) := h
  have h1 : isingLam m = isingLam n := Rat.cast_injective h0
  unfold isingLam at h1
  have h2 : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by linarith
  have h3 : m ^ 2 = n ^ 2 := by exact_mod_cast h2
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h3

theorem kacHL_b0 (a : Label) :
    kacHL a b0 = ((isingLam (4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)).natAbs : ℚ) : ℂ) := by
  unfold kacHL
  rw [def_fixed_specialization_ising.2, isingDelta_eq_lam]

open Classical in
theorem Lam_b0 (N : ℕ) :
    Lam N b0 = ((labels N).image fun a : Label => (4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)).natAbs).image
      fun n : ℕ => ((isingLam n : ℚ) : ℂ) := by
  unfold Lam
  rw [Finset.image_image]
  exact Finset.image_congr fun a _ => kacHL_b0 a

theorem qb2_b0_rational {x : ℂ} (hx : x ∈ Qb2 b0) : ∃ q : ℚ, (q : ℂ) = x := by
  have hle : Qb2 b0 ≤ (algebraMap ℚ ℂ).fieldRange := by
    apply Subfield.closure_le.2
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    refine ⟨-4 / 3, ?_⟩
    rw [hy, b0_sq]
    norm_num
  obtain ⟨q, hq⟩ := hle hx
  exact ⟨q, by simpa using hq⟩

/-- Corollary 4.4 from the generic recursion in the form consumed by the proof of
Theorem 4.3. -/
theorem cor_ising_confluence (hrec : GenericRecursionUniform) : Stmt_cor_ising_confluence := by
  classical
  have hc : kacC b0 = 1 / 2 := def_fixed_specialization_ising.1
  refine ⟨hc, fun N hN => ?_, ?_⟩
  · have hmemLam : ∀ n ∈ (labels N).image fun a : Label => (4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)).natAbs,
        ((isingLam n : ℚ) : ℂ) ∈ Lam N b0 := by
      intro n hn
      rw [Lam_b0]
      exact Finset.mem_image_of_mem _ hn
    refine ⟨fun n => ?_, ?_, fun n hn k hk => ?_, fun n hn => ?_⟩
    · ext a
      rw [mem_collClass, Finset.mem_filter, kacHL_b0]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, isingLam_cast_injective h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]⟩
    · have h := confluence_eq hrec b0_ne_zero hN
      rw [hc, Lam_b0, Finset.sum_image fun x _ y _ hxy => isingLam_cast_injective hxy] at h
      exact h
    · have hlam := hmemLam n hn
      obtain ⟨hA, -⟩ := confluence_moments hrec b0_ne_zero hN hlam
      refine ⟨hA k hk, ?_⟩
      obtain ⟨p, hp, hpA⟩ := astar_isPolyOver b0_ne_zero hlam k
      have hlift : p ∈ Polynomial.lifts (algebraMap ℚ ℂ) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro i
        obtain ⟨q, hq⟩ := qb2_b0_rational (hp i)
        exact ⟨q, by simpa using hq⟩
      obtain ⟨q, hq⟩ := (Polynomial.mem_lifts p).1 hlift
      exact ⟨q, by rw [hq, hpA, hA k hk]⟩
    · exact (confluence_moments hrec b0_ne_zero hN (hmemLam n hn)).2
  · ext N
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hN : N = 0
    · subst hN
      simp [HN_zero]
    · rw [if_neg hN, if_neg hN, zero_add]
      have h := HN_eq_sum_PP hrec b0_ne_zero (show 1 ≤ N by omega)
      rw [hc, Lam_b0, Finset.sum_image fun x _ y _ hxy => isingLam_cast_injective hxy] at h
      exact h

example (hrec : GenericRecursionUniform) : Stmt_cor_ising_confluence := cor_ising_confluence hrec

end Virasoro
