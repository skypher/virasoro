import Virasoro.Proofs.Sec11
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Theorem 4.2: uniqueness, coefficient field and multiplicities; existence from the recursion

The uniqueness of the partial-fraction coefficients, their coefficient field `ℚ(b⋆²)[d]`, and
the multiplicity statements are proved unconditionally.  The existence of the expansion is
derived here from the generic recursion (through equation (4.1)); the paper derives it from the
Kac determinant and Lemma 4.1.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

theorem ppCoeff_poleOrder_ne_zero {K : Type*} [Field K] (f : RatFunc K) (a : K)
    (h : ∃ k : ℕ, 1 ≤ k ∧ ppCoeff f a k ≠ 0) :
    ppCoeff f a (poleOrder f a) ≠ 0 ∧ 1 ≤ poleOrder f a := by
  obtain ⟨k, hk, hne⟩ := h
  have hE : expandAt f a ≠ 0 := by
    intro h0
    apply hne
    simp [ppCoeff, lcoeff, h0]
  have hord : (expandAt f a).order ≤ -(k : ℤ) := HahnSeries.order_le_of_coeff_ne_zero hne
  have hm : ((poleOrder f a : ℕ) : ℤ) = -(expandAt f a).order := by
    unfold poleOrder
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨?_, by omega⟩
  unfold ppCoeff lcoeff
  rw [hm, neg_neg]
  exact fun h0 => hE (HahnSeries.coeff_order_eq_zero.mp h0)

theorem poleOrder_eq_zero_of {K : Type*} [Field K] (f : RatFunc K) (a : K)
    (h : ∀ k : ℕ, 1 ≤ k → ppCoeff f a k = 0) : poleOrder f a = 0 := by
  by_contra hne
  have hpos : 0 < poleOrder f a := Nat.pos_of_ne_zero hne
  have hE : expandAt f a ≠ 0 := by
    intro h0
    unfold poleOrder at hpos
    rw [h0] at hpos
    simp at hpos
  have hm : ((poleOrder f a : ℕ) : ℤ) = -(expandAt f a).order := by
    unfold poleOrder
    apply Int.toNat_of_nonneg
    unfold poleOrder at hpos
    by_contra hneg
    push Not at hneg
    rw [Int.toNat_of_nonpos hneg.le] at hpos
    exact absurd hpos (by simp)
  have h0 := h (poleOrder f a) hpos
  unfold ppCoeff lcoeff at h0
  rw [hm, neg_neg] at h0
  exact hE (HahnSeries.coeff_order_eq_zero.mp h0)

/-- Uniqueness of the partial-fraction coefficients (Theorem 4.2). -/
theorem astar_unique {b : ℂ} {N : ℕ} (A' : ℂ → ℕ → Kd)
    (hsupp : ∀ lam k, (lam ∉ Lam N b ∨ k = 0) → A' lam k = 0)
    (hfin : {q : ℂ × ℕ | A' q.1 q.2 ≠ 0}.Finite)
    (heq : HN (kacC b) N = ∑ lam ∈ Lam N b, ∑ᶠ k : ℕ, poleTerm (A' lam k) lam k)
    {lam : ℂ} (hlam : lam ∈ Lam N b) {k : ℕ} (hk : 1 ≤ k) : A' lam k = Astar b N lam k := by
  classical
  set n : ℕ := hfin.toFinset.sup fun q => q.2 with hn
  have hbound : ∀ lam' k', A' lam' k' ≠ 0 → 1 ≤ k' ∧ k' ≤ n := by
    intro lam' k' hne
    refine ⟨?_, ?_⟩
    · by_contra h0
      exact hne (hsupp lam' k' (Or.inr (by omega)))
    · exact Finset.le_sup (f := fun q : ℂ × ℕ => q.2)
        (hfin.mem_toFinset.2 (show A' (lam', k').1 (lam', k').2 ≠ 0 from hne))
  have hsum : ∀ lam' : ℂ, ∑ᶠ k' : ℕ, poleTerm (A' lam' k') lam' k' =
      ∑ k' ∈ Finset.Icc 1 n, poleTerm (A' lam' k') lam' k' := by
    intro lam'
    apply finsum_eq_sum_of_support_subset
    intro k' hk'
    rw [Function.mem_support] at hk'
    have hne : A' lam' k' ≠ 0 := by
      intro h0
      apply hk'
      unfold poleTerm
      rw [h0, map_zero]
      exact ratFunc_zero_div _
    exact Finset.mem_coe.2 (Finset.mem_Icc.2 (hbound lam' k' hne))
  rw [Finset.sum_congr rfl fun lam' _ => hsum lam'] at heq
  have hinj : Set.InjOn (fun lam : ℂ => pt lam) (Lam N b : Set ℂ) :=
    fun x _ y _ hxy => RatFunc.C_injective hxy
  have hpp := ppCoeff_sum (Lam N b) (fun lam : ℂ => pt lam) hinj (fun _ => n) A' hlam hk
  unfold Astar
  rw [heq]
  unfold poleTerm
  rw [hpp]
  split_ifs with hle
  · rfl
  · by_contra hne
    exact hle (hbound lam k hne).2

/-- Theorem 4.2 from the expansion of `H_N` into its principal parts at the points of
`Λ_N(b⋆)`. -/
theorem thm_general_partial_fractions_of_sumPP
    (hPP : ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
      HN (kacC b) N = ∑ lam ∈ Lam N b, PP (HN (kacC b) N) (pt lam)) :
    Stmt_thm_general_partial_fractions := by
  classical
  intro b hb
  refine ⟨HN_zero _, fun N hN => ⟨fun lam hlam k _ => astar_isPolyOver hb hlam k, ?_,
    hPP b hb N hN, fun A' _ hsupp hfin heq lam hlam k hk =>
      astar_unique A' hsupp hfin heq hlam hk, fun lam _ => ⟨fun h => ?_, fun h => ?_⟩⟩, ?_⟩
  · refine ((Lam N b ×ˢ Finset.range ((Lam N b).sup (fun lam => mstar b N lam) + 1)
      : Finset (ℂ × ℕ)).finite_toSet).subset ?_
    rintro ⟨lam, k⟩ ⟨hlam, _, hne⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    refine ⟨hlam, ?_⟩
    have hle : k ≤ mstar b N lam := by
      by_contra hgt
      push Not at hgt
      exact hne (ppCoeff_eq_zero_of_gt _ _ hgt)
    have hsup : mstar b N lam ≤ (Lam N b).sup (fun lam => mstar b N lam) :=
      Finset.le_sup (f := fun lam => mstar b N lam) hlam
    omega
  · obtain ⟨h1, h2⟩ := ppCoeff_poleOrder_ne_zero (HN (kacC b) N) (pt lam) h
    exact ⟨h1, h2, fun k hk => ppCoeff_eq_zero_of_gt _ _ hk⟩
  · exact poleOrder_eq_zero_of _ _ h
  · ext N
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hN : N = 0
    · subst hN
      simp [HN_zero]
    · rw [if_neg hN, if_neg hN, zero_add]
      exact hPP b hb N (by omega)

/-- Theorem 4.2 with the existence of the expansion taken from the generic recursion. -/
theorem thm_general_partial_fractions_of_recursion (hrec : GenericRecursionUniform) :
    Stmt_thm_general_partial_fractions :=
  thm_general_partial_fractions_of_sumPP fun _ hb _ hN => HN_eq_sum_PP hrec hb hN

example (hrec : GenericRecursionUniform) : Stmt_thm_general_partial_fractions :=
  thm_general_partial_fractions_of_recursion hrec

end Virasoro
