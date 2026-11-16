import Virasoro.Local
import Virasoro.Proofs.Germs

/-!
# Laurent expansion of sums of simple fractions: uniqueness of partial fractions
-/

namespace Virasoro

open scoped LaurentSeries
open RatFunc

variable {K : Type*} [Field K]

/-- The Laurent expansion at `a` as a ring homomorphism. -/
noncomputable def expandHom (a : K) : RatFunc K →+* K⸨X⸩ :=
  (algebraMap (RatFunc K) K⸨X⸩).comp (RatFunc.laurent a).toRingHom

theorem expandAt_eq (f : RatFunc K) (a : K) : expandAt f a = expandHom a f := rfl

theorem expandHom_C (a c : K) : expandHom a (RatFunc.C c) = HahnSeries.C c := by
  simp only [expandHom, RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Function.comp_apply, RatFunc.laurent_C]
  rw [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply]
  simp

theorem expandHom_X (a : K) : expandHom a RatFunc.X = HahnSeries.single 1 1 + HahnSeries.C a := by
  simp only [expandHom, RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Function.comp_apply, RatFunc.laurent_X, map_add]
  rw [RatFunc.coe_X]
  congr 1
  rw [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply]
  simp

/-- The expansion at `a` of the simple fraction `c/(Δ - a)^k` is `c x^{-k}`. -/
theorem expandHom_pole_same (a c : K) (k : ℕ) :
    expandHom a (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) =
      HahnSeries.single (-(k : ℤ)) c := by
  rw [map_div₀, map_pow, map_sub, expandHom_X, expandHom_C, expandHom_C, add_sub_cancel_right]
  have h1 : (HahnSeries.single (1 : ℤ) (1 : K)) ^ k = HahnSeries.single (k : ℤ) (1 : K) := by
    rw [← RatFunc.single_one_eq_pow]
  rw [h1, div_eq_iff (HahnSeries.single_ne_zero one_ne_zero), HahnSeries.single_mul_single,
    neg_add_cancel, mul_one]
  rfl

/-- The expansion at `a` of a simple fraction with pole at `μ ≠ a` is a power series. -/
theorem expandHom_pole_other {a μ : K} (h : μ ≠ a) (c : K) (k : ℕ) :
    OrdGE (expandHom a (RatFunc.C c / (RatFunc.X - RatFunc.C μ) ^ k)) 0 := by
  rw [map_div₀, map_pow, map_sub, expandHom_X, expandHom_C, expandHom_C]
  have hu : RegVal (HahnSeries.single 1 1 + HahnSeries.C a - HahnSeries.C μ : K⸨X⸩) (a - μ) := by
    have h1 : RegVal (HahnSeries.single 1 1 : K⸨X⸩) 0 :=
      ⟨ordGE_single_one, HahnSeries.coeff_single_of_ne (by norm_num)⟩
    have := (h1.add (regVal_C a)).sub (regVal_C μ)
    simpa using this
  exact ((regVal_C c).div (hu.pow k) (pow_ne_zero k (sub_ne_zero.2 h.symm))).1

/-- Uniqueness of partial fractions: the Laurent coefficients at a pole of a finite sum of simple
fractions with distinct poles are the coefficients of the simple fractions at that pole. -/
theorem ppCoeff_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (pnt : ι → K)
    (hinj : Set.InjOn pnt S) (n : ι → ℕ) (A : ι → ℕ → K) {i₀ : ι} (hi₀ : i₀ ∈ S) {j : ℕ}
    (hj : 1 ≤ j) :
    ppCoeff (∑ i ∈ S, ∑ k ∈ Finset.Icc 1 (n i),
        RatFunc.C (A i k) / (RatFunc.X - RatFunc.C (pnt i)) ^ k) (pnt i₀) j =
      if j ≤ n i₀ then A i₀ j else 0 := by
  unfold ppCoeff lcoeff
  rw [expandAt_eq, map_sum, HahnSeries.coeff_sum, Finset.sum_eq_single i₀]
  · rw [map_sum, HahnSeries.coeff_sum]
    simp only [expandHom_pole_same, HahnSeries.coeff_single]
    by_cases hjn : j ≤ n i₀
    · rw [if_pos hjn, Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        rw [if_neg (by omega)]
      · intro h
        exact absurd (Finset.mem_Icc.2 ⟨hj, hjn⟩) h
    · rw [if_neg hjn]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      have := (Finset.mem_Icc.1 hk).2
      omega
  · intro i hi hne
    rw [map_sum, HahnSeries.coeff_sum]
    apply Finset.sum_eq_zero
    intro k _
    have hne' : pnt i ≠ pnt i₀ := fun h => hne (hinj hi hi₀ h)
    exact (expandHom_pole_other hne' (A i k) k).coeff_eq_zero (by omega)
  · intro h
    exact absurd hi₀ h

/-- The pole order at a pole of a finite sum of simple fractions is at most the largest
exponent at that pole. -/
theorem poleOrder_sum_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (pnt : ι → K)
    (hinj : Set.InjOn pnt S) (n : ι → ℕ) (A : ι → ℕ → K) {i₀ : ι} (hi₀ : i₀ ∈ S) :
    poleOrder (∑ i ∈ S, ∑ k ∈ Finset.Icc 1 (n i),
        RatFunc.C (A i k) / (RatFunc.X - RatFunc.C (pnt i)) ^ k) (pnt i₀) ≤ n i₀ := by
  set f := ∑ i ∈ S, ∑ k ∈ Finset.Icc 1 (n i),
        RatFunc.C (A i k) / (RatFunc.X - RatFunc.C (pnt i)) ^ k with hf
  have hord : OrdGE (expandAt f (pnt i₀)) (-(n i₀ : ℤ)) := by
    rw [expandAt_eq, hf, map_sum]
    refine OrdGE.sum fun i hi => ?_
    rw [map_sum]
    refine OrdGE.sum fun k hk => ?_
    by_cases hii : i = i₀
    · subst hii
      rw [expandHom_pole_same]
      refine ordGE_iff.2 fun m hm => HahnSeries.coeff_single_of_ne ?_
      have := (Finset.mem_Icc.1 hk).2
      omega
    · have hne' : pnt i ≠ pnt i₀ := fun h => hii (hinj hi hi₀ h)
      exact (expandHom_pole_other hne' (A i k) k).mono (by omega)
  unfold poleOrder
  by_cases h0 : expandAt f (pnt i₀) = 0
  · rw [h0]; simp
  · unfold OrdGE at hord
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at hord
    have : -(n i₀ : ℤ) ≤ (expandAt f (pnt i₀)).order := by exact_mod_cast hord
    omega

end Virasoro
