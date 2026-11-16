import Virasoro.Proofs.Sec4Main

/-!
# Theorem 4.3 from the generic recursion: identity, moments, pole bound

`GenericRecursionUniform` is the form of Proposition 6.5 consumed by the proof of Theorem 4.3
(the recursion applied to the formal germ `b = b⋆ + t`).
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

theorem kacHL_ratC (a : Label) (b : ℂ) :
    kacHL a (RatFunc.C b : Kd) = RatFunc.C (kacHL a b) :=
  (map_kacHL (RatFunc.C : ℂ →+* Kd) a b).symm

theorem kacC_ratC (b : ℂ) : kacC (RatFunc.C b : Kd) = RatFunc.C (kacC b) :=
  (map_kacC (RatFunc.C : ℂ →+* Kd) b).symm

theorem collClass_ratC (N : ℕ) (b lam : ℂ) :
    collClass N (RatFunc.C b : Kd) (pt lam) = collClass N b lam := by
  classical
  ext a
  rw [mem_collClass, mem_collClass, kacHL_ratC]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, RatFunc.C_injective h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩

open Classical in
theorem Lam_ratC (N : ℕ) (b : ℂ) :
    Lam N (RatFunc.C b : Kd) = (Lam N b).image fun lam => pt lam := by
  unfold Lam
  rw [Finset.image_image]
  refine Finset.image_congr fun a _ => ?_
  simp [kacHL_ratC]

theorem bGerm_ne_zero_all {K : Type*} [Field K] (bs : K) : bGerm bs ≠ 0 := by
  intro h
  have h3 := congrArg (fun x : K⸨X⸩ => x.coeff 1) h
  simp [bGerm, HahnSeries.C, HahnSeries.coeff_single] at h3

/-- The generic recursion for the germ `b⋆ + t` over `K(Δ)⸨t⸩`, from its uniform form. -/
theorem germ_recursion {K : Type} [Field K] [CharZero K] (hrec : GenericRecursionUniform)
    (bs d : K) (M : ℕ) (hM : 1 ≤ M) :
    GenericRecursionAt (RatFunc K)⸨X⸩
      (mapL (algebraMap K (RatFunc K)) (bGerm bs))
      (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M := by
  obtain ⟨S, hSne, hS⟩ := hrec M hM
  refine hS (RatFunc K)⸨X⸩ _ _ ?_ ?_
  · exact (map_ne_zero (mapL (algebraMap K (RatFunc K)))).2 (bGerm_ne_zero_all bs)
  · intro P hP
    exact aeval_map_ne_zero _ (aeval_bGerm_ne_zero bs (hSne P hP))

/-- Equation (4.1) of Theorem 4.3, from the generic recursion. -/
theorem confluence_eq (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) {N : ℕ}
    (hN : 1 ≤ N) :
    HN (kacC b) N =
      ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (MhatC b N lam),
        poleTerm (AtildeC b N lam k) lam k := by
  classical
  have hbs : (RatFunc.C b : Kd) ≠ 0 := by simpa using hb
  have h := confluence_identity (K := Kd) hbs dvar hN
    (fun M h1 _ => germ_recursion hrec (RatFunc.C b : Kd) dvar M h1)
  unfold HN
  rw [← kacC_ratC, h, Lam_ratC, Finset.sum_image]
  · rfl
  · intro x _ y _ hxy
    exact RatFunc.C_injective hxy

/-- The collision moments are the partial-fraction coefficients, and the pole order is bounded
by the a priori bound. -/
theorem confluence_moments (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) {N : ℕ}
    (hN : 1 ≤ N) {lam : ℂ} (hlam : lam ∈ Lam N b) :
    (∀ k : ℕ, 1 ≤ k → AtildeC b N lam k = Astar b N lam k) ∧
      mstar b N lam ≤ MhatC b N lam := by
  classical
  have hbs : (RatFunc.C b : Kd) ≠ 0 := by simpa using hb
  have heq := confluence_eq hrec hb hN
  have hinj : Set.InjOn (fun lam : ℂ => pt lam) (Lam N b : Set ℂ) :=
    fun x _ y _ hxy => RatFunc.C_injective hxy
  refine ⟨fun k hk => ?_, ?_⟩
  · unfold Astar
    rw [heq]
    have := ppCoeff_sum (Lam N b) (fun lam : ℂ => pt lam) hinj (fun lam => MhatC b N lam)
      (fun lam k => AtildeC b N lam k) hlam hk
    unfold poleTerm
    rw [this]
    split_ifs with hle
    · rfl
    · exact Atilde_eq_zero hbs dvar N (pt lam) (by unfold MhatC at hle; omega)
  · unfold mstar
    rw [heq]
    exact poleOrder_sum_le (Lam N b) (fun lam : ℂ => pt lam) hinj (fun lam => MhatC b N lam)
      (fun lam k => AtildeC b N lam k) hlam

theorem HN_zero (c : ℂ) : HN c 0 = 1 := Hrat_zero _ _

/-- The coefficientwise `q`-series form of (4.1). -/
theorem confluence_series (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) :
    PowerSeries.mk (fun N => HN (kacC b) N) =
      1 + PowerSeries.mk (fun N =>
        if N = 0 then 0 else
          ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (MhatC b N lam),
            poleTerm (AtildeC b N lam k) lam k) := by
  ext N
  rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hN : N = 0
  · subst hN
    simp [HN_zero]
  · rw [if_neg hN, if_neg hN, zero_add]
    exact confluence_eq hrec hb (by omega)

end Virasoro
