import Virasoro.Proofs.Sec4Poly

/-!
# Corollary 7.6 (classwise regularity) and Proposition 6.5 from its uniform form
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section General

variable {K : Type} [Field K] [CharZero K]

open Classical in
/-- Coefficients of `t^m`, `m ≤ 0`, of a class sum, as a finite sum of simple fractions. -/
theorem class_coeff {bs : K} (hbs : bs ≠ 0) (d : K) (N : ℕ) (lam : K) {m : ℤ} (hm : m ≤ 0)
    {n₀ : ℕ} (hn : ∀ a ∈ labels N, vhat bs d N a < n₀) :
    (∑ a ∈ collClass N bs lam, mapL (algebraMap K (RatFunc K)) (BG bs d N a) /
        (HahnSeries.C (RatFunc.X : RatFunc K) -
          mapL (algebraMap K (RatFunc K)) (hG bs a))).coeff m =
      ∑ k ∈ Finset.Icc 1 n₀,
        RatFunc.C (∑ a ∈ collClass N bs lam,
          (BG bs d N a * deltaG bs lam a ^ (k - 1)).coeff m) / (RatFunc.X - RatFunc.C lam) ^ k := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  rw [HahnSeries.coeff_sum]
  have hterm : ∀ a ∈ collClass N bs lam,
      (mapL ι (BG bs d N a) / (HahnSeries.C (RatFunc.X : RatFunc K) - mapL ι (hG bs a))).coeff m =
        ∑ j ∈ Finset.range n₀, RatFunc.C ((BG bs d N a * deltaG bs lam a ^ j).coeff m) /
          (RatFunc.X - RatFunc.C lam) ^ (j + 1) := by
    intro a ha
    obtain ⟨haL, hlam⟩ := mem_collClass.1 ha
    have h1 : mapL ι (deltaG bs lam a) = mapL ι (hG bs a) - HahnSeries.C (RatFunc.C lam) := by
      rw [deltaG, map_sub, mapL_C, hι, RatFunc.algebraMap_eq_C]
    have h2 : (HahnSeries.C (RatFunc.X - RatFunc.C lam) : (RatFunc K)⸨X⸩) =
        HahnSeries.C RatFunc.X - HahnSeries.C (RatFunc.C lam) := map_sub _ _ _
    have hsplit : HahnSeries.C (RatFunc.X : RatFunc K) - mapL ι (hG bs a) =
        HahnSeries.C (RatFunc.X - RatFunc.C lam) - mapL ι (deltaG bs lam a) := by
      rw [h1, h2]; ring
    have hδ : OrdGE (deltaG bs lam a) 1 := by rw [← hlam]; exact ordGE_deltaG_one hbs a
    have hlt : m < -((vhat bs d N a : ℕ) : ℤ) + (n₀ : ℕ) := by
      have : ((vhat bs d N a : ℕ) : ℤ) < (n₀ : ℕ) := by exact_mod_cast hn a haL
      linarith
    rw [hsplit, pole_support ι _ (ratFunc_X_sub_C_ne_zero _) _ _ hδ (ordGE_BG bs d N a) m n₀ hlt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hι, RatFunc.algebraMap_eq_C]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm,
    ← sum_range_succ_eq_Icc (fun k => RatFunc.C (∑ a ∈ collClass N bs lam,
      (BG bs d N a * deltaG bs lam a ^ (k - 1)).coeff m) / (RatFunc.X - RatFunc.C lam) ^ k) n₀]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.sum_div, Nat.add_sub_cancel]

open Classical in
/-- Corollary 7.6 over an arbitrary coefficient field: each class sum is a power series in `t`. -/
theorem class_regular {bs : K} (hbs : bs ≠ 0) (d : K) {N : ℕ} (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M)
    {lam : K} (hlam : lam ∈ Lam N bs) {m : ℤ} (hm : m < 0) :
    (∑ a ∈ collClass N bs lam, mapL (algebraMap K (RatFunc K)) (BG bs d N a) /
        (HahnSeries.C (RatFunc.X : RatFunc K) -
          mapL (algebraMap K (RatFunc K)) (hG bs a))).coeff m = 0 := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  set n₀ : ℕ := (labels N).sup (fun a => vhat bs d N a) + 1 with hn₀
  have hn : ∀ a ∈ labels N, vhat bs d N a < n₀ := by
    intro a ha
    have := Finset.le_sup (f := fun a => vhat bs d N a) ha
    omega
  -- the total sum has no negative powers of `t`
  have hz : ∀ a ∈ labels N, HahnSeries.C (RatFunc.X : RatFunc K) ≠ mapL ι (hG bs a) := by
    intro a _ heq
    have h1 : mapL ι (deltaG bs (kacHL a bs) a) =
        mapL ι (hG bs a) - HahnSeries.C (RatFunc.C (kacHL a bs)) := by
      rw [deltaG, map_sub, mapL_C, hι, RatFunc.algebraMap_eq_C]
    have h0 : HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) -
        mapL ι (deltaG bs (kacHL a bs) a) = 0 := by
      rw [h1, ← heq, map_sub]; ring
    have hc := congrArg (fun x : (RatFunc K)⸨X⸩ => x.coeff 0) h0
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero] at hc
    rw [((ordGE_deltaG_one hbs a).mapL (ι := ι)).coeff_eq_zero (by norm_num), sub_zero] at hc
    have : (HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) : (RatFunc K)⸨X⸩).coeff 0 =
        RatFunc.X - RatFunc.C (kacHL a bs) := (regVal_C _).2
    rw [this] at hc
    exact ratFunc_X_sub_C_ne_zero _ hc
  have htot : (∑ a ∈ labels N, mapL ι (BG bs d N a) /
      (HahnSeries.C (RatFunc.X : RatFunc K) - mapL ι (hG bs a))).coeff m = 0 := by
    rw [← grouped_at bs d N hbs hN hrec hz]
    exact (regVal_Hrat_germ bs d hbs N).1.coeff_eq_zero hm
  -- regroup by classes and use uniqueness of partial fractions for the zero function
  have hmaps : ∀ a ∈ labels N, kacHL a bs ∈ Lam N bs := fun a ha =>
    Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, HahnSeries.coeff_sum] at htot
  have hzero : ∑ lam' ∈ Lam N bs, ∑ k ∈ Finset.Icc 1 n₀,
      RatFunc.C (∑ a ∈ collClass N bs lam',
        (BG bs d N a * deltaG bs lam' a ^ (k - 1)).coeff m) / (RatFunc.X - RatFunc.C lam') ^ k =
        0 := by
    rw [← htot]
    refine Finset.sum_congr rfl fun lam' _ => ?_
    exact (class_coeff hbs d N lam' hm.le hn).symm
  rw [class_coeff hbs d N lam hm.le hn]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_Icc.1 hk
  have hpp := ppCoeff_sum (Lam N bs) (fun x : K => x) (fun x _ y _ h => h) (fun _ => n₀)
    (fun lam' k => ∑ a ∈ collClass N bs lam',
      (BG bs d N a * deltaG bs lam' a ^ (k - 1)).coeff m) hlam hk'.1
  rw [hzero, if_pos hk'.2] at hpp
  have h0 : ppCoeff (0 : RatFunc K) lam k = 0 := by
    simp [ppCoeff, lcoeff, expandAt]
  rw [h0] at hpp
  rw [← hpp, map_zero, zero_div]

end General

/-- Corollary 7.6 (`cor:class-regular`) from the generic recursion in the form consumed by the
proof of Theorem 4.3. -/
theorem cor_class_regular (hrec : GenericRecursionUniform) : Stmt_cor_class_regular := by
  classical
  intro b hb N hN lam hlam m hm
  have hbs : (RatFunc.C b : Kd) ≠ 0 := by simpa using hb
  have hlam' : pt lam ∈ Lam N (RatFunc.C b : Kd) := by
    rw [Lam_ratC]
    exact Finset.mem_image_of_mem _ hlam
  have h := class_regular hbs dvar hN
    (fun M h1 _ => germ_recursion hrec (RatFunc.C b : Kd) dvar M h1) hlam' hm
  rw [collClass_ratC] at h
  exact h

example (hrec : GenericRecursionUniform) : Stmt_cor_class_regular := cor_class_regular hrec

/-- The uniform form of the generic recursion implies Proposition 6.5 as stated. -/
theorem prop_generic_recursion_of_uniform (hrec : GenericRecursionUniform) :
    Stmt_prop_generic_recursion := by
  classical
  intro N hN
  obtain ⟨S, hSne, hS⟩ := hrec N hN
  refine ⟨insert 0 (S.biUnion fun P => (P.map (algebraMap ℚ ℂ)).roots.toFinset), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact isAlgebraic_zero
    · obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
      rw [Multiset.mem_toFinset, mem_roots (Polynomial.map_ne_zero (hSne P hP))] at hxP
      exact ⟨P, hSne P hP, by rwa [IsRoot, eval_map, ← aeval_def] at hxP⟩
  · intro b hb
    have hb0 : b ≠ 0 := fun h => hb (by rw [h]; exact Finset.mem_insert_self _ _)
    refine hS Kd (RatFunc.C b) dvar (by simpa using hb0) fun P hP => ?_
    have hne : aeval b P ≠ 0 := by
      intro h0
      apply hb
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨P, hP, ?_⟩)
      rw [Multiset.mem_toFinset, mem_roots (Polynomial.map_ne_zero (hSne P hP)), IsRoot, eval_map,
        ← aeval_def]
      exact h0
    exact aeval_map_ne_zero (RatFunc.C : ℂ →+* Kd) hne

example (hrec : GenericRecursionUniform) : Stmt_prop_generic_recursion :=
  prop_generic_recursion_of_uniform hrec

end Virasoro
