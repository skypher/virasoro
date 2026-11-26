import Virasoro.Statements.Sec7FixedCharge
import Virasoro.Proofs.Sec7Class
import Virasoro.Proofs.TwoBranchA
import Virasoro.Proofs.GenericH

/-!
# Lemma 7.8 (full moments)

As in the paper: the first assertion is the generic recursion at the weight `z_a(t)`
(`SG_eq_eval`), and the regularity of the full moments is uniqueness of partial fractions for the
coefficient of `t^m`, `m < 0`, of the grouped identity (the argument of `class_regular`, with the
truncation chosen beyond `k`).  The value at `t = 0` is Theorem 7.3.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section General

variable {K : Type} [Field K] [CharZero K]

/-- The generic recursion for the germ `b⋆ + t` over `K⸨t⸩`, from its uniform form. -/
theorem germ_recursion_self (hrec : GenericRecursionUniform) (bs d : K) (M : ℕ) (hM : 1 ≤ M) :
    GenericRecursionAt K⸨X⸩ (bGerm bs) (HahnSeries.C d) M := by
  obtain ⟨S, hSne, hS⟩ := hrec M hM
  exact hS K⸨X⸩ _ _ (bGerm_ne_zero_all bs) fun P hP => aeval_bGerm_ne_zero bs (hSne P hP)

/-- `S_{a,M}(t) = H_M(c(b), z_a(b), d)` as germs. -/
theorem SG_eq_evalAt (hrec : GenericRecursionUniform) {bs : K} (hbs : bs ≠ 0) (d : K) (M : ℕ)
    (a : Label) (ha1 : 0 < a.1) (ha2 : 0 < a.2) :
    SG bs d M a = evalAt (zG bs a) (Hrat (kacC (bGerm bs)) (HahnSeries.C d) M) := by
  have h := SG_eq_eval (ι := RingHom.id K) bs d M hbs
    (fun M' h1 _ => by simpa only [mapL_id] using germ_recursion_self hrec bs d M' h1)
    M le_rfl a ha1 ha2
  simpa only [mapL_id] using h

open Classical in
/-- The full moments have no negative powers of `t`. -/
theorem moment_coeff_neg {bs : K} (hbs : bs ≠ 0) (d : K) {N : ℕ} (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M)
    {lam : K} (hlam : lam ∈ Lam N bs) {k : ℕ} (hk : 1 ≤ k) {m : ℤ} (hm : m < 0) :
    (∑ a ∈ collClass N bs lam, BG bs d N a * deltaG bs lam a ^ (k - 1)).coeff m = 0 := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  set n₀ : ℕ := (labels N).sup (fun a => vhat bs d N a) + 1 + k with hn₀
  have hn : ∀ a ∈ labels N, vhat bs d N a < n₀ := by
    intro a ha
    have := Finset.le_sup (f := fun a => vhat bs d N a) ha
    omega
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
  have hpp := ppCoeff_sum (Lam N bs) (fun x : K => x) (fun x _ y _ h => h) (fun _ => n₀)
    (fun lam' k => ∑ a ∈ collClass N bs lam',
      (BG bs d N a * deltaG bs lam' a ^ (k - 1)).coeff m) hlam hk
  rw [hzero, if_pos (by omega)] at hpp
  have h0 : ppCoeff (0 : RatFunc K) lam k = 0 := by
    simp [ppCoeff, lcoeff, expandAt]
  rw [h0] at hpp
  rw [HahnSeries.coeff_sum]
  exact hpp.symm

end General

/-- Lemma 7.8 from the generic recursion in its uniform form. -/
theorem lem_full_moments_of (hrec : GenericRecursionUniform) : Stmt_lem_full_moments := by
  classical
  intro b hb
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  refine ⟨fun M a ha1 ha2 => SG_eq_evalAt hrec hbs dvar M a ha1 ha2,
    fun N hN lam hlam k hk => ⟨?_, ?_⟩⟩
  · have hlam' : pt lam ∈ Lam N (RatFunc.C b : Kd) := by
      rw [Lam_ratC]
      exact Finset.mem_image_of_mem _ hlam
    have h : OrdGE (fullMomentC b N lam k) 0 := ordGE_iff.2 fun m hm =>
      moment_coeff_neg hbs dvar hN (fun M h1 _ => germ_recursion hrec (bsC b) dvar M h1)
        hlam' hk hm
    simpa [OrdGE] using h
  · have h := (((thm_general_confluence hrec) b hb).1 N hN).2.1 lam hlam k hk
    exact h.1

/-- Lemma 7.8, from the two cited results (through Proposition 6.4).

Paper label: lem:full-moments -/
theorem lem_full_moments_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_lem_full_moments :=
  lem_full_moments_of (genericRecursionUniform hK hH)

end Virasoro
