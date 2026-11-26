import Virasoro.Proofs.Sec7Remainder
import Virasoro.Proofs.Reg2
import Virasoro.Proofs.Sec4PF

/-!
# Lemma 7.11: the remainder has no pole on `b = b⋆` near `Δ = μ`

The proof follows the paper.  Write `Reg^{(M)}_μ = ∑_{w_g ≠ μ} B_{g,M}/(Δ - h_g)` over the common
denominator `E = ∏_{w_g ≠ μ} (Δ - h_g(t))`, a polynomial in `Δ` over `K[[t]]` with
`E(0, μ) = ∏ (μ - w_g) ≠ 0`, and numerator `N = ∑_g B_{g,M} ∏_{g' ≠ g} (Δ - h_{g'})`, a polynomial
in `Δ` over `K((t))`.  In `K(Δ)((t))` (`substDelta`) the numerator is `E` times the sum of the groups
`G_{λ'}`, `λ' ≠ μ`, whose coefficients of `t^m` vanish for `m < 0` and give
`∑_k A⋆_{λ',k,M}/(Δ-λ')^k` at `m = 0` (Lemma 7.5, Corollary 7.6, Lemma 7.8).  So `N` has
coefficients in `K[[t]]`, and at `t = 0` the quotient is `∑_{λ' ≠ μ} PP_{λ'} H_M(c⋆,·)`, which is
`H_M(c⋆,·) - PP_μ H_M(c⋆,·)` by Theorem 4.2 (7.6).
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section Field

variable {F : Type*} [Field F]

theorem sum_div_eq_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (a q : ι → F)
    (hq : ∀ i ∈ S, q i ≠ 0) :
    ∑ i ∈ S, a i / q i = (∑ i ∈ S, a i * ∏ j ∈ S.erase i, q j) / ∏ i ∈ S, q i := by
  rw [eq_div_iff (Finset.prod_ne_zero_iff.2 hq), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_prod_erase S q hi]
  field_simp [hq i hi]

/-- Laurent coefficients of index `-k` below the pole order vanish. -/
theorem ppCoeff_eq_zero_of_lt {f : RatFunc F} {a : F} {k : ℕ} (hk : poleOrder f a < k) :
    ppCoeff f a k = 0 := by
  unfold ppCoeff lcoeff
  by_cases h0 : expandAt f a = 0
  · rw [h0, HahnSeries.coeff_zero]
  · apply HahnSeries.coeff_eq_zero_of_lt_order
    unfold poleOrder at hk
    have : -(k : ℤ) < (expandAt f a).order := by omega
    exact this

end Field

section General

variable {K : Type} [Field K] [CharZero K]

/-- Substituting a polynomial in `Δ` over `K((t))` into `K(Δ)((t))`. -/
noncomputable def substDelta : K⸨X⸩[X] →+* (RatFunc K)⸨X⸩ :=
  eval₂RingHom (mapL (algebraMap K (RatFunc K))) (HahnSeries.C RatFunc.X)

theorem phiL_C (a : K⸨X⸩) : substDelta (C a) = mapL (algebraMap K (RatFunc K)) a := by
  simp [substDelta]

theorem phiL_X : substDelta (X : K⸨X⸩[X]) = HahnSeries.C RatFunc.X := by
  simp [substDelta]

/-- The coefficient of `t^m` of the image is the polynomial of the coefficients of `t^m`. -/
theorem phiL_coeff (p : K⸨X⸩[X]) (m : ℤ) :
    (substDelta p).coeff m = algebraMap K[X] (RatFunc K)
      (∑ i ∈ p.support, Polynomial.monomial i ((p.coeff i).coeff m)) := by
  unfold substDelta
  rw [coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def, HahnSeries.coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    mapL_coeff, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]
  ring

theorem coeff_coeff_eq_zero_of_phiL {p : K⸨X⸩[X]} {m : ℤ} (h : (substDelta p).coeff m = 0) (i : ℕ) :
    (p.coeff i).coeff m = 0 := by
  rw [phiL_coeff] at h
  have h' := (map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).1 h
  have hi := congrArg (fun q : K[X] => q.coeff i) h'
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hi
  rw [Finset.sum_ite_eq'] at hi
  by_cases hs : i ∈ p.support
  · rw [if_pos hs] at hi
    exact hi
  · rw [Polynomial.notMem_support_iff.1 hs, HahnSeries.coeff_zero]

/-- A polynomial with coefficients in `K[[t]]` maps to a power series in `t`, with constant term
its restriction to `t = 0`. -/
theorem phiL_lift (P : (PowerSeries K)[X]) :
    OrdGE (substDelta (P.map toLS)) 0 ∧ (substDelta (P.map toLS)).coeff 0 = dnHom P := by
  refine ⟨ordGE_iff.2 fun m hm => ?_, ?_⟩
  · rw [phiL_coeff]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [Polynomial.coeff_map, (regVal_ofPowerSeries (P.coeff i)).1.coeff_eq_zero hm,
        map_zero], map_zero]
  · rw [phiL_coeff, dnHom_apply]
    congr 1
    ext j
    rw [Polynomial.finsetSum_coeff, Polynomial.coeff_map]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hs : j ∈ (P.map toLS).support
    · rw [if_pos hs, Polynomial.coeff_map, (regVal_ofPowerSeries (P.coeff j)).2]
    · rw [if_neg hs]
      have h0 := Polynomial.notMem_support_iff.1 hs
      rw [Polynomial.coeff_map] at h0
      have := (regVal_ofPowerSeries (P.coeff j)).2
      rw [h0, HahnSeries.coeff_zero] at this
      exact this

set_option maxHeartbeats 1000000 in
open Classical in
/-- `H_M(c⋆,·) - PP_μ H_M(c⋆,·)` is the sum of the principal parts at the other weights. -/
theorem Hrat_sub_PP {bs : K} (hbs : bs ≠ 0) (d : K) {M : ℕ} (hM : 1 ≤ M)
    (hrec : ∀ M', 1 ≤ M' → M' ≤ M →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M')
    (mu : K) {n₀ : ℕ} (hn₀ : ∀ w ∈ Lam M bs, Mhat bs d M w ≤ n₀) :
    Hrat (kacC bs) d M - PP (Hrat (kacC bs) d M) mu =
      ∑ w ∈ (Lam M bs).filter (fun w => w ≠ mu), ∑ k ∈ Finset.Icc 1 n₀,
        RatFunc.C (Atilde bs d M w k) / (RatFunc.X - RatFunc.C w) ^ k := by
  have hH : Hrat (kacC bs) d M = ∑ w ∈ Lam M bs, ∑ k ∈ Finset.Icc 1 n₀,
      RatFunc.C (Atilde bs d M w k) / (RatFunc.X - RatFunc.C w) ^ k := by
    rw [confluence_identity hbs d hM hrec]
    refine Finset.sum_congr rfl fun w hw => ?_
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, le_trans hk.2 (hn₀ w hw)⟩
    · intro k _ hk
      simp only [Finset.mem_Icc, not_and, not_le] at hk
      have hk1 : 1 ≤ k := by
        by_contra h
        push Not at h
        simp only [Finset.mem_Icc] at *
        omega
      rw [Atilde_eq_zero hbs d M w (hk hk1), map_zero, zero_div]
  have hinj : Set.InjOn (fun w : K => w) (Lam M bs) := fun x _ y _ h => h
  have hPP : PP (Hrat (kacC bs) d M) mu = ∑ w ∈ (Lam M bs).filter (fun w => ¬ w ≠ mu), ∑ k ∈ Finset.Icc 1 n₀,
      RatFunc.C (Atilde bs d M w k) / (RatFunc.X - RatFunc.C w) ^ k := by
    by_cases hmu : mu ∈ Lam M bs
    · have hfil : (Lam M bs).filter (fun w => ¬ w ≠ mu) = {mu} := by
        ext w
        simp only [Finset.mem_filter, not_not, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro rfl; exact ⟨hmu, rfl⟩
      rw [hfil, Finset.sum_singleton]
      have hpp : ∀ k, 1 ≤ k →
          ppCoeff (Hrat (kacC bs) d M) mu k = if k ≤ n₀ then Atilde bs d M mu k else 0 := by
        intro k hk
        rw [hH]
        exact ppCoeff_sum (Lam M bs) (fun w => w) hinj (fun _ => n₀) (Atilde bs d M) hmu hk
      have hpo : poleOrder (Hrat (kacC bs) d M) mu ≤ n₀ := by
        rw [hH]
        exact poleOrder_sum_le (Lam M bs) (fun w => w) hinj (fun _ => n₀) (Atilde bs d M) hmu
      unfold PP
      apply Finset.sum_subset_zero_on_sdiff
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        exact ⟨hk.1, le_trans hk.2 hpo⟩
      · intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le] at hk
        have h0 := hpp k hk.1.1
        rw [if_pos hk.1.2, ppCoeff_eq_zero_of_lt (hk.2 hk.1.1)] at h0
        rw [← h0, map_zero, zero_div]
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [hpp k hk.1, if_pos (le_trans hk.2 hpo)]
    · have hfil : (Lam M bs).filter (fun w => ¬ w ≠ mu) = ∅ := by
        ext w
        simp only [Finset.mem_filter, not_not, Finset.notMem_empty, iff_false, not_and]
        rintro hw rfl
        exact hmu hw
      rw [hfil, Finset.sum_empty]
      have hpo : poleOrder (Hrat (kacC bs) d M) mu = 0 := by
        apply poleOrder_eq_zero_of
        intro k hk
        unfold ppCoeff lcoeff
        rw [hH, expandAt_eq, map_sum, HahnSeries.coeff_sum]
        refine Finset.sum_eq_zero fun w hw => ?_
        rw [map_sum, HahnSeries.coeff_sum]
        refine Finset.sum_eq_zero fun k' _ => ?_
        have hne : w ≠ mu := fun h => hmu (h ▸ hw)
        exact (expandHom_pole_other hne _ k').coeff_eq_zero (by omega)
      unfold PP
      rw [hpo, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
  rw [hPP, hH, ← Finset.sum_filter_add_sum_filter_not (Lam M bs) (fun w => w ≠ mu)]
  ring

set_option maxHeartbeats 1000000 in
open Classical in
/-- Lemma 7.11 over an arbitrary coefficient field, in the form `Reg = P/E` with `P, E`
polynomials in `Δ` over `K[[t]]`, `E(0, μ) ≠ 0`, and restriction to `t = 0` equal to
`H_M(c⋆,·) - PP_μ H_M(c⋆,·)`. -/
theorem reg_two {bs : K} (hbs : bs ≠ 0) (d : K) {M : ℕ} (hM : 1 ≤ M)
    (hrec : ∀ M', 1 ≤ M' → M' ≤ M →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M')
    (mu : K) :
    ∃ P E : (PowerSeries K)[X], (E.map red0).eval mu ≠ 0 ∧
      (∑ g ∈ (labels M).filter (fun g => kacHL g bs ≠ mu),
        RatFunc.C (BG bs d M g) / (RatFunc.X - RatFunc.C (hG bs g))) = upHom P / upHom E ∧
      Hrat (kacC bs) d M - PP (Hrat (kacC bs) d M) mu = dnHom P / dnHom E := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  set S := (labels M).filter (fun g => kacHL g bs ≠ mu) with hS
  set n₀ : ℕ := (labels M).sup (fun g => vhat bs d M g) +
    (Lam M bs).sup (fun w => Mhat bs d M w) + 1 with hn₀def
  have hvn : ∀ a ∈ labels M, vhat bs d M a < n₀ := by
    intro a ha
    have := Finset.le_sup (f := fun g => vhat bs d M g) ha
    omega
  have hMn : ∀ w ∈ Lam M bs, Mhat bs d M w ≤ n₀ := by
    intro w hw
    have := Finset.le_sup (f := fun w => Mhat bs d M w) hw
    omega
  -- the germs `h_g(t)` as power series
  have hh : ∀ g : Label, ∃ q : PowerSeries K, toLS q = hG bs g ∧ red0 q = kacHL g bs := by
    intro g
    obtain ⟨q, hq, hq0⟩ := exists_ofPowerSeries (regVal_hG hbs g).1
    exact ⟨q, hq.symm, by rw [hq0, (regVal_hG hbs g).2]⟩
  choose hq hhq hhq0 using hh
  set E : (PowerSeries K)[X] := ∏ g ∈ S, (X - C (hq g)) with hE
  set Nl : K⸨X⸩[X] := ∑ g ∈ S, C (BG bs d M g) * ∏ g' ∈ S.erase g, (X - C (hG bs g'))
    with hNl
  have hEmap : E.map toLS = ∏ g ∈ S, (X - C (hG bs g)) := by
    rw [hE, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hhq]
  have hE0 : (E.map red0).eval mu ≠ 0 := by
    rw [hE, Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun g hg => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C, hhq0]
    exact sub_ne_zero.2 (Ne.symm (Finset.mem_filter.1 hg).2)
  -- the denominators in `K(Δ)((t))` do not vanish
  have hz : ∀ g ∈ S, (HahnSeries.C RatFunc.X : (RatFunc K)⸨X⸩) - mapL ι (hG bs g) ≠ 0 := by
    intro g _ heq
    have h1 : mapL ι (deltaG bs (kacHL g bs) g) =
        mapL ι (hG bs g) - HahnSeries.C (RatFunc.C (kacHL g bs)) := by
      rw [deltaG, map_sub, mapL_C, hι, RatFunc.algebraMap_eq_C]
    have h0 : HahnSeries.C (RatFunc.X - RatFunc.C (kacHL g bs)) -
        mapL ι (deltaG bs (kacHL g bs) g) = 0 := by
      rw [h1, map_sub]
      rw [sub_eq_zero] at heq
      rw [← heq]
      ring
    have hc := congrArg (fun x : (RatFunc K)⸨X⸩ => x.coeff 0) h0
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero] at hc
    rw [((ordGE_deltaG_one hbs g).mapL (ι := ι)).coeff_eq_zero (by norm_num), sub_zero] at hc
    have : (HahnSeries.C (RatFunc.X - RatFunc.C (kacHL g bs)) : (RatFunc K)⸨X⸩).coeff 0 =
        RatFunc.X - RatFunc.C (kacHL g bs) := (regVal_C _).2
    rw [this] at hc
    exact ratFunc_X_sub_C_ne_zero _ hc
  have hphiE : substDelta (E.map toLS) = ∏ g ∈ S, (HahnSeries.C RatFunc.X - mapL ι (hG bs g)) := by
    rw [hEmap, map_prod]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [map_sub, phiL_X, phiL_C]
  have hphiN : substDelta Nl = ∑ g ∈ S, mapL ι (BG bs d M g) *
      ∏ g' ∈ S.erase g, (HahnSeries.C RatFunc.X - mapL ι (hG bs g')) := by
    rw [hNl, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, phiL_C, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun g' _ => ?_
    rw [map_sub, phiL_X, phiL_C]
  set G : (RatFunc K)⸨X⸩ := ∑ g ∈ S, mapL ι (BG bs d M g) /
      (HahnSeries.C RatFunc.X - mapL ι (hG bs g)) with hG'
  have hNG : substDelta Nl = substDelta (E.map toLS) * G := by
    rw [hphiN, hphiE, hG', sum_div_eq_prod S _ _ hz, mul_div_cancel₀]
    exact Finset.prod_ne_zero_iff.2 hz
  -- the groups `G_{λ'}`
  have hmaps : ∀ g ∈ S, kacHL g bs ∈ (Lam M bs).filter (fun w => w ≠ mu) := by
    intro g hg
    obtain ⟨hgl, hgw⟩ := Finset.mem_filter.1 hg
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hgl, hgw⟩
  have hgroups : G = ∑ w ∈ (Lam M bs).filter (fun w => w ≠ mu),
      ∑ g ∈ collClass M bs w, mapL ι (BG bs d M g) /
        (HahnSeries.C RatFunc.X - mapL ι (hG bs g)) := by
    rw [hG', ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hwmu : w ≠ mu := (Finset.mem_filter.1 hw).2
    have hfib : S.filter (fun g => kacHL g bs = w) = collClass M bs w := by
      ext g
      simp only [hS, Finset.mem_filter, mem_collClass]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hwmu⟩, h3⟩
    rw [hfib]
  have hGo : OrdGE G 0 := by
    refine ordGE_iff.2 fun m hm => ?_
    rw [hgroups, HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun w hw => ?_
    exact class_regular hbs d hM hrec (Finset.mem_filter.1 hw).1 hm
  have hG0 : G.coeff 0 = ∑ w ∈ (Lam M bs).filter (fun w => w ≠ mu), ∑ k ∈ Finset.Icc 1 n₀,
      RatFunc.C (Atilde bs d M w k) / (RatFunc.X - RatFunc.C w) ^ k := by
    rw [hgroups, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [class_coeff hbs d M w (le_refl 0) hvn]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold Atilde
    rw [HahnSeries.coeff_sum]
  -- the numerator has coefficients in `K[[t]]`
  obtain ⟨hEo, hE0'⟩ := phiL_lift E
  have hNl0 : ∀ i, OrdGE (Nl.coeff i) 0 := by
    intro i
    refine ordGE_iff.2 fun m hm => coeff_coeff_eq_zero_of_phiL ?_ i
    rw [hNG]
    have := hEo.mul hGo
    exact this.coeff_eq_zero (by simpa using hm)
  obtain ⟨P, hP⟩ : ∃ P : (PowerSeries K)[X], P.map toLS = Nl := by
    have hlift : Nl ∈ Polynomial.lifts toLS := by
      refine (Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_
      obtain ⟨q, hq', -⟩ := exists_ofPowerSeries (hNl0 i)
      exact ⟨q, hq'.symm⟩
    exact (Polynomial.mem_lifts _).1 hlift
  refine ⟨P, E, hE0, ?_, ?_⟩
  · -- `Reg = P/E` in `K((t))(Δ)`
    rw [upHom_apply, upHom_apply, hP, hEmap, hNl]
    have hq0 : ∀ g ∈ S, (RatFunc.X - RatFunc.C (hG bs g) : RatFunc K⸨X⸩) ≠ 0 :=
      fun g _ => ratFunc_X_sub_C_ne_zero _
    rw [sum_div_eq_prod S _ _ hq0, map_sum, map_prod]
    congr 1
    · refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, map_prod, RatFunc.algebraMap_C]
      congr 1
      refine Finset.prod_congr rfl fun g' _ => ?_
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    · refine Finset.prod_congr rfl fun g _ => ?_
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  · -- the restriction to `t = 0`
    rw [Hrat_sub_PP hbs d hM hrec mu hMn, ← hG0]
    have hP0 := (phiL_lift P).2
    rw [hP] at hP0
    have h0 : (substDelta Nl).coeff 0 = (substDelta (E.map toLS)).coeff 0 * G.coeff 0 := by
      rw [hNG]
      have hr1 : RegVal (substDelta (E.map toLS)) ((substDelta (E.map toLS)).coeff 0) := ⟨hEo, rfl⟩
      have hr2 : RegVal G (G.coeff 0) := ⟨hGo, rfl⟩
      exact (hr1.mul hr2).2
    rw [hP0, hE0'] at h0
    rw [h0, mul_div_cancel_left₀ _ (dnHom_ne_zero hE0)]

end General

open Classical in
/-- Lemma 7.11 from the generic recursion in its uniform form. -/
theorem lem_regular_remainder_of (hrec : GenericRecursionUniform) :
    Stmt_lem_regular_remainder := by
  intro b hb M hM mu
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  have hfil : (labels M).filter (fun g => kacHL g b ≠ mu) =
      (labels M).filter (fun g => kacHL g (bsC b) ≠ pt mu) := by
    ext g
    simp only [Finset.mem_filter, bsC, kacHL_ratC, pt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (RatFunc.C_injective h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (by rw [h])⟩
  have hHN : HN (kacC b) M = Hrat (kacC (bsC b)) dvar M := by
    rw [HN, bsC, kacC_ratC]
  obtain ⟨P, E, hE0, h1, h2⟩ := reg_two hbs dvar hM
    (fun M' h1 _ => germ_recursion hrec (bsC b) dvar M' h1) (pt mu)
  refine ⟨regC_eq hrec hb hM mu, ⟨P, E, hE0, ?_, ?_⟩, fun j => ⟨phiRemC_eq_lcoeff hrec hb hM mu j, ?_⟩⟩
  · rw [regC_eq hrec hb hM mu, hfil, h1, upHom_apply, upHom_apply]
  · rw [hHN, h2, dnHom_apply, dnHom_apply]
  · have h := phiRem_regular hbs dvar hM (fun M' h1 _ => germ_recursion hrec (bsC b) dvar M' h1)
      (pt mu) j
    have h1' : OrdGE (phiRemC b M mu j) 0 := h.1
    refine ⟨by simpa [OrdGE] using h1', ?_⟩
    rw [hHN]
    exact h.2

/-- Lemma 7.11, from the two cited results (through Proposition 6.4 and Theorem 4.2).

Paper label: lem:regular-remainder -/
theorem lem_regular_remainder_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_lem_regular_remainder :=
  lem_regular_remainder_of (genericRecursionUniform hK hH)

end Virasoro
