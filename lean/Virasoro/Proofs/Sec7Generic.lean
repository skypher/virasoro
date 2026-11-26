import Virasoro.Proofs.Sec7FixedCharge

/-!
# Corollary 7.15 (generic charge)

As in the paper: if `b⋆²` is irrational, no `h_{g'}(b⋆)` equals `h_g(b⋆) + ℓ_g`
(Lemma 6.3), so every chain has a single label (`chainFn_single`), and
`c^{(k)}_{λ→μ,j} = R_a δ_a^{k-1+j}/j!` vanishes at `b⋆` unless `k = 1` and `j = 0`, since the
`R_a` are regular there.  The remaining terms are `R_a(b⋆)` times the coefficient of
`(Δ - μ)⁰` of `H_{N-ℓ_a}(c⋆,·)` at `μ = z_a(b⋆)`, which is not a Kac weight of level `N - ℓ_a`;
there the coefficient is the value (`evalAt_eq_lcoeff_zero`, with Theorem 4.2).
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section Local

variable {K : Type*} [Field K]

theorem pole_as_div (c a : K) (k : ℕ) :
    (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k : RatFunc K) =
      algebraMap K[X] (RatFunc K) (Polynomial.C c) /
        algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C a) ^ k) := by
  rw [map_pow, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem evalAt_pole {a z : K} (h : z ≠ a) (c : K) (k : ℕ) :
    evalAt z (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) = c / (z - a) ^ k := by
  rw [pole_as_div, evalAt_div z _ (by simp [sub_ne_zero.2 h])]
  simp

theorem regAt_poleK {a z : K} (h : z ≠ a) (c : K) (k : ℕ) :
    RegAt z (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) := by
  rw [pole_as_div]
  exact regAt_div z _ (by simp [sub_ne_zero.2 h])

/-- For a finite sum of simple fractions with poles away from `z`, the value at `z` is the
coefficient of `(Δ - z)⁰` of the Laurent expansion at `z`. -/
theorem evalAt_eq_lcoeff_zero {ι : Type*} (S : Finset ι) (pnt : ι → K) (n : ι → ℕ)
    (A : ι → ℕ → K) {z : K} (hz : ∀ i ∈ S, z ≠ pnt i) :
    evalAt z (∑ i ∈ S, ∑ k ∈ Finset.Icc 1 (n i),
        RatFunc.C (A i k) / (RatFunc.X - RatFunc.C (pnt i)) ^ k) =
      lcoeff (∑ i ∈ S, ∑ k ∈ Finset.Icc 1 (n i),
        RatFunc.C (A i k) / (RatFunc.X - RatFunc.C (pnt i)) ^ k) z 0 := by
  rw [evalAt_sum (fun i hi => RegAt.sum fun k _ => regAt_poleK (hz i hi) _ _), lcoeff_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [evalAt_sum (fun k _ => regAt_poleK (hz i hi) _ _), lcoeff_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 := (Finset.mem_Icc.1 hk).1
  have h := lcoeff_pole_other (hz i hi) (A i k) hk1 0
  simp only [Nat.cast_zero] at h
  rw [evalAt_pole (hz i hi), h, show 0 + (k - 1) + 1 = k by omega]
  simp only [pow_zero, add_zero, Nat.choose_self, Nat.cast_one, one_mul, mul_one_div]

end Local

section Germ

variable {K : Type} [Field K] [CharZero K]

/-- At an irrational base point no label starts where another ends (Lemma 6.3). -/
theorem labelsAt_shift_empty {bs : K} (hbs : bs ≠ 0) (hirr : SqIrrational bs) {a : Label}
    (ha1 : 0 < a.1) (ha2 : 0 < a.2) (D : ℕ) :
    labelsAt bs D (kacHL a bs + (a.lvl : K)) = ∅ := by
  ext g
  simp only [Finset.notMem_empty, iff_false]
  intro hg
  obtain ⟨hgl, hgw⟩ := (mem_labelsAt bs).1 hg
  have hp := pos_of_mem_labels hgl
  apply kacH_shift_ne hbs hirr (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
    (by exact_mod_cast ha1) (by exact_mod_cast ha2) (by exact_mod_cast hp.1)
    (by exact_mod_cast hp.2)
  have hcast : (((a.1 : ℤ) * (a.2 : ℤ) : ℤ) : K) = (a.lvl : K) := by
    simp [Label.lvl]
  rw [hcast]
  unfold kacHL at hgw
  rw [hgw]
  ring

/-- At an irrational base point every chain has a single label. -/
theorem chainFn_single {bs : K} (hbs : bs ≠ 0) (hirr : SqIrrational bs) (d lam : K)
    (D k j : ℕ) :
    chainFn bs d lam D k j = ∑ a ∈ labelsAt bs D lam,
      if a.lvl = D then RG bs d a * delG bs a ^ (k - 1) * (delG bs a ^ j / (j.factorial : K⸨X⸩))
        else 0 := by
  unfold chainFn
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨hal, haw⟩ := (mem_labelsAt bs).1 ha
  have hp := pos_of_mem_labels hal
  by_cases hD : a.lvl = D
  · rw [if_pos hD, if_pos hD]
  · rw [if_neg hD, if_neg hD, chainTail_eq, ← haw, labelsAt_shift_empty hbs hirr hp.1 hp.2,
      Finset.sum_empty, mul_zero]

/-- The values of the chain functions at an irrational base point. -/
theorem chainFn_single_coeff {bs : K} (hbs : bs ≠ 0) (hirr : SqIrrational bs) (d lam : K)
    (D k j : ℕ) (hk : 1 ≤ k) :
    (chainFn bs d lam D k j).coeff 0 = ∑ a ∈ labelsAt bs D lam,
      if a.lvl = D then (if k = 1 ∧ j = 0 then genR a.1 a.2 bs d else 0) else 0 := by
  rw [chainFn_single hbs hirr, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hD : a.lvl = D
  · rw [if_pos hD, if_pos hD]
    have hR := regVal_RG hbs hirr d a
    have hδ : RegVal (delG bs a) 0 :=
      ⟨(ordGE_deltaG_one hbs a).mono (by norm_num),
        (ordGE_deltaG_one hbs a).coeff_eq_zero (by norm_num)⟩
    have hf := regVal_natCast (K := K) j.factorial
    have hv := (hR.mul (hδ.pow (k - 1))).mul ((hδ.pow j).div hf
      (by exact_mod_cast Nat.factorial_ne_zero j))
    rw [hv.2]
    by_cases hkj : k = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hkj
      simp
    · rw [if_neg hkj]
      rcases not_and_or.1 hkj with h1 | h2
      · rw [zero_pow (by omega)]; ring
      · rw [zero_pow h2]; ring
  · rw [if_neg hD, if_neg hD, HahnSeries.coeff_zero]

end Germ

open Classical in
/-- Corollary 7.15 from the generic recursion in its uniform form. -/
theorem cor_fixed_charge_generic_of (hrec : GenericRecursionUniform) :
    Stmt_cor_fixed_charge_generic := by
  intro b hb hq N hN lam _ k hk J hJ
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  have hirr : SqIrrational b := hq
  have hirrK : SqIrrational (bsC b) := sqIrrational_map (RatFunc.C : ℂ →+* Kd) hirr
  have hpf := thm_general_partial_fractions_of_recursion hrec
  set G : Label → Kd := fun a => genR a.1 a.2 (bsC b) dvar with hG
  -- the classes over `ℂ(d)` and over `ℂ`
  have hLC : ∀ M, labelsAt (bsC b) M (pt lam) = collClass M b lam := by
    intro M
    ext a
    rw [mem_labelsAt, mem_collClass, bsC, kacHL_ratC]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, RatFunc.C_injective h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩
  have hcf : ∀ D j, (chainFnC b lam D k j).coeff 0 = ∑ a ∈ collClass D b lam,
      if a.lvl = D then (if k = 1 ∧ j = 0 then G a else 0) else 0 := by
    intro D j
    rw [← hLC D]
    exact chainFn_single_coeff hbs hirrK dvar (pt lam) D k j hk
  unfold fixedChargeRHS
  simp_rw [hcf]
  by_cases hk1 : k = 1
  · subst hk1
    rw [if_pos rfl]
    simp only [true_and]
    -- only `j = 0` contributes
    have hj0 : ∀ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
        (∑ a ∈ collClass n b lam, if a.lvl = n then (if j = 0 then G a else 0) else 0) *
          ((j.factorial : Kd) * lcoeff (HN (kacC b) (N - n)) (pt (lam + n)) j) =
        (∑ a ∈ collClass N b lam, if a.lvl = n then G a else 0) *
          lcoeff (HN (kacC b) (N - n)) (pt (lam + n)) 0 := by
      intro n hn
      have hnN : n ≤ N := (Finset.mem_Ioo.1 hn).2.le
      rw [Finset.sum_eq_single 0]
      · simp only [if_true, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero]
        congr 1
        apply Finset.sum_subset
        · intro a ha
          rw [mem_collClass] at ha ⊢
          refine ⟨?_, ha.2⟩
          have hl := ha.1
          simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hl ⊢
          exact ⟨⟨⟨hl.1.1.1, le_trans hl.1.1.2 hnN⟩, ⟨hl.1.2.1, le_trans hl.1.2.2 hnN⟩⟩,
            le_trans hl.2 hnN⟩
        · intro a ha hna
          rw [if_neg]
          intro hl
          apply hna
          rw [mem_collClass] at ha ⊢
          refine ⟨?_, ha.2⟩
          rw [← hl]
          exact mem_labels_self ha.1
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_range.2 hJ) h
    rw [Finset.sum_congr rfl hj0]
    -- regroup by labels
    have hreg : ∀ a ∈ collClass N b lam, (if a.lvl = N then G a else 0) +
        ∑ n ∈ Finset.Ioo 0 N, (if a.lvl = n then G a else 0) *
          lcoeff (HN (kacC b) (N - n)) (pt (lam + n)) 0 =
        G a * RatFunc.eval (RingHom.id Kd) (pt (kacHL a b + (a.lvl : ℂ)))
          (HN (kacC b) (N - a.lvl)) := by
      intro a ha
      obtain ⟨hal, haw⟩ := mem_collClass.1 ha
      have hp := pos_of_mem_labels hal
      have hle := lvl_le_of_mem_labels hal
      have hpos := lvl_pos_of_mem_labels hal
      rw [haw]
      by_cases hD : a.lvl = N
      · rw [if_pos hD, Finset.sum_eq_zero, add_zero, hD, Nat.sub_self, HN, Hrat_zero,
          RatFunc.eval_one, mul_one]
        intro n hn
        rw [if_neg (by have := (Finset.mem_Ioo.1 hn).2; omega), zero_mul]
      · rw [if_neg hD, zero_add]
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq (Finset.Ioo 0 N) a.lvl, if_pos (Finset.mem_Ioo.2 ⟨hpos, by omega⟩)]
        congr 1
        -- the coefficient of `(Δ - μ)⁰` is the value, `μ = λ + ℓ_a` not a Kac weight
        have hM : 1 ≤ N - a.lvl := by omega
        have hHN : HN (kacC b) (N - a.lvl) =
            ∑ lam' ∈ Lam (N - a.lvl) b, PP (HN (kacC b) (N - a.lvl)) (pt lam') :=
          ((hpf b hb).2.1 (N - a.lvl) hM).2.2.1
        have hz : ∀ lam' ∈ Lam (N - a.lvl) b, pt (lam + (a.lvl : ℂ)) ≠ pt lam' := by
          intro lam' hlam' heq
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hlam'
          have hgp := pos_of_mem_labels hg
          apply kacH_shift_ne hb hirr (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
            (by exact_mod_cast hp.1) (by exact_mod_cast hp.2) (by exact_mod_cast hgp.1)
            (by exact_mod_cast hgp.2)
          have h1 := RatFunc.C_injective heq
          have hcast : (((a.1 : ℤ) * (a.2 : ℤ) : ℤ) : ℂ) = (a.lvl : ℂ) := by
            simp [Label.lvl]
          rw [hcast]
          unfold kacHL at h1 haw
          rw [← h1, haw]
          ring
        rw [hHN]
        unfold PP
        exact (evalAt_eq_lcoeff_zero (Lam (N - a.lvl) b) (fun lam' => pt lam')
          (fun lam' => poleOrder (HN (kacC b) (N - a.lvl)) (pt lam'))
          (fun lam' k => ppCoeff (HN (kacC b) (N - a.lvl)) (pt lam') k) hz).symm
    rw [← Finset.sum_congr rfl hreg, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  · rw [if_neg hk1]
    simp [hk1]

/-- Corollary 7.15, from the two cited results (through Proposition 6.4 and Theorem 4.2).

Paper label: cor:fixed-charge-generic -/
theorem cor_fixed_charge_generic_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_cor_fixed_charge_generic :=
  cor_fixed_charge_generic_of (genericRecursionUniform hK hH)

end Virasoro
