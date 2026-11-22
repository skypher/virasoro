import Virasoro.Cited2
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.P2Sec10OrbitArith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Lemma 10.3 (structure and arithmetic of primitive BGG arrows), paper.tex l.2185–2286

Part (i) is cited in the paper (l.2232–2239).  Parts (ii)–(iv) follow l.2240–2285.
-/

namespace Virasoro

/-- `h'_{R,S}(t) = (1-R²)/4 - (1-S²)/(4t²)` (l.2273–2274). -/
theorem hT_hasDerivAt (R S : ℤ) {t₀ : ℂ} (ht : t₀ ≠ 0) :
    HasDerivAt (fun t : ℂ => hT R S t)
      ((1 - (R : ℂ) ^ 2) / 4 - (1 - (S : ℂ) ^ 2) / (4 * t₀ ^ 2)) t₀ := by
  have h1 : HasDerivAt (fun t : ℂ => (t + 1) ^ 2 - ((R : ℂ) * t + S) ^ 2)
      (2 * (t₀ + 1) - 2 * ((R : ℂ) * t₀ + S) * R) t₀ := by
    have a := ((hasDerivAt_id' t₀).add_const (1 : ℂ)).pow 2
    have b := (((hasDerivAt_id' t₀).const_mul (R : ℂ)).add_const (S : ℂ)).pow 2
    exact (a.sub b).congr_deriv (by simp <;> ring)
  have h2 : HasDerivAt (fun t : ℂ => 4 * t) 4 t₀ := by
    simpa using (hasDerivAt_id' t₀).const_mul (4 : ℂ)
  have h3 : HasDerivAt (fun t : ℂ => hT R S t) _ t₀ := h1.div h2 (by simpa using ht)
  exact h3.congr_deriv (by field_simp; ring)

variable {p p' r s : ℕ} {b : ℂ}

/-- `n⁺_k ≠ n⁻_k`: `n₀ ≠ 0` and `n₁ ≠ pp'` (l.2267–2270). -/
theorem nOrb_true_ne_false (hcop : Nat.Coprime p p') (hr0 : 0 < r) (hr : r < p)
    (hn1 : p' * r + p * s < p * p') (k : ℕ) :
    nOrb p p' r s true k ≠ nOrb p p' r s false k := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [nOrb_even_true, nOrb_even_false]
    intro h
    have h0 : (p' : ℤ) * r = p * s := by linarith
    have h1 := Int.eq_zero_of_abs_lt_dvd (coprime_two_dvd hcop h0).1
      (abs_lt.2 ⟨by omega, by omega⟩)
    omega
  · rw [nOrb_odd_true, nOrb_odd_false]
    intro h
    have hz : (p' : ℤ) * r + p * s < p * p' := by exact_mod_cast hn1
    linarith

/-- Lemma 10.3 from the cited Jantzen layers of the orbit (part (i)) and the cited
normalization identities (the value of `γ_{R,S}` in part (iii)).
Paper label: lem:bgg-arrows -/
theorem lem_bgg_arrows_of_cited (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations) :
    Stmt_lem_bgg_arrows := by
  intro p p' r s b hset
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hpz' : (0 : ℤ) < p' := by exact_mod_cast hp'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have ht0 : (-(p' : ℂ) / p) ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hb
    exact ht0 hb.symm
  refine ⟨ell_one_lt_two hr0 hr hs0 hs, fun ε k => ⟨hJ p p' r s b hset ε k, fun ε' => ?_, ?_⟩⟩
  · -- (ii) and (iii)
    -- existence from the consecutive-layer formulas (l.2246–2247)
    obtain ⟨R, S, hR, hS, hsum, hdiff, -, -, -⟩ := arrow_data hr0 hr hs0 hs ε k ε'
    -- (10.11)–(10.13) by reduction modulo `p`, `p'` and `0 < n_ν - |n_μ| < 2pp'` (l.2249–2262)
    obtain ⟨hcR, hcS⟩ := congr_of_reduce hcop hr0 hr hs0 hs (nOrb_mod ε k) hdiff
    have hsmall := small_of_gap hp hp' hsum hdiff (nOrb_gap hr0 hr hs0 hs hp hp' ε k ε').2
    have hRz : (0 : ℤ) < R := by exact_mod_cast hR
    have hSz : (0 : ℤ) < S := by exact_mod_cast hS
    have hnμ := nOrb_not_dvd hcop hr0 hr hs0 hs ε k
    have hμ : kacH R S b = muOrb p p' r s ε k := by
      rw [kacH_momWt hp hp' hb, muOrb]
      rcases hdiff with h | h
      · rw [h]
      · rw [h, momWt_neg]
    have hν : kacH (R : ℤ) (-(S : ℤ)) b = muOrb p p' r s ε' (k + 1) := by
      rw [kacH_momWt hp hp' hb, muOrb, ← hsum]
      congr 1
      ring
    refine ⟨R, S, hR, hS, arrowLabel_eq_of_not_dvd hp hp' hsum hdiff hnμ.2, hμ, hν, hsum, hdiff, ?_,
      mod_of_congr hcR, mod_of_congr hcS, min_le_of_congr hcR, min_le_of_congr hcS, hsmall,
      box_clause hp hp' hsmall, ?_⟩
    · -- uniqueness of the label (l.2242–2247)
      intro R' S' hR' hS' h1 h2
      rw [← hμ] at h1
      rw [← hν] at h2
      have d1 := (kacH_eq_iff hp hp' hb _ _ _ _).1 h1
      have d2 := (kacH_eq_iff hp hp' hb _ _ _ _).1 h2
      have a1 := mul_pos hpz' hR'
      have a2 := mul_pos hpz hS'
      have a3 := mul_pos hpz' hRz
      have a4 := mul_pos hpz hSz
      have hsumeq : (p' : ℤ) * R' + p * S' = p' * R + p * S := by
        rcases d2 with h | h
        · linarith
        · exfalso; linarith
      rcases d1 with h | h
      · have e1 : (p' : ℤ) * (R' - R) = 0 := by linarith
        have e2 : (p : ℤ) * (S' - S) = 0 := by linarith
        rcases mul_eq_zero.1 e1 with h' | h'
        · omega
        · rcases mul_eq_zero.1 e2 with h'' | h''
          · omega
          · exact ⟨by linarith, by linarith⟩
      · exfalso
        have e : (p' : ℤ) * R' = p * S := by linarith
        -- both signs would give `p' ∣ n_μ` (l.2244–2246)
        refine hnμ.2 ?_
        rcases hdiff with h | h
        · exact ⟨R - R', by linear_combination e - h⟩
        · exact ⟨R' - R, by linear_combination h - e⟩
    · -- `γ_{R,S}(b⋆) ≠ 0` (l.2262–2265)
      intro pc hpc1 hsing
      obtain ⟨-, -, -, -, hcross⟩ :=
        lem_regular_everywhere_of_cited hH R S hR hS pc hpc1 hsing b hb0
      have hfac : ∀ pq ∈ genAIndex R S, (pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹ ≠ 0 := by
        intro pq hpq h0
        simp only [genAIndex, Finset.mem_filter] at hpq
        have e : (pq.1 : ℂ) * b ^ 2 + pq.2 = ((pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹) * b := by
          field_simp
        rw [h0, zero_mul, hb] at e
        have h3 : (p' : ℂ) * pq.1 = p * pq.2 := by
          have e4 : (pq.1 : ℂ) * (-(p' : ℂ) / p) * p + pq.2 * p = 0 := by
            rw [← add_mul, e, zero_mul]
          have e5 : (pq.1 : ℂ) * (-(p' : ℂ) / p) * p = -(pq.1 * p') := by field_simp
          rw [e5] at e4
          linear_combination -e4
        have h4 : (p' : ℤ) * pq.1 = p * pq.2 := by exact_mod_cast h3
        obtain ⟨l, hl1, hl2⟩ := (coprime_ratio (p : ℤ) (p' : ℤ) hpz.ne'
          (Nat.isCoprime_iff_coprime.2 hcop) pq.1 pq.2).1 h4
        have hl : l ≠ 0 := by
          rintro rfl
          apply hpq.2.1
          ext <;> simp [hl1, hl2]
        refine box_clause hp hp' hsmall l hl ?_
        have e6 : (l * (p : ℤ), l * (p' : ℤ)) = pq := by
          ext <;> simp [hl1, hl2, mul_comm]
        rw [e6]
        exact hpq.1
      have hgen : genA R S b ≠ 0 := by
        unfold genA
        exact mul_ne_zero (by norm_num)
          (Finset.prod_ne_zero_iff.2 fun pq h => inv_ne_zero (hfac pq h))
      rw [hcross hfac]
      exact inv_ne_zero hgen
  · -- (iv)
    intro R₁ S₁ R₂ S₂ hl1 hl2
    obtain ⟨Ra, Sa, hRa, hSa, hsuma, hdiffa, hcRa, hcSa, -⟩ :=
      arrow_data hr0 hr hs0 hs ε k true
    obtain ⟨Rb, Sb, hRb, hSb, hsumb, hdiffb, hcRb, hcSb, -⟩ :=
      arrow_data hr0 hr hs0 hs ε k false
    rw [arrowLabel_eq hcop hp hp' hsuma hdiffa (not_dvd_of_congr hs0 hs hcSa)] at hl1
    rw [arrowLabel_eq hcop hp hp' hsumb hdiffb (not_dvd_of_congr hs0 hs hcSb)] at hl2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl2
    have hRaz : (0 : ℤ) < Ra := by exact_mod_cast hRa
    have hSaz : (0 : ℤ) < Sa := by exact_mod_cast hSa
    have hRbz : (0 : ℤ) < Rb := by exact_mod_cast hRb
    have hSbz : (0 : ℤ) < Sb := by exact_mod_cast hSb
    have a1 := mul_pos hpz' hRaz
    have a2 := mul_pos hpz hSaz
    have a3 := mul_pos hpz' hRbz
    have a4 := mul_pos hpz hSbz
    have hN := nOrb_true_ne_false (s := s) hcop hr0 hr hn1 (k + 1)
    have hnμ : nOrb p p' r s ε k ≠ 0 := by
      intro h0
      rw [h0, neg_zero, or_self] at hdiffa
      have e : (p' : ℤ) * Ra = p * Sa := by linarith
      exact not_dvd_of_congr hr0 hr hcRa (coprime_two_dvd hcop e).1
    have ma : ((p' : ℤ) * Ra - p * Sa) ^ 2 = nOrb p p' r s ε k ^ 2 := by
      rcases hdiffa with h | h <;> rw [h] <;> ring
    have mb : ((p' : ℤ) * Rb - p * Sb) ^ 2 = nOrb p p' r s ε k ^ 2 := by
      rcases hdiffb with h | h <;> rw [h] <;> ring
    refine ⟨?_, by linarith, by linarith, ?_, ?_⟩
    · -- distinct levels (l.2266–2270)
      intro h
      have hsq : nOrb p p' r s true (k + 1) ^ 2 = nOrb p p' r s false (k + 1) ^ 2 := by
        rw [← hsuma, ← hsumb]
        linear_combination ma - mb + 4 * (p : ℤ) * p' * h
      have e : (nOrb p p' r s true (k + 1) - nOrb p p' r s false (k + 1)) *
          (nOrb p p' r s true (k + 1) + nOrb p p' r s false (k + 1)) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.1 e with h' | h'
      · exact hN (by linarith)
      · linarith
    · -- `m₂n₂ - m₁n₁ ≠ 0` (l.2279–2282)
      rw [hsuma, hsumb]
      intro h
      rcases hdiffa with ha | ha <;> rcases hdiffb with hb' | hb' <;> rw [ha, hb'] at h
      · have e : nOrb p p' r s ε k *
            (nOrb p p' r s false (k + 1) - nOrb p p' r s true (k + 1)) = 0 := by
          linear_combination h
        rcases mul_eq_zero.1 e with h' | h'
        · exact hnμ h'
        · exact hN (by linarith)
      · have e : nOrb p p' r s ε k *
            (nOrb p p' r s false (k + 1) + nOrb p p' r s true (k + 1)) = 0 := by
          linear_combination -h
        rcases mul_eq_zero.1 e with h' | h'
        · exact hnμ h'
        · linarith
      · have e : nOrb p p' r s ε k *
            (nOrb p p' r s false (k + 1) + nOrb p p' r s true (k + 1)) = 0 := by
          linear_combination h
        rcases mul_eq_zero.1 e with h' | h'
        · exact hnμ h'
        · linarith
      · have e : nOrb p p' r s ε k *
            (nOrb p p' r s false (k + 1) - nOrb p p' r s true (k + 1)) = 0 := by
          linear_combination -h
        rcases mul_eq_zero.1 e with h' | h'
        · exact hnμ h'
        · exact hN (by linarith)
    · -- the transverse slope (10.14) (l.2271–2278)
      have d := (hT_hasDerivAt (Ra : ℤ) (Sa : ℤ) ht0).sub (hT_hasDerivAt (Rb : ℤ) (Sb : ℤ) ht0)
      refine d.congr_deriv ?_
      push_cast
      field_simp
      ring

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations) : Stmt_lem_bgg_arrows :=
  lem_bgg_arrows_of_cited hJ hH

end Virasoro
