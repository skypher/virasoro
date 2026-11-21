import Virasoro.Proofs.Sec5SharpArith
import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Proofs.Sec6TwoTerm
import Virasoro.Proofs.TopTermPoly
import Virasoro.Proofs.LevelComp
import Virasoro.Statements.Sec6b

/-!
# Corollary 5.10 of `paper.tex` at 70bac53 from Theorem 5.9 and Propositions 6.7–6.9

The paper's proof (l.900–917): with `k = j_N(λ) ≥ 1`, the coefficient of `(Δ-λ)^{-k}` of `H_N` is
the right side `P_N` of (5.1) and the pole order is at most `k`, so it suffices that `P_N ≢ 0`.
* single-vector level `ℓ_k ≤ N < max(ℓ⁺_k, ℓ⁻_k)`: `P_N = (τ/γ) H_M(c⋆, μ, d)` with `τ ≠ 0` and
  `H_M(c⋆, μ, d) ≢ 0` (`H_0 = 1`; Proposition 6.8 for `M ≥ 1`);
* `N = max(ℓ⁺_k, ℓ⁻_k)`: the summand with `H_M`, `M ≥ 1`, vanishes at `d = 0` to order at least
  `k + 1` and the other to order exactly `k` (Lemma 6.5, Proposition 6.7);
* two-vector level: Proposition 6.9.
The case `k = 0` is the bound `poleOrder ≤ j_N(λ)` of Theorem 5.8.
-/

namespace Virasoro

open Verma Polynomial

/-- `H_M(c⋆, μ, d) ≢ 0` at `μ = λ + ℓ` of momentum form, from Proposition 6.8(iii). -/
theorem HpolyD_ne_zero_min (h68 : Stmt_prop_h13_nonvanishing) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {ℓ : ℕ} {m : ℤ}
    (hm : m ^ 2 = ((p' : ℤ) * r - (p : ℤ) * s) ^ 2 + 4 * p * p' * (ℓ : ℤ)) {M : ℕ}
    (hdet : (gram (kacC b) (kacH r s b + (ℓ : ℂ)) M).det ≠ 0) :
    HpolyD (kacC b) (kacH r s b + (ℓ : ℂ)) M ≠ 0 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · intro h0
    have h1 := eval_HpolyD (kacC b) (kacH r s b + (ℓ : ℂ)) 0 0
    rw [h0, Hval_level_zero] at h1
    simp at h1
  · obtain ⟨P, -, -, -, h3, -⟩ := h68
    have h4 := h3 p p' hp hp' hcop M m hM
    rw [kacC_min (by omega) (by omega) hb, kacH_min_add (by omega) (by omega) hb r s ℓ hm] at hdet ⊢
    have hg := gram_map (Rat.castHom ℂ) (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M
    have hd := (RingHom.map_det (Rat.castHom ℂ) (gram (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M)).symm
    have hq := (h4 fun h0 => hdet (by
      change (gram (Rat.castHom ℂ _) (Rat.castHom ℂ _) M).det = 0
      rw [hg]
      exact hd.trans (by rw [h0, map_zero]))).1
    change HpolyD (Rat.castHom ℂ _) (Rat.castHom ℂ _) M ≠ 0
    rw [HpolyD_map]
    exact (Polynomial.map_ne_zero_iff (Rat.castHom ℂ).injective).2 hq

/-- A single-vector level: only the summand of `ℓ₁` is present in (5.1). -/
theorem topTerm_single_ne (c lam : ℂ) (k : ℕ) {N ℓ₁ ℓ₂ : ℕ} (x₁ : Nat.Partition ℓ₁ → ℂ)
    (x₂ : Nat.Partition ℓ₂ → ℂ) (h1 : ℓ₁ ≤ N) (h2 : ¬ ℓ₂ ≤ N)
    (hτ : torusPolyForm c lam x₁ ≠ 0) (hγ : jform c lam ℓ₁ k x₁ x₁ ≠ 0)
    (hdet : ∀ M : ℕ, M ≤ N - ℓ₁ → (gram c (lam + (ℓ₁ : ℂ)) M).det ≠ 0)
    (hH : HpolyD c (lam + (ℓ₁ : ℂ)) (N - ℓ₁) ≠ 0) :
    topTerm c lam N ℓ₁ k x₁ + topTerm c lam N ℓ₂ k x₂ ≠ 0 := by
  have h0 : topTerm c lam N ℓ₂ k x₂ = 0 := by
    unfold topTerm
    rw [if_neg h2]
  rw [h0, add_zero, topTerm_eq_poly c lam k x₁ h1 hdet]
  exact (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] Kd)).2
    (mul_ne_zero (mul_ne_zero hτ (C_ne_zero.2 (inv_ne_zero hγ))) hH)

/-- The level `N = ℓ₁ > ℓ₂`: the summand of `ℓ₂` is `O(d^{k+1})`, the summand of `ℓ₁` has a nonzero
coefficient of `d^k`. -/
theorem topTerm_max_ne (c lam : ℂ) (k : ℕ) {ℓ₁ ℓ₂ : ℕ} (hlt : ℓ₂ < ℓ₁) (x₁ : Nat.Partition ℓ₁ → ℂ)
    (x₂ : Nat.Partition ℓ₂ → ℂ) (hγ : jform c lam ℓ₁ k x₁ x₁ ≠ 0)
    (hτ₁ : (torusPolyForm c lam x₁).coeff k ≠ 0)
    (hτ₂ : ∀ n < k, (torusPolyForm c lam x₂).coeff n = 0)
    (hdet : ∀ M : ℕ, M ≤ ℓ₁ - ℓ₂ → (gram c (lam + (ℓ₂ : ℂ)) M).det ≠ 0) :
    topTerm c lam ℓ₁ ℓ₁ k x₁ + topTerm c lam ℓ₁ ℓ₂ k x₂ ≠ 0 := by
  rw [topTerm_self, topTerm_eq_poly c lam k x₂ hlt.le hdet, ← map_add]
  refine (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] Kd)).2 fun h0 => ?_
  have h1 := congrArg (fun P : ℂ[X] => P.coeff k) h0
  simp only [coeff_add, coeff_zero] at h1
  rw [coeff_mul_low (fun n hn => by rw [Polynomial.coeff_mul_C, hτ₂ n hn, zero_mul])
    (HpolyD_coeff_zero_at (by omega) hdet) k le_rfl, add_zero, Polynomial.coeff_mul_C] at h1
  exact mul_ne_zero hτ₁ (inv_ne_zero hγ) h1

set_option maxHeartbeats 800000 in
/-- Corollary 5.10 from Theorem 5.8 (cited Jantzen layers), Theorem 5.9 (cited injectivity of the
singular embedding) and Propositions 6.7, 6.8, 6.9. -/
theorem cor_top_layer_sharp_of_props (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (h67 : Stmt_prop_layer_coefficients) (h68 : Stmt_prop_h13_nonvanishing)
    (h69 : Stmt_prop_two_term_criteria) : Stmt_cor_top_layer_sharp := by
  intro p p' r s b hset N hN
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  obtain ⟨wp, wm, hsing, hjan, -, hpole⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsing, hjan⟩
  have hle := (hpole N).2.2
  rcases Nat.eq_zero_or_pos (jDepth p p' r s N) with h0 | hk
  · rw [h0] at hle ⊢
    exact Nat.le_zero.1 hle
  obtain ⟨hN1, hN2⟩ := jDepth_range hp hp' hr hrp hs hsp hk
  generalize jDepth p p' r s N = k at hle hk hN1 hN2 ⊢
  have top := thm_top_layer_of_cited hI p p' r s b hset wp wm hT k N hk hN1 hN2
  have hcp : pbwCoord (ellPlus p p' r s k) (comp (ellPlus p p' r s k) (wp k)) = wp k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing k hk).1.2.1)
  have hcm : pbwCoord (ellMinus p p' r s k) (comp (ellMinus p p' r s k) (wm k)) = wm k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing k hk).2.2.1)
  obtain ⟨hpo, hpc⟩ := top.2.2.2 _ _ hcp hcm
  have tp := top.2.1 _ hcp
  have tm := top.2.2.1 _ hcm
  obtain ⟨l67p, l67m⟩ := h67 p p' r s b hset wp wm hT k hk
  have lp := l67p _ hcp
  have lm := l67m _ hcm
  obtain ⟨mp, hmp⟩ := ellPlus_momentum (p := p) (r := r) hsp k
  obtain ⟨mm, hmm⟩ := ellMinus_momentum (p := p) (s := s) hrp hsp k
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  refine poleOrder_eq_of_ppCoeff_ne hpo ?_
  rw [hpc]
  by_cases hpN : ellPlus p p' r s k ≤ N
  · by_cases hmN : ellMinus p p' r s k ≤ N
    · rcases lt_or_eq_of_le (max_le hpN hmN) with hlt' | heq
      · exact (h69 p p' r s b hset wp wm hT k N hk hlt' hN2 _ _ hcp hcm).1
      · rcases le_total (ellMinus p p' r s k) (ellPlus p p' r s k) with hmp' | hpm'
        · rw [max_eq_left hmp'] at heq
          subst heq
          exact topTerm_max_ne _ _ k (lt_of_le_of_ne hmp' hne.symm) _ _ (tp le_rfl).1 lp.2.2
            lm.1 (tm hmN).2.1
        · rw [max_eq_right hpm'] at heq
          subst heq
          rw [add_comm]
          exact topTerm_max_ne _ _ k (lt_of_le_of_ne hpm' hne) _ _ (tm le_rfl).1 lm.2.2
            lp.1 (tp hpN).2.1
    · exact topTerm_single_ne _ _ k _ _ hpN hmN
        (fun h0 => lp.2.2 (by rw [h0, coeff_zero])) (tp hpN).1 (tp hpN).2.1
        (HpolyD_ne_zero_min h68 hset hmp ((tp hpN).2.1 _ le_rfl))
  · have hmN : ellMinus p p' r s k ≤ N := by
      rcases min_le_iff.1 hN1 with h1 | h1
      · exact absurd h1 hpN
      · exact h1
    rw [add_comm]
    exact topTerm_single_ne _ _ k _ _ hmN hpN
      (fun h0 => lm.2.2 (by rw [h0, coeff_zero])) (tm hmN).1 (tm hmN).2.1
      (HpolyD_ne_zero_min h68 hset hmm ((tm hmN).2.1 _ le_rfl))

end Virasoro
