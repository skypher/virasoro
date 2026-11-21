import Virasoro.Proofs.Sec5TopNondeg
import Virasoro.Proofs.TopLayerCoeffF
import Virasoro.Proofs.TopLayerTrace

/-!
# Theorem 5.9 of `paper.tex` at 70bac53: the coefficient of `(Δ-λ)^{-k}` and the theorem

Paper.tex l.871–888.  For `ℓ_k ≤ N' ≤ N`, `[x^{-k}] F_{N'}(c⋆,λ+x,d)` is the trace of
`[x^{-k}] G_{N'}⁻¹ = ∑_± (γ^±)⁻¹ U^± G(μ^±)⁻¹ (U^±)ᵀ` against `ρ_{N'}`, which is
`∑_± τ^±/γ^± F_{N'-ℓ^±}(c⋆,μ^±,d)`; for `N' < ℓ_k` the pole order of `G_{N'}⁻¹` is below `k`.
Summing with the Euler coefficients gives equation (5.1).  The theorem takes the cited
injectivity of the singular embedding (Cited_VermaHomInjective).
-/

namespace Virasoro

open scoped LaurentSeries
open Verma Module Polynomial

/-- The sub-statement `Stmt_sub_top_layer_coeff` of Theorem 5.9, from the cited injectivity of
the singular embedding. -/
theorem sub_top_layer_coeff_of_cited (hI : Cited_VermaHomInjective) :
    Stmt_sub_top_layer_coeff := by
  classical
  intro p p' r s b hset wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  have hJ := hT.2 k hk
  have hsing := hT.1 k hk
  obtain ⟨hndp, hndm⟩ :=
    sub_top_layer_nondeg_of_cited hI p p' r s b hset' wp wm hT k N hk hN1 hN2
  have hjN : jDepth p p' r s N = k := jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2
  have hF : ∀ N' : ℕ, N' ≤ N →
      ppCoeff (FN (kacC b) N') (pt (kacH r s b)) k = algebraMap ℂ[X] Kd
        (blockPoly (kacC b) (kacH r s b) k (ellPlus p p' r s k) xp N' +
          blockPoly (kacC b) (kacH r s b) k (ellMinus p p' r s k) xm N') := by
    intro N' hN'
    have hpo := poleOrderInv_eq_jDepth hset' hT N'
    rw [ppCoeff_FN_top _ _ _ _ (by rw [hpo, ← hjN]; exact jDepth_mono p p' r s hN')]
    congr 1
    by_cases hlow : ellMin p p' r s k ≤ N'
    · have htop : ∃ s' : Multiset ℕ,
          IsSmith (gramLocal (kacC b) (kacH r s b) N') s' ∧ s'.sup = k := by
        obtain ⟨e, he⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH r s b) N')
        refine ⟨e, he, ?_⟩
        rw [← (smith_main he).2.2, hpo]
        exact jDepth_eq_of_range hp hp' hr hrp hs hsp hk hlow (lt_of_le_of_lt hN' hN2)
      have hχp : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s k) xp)
          (ellPlus p p' r s k) := by
        rw [hxp]
        exact hsing.1
      have hχm : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s k) xm)
          (ellMinus p p' r s k) := by
        rw [hxm]
        exact hsing.2
      have hJ' : jantzen (kacC b) (kacH r s b) k =
          negSpan (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s k) xp) ⊔
            negSpan (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s k) xm) := by
        rw [hxp, hxm]
        exact hJ
      rw [invCoeff_top_eq hI hχp hχm hne hJ' N' (N' - ellPlus p p' r s k)
        (N' - ellMinus p p' r s k) (by omega) (by omega) htop
        (fun hle => by
          rw [jv_pbwCoord]
          exact (hndp xp hxp (le_trans hle hN')).1)
        (fun hle => by
          rw [jv_pbwCoord]
          exact (hndm xm hxm (le_trans hle hN')).1)
        (fun hle => (hndp xp hxp (le_trans hle hN')).2 _ (by omega))
        (fun hle => (hndm xm hxm (le_trans hle hN')).2 _ (by omega))]
      simp only [Matrix.add_apply, C_add, add_mul, Finset.sum_add_distrib]
      rw [topBlock_trace _ _ k xp hχp N', topBlock_trace _ _ k xm hχm N']
    · have hlt' : jDepth p p' r s N' < k := by
        unfold jDepth
        rw [Finset.sup_lt_iff (by rw [Nat.bot_eq_zero]; omega : (⊥ : ℕ) < k)]
        intro i hi
        rw [Finset.mem_filter, Finset.mem_Icc] at hi
        by_contra hik
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hik)
        have := ellMin_mono (p := p) (p' := p') hr hrp hs hsp hk m
        have h2 : ellMin p p' r s (k + m) ≤ N' := hi.2
        omega
      have hzero : invCoeff (gramLocal (kacC b) (kacH r s b) N') (-(k : ℤ)) = 0 := by
        ext Y Y'
        have h1 := matOrdGE_inv (gramLocal (kacC b) (kacH r s b) N') Y Y'
        rw [hpo] at h1
        exact h1.coeff_eq_zero (by omega)
      have hlp : ¬ ellPlus p p' r s k ≤ N' := fun h1 => hlow (le_trans (min_le_left _ _) h1)
      have hlm : ¬ ellMinus p p' r s k ≤ N' := fun h1 => hlow (le_trans (min_le_right _ _) h1)
      rw [hzero, blockPoly, if_neg hlp, blockPoly, if_neg hlm]
      simp
  rw [ppCoeff_HN_eq, Finset.sum_congr rfl fun j _ => by rw [hF (N - j) (Nat.sub_le N j)]]
  simp only [map_add, mul_add, Finset.sum_add_distrib]
  rw [block_sum _ _ k _ xp N fun hle => (hndp xp hxp hle).2,
    block_sum _ _ k _ xm N fun hle => (hndm xm hxm hle).2]

/-- Theorem 5.9 from the cited injectivity of the singular embedding (paper.tex l.854–855). -/
theorem thm_top_layer_of_cited (hI : Cited_VermaHomInjective) : Stmt_thm_top_layer :=
  thm_top_layer_of_subs (sub_top_layer_nondeg_of_cited hI) (sub_top_layer_coeff_of_cited hI)

example (hI : Cited_VermaHomInjective) : Stmt_thm_top_layer := thm_top_layer_of_cited hI

end Virasoro
