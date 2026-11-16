import Virasoro.Proofs.Sec4Ising
import Virasoro.Statements.Sec11
import Virasoro.Cited

/-!
# Proposition 11.1 (identity insertion) from the generic recursion, and Proposition 6.2
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

theorem one_mem_oddsBelow {n : ℕ} (hn : 0 < n) : 1 ∈ oddsBelow n := by
  rw [oddsBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by norm_num⟩

/-- For `d = 0` the fusion polynomial vanishes: the factor with `k = l = 1` is zero. -/
theorem genP_zero {𝔽 : Type*} [Field 𝔽] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (b : 𝔽) :
    genP r s b 0 = 0 := by
  unfold genP
  refine Finset.prod_eq_zero (one_mem_oddsBelow hr) (Finset.prod_eq_zero (one_mem_oddsBelow hs) ?_)
  simp [lamSq]

/-- Proposition 11.1 from the generic recursion in the form consumed by the proof of
Theorem 4.3: for `d = 0`, `H_0 = 1` and `H_N(1/2,Δ,0) = 0` for `N ≥ 1`. -/
theorem prop_identity_verma (hrec : GenericRecursionUniform) : Stmt_prop_identity_verma := by
  classical
  have hc : kacC b0 = 1 / 2 := def_fixed_specialization_ising.1
  refine ⟨Hrat_zero _ _, fun N hN => ?_⟩
  have h := confluence_identity (K := ℂ) b0_ne_zero 0 hN
    (fun M h1 _ => germ_recursion hrec b0 0 M h1)
  rw [hc] at h
  rw [h]
  apply Finset.sum_eq_zero
  intro lam _
  apply Finset.sum_eq_zero
  intro k _
  have hA : Atilde b0 (0 : ℂ) N lam k = 0 := by
    unfold Atilde
    rw [HahnSeries.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    have hpos := labels_pos (mem_collClass.1 ha).1
    have hR : RG b0 (0 : ℂ) a = 0 := by
      unfold RG genR
      rw [map_zero, genP_zero a.1 a.2 hpos.1 hpos.2, mul_zero]
    unfold BG
    rw [hR, zero_mul, zero_mul, HahnSeries.coeff_zero]
  rw [hA, map_zero]
  exact ratFunc_zero_div _

example (hrec : GenericRecursionUniform) : Stmt_prop_identity_verma := prop_identity_verma hrec

end Virasoro
