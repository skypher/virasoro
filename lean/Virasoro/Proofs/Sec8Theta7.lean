import Virasoro.Proofs.Sec8Theta7Vals
import Virasoro.Proofs.Sec8NoDouble
import Virasoro.Proofs.TwoBranchD
import Virasoro.Proofs.Expand

/-!
# Theorem 8.5: the level-seven principal part at the Ising point

Proposition 7.7 is applied at `b₀ = 2i/√3`, `N = 7`, `λ = 1/2` with the branches
`κ₁ = (2,1)`, `τ₁ = (1,5)` and `κ₂ = (1,3)`, `τ₂ = (4,1)`.  The derivative terms are evaluated
through the jets of `𝒜`, `𝒫` and `h` at `b₀` (files `Jets`, `Sec8Jets`, `Sec8Theta7Vals`), which
gives `Θ₇ = T₁ + T₂` in the factored form (A.1).
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

/-! ### The pole order from a principal part with two terms -/

theorem coeff_expandHom_PP {K : Type*} [Field K] (f : RatFunc K) (a : K) (m : ℕ) (hm : 1 ≤ m) :
    (expandHom a (PP f a)).coeff (-(m : ℤ)) =
      if m ≤ poleOrder f a then ppCoeff f a m else 0 := by
  unfold PP
  rw [map_sum, HahnSeries.coeff_sum]
  simp only [expandHom_pole_same, HahnSeries.coeff_single, neg_inj, Nat.cast_inj]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_Icc, hm]

/-- If the principal part at `a` is `A₂/(Δ-a)² + A₁/(Δ-a)` with `A₂ ≠ 0`, the pole has order `2`. -/
theorem poleOrder_eq_two_of_PP {K : Type*} [Field K] (f : RatFunc K) (a A2 A1 : K) (hA : A2 ≠ 0)
    (h : PP f a = RatFunc.C A2 / (RatFunc.X - RatFunc.C a) ^ 2 +
      RatFunc.C A1 / (RatFunc.X - RatFunc.C a) ^ 1) :
    poleOrder f a = 2 := by
  have hR : ∀ m : ℕ, (expandHom a (PP f a)).coeff (-(m : ℤ)) =
      (if m = 2 then A2 else 0) + (if m = 1 then A1 else 0) := by
    intro m
    rw [h, map_add, expandHom_pole_same, expandHom_pole_same, HahnSeries.coeff_add,
      HahnSeries.coeff_single, HahnSeries.coeff_single]
    simp only [neg_inj, Nat.cast_inj]
  have h2 := coeff_expandHom_PP f a 2 (by norm_num)
  rw [hR 2] at h2
  simp only [if_true, show (2 : ℕ) ≠ 1 by norm_num, if_false, add_zero] at h2
  have hle : 2 ≤ poleOrder f a := by
    by_contra hlt
    rw [if_neg hlt] at h2
    exact hA h2
  rw [if_pos hle] at h2
  have hne := (ppCoeff_poleOrder_ne_zero f a ⟨2, by norm_num, h2 ▸ hA⟩).1
  by_contra hn
  have hgt : 2 < poleOrder f a := lt_of_le_of_ne hle (Ne.symm hn)
  have hn' := coeff_expandHom_PP f a (poleOrder f a) (by omega)
  rw [hR, if_pos le_rfl, if_neg hn, if_neg (by omega), add_zero] at hn'
  exact hne hn'.symm

/-! ### Values at `b₀` -/

theorem Pval_ne (r s : ℕ) : Pval r s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2 fun l _ =>
    mul_ne_zero (pval_ne k l 1) (pval_ne k l (-1))

theorem aM_E2 : algebraMap ℂ[X] Kd E2 = Pval 2 1 := by
  rw [Pval_21]
  simp only [E2, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

theorem aM_E3 : algebraMap ℂ[X] Kd E3 = Pval 1 3 := by
  rw [Pval_13]
  simp only [E3, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

theorem aM_P15 : algebraMap ℂ[X] Kd P15 = Pval 1 5 := by
  rw [Pval_15]
  simp only [P15, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

theorem aM_P41 : algebraMap ℂ[X] Kd P41 = Pval 4 1 := by
  rw [Pval_41]
  simp only [P41, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

/-- `Θ₇ = T₁ + T₂` in the factored form (A.1). -/
theorem theta7_eq :
    Tterm b0 (2, 1) (1, 5) + Tterm b0 (1, 3) (4, 1) = algebraMap ℂ[X] Kd Theta7 := by
  rw [Tterm_b0_split (2, 1) (1, 5) hne_21 hne_15 (by rw [hD_21, hD_15]; norm_num),
    Tterm_b0_split (1, 3) (4, 1) hne_13 hne_41 (by rw [hD_13, hD_41]; norm_num)]
  dsimp only
  rw [PsigP_21, PsigP_15, PsigP_13, PsigP_41, Pval_21, Pval_15, Pval_13, Pval_41, genAK_21,
    genAK_15, genAK_13, genAK_41, sigA_21, sigA_15, sigA_13, sigA_41, hD_21, hD_15, hD_13, hD_41,
    hE_21, hE_15, hE_13, hE_41]
  simp only [Theta7, map_mul, map_sub, map_neg, map_add, map_pow, map_ofNat, map_one, map_div₀,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  ring


/-! ### The hypotheses of Proposition 7.7 at `b₀`, `N = 7`, `λ = 1/2` -/

theorem kacHL_βd (a : Label) : kacHL a βd = ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : Kd) := by
  rw [show βd = RatFunc.C b0 from rfl, ← map_kacHL, kacHL_b0_cast]
  exact map_ratCast _ _

/-- An element with valuation `≥ 0`, zero constant term and nonzero linear term has order `1`. -/
theorem orderTop_eq_one_of {K : Type*} [Field K] {x : K⸨X⸩} (h : OrdGE x 0) (h0 : x.coeff 0 = 0)
    (h1 : x.coeff 1 ≠ 0) : x.orderTop = (1 : ℤ) := by
  have hx : x ≠ 0 := by
    intro hx; rw [hx] at h1; simp at h1
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx]
  congr 1
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1)
  by_contra hlt
  push Not at hlt
  have hc : x.coeff x.order ≠ 0 := fun h' => hx (HahnSeries.coeff_order_eq_zero.mp h')
  rcases lt_or_eq_of_le (show x.order ≤ 0 by omega) with hneg | hz
  · exact hc (h.coeff_eq_zero hneg)
  · rw [hz] at hc; exact hc h0

theorem zeta0_eq {κ τ : Label}
    (h : isingDelta (κ.1 : ℤ) (κ.2 : ℤ) + (κ.lvl : ℚ) - isingDelta (τ.1 : ℤ) (τ.2 : ℤ) = 0) :
    kacHL κ βd + (κ.lvl : Kd) - kacHL τ βd = 0 := by
  rw [kacHL_βd, kacHL_βd]
  have := congrArg (fun q : ℚ => (q : Kd)) h
  push_cast at this
  exact this

theorem twoBranchHyp_b0 {N : ℕ} {κ τ : Label}
    (hκ : ∀ pq ∈ genAIndex κ.1 κ.2, 4 * pq.1 ≠ 3 * pq.2)
    (hτ : ∀ pq ∈ genAIndex τ.1 τ.2, 4 * pq.1 ≠ 3 * pq.2) (hc : hD κ - hD τ ≠ 0)
    (hlvl : τ.lvl = N - κ.lvl) (hmem : τ ∈ labels (N - κ.lvl))
    (huniq : ∀ g ∈ labels (N - κ.lvl), isingKey g = isingKey κ + 48 * (κ.lvl : ℤ) ↔ g = τ)
    (hz : isingDelta (κ.1 : ℤ) (κ.2 : ℤ) + (κ.lvl : ℚ) - isingDelta (τ.1 : ℤ) (τ.2 : ℤ) = 0) :
    TwoBranchHyp b0 N κ τ := by
  refine ⟨hlvl, hmem, fun g hg => ?_, ?_, ?_, ?_⟩
  · rw [kacHL_b0_cast, kacHL_b0_cast, isingDelta_cast_shift_iff]
    exact huniq g hg
  · simpa [OrdGE] using (j1_RG κ hκ).1
  · simpa [OrdGE] using (j1_RG τ hτ).1
  · have Z := j2_zeta κ τ
    refine orderTop_eq_one_of Z.1 (by rw [Z.2.1]; exact zeta0_eq hz) ?_
    rw [Z.2.2.1]
    exact mul_ne_zero βd_ne_zero hc

theorem twoBranch_7a : TwoBranchHyp b0 7 (2, 1) (1, 5) :=
  twoBranchHyp_b0 hne_21 hne_15 (by rw [hD_21, hD_15]; norm_num) (by decide) (by decide)
    (by decide) (by norm_num [isingDelta, Label.lvl])

theorem twoBranch_7b : TwoBranchHyp b0 7 (1, 3) (4, 1) :=
  twoBranchHyp_b0 hne_13 hne_41 (by rw [hD_13, hD_41]; norm_num) (by decide) (by decide)
    (by decide) (by norm_num [isingDelta, Label.lvl])

theorem kacHL_21_b0 : kacHL (2, 1) b0 = 1 / 2 := by
  rw [kacHL_b0_cast]; norm_num [isingDelta]

theorem collClass_7_half : collClass 7 b0 (1 / 2) = {(2, 1), (1, 3)} := by
  classical
  rw [← kacHL_21_b0]
  unfold collClass
  rw [Finset.filter_congr (q := fun g : Label => isingKey g = isingKey (2, 1))
    (fun g _ => by rw [kacHL_b0_cast, kacHL_b0_cast, isingDelta_cast_eq_iff])]
  decide

theorem half_mem_Lam7 : (1 / 2 : ℂ) ∈ Lam 7 b0 := by
  classical
  unfold Lam
  exact Finset.mem_image.2 ⟨(2, 1), by decide, kacHL_21_b0⟩

/-! ### Theorem 8.5 -/

/-- Theorem 8.5 (`thm:level-seven-principal-part`). -/
theorem thm_level_seven_principal_part (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hJ : Cited_JantzenLayers) : Stmt_thm_level_seven_principal_part := by
  have hc : kacC b0 = 1 / 2 := def_fixed_specialization_ising.1
  have key := prop_two_branch hK hH b0 b0_ne_zero 7 (by norm_num) (1 / 2) half_mem_Lam7 (2, 1)
    (1, 3) (1, 5) (4, 1) (by decide) collClass_7_half twoBranch_7a twoBranch_7b
  have hPP := key.2
  have hQ1 : finitePart (kacC b0) (7 - Label.lvl (2, 1)) (kacHL (2, 1) b0 + ((Label.lvl (2, 1) : ℕ) : ℂ))
      = finitePart (1 / 2) 5 (5 / 2) := by
    rw [hc, kacHL_b0_cast]
    norm_num [isingDelta, Label.lvl]
  have hQ2 : finitePart (kacC b0) (7 - Label.lvl (1, 3)) (kacHL (1, 3) b0 + ((Label.lvl (1, 3) : ℕ) : ℂ))
      = finitePart (1 / 2) 4 (7 / 2) := by
    rw [hc, kacHL_b0_cast]
    norm_num [isingDelta, Label.lvl]
  simp only [germ0, germDot] at hPP
  rw [hQ1, hQ2, hc, (j1_RG (2, 1) hne_21).2.1, (j1_RG (1, 5) hne_15).2.1,
    (j1_RG (1, 3) hne_13).2.1, (j2_hG (2, 1)).2.2.1, (j2_hG (1, 3)).2.2.1,
    (j2_zeta (2, 1) (1, 5)).2.2.1] at hPP
  dsimp only at hPP
  rw [genAK_21, genAK_15, genAK_13, hD_21, hD_15, hD_13] at hPP
  have hA2 : (βd * (-3 / 2 : Kd) - βd * (9 / 4 : Kd)) * ((9 / 28 : Kd) * Pval 2 1) *
      ((-1 / 102375 : Kd) * Pval 1 5) / (βd * ((-3 / 2 : Kd) - (27 / 4 : Kd)))
      = -(algebraMap ℂ[X] Kd (E2 * P15)) / 700700 := by
    rw [map_mul, aM_E2, aM_P15]
    have := βd_ne_zero
    field_simp
    ring
  rw [hA2] at hPP
  unfold Stmt_thm_level_seven_principal_part
  dsimp only
  refine ⟨theta7_eq, ?_, ?_, fun N hN lam => (prop_no_earlier_double_pole hK hJ N hN lam).2.2.2⟩
  · rw [hPP, aM_E2, aM_E3]
    congr 2
    ring
  · refine poleOrder_eq_two_of_PP _ _ _ _ ?_ hPP
    rw [map_mul, aM_E2, aM_P15]
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (Pval_ne 2 1) (Pval_ne 1 5))) (by norm_num)

end Virasoro
