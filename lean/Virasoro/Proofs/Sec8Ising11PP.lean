import Virasoro.Proofs.Sec8Theta7
import Virasoro.Proofs.Sec9Leading

/-!
# Proposition 8.1 of `paper.tex` at 70bac53: the double pole at level eleven

Proposition 7.7 at `b₀ = 2i/√3`, `N = 11`, `λ = 0` with the branches `κ₁ = (1,1)`,
`τ₁ = (2,5)` and `κ₂ = (2,3)`, `τ₂ = (5,1)` gives the coefficient of `Δ^{-2}` of
`H₁₁(1/2,Δ,d)`:
`(ḣ_{1,1} - ḣ_{2,3})/(ḣ_{1,1} - ḣ_{2,5}) 𝒜_{1,1} 𝒜_{2,5} 𝒫_{1,1} 𝒫_{2,5}`, with
`ḣ_{1,1} : ḣ_{2,3} : ḣ_{2,5} = 0 : 3/4 : 21/4`, `𝒜_{1,1} = 1/2`,
`𝒜_{2,5} = -6561/176994082890625`, that is `𝒫_{1,1} 𝒫_{2,5} / γ₁₁` with
`γ₁₁ = -2477917160468750/6561`.
-/

namespace Virasoro

open Polynomial

/-- `𝒫_{r,s}(b₀,d)` over `ℂ(d)` is the product of fusion values `Pval r s`. -/
theorem genP_βd (r s : ℕ) : genP r s βd dvar = Pval r s := by
  unfold genP Pval pval lamSq
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => ?_
  have h2 := βd_sq
  rw [βd_inv]
  congr 1
  · push_cast
    linear_combination ((1 / 16 - ((k : Kd) - 3 * (l : Kd) / 4) ^ 2) / 4) * h2
  · push_cast
    linear_combination ((1 / 16 - ((k : Kd) + 3 * (l : Kd) / 4) ^ 2) / 4) * h2

theorem hne_11 : ∀ pq ∈ genAIndex 1 1, 4 * pq.1 ≠ 3 * pq.2 := by decide
theorem hne_25 : ∀ pq ∈ genAIndex 2 5, 4 * pq.1 ≠ 3 * pq.2 := by decide
theorem hne_23 : ∀ pq ∈ genAIndex 2 3, 4 * pq.1 ≠ 3 * pq.2 := by decide
theorem hne_51 : ∀ pq ∈ genAIndex 5 1, 4 * pq.1 ≠ 3 * pq.2 := by decide

theorem genAIndex_11 : genAIndex 1 1 = {(0, 1), (1, 0)} := by decide

theorem genAIndex_25 : genAIndex 2 5 = {(-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1),
    (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 1), (0, 2), (0, 3),
    (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
    (1, 5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)} := by
  decide

theorem genAK_11 : genA 1 1 βd = (1 / 2 : Kd) := by
  rw [genA_βd_prod, show (genAIndex 1 1).card = 2 from by decide, βd_inv_sq, genAIndex_11]
  simp [Finset.prod_insert]
  norm_num

theorem genAK_25 : genA 2 5 βd = (-6561 / 176994082890625 : Kd) := by
  rw [genA_βd_prod, show (genAIndex 2 5).card = 38 from by decide,
    show βd⁻¹ ^ 38 = (βd⁻¹ ^ 2) ^ 19 from by ring, βd_inv_sq, genAIndex_25]
  simp [Finset.prod_insert]
  norm_num

theorem hD_11 : hD (1, 1) = (0 : Kd) := by unfold hD; norm_num
theorem hD_25 : hD (2, 5) = (21 / 4 : Kd) := by unfold hD; norm_num
theorem hD_23 : hD (2, 3) = (3 / 4 : Kd) := by unfold hD; norm_num
theorem hD_51 : hD (5, 1) = (-12 : Kd) := by unfold hD; norm_num

theorem twoBranch_11a : TwoBranchHyp b0 11 (1, 1) (2, 5) :=
  twoBranchHyp_b0 hne_11 hne_25 (by rw [hD_11, hD_25]; norm_num) (by decide) (by decide)
    (by decide) (by norm_num [isingDelta, Label.lvl])

theorem twoBranch_11b : TwoBranchHyp b0 11 (2, 3) (5, 1) :=
  twoBranchHyp_b0 hne_23 hne_51 (by rw [hD_23, hD_51]; norm_num) (by decide) (by decide)
    (by decide) (by norm_num [isingDelta, Label.lvl])

theorem kacHL_11_b0 : kacHL (1, 1) b0 = 0 := by
  rw [kacHL_b0_cast]; norm_num [isingDelta]

theorem collClass_11_zero : collClass 11 b0 0 = {(1, 1), (2, 3)} := by
  classical
  rw [← kacHL_11_b0]
  unfold collClass
  rw [Finset.filter_congr (q := fun g : Label => isingKey g = isingKey (1, 1))
    (fun g _ => by rw [kacHL_b0_cast, kacHL_b0_cast, isingDelta_cast_eq_iff])]
  decide

theorem zero_mem_Lam11 : (0 : ℂ) ∈ Lam 11 b0 := by
  classical
  unfold Lam
  exact Finset.mem_image.2 ⟨(1, 1), by decide, kacHL_11_b0⟩

set_option maxRecDepth 100000 in
/-- The pole of `H₁₁(1/2,Δ,d)` at `Δ = 0` has order `2`, and the coefficient of `Δ^{-2}` is
`𝒫_{1,1}(b₀,d) 𝒫_{2,5}(b₀,d)/γ₁₁`. -/
theorem level_eleven_double_pole (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    poleOrder (HN (kacC b0) 11) (pt 0) = 2 ∧
    ppCoeff (HN (kacC b0) 11) (pt 0) 2 =
      genP 1 1 (RatFunc.C b0 : Kd) dvar * genP 2 5 (RatFunc.C b0 : Kd) dvar /
        RatFunc.C (-2477917160468750 / 6561 : ℂ) := by
  have key := prop_two_branch hK hH b0 b0_ne_zero 11 (by norm_num) 0 zero_mem_Lam11 (1, 1)
    (2, 3) (2, 5) (5, 1) (by decide) collClass_11_zero twoBranch_11a twoBranch_11b
  have hPP := key.2
  simp only [germ0, germDot] at hPP
  rw [(j1_RG (1, 1) hne_11).2.1, (j1_RG (2, 5) hne_25).2.1, (j2_hG (1, 1)).2.2.1,
    (j2_hG (2, 3)).2.2.1, (j2_zeta (1, 1) (2, 5)).2.2.1] at hPP
  dsimp only at hPP
  rw [genAK_11, genAK_25, hD_11, hD_23, hD_25] at hPP
  have hA2 : (βd * (0 : Kd) - βd * (3 / 4 : Kd)) * ((1 / 2 : Kd) * Pval 1 1) *
      ((-6561 / 176994082890625 : Kd) * Pval 2 5) / (βd * ((0 : Kd) - (21 / 4 : Kd)))
      = Pval 1 1 * Pval 2 5 / RatFunc.C (-2477917160468750 / 6561 : ℂ) := by
    rw [map_div₀, map_neg, map_ofNat, map_ofNat]
    have := βd_ne_zero
    field_simp
    ring
  rw [hA2] at hPP
  have hne : Pval 1 1 * Pval 2 5 / RatFunc.C (-2477917160468750 / 6561 : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (Pval_ne 1 1) (Pval_ne 2 5))
      ((map_ne_zero (RatFunc.C : ℂ →+* Kd)).2 (by norm_num))
  unfold poleTerm at hPP
  refine ⟨poleOrder_eq_two_of_PP _ _ _ _ hne hPP, ?_⟩
  rw [ppCoeff_two_of_PP _ _ _ _ hne hPP]
  rw [show (RatFunc.C b0 : Kd) = βd from rfl, genP_βd, genP_βd]

end Virasoro
