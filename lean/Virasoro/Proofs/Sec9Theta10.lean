import Virasoro.Proofs.Sec8Theta7
import Virasoro.Proofs.Sec9Theta10Vals
import Virasoro.Statements.Sec9

/-!
# Theorem 9.4: the level-ten principal part at the Ising point

Proposition 7.7 at `b₀`, `N = 10`, `λ = h₀ = 1/16` with the branches `κ₁ = (1,2)`, `τ₁ = (4,2)`
and `κ₂ = (2,2)`, `τ₂ = (1,6)`; the derivative terms give `Θ₁₀` in the factored form (A.2).
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

theorem aM_P2 : algebraMap ℂ[X] Kd P2 = Pval 1 2 := by
  rw [Pval_12]
  simp only [P2, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

theorem aM_P4 : algebraMap ℂ[X] Kd P4 = Pval 2 2 := by
  rw [Pval_22]
  simp only [P4, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

theorem aM_P42 : algebraMap ℂ[X] Kd P42 = Pval 4 2 := by
  rw [Pval_42]
  simp only [P42, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

theorem aM_P16 : algebraMap ℂ[X] Kd P16 = Pval 1 6 := by
  rw [Pval_16]
  simp only [P16, map_mul, map_sub, map_ofNat, map_one, map_div₀, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  ring

/-- `Θ₁₀ = T₁ + T₂` in the factored form (A.2). -/
theorem theta10_eq :
    Tterm b0 (1, 2) (4, 2) + Tterm b0 (2, 2) (1, 6) = algebraMap ℂ[X] Kd Theta10 := by
  rw [Tterm_b0_split (1, 2) (4, 2) hne_12 hne_42 (by rw [hD_12, hD_42]; norm_num),
    Tterm_b0_split (2, 2) (1, 6) hne_22 hne_16 (by rw [hD_22, hD_16]; norm_num)]
  dsimp only
  rw [PsigP_12, PsigP_42, PsigP_22, PsigP_16, Pval_12, Pval_42, Pval_22, Pval_16, genAK_12,
    genAK_42, genAK_22, genAK_16, sigA_12, sigA_42, sigA_22, sigA_16, hD_12, hD_42, hD_22, hD_16,
    hE_12, hE_42, hE_22, hE_16]
  simp only [Theta10, map_mul, map_sub, map_neg, map_add, map_pow, map_ofNat, map_one, map_div₀,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  ring

theorem twoBranch_10a : TwoBranchHyp b0 10 (1, 2) (4, 2) :=
  twoBranchHyp_b0 hne_12 hne_42 (by rw [hD_12, hD_42]; norm_num) (by decide) (by decide)
    (by decide) (by norm_num [isingDelta, Label.lvl])

theorem twoBranch_10b : TwoBranchHyp b0 10 (2, 2) (1, 6) :=
  twoBranchHyp_b0 hne_22 hne_16 (by rw [hD_22, hD_16]; norm_num) (by decide) (by decide)
    (by decide) (by norm_num [isingDelta, Label.lvl])

theorem kacHL_12_b0 : kacHL (1, 2) b0 = 1 / 16 := by
  rw [kacHL_b0_cast]; norm_num [isingDelta]

theorem collClass_10_h0 : collClass 10 b0 (1 / 16) = {(1, 2), (2, 2)} := by
  classical
  rw [← kacHL_12_b0]
  unfold collClass
  rw [Finset.filter_congr (q := fun g : Label => isingKey g = isingKey (1, 2))
    (fun g _ => by rw [kacHL_b0_cast, kacHL_b0_cast, isingDelta_cast_eq_iff])]
  decide

theorem h0_mem_Lam10 : (1 / 16 : ℂ) ∈ Lam 10 b0 := by
  classical
  unfold Lam
  exact Finset.mem_image.2 ⟨(1, 2), by decide, kacHL_12_b0⟩

/-- Theorem 9.4 (`thm:level-ten-principal-part`). -/
theorem thm_level_ten_principal_part (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_thm_level_ten_principal_part := by
  have hc : kacC b0 = 1 / 2 := def_fixed_specialization_ising.1
  have key := prop_two_branch hK hH b0 b0_ne_zero 10 (by norm_num) (1 / 16) h0_mem_Lam10 (1, 2)
    (2, 2) (4, 2) (1, 6) (by decide) collClass_10_h0 twoBranch_10a twoBranch_10b
  have hPP := key.2
  have hQ1 : finitePart (kacC b0) (10 - Label.lvl (1, 2))
      (kacHL (1, 2) b0 + ((Label.lvl (1, 2) : ℕ) : ℂ)) = finitePart (1 / 2) 8 (33 / 16) := by
    rw [hc, kacHL_b0_cast]
    norm_num [isingDelta, Label.lvl]
  have hQ2 : finitePart (kacC b0) (10 - Label.lvl (2, 2))
      (kacHL (2, 2) b0 + ((Label.lvl (2, 2) : ℕ) : ℂ)) = finitePart (1 / 2) 6 (65 / 16) := by
    rw [hc, kacHL_b0_cast]
    norm_num [isingDelta, Label.lvl]
  have e12 : (RG βd dvar (1, 2)).coeff 0 = genA 1 2 βd * Pval 1 2 := (j1_RG (1, 2) hne_12).2.1
  have e42 : (RG βd dvar (4, 2)).coeff 0 = genA 4 2 βd * Pval 4 2 := (j1_RG (4, 2) hne_42).2.1
  have e22 : (RG βd dvar (2, 2)).coeff 0 = genA 2 2 βd * Pval 2 2 := (j1_RG (2, 2) hne_22).2.1
  simp only [germ0, germDot] at hPP
  have d12 : (hG βd (1, 2)).coeff 1 = βd * hD (1, 2) := (j2_hG (1, 2)).2.2.1
  have d22 : (hG βd (2, 2)).coeff 1 = βd * hD (2, 2) := (j2_hG (2, 2)).2.2.1
  have z1 : (zetaG b0 (1, 2) (4, 2)).coeff 1 = βd * (hD (1, 2) - hD (4, 2)) :=
    (j2_zeta (1, 2) (4, 2)).2.2.1
  rw [hQ1, hQ2, hc] at hPP
  simp only [e12, e42, e22, d12, d22, z1] at hPP
  rw [genAK_12, genAK_42, genAK_22, hD_12, hD_42, hD_22] at hPP
  unfold Stmt_thm_level_ten_principal_part
  dsimp only
  refine ⟨theta10_eq, ?_⟩
  rw [hPP, map_mul, aM_P2, aM_P4, aM_P42]
  congr 2
  · have := βd_ne_zero
    field_simp
    ring
  · ring

end Virasoro
