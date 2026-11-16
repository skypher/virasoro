import Virasoro.Proofs.GenericResidue
import Virasoro.Proofs.PartialFractions
import Virasoro.Proofs.LargeWeightCore

/-!
# The partial-fraction expansion of `F_N` at generic `b`

`F_M(c(b),Δ,d) = p(M) + ∑_{ℓ_a ≤ M} ℛ_a(b,d) F_{M-ℓ_a}(c(b), h_a(b)+ℓ_a, d) / (Δ - h_a(b))`.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

open Classical in
/-- `F_M(c(b),Δ,d) - p(M)` is a finite sum of simple fractions with poles in `Λ_M(b)`, over
every field of characteristic zero. -/
theorem isPoleSum_Frat_sub_field (hK : Cited_KacDeterminant) {b : 𝔽} (hb : b ≠ 0) (d : 𝔽)
    (M : ℕ) :
    IsPoleSum (Lam M b) (Frat (kacC b) d M - (Fintype.card (Nat.Partition M) : RatFunc 𝔽)) := by
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hb M
  set g : Label → 𝔽 := fun a => kacHL a b with hg
  set e : Label → ℕ := fun a => Fintype.card (Nat.Partition (M - a.lvl)) with he
  set S : Finset 𝔽 := Lam M b with hS
  have hSg : S = (labels M).image g := rfl
  set m : 𝔽 → ℕ := fun μ => ∑ a ∈ (labels M).filter (fun a => g a = μ), e a with hm
  set G : 𝔽[X] := ∏ μ ∈ S, (X - C μ) ^ m μ with hG
  have hprod : kacProd b M = G := by
    rw [hG, hSg, kacProd, ← Finset.prod_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image_of_mem g ha)]
    refine Finset.prod_congr rfl fun μ _ => ?_
    rw [hm, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← (Finset.mem_filter.1 ha).2]
  rw [hprod] at hdet
  set P : 𝔽[X] := Fnum (kacC b) d M
    - (Fintype.card (Nat.Partition M) : 𝔽[X]) * (gramPoly (kacC b) M).det with hP
  have hGdeg : G.natDegree ≤ ∑ μ ∈ S, m μ := by
    refine le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun μ _ => ?_)
    refine le_trans natDegree_pow_le ?_
    rw [natDegree_X_sub_C, mul_one]
  have hPd : DLt P (∑ μ ∈ S, m μ) := by
    have h1 := degree_Fnum_sub_lt (kacC b) d M
    rw [hdet] at h1
    have h2 : (C C₀ * G).degree ≤ ((∑ μ ∈ S, m μ : ℕ) : WithBot ℕ) :=
      le_trans degree_le_natDegree
        (WithBot.coe_le_coe.2 (le_trans (natDegree_C_mul_le _ _) hGdeg))
    rw [hP, hdet]
    exact lt_of_lt_of_le h1 h2
  have hPd' : DLt (C C₀⁻¹ * P) (∑ μ ∈ S, m μ) := by
    by_cases h0 : P = 0
    · rw [h0, mul_zero]; exact dlt_zero _
    · exact dlt_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) (hPd.natDegree_lt h0))
  have key := isPoleSum_div S m (C C₀⁻¹ * P) hPd'
  have hG0 : algebraMap 𝔽[X] (RatFunc 𝔽) G ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).2 ?_
    rw [hG]
    exact Finset.prod_ne_zero_iff.2 fun μ _ => pow_ne_zero _ (X_sub_C_ne_zero μ)
  have hC₀r : (RatFunc.C C₀ : RatFunc 𝔽) ≠ 0 := (map_ne_zero_iff _ RatFunc.C_injective).2 hC₀
  have heq : Frat (kacC b) d M - (Fintype.card (Nat.Partition M) : RatFunc 𝔽)
      = algebraMap 𝔽[X] (RatFunc 𝔽) (C C₀⁻¹ * P) / algebraMap 𝔽[X] (RatFunc 𝔽) G := by
    rw [Frat, hP, hdet]
    simp only [map_mul, map_sub, map_natCast, RatFunc.algebraMap_C, map_inv₀]
    field_simp
  rw [heq]
  exact key

omit [CharZero 𝔽] in
theorem ordGE_of_poleOrder_le {f : RatFunc 𝔽} {a : 𝔽} {n : ℕ} (h : poleOrder f a ≤ n) :
    OrdGE (expandAt f a) (-(n : ℤ)) := by
  refine (ordGE_order (expandAt f a)).mono ?_
  unfold poleOrder at h
  have := Int.self_le_toNat (-(expandAt f a).order)
  omega

omit [CharZero 𝔽] in
/-- The principal part at a pole of order at most one. -/
theorem PP_of_simple {f : RatFunc 𝔽} {a : 𝔽} (h : poleOrder f a ≤ 1) :
    PP f a = RatFunc.C (ppCoeff f a 1) / (RatFunc.X - RatFunc.C a) := by
  unfold PP
  by_cases h0 : poleOrder f a = 0
  · rw [h0, ppCoeff_eq_zero_of_gt f a (by omega), map_zero, zero_div]
    simp
  · have h1 : poleOrder f a = 1 := by omega
    rw [h1]
    simp

theorem ppCoeff_sub_natCast (f : RatFunc 𝔽) (a : 𝔽) (n : ℕ) :
    ppCoeff (f - (n : RatFunc 𝔽)) a 1 = ppCoeff f a 1 := by
  unfold ppCoeff lcoeff
  rw [expandAt_eq, expandAt_eq, map_sub, map_natCast, HahnSeries.coeff_sub]
  have h0 : ((n : 𝔽⸨X⸩)).coeff (-((1 : ℕ) : ℤ)) = 0 :=
    (regVal_natCast n).1.coeff_eq_zero (by norm_num)
  rw [h0, sub_zero]

theorem poleOrder_sub_natCast_le {f : RatFunc 𝔽} {a : 𝔽} (n : ℕ) (h : poleOrder f a ≤ 1) :
    poleOrder (f - (n : RatFunc 𝔽)) a ≤ 1 := by
  refine poleOrder_le_of_ordGE ?_
  rw [expandAt_eq, map_sub, map_natCast]
  exact (ordGE_of_poleOrder_le h).sub ((regVal_natCast n).1.mono (by norm_num))

variable {hN : NormalizationIdentities} {N : ℕ} {b : 𝔽}

/-- The partial-fraction expansion of `F_M` at generic `b`. -/
theorem GenericAt.Frat_eq (hK : Cited_KacDeterminant) (hgen : GenericAt hN N b) {M : ℕ}
    (hM : M ≤ N) (d : 𝔽) :
    Frat (kacC b) d M = (Fintype.card (Nat.Partition M) : RatFunc 𝔽)
      + ∑ a ∈ labels M,
          RatFunc.C (genR a.1 a.2 b d *
              Fval (kacC b) d (kacHL a b + (a.lvl : 𝔽)) (M - a.lvl))
            / (RatFunc.X - RatFunc.C (kacHL a b)) := by
  classical
  have hsum := (isPoleSum_Frat_sub_field hK hgen.ne_zero d M).eq_sum_PP
  have himg : Lam M b = (labels M).image fun a => kacHL a b := rfl
  rw [himg, Finset.sum_image (fun a ha g hg h =>
    hgen.kacHL_inj (labels_subset hM ha) (labels_subset hM hg) h)] at hsum
  rw [← sub_eq_iff_eq_add', hsum]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨h1, h2⟩ := hgen.residue hK hM ha d
  rw [PP_of_simple (poleOrder_sub_natCast_le _ h1), ppCoeff_sub_natCast, h2]

end Virasoro
