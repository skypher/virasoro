import Virasoro.Proofs.PartialFractions
import Virasoro.Proofs.LargeWeightCore
import Virasoro.Proofs.EtaPartition
import Virasoro.Cited

/-!
# Theorem 4.2 from the Kac determinant and Lemma 4.1

By the Kac determinant formula the denominator of `F_M(c⋆,Δ,d)` splits with roots in
`Λ_M(b⋆)`, and by the degree comparison of Lemma 4.1 the numerator of `F_M - p(M)` has smaller
degree.  Hence `F_M - p(M)` is a finite sum of simple fractions with poles in `Λ_M(b⋆)`, and
`H_N = ∑ η_j F_{N-j}` (`N ≥ 1`) is the sum of its principal parts at the points of `Λ_N(b⋆)`.
-/

namespace Virasoro

open Polynomial

theorem labels_mono {M N : ℕ} (h : M ≤ N) : labels M ⊆ labels N := by
  intro a ha
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha ⊢
  omega

theorem Lam_mono {𝔽 : Type*} [Field 𝔽] {M N : ℕ} (h : M ≤ N) (b : 𝔽) : Lam M b ⊆ Lam N b := by
  classical
  unfold Lam
  exact Finset.image_subset_image (labels_mono h)

/-- The Shapovalov determinant over `ℂ(d)[Δ]` is the image of the determinant over `ℂ[Δ]`. -/
theorem gramPoly_det_ratC (c : ℂ) (M : ℕ) :
    (gramPoly (RatFunc.C c : Kd) M).det
      = Polynomial.map (RatFunc.C : ℂ →+* Kd) (gramPoly c M).det := by
  have h := map_detR (Polynomial.mapRingHom (RatFunc.C : ℂ →+* Kd)) (C c) (X : ℂ[X]) M
  simp only [coe_mapRingHom, map_C, map_X] at h
  exact h.symm

open Classical in
/-- `F_M(c⋆,Δ,d) - p(M)` is a finite sum of simple fractions with poles in `Λ_M(b⋆)`. -/
theorem isPoleSum_Frat_sub (hK : Cited_KacDeterminant) {b : ℂ} (hb : b ≠ 0) (M : ℕ) :
    IsPoleSum ((Lam M b).image fun lam => pt lam)
      (Frat (RatFunc.C (kacC b) : Kd) dvar M - (Fintype.card (Nat.Partition M) : RatFunc Kd)) := by
  classical
  obtain ⟨C₀, hC₀, hdet⟩ := hK b hb M
  set g : Label → Kd := fun a => pt (kacHL a b) with hg
  set e : Label → ℕ := fun a => Fintype.card (Nat.Partition (M - a.lvl)) with he
  set S : Finset Kd := (Lam M b).image fun lam => pt lam with hS
  have hSg : S = (labels M).image g := by
    rw [hS, Lam, Finset.image_image]
    rfl
  set m : Kd → ℕ := fun μ => ∑ a ∈ (labels M).filter (fun a => g a = μ), e a with hm
  set G : Kd[X] := ∏ μ ∈ S, (X - C μ) ^ m μ with hG
  set a₀ : Kd := RatFunc.C C₀ with ha₀
  have ha₀ne : a₀ ≠ 0 := (map_ne_zero_iff _ RatFunc.C_injective).2 hC₀
  have hdetK : (gramPoly (RatFunc.C (kacC b) : Kd) M).det = C a₀ * G := by
    rw [gramPoly_det_ratC, hdet, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    congr 1
    rw [hG, hSg, ← Finset.prod_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image_of_mem g ha)]
    refine Finset.prod_congr rfl fun μ _ => ?_
    rw [hm, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      ← (Finset.mem_filter.1 ha).2]
  set P : Kd[X] := Fnum (RatFunc.C (kacC b) : Kd) dvar M
    - (Fintype.card (Nat.Partition M) : Kd[X]) * (gramPoly (RatFunc.C (kacC b) : Kd) M).det
    with hP
  have hGdeg : G.natDegree ≤ ∑ μ ∈ S, m μ := by
    refine le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun μ _ => ?_)
    refine le_trans natDegree_pow_le ?_
    rw [natDegree_X_sub_C, mul_one]
  have hPd : DLt P (∑ μ ∈ S, m μ) := by
    have h1 := degree_Fnum_sub_lt (RatFunc.C (kacC b) : Kd) dvar M
    rw [hdetK] at h1
    have h2 : (C a₀ * G).degree ≤ ((∑ μ ∈ S, m μ : ℕ) : WithBot ℕ) :=
      le_trans degree_le_natDegree
        (WithBot.coe_le_coe.2 (le_trans (natDegree_C_mul_le _ _) hGdeg))
    rw [hP, hdetK]
    exact lt_of_lt_of_le h1 h2
  have hPd' : DLt (C a₀⁻¹ * P) (∑ μ ∈ S, m μ) := by
    by_cases h0 : P = 0
    · rw [h0, mul_zero]; exact dlt_zero _
    · exact dlt_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) (hPd.natDegree_lt h0))
  have key := isPoleSum_div S m (C a₀⁻¹ * P) hPd'
  have hG0 : algebraMap Kd[X] (RatFunc Kd) G ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective Kd[X] (RatFunc Kd))).2 ?_
    rw [hG]
    exact Finset.prod_ne_zero_iff.2 fun μ _ => pow_ne_zero _ (X_sub_C_ne_zero μ)
  have ha₀r : (RatFunc.C a₀ : RatFunc Kd) ≠ 0 := (map_ne_zero_iff _ RatFunc.C_injective).2 ha₀ne
  have heq : Frat (RatFunc.C (kacC b) : Kd) dvar M - (Fintype.card (Nat.Partition M) : RatFunc Kd)
      = algebraMap Kd[X] (RatFunc Kd) (C a₀⁻¹ * P) / algebraMap Kd[X] (RatFunc Kd) G := by
    rw [Frat, hP, hdetK]
    simp only [map_mul, map_sub, map_natCast, RatFunc.algebraMap_C, map_inv₀]
    field_simp
  rw [heq]
  exact key

/-- `H_N(c⋆,Δ,d)` is the sum of its principal parts at the points of `Λ_N(b⋆)`: the
derivation from the Kac determinant and the large-weight limit. -/
theorem HN_eq_sum_PP_of_kac (hK : Cited_KacDeterminant) {b : ℂ} (hb : b ≠ 0) {N : ℕ}
    (hN : 1 ≤ N) :
    HN (kacC b) N = ∑ lam ∈ Lam N b, PP (HN (kacC b) N) (pt lam) := by
  classical
  have hsum : IsPoleSum ((Lam N b).image fun lam => pt lam) (HN (kacC b) N) := by
    have h1 : HN (kacC b) N = ∑ j ∈ Finset.range (N + 1),
        RatFunc.C ((eta j : ℤ) : Kd) * (Frat (RatFunc.C (kacC b) : Kd) dvar (N - j)
          - (Fintype.card (Nat.Partition (N - j)) : RatFunc Kd)) := by
      have h2 : (∑ j ∈ Finset.range (N + 1),
          (eta j : RatFunc Kd) * (Fintype.card (Nat.Partition (N - j)) : RatFunc Kd)) = 0 := by
        have := congrArg (Int.cast : ℤ → RatFunc Kd) (eta_partition N)
        push_cast at this
        rw [this, if_neg (by omega)]
      rw [HN, Hrat, ← sub_zero (∑ j ∈ Finset.range (N + 1), _), ← h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_intCast]
      ring
    rw [h1]
    refine isPoleSum_sum _ _ fun j _ => ?_
    refine IsPoleSum.const_mul _ ((isPoleSum_Frat_sub hK hb (N - j)).mono ?_)
    exact Finset.image_subset_image (f := fun lam : ℂ => pt lam) (Lam_mono (Nat.sub_le N j) b)
  have h := hsum.eq_sum_PP
  rw [Finset.sum_image (fun x _ y _ hxy => RatFunc.C_injective hxy)] at h
  exact h

/-- Theorem 4.2, derived as in the paper from the Kac determinant formula and Lemma 4.1. -/
theorem thm_general_partial_fractions (hK : Cited_KacDeterminant) :
    Stmt_thm_general_partial_fractions :=
  thm_general_partial_fractions_of_sumPP fun _ hb _ hN => HN_eq_sum_PP_of_kac hK hb hN

example (hK : Cited_KacDeterminant) : Stmt_thm_general_partial_fractions :=
  thm_general_partial_fractions hK

end Virasoro
