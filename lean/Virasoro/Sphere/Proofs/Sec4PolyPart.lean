import Virasoro.Sphere.Proofs.Sec4PsiDeg
import Virasoro.Sphere.Proofs.Sec4ConflFinal

/-!
# Sphere paper Theorem 4.7 (iii): the polynomial part of `ℬ_N`

`sphere/paper.tex` l.1385–1388 and l.1421–1422: by equation (2.8),
`ℬ_N = ψ_N(c,Δ,Δ_i) + ∑_{m=1}^N ψ_{N-m}(c,Δ+m,Δ_i) H_m`, where `ψ_r` has degree `r` in `Δ`
and `H_m`, `m ≥ 1`, is a sum of principal parts (`deg P_m < deg det G_m`, Theorem 3.1).  Hence
`ℬ_N` is a polynomial of degree exactly `N` plus the sum of its principal parts at `Λ_N(b⋆)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

section Local

variable {𝔽 : Type*} [Field 𝔽]

/-- The principal part as a sum up to any bound on the pole order. -/
theorem PP_eq_sum_of_le (f : RatFunc 𝔽) (a : 𝔽) {n : ℕ} (h : poleOrder f a ≤ n) :
    PP f a = ∑ k ∈ Finset.Icc 1 n, RatFunc.C (ppCoeff f a k) / (RatFunc.X - RatFunc.C a) ^ k := by
  unfold PP
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right h) fun k hk hk' => ?_
  have hgt : poleOrder f a < k := by
    simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
    exact hk' hk.1
  rw [ppCoeff_eq_zero_of_gt f a hgt, map_zero, zero_div]

end Local

section Field

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- Subtracting a polynomial does not change a principal part. -/
theorem PP_sub_poly (f : RatFunc 𝔽) (q : 𝔽[X]) (a : 𝔽) :
    PP (f - algebraMap 𝔽[X] (RatFunc 𝔽) q) a = PP f a := by
  have hc : ∀ k : ℕ, 1 ≤ k →
      ppCoeff (f - algebraMap 𝔽[X] (RatFunc 𝔽) q) a k = ppCoeff f a k := by
    intro k hk
    unfold ppCoeff lcoeff
    rw [expandAt_eq, expandAt_eq, map_sub, HahnSeries.coeff_sub]
    have h0 := (regVal_of_regAt (regAt_algebraMap a q)).1.coeff_eq_zero
      (show -(k : ℤ) < 0 by omega)
    rw [h0, sub_zero]
  rw [PP_eq_sum_of_le _ a (le_max_left (poleOrder (f - algebraMap 𝔽[X] (RatFunc 𝔽) q) a)
      (poleOrder f a)),
    PP_eq_sum_of_le f a (le_max_right (poleOrder (f - algebraMap 𝔽[X] (RatFunc 𝔽) q) a)
      (poleOrder f a))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hc k (Finset.mem_Icc.1 hk).1]

theorem gramPoly_det_eq_tau (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) :
    (gramPoly c N).det = (tau (det6 N)).map (ev5U c Δe) := by
  apply IsFractionRing.injective 𝔽[X] (RatFunc 𝔽)
  rw [← aeval_vec6U, ← a6U_apply, a6U_det6]

/-- A finite sum of polynomials of degree less than `n`. -/
theorem sum_poly_lt {ι : Type*} (s : Finset ι) (f : ι → RatFunc 𝔽) {n : ℕ} (hn : 0 < n)
    (h : ∀ i ∈ s, ∃ T : 𝔽[X], f i = algebraMap 𝔽[X] (RatFunc 𝔽) T ∧ T.natDegree < n) :
    ∃ T : 𝔽[X], ∑ i ∈ s, f i = algebraMap 𝔽[X] (RatFunc 𝔽) T ∧ T.natDegree < n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simpa using hn⟩
  | insert i s hi ih =>
    obtain ⟨T₁, h1, h1'⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨T₂, h2, h2'⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨T₁ + T₂, ?_, ?_⟩
    · rw [Finset.sum_insert hi, h1, h2, map_add]
    · exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt h1' h2')

/-- The numerator of `ℬ_N` has degree `N + deg det G_N` (l.396–397). -/
theorem natDegree_Bnum (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) (c : 𝔽) (Δe : Fin 4 → 𝔽)
    {N : ℕ} (hN : 1 ≤ N) :
    (Bnum c Δe N).natDegree = N + (gramPoly c N).det.natDegree := by
  set DN := (gramPoly c N).det with hDN
  have hDN0 : DN ≠ 0 := gramPoly_det_ne_zero c N
  have haD : algebraMap 𝔽[X] (RatFunc 𝔽) DN ≠ 0 := fun h0 =>
    hDN0 ((map_eq_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).mp h0)
  -- the terms `m ≥ 1`
  have hterm : ∀ i ∈ Finset.range N, ∃ T : 𝔽[X],
      Hsph c Δe (i + 1) * wZ c Δe N (i + 1) * algebraMap 𝔽[X] (RatFunc 𝔽) DN =
        algebraMap 𝔽[X] (RatFunc 𝔽) T ∧ T.natDegree < N + DN.natDegree := by
    intro i hi
    have hiN : i + 1 ≤ N := Finset.mem_range.1 hi
    obtain ⟨U, hU, hH⟩ := hsph_poly_deg hF hK hJ1 hJ2 (N := i + 1) (by omega)
    have hHP := hH 𝔽 c Δe
    set Dm := (gramPoly c (i + 1)).det with hDm
    have hDm0 : Dm ≠ 0 := gramPoly_det_ne_zero c (i + 1)
    have hPdeg : (U.map (ev5U c Δe)).degree < Dm.degree :=
      calc (U.map (ev5U c Δe)).degree ≤ U.degree := degree_map_le
        _ < (dN (i + 1) : WithBot ℕ) := hU
        _ ≤ Dm.degree := le_degree_of_ne_zero (gramPoly_det_coeff_ne_zero c (i + 1))
    obtain ⟨q, hq⟩ := det6_dvd hK hiN
    have hE : DN = Dm * (tau q).map (ev5U c Δe) := by
      rw [hDN, hDm, gramPoly_det_eq_tau c Δe N, gramPoly_det_eq_tau c Δe (i + 1), hq, map_mul,
        Polynomial.map_mul]
    obtain ⟨a, wp, hw, hwdeg, -⟩ := polyLe_wZ c Δe hiN
    refine ⟨U.map (ev5U c Δe) * wp * (tau q).map (ev5U c Δe), ?_, ?_⟩
    · rw [hw, hE, map_mul, map_mul, map_mul, ← hHP]
      ring
    · by_cases hP0 : U.map (ev5U c Δe) = 0
      · rw [hP0, zero_mul, zero_mul, natDegree_zero]
        omega
      · have h1 := natDegree_lt_natDegree hP0 hPdeg
        have hE0 : (tau q).map (ev5U c Δe) ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hE
          exact hDN0 hE
        have h2 : DN.natDegree = Dm.natDegree + ((tau q).map (ev5U c Δe)).natDegree := by
          rw [hE, natDegree_mul hDm0 hE0]
        have h3 := natDegree_mul_le (p := U.map (ev5U c Δe) * wp)
          (q := (tau q).map (ev5U c Δe))
        have h4 := natDegree_mul_le (p := U.map (ev5U c Δe)) (q := wp)
        omega
  obtain ⟨T, hT, hTdeg⟩ := sum_poly_lt (Finset.range N)
    (fun i => Hsph c Δe (i + 1) * wZ c Δe N (i + 1) * algebraMap 𝔽[X] (RatFunc 𝔽) DN)
    (by omega) hterm
  -- the term `m = 0`
  obtain ⟨a, ha0, ψp, hψ, hψdeg, hψc⟩ := polyLe_psiZ c Δe N
  have hψN : ψp.natDegree = N :=
    le_antisymm hψdeg (le_natDegree_of_ne_zero (by rw [hψc]; exact ha0))
  have hψ0 : ψp ≠ 0 := by
    intro h0
    rw [h0, coeff_zero] at hψc
    exact ha0 hψc.symm
  -- assemble
  have hB : Bsph c Δe N * algebraMap 𝔽[X] (RatFunc 𝔽) DN =
      algebraMap 𝔽[X] (RatFunc 𝔽) (Bnum c Δe N) := by
    rw [Bsph, div_mul_cancel₀ _ haD]
  have hsum : algebraMap 𝔽[X] (RatFunc 𝔽) (Bnum c Δe N) =
      algebraMap 𝔽[X] (RatFunc 𝔽) (ψp * DN + T) := by
    rw [← hB, B_from_H, Finset.sum_mul, Finset.sum_range_succ', hT, Hsph_zero, wZ_zero, hψ,
      map_add, map_mul]
    ring
  have hnum : Bnum c Δe N = ψp * DN + T := IsFractionRing.injective 𝔽[X] (RatFunc 𝔽) hsum
  have hmain : (ψp * DN).natDegree = N + DN.natDegree := by
    rw [natDegree_mul hψ0 hDN0, hψN]
  rw [hnum, natDegree_add_eq_left_of_natDegree_lt (by rw [hmain]; exact hTdeg), hmain]

open Classical in
/-- Theorem 4.7 (iii) over a field: `ℬ_N(c(b),Δ,Δ_i)` is a polynomial of degree `N` plus the
sum of its principal parts at `Λ_N(b)`. -/
theorem poly_part_field (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) {b : 𝔽} (hb : b ≠ 0)
    (Δe : Fin 4 → 𝔽) {N : ℕ} (hN : 1 ≤ N) :
    ∃ Q : 𝔽[X], Q.natDegree = N ∧
      Bsph (kacC b) Δe N =
        algebraMap 𝔽[X] (RatFunc 𝔽) Q + ∑ μ ∈ Lam N b, PP (Bsph (kacC b) Δe N) μ := by
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hb N
  set g : Label → 𝔽 := fun a => kacHL a b with hg
  set e : Label → ℕ := fun a => Fintype.card (Nat.Partition (N - a.lvl)) with he
  set S : Finset 𝔽 := Lam N b with hS
  have hSg : S = (labels N).image g := rfl
  set m : 𝔽 → ℕ := fun μ => ∑ a ∈ (labels N).filter (fun a => g a = μ), e a with hm
  set G : 𝔽[X] := ∏ μ ∈ S, (X - C μ) ^ m μ with hG
  have hprod : kacProd b N = G := by
    rw [hG, hSg, kacProd, ← Finset.prod_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image_of_mem g ha)]
    refine Finset.prod_congr rfl fun μ _ => ?_
    rw [hm, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← (Finset.mem_filter.1 ha).2]
  have hGmonic : G.Monic := by
    rw [← hprod]
    exact kacProd_monic b N
  rw [hprod] at hdet
  have hGdeg : G.natDegree ≤ ∑ μ ∈ S, m μ := by
    refine le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun μ _ => ?_)
    refine le_trans natDegree_pow_le ?_
    rw [natDegree_X_sub_C, mul_one]
  have hG0 : algebraMap 𝔽[X] (RatFunc 𝔽) G ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).2 hGmonic.ne_zero
  have hC₀r : (RatFunc.C C₀ : RatFunc 𝔽) ≠ 0 := (map_ne_zero_iff _ RatFunc.C_injective).2 hC₀
  set T : 𝔽[X] := C C₀⁻¹ * Bnum (kacC b) Δe N with hT
  have hBT : Bsph (kacC b) Δe N =
      algebraMap 𝔽[X] (RatFunc 𝔽) T / algebraMap 𝔽[X] (RatFunc 𝔽) G := by
    rw [Bsph, hdet, hT]
    simp only [map_mul, RatFunc.algebraMap_C, map_inv₀]
    field_simp
  have hdetdeg : (gramPoly (kacC b) N).det.natDegree = G.natDegree := by
    rw [hdet, natDegree_C_mul hC₀]
  have hTdeg : T.natDegree = N + G.natDegree := by
    rw [hT, natDegree_C_mul (inv_ne_zero hC₀), natDegree_Bnum hF hK hJ1 hJ2 (kacC b) Δe hN,
      hdetdeg]
  have hdiv := modByMonic_add_div T G
  refine ⟨T /ₘ G, by rw [natDegree_divByMonic T hGmonic, hTdeg, Nat.add_sub_cancel], ?_⟩
  have hr : DLt (T %ₘ G) (∑ μ ∈ S, m μ) :=
    lt_of_lt_of_le (degree_modByMonic_lt T hGmonic)
      (le_trans degree_le_natDegree (WithBot.coe_le_coe.2 hGdeg))
  have hps := isPoleSum_div S m (T %ₘ G) hr
  have hsplit : Bsph (kacC b) Δe N - algebraMap 𝔽[X] (RatFunc 𝔽) (T /ₘ G) =
      algebraMap 𝔽[X] (RatFunc 𝔽) (T %ₘ G) / algebraMap 𝔽[X] (RatFunc 𝔽) G := by
    rw [hBT, eq_div_iff hG0, sub_mul, div_mul_cancel₀ _ hG0, ← map_mul, ← map_sub]
    congr 1
    linear_combination (-1 : 𝔽[X]) * hdiv
  rw [← hsplit] at hps
  have hsum := hps.eq_sum_PP
  rw [Finset.sum_congr rfl fun μ _ => PP_sub_poly _ _ μ] at hsum
  rw [← hsum]
  ring

end Field

/-- Theorem 4.7 (iii). -/
theorem sub_confluence_poly_part (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_sub_confluence_poly_part := by
  classical
  intro b hb N hN
  have hbs : cK b ≠ 0 := (map_ne_zero (algebraMap ℂ K4)).2 hb
  obtain ⟨Q, hQ, h⟩ := poly_part_field hF hK hJ1 hJ2 hbs ΔK hN
  refine ⟨Q, hQ, ?_⟩
  rw [Lam_cK, Finset.sum_image fun x _ y _ hxy => cK_injective hxy] at h
  exact h

/-- Theorem 4.7 (sphere/paper.tex l.1369–1422), from Proposition 4.4 and Theorem 3.1.

Paper label: thm:confluence -/
theorem thm_confluence_of_cited (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) :
    Stmt_thm_confluence :=
  thm_confluence_of_poly_part hF hK hJ1 hJ2 hH hFus (sub_confluence_poly_part hF hK hJ1 hJ2)

example (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) :
    Stmt_thm_confluence := thm_confluence_of_cited hF hK hJ1 hJ2 hH hFus

end Virasoro.Sphere
