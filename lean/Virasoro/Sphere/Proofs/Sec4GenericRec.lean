import Virasoro.Proofs.GenericH
import Virasoro.Proofs.Sec6Regular
import Virasoro.Sphere.Proofs.Sec4ResB
import Virasoro.Sphere.Proofs.Sec5TopLayerH

/-!
# Sphere paper Proposition 4.4: the generic recursion at a generic `b`, over any field

`sphere/paper.tex` l.1297–1319.  For generic `b` the Kac roots `h_a(b)`, `ℓ_a ≤ N`, are distinct
and no `h_a(b)+ℓ_a` is a Kac root; then
`Res_{Δ=h_a} ℬ_m = ℛ^sph_a ℬ_{m-ℓ_a}(c,h_a+ℓ_a,Δ_i)` for `ℓ_a ≤ m ≤ N` (and `0` for `m < ℓ_a`),
division by `Φ̃` gives `Res_{Δ=h_a} H_N = ℛ^sph_a H_{N-ℓ_a}(c,h_a+ℓ_a,Δ_i)` with simple poles, and
`H_N` is the sum of its principal parts once `deg_Δ P_N < deg_Δ det G_N` (Theorem 3.1).
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- Genericity of `b` at level `N` for the sphere recursion: the torus genericity, and the
second identity of Proposition 4.3 at `b`. -/
structure GenericAtSph (hN : NormalizationIdentities) (N : ℕ) (b : 𝔽) : Prop
    extends GenericAt hN N b where
  fus : ∀ a ∈ labels N, ∀ Δa Δb : 𝔽,
    ∑ Y, RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y) *
        gammaY (kacHL a b) Δa Δb Y.word = fusP a.1 a.2 b Δa Δb

variable {hN : NormalizationIdentities} {N : ℕ} {b : 𝔽}

/-- For generic `b` and a label `a` of level at most `M ≤ N`: `ℬ_M(c(b),Δ,Δ_i)` has at most a
simple pole at `Δ = h_a(b)`, with residue `ℛ^sph_a(b,Δ_i) ℬ_{M-ℓ_a}(c(b), h_a(b)+ℓ_a, Δ_i)`. -/
theorem GenericAtSph.residueB (hK : Cited_KacDeterminant) (hgen : GenericAtSph hN N b) {M : ℕ}
    (hM : M ≤ N) {a : Label} (ha : a ∈ labels M) (Δe : Fin 4 → 𝔽) :
    poleOrder (Bsph (kacC b) Δe M) (kacHL a b) ≤ 1 ∧
      ppCoeff (Bsph (kacC b) Δe M) (kacHL a b) 1 =
        Rsph a.1 a.2 b Δe *
          evalAt (kacHL a b + (a.lvl : 𝔽)) (Bsph (kacC b) Δe (M - a.lvl)) := by
  obtain ⟨ha1, ha2, ha3⟩ := mem_labels.1 ha
  have haN := labels_subset hM ha
  obtain ⟨M', rfl⟩ : ∃ M', M = a.1 * a.2 + M' := Nat.exists_eq_add_of_le ha3
  obtain ⟨hsing, hcross, -⟩ := normP_spec hN ha1 ha2 hgen.ne_zero (hgen.reg a haN)
  have hsub : a.1 * a.2 + M' - a.lvl = M' := by
    unfold Label.lvl
    omega
  have hβ : crossScalar (kacC b) (kacH (a.1 : ℤ) (a.2 : ℤ) b)
      (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y)) ≠ 0 := by
    rw [hcross]
    exact hgen.cross_ne haN
  have hg := hgen.toGenericAt.gram_det_shift_ne hK haN (M := M') (by omega)
  have hord := hgen.toGenericAt.gramLocal_det_order hK hM ha
  rw [hsub] at hord
  have hres := residue_Bsph (kacC b) (kacHL a b) (a.1 * a.2) M'
    (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y)) Δe
    (Nat.mul_pos ha1 ha2) hsing hβ hg hord
  refine ⟨hres.1, ?_⟩
  have e2 : crossScalar (kacC b) (kacHL a b)
      (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y)) = (genA a.1 a.2 b)⁻¹ := by
    rw [genA_inv]
    exact hcross
  rw [hres.2, hsub, hgen.fus a haN, hgen.fus a haN, e2, div_inv_eq_mul, Rsph]
  have hl : ((a.1 * a.2 : ℕ) : 𝔽) = (a.lvl : 𝔽) := rfl
  rw [hl]
  ring

/-- For generic `b`, `G_M(c(b),h_a(b))` is invertible when `ℓ_a > M`. -/
theorem GenericAtSph.gram_det_ne (hK : Cited_KacDeterminant) (hgen : GenericAtSph hN N b)
    {a : Label} (ha : a ∈ labels N) {M : ℕ} (hM : M ≤ N) (hna : a ∉ labels M) :
    (gram (kacC b) (kacHL a b) M).det ≠ 0 := by
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hgen.ne_zero M
  rw [← gramPoly_det_eval, hdet, eval_mul, eval_C, kacProd, eval_prod]
  refine mul_ne_zero hC₀ (Finset.prod_ne_zero_iff.2 fun g hg => ?_)
  rw [eval_pow, eval_sub, eval_X, eval_C]
  refine pow_ne_zero _ (sub_ne_zero.2 fun e => hna ?_)
  rw [hgen.toGenericAt.kacHL_inj ha (labels_subset hM hg) e]
  exact hg

/-- For generic `b` and a label `a` of level at most `N`: `H_N(c(b),Δ,Δ_i)` has at most a simple
pole at `Δ = h_a(b)`, with residue `ℛ^sph_a(b,Δ_i) H_{N-ℓ_a}(c(b), h_a(b)+ℓ_a, Δ_i)`. -/
theorem GenericAtSph.residueH (hK : Cited_KacDeterminant) (hgen : GenericAtSph hN N b)
    {a : Label} (ha : a ∈ labels N) (Δe : Fin 4 → 𝔽) :
    poleOrder (Hsph (kacC b) Δe N) (kacHL a b) ≤ 1 ∧
      ppCoeff (Hsph (kacC b) Δe N) (kacHL a b) 1 =
        Rsph a.1 a.2 b Δe *
          evalAt (kacHL a b + (a.lvl : 𝔽)) (Hsph (kacC b) Δe (N - a.lvl)) := by
  classical
  obtain ⟨ha1, ha2, ha3⟩ := mem_labels.1 ha
  have hB : ∀ M ≤ N, OrdGE (expandAt (Bsph (kacC b) Δe M) (kacHL a b)) (-((1 : ℕ) : ℤ)) := by
    intro M hM
    by_cases hmem : a ∈ labels M
    · exact ordGE_of_poleOrder_le (hgen.residueB hK hM hmem Δe).1
    · rw [expandAt_eq]
      exact (regVal_of_regAt (regAt_Bsph Δe (hgen.gram_det_ne hK ha hM hmem))).1.mono
        (by norm_num)
  refine ⟨poleOrder_le_of_ordGE (ordGE_expandAt_Hsph _ _ Δe N 1 hB), ?_⟩
  have hcoef : ∀ m ≤ N, (expandAt (Bsph (kacC b) Δe m) (kacHL a b)).coeff (-((1 : ℕ) : ℤ)) =
      Rsph a.1 a.2 b Δe * shiftSeq a.lvl
        (fun M => evalAt (kacHL a b + (a.lvl : 𝔽)) (Bsph (kacC b) Δe M)) m := by
    intro m hm
    unfold shiftSeq
    by_cases hl : a.lvl ≤ m
    · rw [if_pos hl]
      exact (hgen.residueB hK hm (mem_labels.2 ⟨ha1, ha2, hl⟩) Δe).2
    · rw [if_neg hl, mul_zero]
      have hmem : a ∉ labels m := fun h => hl (mem_labels.1 h).2.2
      have hr := regVal_of_regAt (regAt_Bsph Δe (hgen.gram_det_ne hK ha hm hmem))
      rw [expandAt_eq]
      exact hr.1.coeff_eq_zero (by norm_num)
  have hlN : a.lvl ≤ N := ha3
  show (expandAt (Hsph (kacC b) Δe N) (kacHL a b)).coeff (-((1 : ℕ) : ℤ)) = _
  rw [lcoeff_Hsph _ _ Δe N 1 hB, coeff_mul_compS_congr _ _ hcoef, compS_smul, coeff_shift_term,
    if_pos hlN, evalAt_Hsph (kacC b) (kacHL a b + (a.lvl : 𝔽)) Δe (N - a.lvl) fun m hm =>
      regAt_Bsph Δe (hgen.toGenericAt.gram_det_shift_ne hK ha (by omega))]
  obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le hlN
  rw [hM, Nat.add_sub_cancel_left, pow_add]
  have h16 : (16 : 𝔽) ^ a.lvl ≠ 0 := pow_ne_zero _ (by norm_num)
  have h16' : (16 : 𝔽) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

open Classical in
/-- `H_N(c(b),Δ,Δ_i)` is a finite sum of fractions with poles in `Λ_N(b)` once
`H_N det G_N = P` with `deg P < deg det G_N` (Theorem 3.1), over every field of characteristic
zero. -/
theorem isPoleSum_Hsph (hK : Cited_KacDeterminant) {b : 𝔽} (hb : b ≠ 0) (Δe : Fin 4 → 𝔽)
    (N : ℕ) (P : 𝔽[X])
    (hP : Hsph (kacC b) Δe N * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly (kacC b) N).det =
      algebraMap 𝔽[X] (RatFunc 𝔽) P)
    (hdeg : P.degree < (gramPoly (kacC b) N).det.degree) :
    IsPoleSum (Lam N b) (Hsph (kacC b) Δe N) := by
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
  rw [hprod] at hdet
  have hGdeg : G.natDegree ≤ ∑ μ ∈ S, m μ := by
    refine le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun μ _ => ?_)
    refine le_trans natDegree_pow_le ?_
    rw [natDegree_X_sub_C, mul_one]
  have hPd : DLt P (∑ μ ∈ S, m μ) := by
    rw [hdet] at hdeg
    have h2 : (C C₀ * G).degree ≤ ((∑ μ ∈ S, m μ : ℕ) : WithBot ℕ) :=
      le_trans degree_le_natDegree
        (WithBot.coe_le_coe.2 (le_trans (natDegree_C_mul_le _ _) hGdeg))
    exact lt_of_lt_of_le hdeg h2
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
  have heq : Hsph (kacC b) Δe N
      = algebraMap 𝔽[X] (RatFunc 𝔽) (C C₀⁻¹ * P) / algebraMap 𝔽[X] (RatFunc 𝔽) G := by
    rw [hdet] at hP
    rw [eq_div_iff hG0, map_mul, ← hP]
    simp only [map_mul, RatFunc.algebraMap_C, map_inv₀]
    field_simp
  rw [heq]
  exact key

/-- The generic recursion (4.3) at a generic value of `b`, given the degree bound of
Theorem 3.1 in the form of a pole sum. -/
theorem GenericAtSph.recursion (hK : Cited_KacDeterminant) (hgen : GenericAtSph hN N b)
    (Δe : Fin 4 → 𝔽) (hps : IsPoleSum (Lam N b) (Hsph (kacC b) Δe N)) :
    Hsph (kacC b) Δe N =
      ∑ a ∈ labels N,
        RatFunc.C (Rsph a.1 a.2 b Δe) / (RatFunc.X - RatFunc.C (kacHL a b)) *
          RatFunc.C (evalAt (kacHL a b + (a.lvl : 𝔽)) (Hsph (kacC b) Δe (N - a.lvl))) := by
  classical
  have hsum := hps.eq_sum_PP
  have himg : Lam N b = (labels N).image fun a => kacHL a b := rfl
  rw [himg, Finset.sum_image (fun a ha g hg h => hgen.toGenericAt.kacHL_inj ha hg h)] at hsum
  refine hsum.trans (Finset.sum_congr rfl fun a ha => ?_)
  obtain ⟨h1, h2⟩ := hgen.residueH hK ha Δe
  rw [PP_of_simple h1, h2, map_mul]
  ring

end Virasoro.Sphere
