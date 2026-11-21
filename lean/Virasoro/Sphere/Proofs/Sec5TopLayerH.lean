import Virasoro.Sphere.Proofs.RegEval
import Virasoro.Sphere.Proofs.Sec5TopLayerB

/-!
# Sphere paper Theorem 5.3: equation (5.2) for `H_N`

`sphere/paper.tex` l.1584–1604.  Expand `H = Φ̃⁻¹ ∑_m ℬ_m z(q)^m` at `Δ = λ + x`.  The
coefficients of `Φ̃⁻¹` are regular at `Δ = λ`, so the coefficient of `x^{-k}` of `H_N` is the
coefficient of `(16q)^N` in `Φ̃(λ;q)⁻¹ ∑_m ([x^{-k}] ℬ_m) z(q)^m`.  For `m ≤ N` equation (5.1)
gives `[x^{-k}] ℬ_m = ∑_± A^± ℬ_{m-ℓ^±}(μ^±)`, and
`Φ̃(λ;q)⁻¹ z(q)^{ℓ} = (16q)^{ℓ} Φ̃(λ+ℓ;q)⁻¹` turns each sign into
`A^± (16q)^{ℓ^±} H(μ^±;q)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Verma Polynomial

section Local

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem coeff_zq_pow (j m : ℕ) :
    PowerSeries.coeff j (zq (RatFunc 𝔽) ^ m) = RatFunc.C (PowerSeries.coeff j (zq 𝔽 ^ m)) := by
  rw [← map_zq (RatFunc.C : 𝔽 →+* RatFunc 𝔽), ← map_pow, PowerSeries.coeff_map]

/-- The coefficient of `(Δ-a)^{-k}` of `H_N`, when `ℬ_M` (`M ≤ N`) have pole order at most `k`
at `Δ = a`: it is the coefficient of `(16q)^N` of `Φ̃(a;q)⁻¹ ∑_m ([(Δ-a)^{-k}] ℬ_m) z(q)^m`. -/
theorem lcoeff_Hsph (c a : 𝔽) (Δe : Fin 4 → 𝔽) (N k : ℕ)
    (hB : ∀ M ≤ N, OrdGE (expandAt (Bsph c Δe M) a) (-(k : ℤ))) :
    (expandAt (Hsph c Δe N) a).coeff (-(k : ℤ)) =
      PowerSeries.coeff N ((PhiAt c a Δe)⁻¹ *
        compS (fun m => (expandAt (Bsph c Δe m) a).coeff (-(k : ℤ))) (zq 𝔽)) / 16 ^ N := by
  have hBz : ∀ j ≤ N,
      OrdGE (expandHom a (PowerSeries.coeff j (BzSeries c Δe))) (-(k : ℤ)) ∧
      (expandHom a (PowerSeries.coeff j (BzSeries c Δe))).coeff (-(k : ℤ)) =
        PowerSeries.coeff j
          (compS (fun m => (expandAt (Bsph c Δe m) a).coeff (-(k : ℤ))) (zq 𝔽)) := by
    intro j hj
    simp only [BzSeries, compS, PowerSeries.coeff_mk]
    rw [map_sum]
    refine ⟨OrdGE.sum fun m hm => ?_, ?_⟩
    · rw [map_mul, coeff_zq_pow, expandHom_C]
      have h := (hB m (by have := Finset.mem_range.1 hm; omega)).mul
        (ordGE_C (PowerSeries.coeff j (zq 𝔽 ^ m)))
      rwa [add_zero] at h
    · rw [HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [map_mul, coeff_zq_pow, expandHom_C]
      exact coeff_mul_regVal (hB m (by have := Finset.mem_range.1 hm; omega)) (regVal_C _)
  have h16 : ((16 : RatFunc 𝔽) ^ N)⁻¹ = RatFunc.C (((16 : 𝔽) ^ N)⁻¹) := by
    rw [map_inv₀, map_pow, map_ofNat]
  have hsum : OrdGE (expandHom a (PowerSeries.coeff N (Hseries c Δe))) (-(k : ℤ)) ∧
      (expandHom a (PowerSeries.coeff N (Hseries c Δe))).coeff (-(k : ℤ)) =
        PowerSeries.coeff N ((PhiAt c a Δe)⁻¹ *
          compS (fun m => (expandAt (Bsph c Δe m) a).coeff (-(k : ℤ))) (zq 𝔽)) := by
    unfold Hseries
    rw [PowerSeries.coeff_mul, map_sum, PowerSeries.coeff_mul]
    refine ⟨OrdGE.sum fun p hp => ?_, ?_⟩
    · have hp2 : p.2 ≤ N := Finset.HasAntidiagonal.antidiagonal.snd_le hp
      rw [map_mul]
      have h := (regVal_of_mem_regRing (coeffIn_PhiTilde_inv c a Δe p.1)).1.mul (hBz p.2 hp2).1
      rwa [zero_add] at h
    · rw [HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp2 : p.2 ≤ N := Finset.HasAntidiagonal.antidiagonal.snd_le hp
      rw [map_mul, mul_comm (expandHom a (PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹)),
        coeff_mul_regVal (hBz p.2 hp2).1
          (regVal_of_mem_regRing (coeffIn_PhiTilde_inv c a Δe p.1)),
        (hBz p.2 hp2).2, ← evS_PhiTilde_inv, mul_comm]
      simp only [evS, PowerSeries.coeff_mk]
  unfold Hsph
  rw [expandAt_eq, div_eq_mul_inv, map_mul, h16, expandHom_C,
    coeff_mul_regVal hsum.1 (regVal_C _), hsum.2, div_eq_mul_inv]

theorem regAt_Bsph {c z : 𝔽} (Δe : Fin 4 → 𝔽) {M : ℕ} (h : (gram c z M).det ≠ 0) :
    RegAt z (Bsph c Δe M) := by
  unfold Bsph
  exact regAt_div z _ (by rwa [gramPoly_det_eval])

/-- The value of `H_M` at a point where `ℬ_m`, `m ≤ M`, are regular. -/
theorem evalAt_Hsph (c μ : 𝔽) (Δe : Fin 4 → 𝔽) (M : ℕ)
    (hreg : ∀ m ≤ M, RegAt μ (Bsph c Δe m)) :
    evalAt μ (Hsph c Δe M) =
      PowerSeries.coeff M ((PhiAt c μ Δe)⁻¹ *
        compS (fun m => evalAt μ (Bsph c Δe m)) (zq 𝔽)) / 16 ^ M := by
  have e0 : (-((0 : ℕ) : ℤ)) = 0 := by simp
  have hB0 : ∀ m ≤ M, OrdGE (expandAt (Bsph c Δe m) μ) (-((0 : ℕ) : ℤ)) := by
    intro m hm
    rw [e0]
    exact (regVal_of_regAt (hreg m hm)).1
  have h := lcoeff_Hsph c μ Δe M 0 hB0
  have hord := ordGE_expandAt_Hsph c μ Δe M 0 hB0
  rw [e0] at h hord
  have hmem : Hsph c Δe M ∈ regRing μ := mem_regRing.2 hord
  rw [← (regVal_of_mem_regRing hmem).2, ← expandAt_eq, h]
  congr 1
  refine coeff_mul_compS_congr _ _ fun m hm => ?_
  exact (regVal_of_regAt (hreg m hm)).2

/-- One sign of (5.2) at the level of `q`-series. -/
theorem coeff_shift_term (c a : 𝔽) (Δe : Fin 4 → 𝔽) (b : ℕ → 𝔽) (ℓ N : ℕ) (t : 𝔽) :
    PowerSeries.coeff N ((PhiAt c a Δe)⁻¹ * (PowerSeries.C t * compS (shiftSeq ℓ b) (zq 𝔽))) =
      if ℓ ≤ N then
        t * (16 ^ ℓ * PowerSeries.coeff (N - ℓ)
          ((PhiAt c (a + (ℓ : 𝔽)) Δe)⁻¹ * compS b (zq 𝔽)))
      else 0 := by
  have h16 : (16 : PowerSeries 𝔽) ^ ℓ = PowerSeries.C ((16 : 𝔽) ^ ℓ) := by
    rw [map_pow, map_ofNat]
  have e : (PhiAt c a Δe)⁻¹ * (PowerSeries.C t * compS (shiftSeq ℓ b) (zq 𝔽)) =
      PowerSeries.C t * (PowerSeries.C ((16 : 𝔽) ^ ℓ) * (PowerSeries.X ^ ℓ *
        ((PhiAt c (a + (ℓ : 𝔽)) Δe)⁻¹ * compS b (zq 𝔽)))) := by
    rw [← compS_mul_pow constantCoeff_zq]
    calc (PhiAt c a Δe)⁻¹ * (PowerSeries.C t * (compS b (zq 𝔽) * zq 𝔽 ^ ℓ))
        = PowerSeries.C t * ((PhiAt c a Δe)⁻¹ * zq 𝔽 ^ ℓ * compS b (zq 𝔽)) := by ring
      _ = _ := by
        rw [PhiAt_inv_mul_zq_pow, mul_pow, h16]
        ring
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

end Local

/-- The summand of (5.1), (5.2) as a shifted sequence. -/
theorem topTermSph_eq (f : ℕ → RatFunc K4) (c lam : ℂ) (N ℓ k : ℕ) (x : Nat.Partition ℓ → ℂ) :
    topTermSph f c lam N ℓ k x =
      piScalar lam x (ΔK 3) (ΔK 2) * piScalar lam x (ΔK 0) (ΔK 1) *
          cK (jform c lam ℓ k x x)⁻¹ *
        shiftSeq ℓ (fun M => evalAt (cK (lam + (ℓ : ℂ))) (f M)) N := by
  unfold topTermSph shiftSeq
  by_cases h : ℓ ≤ N
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- One sign of (5.2). -/
theorem top_term_H (c lam : ℂ) (N ℓ : ℕ) (t : K4)
    (hdet : ℓ ≤ N → ∀ M ≤ N - ℓ, (gram c (lam + (ℓ : ℂ)) M).det ≠ 0) :
    PowerSeries.coeff N ((PhiAt (cK c) (cK lam) ΔK)⁻¹ * (PowerSeries.C t *
        compS (shiftSeq ℓ fun M => evalAt (cK (lam + (ℓ : ℂ))) (Bsph (cK c) ΔK M)) (zq K4))) /
        16 ^ N =
      t * shiftSeq ℓ (fun M => evalAt (cK (lam + (ℓ : ℂ))) (Hsph (cK c) ΔK M)) N := by
  have hμ : cK (lam + (ℓ : ℂ)) = cK lam + (ℓ : K4) := by
    rw [cK, map_add, map_natCast]
  rw [coeff_shift_term]
  simp only [shiftSeq]
  by_cases h : ℓ ≤ N
  · rw [if_pos h, if_pos h, evalAt_Hsph (cK c) (cK (lam + (ℓ : ℂ))) ΔK (N - ℓ) fun m hm =>
      regAt_Bsph ΔK (gramK_det_ne_zero (hdet h m hm)), ← hμ]
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, pow_add]
    have h16 : (16 : K4) ^ ℓ ≠ 0 := pow_ne_zero _ (by norm_num)
    have h16' : (16 : K4) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  · rw [if_neg h, if_neg h, zero_div, mul_zero]

/-- Equation (5.2) of Theorem 5.3 (sphere/paper.tex l.1584–1604). -/
theorem sub_top_layer_Hcoeff_of_cited (hI : Cited_VermaHomInjective) :
    Stmt_sub_top_layer_Hcoeff := by
  intro p p' r s b hset wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  obtain ⟨hndp, hndm⟩ :=
    sub_top_layer_nondeg_of_cited hI p p' r s b hset' wp wm hT k N hk hN1 hN2
  have hjN : jDepth p p' r s N = k := jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2
  have hBM : ∀ M ≤ N, OrdGE (expandAt (Bsph (cK (kacC b)) ΔK M) (cK (kacH r s b)))
      (-(k : ℤ)) := by
    intro M hM
    refine (ordGE_expandAt_BsphK (kacC b) (kacH r s b) M).mono ?_
    rw [poleOrderInv_eq_jDepth hset' hT M]
    have := jDepth_mono p p' r s hM
    omega
  have hβ : ∀ m ≤ N,
      (expandAt (Bsph (cK (kacC b)) ΔK m) (cK (kacH r s b))).coeff (-(k : ℤ)) =
        piScalar (kacH r s b) xp (ΔK 3) (ΔK 2) * piScalar (kacH r s b) xp (ΔK 0) (ΔK 1) *
            cK (jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp)⁻¹ *
          shiftSeq (ellPlus p p' r s k) (fun M =>
            evalAt (cK (kacH r s b + (ellPlus p p' r s k : ℂ))) (Bsph (cK (kacC b)) ΔK M)) m +
        piScalar (kacH r s b) xm (ΔK 3) (ΔK 2) * piScalar (kacH r s b) xm (ΔK 0) (ΔK 1) *
            cK (jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm)⁻¹ *
          shiftSeq (ellMinus p p' r s k) (fun M =>
            evalAt (cK (kacH r s b + (ellMinus p p' r s k : ℂ))) (Bsph (cK (kacC b)) ΔK M)) m := by
    intro m hm
    rw [← topTermSph_eq, ← topTermSph_eq]
    exact top_layer_B hI hset' hT hk hN1 hN2 xp xm hxp hxm m hm
  rw [topTermSph_eq, topTermSph_eq]
  show (expandAt (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b))).coeff (-(k : ℤ)) = _
  rw [lcoeff_Hsph _ _ _ N k hBM, coeff_mul_compS_congr _ _ hβ, compS_add, compS_smul, compS_smul,
    mul_add, map_add, add_div,
    top_term_H _ _ _ _ _ fun hle M hM => (hndp xp hxp hle).2 M hM,
    top_term_H _ _ _ _ _ fun hle M hM => (hndm xm hxm hle).2 M hM]

/-- Theorem 5.3 of the sphere paper, from the cited injectivity of homomorphisms of Verma
modules used in the torus Theorem 5.9.

Paper label: thm:top-layer -/
theorem thm_top_layer_of_cited (hI : Cited_VermaHomInjective) : Stmt_thm_top_layer :=
  thm_top_layer_of_sub hI (sub_top_layer_Hcoeff_of_cited hI)

example (hI : Cited_VermaHomInjective) : Stmt_thm_top_layer := thm_top_layer_of_cited hI

end Virasoro.Sphere
