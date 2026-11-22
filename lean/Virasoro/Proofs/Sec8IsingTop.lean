import Virasoro.Proofs.Sec8Ising11
import Virasoro.Proofs.Sec8IsingRows
import Virasoro.Proofs.Sec6LayerFinal
import Virasoro.Proofs.Sec6TTLabel

/-!
# Proposition 8.1 of `paper.tex` at 70bac53, by the paper's argument (l.1755–1771)

At `N = min(ℓ⁺₂, ℓ⁻₂)` equation (5.1) of Theorem 5.9 has the single term `τ/γ` with `M = 0`;
Proposition 6.7 with `c₂ = -1` gives `[d²]τ = -γρ²`, `ρ = -n₀/2`; the torus norm `τ` is the
product of two fusion polynomials (Lemma 5.5 with Proposition 6.2 or Lemma 6.6), so `γ` is read
off from `[d²]τ`.  The pole order `2` is Corollary 5.10.
-/

namespace Virasoro

open Verma Polynomial

section Single

variable {p p' r s : ℕ} {b : ℂ}

/-- Replacing `w⁻₂` by another singular vector of the same level keeps the setting of
Theorem 5.8 (singular vectors of a level are proportional). -/
theorem setting_update_minus (hU : Cited_SingularUnique)
    {wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)} (hT : TopLayerSetting p p' r s b wp wm)
    (x : Nat.Partition (ellMinus p p' r s 2) → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s 2) x)
      (ellMinus p p' r s 2)) :
    TopLayerSetting p p' r s b wp (Function.update wm 2 (pbwCoord (ellMinus p p' r s 2) x)) := by
  obtain ⟨hsg, hjan⟩ := hT
  obtain ⟨e, he⟩ := hU _ _ _ _ _ (hsg 2 (by norm_num)).2 hx
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [he]; exact zero_smul ℂ (wm 2))
  refine ⟨fun k hk => ⟨(hsg k hk).1, ?_⟩, fun i hi => ?_⟩
  · by_cases hk2 : k = 2
    · subst hk2
      rw [Function.update_self]
      exact hx
    · rw [Function.update_of_ne hk2]
      exact (hsg k hk).2
  · by_cases hi2 : i = 2
    · subst hi2
      rw [Function.update_self, hjan 2 hi, he, negSpan_smul _ he0]
    · rw [Function.update_of_ne hi2]
      exact hjan i hi

/-- The same for `w⁺₂`. -/
theorem setting_update_plus (hU : Cited_SingularUnique)
    {wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)} (hT : TopLayerSetting p p' r s b wp wm)
    (x : Nat.Partition (ellPlus p p' r s 2) → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s 2) x)
      (ellPlus p p' r s 2)) :
    TopLayerSetting p p' r s b (Function.update wp 2 (pbwCoord (ellPlus p p' r s 2) x)) wm := by
  obtain ⟨hsg, hjan⟩ := hT
  obtain ⟨e, he⟩ := hU _ _ _ _ _ (hsg 2 (by norm_num)).1 hx
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [he]; exact zero_smul ℂ (wp 2))
  refine ⟨fun k hk => ⟨?_, (hsg k hk).2⟩, fun i hi => ?_⟩
  · by_cases hk2 : k = 2
    · subst hk2
      rw [Function.update_self]
      exact hx
    · rw [Function.update_of_ne hk2]
      exact (hsg k hk).1
  · by_cases hi2 : i = 2
    · subst hi2
      rw [Function.update_self, hjan 2 hi, he, negSpan_smul _ he0]
    · rw [Function.update_of_ne hi2]
      exact hjan i hi

set_option maxHeartbeats 1600000 in
/-- Equation (5.1) at `N = ℓ⁺₂ < ℓ⁻₂`, where it has the single term `τ/γ`. -/
theorem top_two_single_plus (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique)
    (hset : MinimalSetting p p' r s b) (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b))
    (hT : TopLayerSetting p p' r s b wp wm) (hlt : ellPlus p p' r s 2 < ellMinus p p' r s 2)
    (hN3 : ellPlus p p' r s 2 < ellMin p p' r s 3) (x : Nat.Partition (ellPlus p p' r s 2) → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s 2) x)
      (ellPlus p p' r s 2)) :
    ppCoeff (HN (kacC b) (ellPlus p p' r s 2)) (pt (kacH r s b)) 2 =
      algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
        RatFunc.C (jform (kacC b) (kacH r s b) (ellPlus p p' r s 2) 2 x x)⁻¹ := by
  obtain ⟨-, -, -, hpp⟩ := thm_top_layer_of_cited hI p p' r s b hset _ wm
    (setting_update_plus hU hT x hx) 2 (ellPlus p p' r s 2) (by norm_num) (Nat.min_le_left _ _)
    hN3
  obtain ⟨xm, hxm⟩ := mem_level_of_L_zero (hT.1 2 (by norm_num)).2.2.1
  have h := (hpp x xm (by rw [Function.update_self]) hxm).2
  unfold topTerm at h
  rw [if_pos le_rfl, if_neg (not_le.2 hlt), add_zero, Nat.sub_self, HN_zero, RatFunc.eval_one,
    mul_one] at h
  exact h

theorem layerConst_two : (layerConst 2 : ℂ) = -1 := by norm_num [layerConst]

/-- At a level `N = ℓ^ε₂ < ℓ^{¬ε}₂, ℓ₃` with a single summand in (5.1): the pole order is `2`
(Corollary 5.10), the coefficient is `τ/γ` (Theorem 5.9), and `[d²]τ = -γρ²` (Proposition 6.7
with `c₂ = -1`), for any singular vector of level `N`. -/
theorem core_single (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    (hset : MinimalSetting p p' r s b) (ε : Bool) {N : ℕ} (hN : ellOrb p p' r s ε 2 = N)
    (hlt : N < ellOrb p p' r s (!ε) 2) (hN3 : N < ellMin p p' r s 3) (x : Nat.Partition N → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) N x) N) :
    poleOrder (HN (kacC b) N) (pt (kacH r s b)) = 2 ∧
      ppCoeff (HN (kacC b) N) (pt (kacH r s b)) 2 =
        algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
          RatFunc.C (jform (kacC b) (kacH r s b) N 2 x x)⁻¹ ∧
      (torusPolyForm (kacC b) (kacH r s b) x).coeff 2 =
        -(jform (kacC b) (kacH r s b) N 2 x x) *
          (-((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p))) ^ 2 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt1, hb⟩ := id hset
  obtain ⟨wp, wm, hsg, hjan, -, -⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt1 b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsg, hjan⟩
  have hN1 : 1 ≤ N := by rw [← hN]; exact TT.ellOrb_pos hp hp' hr hrp hs hsp ε (by norm_num)
  cases ε
  · have hN' : ellMinus p p' r s 2 = N := by rw [← hN, ellOrb, if_neg (by norm_num)]; rfl
    subst hN'
    have hlt' : ellMinus p p' r s 2 < ellPlus p p' r s 2 := by
      rw [ellOrb, if_neg (by norm_num)] at hlt; exact hlt
    have hjd : jDepth p p' r s (ellMinus p p' r s 2) = 2 :=
      jDepth_eq_of_range hp hp' hr hrp hs hsp (by norm_num) (Nat.min_le_right _ _) hN3
    refine ⟨(cor_top_layer_sharp_of_cited hJ hI hK hH hU p p' r s b hset _ hN1).trans hjd,
      top_two_single hI hU hset wp wm hT rfl hlt' hN3 x hx, ?_⟩
    obtain ⟨-, hc2, -⟩ := (prop_layer_coefficients_of_cited hI hK hH p p' r s b hset wp _
      (setting_update_minus hU hT x hx) 2 (by norm_num)).2 x (by rw [Function.update_self])
    rw [hc2, layerConst_two]
    ring
  · have hN' : ellPlus p p' r s 2 = N := by rw [← hN, ellOrb, if_neg (by norm_num)]; rfl
    subst hN'
    have hlt' : ellPlus p p' r s 2 < ellMinus p p' r s 2 := by
      rw [ellOrb, if_neg (by norm_num)] at hlt; exact hlt
    have hjd : jDepth p p' r s (ellPlus p p' r s 2) = 2 :=
      jDepth_eq_of_range hp hp' hr hrp hs hsp (by norm_num) (Nat.min_le_left _ _) hN3
    refine ⟨(cor_top_layer_sharp_of_cited hJ hI hK hH hU p p' r s b hset _ hN1).trans hjd,
      top_two_single_plus hI hU hset wp wm hT hlt' hN3 x hx, ?_⟩
    obtain ⟨-, hc2, -⟩ := (prop_layer_coefficients_of_cited hI hK hH p p' r s b hset _ wm
      (setting_update_plus hU hT x hx) 2 (by norm_num)).1 x (by rw [Function.update_self])
    rw [hc2, layerConst_two]
    ring

end Single

/-! ### The Ising rows -/

/-- A row of the table of Proposition 8.1 from Theorem 5.9 and Proposition 6.7: `γ` is
`-[d²]τ/ρ²` with `ρ = -(4r - 3s)/2`. -/
theorem ising_row_top (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    {r s : ℕ} (hset : MinimalSetting 3 4 r s b0) (ε : Bool) {N : ℕ}
    (hN : ellOrb 3 4 r s ε 2 = N) (hlt : N < ellOrb 3 4 r s (!ε) 2) (hN3 : N < ellMin 3 4 r s 3)
    (x : Nat.Partition N → ℂ) (hx1 : x (onesPartition N) = 1)
    (hx : IsSingular (pbwCoord (c := kacC b0) (h := kacH r s b0) N x) N)
    (R₁ S₁ R₂ S₂ : ℕ) (Q : ℂ[X])
    (hQ : ∀ d : ℂ, torusForm (kacC b0) (kacH r s b0) d N x x = Q.eval d)
    (hQg : ∀ d : ℂ, Q.eval d = genP R₁ S₁ b0 d * genP R₂ S₂ b0 d)
    (hQK : algebraMap ℂ[X] Kd Q =
      genP R₁ S₁ (RatFunc.C b0 : Kd) dvar * genP R₂ S₂ (RatFunc.C b0 : Kd) dvar)
    (γ : ℂ) (hρ : (4 : ℂ) * r - 3 * s ≠ 0)
    (hc : Q.coeff 2 = -γ * (((4 : ℂ) * r - 3 * s) / 2) ^ 2) :
    poleOrder (HN (kacC b0) N) (pt (kacH r s b0)) = 2 ∧
      ppCoeff (HN (kacC b0) N) (pt (kacH r s b0)) 2 =
        genP R₁ S₁ (RatFunc.C b0 : Kd) dvar * genP R₂ S₂ (RatFunc.C b0 : Kd) dvar /
          RatFunc.C γ ∧
      ∃ x : Nat.Partition N → ℂ, x (onesPartition N) = 1 ∧
        IsSingular (pbwCoord (c := kacC b0) (h := kacH r s b0) N x) N ∧
        (∀ d : ℂ, torusForm (kacC b0) (kacH r s b0) d N x x =
          genP R₁ S₁ b0 d * genP R₂ S₂ b0 d) ∧
        jform (kacC b0) (kacH r s b0) N 2 x x = γ := by
  obtain ⟨hpo, hpp, hc2⟩ := core_single hJ hI hK hH hU hset ε hN hlt hN3 x hx
  have hτ : torusPolyForm (kacC b0) (kacH r s b0) x = Q := torusForm_poly_eq hQ
  rw [hτ, hc] at hc2
  have hA' : (-(((4 : ℕ) : ℂ) * r - ((3 : ℕ) : ℂ) * s) / (2 * (((4 : ℕ) : ℂ) - ((3 : ℕ) : ℂ)))) ^ 2 =
      (((4 : ℂ) * r - 3 * s) / 2) ^ 2 := by push_cast; ring
  rw [hA'] at hc2
  have hρ2 : (((4 : ℂ) * r - 3 * s) / 2) ^ 2 ≠ 0 := pow_ne_zero _ (div_ne_zero hρ two_ne_zero)
  have hj : jform (kacC b0) (kacH r s b0) N 2 x x = γ :=
    neg_inj.1 (mul_right_cancel₀ hρ2 hc2.symm)
  refine ⟨hpo, ?_, x, hx1, hx, fun d => (hQ d).trans (hQg d), hj⟩
  rw [hpp, hτ, hQK, hj, div_eq_mul_inv, map_inv₀]

/-- `[d²]` of a product of two polynomials vanishing at `0`. -/
theorem coeff_two_mul_X {A B A' B' : ℂ[X]} (hA : A = X * A') (hB : B = X * B') :
    (A * B).coeff 2 = A'.eval 0 * B'.eval 0 := by
  rw [hA, hB, show X * A' * (X * B') = A' * B' * X ^ 2 by ring,
    show (2 : ℕ) = 0 + 2 from rfl, coeff_mul_X_pow, coeff_zero_eq_eval_zero, eval_mul]

theorem coeff_E2_P15 : (E2 * P15).coeff 2 = 4379375 := by
  rw [coeff_two_mul_X (A' := C (1 / 9) * (X - 1) * (3 * X - 14) * (3 * X - 5))
    (B' := C (1 / 16) * (X - 20) * (X - 13) * (X - 11) * (X - 6) * (X - 1) *
      (2 * X - 15) * (2 * X - 7) * (2 * X - 5) * (2 * X - 1)) (by unfold E2; ring)
    (by unfold P15; ring)]
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_ofNat, eval_one]
  norm_num

theorem coeff_P2_P42 : (P2 * P42).coeff 2 = 1121229484375 / 192 := by
  rw [coeff_two_mul_X (A' := C (1 / 4) * (X - 1) * (2 * X - 7) * (2 * X - 1))
    (B' := C (1 / 20736) * (X - 20) * (X - 13) * (X - 11) * (X - 6) * (X - 1) *
      (2 * X - 57) * (2 * X - 35) * (2 * X - 15) * (2 * X - 7) * (2 * X - 5) * (2 * X - 1) *
      (3 * X - 14) * (3 * X - 5) * (6 * X - 55) * (6 * X - 1)) (by unfold P2; ring)
    (by unfold P42; ring)]
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_ofNat, eval_one]
  norm_num

/-- `𝒫_{1,1}(b₀,d) = d(d-1)`. -/
noncomputable def P11x : ℂ[X] := X * (X - 1)

/-- `𝒫_{2,5}(b₀,d) = -d ∏ (h - d)` over the nineteen other roots `h = ((4k ∓ 3l)² - 1)/48`. -/
noncomputable def P25r : ℂ[X] :=
  (C 1 - X) * (C (1 / 2) - X) * (C (7 / 2) - X) * (C (5 / 2) - X) * (C (15 / 2) - X) *
    (C 6 - X) * (C 13 - X) * (C 11 - X) * (C 20 - X) * (C (5 / 3) - X) * (C (14 / 3) - X) *
    (C (1 / 6) - X) * (C (55 / 6) - X) * (C (1 / 6) - X) * (C (91 / 6) - X) * (C (5 / 3) - X) *
    (C (68 / 3) - X) * (C (14 / 3) - X) * (C (95 / 3) - X)

theorem genP_11x (d : ℂ) : genP 1 1 b0 d = P11x.eval d := by
  rw [genP_b0, show oddsBelow 1 = {1} from by decide]
  simp [P11x]
  ring

theorem genP_25x (d : ℂ) : genP 2 5 b0 d = (-X * P25r).eval d := by
  rw [genP_b0, show oddsBelow 2 = {1, 3} from by decide,
    show oddsBelow 5 = {1, 3, 5, 7, 9} from by decide]
  simp [Finset.prod_insert, P25r]
  ring

theorem coeff_P11_P25 :
    (genPpoly 1 1 b0 * genPpoly 2 5 b0).coeff 2 = 9911668641875000 / 104976 := by
  have h1 : genPpoly 1 1 b0 = P11x :=
    Polynomial.funext fun d => by rw [genPpoly_eval, genP_11x]
  have h2 : genPpoly 2 5 b0 = -X * P25r :=
    Polynomial.funext fun d => by rw [genPpoly_eval, genP_25x]
  rw [h1, h2, coeff_two_mul_X (A' := X - 1) (B' := -P25r) (by unfold P11x; ring) (by ring)]
  simp only [P25r, eval_neg, eval_mul, eval_sub, eval_C, eval_X, eval_one]
  norm_num

theorem kacH_b0_val (r s : ℕ) : kacH ((r : ℕ) : ℤ) ((s : ℕ) : ℤ) b0 =
    (((4 * (r : ℂ) - 3 * (s : ℂ)) ^ 2 - 1) / 48) := by
  have a := kacHL_b0_cast (r, s)
  rw [kacHL] at a
  rw [a]
  simp [isingDelta]

theorem ising_hb : b0 ^ 2 = -((4 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by
  rw [b0_sq]
  norm_num

/-- The row `λ = 1/2`, `N = 7` of the table of Proposition 8.1. -/
theorem ising_row_seven (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) :
    IsingDoublePoleTop (1 / 2) 7 2 1 1 5 (-700700) := by
  have hset : MinimalSetting 3 4 2 1 b0 :=
    ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, ising_hb⟩
  have e7 : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = (1 / 2 : ℂ) := by
    rw [kacH_b0_val]; norm_num
  obtain ⟨hx1, hxs, hxt⟩ := vec_seven hH
  have hxs' : IsSingular (pbwCoord (c := kacC b0) (h := kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0) 7
      (St.coords 7 (mapSt qC x7Q))) 7 := by
    rw [kacC_b0', e7]
    exact hxs
  have main := ising_row_top hJ hI hK hH hU hset false (N := 7) (by decide) (by decide)
    (by decide) _ hx1 hxs' 2 1 1 5 (E2 * P15)
    (fun d => by rw [kacC_b0', e7, hxt d, eval_mul, genP_21, genP_15])
    (fun d => by rw [eval_mul, genP_21, genP_15])
    (by rw [map_mul, genP_Kd genP_21, genP_Kd genP_15]) (-700700) (by norm_num)
    (by rw [coeff_E2_P15]; push_cast; norm_num)
  rw [e7, kacC_b0'] at main
  exact main

set_option maxRecDepth 100000 in
/-- The row `λ = 1/16`, `N = 10` of the table of Proposition 8.1. -/
theorem ising_row_ten (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) :
    IsingDoublePoleTop (1 / 16) 10 1 2 4 2 (-1121229484375 / 192) := by
  have hset : MinimalSetting 3 4 1 2 b0 :=
    ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, ising_hb⟩
  have e10 : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0 = (1 / 16 : ℂ) := by
    rw [kacH_b0_val]; norm_num
  obtain ⟨hx1, hxs, hxt⟩ := vec_ten hH
  have hxs' : IsSingular (pbwCoord (c := kacC b0) (h := kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0) 10
      (St.coords 10 (mapSt qC x10Q))) 10 := by
    rw [kacC_b0', e10]
    exact hxs
  have main := ising_row_top hJ hI hK hH hU hset true (N := 10) (by decide) (by decide)
    (by decide) _ hx1 hxs' 1 2 4 2 (P2 * P42)
    (fun d => by rw [kacC_b0', e10, hxt d, eval_mul, genP_12, genP_42])
    (fun d => by rw [eval_mul, genP_12, genP_42])
    (by rw [map_mul, genP_Kd genP_12, genP_Kd genP_42]) (-1121229484375 / 192) (by norm_num)
    (by rw [coeff_P2_P42]; push_cast; norm_num)
  rw [e10, kacC_b0'] at main
  exact main

set_option maxRecDepth 100000 in
/-- The row `λ = 0`, `N = 11` of the table of Proposition 8.1. -/
theorem ising_row_eleven (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) :
    IsingDoublePoleTop 0 11 1 1 2 5 (-2477917160468750 / 6561) := by
  have hset : MinimalSetting 3 4 1 1 b0 :=
    ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, ising_hb⟩
  have e11 : kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = (0 : ℂ) := by
    rw [kacH_b0_val]; norm_num
  obtain ⟨x, hx1, hxs, hxt⟩ := exists_vec_eleven hI hH
  have main := ising_row_top hJ hI hK hH hU hset false (N := 11) (by decide) (by decide)
    (by decide) x hx1 hxs 1 1 2 5 (genPpoly 1 1 b0 * genPpoly 2 5 b0) hxt
    (fun d => by rw [eval_mul, genPpoly_eval, genPpoly_eval])
    (by rw [map_mul, genP_Kd_poly, genP_Kd_poly]) (-2477917160468750 / 6561) (by norm_num)
    (by rw [coeff_P11_P25]; push_cast; norm_num)
  rw [e11, kacC_b0'] at main
  exact main

/-- The three rows of the table of Proposition 8.1 at the levels `7, 10, 11`. -/
theorem sub_ising_rows_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) :
    Stmt_sub_ising_rows :=
  ⟨ising_row_seven hK hH hJ hI hU, ising_row_ten hK hH hJ hI hU,
    ising_row_eleven hK hH hJ hI hU⟩

/-- Proposition 8.1, from the cited Kac determinant, the cited normalizations of
Proposition 6.2, the cited Jantzen layers, the cited injectivity of Verma homomorphisms and the
cited uniqueness of singular vectors.

Paper label: prop:ising-double-poles -/
theorem prop_ising_double_poles_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hU : Cited_SingularUnique) : Stmt_prop_ising_double_poles :=
  prop_ising_double_poles_of_rows hK hJ (sub_ising_rows_of_cited hK hH hJ hI hU)

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (hJ : Cited_JantzenLayers)
    (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) : Stmt_prop_ising_double_poles :=
  prop_ising_double_poles_of_cited hK hH hJ hI hU

end Virasoro
