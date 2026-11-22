import Virasoro.Sphere.Proofs.Sec5SharpHLog

/-!
# Theorem 5.5 (`thm:sharp-H`): the pole of `H_N` at `Δ = λ` has order exactly `j_N(λ)`

sphere/paper.tex l.1693–1789.  As for Theorem 5.4, the coefficient of `(Δ-λ)^{-k}` (Theorem 5.3)
is the image in `K4` of a polynomial `R` in `Δ₁,…,Δ₄`.  Specialize `(Δ₁,Δ₂) = (μ,0)` and put
`(Δ₃,Δ₄)` on the line `(wt((w+X)/2), wt((w-X)/2))`, `X = m^big - p' - p` (l.1708–1714): the
image of `R` in `ℂ[w]` is `π^small(Δ₄,Δ₃) π^small(μ,0)/γ · H_M(w)`; the higher branch vanishes
identically (Lemma 5.2(iii)), `π^small(Δ₄,Δ₃) ≢ 0`, `π^small(μ,0) ≠ 0`, and
`[w^M] H_M(w) = k_M/(16^M M!) ≠ 0` (l.1735–1781).
-/

namespace Virasoro.Sphere

open Polynomial Finset Verma

/-! ### The specialization `ℂ[Δ₁,…,Δ₄] → ℂ[w]` -/

section Line

variable (p p' : ℕ) (μ Xc : ℂ)

/-- `wt(a) = (a² - (p'-p)²)/(4pp')` for a polynomial `a` in `w`. -/
noncomputable def momPoly (a : ℂ[X]) : ℂ[X] :=
  C (1 / (4 * (p : ℂ) * p')) * (a ^ 2 - C (((p' : ℂ) - p) ^ 2))

/-- `(μ, 0, wt((w+X)/2), wt((w-X)/2))` as polynomials in `w`. -/
noncomputable def gW : Fin 4 → ℂ[X] :=
  ![C μ, 0, momPoly p p' (C (1 / 2 : ℂ) * (X + C Xc)), momPoly p p' (C (1 / 2 : ℂ) * (X - C Xc))]

/-- The specialization of l.1708–1714. -/
noncomputable def psiW : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] ℂ[X] := MvPolynomial.aeval (gW p p' μ Xc)

theorem eval_gW (w : ℂ) (i : Fin 4) : (gW p p' μ Xc i).eval w = ptW p p' μ Xc w i := by
  fin_cases i <;> simp [gW, ptW, momPoly, momC] <;> ring

theorem eval_psiW (R : MvPolynomial (Fin 4) ℂ) (w : ℂ) :
    (psiW p p' μ Xc R).eval w = MvPolynomial.eval (ptW p p' μ Xc w) R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [psiW]
  | add P Q hP hQ => rw [map_add, eval_add, hP, hQ, map_add]
  | mul_X P i hP =>
    rw [map_mul, eval_mul, hP, map_mul, MvPolynomial.eval_X, psiW, MvPolynomial.aeval_X, eval_gW]

end Line

/-! ### The summand of (5.2) as a polynomial -/

/-- The polynomial representative of `topTermSph (Hsph …)`. -/
noncomputable def topRH (c lam : ℂ) (N ℓ k : ℕ) (x : Nat.Partition ℓ → ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  if ℓ ≤ N then
    piR lam x 3 2 * piR lam x 0 1 * MvPolynomial.C (jform c lam ℓ k x x)⁻¹ *
      HR c (lam + (ℓ : ℂ)) (N - ℓ)
  else 0

theorem topTermSphH_eq {c lam : ℂ} {N ℓ : ℕ} (k : ℕ) (x : Nat.Partition ℓ → ℂ)
    (hdet : ℓ ≤ N → ∀ m ≤ N - ℓ, (gram c (lam + (ℓ : ℂ)) m).det ≠ 0) :
    topTermSph (Hsph (cK c) ΔK) c lam N ℓ k x =
      algebraMap (MvPolynomial (Fin 4) ℂ) K4 (topRH c lam N ℓ k x) := by
  unfold topTermSph topRH
  split_ifs with hN
  · rw [evalHsph_K4 (hdet hN), map_mul, map_mul, map_mul, ← piScalar_K4, ← piScalar_K4,
      algebraMap_C_K4]
  · rw [map_zero]

/-! ### Arithmetic of `X = m^big - p' - p` (l.1758–1773) -/

/-- For `{p,p'} = {2,3}` the unique interior weight is `(1,1)` and every momentum is odd, so
`X ≠ 3` (l.1768–1771). -/
theorem X_ne_three_exc {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool)
    (k : ℕ) (h6 : (p : ℤ) * p' = 6) : nOrb p p' r s ε k - p' - p ≠ 3 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, -⟩ := hset
  have h6' : p * p' = 6 := by exact_mod_cast h6
  have hp3 : p ≤ 3 := by nlinarith
  have hcase : (p = 2 ∧ p' = 3) ∨ (p = 3 ∧ p' = 2) := by
    interval_cases p <;> omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain rfl : r = 1 := by omega
    obtain rfl : s = 1 := by omega
    unfold nOrb
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> cases ε <;> simp [h] <;> omega
  · obtain rfl : s = 1 := by omega
    obtain rfl : r = 1 := by omega
    unfold nOrb
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> cases ε <;> simp [h] <;> omega

/-- `2X² ≠ pp'` and `2X² ≠ 3pp'` (l.1762–1773). -/
theorem X_arith {p p' : ℕ} (hp : 2 ≤ p) (hp' : 2 ≤ p') (hcop : Nat.Coprime p p') {X : ℤ}
    (hX : ((p : ℤ) - 1) * ((p' : ℤ) - 1) ≤ X) (hexc : (p : ℤ) * p' = 6 → X ≠ 3) :
    2 * X ^ 2 ≠ p * p' ∧ 2 * X ^ 2 ≠ 3 * p * p' := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hp2' : (2 : ℤ) ≤ p' := by exact_mod_cast hp'
  have hY : (1 : ℤ) ≤ ((p : ℤ) - 1) * ((p' : ℤ) - 1) := by nlinarith
  have hX0 : 0 < X := by linarith
  have hXY : (((p : ℤ) - 1) * ((p' : ℤ) - 1)) ^ 2 ≤ X ^ 2 := by nlinarith
  rcases Nat.lt_or_ge p 3 with hp3 | hp3 <;> rcases Nat.lt_or_ge p' 3 with hq3 | hq3
  · obtain rfl : p = 2 := by omega
    obtain rfl : p' = 2 := by omega
    exact absurd hcop (by decide)
  · obtain rfl : p = 2 := by omega
    have h4 : p' ≠ 4 := by rintro rfl; exact absurd hcop (by decide)
    push_cast at hX hexc ⊢
    rcases Nat.lt_or_ge p' 4 with h | h
    · obtain rfl : p' = 3 := by omega
      push_cast at hX hexc ⊢
      have hX3 := hexc (by norm_num)
      refine ⟨by nlinarith, fun h => hX3 ?_⟩
      nlinarith
    · have h5 : (5 : ℤ) ≤ p' := by exact_mod_cast (by omega : 5 ≤ p')
      constructor <;> nlinarith
  · obtain rfl : p' = 2 := by omega
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hcop (by decide)
    push_cast at hX hexc ⊢
    rcases Nat.lt_or_ge p 4 with h | h
    · obtain rfl : p = 3 := by omega
      push_cast at hX hexc ⊢
      have hX3 := hexc (by norm_num)
      refine ⟨by nlinarith, fun h => hX3 ?_⟩
      nlinarith
    · have h5 : (5 : ℤ) ≤ p := by exact_mod_cast (by omega : 5 ≤ p)
      constructor <;> nlinarith
  · have h3 : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have h3' : (3 : ℤ) ≤ p' := by exact_mod_cast hq3
    have hab : (4 : ℤ) ≤ ((p : ℤ) - 1) * ((p' : ℤ) - 1) := by nlinarith
    constructor <;> nlinarith

/-! ### The nonvanishing of the two summands (l.1703–1787) -/

section Pair

variable {p p' r s : ℕ} {b : ℂ}

theorem momC_diff (p p' : ℕ) : momC p p' ((p' : ℂ) - p) = 0 := by
  unfold momC
  ring

set_option maxHeartbeats 1000000 in
theorem sharpH_pair_ne (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hS : Cited_SchurHermite)
    (hset : MinimalSetting p p' r s b) {k N : ℕ} (hk : 1 ≤ k) (ε : Bool) {ns nb : ℕ}
    (hns : ellOrb p p' r s ε k = ns) (hnb : ellOrb p p' r s (!ε) k = nb) (hlt : ns < nb)
    (hsN : ns ≤ N) (xs : Nat.Partition ns → ℂ) (xb : Nat.Partition nb → ℂ)
    (hxs : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) ns xs) ns)
    (hxb : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) nb xb) nb)
    (hγ : jform (kacC b) (kacH r s b) ns k xs xs ≠ 0)
    (hdets : ∀ M : ℕ, M ≤ N - ns → (gram (kacC b) (kacH r s b + (ns : ℂ)) M).det ≠ 0)
    (hdetb : nb ≤ N → ∀ M : ℕ, M ≤ N - nb →
      (gram (kacC b) (kacH r s b + (nb : ℂ)) M).det ≠ 0) :
    topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N ns k xs +
      topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N nb k xb ≠ 0 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt', hb⟩ := id hset
  rw [topTermSphH_eq k xs (fun _ => hdets), topTermSphH_eq k xb hdetb, ← map_add]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 4) ℂ) K4)).2 ?_
  -- the momenta
  set m : ℤ := nOrb p p' r s ε k with hm_def
  set mb : ℤ := nOrb p p' r s (!ε) k with hmb_def
  have hsum : m + mb = 2 * k * p * p' := nOrb_add_not ε k
  have hm2 := TT.nOrb_sq (p := p) (p' := p') hrp hsp ε hk
  have hmb2 := TT.nOrb_sq (p := p) (p' := p') hrp hsp (!ε) hk
  rw [← hm_def, hns] at hm2
  rw [← hmb_def, hnb] at hmb2
  have hkpp : (0 : ℤ) < 2 * k * p * p' := by positivity
  have hnsnb : (ns : ℤ) < nb := by exact_mod_cast hlt
  have hppos : (0 : ℤ) < 4 * p * p' := by positivity
  have hpos : 0 < m + mb := by rw [hsum]; exact hkpp
  have hmlt : m < mb := by
    nlinarith [hpos, hm2, hmb2, mul_lt_mul_of_pos_left hnsnb hppos]
  set X : ℤ := mb - p' - p with hX_def
  have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hXge : ((p : ℤ) - 1) * ((p' : ℤ) - 1) ≤ X := by
    have e1 : (k : ℤ) * p * p' + 1 ≤ mb := by linarith
    have e2 : 1 * ((p : ℤ) * p') ≤ (k : ℤ) * ((p : ℤ) * p') :=
      mul_le_mul_of_nonneg_right hk1 (by positivity)
    rw [hX_def]
    linarith
  have hX0 : 0 < X := by
    have h1 : (1 : ℤ) ≤ (p : ℤ) - 1 := by have := hp; omega
    have h2 : (1 : ℤ) ≤ (p' : ℤ) - 1 := by have := hp'; omega
    have : (1 : ℤ) ≤ ((p : ℤ) - 1) * ((p' : ℤ) - 1) := one_le_mul_of_one_le_of_one_le h1 h2
    linarith
  set Xc : ℂ := (X : ℂ) with hXc
  set μ : ℂ := kacH r s b + (ns : ℂ) with hμ_def
  have hμ : μ = momC p p' (m : ℂ) := by
    rw [hμ_def, kacH_min_add (by omega) (by omega) hb r s ns hm2]
    unfold momC
    push_cast
    ring
  set ψ := psiW p p' μ Xc with hψ
  -- (1) the higher branch vanishes identically in `w`
  have hbig : ψ (topRH (kacC b) (kacH r s b) N nb k xb) = 0 := by
    unfold topRH
    split_ifs with hbN
    · have hπ : ψ (piR (kacH r s b) xb 3 2) = 0 := by
        refine Polynomial.funext fun w => ?_
        rw [hψ, eval_psiW, eval_piR, eval_zero]
        have hz := (pi_iii_any hH hF hU hset (!ε) hk hnb xb hxb ((w - Xc) / 2) ((w + Xc) / 2)).2
          (Or.inr (by rw [← hmb_def, hXc, hX_def]; push_cast; ring))
        simpa [ptW] using hz
      rw [map_mul, map_mul, map_mul, hπ, zero_mul, zero_mul, zero_mul]
    · rw [map_zero]
  -- (2) the lower-branch factors
  have hπ1 : ψ (piR (kacH r s b) xs 3 2) ≠ 0 := by
    intro hz
    have h1 := congrArg (Polynomial.eval (1 / 2 : ℂ)) hz
    rw [hψ, eval_psiW, eval_piR, eval_zero] at h1
    have h1' : piScalar (kacH r s b) xs (momC p p' ((1 / 2 - Xc) / 2))
        (momC p p' ((1 / 2 + Xc) / 2)) = 0 := by simpa [ptW] using h1
    obtain ⟨c₀, hc₀, hc⟩ := (pi_iii_any hH hF hU hset ε hk hns xs hxs _ _).1 h1'
    rw [← hm_def] at hc₀
    rcases hc with hc | hc
    · have : ((2 * c₀ : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
        push_cast
        linear_combination -2 * hc
      have := Int.cast_injective this
      omega
    · have : ((-X : ℤ) : ℂ) = (c₀ : ℂ) := by
        push_cast
        rw [← hXc]
        linear_combination hc
      have hc' := Int.cast_injective this
      have h3 := neg_le_abs c₀
      rw [← hc'] at h3 hc₀
      rw [neg_neg] at h3
      linarith
  have hπ2 : ψ (piR (kacH r s b) xs 0 1) ≠ 0 := by
    intro hz
    have h1 := congrArg (Polynomial.eval (0 : ℂ)) hz
    rw [hψ, eval_psiW, eval_piR, eval_zero] at h1
    have h1' : piScalar (kacH r s b) xs (momC p p' (m : ℂ)) (momC p p' ((p' : ℂ) - p)) = 0 := by
      rw [momC_diff, ← hμ]
      simpa [ptW] using h1
    obtain ⟨c₀, hc₀, hc⟩ := (pi_iii_any hH hF hU hset ε hk hns xs hxs _ _).1 h1'
    rw [← hm_def] at hc₀
    have habs := le_abs_self c₀
    rcases hc with hc | hc
    · have : m + p' - p = c₀ := by
        have : ((m + p' - p : ℤ) : ℂ) = (c₀ : ℂ) := by push_cast; linear_combination hc
        exact_mod_cast this
      have : (2 : ℤ) ≤ p' := by exact_mod_cast hp'
      linarith
    · have : m - p' + p = c₀ := by
        have : ((m - p' + p : ℤ) : ℂ) = (c₀ : ℂ) := by push_cast; linear_combination hc
        exact_mod_cast this
      have : (2 : ℤ) ≤ p := by exact_mod_cast hp
      linarith
  have hγC : ψ (MvPolynomial.C (jform (kacC b) (kacH r s b) ns k xs xs)⁻¹) ≠ 0 := by
    rw [hψ, psiW, MvPolynomial.aeval_C, Polynomial.algebraMap_apply]
    simpa using hγ
  -- (3) the leading coefficient of `H_M(w)`
  set M := N - ns with hM
  set bq : ℚ := 2 * X / (p * p') with hbq
  set gq : ℚ := 1 / (p * p') with hgq
  set b' : ℕ → ℂ := fun j => algebraMap ℚ ℂ (1 / (j.factorial : ℚ)) with hb'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (show 0 < p by omega).ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast (show 0 < p' by omega).ne'
  obtain ⟨h10, h20, h21, h11, h22⟩ := sOne_sTwo_coeffs p p' Xc
  have h00 := coeff_zero_sZero p p' (kacC b) μ Xc
  set T := PowerSeries.coeff M (compR b' (quadS (sW0 p p' (kacC b) μ Xc) (sW1 p p' Xc)
    (sW2 p p'))) with hT
  have hmkexp : PowerSeries.mk b' = PowerSeries.exp ℂ := rfl
  have hHR : ψ (HR (kacC b) μ M) = C (((16 : ℂ) ^ M)⁻¹) * T := by
    refine Polynomial.funext fun w => ?_
    have hw0 : ptW p p' μ Xc w 0 = μ := rfl
    have hw1 : ptW p p' μ Xc w 1 = 0 := rfl
    have hc0 : PowerSeries.constantCoeff (sW0 p p' (kacC b) μ Xc + w • sW1 p p' Xc +
        w ^ 2 • sW2 p p') = 0 := by
      have e0 := h00
      have e1 := h10
      have e2 := h20
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at e0 e1 e2
      simp [e0, e1, e2]
    rw [hψ, eval_psiW, eval_HR hdets, evalAt_Hsph_collapse hw0 hw1 hdets, Sexp_ptW p p' (by omega)
      (by omega), eval_mul, eval_C, hT, eval_coeff_compR, map_quadS, compS_eq_subst b' hc0,
      hmkexp, div_eq_inv_mul]
  have hTM : T.coeff M ≠ 0 := by
    rw [hT, coeff_coeff_compR_quadS h10 h20 h21, h00, h11, h22, map_zero, zero_add]
    have hu : PowerSeries.constantCoeff (PowerSeries.C (-(2 * Xc / (p * p'))) * PowerSeries.X +
        PowerSeries.C (-(1 / ((p : ℂ) * p'))) * PowerSeries.X ^ 2) = 0 := by simp
    rw [compS_eq_subst b' hu, hmkexp]
    have hbc : -(2 * Xc / (p * p')) = -((bq : ℚ) : ℂ) := by rw [hbq, hXc]; push_cast; ring
    have hgc : -(1 / ((p : ℂ) * p')) = -((gq : ℚ) : ℂ) := by rw [hgq]; push_cast; ring
    rw [hbc, hgc]
    intro h0
    have hk' := coeff_exp_quad bq gq M
    rw [h0, zero_mul] at hk'
    have hne : kseq bq gq M ≠ 0 := by
      have hpq : (0 : ℚ) < p * p' := by positivity
      have hXq : (X : ℚ) ≠ 0 := by exact_mod_cast hX0.ne'
      have hr : bq ^ 2 / (4 * gq) = (X : ℚ) ^ 2 / (p * p') := by
        rw [hbq, hgq]
        field_simp
        ring
      obtain ⟨a2, a3⟩ := X_arith hp hp' hcop hXge (fun h6 => by
        rw [hX_def, hmb_def]; exact X_ne_three_exc hset (!ε) k h6)
      refine kseq_ne_zero hS (by rw [hbq]; positivity) (by rw [hgq]; positivity) ?_ ?_ M
      · rw [hr]
        intro h
        apply a2
        field_simp at h
        exact_mod_cast (by linarith : (2 : ℚ) * (X : ℚ) ^ 2 = (p : ℚ) * p')
      · rw [hr]
        intro h
        apply a3
        field_simp at h
        exact_mod_cast (by linarith : (2 : ℚ) * (X : ℚ) ^ 2 = 3 * (p : ℚ) * p')
    exact hne (by exact_mod_cast hk'.symm)
  have hHR0 : ψ (HR (kacC b) μ M) ≠ 0 := by
    rw [hHR]
    refine mul_ne_zero (by simp) ?_
    intro h0
    rw [h0, coeff_zero] at hTM
    exact hTM rfl
  -- assembly
  intro h0
  have h1 := congrArg ψ h0
  rw [map_add, hbig, add_zero, map_zero] at h1
  unfold topRH at h1
  rw [if_pos hsN, map_mul, map_mul, map_mul] at h1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hπ1 hπ2) hγC) hHR0 h1

end Pair

/-- Theorem 5.5 (sphere/paper.tex l.1693–1701, proof l.1703–1787).
Paper label: thm:sharp-H -/
theorem thm_sharp_H_of_cited (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hS : Cited_SchurHermite) : Stmt_thm_sharp_H := by
  intro p p' r s b hset N hN
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  obtain ⟨wp, wm, hsing, hjan, -, -⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsing, hjan⟩
  have hle := (thm_jantzen_bound_of_cited hJ p p' r s b hset N).2
  rcases Nat.eq_zero_or_pos (jDepth p p' r s N) with h0 | hk
  · rw [h0] at hle ⊢
    exact Nat.le_zero.1 hle
  obtain ⟨hN1, hN2⟩ := jDepth_range hp hp' hr hrp hs hsp hk
  generalize jDepth p p' r s N = k at hle hk hN1 hN2 ⊢
  have top := thm_top_layer_of_cited hI p p' r s b hset wp wm hT k N hk hN1 hN2
  have hcp : pbwCoord (ellPlus p p' r s k) (comp (ellPlus p p' r s k) (wp k)) = wp k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing k hk).1.2.1)
  have hcm : pbwCoord (ellMinus p p' r s k) (comp (ellMinus p p' r s k) (wm k)) = wm k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing k hk).2.2.1)
  obtain ⟨hpo, hpc⟩ := (top.2.2.2 _ _ hcp hcm).2
  have tp := top.2.1 _ hcp
  have tm := top.2.2.1 _ hcm
  have hsp' : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s k)
      (comp (ellPlus p p' r s k) (wp k))) (ellPlus p p' r s k) := by
    rw [hcp]; exact (hsing k hk).1
  have hsm' : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s k)
      (comp (ellMinus p p' r s k) (wm k))) (ellMinus p p' r s k) := by
    rw [hcm]; exact (hsing k hk).2
  have hplus : ellOrb p p' r s true k = ellPlus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  have hminus : ellOrb p p' r s (!true) k = ellMinus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  have hminus' : ellOrb p p' r s false k = ellMinus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  have hplus' : ellOrb p p' r s (!false) k = ellPlus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  refine poleOrder_eq_of_ppCoeff_ne hpo ?_
  rw [hpc]
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  rcases lt_or_gt_of_ne hne with hpm | hmp
  · have hpN : ellPlus p p' r s k ≤ N := (min_eq_left hpm.le).symm ▸ hN1
    exact sharpH_pair_ne hH hF hU hS hset hk true hplus hminus hpm hpN _ _ hsp' hsm'
      (tp hpN).1 (tp hpN).2 (fun h => (tm h).2)
  · have hmN : ellMinus p p' r s k ≤ N := (min_eq_right hmp.le).symm ▸ hN1
    rw [add_comm]
    exact sharpH_pair_ne hH hF hU hS hset hk false hminus' hplus' hmp hmN _ _ hsm' hsp'
      (tm hmN).1 (tm hmN).2 (fun h => (tp h).2)

example (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hS : Cited_SchurHermite) : Stmt_thm_sharp_H :=
  thm_sharp_H_of_cited hJ hI hH hF hU hS

end Virasoro.Sphere
