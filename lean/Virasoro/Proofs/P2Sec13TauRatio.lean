import Virasoro.Proofs.P2Sec13TauFinal
import Virasoro.Proofs.P2Sec13BoxLimit
import Virasoro.Proofs.P2Sec9BoxFinal
import Virasoro.Proofs.P2Sec13GenLayers

/-!
# Lemma 13.1, Step 3/4: equation (13.3), second line, and the ratio (paper.tex l.2948–2977,
3012–3023)

`g_ρ(b,Δ) = ρ_{c(b),Δ,h_{u,v}(b)}(χ_{R₂,S₂}(b),χ_{R₂,S₂}(b))` vanishes along `Δ = h_{R₂,S₂}(b)`
(`0 ≤ k < R₂`, `0 ≤ m < S₂`), so `[X¹] ρ_X(w₂,w₂) = [X¹](Δ₁ - Δ₂) · ∂_Δ g_ρ(b⋆,μ)`, as for `g_B`.
The rational identity of Theorem 9.2, `∂_Δ g_ρ · boxDen = ∂_Δ g_B · boxNum` at generic `b`, holds
in `ℂ[b,b⁻¹]` after clearing the reduced denominator of `c_{R₂,S₂}(t;u,v)`, and specializes at
`b⋆`, where the reduced denominator is nonzero and the value is `Ω_{u,v}(μ→ν₂)`
(Proposition 12.1(i)).
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial

open scoped PowerSeries

/-- The fusion box condition for an arrow label (paper.tex l.2880–2881): `k < R`, `m < S`. -/
theorem box_of_label {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) {k m : ℕ}
    (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (ε : Bool) (j : ℕ) (ε' : Bool) {R S : ℕ}
    (hlab : arrowLabel p p' (nOrb p p' r s ε j) (nOrb p p' r s ε' (j + 1)) =
      ((R : ℤ), (S : ℤ))) : k < R ∧ m < S := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨R', S', hR, hS, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε j ε'
  have hL := arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)
  rw [hlab, Prod.mk.injEq] at hL
  obtain ⟨e1, e2⟩ := hL
  have e1' : R = R' := by exact_mod_cast e1
  have e2' : S = S' := by exact_mod_cast e2
  subst e1' e2'
  have h1 : min r (p - r) ≤ R := by
    obtain ⟨a, ha | ha⟩ := hcR
    · rw [ha]; exact (min_le_left _ _).trans (Nat.le_add_left _ _)
    · rw [ha]; exact (min_le_right _ _).trans (Nat.le_add_left _ _)
  have h2 : min s (p' - s) ≤ S := by
    obtain ⟨a, ha | ha⟩ := hcS
    · rw [ha]; exact (min_le_left _ _).trans (Nat.le_add_left _ _)
    · rw [ha]; exact (min_le_right _ _).trans (Nat.le_add_left _ _)
  exact ⟨lt_of_lt_of_le hk h1, lt_of_lt_of_le hm h2⟩

set_option maxHeartbeats 3200000 in
/-- `Stmt_sub_tau_ratio`: equation (13.3), second line, and the ratio
`g̃_ρ(t₀,μ)/γ_{R₂,S₂}(b⋆) = c_{R₂,S₂}(t₀;u,v) = Ω_{u,v}(μ→ν₂)` (paper.tex l.2948–2977,
3012–3023). -/
theorem sub_tau_ratio_of_cited (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) : Stmt_sub_tau_ratio := by
  classical
  intro p p' r s b hset k m hk hm ε k₀ ε₁ R₁ S₁ R S hlab₁ hlab₂ x₂ hx₂ V₂ hV₂
  obtain ⟨-, -, hμ₁, -⟩ := arrow_facts hset ε k₀ ε₁ hlab₁
  obtain ⟨hR, hS, hμ₂, -⟩ := arrow_facts hset ε k₀ (!ε₁) hlab₂
  obtain ⟨hkR, hmS⟩ := box_of_label hset hk hm ε k₀ (!ε₁) hlab₂
  have hb := minimalSetting_b_ne_zero hset
  have hRS : 1 ≤ R * S := Nat.mul_pos hR hS
  have hLay := sub_generic_layers_of_cited hK hE hH hU hF
  obtain ⟨pf, xLam, a, ha0, hp1, hsingQ, hxev, hxs, hx₂a⟩ := lam_setup hH hU hLau hb hR hS hx₂
  -- the polynomials `g_B(b,Δ)` and `g_ρ(b,Δ)` over `ℂ[b,b⁻¹]`
  set PB : Lam[X] := gramForm (C cLam) (X : Lam[X]) (R * S) (fun Y => C (xLam Y))
    (fun Y => C (xLam Y)) with hPB
  set PT : Lam[X] := torusForm (C cLam) (X : Lam[X]) (C (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)))
    (R * S) (fun Y => C (xLam Y)) (fun Y => C (xLam Y)) with hPT
  have hPBe : ∀ h : Lam, PB.eval h = gramForm cLam h (R * S) xLam xLam := by
    intro h
    have h1 := map_gramForm (evalRingHom h) (C cLam) (X : Lam[X]) (R * S)
      (fun Y => C (xLam Y)) (fun Y => C (xLam Y))
    simp only [coe_evalRingHom, eval_C, eval_X] at h1
    exact h1
  have hPTe : ∀ h : Lam, PT.eval h =
      torusForm cLam h (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S) xLam xLam := by
    intro h
    have h1 := map_torusForm (evalRingHom h) (C cLam) (X : Lam[X])
      (C (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1))) (R * S)
      (fun Y => C (xLam Y)) (fun Y => C (xLam Y))
    simp only [coe_evalRingHom, eval_C, eval_X] at h1
    exact h1
  have hPBm : ∀ (b' : ℂ) (hb' : b' ≠ 0), PB.map (evLam b' hb') =
      gramForm (C (kacC b')) (X : ℂ[X]) (R * S)
        (fun Y => C (evLam b' hb' (xLam Y))) (fun Y => C (evLam b' hb' (xLam Y))) := by
    intro b' hb'
    have h1 := map_gramForm (mapRingHom (evLam b' hb')) (C cLam) (X : Lam[X]) (R * S)
      (fun Y => C (xLam Y)) (fun Y => C (xLam Y))
    simp only [coe_mapRingHom, map_C, map_X, evLam_cLam] at h1
    exact h1
  have hPTm : ∀ (b' : ℂ) (hb' : b' ≠ 0), PT.map (evLam b' hb') =
      torusForm (C (kacC b')) (X : ℂ[X]) (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b'))
        (R * S) (fun Y => C (evLam b' hb' (xLam Y))) (fun Y => C (evLam b' hb' (xLam Y))) := by
    intro b' hb'
    have h1 := map_torusForm (mapRingHom (evLam b' hb')) (C cLam) (X : Lam[X])
      (C (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1))) (R * S)
      (fun Y => C (xLam Y)) (fun Y => C (xLam Y))
    simp only [coe_mapRingHom, map_C, map_X, evLam_cLam, evLam_hLam] at h1
    exact h1
  -- the roots along `Δ = h_{R₂,S₂}(b)`
  have hrootB : PB.eval (hLam R S) = 0 := by
    rw [hPBe]
    refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' _ => ?_
    rw [map_gramForm, evLam_cLam, evLam_hLam, ← shap_pbwCoord]
    have h1 := shap_singular (kacC b') (kacH R S b') (hxs b' hb') hRS []
      (pbwCoord (R * S) fun Y => evLam b' hb' (xLam Y))
    rwa [negOp_nil_smul] at h1
  have hTL : (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)).mulVec
        xLam = 0 ∧
      Matrix.vecMul xLam
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)) = 0 := by
    have hgen : ∀ (b' : ℂ) (hb' : b' ≠ 0), (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → ∀ Y,
        (torus (kacC b') (kacH R S b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b')
            (R * S)).mulVec (fun Y => evLam b' hb' (xLam Y)) Y = 0 ∧
          Matrix.vecMul (fun Y => evLam b' hb' (xLam Y))
            (torus (kacC b') (kacH R S b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b')
              (R * S)) Y = 0 := by
      intro b' hb' hirr Y
      have hd := generic_descends hH hU hF hLay hb' hirr hR hS hkR hmS
      have h2 := torusForm_ker_of_descends hd (gram_mulVec_singular hRS (hxs b' hb'))
        (Pi.single Y 1)
      rw [torus_mulVec_eq_torusForm, torus_vecMul_eq_torusForm]
      exact ⟨h2.2, h2.1⟩
    constructor
    · funext Y
      refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' hG' => ?_
      have h1 := map_mulVec_apply (evLam b' hb')
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)) xLam Y
      rw [← torus_map, evLam_cLam hb', evLam_hLam hb' R S, evLam_hLam hb',
        (hgen b' hb' hG'.2.1 Y).1] at h1
      exact h1.symm
    · funext Y
      refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' hG' => ?_
      have h1 := map_vecMul_apply (evLam b' hb')
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)) xLam Y
      rw [← torus_map, evLam_cLam hb', evLam_hLam hb' R S, evLam_hLam hb',
        (hgen b' hb' hG'.2.1 Y).2] at h1
      exact h1.symm
  have hrootT : PT.eval (hLam R S) = 0 := by
    rw [hPTe]
    unfold torusForm
    rw [hTL.1, dotProduct_zero]
  have hμ : evLam b hb (hLam R₁ S₁) = evLam b hb (hLam R S) := by
    rw [evLam_hLam, evLam_hLam]
    exact hμ₁.trans hμ₂.symm
  have hcB := coeff_one_of_root hb hrootB hμ
  have hcT := coeff_one_of_root hb hrootT hμ
  rw [hPBe, hPBm b hb, evLam_hLam, map_sub, locLam_hLam, locLam_hLam] at hcB
  rw [hPTe, hPTm b hb, evLam_hLam, map_sub, locLam_hLam, locLam_hLam] at hcT
  -- Theorem 9.2 in `ℂ[b,b⁻¹]` and its value at `b⋆`
  set TL : Lam := (derivative PT).eval (hLam R S) with hTLdef
  set CL : Lam := (derivative PB).eval (hLam R S) with hCLdef
  have hTev : ∀ (b' : ℂ) (hb' : b' ≠ 0), evLam b' hb' TL =
      torusCrossScalar (kacC b') (kacH R S b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b')
        (fun Y => evLam b' hb' (xLam Y)) := by
    intro b' hb'
    rw [hTLdef, hom_eval', ← Polynomial.derivative_map, hPTm b' hb', evLam_hLam]
    rfl
  have hCev : ∀ (b' : ℂ) (hb' : b' ≠ 0), evLam b' hb' CL =
      crossScalar (kacC b') (kacH R S b') (fun Y => evLam b' hb' (xLam Y)) := by
    intro b' hb'
    rw [hCLdef, hom_eval', ← Polynomial.derivative_map, hPBm b' hb', evLam_hLam]
    rfl
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  obtain ⟨-, hden, hval, -⟩ := (prop_bgg_cocycle p p' r s b hset k m hk hm).1 ε k₀ (!ε₁)
  simp only [hlab₂] at hden hval
  set ρ : RatFunc ℚ := boxRatio (R : ℤ) (S : ℤ) k m with hρ
  set n : ℚ[X] := ρ.num with hn
  set dn : ℚ[X] := ρ.denom with hdn
  have hdn0 : dn ≠ 0 := RatFunc.denom_ne_zero ρ
  have hcross : n * boxDenPoly (R : ℤ) (S : ℤ) = boxNumPoly (R : ℤ) (S : ℤ) k m * dn := by
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    have h1 : algebraMap ℚ[X] (RatFunc ℚ) n / algebraMap ℚ[X] (RatFunc ℚ) dn =
        algebraMap ℚ[X] (RatFunc ℚ) (boxNumPoly (R : ℤ) (S : ℤ) k m) /
          algebraMap ℚ[X] (RatFunc ℚ) (boxDenPoly (R : ℤ) (S : ℤ)) := RatFunc.num_div_denom ρ
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero hdn0)
      (RatFunc.algebraMap_ne_zero (boxDenPoly_ne_zero _ _))] at h1
    rw [map_mul, map_mul]
    exact h1
  set NL : Lam := algebraMap ℂ[X] Lam ((n.map (algebraMap ℚ ℂ)).comp (X ^ 2)) with hNL
  set DL : Lam := algebraMap ℂ[X] Lam ((dn.map (algebraMap ℚ ℂ)).comp (X ^ 2)) with hDL
  have hNev : ∀ (b' : ℂ) (hb' : b' ≠ 0),
      evLam b' hb' NL = (n.map (algebraMap ℚ ℂ)).eval (b' ^ 2) := by
    intro b' hb'
    rw [hNL, evLam_algebraMap, eval_comp, eval_pow, eval_X]
  have hDev : ∀ (b' : ℂ) (hb' : b' ≠ 0),
      evLam b' hb' DL = (dn.map (algebraMap ℚ ℂ)).eval (b' ^ 2) := by
    intro b' hb'
    rw [hDL, evLam_algebraMap, eval_comp, eval_pow, eval_X]
  have hzero : TL * DL - CL * NL = 0 := by
    refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' hG' => ?_
    obtain ⟨hbd, -, heq, -, -⟩ := thm_first_layer_ratio_of_cited hE hH hU hF b' hb' hG'.2.1
      R S k m hR hS hkR hmS _ (hxs b' hb')
    rw [map_sub, map_mul, map_mul, hTev, hCev, hNev, hDev]
    have hc := congrArg (fun f : ℚ[X] => (f.map (algebraMap ℚ ℂ)).eval (b' ^ 2)) hcross
    simp only [Polynomial.map_mul, eval_mul, boxDenPoly_eval, boxNumPoly_eval] at hc
    apply mul_right_cancel₀ hbd
    linear_combination ((dn.map (algebraMap ℚ ℂ)).eval (b' ^ 2)) * heq -
      (crossScalar (kacC b') (kacH R S b') (fun Y => evLam b' hb' (xLam Y))) * hc
  have h0 := congrArg (evLam b hb) hzero
  rw [map_sub, map_mul, map_mul, hTev, hCev, hNev, hDev, map_zero] at h0
  have ht0 : b ^ 2 = ((-(p' : ℚ) / p : ℚ) : ℂ) := by
    rw [hbsq]
    push_cast
    rfl
  rw [ht0, eval_map_ratCast, eval_map_ratCast] at h0
  have hdnc : ((dn.eval (-(p' : ℚ) / p) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hden
  have hcA : (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) =
      ((n.eval (-(p' : ℚ) / p) : ℚ) : ℂ) / ((dn.eval (-(p' : ℚ) / p) : ℚ) : ℂ) := by
    have h1 : RatFunc.eval (RingHom.id ℚ) (-(p' : ℚ) / p) ρ =
        n.eval (-(p' : ℚ) / p) / dn.eval (-(p' : ℚ) / p) := by
      simp only [RatFunc.eval, Polynomial.eval₂_id]
      rfl
    have h2 : (cArrow p p' r s k m ε k₀ (!ε₁) : ℚ) = cMM p p' (R : ℤ) (S : ℤ) k m := by
      unfold cArrow
      rw [hlab₂]
    rw [h2, ← hval, h1]
    push_cast
    rfl
  have hTC : torusCrossScalar (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
        (fun Y => evLam b hb (xLam Y)) =
      (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) *
        crossScalar (kacC b) (kacH R S b) (fun Y => evLam b hb (xLam Y)) := by
    rw [hcA, div_mul_eq_mul_div, eq_div_iff hdnc]
    linear_combination h0
  -- the lift `a · χ_{R₂,S₂}(b⋆+X)` and lift independence
  set V₀ : Nat.Partition (R * S) → ℂ⟦X⟧ := fun Y => locLam b hb (xLam Y) with hV₀
  set V' : Nat.Partition (R * S) → ℂ⟦X⟧ := (PowerSeries.C a : ℂ⟦X⟧) • V₀ with hV'
  have hformB : V₀ ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V₀ =
      locLam b hb (gramForm cLam (hLam R₁ S₁) (R * S) xLam xLam) := by
    rw [map_gramForm, locLam_cLam, locLam_hLam]
    rfl
  have hformT : V₀ ⬝ᵥ (torus (cLoc b) (hLoc R₁ S₁ b)
        (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S)).mulVec V₀ =
      locLam b hb (torusForm cLam (hLam R₁ S₁) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)
        xLam xLam) := by
    rw [map_torusForm, locLam_cLam, locLam_hLam, locLam_hLam]
    rfl
  have h0' : ∀ Y, PowerSeries.constantCoeff (V₂ Y) = PowerSeries.constantCoeff (V' Y) := by
    intro Y
    rw [hV₂ Y, hx₂a, hV', hV₀]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, PowerSeries.constantCoeff_C,
      constantCoeff_locLam]
  have hc0 : (fun Z => PowerSeries.constantCoeff (V' Z)) = x₂ := by
    funext Z
    rw [← h0' Z, hV₂ Z]
  have hG0 : (gram (kacC b) (kacH R₁ S₁ b) (R * S)).mulVec x₂ = 0 := by
    rw [hμ₁, ← hμ₂]
    exact gram_mulVec_singular hRS hx₂
  have hT0 : (torus (kacC b) (kacH R₁ S₁ b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
        (R * S)).mulVec x₂ = 0 ∧
      Matrix.vecMul x₂ (torus (kacC b) (kacH R₁ S₁ b)
        (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S)) = 0 := by
    rw [hμ₁, ← hμ₂, hx₂a]
    constructor
    · rw [Matrix.mulVec_smul]
      funext Y
      have h1 := map_mulVec_apply (evLam b hb)
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)) xLam Y
      rw [← torus_map, evLam_cLam hb, evLam_hLam hb R S, evLam_hLam hb, hTL.1] at h1
      rw [Pi.smul_apply, h1]
      simp
    · rw [Matrix.smul_vecMul]
      funext Y
      have h1 := map_vecMul_apply (evLam b hb)
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) (R * S)) xLam Y
      rw [← torus_map, evLam_cLam hb, evLam_hLam hb R S, evLam_hLam hb, hTL.2] at h1
      rw [Pi.smul_apply, h1]
      simp
  have hkerRB : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ∣
      ((gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V') Y := by
    intro Y
    rw [PowerSeries.X_dvd_iff]
    have h1 := map_mulVec_apply (PowerSeries.constantCoeff (R := ℂ))
      (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)) V' Y
    rw [← gram_map, constantCoeff_cLoc, constantCoeff_hLoc] at h1
    rw [← h1, hc0, hG0]
    rfl
  have hkerLB : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ∣
      (Matrix.vecMul V' (gram (cLoc b) (hLoc R₁ S₁ b) (R * S))) Y := by
    intro Y
    have e : Matrix.vecMul V' (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)) =
        (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V' := by
      rw [← Matrix.mulVec_transpose, gram_transpose]
    rw [e]
    exact hkerRB Y
  have hkerRT : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ∣
      ((torus (cLoc b) (hLoc R₁ S₁ b) (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
        (R * S)).mulVec V') Y := by
    intro Y
    rw [PowerSeries.X_dvd_iff]
    have h1 := map_mulVec_apply (PowerSeries.constantCoeff (R := ℂ))
      (torus (cLoc b) (hLoc R₁ S₁ b) (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S)) V' Y
    rw [← torus_map, constantCoeff_cLoc, constantCoeff_hLoc, constantCoeff_hLoc] at h1
    rw [← h1, hc0, hT0.1]
    rfl
  have hkerLT : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ∣
      (Matrix.vecMul V' (torus (cLoc b) (hLoc R₁ S₁ b)
        (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S))) Y := by
    intro Y
    rw [PowerSeries.X_dvd_iff]
    have h1 := map_vecMul_apply (PowerSeries.constantCoeff (R := ℂ))
      (torus (cLoc b) (hLoc R₁ S₁ b) (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S)) V' Y
    rw [← torus_map, constantCoeff_cLoc, constantCoeff_hLoc, constantCoeff_hLoc] at h1
    rw [← h1, hc0, hT0.2]
    rfl
  rw [coeff_one_lift_indep h0' hkerRT hkerLT, coeff_one_lift_indep h0' hkerRB hkerLB]
  have hscaleB : V' ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V' =
      PowerSeries.C a * (PowerSeries.C a *
        (V₀ ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V₀)) := by
    rw [hV']
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have hscaleT : V' ⬝ᵥ (torus (cLoc b) (hLoc R₁ S₁ b)
        (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S)).mulVec V' =
      PowerSeries.C a * (PowerSeries.C a *
        (V₀ ⬝ᵥ (torus (cLoc b) (hLoc R₁ S₁ b)
          (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R * S)).mulVec V₀)) := by
    rw [hV']
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hscaleT, hscaleB, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, hformT, hformB, hcT, hcB]
  have e1 : (derivative (torusForm (C (kacC b)) (X : ℂ[X])
      (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)) (R * S)
      (fun Y => C (evLam b hb (xLam Y))) (fun Y => C (evLam b hb (xLam Y))))).eval (kacH R S b) =
      torusCrossScalar (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
        (fun Y => evLam b hb (xLam Y)) := rfl
  have e2 : (derivative (gramForm (C (kacC b)) (X : ℂ[X]) (R * S)
      (fun Y => C (evLam b hb (xLam Y))) (fun Y => C (evLam b hb (xLam Y))))).eval (kacH R S b) =
      crossScalar (kacC b) (kacH R S b) (fun Y => evLam b hb (xLam Y)) := rfl
  rw [e1, e2, hTC]
  ring

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) : Stmt_sub_tau_ratio :=
  sub_tau_ratio_of_cited hK hE hH hU hF hLau

end Virasoro.P2
