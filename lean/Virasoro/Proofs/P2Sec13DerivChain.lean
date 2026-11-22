import Virasoro.Proofs.P2Sec13Slope
import Virasoro.Proofs.P2Sec13KernelLift

/-!
# Lemma 13.1, Step 3: equation (13.3) (paper.tex l.2948–2983)

`g_B(b,Δ) = B_{c(b),Δ}(χ_{R₂,S₂}(b),χ_{R₂,S₂}(b))` is a polynomial in `Δ` over `ℂ[b,b⁻¹]` that
vanishes at `Δ = h_{R₂,S₂}(b)`; dividing by the monic factor `Δ - h_{R₂,S₂}(b)` and evaluating
along `Δ = h_{R₁,S₁}(b)`, `b = b⋆ + X`, gives
`[X¹] B_X(w₂,w₂) = [X¹](Δ₁ - Δ₂) · γ_{R₂,S₂}(b⋆)`, and the coefficient does not depend on the
lift of `w₂(0)`.
-/

namespace Virasoro.P2

open Virasoro Verma

section PS

open PowerSeries

/-- The coefficient of `X¹` of `Vᵀ T V` depends only on `V(0)` when `V(0)` lies in the left and
right kernels of `T(0)` (l.2978–2983, 3000–3003). -/
theorem coeff_one_lift_indep {ι : Type*} [Fintype ι] {T : Matrix ι ι ℂ⟦X⟧} {V V' : ι → ℂ⟦X⟧}
    (h0 : ∀ j, constantCoeff (V j) = constantCoeff (V' j))
    (hkerR : ∀ j, (X : ℂ⟦X⟧) ∣ (T.mulVec V') j)
    (hkerL : ∀ j, (X : ℂ⟦X⟧) ∣ (Matrix.vecMul V' T) j) :
    coeff 1 (V ⬝ᵥ T.mulVec V) = coeff 1 (V' ⬝ᵥ T.mulVec V') := by
  have hdiv : ∀ j, (X : ℂ⟦X⟧) ∣ V j - V' j := fun j => by
    rw [X_dvd_iff, map_sub, h0, sub_self]
  choose U hU using hdiv
  have hV : V = V' + (X : ℂ⟦X⟧) • U := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hU j]
    ring
  obtain ⟨q₁, hq₁⟩ : (X : ℂ⟦X⟧) ∣ U ⬝ᵥ T.mulVec V' := dvd_dot_right hkerR
  obtain ⟨q₂, hq₂⟩ : (X : ℂ⟦X⟧) ∣ V' ⬝ᵥ T.mulVec U := by
    rw [Matrix.dotProduct_mulVec]
    exact dvd_dot_left hkerL
  have hexp : V ⬝ᵥ T.mulVec V = V' ⬝ᵥ T.mulVec V' +
      (X : ℂ⟦X⟧) ^ 2 * (q₁ + q₂ + U ⬝ᵥ T.mulVec U) := by
    rw [hV]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hq₁, hq₂]
    ring
  rw [hexp, map_add, coeff_X_pow_mul']
  norm_num

end PS

open Polynomial

open scoped PowerSeries

theorem hom_eval' {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (P : R[X]) (x : R) :
    g (P.eval x) = (P.map g).eval (g x) := by
  conv_lhs => rw [← eval₂_id]
  rw [hom_eval₂, RingHom.comp_id, eval_map]

/-- For a polynomial `P(Δ)` over `ℂ[b,b⁻¹]` with `P(h₂(b)) = 0` and `h₁(b⋆) = h₂(b⋆)`:
`[X¹] P(h₁(b⋆+X)) = [X¹](h₁ - h₂)(b⋆+X) · ∂_Δ P|_{b⋆, Δ = h₂(b⋆)}` (l.2958–2977). -/
theorem coeff_one_of_root {b : ℂ} (hb : b ≠ 0) {P : Lam[X]} {h₁ h₂ : Lam}
    (hroot : P.eval h₂ = 0) (hμ : evLam b hb h₁ = evLam b hb h₂) :
    PowerSeries.coeff 1 (locLam b hb (P.eval h₁)) =
      PowerSeries.coeff 1 (locLam b hb (h₁ - h₂)) *
        (derivative (P.map (evLam b hb))).eval (evLam b hb h₂) := by
  have hfac := (mul_divByMonic_eq_iff_isRoot (p := P) (a := h₂)).2 hroot
  set Q := P /ₘ (X - C h₂) with hQ
  have h1 : P.eval h₁ = (h₁ - h₂) * Q.eval h₁ := by
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_sub, eval_X, eval_C]
  have h2 : (derivative (P.map (evLam b hb))).eval (evLam b hb h₂) =
      (Q.map (evLam b hb)).eval (evLam b hb h₁) := by
    conv_lhs => rw [← hfac]
    simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, derivative_mul,
      derivative_sub, derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul, add_zero, sub_zero, one_mul, hμ]
  have hA : PowerSeries.constantCoeff (locLam b hb (h₁ - h₂)) = 0 := by
    rw [constantCoeff_locLam, map_sub, hμ, sub_self]
  rw [h1, map_mul, coeff_one_mul_of_constantCoeff_zero hA, constantCoeff_locLam, hom_eval', h2]

/-- A singular vector of positive level lies in the kernel of the Gram matrix. -/
theorem gram_mulVec_singular {c h : ℂ} {n : ℕ} (hn : 1 ≤ n) {x : Nat.Partition n → ℂ}
    (hx : IsSingular (pbwCoord (c := c) (h := h) n x) n) : (gram c h n).mulVec x = 0 := by
  classical
  funext Y
  rw [gram_mulVec_eq_gramForm, ← shap_pbwCoord]
  have h1 := shap_singular c h hx hn [] (pbwCoord n (Pi.single Y 1))
  rwa [negOp_nil_smul] at h1

/-- The Laurent family through a singular vector `x₂` of level `RS` at `b⋆` (l.2906–2910,
2946–2948): `x₂ = a · χ_{R,S}(b⋆)` with the normalized family `χ_{R,S}(b)` over `ℂ[b,b⁻¹]`. -/
theorem lam_setup (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    (hLau : Cited_SingularFamilyLaurent) {b : ℂ} (hb : b ≠ 0) {R S : ℕ} (hR : 0 < R)
    (hS : 0 < S) {x₂ : Nat.Partition (R * S) → ℂ}
    (hx₂ : IsSingular (pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x₂) (R * S)) :
    ∃ (pf : Nat.Partition (R * S) → RatFunc ℚ) (xLam : Nat.Partition (R * S) → Lam) (a : ℂ),
      a ≠ 0 ∧ pf (onesPartition (R * S)) = 1 ∧
      IsSingular (pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH R S RatFunc.X)
        (R * S) pf) (R * S) ∧
      (∀ (b' : ℂ) (hb' : b' ≠ 0) (Y : Nat.Partition (R * S)),
        evLam b' hb' (xLam Y) = RatFunc.eval (algebraMap ℚ ℂ) b' (pf Y)) ∧
      (∀ (b' : ℂ) (hb' : b' ≠ 0), IsSingular (pbwCoord (c := kacC b') (h := kacH R S b')
        (R * S) fun Y => evLam b' hb' (xLam Y)) (R * S)) ∧
      x₂ = a • fun Y => evLam b hb (xLam Y) := by
  obtain ⟨p, ⟨hp1, hsing⟩, -, -, -, hspec⟩ := normalization_at hH R S hR hS
  choose f n hf using hLau R S hR hS p hp1 hsing
  set xLam : Nat.Partition (R * S) → Lam := fun Y =>
    algebraMap ℂ[X] Lam (((f Y).map (algebraMap ℚ ℂ)).comp (X ^ 2)) * lamXi ^ (2 * n Y) with hxLam
  have hxev : ∀ (b' : ℂ) (hb' : b' ≠ 0) (Y : Nat.Partition (R * S)),
      evLam b' hb' (xLam Y) = RatFunc.eval (algebraMap ℚ ℂ) b' (p Y) := by
    intro b' hb' Y
    have h1 : EvTo b' (p Y)
        ((f Y).eval₂ (algebraMap ℚ ℂ) (b' ^ 2) / b' ^ (2 * n Y)) := by
      rw [hf Y]
      exact (evTo_aeval (f Y) (evTo_X.pow 2)).div (evTo_X.pow (2 * n Y)) (pow_ne_zero _ hb')
    rw [h1.2, hxLam]
    simp only [map_mul, map_pow, evLam_algebraMap, evLam_lamXi, eval_comp, eval_pow, eval_X,
      eval_map]
    rw [div_eq_mul_inv, inv_pow]
  have hxs : ∀ (b' : ℂ) (hb' : b' ≠ 0), IsSingular (pbwCoord (c := kacC b') (h := kacH R S b')
      (R * S) fun Y => evLam b' hb' (xLam Y)) (R * S) := by
    intro b' hb'
    have e : (fun Y => evLam b' hb' (xLam Y)) =
        fun Y => RatFunc.eval (algebraMap ℚ ℂ) b' (p Y) := funext (hxev b' hb')
    rw [e]
    exact (hspec ℂ b' hb' fun Y => regular_of_normalized hR hS p hp1 hsing hb' Y).1
  obtain ⟨a, ha⟩ := hU _ _ _ _ _ (hxs b hb) hx₂
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx₂.1 (ha.trans (zero_smul ℂ (pbwCoord (c := kacC b) (h := kacH R S b) (R * S)
      fun Y => evLam b hb (xLam Y))))
  refine ⟨p, xLam, a, ha0, hp1, hsing, hxev, hxs, ?_⟩
  have h2 := congrArg (Verma.comp (R * S)) ha
  rwa [comp_pbwCoord_same, map_smul, comp_pbwCoord_same] at h2

set_option maxHeartbeats 1600000 in
/-- Equation (13.3), first line, with its value: for every lift `V₂` of a singular vector
`x₂ = a χ_{R₂,S₂}(b⋆)`, `[X¹] B_X(V₂,V₂) = a² · [X¹](Δ₁ - Δ₂) · γ_{R₂,S₂}(b⋆)`, and the three
factors are nonzero. -/
theorem tau_first_order_gram (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hLau : Cited_SingularFamilyLaurent) :
    Stmt_sub_tau_deriv_chain := by
  classical
  intro p p' r s b hset ε k₀ ε₁ R₁ S₁ R S hlab₁ hlab₂ x₂ hx₂ V₂ hV₂
  obtain ⟨-, -, hμ₁, -⟩ := arrow_facts hset ε k₀ ε₁ hlab₁
  obtain ⟨hR, hS, hμ₂, -⟩ := arrow_facts hset ε k₀ (!ε₁) hlab₂
  have hb := minimalSetting_b_ne_zero hset
  have hRS : 1 ≤ R * S := Nat.mul_pos hR hS
  have hs := slope_ne_zero hJ hH hset ε k₀ ε₁ hlab₁ hlab₂
  obtain ⟨pf, xLam, a, ha0, hp1, hsingQ, hxev, hxs, hx₂a⟩ := lam_setup hH hU hLau hb hR hS hx₂
  -- `γ_{R₂,S₂}(b⋆) ≠ 0` (Lemma 10.3(iii))
  have hγ : crossScalar (kacC b) (kacH R S b) (fun Y => evLam b hb (xLam Y)) ≠ 0 := by
    obtain ⟨R', S', -, -, hlab', -, -, -, -, -, -, -, -, -, -, -, hγ'⟩ :=
      ((lem_bgg_arrows_of_cited hJ hH p p' r s b hset).2 ε k₀).2.1 (!ε₁)
    rw [hlab₂, Prod.mk.injEq] at hlab'
    obtain ⟨e1, e2⟩ := hlab'
    have e1' : R = R' := by exact_mod_cast e1
    have e2' : S = S' := by exact_mod_cast e2
    subst e1' e2'
    have e : (fun Y => evLam b hb (xLam Y)) =
        fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (pf Y) := funext (hxev b hb)
    rw [e]
    exact hγ' pf hp1 hsingQ
  -- the polynomial `g_B(b,Δ)`
  set P : Lam[X] := gramForm (C cLam) (X : Lam[X]) (R * S) (fun Y => C (xLam Y))
    (fun Y => C (xLam Y)) with hP
  have hPe : ∀ h : Lam, P.eval h = gramForm cLam h (R * S) xLam xLam := by
    intro h
    have h1 := map_gramForm (evalRingHom h) (C cLam) (X : Lam[X]) (R * S)
      (fun Y => C (xLam Y)) (fun Y => C (xLam Y))
    simp only [coe_evalRingHom, eval_C, eval_X] at h1
    exact h1
  have hPm : P.map (evLam b hb) = gramForm (C (kacC b)) (X : ℂ[X]) (R * S)
      (fun Y => C (evLam b hb (xLam Y))) (fun Y => C (evLam b hb (xLam Y))) := by
    have h1 := map_gramForm (mapRingHom (evLam b hb)) (C cLam) (X : Lam[X]) (R * S)
      (fun Y => C (xLam Y)) (fun Y => C (xLam Y))
    simp only [coe_mapRingHom, map_C, map_X, evLam_cLam] at h1
    exact h1
  have hroot : P.eval (hLam R S) = 0 := by
    rw [hPe]
    refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' _ => ?_
    rw [map_gramForm, evLam_cLam, evLam_hLam, ← shap_pbwCoord]
    have h1 := shap_singular (kacC b') (kacH R S b') (hxs b' hb') hRS []
      (pbwCoord (R * S) fun Y => evLam b' hb' (xLam Y))
    rwa [negOp_nil_smul] at h1
  have hμ : evLam b hb (hLam R₁ S₁) = evLam b hb (hLam R S) := by
    rw [evLam_hLam, evLam_hLam]
    exact hμ₁.trans hμ₂.symm
  have hc := coeff_one_of_root hb hroot hμ
  rw [hPe, hPm, evLam_hLam, map_sub, locLam_hLam, locLam_hLam] at hc
  -- the lift `a · χ_{R₂,S₂}(b⋆+X)`
  set V₀ : Nat.Partition (R * S) → ℂ⟦X⟧ := fun Y => locLam b hb (xLam Y) with hV₀
  set V' : Nat.Partition (R * S) → ℂ⟦X⟧ := (PowerSeries.C a : ℂ⟦X⟧) • V₀ with hV'
  have hform : V₀ ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V₀ =
      locLam b hb (gramForm cLam (hLam R₁ S₁) (R * S) xLam xLam) := by
    rw [map_gramForm, locLam_cLam, locLam_hLam]
    rfl
  have h0 : ∀ Y, PowerSeries.constantCoeff (V₂ Y) = PowerSeries.constantCoeff (V' Y) := by
    intro Y
    rw [hV₂ Y, hx₂a, hV', hV₀]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, PowerSeries.constantCoeff_C,
      constantCoeff_locLam]
  have hG0 : (gram (kacC b) (kacH R₁ S₁ b) (R * S)).mulVec x₂ = 0 := by
    rw [hμ₁, ← hμ₂]
    exact gram_mulVec_singular hRS hx₂
  have hkerR : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ∣
      ((gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V') Y := by
    intro Y
    rw [PowerSeries.X_dvd_iff]
    have h1 := map_mulVec_apply (PowerSeries.constantCoeff (R := ℂ))
      (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)) V' Y
    rw [← gram_map, constantCoeff_cLoc, constantCoeff_hLoc] at h1
    rw [← h1]
    have e : (fun Z => PowerSeries.constantCoeff (V' Z)) = x₂ := by
      funext Z
      rw [← h0 Z, hV₂ Z]
    rw [e, hG0]
    rfl
  have hkerL : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ∣
      (Matrix.vecMul V' (gram (cLoc b) (hLoc R₁ S₁ b) (R * S))) Y := by
    intro Y
    have e : Matrix.vecMul V' (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)) =
        (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V' := by
      rw [← Matrix.mulVec_transpose, gram_transpose]
    rw [e]
    exact hkerR Y
  rw [coeff_one_lift_indep h0 hkerR hkerL]
  have hscale : V' ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V' =
      PowerSeries.C a * (PowerSeries.C a *
        (V₀ ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R * S)).mulVec V₀)) := by
    rw [hV']
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hscale, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hform, hc]
  exact mul_ne_zero ha0 (mul_ne_zero ha0 (mul_ne_zero hs hγ))

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hLau : Cited_SingularFamilyLaurent) :
    Stmt_sub_tau_deriv_chain := tau_first_order_gram hJ hH hU hLau

end Virasoro.P2
