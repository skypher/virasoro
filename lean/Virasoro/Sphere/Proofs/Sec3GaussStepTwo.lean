import Virasoro.Sphere.Proofs.Sec3GaussSaddleI0

/-!
# `e^{-λ²𝓘₀} ℬ(z)` as a Gaussian expectation at the saddle point (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.663–684.  After completing the square, the saddle value `e^{λ²𝓘₀(z)}` factors
out: in `ℂ((t))[[z]]/(z^{n+1})`, the coefficient of `z^n` of `e^{-λ²𝓘₀(z)} ℬ(z)` is that of
`𝔼_{Q₀}[e^q R(x + λ(σ_*, σ̄_*))]`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

/-- The exponential of a series without constant term, modulo `z^{N+1}`. -/
theorem mkT_exp_subst {A : Type*} [CommRing A] [Algebra ℚ A] {N : ℕ} (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) :
    mkT N A ((PowerSeries.exp A).subst g) = IsNilpotent.exp (mkT N A g) := by
  classical
  obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
  have hpow : (mkT N A (PowerSeries.X * g')) ^ (N + 1) = 0 := by
    rw [map_mul, mul_pow, mkT_X_pow, zero_mul]
  rw [IsNilpotent.exp_eq_sum hpow]
  refine ext_cf fun j hj => ?_
  rw [cf_mkT hj, cf_sum _ _ hj]
  have hterm : ∀ d : ℕ, cfT j ((d.factorial : ℚ)⁻¹ • mkT N A (PowerSeries.X * g') ^ d) =
      algebraMap ℚ A (1 / d.factorial) * PowerSeries.coeff j ((PowerSeries.X * g') ^ d) := by
    intro d
    rw [Algebra.smul_def ((d.factorial : ℚ)⁻¹) (mkT N A (PowerSeries.X * g') ^ d),
      algebraMap_TR, ← map_pow, ← map_mul, cf_mkT hj, PowerSeries.coeff_C_mul, one_div]
  rw [Finset.sum_congr rfl fun d _ => hterm d]
  have hs : PowerSeries.HasSubst (PowerSeries.X * g') :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hz : ∀ d : ℕ, N + 1 ≤ d → PowerSeries.coeff j ((PowerSeries.X * g') ^ d) = 0 := by
    intro d hd
    rw [mul_pow]
    exact PowerSeries.X_pow_dvd_iff.1 (dvd_mul_right _ _) j (by omega)
  have hsupp : (Function.support fun d : ℕ => PowerSeries.coeff d (PowerSeries.exp A) •
      MvPowerSeries.coeff (Finsupp.single () j) ((PowerSeries.X * g') ^ d)) ⊆
      ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact hd (by
      show _ • PowerSeries.coeff j ((PowerSeries.X * g') ^ d) = 0
      rw [hz d (by omega), smul_zero])
  show MvPowerSeries.coeff (Finsupp.single () j) ((PowerSeries.exp A).subst (PowerSeries.X * g'))
    = _
  rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [PowerSeries.coeff_exp, smul_eq_mul]
  rfl

section StepTwo

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

theorem constantCoeff_I0def :
    PowerSeries.constantCoeff (I0def sigmaStar (fun m => -sigmaStar m)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_I0def_sigmaStar]
  have h := constantCoeff_I0Q
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, I0Q, PowerSeries.coeff_mk] at h
  rw [h]
  simp

include hF hK in
/-- Steps 1–2 of Lemma 3.3(iii) (sphere/paper.tex l.637–684): the coefficient of `z^n` of
`e^{-λ²𝓘₀(z)} ℬ(z)`, expanded at `λ = ∞`, is the coefficient of `z^n` of
`𝔼_{Q₀}[e^q R(x + λ(σ_*, σ̄_*))]` in `ℂ((t))[[z]]/(z^{n+1})`. -/
theorem EInf_gaussCoeff (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) (n : ℕ) :
    EInf (gaussCoeff (I0def sigmaStar (fun m => -sigmaStar m)) μ Δe n) =
      cfT n (fockP n n (phiL n PowerSeries.X)
        (mexp (quadB n (TR n LL)) *
          trans (fun a => psiL n tL⁻¹ * sgT n a)
            (mexp (psiL n tL⁻¹ • remU (psiL n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
              psiL n tL⁻¹ • remB (psiL n) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)))))) := by
  set I0 := I0def sigmaStar (fun m => -sigmaStar m) with hI0
  have h0 : PowerSeries.constantCoeff I0 = 0 := constantCoeff_I0def
  have hs : PowerSeries.HasSubst
      (PowerSeries.C (-(RatFunc.X : KK) ^ 2) * I0.map (algebraMap ℂ KK)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      rw [map_mul, constantCoeff_map_zero _ h0, mul_zero])
  have h2 : PowerSeries.map EInf ((PowerSeries.exp KK).subst
      (PowerSeries.C (-(RatFunc.X : KK) ^ 2) * I0.map (algebraMap ℂ KK))) =
      (PowerSeries.exp LL).subst (PowerSeries.C (-(tL⁻¹) ^ 2) * I0.map HahnSeries.C) := by
    refine (PowerSeries.map_subst hs (h := EInf) _).trans ?_
    rw [PowerSeries.map_exp]
    congr 1
    change PowerSeries.map EInf _ = _
    have e : PowerSeries.map EInf (PowerSeries.map (algebraMap ℂ KK) I0) =
        PowerSeries.map HahnSeries.C I0 := by
      refine PowerSeries.ext fun k => ?_
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
      show EInf (RatFunc.C _) = _
      exact EInf_C _
    rw [map_mul, PowerSeries.map_C, e, map_neg, map_pow, EInf_X]
  have hg0 : PowerSeries.constantCoeff
      (PowerSeries.C (-(tL⁻¹) ^ 2) * I0.map (HahnSeries.C : ℂ →+* LL)) = 0 := by
    rw [map_mul, constantCoeff_map_zero _ h0, mul_zero]
  have h3 : mkT n LL (PowerSeries.C (-(tL⁻¹) ^ 2) * I0.map (HahnSeries.C : ℂ →+* LL)) =
      -(psiL n tL⁻¹ ^ 2 * iotaZ n I0) := by
    rw [map_mul]
    simp only [map_neg, map_pow, neg_mul]
    rfl
  have h4 : mkT n LL (PowerSeries.map EInf (PowerSeries.mk (pairK μ Δe))) =
      IsNilpotent.exp (psiL n tL⁻¹ ^ 2 * iotaZ n I0) *
        fockP n n (phiL n PowerSeries.X)
          (mexp (quadB n (TR n LL)) *
            trans (fun a => psiL n tL⁻¹ * sgT n a)
              (mexp (psiL n tL⁻¹ • remU (psiL n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
                psiL n tL⁻¹ • remB (psiL n) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ))))) := by
    refine ext_cf fun j hj => ?_
    rw [cf_mkT hj, PowerSeries.coeff_map, PowerSeries.coeff_mk,
      EInf_pairK_eq_shift hF hK μ hμ Δe hj, JCJ_eq,
      show (fun a => ∑ b, covN n (phiL n) n a b * JL n (psiL n) b) =
        fun a => psiL n tL⁻¹ * sgT n a from funext fun a => CJ_eq n a]
  have hnil : IsNilpotent (psiL n tL⁻¹ ^ 2 * iotaZ n I0) := by
    obtain ⟨g', hg'⟩ := PowerSeries.X_dvd_iff.2 h0
    refine ⟨n + 1, ?_⟩
    rw [hg', map_mul, iotaZ_X, mul_pow, mul_pow, phiL_X_pow, zero_mul, mul_zero]
  rw [gaussCoeff, ← PowerSeries.coeff_map, map_mul, ← cf_mkT (N := n) le_rfl, map_mul, h2,
    mkT_exp_subst _ hg0, h3, h4, ← mul_assoc, IsNilpotent.exp_neg_mul_exp_self hnil, one_mul]

end StepTwo

end Virasoro.Sphere
