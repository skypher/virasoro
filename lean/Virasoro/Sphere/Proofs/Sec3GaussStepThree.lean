import Virasoro.Sphere.Proofs.Sec3GaussLift

/-!
# Lemma 3.3(iii): reduction to the identification of the `t = 0` value

sphere/paper.tex l.684–708.  With the `λ⁻¹`-expansion of the shifted factor (`gauss_lift`) and
the Gaussian expectation of a linear exponential (`gauss_expect_of_lift`), the coefficient of
`z^n` of `e^{-λ²𝓘₀} ℬ(z)` is regular at `λ = ∞` with value the coefficient of `z^n` of
`det(I - M²)^{-1/2} exp(S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*) + ½ L·CL)`, `L` the gradient of
`S⁽¹⁾ + S̃⁽¹⁾` at the saddle point and `C` the Neumann covariance.  What is left
(`Stmt_sub_gauss_cov`, l.703–708) is to identify this value with the one in (3.5).
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

/-- Lemma 3.3(iii), last step (sphere/paper.tex l.703–708): in `ℂ[[z]]/(z^{n+1})`, the
coefficient of `z^n` of `e^{S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*)} e^{½ L·CL} det(I - M²)^{-1/2}`, with `L` the
gradient of `S⁽¹⁾(σ) + S̃⁽¹⁾(σ̄)` at the saddle point and `C` the Neumann covariance in `n` modes,
is the coefficient of `z^n` of
`det(I - M(z)²)^{-1/2} exp(μ²Φ_c^raw + (Δ₁+Δ₄-1/8)Φ₁ + (Δ₂+Δ₃-1/8)Φ₂)`:
half the covariance contraction of the gradient is `μ²Ψ₁`, and `ι`-evenness of `S⁽²⁾` identifies
`S̃⁽²⁾(σ̄_*)`. -/
def Stmt_sub_gauss_cov : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ μ : ℝ, 0 < μ → ∀ (Δe : Fin 4 → ℝ) (n : ℕ),
      cfT n (IsNilpotent.exp
            (constC (n := n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ))) *
          (IsNilpotent.exp ((1 / 2 : ℚ) • ∑ a, ∑ b,
              gradL (n := n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)) a *
                covN n (phiA n ℂ) n a b *
                gradL (n := n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ))
                  (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)) b) *
            phiA n ℂ detInvSqrt)) =
        PowerSeries.coeff n
          (detInvSqrt.map (algebraMap ℚ ℂ) *
            (PowerSeries.exp ℂ).subst
              ((μ : ℂ) ^ 2 • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
                ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S21 +
                ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S22))

section StepThree

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- Steps 3–4a of Lemma 3.3(iii) (sphere/paper.tex l.684–706): the Gaussian expectation of the
shifted factor has coefficients in `ℂ[[t]]`, with the value at `t = 0` given by the gradient of
`S⁽¹⁾` and the value of `S⁽²⁾` at the saddle point. -/
theorem gauss_expect_abstract (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) (n : ℕ) :
    ∃ w : PP,
      HahnSeries.ofPowerSeries ℤ ℂ w =
        cfT n (fockP n n (phiL n PowerSeries.X)
          (mexp (quadB n (TR n LL)) *
            trans (fun a => psiL n tL⁻¹ * sgT n a)
              (mexp (psiL n tL⁻¹ • remU (psiL n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
                psiL n tL⁻¹ • remB (psiL n) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)))))) ∧
      PowerSeries.constantCoeff w =
        cfT n (IsNilpotent.exp
            (constC (n := n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ))) *
          (IsNilpotent.exp ((1 / 2 : ℚ) • ∑ a, ∑ b,
              gradL (n := n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)) a *
                covN n (phiA n ℂ) n a b *
                gradL (n := n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ))
                  (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)) b) *
            phiA n ℂ detInvSqrt)) := by
  have hW := wardRat_isWard hF hK μ hμ (Δe 0 : ℂ) (Δe 1 : ℂ)
  have hW' := wardRat_isWard hF hK μ hμ (Δe 3 : ℂ) (Δe 2 : ℂ)
  obtain ⟨S1t, S2c, S21, S22, hE, hodd, -, -⟩ := sub_lam_orders hF hK
  have h1 := (hE μ hμ (Δe 0) (Δe 1) _ hW).1
  have h1' := (hE μ hμ (Δe 3) (Δe 2) _ hW').1
  have hodd' : iota (Sord (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)) 1) =
      -Sord (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) 1 := by
    rw [h1, h1', iota_smul, hodd, Complex.conj_ofReal, smul_neg]
  obtain ⟨EP, hnil, hlift, hred, hcn⟩ := gauss_lift (n := n) hW hW' hodd'
  have ha' : ∀ x, IsNilpotent (psiL n tL⁻¹ * sgT n x) := fun x => by
    obtain ⟨k, hk⟩ := sgT_nilpotent x
    exact ⟨k, by rw [mul_pow, hk, mul_zero]⟩
  have hE0 : IsNilpotent (constantCoeff
      (psiL n tL⁻¹ • remU (N := n) (psiL n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
        psiL n tL⁻¹ • remB (N := n) (psiL n) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)))) := by
    rw [map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, constantCoeff_remU _ hW,
      constantCoeff_remB _ hW']
    simp only [mul_zero, add_zero]
    exact IsNilpotent.zero
  have hT : trans (fun a => psiL n tL⁻¹ * sgT n a)
      (mexp (psiL n tL⁻¹ • remU (psiL n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
        psiL n tL⁻¹ • remB (psiL n) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)))) =
      map (rhoT n) (mexp EP) := by
    rw [map_mexp _ hnil, ← hlift]
    exact subst_mexp hE0 (hasSubst_trans ha')
  rw [hT]
  exact gauss_expect_of_lift n EP hnil _ _ hcn hred

include hF hK in
/-- Lemma 3.3(iii), the Gaussian evaluation in `λ⁻¹`, from its last step. -/
theorem sub_lam_gauss_of_cov (h : Stmt_sub_gauss_cov) : Stmt_sub_lam_gauss := by
  refine sub_lam_gauss_of_expect hF hK ?_
  intro S1t S2c S21 S22 hE μ hμ Δe n
  obtain ⟨w, hw, hw0⟩ := gauss_expect_abstract hF hK μ hμ Δe n
  exact ⟨w, hw, hw0.trans (h S1t S2c S21 S22 hE μ hμ Δe n)⟩

end StepThree

end Virasoro.Sphere
