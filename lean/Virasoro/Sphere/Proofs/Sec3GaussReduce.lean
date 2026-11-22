import Virasoro.Sphere.Proofs.Sec3GaussStepTwo

/-!
# Lemma 3.3(iii): reduction of the Gaussian evaluation to the expectation at the saddle point

sphere/paper.tex l.637–711.  The first half of the proof (l.637–684: the pairing as an algebraic
Gaussian expectation, the perturbed Hessian, completing the square at the saddle point, the
saddle value `e^{λ²𝓘₀}`) is `EInf_gaussCoeff`.  What is left (l.684–708) is the `λ⁻¹`-expansion
of the shifted integrand and its Gaussian expectation, `Stmt_sub_gauss_expect`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

/-- Lemma 3.3(iii), second half (sphere/paper.tex l.684–708).  In `ℂ((t))[[z]]/(z^{n+1})`,
`t = 1/λ`, the coefficient of `z^n` of the centered Gaussian expectation
`𝔼_{Q₀}[e^q R(x + λ(σ_*, σ̄_*))]` of the shifted factor `R` is a power series `w` in `t` (the
orders `λ¹` cancel by `ι`-oddness of `S̃⁽¹⁾`), and its value at `t = 0` is the coefficient of
`z^n` of `det(I - M(z)²)^{-1/2} exp(μ²Φ_c^raw + (Δ₁+Δ₄-1/8)Φ₁ + (Δ₂+Δ₃-1/8)Φ₂)`. -/
def Stmt_sub_gauss_expect : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ μ : ℝ, 0 < μ → ∀ (Δe : Fin 4 → ℝ) (n : ℕ),
      ∃ w : PowerSeries ℂ,
        HahnSeries.ofPowerSeries ℤ ℂ w =
          cfT n (fockP n n (phiL n PowerSeries.X)
            (mexp (quadB n (TR n LL)) *
              trans (fun a => psiL n tL⁻¹ * sgT n a)
                (mexp (psiL n tL⁻¹ • remU (psiL n) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
                  psiL n tL⁻¹ • remB (psiL n) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)))))) ∧
        PowerSeries.constantCoeff w =
          PowerSeries.coeff n
            (detInvSqrt.map (algebraMap ℚ ℂ) *
              (PowerSeries.exp ℂ).subst
                ((μ : ℂ) ^ 2 • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
                  ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S21 +
                  ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S22))

/-- Lemma 3.3(iii), the Gaussian evaluation in `λ⁻¹`, from its second half. -/
theorem sub_lam_gauss_of_expect (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (h : Stmt_sub_gauss_expect) : Stmt_sub_lam_gauss := by
  intro S1t S2c S21 S22 hE σ σb hs μ hμ Δe n
  obtain ⟨rfl, rfl⟩ := hs.eq_sigmaStar
  obtain ⟨w, hw, hw0⟩ := h S1t S2c S21 S22 hE μ hμ Δe n
  have he := EInf_gaussCoeff hF hK μ hμ Δe n
  rw [← hw] at he
  refine ⟨(regularAtInfty_iff _).2 ?_, ?_⟩
  · rw [he, ordGE_iff]
    intro m hm
    have := PowerSeries.coeff_coe (R := ℂ) w m
    rw [if_pos hm] at this
    exact this
  · rw [inftyCoeff_eq, he, ← hw0]
    have := PowerSeries.coeff_coe (R := ℂ) w 0
    rw [if_neg (lt_irrefl 0)] at this
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact this

end Virasoro.Sphere
