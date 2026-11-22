import Virasoro.Sphere.Proofs.Sec3GaussCovFinal
import Virasoro.Sphere.Proofs.Sec3GaussRational

/-!
# Lemma 3.3(iii): `Φ_c^raw ∈ zℚ[[z]]` from Lemma 3.7 (sphere paper)

sphere/paper.tex l.541–542.  By Lemma 3.7, `exp(Φ_c^raw - 𝓘₀) = ∏(1 - q(z)^{2m})^{12}` is a series
with rational coefficients, so `Φ_c^raw - 𝓘₀` is its logarithm and lies in `zℚ[[z]]`; and
`𝓘₀ ∈ zℚ[[z]]` (Lemma 3.4(iii)).  With the Gaussian evaluation `sub_lam_gauss`, this gives
Lemma 3.3 from Lemma 3.7.
-/

namespace Virasoro.Sphere

open PowerSeries

theorem constantCoeff_exp_subst (g : PowerSeries ℂ) (hg : constantCoeff g = 0) :
    constantCoeff ((exp ℂ).subst g) = 1 :=
  constantCoeff_subst_of_one' hg _ constantCoeff_exp

theorem deriv_exp_subst (g : PowerSeries ℂ) (hg : constantCoeff g = 0) :
    derivative ℂ ((exp ℂ).subst g) = (exp ℂ).subst g * derivative ℂ g := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hg), derivative_exp]

/-- `log(exp g) = g` for a series `g` without constant term. -/
theorem log_exp_subst (g : PowerSeries ℂ) (hg : constantCoeff g = 0) :
    (log ℂ).subst ((exp ℂ).subst g - 1) = g := by
  have hE := constantCoeff_exp_subst g hg
  have h1 : constantCoeff ((exp ℂ).subst g - 1) = 0 := by rw [map_sub, hE, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' h1
  apply derivative.ext
  · rw [derivative_subst hs1, map_sub, Derivation.map_one_eq_zero, sub_zero, deriv_exp_subst g hg]
    have e := deriv_log_subst_mul (τ := Unit) ((exp ℂ).subst g - 1) h1
    rw [add_sub_cancel] at e
    linear_combination derivative ℂ g * e
  · rw [hg]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log

/-- `log θ(q(z))` lies in `zℚ[[z]]` for a rational series `θ` with constant term `1`. -/
theorem inZQ_log_subst_one (θ : PowerSeries ℚ) (hθ : constantCoeff θ = 1) :
    InZQ ((log ℂ).subst ((θ.map (algebraMap ℚ ℂ)).subst (Q0.map (algebraMap ℚ ℂ)) - 1)) := by
  have hQs := HasSubst.of_constantCoeff_zero' constantCoeff_Q0
  have h1 : constantCoeff (θ.subst Q0 - 1) = 0 := by
    rw [map_sub, constantCoeff_subst_of_one' constantCoeff_Q0 θ hθ, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' h1
  refine ⟨(log ℚ).subst (θ.subst Q0 - 1), constantCoeff_subst_eq_zero h1 _ constantCoeff_log, ?_⟩
  symm
  refine (PowerSeries.map_subst hs1 (h := algebraMap ℚ ℂ) _).trans ?_
  rw [map_log]
  congr 1
  change PowerSeries.map (algebraMap ℚ ℂ) (θ.subst Q0 - 1) = _
  rw [map_sub, map_one]
  congr 1
  exact PowerSeries.map_subst hQs (h := algebraMap ℚ ℂ) θ

theorem constantCoeff_etaSqPow (e : ℕ) : constantCoeff (etaSqPow e) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, etaSqPow, coeff_mk]
  simp

section

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
theorem coeff_zero_S2c_of_data {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) : MvPowerSeries.coeff 0 S2c = 0 := by
  have hW := wardRat_isWard hF hK 1 one_pos (((1 / 16 : ℝ)) : ℂ) (((1 / 16 : ℝ)) : ℂ)
  have h2 := (hE 1 one_pos (1 / 16) (1 / 16) _ hW).2
  have e16 : (((1 / 16 : ℝ)) : ℂ) - 1 / 16 = 0 := by
    push_cast
    ring
  have h3 := congrArg (MvPowerSeries.coeff 0) h2
  rw [coeff_zero_Sord hW 2, e16, zero_smul, zero_smul, add_zero, add_zero] at h3
  simpa using h3.symm

include hF hK in
/-- `Φ_c^raw ∈ zℚ[[z]]` from Lemma 3.7. -/
theorem sub_lam_rational_c_of_central (hJ2 : Cited_JacobiIdentities2)
    (h37 : Stmt_lem_central_charge) : Stmt_sub_lam_rational_c := by
  intro S1t S2c S21 S22 hE σ σb hs
  have hQ0 : constantCoeff (Q0.map (algebraMap ℚ ℂ)) = 0 :=
    constantCoeff_map_zero _ constantCoeff_Q0
  have hQ : (zq ℂ).subst (Q0.map (algebraMap ℚ ℂ)) = PowerSeries.X := by
    have h1 := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) zq_subst_Q0
    rw [PowerSeries.map_X] at h1
    rw [← h1, ← map_zq (algebraMap ℚ ℂ)]
    exact (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' constantCoeff_Q0)
      (h := algebraMap ℚ ℂ) _).symm
  obtain ⟨h1, -⟩ := h37 S1t S2c S21 S22 hE σ σb hs _ hQ0 hQ
  obtain ⟨e1, e2⟩ := hs.eq_sigmaStar
  subst e1 e2
  obtain ⟨g2, hg2, eg2⟩ := inZQ_I0 hJ2
  have hc0 : constantCoeff (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m)) = 0 := by
    have ha : MvPowerSeries.constantCoeff (MvPowerSeries.subst sigmaStar S2c) = 0 :=
      MvPowerSeries.constantCoeff_subst_eq_zero hs.hasSubst
        (fun m => constantCoeff_sigmaStar m) (coeff_zero_S2c_of_data hF hK hE)
    rw [PhiCraw, map_add, map_mul, constantCoeff_Psi1, add_zero]
    exact mul_eq_zero_of_right _ ha
  have hd0 : constantCoeff (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
      I0def sigmaStar (fun m => -sigmaStar m)) = 0 := by
    rw [map_sub, hc0, eg2, constantCoeff_map_zero _ hg2, sub_zero]
  have h2 := log_exp_subst _ hd0
  rw [h1] at h2
  obtain ⟨g1, hg1, eg1⟩ := inZQ_log_subst_one (etaSqPow 12) (constantCoeff_etaSqPow 12)
  rw [h2] at eg1
  refine ⟨g1 + g2, by rw [map_add, hg1, hg2, add_zero], ?_⟩
  rw [map_add, ← eg1, ← eg2, sub_add_cancel]

include hF hK in
/-- Lemma 3.3 from Lemma 3.7. -/
theorem lem_lambda_expansion_of_central (hJ1 : Cited_JacobiIdentities)
    (hJ2 : Cited_JacobiIdentities2) (h37 : Stmt_lem_central_charge) :
    Stmt_lem_lambda_expansion :=
  lem_lambda_expansion_of_gauss hF hK hJ1 hJ2 (sub_lam_rational_c_of_central hF hK hJ2 h37)
    (sub_lam_gauss hF hK)

include hF hK in
/-- The limit (3.5) of Lemma 3.3(iii), from the Gaussian evaluation alone. -/
theorem lam_limit (hJ2 : Cited_JacobiIdentities2) {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) (n : ℕ) :
    Filter.Tendsto
      (fun lam : ℝ => PowerSeries.coeff n
        ((PowerSeries.exp ℂ).subst
            (PowerSeries.C (-(lam : ℂ) ^ 2) * I0def sigmaStar (fun m => -sigmaStar m)) *
          PowerSeries.mk fun j =>
            RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
              (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) j)))
      Filter.atTop
      (nhds (PowerSeries.coeff n
        (detInvSqrt.map (algebraMap ℚ ℂ) *
          (PowerSeries.exp ℂ).subst
            ((μ : ℂ) ^ 2 • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
              ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S21 +
              ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S22)))) := by
  obtain ⟨hreg, hval⟩ := sub_lam_gauss hF hK S1t S2c S21 S22 hE _ _ isSaddle_sigmaStar μ hμ Δe n
  have h0 : constantCoeff (I0def sigmaStar (fun m => -sigmaStar m)) = 0 := by
    obtain ⟨g, hg, hg'⟩ := inZQ_I0 hJ2
    rw [hg']
    exact constantCoeff_map_zero _ hg
  have ht := tendsto_evalAt_of_regularAtInfty _ hreg
  rw [hval] at ht
  refine ht.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with lam hlam
  exact gaussCoeff_eval hF hK _ h0 μ hμ Δe lam hlam n

end

end Virasoro.Sphere
