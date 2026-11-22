import Virasoro.Sphere.Proofs.Sec3ExtExp
import Virasoro.Sphere.Proofs.Sec3SaddleI0e
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Sphere paper Lemma 3.6: the values at the saddle point (l.1008–1009)

`Φ₂ = S_2^{(2)}(σ_*) = 2 log(1 - g_*(1)) = -4 log θ₄(q(z))` and
`Φ₁ = 2 log(1 - g_*(-1)) = -4 log θ₃(q(z))`, from the saddle values of Lemma 3.4(iii),
`1 - g_*(1) = θ₄⁻²`, `1 - g_*(-1) = θ₃⁻²`.
-/

namespace Virasoro.Sphere

open PowerSeries

/-- `log(θ⁻²) = -2 log θ` for a series `θ` with constant term `1`: both sides have the same
derivative and zero constant term. -/
theorem log_inv_sq (θ : PowerSeries ℂ) (hθ : constantCoeff θ = 1) :
    (log ℂ).subst ((θ ^ 2)⁻¹ - 1) = (-2 : ℂ) • (log ℂ).subst (θ - 1) := by
  set v := (θ ^ 2)⁻¹ with hv
  have hc2 : constantCoeff (θ ^ 2) ≠ 0 := by
    rw [map_pow, hθ]
    norm_num
  have hvθ : v * θ * θ = 1 := by
    rw [mul_assoc, ← pow_two]
    exact PowerSeries.inv_mul_cancel _ hc2
  have hcv : constantCoeff v = 1 := by
    rw [hv, constantCoeff_inv, map_pow, hθ]
    norm_num
  have hg1 : constantCoeff (v - 1) = 0 := by rw [map_sub, hcv, map_one, sub_self]
  have hg2 : constantCoeff (θ - 1) = 0 := by rw [map_sub, hθ, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' hg1
  have hs2 := HasSubst.of_constantCoeff_zero' hg2
  apply derivative.ext
  · rw [derivative_subst hs1, Derivation.map_smul, derivative_subst hs2]
    have e1 : (derivative ℂ (log ℂ)).subst (v - 1) * v = 1 := by
      have := deriv_log_subst_mul (τ := Unit) (v - 1) hg1
      rwa [add_sub_cancel] at this
    have e2 : (derivative ℂ (log ℂ)).subst (θ - 1) * θ = 1 := by
      have := deriv_log_subst_mul (τ := Unit) (θ - 1) hg2
      rwa [add_sub_cancel] at this
    have dv : derivative ℂ (v - 1) = derivative ℂ v := by
      rw [map_sub, Derivation.map_one_eq_zero, sub_zero]
    have dθ : derivative ℂ (θ - 1) = derivative ℂ θ := by
      rw [map_sub, Derivation.map_one_eq_zero, sub_zero]
    have hprod := congrArg (derivative ℂ) hvθ
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at hprod
    rw [dv, dθ, PowerSeries.smul_eq_C_mul, map_neg, map_ofNat]
    linear_combination (-((derivative ℂ (log ℂ)).subst (v - 1) * derivative ℂ v +
      2 * ((derivative ℂ (log ℂ)).subst (θ - 1) * derivative ℂ θ))) * hvθ + hprod +
      (derivative ℂ v * θ ^ 2) * e1 + (2 * derivative ℂ θ * v * θ) * e2
  · have h1 : constantCoeff ((log ℂ).subst (v - 1)) = 0 :=
      constantCoeff_subst_eq_zero hg1 _ constantCoeff_log
    have h2 : constantCoeff ((log ℂ).subst (θ - 1)) = 0 :=
      constantCoeff_subst_eq_zero hg2 _ constantCoeff_log
    rw [h1, PowerSeries.smul_eq_C_mul, map_mul, h2, mul_zero]

theorem subst_two_log (s : ℂ) (θ : PowerSeries ℂ) (hθ : constantCoeff θ = 1)
    (hval : 1 - MvPowerSeries.subst sigmaStar (gAt s) = (θ ^ 2)⁻¹) :
    MvPowerSeries.subst sigmaStar ((2 : ℂ) • (log ℂ).subst (-gAt s)) =
      (-4 : ℂ) • (log ℂ).subst (θ - 1) := by
  have ha := isSaddle_sigmaStar.hasSubst
  have hc : MvPowerSeries.subst sigmaStar ((log ℂ).subst (-gAt s)) =
      (log ℂ).subst (MvPowerSeries.subst sigmaStar (-gAt s)) :=
    MvPowerSeries.subst_comp_subst_apply
      (HasSubst.const (HasSubst.of_constantCoeff_zero (constantCoeff_neg_gAt s))) ha _
  have hn : MvPowerSeries.subst sigmaStar (-gAt s) = (θ ^ 2)⁻¹ - 1 := by
    rw [← hval, ← MvPowerSeries.coe_substAlgHom ha, map_neg]
    ring
  rw [← MvPowerSeries.coe_substAlgHom ha, map_smul, MvPowerSeries.coe_substAlgHom ha, hc, hn,
    log_inv_sq θ hθ, smul_smul]
  norm_num

/-- Lemma 3.6 from the linear equations `L_k^{(0)}g(1) = -(k/2)(1 - g(1))`,
`L_k^{(0)}g(-1) = ½(1 - g(-1))` (l.981–1006), with Lemma 3.3(i),(ii) and Lemma 3.4(iii). -/
theorem lem_ext_exponents_of_linear (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hlin : Stmt_sub_ext_linear) : Stmt_lem_ext_exponents := by
  intro S1t S2c S21 S22 hE
  obtain ⟨h22, h21⟩ := ext_exponents_series hF hK hlin hE
  refine ⟨h22, h21, fun σ σb hs Q hQ0 hQ => ?_⟩
  obtain ⟨rfl, rfl⟩ := hs.eq_sigmaStar
  rw [h22, h21]
  exact ⟨subst_two_log 1 _ (constantCoeff_subst_of_one' hQ0 _ constantCoeff_th4)
      (gStar_one hJ1 hJ2 hQ0 hQ),
    subst_two_log (-1) _ (constantCoeff_subst_of_one' hQ0 _ constantCoeff_th3)
      (gStar_neg_one hJ2 hQ0 hQ)⟩

example (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hlin : Stmt_sub_ext_linear) : Stmt_lem_ext_exponents :=
  lem_ext_exponents_of_linear hF hK hJ1 hJ2 hlin

end Virasoro.Sphere
