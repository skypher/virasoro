import Virasoro.Sphere.Proofs.Sec3GaussSubs
import Virasoro.Sphere.Proofs.Sec3ExtLinear

/-!
# Sphere paper Lemma 3.3(iii): `Φ₁, Φ₂ ∈ zℚ[[z]]` (`sphere/paper.tex` l.541–545)

By Lemma 3.6 (which uses Lemma 3.3(i),(ii) and Lemma 3.4 only), `Φ₂ = -4 log θ₄(q(z))` and
`Φ₁ = -4 log θ₃(q(z))`, and `q(z)`, the compositional inverse of `z(q)`, has rational
coefficients.  The membership statement of Lemma 3.3(iii) is thereby reduced to
`Φ_c^raw ∈ zℚ[[z]]` (`Stmt_sub_lam_rational_c`).
-/

namespace Virasoro.Sphere

/-- Lemma 3.3(iii), `Φ_c^raw = 2S_c^{(2)}(σ_*) + Ψ₁ ∈ zℚ[[z]]` (sphere/paper.tex l.541–542,
l.705–708). -/
def Stmt_sub_lam_rational_c : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb → InZQ (PhiCraw S1t S2c σ σb)

/-- `-4 log θ(q(z))` lies in `zℚ[[z]]` for a rational series `θ` with constant term `1`. -/
theorem inZQ_log_subst (θ : PowerSeries ℚ) (hθ : PowerSeries.constantCoeff θ = 1) :
    InZQ ((-4 : ℂ) • (PowerSeries.log ℂ).subst
      ((θ.map (algebraMap ℚ ℂ)).subst (Q0.map (algebraMap ℚ ℂ)) - 1)) := by
  have hQs := PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_Q0
  have h1 : PowerSeries.constantCoeff (θ.subst Q0 - 1) = 0 := by
    rw [map_sub, constantCoeff_subst_of_one' constantCoeff_Q0 θ hθ, map_one, sub_self]
  have hs1 := PowerSeries.HasSubst.of_constantCoeff_zero' h1
  refine ⟨(-4 : ℚ) • (PowerSeries.log ℚ).subst (θ.subst Q0 - 1), ?_, ?_⟩
  · have h2 : PowerSeries.constantCoeff ((PowerSeries.log ℚ).subst (θ.subst Q0 - 1)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero h1 _ PowerSeries.constantCoeff_log
    rw [PowerSeries.smul_eq_C_mul, map_mul, h2, mul_zero]
  · have e1 : ((PowerSeries.log ℚ).subst (θ.subst Q0 - 1)).map (algebraMap ℚ ℂ) =
        (PowerSeries.log ℂ).subst
          ((θ.map (algebraMap ℚ ℂ)).subst (Q0.map (algebraMap ℚ ℂ)) - 1) := by
      refine (PowerSeries.map_subst hs1 (h := algebraMap ℚ ℂ) _).trans ?_
      rw [PowerSeries.map_log]
      congr 1
      change PowerSeries.map (algebraMap ℚ ℂ) (θ.subst Q0 - 1) = _
      rw [map_sub, map_one]
      congr 1
      exact PowerSeries.map_subst hQs (h := algebraMap ℚ ℂ) θ
    have e3 : PowerSeries.C ((algebraMap ℚ ℂ) (-4)) = PowerSeries.C (-4 : ℂ) := by simp
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, e3]
    exact congrArg (fun x => PowerSeries.C (-4 : ℂ) * x) e1.symm

/-- The membership statement of Lemma 3.3(iii) from Lemma 3.6 and `Φ_c^raw ∈ zℚ[[z]]`. -/
theorem sub_lam_rational_of_c (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hc : Stmt_sub_lam_rational_c) : Stmt_sub_lam_rational := by
  intro S1t S2c S21 S22 hE σ σb hs
  obtain ⟨-, -, h⟩ := lem_ext_exponents_of_cited hF hK hJ1 hJ2 S1t S2c S21 S22 hE
  have hQ0 : PowerSeries.constantCoeff (Q0.map (algebraMap ℚ ℂ)) = 0 :=
    constantCoeff_map_zero _ constantCoeff_Q0
  have hQ : (zq ℂ).subst (Q0.map (algebraMap ℚ ℂ)) = PowerSeries.X := by
    have h1 := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) zq_subst_Q0
    rw [PowerSeries.map_X] at h1
    rw [← h1, ← map_zq (algebraMap ℚ ℂ)]
    exact (PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_Q0)
      (h := algebraMap ℚ ℂ) _).symm
  obtain ⟨h22, h21⟩ := h σ σb hs _ hQ0 hQ
  refine ⟨hc S1t S2c S21 S22 hE σ σb hs, ?_, ?_⟩
  · rw [h21, ← map_th3 (algebraMap ℚ ℂ)]
    exact inZQ_log_subst (th3 ℚ) constantCoeff_th3
  · rw [h22, ← map_th4 (algebraMap ℚ ℂ)]
    exact inZQ_log_subst (th4 ℚ) constantCoeff_th4

/-- Lemma 3.3 from the two remaining statements of part (iii): `Φ_c^raw ∈ zℚ[[z]]` and the
Gaussian evaluation in `λ⁻¹`. -/
theorem lem_lambda_expansion_of_gauss (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hc : Stmt_sub_lam_rational_c) (hg : Stmt_sub_lam_gauss) : Stmt_lem_lambda_expansion :=
  lem_lambda_expansion_of_limit hF hK hJ2
    (sub_lam_limit_of_gauss hF hK hJ2 (sub_lam_rational_of_c hF hK hJ1 hJ2 hc) hg)

end Virasoro.Sphere
