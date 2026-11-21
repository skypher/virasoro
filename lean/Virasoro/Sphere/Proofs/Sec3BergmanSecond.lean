import Virasoro.Sphere.Proofs.Sec3SaddleI0e

/-!
# Sphere paper Lemma 3.5: the second identity from the first (`sphere/paper.tex` l.829–831, l.969)

`₂F₁(1/2,1/2;1;z)^{-1/2} = θ₃(q(z))⁻¹` by the cited identity `₂F₁(z(q)) = θ₃(q)²`, so
`det(I - M(z)²)^{-1/2} = (1-z)^{-1/8} θ₃(q(z))⁻¹` follows from the first identity of the lemma.

Consumer: `Stmt_lem_bergman_det`.
-/

namespace Virasoro.Sphere

open PowerSeries

theorem constantCoeff_fpow {f : PowerSeries ℚ} (a : ℚ) : constantCoeff (fpow f a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact fpow_coeff_zero f a

/-- `(T²)^{-1/2} = T⁻¹` for a series `T` with constant term `1`. -/
theorem fpow_neg_half_sq {T : PowerSeries ℚ} (hT : constantCoeff T = 1) :
    fpow (T ^ 2) (-1 / 2 : ℚ) = T⁻¹ := by
  have hf : constantCoeff (T ^ 2) = 1 := by rw [map_pow, hT, one_pow]
  have h1 : fpow (T ^ 2) (-1 / 2 : ℚ) * fpow (T ^ 2) (-1 / 2 : ℚ) * T ^ 2 = 1 := by
    rw [← fpow_add hf]
    nth_rewrite 2 [← fpow_one hf]
    rw [← fpow_add hf, show (-1 / 2 + -1 / 2 + 1 : ℚ) = 0 by norm_num, fpow_zero hf]
  have h0 : (fpow (T ^ 2) (-1 / 2 : ℚ) * T - 1) * (fpow (T ^ 2) (-1 / 2 : ℚ) * T + 1) = 0 := by
    linear_combination h1
  have hT0 : constantCoeff T ≠ 0 := by rw [hT]; exact one_ne_zero
  refine (PowerSeries.eq_inv_iff_mul_eq_one hT0).2 ?_
  rcases mul_eq_zero.1 h0 with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, map_mul, constantCoeff_fpow, hT, map_one, map_zero] at this
    norm_num at this

/-- `₂F₁ = θ₃(q(z))²` over `ℚ`, for every `q(z)`. -/
theorem hyp2F1_eq_th3_rat (hJ2 : Cited_JacobiIdentities2) {Q : PowerSeries ℚ}
    (hQ0 : constantCoeff Q = 0) (hQ : (zq ℚ).subst Q = X) :
    hyp2F1 = ((th3 ℚ).subst Q) ^ 2 := by
  have hQs := HasSubst.of_constantCoeff_zero' hQ0
  have hzs : HasSubst (zq ℚ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
  have h := congrArg (PowerSeries.subst Q) hJ2.1
  rw [subst_comp_subst_apply hzs hQs, hQ, subst_X_self', subst_pow hQs] at h
  exact h

/-- Lemma 3.5 from its first identity and the cited identity `₂F₁(z(q)) = θ₃(q)²`. -/
theorem lem_bergman_det_of_first (hJ2 : Cited_JacobiIdentities2)
    (h1 : detInvSqrt = fpow (1 - PowerSeries.X) (-1 / 8 : ℚ) * fpow hyp2F1 (-1 / 2 : ℚ)) :
    Stmt_lem_bergman_det := by
  refine ⟨h1, fun Q hQ0 hQ => ?_⟩
  rw [h1, hyp2F1_eq_th3_rat hJ2 hQ0 hQ,
    fpow_neg_half_sq (constantCoeff_subst_of_one' hQ0 _ constantCoeff_th3)]

end Virasoro.Sphere
