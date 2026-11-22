import Virasoro.Sphere.Proofs.Sec3CentralFinal

/-!
# `f^a = exp(a log f)` over `ℂ` (sphere paper, proof of Theorem 3.1)

sphere/paper.tex l.1183–1203 combines the exponentials of Lemmas 3.3–3.7 with the powers in
`Φ̃` of Definition 2.2.  The power `fpow f a = ∑_k binom(a,k)(f-1)^k` of a series with constant
term `1` is `exp(a log f)`: both have the logarithmic derivative `a f'/f` and constant term `1`.
-/

namespace Virasoro.Sphere

open PowerSeries

theorem gbinom_succ_mul2C (a : ℂ) (k : ℕ) :
    gbinom a (k + 1) * ((k : ℂ) + 1) = (a - k) * gbinom a k := by
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [gbinom_succ_mul]
  field_simp

/-- `(1+x) d/dx (1+x)^a = a (1+x)^a`. -/
theorem one_add_X_mul_deriv_binomC (a : ℂ) :
    (1 + X) * derivative ℂ (binomialSeries ℂ a) = a • binomialSeries ℂ a := by
  rw [← mk_gbinom]
  ext n
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_smul, coeff_mk, coeff_mk, smul_eq_mul]
  cases n with
  | zero =>
    have := gbinom_succ_mul2C a 0
    simp only [Nat.cast_zero, zero_add, sub_zero] at this
    simp [this]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mk]
    have h1 := gbinom_succ_mul2C a (n + 1)
    push_cast at h1 ⊢
    linear_combination h1

/-- `f (f^a)' = a f^a f'`. -/
theorem deriv_fpow_mul {f : PowerSeries ℂ} (hf : constantCoeff f = 1) (a : ℂ) :
    f * derivative ℂ (fpow f a) = C a * fpow f a * derivative ℂ f := by
  have hu : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hs := HasSubst.of_constantCoeff_zero' hu
  have h1 : f * (derivative ℂ (binomialSeries ℂ a)).subst (f - 1) = C a * fpow f a := by
    have e := congrArg (PowerSeries.subst (f - 1)) (one_add_X_mul_deriv_binomC a)
    rw [subst_mul hs, subst_add hs, subst_X hs, subst_one' hs, subst_smul hs,
      ← fpow_eq_subst hf, smul_eq_C_mul] at e
    rw [← e]
    ring
  rw [fpow_eq_subst hf, derivative_subst hs, map_sub, Derivation.map_one_eq_zero, sub_zero,
    ← fpow_eq_subst hf]
  linear_combination (derivative ℂ f) * h1

theorem constantCoeff_fpowC (f : PowerSeries ℂ) (a : ℂ) : constantCoeff (fpow f a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact fpow_coeff_zero f a

/-- `exp(a log f) = f^a` for a series `f` with constant term `1`. -/
theorem exp_smul_log (f : PowerSeries ℂ) (hf : constantCoeff f = 1) (a : ℂ) :
    (exp ℂ).subst (a • (log ℂ).subst (f - 1)) = fpow f a := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' h1
  have hL : constantCoeff ((log ℂ).subst (f - 1)) = 0 :=
    constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  have haL : constantCoeff (a • (log ℂ).subst (f - 1)) = 0 := by
    rw [smul_eq_C_mul, map_mul, hL, mul_zero]
  refine eq_of_deriv_mul_eq (constantCoeff_exp_subst _ haL) (constantCoeff_fpowC f a) ?_
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, map_zero] at hf
    exact zero_ne_one hf
  refine mul_left_cancel₀ hf0 ?_
  have e := deriv_log_subst_mul (τ := Unit) (f - 1) h1
  rw [add_sub_cancel] at e
  have hdw := deriv_fpow_mul hf a
  rw [deriv_exp_subst _ haL, Derivation.map_smul, derivative_subst hs1, map_sub,
    Derivation.map_one_eq_zero, sub_zero]
  simp only [smul_eq_C_mul]
  linear_combination (C a * (exp ℂ).subst (C a * (log ℂ).subst (f - 1)) * fpow f a *
    derivative ℂ f) * e - (exp ℂ).subst (C a * (log ℂ).subst (f - 1)) * hdw

/-- Substitution into `exp(a log f)`. -/
theorem subst_exp_smul_log (f g : PowerSeries ℂ) (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 0) (a : ℂ) :
    PowerSeries.subst g ((exp ℂ).subst (a • (log ℂ).subst (f - 1))) =
      (exp ℂ).subst (a • (log ℂ).subst (f.subst g - 1)) := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' h1
  have hg' := HasSubst.of_constantCoeff_zero' hg
  have hL : constantCoeff ((log ℂ).subst (f - 1)) = 0 :=
    constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  have haL : constantCoeff (a • (log ℂ).subst (f - 1)) = 0 := by
    rw [smul_eq_C_mul, map_mul, hL, mul_zero]
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' haL) hg', subst_smul hg',
    subst_comp_subst_apply hs1 hg', subst_sub hg', subst_one' hg']

end Virasoro.Sphere
