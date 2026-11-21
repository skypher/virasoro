import Virasoro.Sphere.Proofs.Sec3BergmanTrace

/-!
# Sphere paper Lemma 3.5: integration from `z = 0` (`sphere/paper.tex` l.943–969)

The first identity of Lemma 3.5 follows from the trace formula
`Tr(D M² (I - M²)⁻¹) = z/(8(1-z)) - ½ z F₀'(z)/F₀(z)` (frozen below as
`Stmt_sub_bergman_trace`): both `det(I - M(z)²)^{-1/2}` and `(1-z)^{-1/8} F₀^{-1/2}` solve
`θ y = y · T` with `y(0) = 1`, `θ = z d/dz`.

Consumer: `Stmt_lem_bergman_det`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- Sub-statement of Lemma 3.5 (sphere/paper.tex l.867–966, Steps 1–3 and the residue
evaluation): in `ℚ[[z]]`,
`Tr(B K₁₂ M₁) = Tr(D M(z)² (I - M(z)²)⁻¹) = z/(8(1-z)) - ½ z F₀'(z)/F₀(z)`,
with `F₀ = ₂F₁(½,½;1;z)`. -/
def Stmt_sub_bergman_trace : Prop :=
  traceDM = X * (C (8 : ℚ) * (1 - X))⁻¹ -
    C (1 / 2 : ℚ) * (X * derivative ℚ hyp2F1 * hyp2F1⁻¹)

theorem gbinom_succ_mul2 (a : ℚ) (k : ℕ) :
    gbinom a (k + 1) * ((k : ℚ) + 1) = (a - k) * gbinom a k := by
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [gbinom_succ_mul]
  field_simp

/-- `(1+x) d/dx (1+x)^a = a (1+x)^a`. -/
theorem one_add_X_mul_deriv_binom (a : ℚ) :
    (1 + X) * derivative ℚ (binomialSeries ℚ a) = a • binomialSeries ℚ a := by
  rw [← mk_gbinom]
  ext n
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_smul, coeff_mk, coeff_mk, smul_eq_mul]
  cases n with
  | zero =>
    have := gbinom_succ_mul2 a 0
    simp only [Nat.cast_zero, zero_add, sub_zero] at this
    simp [this]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mk]
    have h1 := gbinom_succ_mul2 a (n + 1)
    push_cast at h1 ⊢
    linear_combination h1

/-- `f · θ(f^a) = a f^a · θ f`. -/
theorem mul_theta_fpow {f : PowerSeries ℚ} (hf : constantCoeff f = 1) (a : ℚ) :
    f * theta (fpow f a) = C a * fpow f a * theta f := by
  have hu : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hs := HasSubst.of_constantCoeff_zero' hu
  have h1 : f * (derivative ℚ (binomialSeries ℚ a)).subst (f - 1) = C a * fpow f a := by
    have e := congrArg (PowerSeries.subst (f - 1)) (one_add_X_mul_deriv_binom a)
    rw [subst_mul hs, subst_add hs, subst_X hs, subst_one'' hs, subst_smul hs,
      ← fpow_eq_subst hf, smul_eq_C_mul] at e
    rw [← e]
    ring
  rw [theta_apply, theta_apply, fpow_eq_subst hf, derivative_subst hs, map_sub,
    Derivation.map_one_eq_zero, sub_zero, ← fpow_eq_subst hf]
  linear_combination (X * derivative ℚ f) * h1

theorem constantCoeff_one_sub_X : constantCoeff (1 - X : PowerSeries ℚ) = 1 := by
  rw [map_sub, map_one, constantCoeff_X, sub_zero]

/-- The logarithmic derivative of `(1-z)^{-1/8} F₀(z)^{-1/2}` (sphere/paper.tex l.965–969). -/
theorem theta_rhs :
    theta (fpow (1 - X) (-1 / 8 : ℚ) * fpow hyp2F1 (-1 / 2 : ℚ)) =
      fpow (1 - X) (-1 / 8 : ℚ) * fpow hyp2F1 (-1 / 2 : ℚ) *
        (X * (C (8 : ℚ) * (1 - X))⁻¹ - C (1 / 2 : ℚ) * (X * derivative ℚ hyp2F1 * hyp2F1⁻¹)) := by
  have hP := mul_theta_fpow constantCoeff_one_sub_X (-1 / 8 : ℚ)
  have hQ := mul_theta_fpow constantCoeff_hyp2F1 (-1 / 2 : ℚ)
  have hth : theta (1 - X : PowerSeries ℚ) = -X := by
    rw [theta_apply, map_sub, Derivation.map_one_eq_zero, derivative_X]
    ring
  rw [hth] at hP
  rw [theta_apply hyp2F1] at hQ
  have i1 : C (8 : ℚ) * (1 - X) * (C (8 : ℚ) * (1 - X))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by
      rw [map_mul, constantCoeff_C, constantCoeff_one_sub_X]; norm_num)
  have i2 : hyp2F1 * hyp2F1⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hyp2F1_unit
  have hc1 : (C (-1 / 8 : ℚ) : PowerSeries ℚ) = -C (1 / 8 : ℚ) := by rw [← map_neg]; norm_num
  have hc2 : (C (-1 / 2 : ℚ) : PowerSeries ℚ) = -C (1 / 2 : ℚ) := by rw [← map_neg]; norm_num
  have h8 : (C (1 / 8 : ℚ) : PowerSeries ℚ) * C (8 : ℚ) = 1 := by
    rw [← map_mul]; norm_num
  rw [hc1] at hP
  rw [hc2] at hQ
  have hne : (1 - X) * hyp2F1 ≠ (0 : PowerSeries ℚ) := by
    intro h
    have := congrArg constantCoeff h
    rw [map_mul, constantCoeff_one_sub_X, constantCoeff_hyp2F1] at this
    norm_num at this
  refine mul_left_cancel₀ hne ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  set P := fpow (1 - X) (-1 / 8 : ℚ)
  set Q := fpow hyp2F1 (-1 / 2 : ℚ)
  set F := hyp2F1
  set J := (C (8 : ℚ) * (1 - X))⁻¹
  set dF := derivative ℚ F
  linear_combination (1 - X) * P * hQ + F * Q * hP +
    C (1 / 2 : ℚ) * (1 - X) * P * Q * X * dF * i2 -
    F * Q * P * X * C (1 / 8 : ℚ) * i1 + F * Q * P * X * (1 - X) * J * h8

/-- A solution of `θ W = W · T` with `W(0) = 0` and `T(0) = 0` vanishes. -/
theorem eq_zero_of_theta {W T : PowerSeries ℚ} (h0 : coeff 0 W = 0) (hT : coeff 0 T = 0)
    (h : theta W = W * T) : W = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h0
    have hc := congrArg (coeff n) h
    rw [coeff_theta, coeff_mul] at hc
    have hz : ∑ p ∈ antidiagonal n, coeff p.1 W * coeff p.2 T = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rcases Nat.eq_zero_or_pos p.2 with h2 | h2
      · rw [h2, hT, mul_zero]
      · have := ih p.1 (by omega)
        rw [map_zero] at this
        rw [this, zero_mul]
    rw [hz] at hc
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simpa [hn'] using hc

/-- The first identity of Lemma 3.5 from the trace formula: integration from `z = 0`
(sphere/paper.tex l.943–945, l.969). -/
theorem bergman_first_of_trace (hT : Stmt_sub_bergman_trace) :
    detInvSqrt = fpow (1 - X) (-1 / 8 : ℚ) * fpow hyp2F1 (-1 / 2 : ℚ) := by
  refine sub_eq_zero.1 (eq_zero_of_theta (T := traceDM) ?_ coeff_zero_traceDM ?_)
  · rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_detInvSqrt, map_mul, constantCoeff_fpow, constantCoeff_fpow]
    norm_num
  · have hT' : traceDM = _ := hT
    rw [map_sub, theta_detInvSqrt, theta_rhs, ← hT']
    ring

/-- Lemma 3.5 from the trace formula and the cited identity `₂F₁(z(q)) = θ₃(q)²`. -/
theorem lem_bergman_det_of_trace (hJ2 : Cited_JacobiIdentities2) (hT : Stmt_sub_bergman_trace) :
    Stmt_lem_bergman_det :=
  lem_bergman_det_of_first hJ2 (bergman_first_of_trace hT)

end Virasoro.Sphere
