import Virasoro.Sphere.Proofs.Sec3BergmanZeroMode
import Virasoro.Sphere.Proofs.Sec3BergmanTraceApm

/-!
# Sphere paper Lemma 3.5, Step 3: the contour integral of `(x/2) W_no(x,x)` (`sphere/paper.tex` l.941–945)

On `0 < |x| < 1` only the diagonal entries of `A₋₊` and `A₊₋` contribute to the coefficient of
`x⁻²` of `[z^j] W_no(x,x)`, so
`∮_{|x|=r} (x/2) W_no(x,x) dx/(2πi) = Tr(B K₁₂ M₁) = Tr(D M(z)² (I - M(z)²)⁻¹)`
coefficientwise in `z`; here without the factor `½`.

Consumer: `Stmt_sub_bergman_residue`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset MeasureTheory Real

theorem circleIntegral_const_mul_zpow' (a : ℂ) (n : ℤ) {r : ℝ} (hr : 0 < r) :
    (∮ z in C(0, r), a * z ^ n) = if n = -1 then a * (2 * π * Complex.I) else 0 := by
  split_ifs with hn
  · rw [circleIntegral.integral_const_mul, hn]
    have := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := r)
      (Metric.mem_ball_self hr)
    simp only [sub_zero] at this
    simp only [zpow_neg_one]
    rw [this]
  · exact circleIntegral_const_mul_zpow a hn r

theorem circleIntegral_four (a1 a2 a3 a4 : ℂ) (e1 e2 e3 e4 : ℤ) {r : ℝ} (hr : 0 < r) :
    (∮ x in C(0, r), (a1 * x ^ e1 + a2 * x ^ e2 + a3 * x ^ e3 + a4 * x ^ e4)) =
      (if e1 = -1 then a1 * (2 * π * Complex.I) else 0) +
        (if e2 = -1 then a2 * (2 * π * Complex.I) else 0) +
        (if e3 = -1 then a3 * (2 * π * Complex.I) else 0) +
        (if e4 = -1 then a4 * (2 * π * Complex.I) else 0) := by
  have hi := fun (a : ℂ) (e : ℤ) => circleIntegrable_const_mul_zpow a e hr
  have h2 : CircleIntegrable (fun x : ℂ => a1 * x ^ e1 + a2 * x ^ e2) 0 r :=
    (hi _ _).add (hi _ _)
  have h3 : CircleIntegrable (fun x : ℂ => a1 * x ^ e1 + a2 * x ^ e2 + a3 * x ^ e3) 0 r :=
    h2.add (hi _ _)
  rw [circleIntegral.integral_add h3 (hi _ _), circleIntegral.integral_add h2 (hi _ _),
    circleIntegral.integral_add (hi _ _) (hi _ _)]
  simp only [circleIntegral_const_mul_zpow' _ _ hr]

theorem mul_term_zpow {x : ℂ} (hx : x ≠ 0) (q : ℂ) (a b : ℤ) :
    x * (q * x ^ a * x ^ b) = q * x ^ (1 + a + b) := by
  rw [zpow_add₀ hx, zpow_add₀ hx, zpow_one]
  ring

/-- `x W_no(x,x)` term by term, for `x ≠ 0`. -/
theorem mul_WnoTerm_diag (j : ℕ) {x : ℂ} (hx : x ≠ 0) (m n : ℕ) :
    x * WnoTerm j x x m n =
      ((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + -((m : ℤ) + 2) + -((n : ℤ) + 2)) +
        ((coeff j (Amm (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + (m : ℤ) + (n : ℤ)) +
        ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + (m : ℤ) + -((n : ℤ) + 2)) +
        ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + -((m : ℤ) + 2) + (n : ℤ)) := by
  rw [WnoTerm, mul_add, mul_add, mul_add]
  simp only [← zpow_natCast]
  rw [mul_term_zpow hx, mul_term_zpow hx, mul_term_zpow hx, mul_term_zpow hx]

/-- The coefficient of `x⁻²` of a term of `[z^j] W_no(x,x)`: only `m = n` contributes, through
`A₋₊` and `A₊₋`. -/
theorem circleIntegral_mul_WnoTerm_diag (j : ℕ) {r : ℝ} (hr : 0 < r) (m n : ℕ) :
    (∮ x in C(0, r), x * WnoTerm j x x m n) =
      if m = n then (((coeff j (Amp (m + 1) (m + 1)) : ℚ) : ℂ) +
        ((coeff j (Apm (m + 1) (m + 1)) : ℚ) : ℂ)) * (2 * π * Complex.I) else 0 := by
  have hcongr : (∮ x in C(0, r), x * WnoTerm j x x m n) =
      ∮ x in C(0, r),
        (((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + -((m : ℤ) + 2) + -((n : ℤ) + 2)) +
        ((coeff j (Amm (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + (m : ℤ) + (n : ℤ)) +
        ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + (m : ℤ) + -((n : ℤ) + 2)) +
        ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * x ^ (1 + -((m : ℤ) + 2) + (n : ℤ))) := by
    refine circleIntegral.integral_congr hr.le fun x hx => ?_
    have hx0 : x ≠ 0 := by
      intro h0
      have hz' : ‖x‖ = r := by simpa using hx
      rw [h0, norm_zero] at hz'
      exact hr.ne hz'
    exact mul_WnoTerm_diag j hx0 m n
  rw [hcongr, circleIntegral_four _ _ _ _ _ _ _ _ hr]
  rw [if_neg (by omega), if_neg (by omega), zero_add, zero_add]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos (by omega), if_pos (by omega), if_pos rfl]
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg hmn, add_zero]

/-- `∮_{|x|=r} x [z^j]W_no(x,x) dx = 2πi · 2 [z^j] Tr(D M(z)² (I - M(z)²)⁻¹)`
(sphere/paper.tex l.941–945). -/
theorem circleIntegral_Wno_diag (j : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ x in C(0, r), x * ∑' mn : ℕ × ℕ, WnoTerm j x x mn.1 mn.2) =
      2 * π * Complex.I * (2 * ((coeff j traceDM : ℚ) : ℂ)) := by
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hcn : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = ‖(r : ℂ)‖ := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr0, hnr]
  have hr1' : ‖(r : ℂ)‖ < 1 := by rw [hnr]; exact hr1
  have hgs := summable_norm_Wno j (x1 := (r : ℂ)) (x2 := (r : ℂ)) hr1' hr1'
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 2 * π)
    (F := fun (mn : ℕ × ℕ) (θ : ℝ) => deriv (circleMap 0 r) θ •
      (circleMap 0 r θ * WnoTerm j (circleMap 0 r θ) (circleMap 0 r θ) mn.1 mn.2))
    (f := fun θ => deriv (circleMap 0 r) θ • (circleMap 0 r θ *
      ∑' mn : ℕ × ℕ, WnoTerm j (circleMap 0 r θ) (circleMap 0 r θ) mn.1 mn.2))
    (fun mn _ => r * (r *
      (‖((coeff j (App (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * cutz j (r : ℂ) mn.1 *
          cutz j (r : ℂ) mn.2‖ +
        ‖((coeff j (Amm (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * (r : ℂ) ^ mn.1 * (r : ℂ) ^ mn.2‖ +
        ‖((coeff j (Amp (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * (r : ℂ) ^ mn.1 *
          cutz j (r : ℂ) mn.2‖ +
        ‖((coeff j (Apm (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * cutz j (r : ℂ) mn.1 *
          (r : ℂ) ^ mn.2‖)))
    ?_ ?_ ?_ ?_ ?_
  · have h0 : (fun mn : ℕ × ℕ => ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ •
        (circleMap 0 r θ * WnoTerm j (circleMap 0 r θ) (circleMap 0 r θ) mn.1 mn.2)) =
        fun mn => if mn.1 = mn.2 then (((coeff j (Amp (mn.1 + 1) (mn.1 + 1)) : ℚ) : ℂ) +
          ((coeff j (Apm (mn.1 + 1) (mn.1 + 1)) : ℚ) : ℂ)) * (2 * π * Complex.I) else 0 :=
      funext fun mn => circleIntegral_mul_WnoTerm_diag j hr0 mn.1 mn.2
    rw [h0] at key
    have hfin : HasSum (fun mn : ℕ × ℕ =>
        if mn.1 = mn.2 then (((coeff j (Amp (mn.1 + 1) (mn.1 + 1)) : ℚ) : ℂ) +
          ((coeff j (Apm (mn.1 + 1) (mn.1 + 1)) : ℚ) : ℂ)) * (2 * π * Complex.I) else 0)
        (∑ b ∈ (range (j + 1)).image (fun m : ℕ => (m, m)),
          if b.1 = b.2 then (((coeff j (Amp (b.1 + 1) (b.1 + 1)) : ℚ) : ℂ) +
            ((coeff j (Apm (b.1 + 1) (b.1 + 1)) : ℚ) : ℂ)) * (2 * π * Complex.I) else 0) := by
      refine hasSum_sum_of_ne_finset_zero fun b hb => ?_
      by_cases hbb : b.1 = b.2
      · have hb1 : j + 1 ≤ b.1 := by
          by_contra hlt
          exact hb (Finset.mem_image.2 ⟨b.1, Finset.mem_range.2 (by omega), Prod.ext rfl hbb⟩)
        rw [if_pos hbb, X_pow_dvd_iff.1 (dvd_Amp (b.1 + 1) (b.1 + 1)) j (by omega),
          X_pow_dvd_iff.1 (dvd_Apm (b.1 + 1) (b.1 + 1)) j (by omega)]
        simp
      · rw [if_neg hbb]
    have hval := key.unique hfin
    have hT : (∮ x in C(0, r), x * ∑' mn : ℕ × ℕ, WnoTerm j x x mn.1 mn.2) =
        ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ • (circleMap 0 r θ *
          ∑' mn : ℕ × ℕ, WnoTerm j (circleMap 0 r θ) (circleMap 0 r θ) mn.1 mn.2) := rfl
    rw [hT, hval, Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.1 h).1)]
    simp only [if_true]
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    have e1 : ∑ m ∈ range (j + 1), ((coeff j (Amp (m + 1) (m + 1)) : ℚ) : ℂ) =
        ((coeff j traceDM : ℚ) : ℂ) := by
      rw [← traceAmp_eq, traceAmp, coeff_mk]
      push_cast
      rfl
    have e2 : ∑ m ∈ range (j + 1), ((coeff j (Apm (m + 1) (m + 1)) : ℚ) : ℂ) =
        ((coeff j traceDM : ℚ) : ℂ) := by
      rw [← traceApm_eq, traceApm, coeff_mk]
      push_cast
      rfl
    rw [e1, e2]
    ring
  · intro mn
    refine Continuous.aestronglyMeasurable ?_
    have hcm := continuous_circleMap 0 r
    have hne : ∀ θ, circleMap 0 r θ ≠ 0 := fun θ => circleMap_ne_center hr0.ne'
    have hz : ∀ k : ℤ, Continuous fun θ => circleMap 0 r θ ^ k := fun k =>
      hcm.zpow₀ k fun θ => Or.inl (hne θ)
    have hd : Continuous (deriv (circleMap 0 r)) := by
      rw [funext (deriv_circleMap 0 r)]
      exact hcm.mul continuous_const
    refine hd.smul ?_
    have : (fun θ => circleMap 0 r θ * WnoTerm j (circleMap 0 r θ) (circleMap 0 r θ) mn.1 mn.2) =
        fun θ => _ := funext fun θ => mul_WnoTerm_diag j (hne θ) mn.1 mn.2
    rw [this]
    exact (((continuous_const.mul (hz _)).add (continuous_const.mul (hz _))).add
      (continuous_const.mul (hz _))).add (continuous_const.mul (hz _))
  · intro mn
    refine Filter.Eventually.of_forall fun θ _ => ?_
    rw [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      abs_of_pos hr0, norm_mul, norm_circleMap_zero, abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (norm_WnoTerm_le j (hcn θ) (hcn θ) mn.1 mn.2) hr0.le) hr0.le
  · exact Filter.Eventually.of_forall fun θ _ => (hgs.mul_left r).mul_left r
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have h1 : ‖circleMap 0 r θ‖ < 1 := by rw [hcn θ]; exact hr1'
    exact ((summable_WnoTerm j h1 h1).hasSum.mul_left _).const_smul _

end Virasoro.Sphere
