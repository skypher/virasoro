import Virasoro.Sphere.Proofs.Sec3BergmanSummable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Sphere paper Lemma 3.5, Step 3: the zero-mode condition (`sphere/paper.tex` l.931–933)

`[z^j] W_no(x₁,x₂)` has no `x₁⁻¹` term on `0 < |x₁| < 1`, so
`∮_{|x₁|=r} [z^j] W_no(x₁,x₂) dx₁ = 0` for `0 < r < 1`: the series converges normally on the
circle and is integrated term by term.

Consumer: `Stmt_sub_bergman_zero_mode`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset MeasureTheory Real

theorem norm_cutz (j : ℕ) {x y : ℂ} (h : ‖x‖ = ‖y‖) (m : ℕ) : ‖cutz j x m‖ = ‖cutz j y m‖ := by
  unfold cutz
  split_ifs
  · rw [norm_zpow, norm_zpow, h]
  · rfl

/-- A majorant of the terms of `[z^j] W_no(x₁,x₂)` that only depends on `|x₁|`. -/
theorem norm_WnoTerm_le (j : ℕ) {x1 y1 x2 y2 : ℂ} (h : ‖x1‖ = ‖y1‖) (h' : ‖x2‖ = ‖y2‖)
    (m n : ℕ) :
    ‖WnoTerm j x1 x2 m n‖ ≤
      ‖((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * cutz j y1 m * cutz j y2 n‖ +
        ‖((coeff j (Amm (m + 1) (n + 1)) : ℚ) : ℂ) * y1 ^ m * y2 ^ n‖ +
        ‖((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * y1 ^ m * cutz j y2 n‖ +
        ‖((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * cutz j y1 m * y2 ^ n‖ := by
  rw [WnoTerm_cut]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans (le_of_eq ?_)
  simp only [norm_mul, norm_pow, norm_cutz j h, norm_cutz j h', h, h']

theorem circleIntegral_const_mul_zpow (a : ℂ) {n : ℤ} (hn : n ≠ -1) (r : ℝ) :
    (∮ z in C(0, r), a * z ^ n) = 0 := by
  rw [circleIntegral.integral_const_mul]
  have := circleIntegral.integral_sub_zpow_of_ne hn 0 0 r
  simp only [sub_zero] at this
  rw [this, mul_zero]

theorem circleIntegrable_const_mul_zpow (a : ℂ) (n : ℤ) {r : ℝ} (hr : 0 < r) :
    CircleIntegrable (fun z => a * z ^ n) 0 r := by
  refine ContinuousOn.circleIntegrable hr.le
    (continuousOn_const.mul (continuousOn_id.zpow₀ n fun z hz => Or.inl ?_))
  intro h0
  have hz' : ‖z‖ = r := by simpa using hz
  rw [show z = 0 from h0, norm_zero] at hz'
  exact hr.ne hz'

theorem WnoTerm_eq_x1 (j : ℕ) (x1 x2 : ℂ) (m n : ℕ) :
    WnoTerm j x1 x2 m n =
      (((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * x2 ^ (-((n : ℤ) + 2)) +
          ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * x2 ^ n) * x1 ^ (-((m : ℤ) + 2)) +
        (((coeff j (Amm (m + 1) (n + 1)) : ℚ) : ℂ) * x2 ^ n +
          ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x2 ^ (-((n : ℤ) + 2))) *
          x1 ^ ((m : ℕ) : ℤ) := by
  rw [WnoTerm, zpow_natCast]
  ring

/-- No term of `[z^j] W_no(x₁,x₂)` is a multiple of `x₁⁻¹`. -/
theorem circleIntegral_WnoTerm (j : ℕ) {r : ℝ} (hr : 0 < r) (x2 : ℂ) (m n : ℕ) :
    (∮ x1 in C(0, r), WnoTerm j x1 x2 m n) = 0 := by
  simp only [WnoTerm_eq_x1]
  rw [circleIntegral.integral_add (circleIntegrable_const_mul_zpow _ _ hr)
    (circleIntegrable_const_mul_zpow _ _ hr), circleIntegral_const_mul_zpow _ (by omega),
    circleIntegral_const_mul_zpow _ (by omega), add_zero]

/-- The zero-mode condition for `W_no` (sphere/paper.tex l.931–933):
`∮_{|x₁|=r} [z^j] W_no(x₁,x₂) dx₁ = 0` for `0 < r < 1` and `|x₂| < 1`. -/
theorem circleIntegral_Wno_eq_zero (j : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {x2 : ℂ}
    (h2 : ‖x2‖ < 1) :
    (∮ x1 in C(0, r), ∑' mn : ℕ × ℕ, WnoTerm j x1 x2 mn.1 mn.2) = 0 := by
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hcn : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = ‖(r : ℂ)‖ := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr0, hnr]
  have hgs := summable_norm_Wno j (x1 := (r : ℂ)) (x2 := x2) (by rw [hnr]; exact hr1) h2
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 2 * π)
    (F := fun (mn : ℕ × ℕ) (θ : ℝ) =>
      deriv (circleMap 0 r) θ • WnoTerm j (circleMap 0 r θ) x2 mn.1 mn.2)
    (f := fun θ =>
      deriv (circleMap 0 r) θ • ∑' mn : ℕ × ℕ, WnoTerm j (circleMap 0 r θ) x2 mn.1 mn.2)
    (fun mn _ => r *
      (‖((coeff j (App (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * cutz j (r : ℂ) mn.1 * cutz j x2 mn.2‖ +
        ‖((coeff j (Amm (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * (r : ℂ) ^ mn.1 * x2 ^ mn.2‖ +
        ‖((coeff j (Amp (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * (r : ℂ) ^ mn.1 * cutz j x2 mn.2‖ +
        ‖((coeff j (Apm (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * cutz j (r : ℂ) mn.1 * x2 ^ mn.2‖))
    ?_ ?_ ?_ ?_ ?_
  · have h0 : (fun mn : ℕ × ℕ => ∫ θ in (0 : ℝ)..2 * π,
        deriv (circleMap 0 r) θ • WnoTerm j (circleMap 0 r θ) x2 mn.1 mn.2) = fun _ => 0 :=
      funext fun mn => circleIntegral_WnoTerm j hr0 x2 mn.1 mn.2
    rw [h0] at key
    exact key.unique hasSum_zero
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
    simp only [WnoTerm_eq_x1]
    exact (continuous_const.mul (hz _)).add (continuous_const.mul (hz _))
  · intro mn
    refine Filter.Eventually.of_forall fun θ _ => ?_
    rw [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_left (norm_WnoTerm_le j (hcn θ) rfl mn.1 mn.2) hr0.le
  · exact Filter.Eventually.of_forall fun θ _ => hgs.mul_left r
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    exact (summable_WnoTerm j (by rw [hcn θ, hnr]; exact hr1) h2).hasSum.const_smul _

end Virasoro.Sphere
