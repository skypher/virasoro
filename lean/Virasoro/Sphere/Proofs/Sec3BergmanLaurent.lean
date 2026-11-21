import Virasoro.Sphere.Proofs.Sec3BergmanDiag

/-!
# Sphere paper Lemma 3.5, Step 3: circle integrals as Laurent coefficients (`sphere/paper.tex` l.931–966)

The contour integrals of Step 3 are evaluated, at each order in `z`, as `2πi` times the
coefficient of `x⁻¹` of a Laurent series that converges on the circle:
`∮_{|x|=r} x^a ∑_i c_i x^i dx = 2πi c_{-a-1}` when `∑ |c_i| r^i < ∞`.

Consumer: `Stmt_sub_bergman_zero_mode`, `Stmt_sub_bergman_residue`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset MeasureTheory Real

/-- `∮_{|x|=r} x^a ∑_i c_i x^i dx = 2πi c_{-a-1}` (zero when `-a-1 < 0`), for a power series
that converges absolutely on the circle. -/
theorem circleIntegral_zpow_mul_tsum (c : ℕ → ℂ) (a : ℤ) {r : ℝ} (hr : 0 < r)
    (hs : Summable fun i : ℕ => ‖c i‖ * r ^ i) :
    (∮ x in C(0, r), x ^ a * ∑' i : ℕ, c i * x ^ i) =
      ∑' i : ℕ, if a + (i : ℤ) = -1 then c i * (2 * π * Complex.I) else 0 := by
  have hne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun θ => circleMap_ne_center hr.ne'
  have hterm : ∀ (i : ℕ) (θ : ℝ), circleMap 0 r θ ^ a * (c i * circleMap 0 r θ ^ i) =
      c i * circleMap 0 r θ ^ (a + (i : ℤ)) := fun i θ => by
    rw [zpow_add₀ (hne θ), zpow_natCast]
    ring
  have hsum : ∀ θ : ℝ, Summable fun i : ℕ => c i * circleMap 0 r θ ^ i := fun θ =>
    Summable.of_norm_bounded hs fun i => by
      rw [norm_mul, norm_pow, norm_circleMap_zero, abs_of_pos hr]
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 2 * π)
    (F := fun (i : ℕ) (θ : ℝ) => deriv (circleMap 0 r) θ •
      (c i * circleMap 0 r θ ^ (a + (i : ℤ))))
    (f := fun θ => deriv (circleMap 0 r) θ •
      (circleMap 0 r θ ^ a * ∑' i : ℕ, c i * circleMap 0 r θ ^ i))
    (fun (i : ℕ) _ => r * (r ^ a * (‖c i‖ * r ^ i))) ?_ ?_ ?_ ?_ ?_
  · have h0 : (fun i : ℕ => ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ •
        (c i * circleMap 0 r θ ^ (a + (i : ℤ)))) =
        fun i : ℕ => if a + (i : ℤ) = -1 then c i * (2 * π * Complex.I) else 0 :=
      funext fun i => circleIntegral_const_mul_zpow' (c i) (a + (i : ℤ)) hr
    rw [h0] at key
    exact key.tsum_eq.symm
  · intro i
    refine Continuous.aestronglyMeasurable ?_
    have hcm := continuous_circleMap 0 r
    have hd : Continuous (deriv (circleMap 0 r)) := by
      rw [funext (deriv_circleMap 0 r)]
      exact hcm.mul continuous_const
    exact hd.smul (continuous_const.mul (hcm.zpow₀ _ fun θ => Or.inl (hne θ)))
  · intro i
    refine Filter.Eventually.of_forall fun θ _ => ?_
    rw [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      abs_of_pos hr, norm_mul, norm_zpow, norm_circleMap_zero, abs_of_pos hr,
      zpow_add₀ hr.ne', zpow_natCast]
    exact le_of_eq (by ring)
  · exact Filter.Eventually.of_forall fun θ _ => (hs.mul_left _).mul_left _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have h := ((hsum θ).hasSum.mul_left (circleMap 0 r θ ^ a)).const_smul
      (deriv (circleMap 0 r) θ)
    simp only [hterm] at h
    exact h

end Virasoro.Sphere
