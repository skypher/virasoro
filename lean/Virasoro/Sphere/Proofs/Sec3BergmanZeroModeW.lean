import Virasoro.Sphere.Proofs.Sec3BergmanResidue

/-!
# Sphere paper Lemma 3.5, Step 3: the zero-mode condition for `W` (`sphere/paper.tex` l.931–933)

Since `[z^j] W(x₁,x₂)` has no `x₁⁻¹` term on `0 < |x₁| < 1` and the diagonal double pole
`(x₁-x₂)⁻²` has zero residue, `∮_{|x₁|=r} W(x₁,x₂) dx₁ = 0` coefficientwise in `z`, for
`0 < r < 1` with `r ≠ |x₂|`.

Consumer: `Stmt_sub_bergman_zero_mode`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Real

/-- The zero-mode condition (sphere/paper.tex l.931–933). -/
theorem circleIntegral_W_eq_zero (j : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {x2 : ℂ}
    (h2 : ‖x2‖ < 1) (hne : ‖x2‖ ≠ r) :
    (∮ x1 in C(0, r), coeff j (Wser x1 x2)) = 0 := by
  have hc : (∮ x1 in C(0, r), coeff j (Wser x1 x2)) =
      ∮ x1 in C(0, r), ((if j = 0 then (1 : ℂ) else 0) * (x1 - x2) ^ (-2 : ℤ) +
        ∑' mn : ℕ × ℕ, WnoTerm j x1 x2 mn.1 mn.2) := by
    refine circleIntegral.integral_congr hr0.le fun x1 _ => ?_
    rw [Wser, coeff_mk, zpow_neg, zpow_ofNat]
    split_ifs <;> simp
  have h1 : CircleIntegrable
      (fun x1 : ℂ => (if j = 0 then (1 : ℂ) else 0) * (x1 - x2) ^ (-2 : ℤ)) 0 r := by
    refine ContinuousOn.circleIntegrable hr0.le (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun x1 hx1 => Or.inl ?_))
    intro h0
    have hx : x1 = x2 := sub_eq_zero.1 h0
    exact hne (by rw [← hx]; exact sphere_norm hx1)
  have h2' : CircleIntegrable
      (fun x1 : ℂ => ∑' mn : ℕ × ℕ, WnoTerm j x1 x2 mn.1 mn.2) 0 r := by
    refine ContinuousOn.circleIntegrable hr0.le fun x1 hx1 => ContinuousAt.continuousWithinAt ?_
    have hx0 : 0 < ‖x1‖ := by rw [sphere_norm hx1]; exact hr0
    have hx1' : ‖x1‖ < 1 := by rw [sphere_norm hx1]; exact hr1
    have := coeffCont_Wnos hx0 hx1' h2 j
    simpa only [Wnos, coeff_mk] using this
  rw [hc, circleIntegral.integral_add h1 h2', circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_zpow_of_ne (by norm_num), mul_zero, zero_add,
    circleIntegral_Wno_eq_zero j hr0 hr1 h2]

end Virasoro.Sphere
