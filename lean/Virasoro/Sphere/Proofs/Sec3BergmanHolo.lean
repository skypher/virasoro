import Virasoro.Sphere.Proofs.Sec3BergmanLiouConst
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Sphere paper Lemma 3.5: each `[z^j] W_no(x₁,x₂)` is holomorphic in `x₁`
(`sphere/paper.tex` l.878–880)

Local normal convergence on `0 < |x₁| < 1`, with the majorant of `summable_norm_block`.

Consumer: `sub_bergman_const_of_patches`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology

/-- Each coefficient `[z^j] W_no(x₁,x₂)` is holomorphic in `x₁` on `0 < |x₁| < 1`. -/
theorem coeffDiff_Wnos {x1 x2 : ℂ} (h0 : 0 < ‖x1‖) (h1 : ‖x1‖ < 1) (h2 : ‖x2‖ < 1) :
    CoeffDiff (fun y => Wnos y x2) x1 := fun j => by
  simp only [Wnos, coeff_mk]
  have hr1pos : 0 < ‖x1‖ / 2 := by positivity
  have hr2lt : (‖x1‖ + 1) / 2 < 1 := by linarith
  have hr2pos : 0 < (‖x1‖ + 1) / 2 := by linarith
  have hU : IsOpen {y : ℂ | ‖x1‖ / 2 < ‖y‖ ∧ ‖y‖ < (‖x1‖ + 1) / 2} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hxU : x1 ∈ {y : ℂ | ‖x1‖ / 2 < ‖y‖ ∧ ‖y‖ < (‖x1‖ + 1) / 2} :=
    ⟨by linarith, by linarith⟩
  have hn1 : ‖((‖x1‖ / 2 : ℝ) : ℂ)‖ = ‖x1‖ / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr1pos.le]
  have hn2 : ‖(((‖x1‖ + 1) / 2 : ℝ) : ℂ)‖ = (‖x1‖ + 1) / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr2pos.le]
  have hn2' : ‖(((‖x1‖ + 1) / 2 : ℝ) : ℂ)‖ < 1 := by rw [hn2]; exact hr2lt
  have hsum := (((summable_norm_block PolyBdd.App j (cutz j ((‖x1‖ / 2 : ℝ) : ℂ)) (cutz j x2)
      (fun d => summable_cutz j d _) (fun d => summable_cutz j d _)).add
    (summable_norm_block PolyBdd.Amm j (fun m => (((‖x1‖ + 1) / 2 : ℝ) : ℂ) ^ m) (fun n => x2 ^ n)
      (fun d => summable_geom_norm d hn2') (fun d => summable_geom_norm d h2))).add
    (summable_norm_block PolyBdd.Amp j (fun m => (((‖x1‖ + 1) / 2 : ℝ) : ℂ) ^ m) (cutz j x2)
      (fun d => summable_geom_norm d hn2') (fun d => summable_cutz j d _))).add
    (summable_norm_block PolyBdd.Apm j (cutz j ((‖x1‖ / 2 : ℝ) : ℂ)) (fun n => x2 ^ n)
      (fun d => summable_cutz j d _) (fun d => summable_geom_norm d h2))
  refine (Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (mn : ℕ × ℕ) (y : ℂ) => WnoTerm j y x2 mn.1 mn.2) hsum
    (fun mn => ?_) hU (fun mn y hy => ?_)).differentiableAt (hU.mem_nhds hxU)
  · simp only [WnoTerm_eq_x1]
    have hne : ∀ y ∈ {y : ℂ | ‖x1‖ / 2 < ‖y‖ ∧ ‖y‖ < (‖x1‖ + 1) / 2}, y ≠ 0 := fun y hy h => by
      have hy' : ‖x1‖ / 2 < ‖y‖ := hy.1
      rw [h, norm_zero] at hy'
      linarith
    exact fun y hy => (((differentiableAt_const _).mul
      (differentiableAt_zpow.2 (Or.inl (hne y hy)))).add ((differentiableAt_const _).mul
      (differentiableAt_zpow.2 (Or.inl (hne y hy))))).differentiableWithinAt
  · rw [WnoTerm_cut]
    have hc : ‖cutz j y mn.1‖ ≤ ‖cutz j ((‖x1‖ / 2 : ℝ) : ℂ) mn.1‖ := by
      unfold cutz
      split_ifs
      · have e : ((mn.1 : ℤ) + 2) = ((mn.1 + 2 : ℕ) : ℤ) := by push_cast; ring
        rw [norm_zpow, norm_zpow, hn1, zpow_neg, zpow_neg, e, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hr1pos _) (pow_le_pow_left₀ hr1pos.le hy.1.le _)
      · exact le_rfl
    have hp : ‖y ^ mn.1‖ ≤ ‖(((‖x1‖ + 1) / 2 : ℝ) : ℂ) ^ mn.1‖ := by
      rw [norm_pow, norm_pow, hn2]
      exact pow_le_pow_left₀ (norm_nonneg _) hy.2.le _
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans ?_
    simp only [norm_mul]
    gcongr

/-- Lemma 3.5, holomorphy of the coefficients of `W_no` (sphere/paper.tex l.878–880). -/
theorem sub_bergman_holo : Stmt_sub_bergman_holo :=
  fun _ h2 _ h10 h11 => coeffDiff_Wnos h10 h11 h2

end Virasoro.Sphere
