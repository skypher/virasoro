import Virasoro.Sphere.Proofs.Sec3BergmanG
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Sphere paper Lemma 3.5, Step 3: the coincidence limit (`sphere/paper.tex` l.946–949)

`W_no(x,x) = lim_{x₁→x} (W(x₁,x) - (x₁-x)⁻²)` coefficientwise in `z`: each coefficient
`[z^j] W_no(x₁,x)` is continuous in `x₁` (normal convergence on an annulus around `|x|`), and so
are the coefficients of `g(x₁)` and `S(x₁,x)`.  The off-diagonal identity
`4 (g₁g₂S - 1)(W_no + 2C g₁g₂) = -(x₁x₂-z)² g₁²g₂²` therefore holds at `x₁ = x₂ = x`, where
`g²S = g²P = -1`:
`W_no(x,x) = (x²-z)² g(x)⁴/8 - 2C g(x)² = (x²-z)²/(8x²(x-1)²(x-z)²) + 2C/(x(x-1)(x-z))`.

Consumer: `Stmt_sub_bergman_residue`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology

/-- Every coefficient of the series `F(y)` is continuous in `y` at `x`. -/
def CoeffCont (F : ℂ → PowerSeries ℂ) (x : ℂ) : Prop :=
  ∀ j : ℕ, ContinuousAt (fun y => coeff j (F y)) x

theorem CoeffCont.const (f : PowerSeries ℂ) (x : ℂ) : CoeffCont (fun _ => f) x :=
  fun _ => continuousAt_const

theorem CoeffCont.add {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffCont F x)
    (hG : CoeffCont G x) : CoeffCont (fun y => F y + G y) x := fun j => by
  simp only [map_add]
  exact (hF j).add (hG j)

theorem CoeffCont.sub {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffCont F x)
    (hG : CoeffCont G x) : CoeffCont (fun y => F y - G y) x := fun j => by
  simp only [map_sub]
  exact (hF j).sub (hG j)

theorem CoeffCont.neg {F : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffCont F x) :
    CoeffCont (fun y => -F y) x := fun j => by
  simp only [map_neg]
  exact (hF j).neg

theorem CoeffCont.mul {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffCont F x)
    (hG : CoeffCont G x) : CoeffCont (fun y => F y * G y) x := fun j => by
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun p _ => (hF p.1).mul (hG p.2)

theorem CoeffCont.pow {F : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffCont F x) (n : ℕ) :
    CoeffCont (fun y => F y ^ n) x := by
  induction n with
  | zero => simpa only [pow_zero] using CoeffCont.const 1 x
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem CoeffCont.C {φ : ℂ → ℂ} {x : ℂ} (h : ContinuousAt φ x) :
    CoeffCont (fun y => PowerSeries.C (φ y)) x := fun j => by
  simp only [coeff_C]
  split_ifs
  · exact h
  · exact continuousAt_const

theorem cpow_half_ne_zero {w : ℂ} (hw : w ≠ 0) : w ^ (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have := cpow_half_sq w
  rw [h] at this
  exact hw (by simpa using this.symm)

theorem coeffCont_gser {x : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) : CoeffCont gser x := fun j => by
  have hre : (1 - x) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have := Complex.re_le_norm x
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hs : ContinuousAt (fun y : ℂ => (1 - y) ^ (1 / 2 : ℂ)) x :=
    ContinuousAt.comp (f := fun y : ℂ => 1 - y) (g := fun w : ℂ => w ^ (1 / 2 : ℂ))
      (continuousAt_cpow_const hre) (continuousAt_const.sub continuousAt_id)
  have hsne : (1 - x) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_half_ne_zero (sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt h1)))
  simp only [gser, coeff_C_mul, invSqrtZ, coeff_mk]
  exact ((continuousAt_id.mul hs).inv₀ (mul_ne_zero h0 hsne)).mul
    (continuousAt_const.mul (continuousAt_zpow₀ x _ (Or.inl h0)))

theorem coeffCont_Sser (x : ℂ) : CoeffCont (fun y => Sser y x) x := by
  unfold Sser
  exact (CoeffCont.C (by fun_prop)).add ((CoeffCont.C (by fun_prop)).mul (CoeffCont.const X x))

/-- Each coefficient `[z^j] W_no(x₁,x₂)` is continuous in `x₁` on `0 < |x₁| < 1`. -/
theorem coeffCont_Wnos {x1 x2 : ℂ} (h0 : 0 < ‖x1‖) (h1 : ‖x1‖ < 1) (h2 : ‖x2‖ < 1) :
    CoeffCont (fun y => Wnos y x2) x1 := fun j => by
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
  refine (continuousOn_tsum (f := fun (mn : ℕ × ℕ) (y : ℂ) => WnoTerm j y x2 mn.1 mn.2)
    (fun mn => ?_) hsum (fun mn y hy => ?_)).continuousAt (hU.mem_nhds hxU)
  · simp only [WnoTerm_eq_x1]
    have hne : ∀ y ∈ {y : ℂ | ‖x1‖ / 2 < ‖y‖ ∧ ‖y‖ < (‖x1‖ + 1) / 2}, y ≠ 0 := fun y hy h => by
      have hy' : ‖x1‖ / 2 < ‖y‖ := hy.1
      rw [h, norm_zero] at hy'
      linarith
    exact (continuousOn_const.mul (continuousOn_id.zpow₀ _ fun y hy => Or.inl (hne y hy))).add
      (continuousOn_const.mul (continuousOn_id.zpow₀ _ fun y hy => Or.inl (hne y hy)))
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

theorem Sser_diag (x : ℂ) : Sser x x = Pser x := by
  have ea : x * x * (x + x) / 2 - x * x = x ^ 2 * (x - 1) := by ring
  have eb : (x + x) / 2 - x * x = -(x * (x - 1)) := by ring
  rw [Sser, Pser, ea, eb, map_neg]
  ring

/-- The coincidence limit (sphere/paper.tex l.946–949):
`8 W_no(x,x) + 16 C g(x)² = (x²-z)² g(x)⁴`, with `g² = -1/P` and `g⁴ = 1/P²`. -/
theorem diag_formula {Cz : PowerSeries ℂ} (hC : IsWFormula Cz) {x : ℂ} (h0 : 0 < ‖x‖)
    (h1 : ‖x‖ < 1) :
    8 * Wnos x x + 16 * Cz * gser x ^ 2 = (PowerSeries.C x * PowerSeries.C x - X) ^ 2 * gser x ^ 4 := by
  have hx0 := norm_pos_iff.1 h0
  have hg := coeffCont_gser hx0 h1
  have hgc := CoeffCont.const (gser x) x
  have hS := coeffCont_Sser x
  have hW := coeffCont_Wnos h0 h1 h1
  have hF1 : CoeffCont (fun y => 4 * ((gser y * gser x * Sser y x - 1) *
      (Wnos y x + 2 * Cz * (gser y * gser x)))) x :=
    (CoeffCont.const 4 x).mul ((((hg.mul hgc).mul hS).sub (CoeffCont.const 1 x)).mul
      (hW.add ((CoeffCont.const (2 * Cz) x).mul (hg.mul hgc))))
  have hF2 : CoeffCont (fun y => -((PowerSeries.C y * PowerSeries.C x - X) ^ 2 * gser y ^ 2 *
      gser x ^ 2)) x :=
    ((((((CoeffCont.C continuousAt_id).mul (CoeffCont.const (PowerSeries.C x) x)).sub
      (CoeffCont.const X x)).pow 2).mul (hg.pow 2)).mul (CoeffCont.const (gser x ^ 2) x)).neg
  have key : 4 * ((gser x * gser x * Sser x x - 1) *
      (Wnos x x + 2 * Cz * (gser x * gser x))) =
      -((PowerSeries.C x * PowerSeries.C x - X) ^ 2 * gser x ^ 2 * gser x ^ 2) := by
    ext j
    have hev : (fun y => coeff j (4 * ((gser y * gser x * Sser y x - 1) *
        (Wnos y x + 2 * Cz * (gser y * gser x))))) =ᶠ[𝓝[≠] x]
        fun y => coeff j (-((PowerSeries.C y * PowerSeries.C x - X) ^ 2 * gser y ^ 2 *
          gser x ^ 2)) := by
      have hopen : IsOpen {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} :=
        (isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)
      have hmem : {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} ∈ 𝓝 x := hopen.mem_nhds ⟨h0, h1⟩
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with y hy hyne
      exact congrArg (coeff j) (offdiag hC hy.1 hy.2 h0 h1 hyne)
    exact tendsto_nhds_unique (((hF1 j).tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
      ((hF2 j).tendsto.mono_left nhdsWithin_le_nhds)
  have hgP := gser_sq_mul_Pser hx0 (ne_one_of_norm_lt h1)
  rw [Sser_diag] at key
  linear_combination (-1) * key + (4 * (Wnos x x + 2 * Cz * gser x ^ 2)) * hgP

end Virasoro.Sphere
