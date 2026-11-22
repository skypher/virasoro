import Virasoro.Sphere.Proofs.Sec3BergmanZeroModeW
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Sphere paper Lemma 3.5, Step 2: `Y(x)` coefficientwise in `z`, and the pole at `x₁ = x₂`
(`sphere/paper.tex` l.914–924)

`Y(x) = x √(1-x) √(1-z/x)` as a series in `z` (the branch `√(x-1) = ±i√(1-x)` only changes `Y`
by a constant factor), with `g(x) Y(x) = 1` and `Y(x)² = -P(x)`.  Coefficientwise
differentiability and boundedness near a point.  The cancellation of the double pole at
`x₁ = x₂` is in `Sec3BergmanPole.lean`.

Consumer: `sub_bergman_const_of_patches`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology

/-- `√(1-p)` with complex coefficients. -/
noncomputable def sOneC : PowerSeries ℂ := sOne.map (algebraMap ℚ ℂ)

/-- `√(1 - z/x)` as a power series in `z`. -/
noncomputable def sqrtZ (x : ℂ) : PowerSeries ℂ := rescale x⁻¹ sOneC

theorem sqrtZ_mul_invSqrtZ (x : ℂ) : sqrtZ x * invSqrtZ x = 1 := by
  rw [sqrtZ, sOneC, invSqrtZ_eq, ← map_mul, ← map_mul, mul_comm, hser_mul_sOne, map_one, map_one]

/-- `Y(x) = x √(1-x) √(1-z/x)`, coefficientwise in `z` (l.914). -/
noncomputable def Yser (x : ℂ) : PowerSeries ℂ := C (x * (1 - x) ^ (1 / 2 : ℂ)) * sqrtZ x

theorem gser_mul_Yser {x : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) : gser x * Yser x = 1 := by
  have hsne : (1 - x) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_half_ne_zero (sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt h1)))
  have hc : (x * (1 - x) ^ (1 / 2 : ℂ))⁻¹ * (x * (1 - x) ^ (1 / 2 : ℂ)) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero h0 hsne)
  have e : C ((x * (1 - x) ^ (1 / 2 : ℂ))⁻¹) * invSqrtZ x * (C (x * (1 - x) ^ (1 / 2 : ℂ)) * sqrtZ x) =
      (C ((x * (1 - x) ^ (1 / 2 : ℂ))⁻¹) * C (x * (1 - x) ^ (1 / 2 : ℂ))) *
        (sqrtZ x * invSqrtZ x) := by ring
  rw [gser, Yser, e, ← map_mul, hc, map_one, one_mul, sqrtZ_mul_invSqrtZ]

theorem Yser_sq {x : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) : Yser x ^ 2 = -Pser x := by
  have hgP := gser_sq_mul_Pser h0 (ne_one_of_norm_lt h1)
  have hgY := gser_mul_Yser h0 h1
  linear_combination Yser x ^ 2 * hgP - Pser x * (gser x * Yser x + 1) * hgY

/-- Every coefficient of the series `F(y)` is differentiable in `y` at `x`. -/
def CoeffDiff (F : ℂ → PowerSeries ℂ) (x : ℂ) : Prop :=
  ∀ j : ℕ, DifferentiableAt ℂ (fun y => coeff j (F y)) x

theorem CoeffDiff.coeffCont {F : ℂ → PowerSeries ℂ} {x : ℂ} (h : CoeffDiff F x) :
    CoeffCont F x := fun j => (h j).continuousAt

theorem CoeffDiff.const (f : PowerSeries ℂ) (x : ℂ) : CoeffDiff (fun _ => f) x :=
  fun _ => differentiableAt_const _

theorem CoeffDiff.add {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffDiff F x)
    (hG : CoeffDiff G x) : CoeffDiff (fun y => F y + G y) x := fun j => by
  simp only [map_add]
  exact (hF j).add (hG j)

theorem CoeffDiff.mul {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffDiff F x)
    (hG : CoeffDiff G x) : CoeffDiff (fun y => F y * G y) x := fun j => by
  simp only [coeff_mul]
  exact DifferentiableAt.fun_sum fun p _ => (hF p.1).mul (hG p.2)

theorem CoeffDiff.C {φ : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ φ x) :
    CoeffDiff (fun y => PowerSeries.C (φ y)) x := fun j => by
  simp only [coeff_C]
  split_ifs
  · exact h
  · exact differentiableAt_const _

theorem slit_one_sub {x : ℂ} (h1 : ‖x‖ < 1) : (1 - x) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have := Complex.re_le_norm x
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem differentiableAt_sqrt_one_sub {x : ℂ} (h1 : ‖x‖ < 1) :
    DifferentiableAt ℂ (fun y : ℂ => (1 - y) ^ (1 / 2 : ℂ)) x :=
  DifferentiableAt.cpow_const ((differentiableAt_const _).sub differentiableAt_id)
    (slit_one_sub h1)

theorem coeff_sqrtZ (x : ℂ) (k : ℕ) : coeff k (sqrtZ x) = x⁻¹ ^ k * coeff k sOneC := by
  rw [sqrtZ, coeff_rescale]

theorem coeffDiff_sqrtZ {x : ℂ} (h0 : x ≠ 0) : CoeffDiff sqrtZ x := fun k => by
  simp only [coeff_sqrtZ]
  exact (((differentiableAt_inv h0).pow k)).mul (differentiableAt_const _)

theorem coeffDiff_Yser {x : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) : CoeffDiff Yser x :=
  (CoeffDiff.C (differentiableAt_id.mul (differentiableAt_sqrt_one_sub h1))).mul
    (coeffDiff_sqrtZ h0)

theorem coeffDiff_Sser (x x2 : ℂ) : CoeffDiff (fun y => Sser y x2) x := by
  unfold Sser
  exact (CoeffDiff.C (by fun_prop)).add ((CoeffDiff.C (by fun_prop)).mul (CoeffDiff.const X x))

/-- `f` is bounded on a punctured neighbourhood of `c`. -/
def BddNear (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ ε > 0, ∃ M : ℝ, ∀ x, x ≠ c → ‖x - c‖ < ε → ‖f x‖ ≤ M

theorem BddNear.add {f g : ℂ → ℂ} {c : ℂ} (hf : BddNear f c) (hg : BddNear g c) :
    BddNear (fun x => f x + g x) c := by
  obtain ⟨ε1, h1, M1, hM1⟩ := hf
  obtain ⟨ε2, h2, M2, hM2⟩ := hg
  refine ⟨min ε1 ε2, lt_min h1 h2, M1 + M2, fun x hx hxε => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (hM1 x hx (lt_of_lt_of_le hxε (min_le_left _ _)))
    (hM2 x hx (lt_of_lt_of_le hxε (min_le_right _ _))))

theorem BddNear.mul {f g : ℂ → ℂ} {c : ℂ} (hf : BddNear f c) (hg : BddNear g c) :
    BddNear (fun x => f x * g x) c := by
  obtain ⟨ε1, h1, M1, hM1⟩ := hf
  obtain ⟨ε2, h2, M2, hM2⟩ := hg
  refine ⟨min ε1 ε2, lt_min h1 h2, M1 * M2, fun x hx hxε => ?_⟩
  have e1 := hM1 x hx (lt_of_lt_of_le hxε (min_le_left _ _))
  have e2 := hM2 x hx (lt_of_lt_of_le hxε (min_le_right _ _))
  rw [norm_mul]
  exact mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)

theorem BddNear.of_tendsto {f : ℂ → ℂ} {c L : ℂ} (h : Tendsto f (𝓝[≠] c) (𝓝 L)) :
    BddNear f c := by
  have h1 : ∀ᶠ x in 𝓝[≠] c, ‖f x‖ < ‖L‖ + 1 :=
    h.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, hh⟩ := h1
  exact ⟨ε, hε, ‖L‖ + 1, fun x hx hxε => (hh (by rwa [dist_eq_norm]) hx).le⟩

theorem BddNear.of_continuousAt {f : ℂ → ℂ} {c : ℂ} (h : ContinuousAt f c) : BddNear f c :=
  BddNear.of_tendsto (h.tendsto.mono_left nhdsWithin_le_nhds)

theorem BddNear.congr {f g : ℂ → ℂ} {c : ℂ} (hf : BddNear f c)
    (h : ∃ δ > 0, ∀ x, x ≠ c → ‖x - c‖ < δ → g x = f x) : BddNear g c := by
  obtain ⟨ε, hε, M, hM⟩ := hf
  obtain ⟨δ, hδ, hh⟩ := h
  refine ⟨min ε δ, lt_min hε hδ, M, fun x hx hxε => ?_⟩
  rw [hh x hx (lt_of_lt_of_le hxε (min_le_right _ _))]
  exact hM x hx (lt_of_lt_of_le hxε (min_le_left _ _))

/-- Coefficient of `g · S(x₁,x₂)` as a polynomial in `x₁`. -/
theorem coeff_mul_Sser (g : PowerSeries ℂ) (x1 x2 : ℂ) (j : ℕ) :
    coeff j (g * Sser x1 x2) =
      coeff j g * (x1 * x2 * (x1 + x2) / 2 - x1 * x2) +
        coeff j (g * X) * ((x1 + x2) / 2 - x1 * x2) := by
  have e : g * Sser x1 x2 = g * C (x1 * x2 * (x1 + x2) / 2 - x1 * x2) +
      g * X * C ((x1 + x2) / 2 - x1 * x2) := by
    rw [Sser]
    ring
  rw [e, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C]

end Virasoro.Sphere
