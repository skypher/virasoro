import Virasoro.Sphere.Proofs.Sec3BergmanZeroModeW
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Sphere paper Lemma 3.5, Step 2: `Y(x)` coefficientwise in `z`, and the pole at `x₁ = x₂`
(`sphere/paper.tex` l.914–924)

`Y(x) = x √(1-x) √(1-z/x)` as a series in `z` (the branch `√(x-1) = ±i√(1-x)` only changes `Y`
by a constant factor), with `g(x) Y(x) = 1` and `Y(x)² = -P(x)`.  Coefficientwise
differentiability, boundedness near a point, and the cancellation of the double pole of
`(Y(x₁) + g(x₂) S(x₁,x₂))/(x₁-x₂)²` at `x₁ = x₂` (`S(x,x) = Y(x)²`, `∂₁S(x,x) = Y(x)Y'(x)`,
here through `S² - P₁P₂ = (x₁-x₂)²(x₁x₂-z)²/4`).

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

/-- If `H(x) F(x) = R(x)` near `c`, the coefficients of `F`, `R` are continuous at `c` and
`[z⁰] F(c) ≠ 0`, then every coefficient of `H(x)` has a limit as `x → c`. -/
theorem tendsto_coeff_of_mul {F H R : ℂ → PowerSeries ℂ} {c : ℂ} (hF : CoeffCont F c)
    (hR : CoeffCont R c) (h0 : coeff 0 (F c) ≠ 0)
    (hmul : ∀ᶠ x in 𝓝[≠] c, H x * F x = R x) (j : ℕ) :
    ∃ L : ℂ, Tendsto (fun x => coeff j (H x)) (𝓝[≠] c) (𝓝 L) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    choose! L hL using ih
    have hF' : ∀ k, Tendsto (fun x => coeff k (F x)) (𝓝[≠] c) (𝓝 (coeff k (F c))) :=
      fun k => (hF k).tendsto.mono_left nhdsWithin_le_nhds
    have hR' : Tendsto (fun x => coeff j (R x)) (𝓝[≠] c) (𝓝 (coeff j (R c))) :=
      (hR j).tendsto.mono_left nhdsWithin_le_nhds
    have hF0 : ∀ᶠ x in 𝓝[≠] c, coeff 0 (F x) ≠ 0 := (hF' 0).eventually_ne h0
    refine ⟨(coeff j (R c) - ∑ k ∈ range j, L k * coeff (j - k) (F c)) / coeff 0 (F c), ?_⟩
    have ht : Tendsto (fun x => (coeff j (R x) - ∑ k ∈ range j,
        coeff k (H x) * coeff (j - k) (F x)) / coeff 0 (F x)) (𝓝[≠] c)
        (𝓝 ((coeff j (R c) - ∑ k ∈ range j, L k * coeff (j - k) (F c)) / coeff 0 (F c))) :=
      (hR'.sub (tendsto_finsetSum _ fun k hk =>
        (hL k (Finset.mem_range.1 hk)).mul (hF' (j - k)))).div (hF' 0) h0
    refine ht.congr' ?_
    filter_upwards [hmul, hF0] with x hx hx0
    have e := congrArg (coeff j) hx
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.sub_self] at e
    rw [div_eq_iff hx0]
    linear_combination (-1 : ℂ) * e

/-- The double pole at `x₁ = x₂` cancels (l.918–924): for `x ≠ x₂`,
`((Y(x) + g(x₂) S(x,x₂))/(x-x₂)²) · 4(Y(x)Y(x₂) - S(x,x₂)) = -g(x₂)(x x₂ - z)²`. -/
theorem pole_identity {x x2 : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) (h20 : x2 ≠ 0) (h21 : ‖x2‖ < 1)
    (hne : x ≠ x2) :
    (Yser x + gser x2 * Sser x x2) * C (((x - x2) ^ 2)⁻¹) *
        (C 4 * (Yser x * Yser x2 - Sser x x2)) =
      -(gser x2 * (C x * C x2 - X) ^ 2) := by
  have hh1 := gser_mul_Yser h20 h21
  have hh2 := Yser_sq h0 h1
  have hh3 := Yser_sq h20 h21
  have hh4 := Sser_sq x x2
  have hh5 : (C x - C x2) ^ 2 * C (((x - x2) ^ 2)⁻¹) = (1 : PowerSeries ℂ) := by
    rw [← map_sub, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero 2 (sub_ne_zero.2 hne)),
      map_one]
  have h4 : (C (4 : ℂ) : PowerSeries ℂ) = 4 := map_ofNat _ 4
  rw [h4]
  linear_combination (-(gser x2 * (C x * C x2 - X) ^ 2)) * hh5 -
    gser x2 * C (((x - x2) ^ 2)⁻¹) * hh4 +
    4 * C (((x - x2) ^ 2)⁻¹) * (Yser x * Sser x x2 + Pser x * Yser x2) * hh1 +
    4 * C (((x - x2) ^ 2)⁻¹) * Yser x2 * hh2 -
    4 * C (((x - x2) ^ 2)⁻¹) * Pser x * gser x2 * hh3

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
