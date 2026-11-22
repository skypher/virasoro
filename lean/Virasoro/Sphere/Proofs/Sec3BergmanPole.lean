import Virasoro.Sphere.Proofs.Sec3BergmanLiouTools
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Sphere paper Lemma 3.5, Step 2: the double pole at `x₁ = x₂` (proof of Lemma 3.5, Step 2)

The paper matches the pole of `[z^j](Y(x₁)W(x₁,x₂))` at `x₁ = x₂` with that of
`[z^j](Y(x₁)S(x₁,x₂)/(Y(x₂)(x₁-x₂)²))` through `S(x,x) = Y(x)²` and `∂_{x₁}S(x,x) = Y(x)Y'(x)`.
Here (with the branch `Y = x√(1-x)√(1-z/x)`, so `Y² = -P` and `S(x,x) = P(x)`, `g = 1/Y`) the
numerator `N(x) = [z^j](Y(x) + g(x₂)S(x,x₂))` is holomorphic near `x₂`, `N(x₂) = 0` by
`S(x,x) = P = -Y²`, and `N'(x₂) = 0` by `∂₁S(x,x) = ½P'(x) = -Y(x)Y'(x)`.  Two divided
differences then show that `N(x)/(x-x₂)²` is bounded near `x₂` (`bddNear_pole`).

The derivative of a series coefficientwise in `x` is `dser`; it obeys the product rule
(`dser_mul`).

Consumer: `sub_bergman_const_of_patches` (`Sec3BergmanLiouConst.lean`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology

/-- The coefficientwise derivative in `y` at `x` of a family of series `F(y)`. -/
noncomputable def dser (F : ℂ → PowerSeries ℂ) (x : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun a => deriv (fun y => coeff a (F y)) x

theorem coeff_dser (F : ℂ → PowerSeries ℂ) (x : ℂ) (a : ℕ) :
    coeff a (dser F x) = deriv (fun y => coeff a (F y)) x := by
  rw [dser, coeff_mk]

theorem dser_add {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffDiff F x) (hG : CoeffDiff G x) :
    dser (fun y => F y + G y) x = dser F x + dser G x := by
  ext a
  simp only [coeff_dser, map_add]
  exact deriv_add (hF a) (hG a)

theorem dser_neg (F : ℂ → PowerSeries ℂ) (x : ℂ) :
    dser (fun y => -F y) x = -dser F x := by
  ext a
  simp only [coeff_dser, map_neg]
  exact deriv.neg

theorem dser_mul {F G : ℂ → PowerSeries ℂ} {x : ℂ} (hF : CoeffDiff F x) (hG : CoeffDiff G x) :
    dser (fun y => F y * G y) x = dser F x * G x + F x * dser G x := by
  ext a
  simp only [coeff_dser, map_add, coeff_mul]
  rw [deriv_fun_sum fun p _ => (hF p.1).mul (hG p.2), ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [deriv_fun_mul (hF p.1) (hG p.2)]

theorem dser_const (f : PowerSeries ℂ) (x : ℂ) : dser (fun _ => f) x = 0 := by
  ext a
  simp [coeff_dser]

theorem dser_C {φ : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ φ x) :
    dser (fun y => C (φ y)) x = C (deriv φ x) := by
  ext a
  rw [coeff_dser, coeff_C]
  simp only [coeff_C]
  split_ifs
  · rfl
  · exact deriv_const _ _

theorem dser_congr {F G : ℂ → PowerSeries ℂ} {x : ℂ} (h : ∀ᶠ y in 𝓝 x, F y = G y) :
    dser F x = dser G x := by
  ext a
  rw [coeff_dser, coeff_dser]
  exact Filter.EventuallyEq.deriv_eq (h.mono fun y hy => by simp only [hy])

/-- `P'(x) = (3x² - 2x) - (2x - 1)z`. -/
theorem dser_Pser (x : ℂ) :
    dser Pser x = C (3 * x ^ 2 - 2 * x) - C (2 * x - 1) * X := by
  have hP : Pser = fun y => C (y ^ 2 * (y - 1)) + C (-(y * (y - 1))) * X := by
    funext y
    rw [Pser, map_neg, neg_mul, sub_eq_add_neg]
  rw [hP, dser_add (CoeffDiff.C (by fun_prop))
      ((CoeffDiff.C (by fun_prop)).mul (CoeffDiff.const X x)),
    dser_C (by fun_prop),
    dser_mul (CoeffDiff.C (by fun_prop)) (CoeffDiff.const X x), dser_C (by fun_prop),
    dser_const]
  have d1 : deriv (fun y : ℂ => y ^ 2 * (y - 1)) x = 3 * x ^ 2 - 2 * x := by
    have : (fun y : ℂ => y ^ 2 * (y - 1)) = fun y => y ^ 3 - y ^ 2 := by funext y; ring
    have h : HasDerivAt (fun y : ℂ => y ^ 3 - y ^ 2)
        (((3 : ℕ) : ℂ) * x ^ (3 - 1) - ((2 : ℕ) : ℂ) * x ^ (2 - 1)) x :=
      (hasDerivAt_pow 3 x).sub (hasDerivAt_pow 2 x)
    rw [this, h.deriv]
    norm_num
  have d2 : deriv (fun y : ℂ => -(y * (y - 1))) x = -(2 * x - 1) := by
    have : (fun y : ℂ => -(y * (y - 1))) = fun y => y - y ^ 2 := by funext y; ring
    have h : HasDerivAt (fun y : ℂ => y - y ^ 2) (1 - ((2 : ℕ) : ℂ) * x ^ (2 - 1)) x :=
      (hasDerivAt_id x).sub (hasDerivAt_pow 2 x)
    rw [this, h.deriv]
    norm_num
  rw [d1, d2, map_neg, mul_zero, add_zero, neg_mul, ← sub_eq_add_neg]

/-- `∂_{x₁}S(x₁,x₂)` at `x₁ = x₂ = x` is `½P'(x)` (the paper's `∂₁S(x,x) = YY'`). -/
theorem dser_Sser_diag (x : ℂ) :
    dser (fun y => Sser y x) x = C (1 / 2) * dser Pser x := by
  unfold Sser
  rw [dser_add (CoeffDiff.C (by fun_prop))
      ((CoeffDiff.C (by fun_prop)).mul (CoeffDiff.const X x)),
    dser_C (by fun_prop),
    dser_mul (CoeffDiff.C (by fun_prop)) (CoeffDiff.const X x), dser_C (by fun_prop),
    dser_const, dser_Pser]
  have d1 : deriv (fun y : ℂ => y * x * (y + x) / 2 - y * x) x = 3 / 2 * x ^ 2 - x := by
    have : (fun y : ℂ => y * x * (y + x) / 2 - y * x) =
        fun y => x / 2 * y ^ 2 + (x ^ 2 / 2 - x) * y := by funext y; ring
    have h : HasDerivAt (fun y : ℂ => x / 2 * y ^ 2 + (x ^ 2 / 2 - x) * y)
        (x / 2 * (((2 : ℕ) : ℂ) * x ^ (2 - 1)) + (x ^ 2 / 2 - x) * 1) x :=
      ((hasDerivAt_pow 2 x).const_mul (x / 2)).add ((hasDerivAt_id x).const_mul (x ^ 2 / 2 - x))
    rw [this, h.deriv]
    norm_num
    ring
  have d2 : deriv (fun y : ℂ => (y + x) / 2 - y * x) x = 1 / 2 - x := by
    have : (fun y : ℂ => (y + x) / 2 - y * x) = fun y => (1 / 2 - x) * y + x / 2 := by
      funext y; ring
    have h : HasDerivAt (fun y : ℂ => (1 / 2 - x) * y + x / 2) ((1 / 2 - x) * 1) x :=
      ((hasDerivAt_id x).const_mul (1 / 2 - x)).add_const (x / 2)
    rw [this, h.deriv, mul_one]
  rw [d1, d2, mul_zero, add_zero, mul_sub, ← mul_assoc, ← map_mul, ← map_mul,
    show (1 / 2 : ℂ) * (3 * x ^ 2 - 2 * x) = 3 / 2 * x ^ 2 - x by ring,
    show (1 / 2 : ℂ) * (2 * x - 1) = -(1 / 2 - x) by ring, map_neg, neg_mul, sub_neg_eq_add]

/-- `2 Y(x) Y'(x) = -P'(x)`, from `Y² = -P` near `x` (the paper's `S(x,x) = Y(x)²`, differentiated). -/
theorem Yser_dser {x : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) :
    C 2 * Yser x * dser Yser x = -dser Pser x := by
  have hopen : IsOpen {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hev : ∀ᶠ y in 𝓝 x, Yser y * Yser y = -Pser y := by
    filter_upwards [hopen.mem_nhds ⟨norm_pos_iff.2 h0, h1⟩] with y hy
    rw [← pow_two, Yser_sq (norm_pos_iff.1 hy.1) hy.2]
  have hY := coeffDiff_Yser h0 h1
  have e := dser_congr hev
  rw [dser_mul hY hY, dser_neg] at e
  rw [← e, map_ofNat]
  ring

/-- `N'(x₂) = 0` as a series: `Y'(x₂) + g(x₂) ∂₁S(x₂,x₂) = 0`. -/
theorem dser_pole_num {x2 : ℂ} (h0 : x2 ≠ 0) (h1 : ‖x2‖ < 1) :
    dser (fun y => Yser y + gser x2 * Sser y x2) x2 = 0 := by
  have hY := coeffDiff_Yser h0 h1
  rw [dser_add hY ((CoeffDiff.const (gser x2) x2).mul (coeffDiff_Sser x2 x2)),
    dser_mul (CoeffDiff.const (gser x2) x2) (coeffDiff_Sser x2 x2), dser_const, dser_Sser_diag]
  have hYd := Yser_dser h0 h1
  have hgY := gser_mul_Yser h0 h1
  have h2 : (C (1 / 2 : ℂ) : PowerSeries ℂ) * C 2 = 1 := by
    rw [← map_mul]; norm_num
  linear_combination (gser x2 * C (1 / 2 : ℂ)) * hYd -
    (C (1 / 2 : ℂ) * C 2 * dser Yser x2) * hgY - dser Yser x2 * h2

/-- `N(x₂) = 0` as a series: `Y(x₂) + g(x₂) S(x₂,x₂) = 0`. -/
theorem pole_num_zero {x2 : ℂ} (h0 : x2 ≠ 0) (h1 : ‖x2‖ < 1) :
    Yser x2 + gser x2 * Sser x2 x2 = 0 := by
  rw [Sser_diag]
  have hgY := gser_mul_Yser h0 h1
  have hY2 := Yser_sq h0 h1
  linear_combination (gser x2) * hY2 - Yser x2 * hgY

/-- A function holomorphic near `c` with a zero of order at least two at `c`, divided by
`(x-c)²`, is bounded near `c`. -/
theorem bddNear_of_double_zero {N : ℂ → ℂ} {c : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 c)
    (hN : DifferentiableOn ℂ N s) (h0 : N c = 0) (h1 : deriv N c = 0) :
    BddNear (fun x => N x * ((x - c) ^ 2)⁻¹) c := by
  have hD1 : DifferentiableOn ℂ (dslope N c) s := (Complex.differentiableOn_dslope hs).2 hN
  have hD2 : DifferentiableOn ℂ (dslope (dslope N c) c) s :=
    (Complex.differentiableOn_dslope hs).2 hD1
  have hcont : ContinuousAt (dslope (dslope N c) c) c :=
    (hD2.differentiableAt hs).continuousAt
  refine (BddNear.of_continuousAt hcont).congr ⟨1, one_pos, fun x hx _ => ?_⟩
  have hxc : x - c ≠ 0 := sub_ne_zero.2 hx
  rw [dslope_of_ne _ hx, slope_def_field, dslope_of_ne _ hx, slope_def_field, dslope_same, h1, h0]
  field_simp
  ring

/-- The pole at `x₁ = x₂` of `[z^j]((Y(x) + g(x₂)S(x,x₂))/(x-x₂)²)` is removable: the numerator
vanishes to second order at `x = x₂`. -/
theorem bddNear_pole {x2 : ℂ} (h20 : x2 ≠ 0) (h21 : ‖x2‖ < 1) (j : ℕ) :
    BddNear (fun x => coeff j ((Yser x + gser x2 * Sser x x2) * C (((x - x2) ^ 2)⁻¹))) x2 := by
  have hopen : IsOpen {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hs : {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} ∈ 𝓝 x2 := hopen.mem_nhds ⟨norm_pos_iff.2 h20, h21⟩
  have hD : ∀ y ∈ {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1},
      CoeffDiff (fun y => Yser y + gser x2 * Sser y x2) y := fun y hy =>
    (coeffDiff_Yser (norm_pos_iff.1 hy.1) hy.2).add
      ((CoeffDiff.const (gser x2) y).mul (coeffDiff_Sser y x2))
  have hN : DifferentiableOn ℂ (fun y => coeff j (Yser y + gser x2 * Sser y x2))
      {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} := fun y hy => (hD y hy j).differentiableWithinAt
  have h0 : coeff j (Yser x2 + gser x2 * Sser x2 x2) = 0 := by
    rw [pole_num_zero h20 h21, map_zero]
  have h1 : deriv (fun y => coeff j (Yser y + gser x2 * Sser y x2)) x2 = 0 := by
    have e := coeff_dser (fun y => Yser y + gser x2 * Sser y x2) x2 j
    rw [dser_pole_num h20 h21, map_zero] at e
    exact e.symm
  refine (bddNear_of_double_zero hs hN h0 h1).congr ⟨1, one_pos, fun x _ _ => ?_⟩
  rw [PowerSeries.coeff_mul_C]

end Virasoro.Sphere
