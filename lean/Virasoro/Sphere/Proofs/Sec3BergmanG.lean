import Virasoro.Sphere.Proofs.Sec3BergmanSteps

/-!
# Sphere paper Lemma 3.5, Step 3: the formula for `W_no` off the diagonal (`sphere/paper.tex` l.914–929, l.946–949)

With `g(y) = (1-z/y)^{-1/2}/(y√(1-y))` (so that `g(y)² P(y) = -1`, `P(y) = y(y-1)(y-z)`, and
`1/(Y(x₁)Y(x₂)) = -g(x₁)g(x₂)`), the formula of Step 2 gives for `x₁ ≠ x₂`
`(g₁g₂S - 1)(W_no + 2C g₁g₂) = -(S² - P₁P₂) g₁²g₂²/(x₁-x₂)²`, and
`S(x₁,x₂)² - P(x₁)P(x₂) = ¼ (x₁-x₂)² (x₁x₂-z)²`; on the diagonal this is the polynomial identity
`4P(x)(-2x+1+z) + P'(x)² = (x²-z)²` of l.946.

Consumer: the coincidence limit in `Stmt_sub_bergman_residue`.
-/

namespace Virasoro.Sphere

open PowerSeries

/-- `g(y) = (1-z/y)^{-1/2}/(y√(1-y))`, coefficientwise in `z`. -/
noncomputable def gser (y : ℂ) : PowerSeries ℂ :=
  C ((y * (1 - y) ^ (1 / 2 : ℂ))⁻¹) * invSqrtZ y

/-- `P(y) = y(y-1)(y-z)` as a polynomial in `z` (sphere/paper.tex l.946). -/
noncomputable def Pser (y : ℂ) : PowerSeries ℂ := C (y ^ 2 * (y - 1)) - C (y * (y - 1)) * X

/-- `W_no(x₁,x₂)` as a power series in `z`. -/
noncomputable def Wnos (x1 x2 : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun j => ∑' mn : ℕ × ℕ, WnoTerm j x1 x2 mn.1 mn.2

theorem Wser_eq (x1 x2 : ℂ) : Wser x1 x2 = C (((x1 - x2) ^ 2)⁻¹) + Wnos x1 x2 := by
  ext j
  rw [Wser, Wnos, map_add, coeff_mk, coeff_mk, coeff_C]

theorem YYinv_eq (x1 x2 : ℂ) : YYinv x1 x2 = -(gser x1 * gser x2) := by
  rw [YYinv, gser, gser]
  have h : (-(x1 * x2 * (1 - x1) ^ (1 / 2 : ℂ) * (1 - x2) ^ (1 / 2 : ℂ))⁻¹ : ℂ) =
      -((x1 * (1 - x1) ^ (1 / 2 : ℂ))⁻¹ * (x2 * (1 - x2) ^ (1 / 2 : ℂ))⁻¹) := by
    rw [← mul_inv]
    ring_nf
  rw [h, map_neg, map_mul]
  ring

theorem invSqrtZ_eq (y : ℂ) : invSqrtZ y = rescale y⁻¹ (hser.map (algebraMap ℚ ℂ)) := by
  ext j
  rw [invSqrtZ, coeff_mk, coeff_rescale, coeff_map, hser, coeff_mk, zpow_neg, zpow_natCast,
    inv_pow, eq_ratCast, mul_comm]

/-- `((1-z/y)^{-1/2})² (1 - z/y) = 1`. -/
theorem invSqrtZ_sq (y : ℂ) : invSqrtZ y ^ 2 * (1 - C y⁻¹ * X) = 1 := by
  have h := congrArg (fun f => rescale y⁻¹ (f.map (algebraMap ℚ ℂ))) hser_sq
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X, rescale_X] at h
  rw [invSqrtZ_eq]
  exact h

theorem cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  have := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  rwa [show (((2 : ℕ) : ℂ))⁻¹ = (1 / 2 : ℂ) by norm_num] at this

/-- `g(y)² P(y) = -1`: `g = ±i/Y`. -/
theorem gser_sq_mul_Pser {y : ℂ} (hy0 : y ≠ 0) (hy1 : y ≠ 1) : gser y ^ 2 * Pser y = -1 := by
  have h1y : (1 - y) ≠ 0 := sub_ne_zero.2 (Ne.symm hy1)
  have e : (C (y * (y - 1)) : PowerSeries ℂ) = C (y ^ 2 * (y - 1)) * C y⁻¹ := by
    rw [← map_mul]
    congr 1
    field_simp
  have hP : Pser y = C (y ^ 2 * (y - 1)) * (1 - C y⁻¹ * X) := by
    rw [Pser, e]
    ring
  have hs := cpow_half_sq (1 - y)
  have hc : ((y * (1 - y) ^ (1 / 2 : ℂ))⁻¹) ^ 2 * (y ^ 2 * (y - 1)) = -1 := by
    rw [inv_pow, mul_pow, hs]
    field_simp
    ring
  calc gser y ^ 2 * Pser y
      = (C ((y * (1 - y) ^ (1 / 2 : ℂ))⁻¹) ^ 2 * C (y ^ 2 * (y - 1))) *
          (invSqrtZ y ^ 2 * (1 - C y⁻¹ * X)) := by
        rw [hP, gser, mul_pow]
        ring
    _ = -1 := by rw [invSqrtZ_sq, mul_one, ← map_pow, ← map_mul, hc, map_neg, map_one]

theorem alg_Q {R : Type*} [CommRing R] (u v w S P1 P2 : R)
    (hS : 2 * S = u * v * (u + v) - 2 * (1 + w) * (u * v) + w * (u + v))
    (hP1 : P1 = u * (u - 1) * (u - w)) (hP2 : P2 = v * (v - 1) * (v - w)) :
    4 * (S ^ 2 - P1 * P2) = (u - v) ^ 2 * (u * v - w) ^ 2 := by
  subst hP1 hP2
  linear_combination (2 * S + (u * v * (u + v) - 2 * (1 + w) * (u * v) + w * (u + v))) * hS

theorem two_mul_Sser (x1 x2 : ℂ) :
    2 * Sser x1 x2 =
      C x1 * C x2 * (C x1 + C x2) - 2 * (1 + X) * (C x1 * C x2) + X * (C x1 + C x2) := by
  have h2 : (2 : PowerSeries ℂ) = C 2 := (map_ofNat C 2).symm
  have e1 : (C x1 * C x2 * (C x1 + C x2) - 2 * (C x1 * C x2) : PowerSeries ℂ) =
      2 * C (x1 * x2 * (x1 + x2) / 2 - x1 * x2) := by
    rw [h2]
    simp only [← map_mul, ← map_add, ← map_sub]
    congr 1
    ring
  have e2 : (C x1 + C x2 - 2 * (C x1 * C x2) : PowerSeries ℂ) =
      2 * C ((x1 + x2) / 2 - x1 * x2) := by
    rw [h2]
    simp only [← map_mul, ← map_add, ← map_sub]
    congr 1
    ring
  rw [Sser]
  linear_combination -e1 - X * e2

theorem Pser_eq (y : ℂ) : Pser y = C y * (C y - 1) * (C y - X) := by
  rw [Pser]
  simp only [map_mul, map_pow, map_sub, map_one]
  ring

/-- `S(x₁,x₂)² - P(x₁)P(x₂) = ¼ (x₁-x₂)² (x₁x₂-z)²`. -/
theorem Sser_sq (x1 x2 : ℂ) :
    4 * (Sser x1 x2 ^ 2 - Pser x1 * Pser x2) = (C x1 - C x2) ^ 2 * (C x1 * C x2 - X) ^ 2 :=
  alg_Q _ _ _ _ _ _ (two_mul_Sser x1 x2) (Pser_eq x1) (Pser_eq x2)

theorem ne_one_of_norm_lt {x : ℂ} (h : ‖x‖ < 1) : x ≠ 1 := by
  rintro rfl
  rw [norm_one] at h
  exact lt_irrefl _ h

/-- The formula of Step 2 with the double pole removed, for `x₁ ≠ x₂`:
`4 (g₁g₂S - 1)(W_no + 2C g₁g₂) = -(x₁x₂-z)² g₁² g₂²`. -/
theorem offdiag {Cz : PowerSeries ℂ} (hC : IsWFormula Cz) {x1 x2 : ℂ} (h1 : 0 < ‖x1‖)
    (h1' : ‖x1‖ < 1) (h2 : 0 < ‖x2‖) (h2' : ‖x2‖ < 1) (hne : x1 ≠ x2) :
    4 * ((gser x1 * gser x2 * Sser x1 x2 - 1) *
        (Wnos x1 x2 + 2 * Cz * (gser x1 * gser x2))) =
      -((C x1 * C x2 - X) ^ 2 * gser x1 ^ 2 * gser x2 ^ 2) := by
  have hW := (hC x1 x2 h1 h1' h2 h2' hne).2
  rw [Wser_eq, YYinv_eq] at hW
  have hF1 := gser_sq_mul_Pser (norm_pos_iff.1 h1) (ne_one_of_norm_lt h1')
  have hF2 := gser_sq_mul_Pser (norm_pos_iff.1 h2) (ne_one_of_norm_lt h2')
  have hQ := Sser_sq x1 x2
  have hd : C (((x1 - x2) ^ 2)⁻¹) * (C x1 - C x2) ^ 2 = 1 := by
    rw [← map_sub, ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero 2 (sub_ne_zero.2 hne)),
      map_one]
  linear_combination (4 * (gser x1 * gser x2 * Sser x1 x2 - 1)) * hW -
    (C (((x1 - x2) ^ 2)⁻¹) * gser x1 ^ 2 * gser x2 ^ 2) * hQ -
    (4 * C (((x1 - x2) ^ 2)⁻¹) * gser x2 ^ 2 * Pser x2) * hF1 +
    (4 * C (((x1 - x2) ^ 2)⁻¹)) * hF2 -
    (gser x1 ^ 2 * gser x2 ^ 2 * (C x1 * C x2 - X) ^ 2) * hd

end Virasoro.Sphere
