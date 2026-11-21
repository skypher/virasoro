import Virasoro.Sphere.Proofs.Sec3BergmanOde
import Virasoro.Sphere.Proofs.Sec3SaddleA

/-!
# Sphere paper Lemma 3.5, Step 3: the series `F₁` (`sphere/paper.tex` l.935–941)

`F₀(z) = [x⁰](1-z/x)^{-1/2}(1-x)^{-1/2} = ∑ h_n² z^n` and
`F₁(z) = [x⁻¹](1-z/x)^{-1/2}(1-x)^{-1/2} = ∑ h_{n+1} h_n z^{n+1}`, `h_n = [x^n](1-x)^{-1/2}`.
Because `[z^{n+1}] z(1-z)F₀'(z) = h_n²/(4(n+1))`, `F₁ = zF₀ - 2z(1-z)F₀'`, and so
`-½F₁/F₀ = -z/2 + z(1-z)F₀'/F₀`.

Consumer: `Stmt_sub_bergman_zero_mode`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `F₁(z) = ∑_n h_{n+1} h_n z^{n+1}`, the coefficient of `x⁻¹` of
`(1-z/x)^{-1/2}(1-x)^{-1/2}` on `|z| < |x| < 1`. -/
noncomputable def F1ser : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 0 else halfBinom k * halfBinom (k - 1)

/-- `[z^{n+1}] z(1-z)F₀'(z) = h_n²/(4(n+1))` (sphere/paper.tex l.938). -/
theorem coeff_X_one_sub_deriv (n : ℕ) :
    coeff (n + 1) (X * ((1 - X) * derivative ℚ hyp2F1)) =
      halfBinom n ^ 2 / (4 * ((n : ℚ) + 1)) := by
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [coeff_succ_X_mul, sub_mul, one_mul, map_sub, ← theta_apply, coeff_theta, coeff_derivative,
    hyp2F1_eq, coeff_mk, coeff_mk, halfBinom_succ]
  field_simp
  ring

/-- `F₁ = zF₀ - 2z(1-z)F₀'` (sphere/paper.tex l.939). -/
theorem F1ser_eq :
    F1ser = X * hyp2F1 - 2 * (X * ((1 - X) * derivative ℚ hyp2F1)) := by
  ext k
  cases k with
  | zero =>
    rw [F1ser, coeff_mk, if_pos rfl, map_sub, two_mul, map_add]
    simp
  | succ n =>
    have hn1 : ((n : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [F1ser, coeff_mk, if_neg (Nat.succ_ne_zero n), map_sub, two_mul, map_add,
      coeff_X_one_sub_deriv, coeff_succ_X_mul, hyp2F1_eq, coeff_mk, Nat.add_sub_cancel,
      halfBinom_succ]
    field_simp
    ring

/-- `-½ F₁/F₀ = -z/2 + z(1-z)F₀'/F₀` (sphere/paper.tex l.940–941), multiplied by `2F₀`. -/
theorem F1ser_ratio :
    -F1ser = (2 * (X * (1 - X) * derivative ℚ hyp2F1 * hyp2F1⁻¹) - X) * hyp2F1 := by
  have i2 : hyp2F1 * hyp2F1⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hyp2F1_unit
  rw [F1ser_eq]
  linear_combination (-2 * (X * (1 - X) * derivative ℚ hyp2F1)) * i2

end Virasoro.Sphere
