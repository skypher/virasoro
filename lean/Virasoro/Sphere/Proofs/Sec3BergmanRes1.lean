import Virasoro.Sphere.Proofs.Sec3BergmanCont

/-!
# Sphere paper Lemma 3.5, Step 3: the residues inside `|x| = r` (`sphere/paper.tex` l.950–963)

Coefficientwise in `z`, `g(x)² = -1/(x(x-1)(x-z)) = (x²(1-x))⁻¹ ∑_k z^k x^{-k}` and
`g(x)⁴ = (x²(1-x))⁻² ∑_k (k+1) z^k x^{-k}`.  The circle integrals of `x [z^k] g(x)²` and of
`x^{e+1} [z^k] g(x)⁴` over `|x| = r < 1` are `2πi` times a coefficient of the expansion of
`(1-x)⁻¹` or `(1-x)⁻²` at `x = 0`: the residues at `x = 0, z` at each order in `z`.

Consumer: `Stmt_sub_bergman_residue`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Real

/-- `(1 - a z)⁻¹ = ∑_k a^k z^k`. -/
noncomputable def Eser (a : ℂ) : PowerSeries ℂ := PowerSeries.mk fun k => a ^ k

theorem Eser_mul (a : ℂ) : Eser a * (1 - C a * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc]
  cases n with
  | zero => simp [Eser]
  | succ n =>
    rw [coeff_succ_mul_X, PowerSeries.coeff_mul_C, Eser, coeff_mk, coeff_mk, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero n)]
    ring

theorem invSqrtZ_sq_eq (y : ℂ) : invSqrtZ y ^ 2 = Eser y⁻¹ := by
  have h1 := invSqrtZ_sq y
  have h2 := Eser_mul y⁻¹
  calc invSqrtZ y ^ 2 = invSqrtZ y ^ 2 * (Eser y⁻¹ * (1 - C y⁻¹ * X)) := by rw [h2, mul_one]
    _ = (invSqrtZ y ^ 2 * (1 - C y⁻¹ * X)) * Eser y⁻¹ := by ring
    _ = Eser y⁻¹ := by rw [h1, one_mul]

theorem gser_sq (y : ℂ) : gser y ^ 2 = C ((y ^ 2 * (1 - y))⁻¹) * Eser y⁻¹ := by
  rw [gser, mul_pow, invSqrtZ_sq_eq, ← map_pow, inv_pow, mul_pow, cpow_half_sq]

theorem coeff_gser_sq (y : ℂ) (k : ℕ) :
    coeff k (gser y ^ 2) = (y ^ 2 * (1 - y))⁻¹ * y⁻¹ ^ k := by
  rw [gser_sq, coeff_C_mul, Eser, coeff_mk]

theorem Eser_sq (a : ℂ) : Eser a ^ 2 = PowerSeries.mk fun k => ((k : ℂ) + 1) * a ^ k := by
  ext k
  rw [pow_two, coeff_mul, coeff_mk]
  simp only [Eser, coeff_mk]
  rw [Finset.sum_congr rfl (fun p hp => by
      rw [← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hp] :
        ∀ p ∈ antidiagonal k, a ^ p.1 * a ^ p.2 = a ^ k),
    Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  push_cast
  ring

theorem coeff_gser_four (y : ℂ) (k : ℕ) :
    coeff k (gser y ^ 4) = ((y ^ 2 * (1 - y))⁻¹) ^ 2 * (((k : ℂ) + 1) * y⁻¹ ^ k) := by
  rw [show gser y ^ 4 = (gser y ^ 2) ^ 2 by ring, gser_sq, mul_pow, Eser_sq, ← map_pow,
    coeff_C_mul, coeff_mk]

theorem tsum_succ_mul_geom {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' i : ℕ, ((i : ℂ) + 1) * x ^ i = ((1 - x) ^ 2)⁻¹ := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hx).add (hasSum_geometric_of_norm_lt_one hx)
  have hne : (1 - x) ≠ 0 := sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt hx))
  rw [show (fun i : ℕ => ((i : ℂ) + 1) * x ^ i) = fun i : ℕ => (i : ℂ) * x ^ i + x ^ i from
    funext fun i => by ring, h.tsum_eq]
  field_simp
  ring

theorem summable_succ_mul_geom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (κ : ℂ) :
    Summable fun i : ℕ => ‖κ * ((i : ℂ) + 1)‖ * r ^ i := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have h := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.add
    (summable_geometric_of_lt_one h0 h1)).mul_left ‖κ‖
  refine h.congr fun i => ?_
  rw [norm_mul, show ((i : ℂ) + 1) = ((i + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
  push_cast
  ring

variable {r : ℝ}

theorem sphere_ne_zero (hr : 0 < r) {x : ℂ} (hx : x ∈ Metric.sphere (0 : ℂ) r) : x ≠ 0 := by
  intro h0
  have hz' : ‖x‖ = r := by simpa using hx
  rw [h0, norm_zero] at hz'
  exact hr.ne hz'

theorem sphere_norm {x : ℂ} (hx : x ∈ Metric.sphere (0 : ℂ) r) : ‖x‖ = r := by simpa using hx

/-- `∮ x [z^k] g(x)² dx = 2πi`: the residue of `x^{-k-1}(1-x)⁻¹` at `x = 0`. -/
theorem int_g2 (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (∮ x in C(0, r), x * coeff k (gser x ^ 2)) = 2 * π * Complex.I := by
  have hc : (∮ x in C(0, r), x * coeff k (gser x ^ 2)) =
      ∮ x in C(0, r), x ^ (-(k : ℤ) - 1) * ∑' i : ℕ, (1 : ℂ) * x ^ i := by
    refine circleIntegral.integral_congr hr0.le fun x hx => ?_
    have hx0 := sphere_ne_zero hr0 hx
    have hx1 : ‖x‖ < 1 := by rw [sphere_norm hx]; exact hr1
    have hne : (1 - x) ≠ 0 := sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt hx1))
    simp only [one_mul]
    rw [coeff_gser_sq, tsum_geometric_of_norm_lt_one hx1,
      show (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    simp only [inv_pow]
    field_simp
    ring
  have hs : Summable fun i : ℕ => ‖(1 : ℂ)‖ * r ^ i := by
    simpa using summable_geometric_of_lt_one hr0.le hr1
  rw [hc, circleIntegral_zpow_mul_tsum (fun _ => 1) _ hr0 hs, tsum_eq_single k]
  · rw [if_pos (by ring), one_mul]
  · intro i hi
    rw [if_neg]
    intro h
    exact hi (by omega)

/-- `∮ x^{e+1} [z^k] g(x)⁴ dx` as `2πi` times a coefficient of `(k+1)(1-x)⁻²`. -/
theorem int_g4 (hr0 : 0 < r) (hr1 : r < 1) (k e : ℕ) :
    (∮ x in C(0, r), x * (x ^ e * coeff k (gser x ^ 4))) =
      ∑' i : ℕ, if ((e : ℤ) - 3 - k) + (i : ℤ) = -1 then
        (((k : ℂ) + 1) * ((i : ℂ) + 1)) * (2 * π * Complex.I) else 0 := by
  have hc : (∮ x in C(0, r), x * (x ^ e * coeff k (gser x ^ 4))) =
      ∮ x in C(0, r), x ^ ((e : ℤ) - 3 - k) *
        ∑' i : ℕ, (((k : ℂ) + 1) * ((i : ℂ) + 1)) * x ^ i := by
    refine circleIntegral.integral_congr hr0.le fun x hx => ?_
    have hx0 := sphere_ne_zero hr0 hx
    have hx1 : ‖x‖ < 1 := by rw [sphere_norm hx]; exact hr1
    have hne : (1 - x) ≠ 0 := sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt hx1))
    simp only [mul_assoc]
    rw [tsum_mul_left, tsum_succ_mul_geom hx1, coeff_gser_four, zpow_sub₀ hx0, zpow_sub₀ hx0,
      zpow_natCast, zpow_natCast, zpow_ofNat]
    simp only [inv_pow]
    field_simp
  rw [hc, circleIntegral_zpow_mul_tsum _ _ hr0 (summable_succ_mul_geom hr0.le hr1 _)]

theorem int_g4_four (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (∮ x in C(0, r), x * (x ^ 4 * coeff k (gser x ^ 4))) =
      2 * π * Complex.I * (((k : ℂ) + 1) * ((k - 1 : ℕ) : ℂ)) := by
  rw [int_g4 hr0 hr1]
  by_cases hk : 2 ≤ k
  · rw [tsum_eq_single (k - 2)]
    · rw [if_pos (by push_cast [Nat.cast_sub hk]; ring)]
      have e1 : (((k - 2 : ℕ) : ℂ)) + 1 = ((k - 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub hk, Nat.cast_sub (by omega : 1 ≤ k)]
        push_cast
        ring
      rw [e1]
      ring
    · intro i hi
      rw [if_neg]
      intro h
      exact hi (by omega)
  · have hk1 : k - 1 = 0 := by omega
    rw [hk1, Nat.cast_zero, mul_zero, mul_zero]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [if_neg]
    intro h
    push_cast at h
    omega

theorem int_g4_two (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (∮ x in C(0, r), x * (x ^ 2 * coeff k (gser x ^ 4))) =
      2 * π * Complex.I * (((k : ℂ) + 1) * ((k : ℂ) + 1)) := by
  rw [int_g4 hr0 hr1, tsum_eq_single k]
  · rw [if_pos (by push_cast; ring)]
    ring
  · intro i hi
    rw [if_neg]
    intro h
    exact hi (by push_cast at h; omega)

theorem int_g4_zero (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (∮ x in C(0, r), x * (x ^ 0 * coeff k (gser x ^ 4))) =
      2 * π * Complex.I * (((k : ℂ) + 1) * ((k : ℂ) + 3)) := by
  rw [int_g4 hr0 hr1, tsum_eq_single (k + 2)]
  · rw [if_pos (by push_cast; ring)]
    push_cast
    ring
  · intro i hi
    rw [if_neg]
    intro h
    exact hi (by push_cast at h; omega)

end Virasoro.Sphere
