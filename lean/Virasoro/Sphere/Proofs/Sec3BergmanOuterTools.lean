import Virasoro.Sphere.Proofs.Sec3BergmanEval

/-!
# Sphere paper Lemma 3.5, Step 2, outer patch: the functions `P_n(1/x₁)`
(`sphere/paper.tex` l.906–913)

`x^{-n} R_n(x) = -2 P_n(1/x)` is a polynomial in `1/x`; on `0 < |x| < 1`,
`x √(1-x) · (n x^{-n-1} - x^{-1} ∑_m B_{m,n} x^m) = ½ x^{-n} R_n(x)`, which is
`x₁√(x₁-1) · (-x₁⁻² f_n(1/x₁)) = i P_n(1/x₁)` up to the branch constant.

Consumer: `sub_bergman_outer`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `x^{-n} R_n(x) = ∑_{k ≤ n} ρ_{n,k} x^{-(n-k)}`, a polynomial in `1/x`. -/
noncomputable def Rinv (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), ((coeff k (Rrev n) : ℚ) : ℂ) * x⁻¹ ^ (n - k)

theorem Rinv_eq (n : ℕ) {x : ℂ} (hx : x ≠ 0) : Rinv n x = x⁻¹ ^ n * Rf n x := by
  rw [Rinv, Rf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by have := Finset.mem_range.1 hk; omega
  have e1 : x⁻¹ ^ n = x⁻¹ ^ (n - k) * x⁻¹ ^ k := by rw [← pow_add, Nat.sub_add_cancel hkn]
  have e2 : x⁻¹ ^ k * x ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  rw [e1]
  linear_combination (-(((coeff k (Rrev n) : ℚ) : ℂ) * x⁻¹ ^ (n - k))) * e2

theorem norm_Rinv_le (n : ℕ) {x : ℂ} {t : ℝ} (ht : 1 ≤ t) (hx : ‖x⁻¹‖ ≤ t) :
    ‖Rinv n x‖ ≤ 4 * (n : ℝ) * ((n : ℝ) + 1) * t ^ n := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hterm : ∀ k ∈ range (n + 1),
      ‖((coeff k (Rrev n) : ℚ) : ℂ) * x⁻¹ ^ (n - k)‖ ≤ 4 * (n : ℝ) * t ^ n := fun k _ => by
    rw [norm_mul, norm_pow]
    have h1 : ‖((coeff k (Rrev n) : ℚ) : ℂ)‖ ≤ ((4 * (n : ℚ) : ℚ) : ℝ) :=
      norm_ratCast_le (abs_coeff_Rrev_le n k)
    have h1' : ‖((coeff k (Rrev n) : ℚ) : ℂ)‖ ≤ 4 * (n : ℝ) := by
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    have h2 : ‖x⁻¹‖ ^ (n - k) ≤ t ^ n :=
      (pow_le_pow_left₀ (norm_nonneg _) hx _).trans (pow_le_pow_right₀ ht (Nat.sub_le n k))
    exact mul_le_mul h1' h2 (pow_nonneg (norm_nonneg _) _) (by positivity)
  calc ‖Rinv n x‖ ≤ ∑ k ∈ range (n + 1), ‖((coeff k (Rrev n) : ℚ) : ℂ) * x⁻¹ ^ (n - k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (n + 1), 4 * (n : ℝ) * t ^ n := Finset.sum_le_sum hterm
    _ = 4 * (n : ℝ) * ((n : ℝ) + 1) * t ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem differentiableAt_Rinv (n : ℕ) {x : ℂ} (hx : x ≠ 0) : DifferentiableAt ℂ (Rinv n) x := by
  unfold Rinv
  exact DifferentiableAt.fun_sum fun k _ =>
    (differentiableAt_const _).mul ((differentiableAt_inv hx).pow _)

/-- Step 1 on the outer patch (l.908–910): for `0 < |x| < 1` and `n = l+1`,
`x√(1-x)(n x^{-n-1} - x^{-1} ∑_m B_{m,n}x^m) = ½ x^{-n}R_n(x)`. -/
theorem half_Rinv {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (l : ℕ) :
    x * (1 - x) ^ (1 / 2 : ℂ) * (((l + 1 : ℕ) : ℂ) * x⁻¹ ^ (l + 2) - x⁻¹ * colBf (l + 1) x) =
      1 / 2 * Rinv (l + 1) x := by
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have h2 := sqrt_mul_hfun hx
  have h3 := colBf_closed hx (n := l + 1) (by omega)
  have h4 : x⁻¹ ^ (l + 1) * x ^ (l + 1) = 1 := by rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow]
  rw [Rinv_eq _ hx0]
  linear_combination ((1 - x) ^ (1 / 2 : ℂ) * ((l + 1 : ℕ) : ℂ) * x⁻¹ ^ (l + 1) -
      (1 - x) ^ (1 / 2 : ℂ) * colBf (l + 1) x) * h1 -
    (1 / 2) * x⁻¹ ^ (l + 1) * (1 - x) ^ (1 / 2 : ℂ) * h3 +
    (1 - x) ^ (1 / 2 : ℂ) * colBf (l + 1) x * h4 +
    (1 / 2) * x⁻¹ ^ (l + 1) * Rf (l + 1) x * h2

theorem summable_bdd_geom {a : ℕ → ℚ} {c : ℚ} (h : ∀ m, |a m| ≤ c) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun m : ℕ => ((a m : ℚ) : ℂ) * x ^ m := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left (c : ℝ)))
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (norm_ratCast_le (h k)) (pow_nonneg (norm_nonneg x) k)

theorem bet_eq (m l : ℕ) : bet m l = ((Bcoef (m + 1) (l + 1) : ℚ) : ℂ) / ((l + 1 : ℕ) : ℂ) := by
  rw [bet]
  push_cast
  ring

theorem summable_bet {x : ℂ} (hx : ‖x‖ < 1) (l : ℕ) : Summable fun m : ℕ => bet m l * x ^ m := by
  have h := (summable_bdd_geom (a := fun m => Bcoef (m + 1) (l + 1))
    (fun m => Bcoef_abs_le (m + 1) (l + 1)) hx).mul_left (((l + 1 : ℕ) : ℂ))⁻¹
  refine h.congr fun m => ?_
  rw [bet_eq]
  ring

/-- `∑_m (B_{m+1,l+1}/(l+1)) x^m = x^{-1} (∑_m B_{m,l+1} x^m)/(l+1)`. -/
theorem tsum_bet {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (l : ℕ) :
    ∑' m : ℕ, bet m l * x ^ m = x⁻¹ * colBf (l + 1) x / ((l + 1 : ℕ) : ℂ) := by
  rw [colBf_shift hx, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul, ← tsum_div_const]
  exact tsum_congr fun m => by rw [bet_eq]; ring

theorem cutz_eq_pow {i l : ℕ} (h : l + 2 ≤ i) (x : ℂ) : cutz i x l = x⁻¹ ^ (l + 2) := by
  rw [cutz, if_pos h, show -((l : ℤ) + 2) = -((l + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast, inv_pow]

theorem aR_mul_cutz (x2 x : ℂ) (i l : ℕ) :
    aR x2 i l * cutz i x l = aR x2 i l * x⁻¹ ^ (l + 2) := by
  by_cases h : l + 2 ≤ i
  · rw [cutz_eq_pow h]
  · rw [aR_eq_zero x2 (by omega), zero_mul, zero_mul]

/-- The expansion of `(x-x₂)⁻²` on `|x₂| < |x|` (l.907). -/
theorem pole_outer {x x2 : ℂ} (hx : ‖x2‖ < ‖x‖) :
    (Summable fun k : ℕ => x2 ^ k * (((k + 1 : ℕ) : ℂ) * x⁻¹ ^ (k + 2))) ∧
      ∑' k : ℕ, x2 ^ k * (((k + 1 : ℕ) : ℂ) * x⁻¹ ^ (k + 2)) = ((x - x2) ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) hx)
  have hq : ‖x2 * x⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one (norm_pos_iff.2 hx0)]
    exact hx
  have e : ∀ k : ℕ, x2 ^ k * (((k + 1 : ℕ) : ℂ) * x⁻¹ ^ (k + 2)) =
      x⁻¹ ^ 2 * (((k : ℂ) + 1) * (x2 * x⁻¹) ^ k) := fun k => by
    push_cast
    ring
  have hs : Summable fun k : ℕ => ((k : ℂ) + 1) * (x2 * x⁻¹) ^ k :=
    ((hasSum_coe_mul_geometric_of_norm_lt_one hq).summable.add
      (hasSum_geometric_of_norm_lt_one hq).summable).congr fun k => by ring
  refine ⟨(hs.mul_left _).congr fun k => (e k).symm, ?_⟩
  simp only [e]
  rw [tsum_mul_left, tsum_succ_mul_geom hq]
  have hne : x - x2 ≠ 0 := sub_ne_zero.2 fun h => by rw [h] at hx; exact lt_irrefl _ hx
  have h1 : (1 - x2 * x⁻¹) = (x - x2) / x := by field_simp
  rw [h1]
  field_simp

end Virasoro.Sphere
