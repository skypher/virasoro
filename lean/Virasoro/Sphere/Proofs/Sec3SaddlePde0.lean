import Virasoro.Sphere.Proofs.Sec3SaddleOmega

/-!
# Sphere paper Lemma 3.4(i), the `σ⁰` component of the order-`λ⁰` equation
(`sphere/paper.tex` l.737–741)

The `σ⁰` component of `pdeZero k S⁽⁰⁾` is the coefficient of `p^k` in
`iA(p) - ¼A(p)² - p/(1-p)`, which vanishes because `A(p) = -2i((1-p)^{-1/2} - 1)`:
`2h_k + ∑_{n=1}^{k-1} h_n h_{k-n} = 1` for `h_n = [p^n](1-p)^{-1/2}`, by
`(1-p)^{-1/2}(1-p)^{-1/2} = (1-p)^{-1}`.

Consumer: part (i) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem gbinom_neg_one (k : ℕ) : gbinom (-1 : ℚ) k = (-1) ^ k := by
  induction k with
  | zero => simp [gbinom]
  | succ k ih =>
    have hk1 : ((k : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [gbinom_succ_mul, ih, pow_succ]
    field_simp
    ring

/-- `∑_{i+j=k} h_i h_j = 1`: the coefficient of `p^k` in `(1-p)^{-1}`. -/
theorem sum_halfBinom_mul (k : ℕ) :
    ∑ ij ∈ antidiagonal k, halfBinom ij.1 * halfBinom ij.2 = 1 := by
  have h := congrArg (PowerSeries.coeff k)
    (PowerSeries.binomialSeries_add (R := ℚ) (A := ℚ) (-1 / 2) (-1 / 2))
  rw [PowerSeries.coeff_mul] at h
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, ← gbinom_eq_choose] at h
  have e : (-1 / 2 + -1 / 2 : ℚ) = -1 := by norm_num
  rw [e, gbinom_neg_one] at h
  have h2 : ∑ ij ∈ antidiagonal k, halfBinom ij.1 * halfBinom ij.2 =
      (-1) ^ k * ∑ ij ∈ antidiagonal k, gbinom (-1 / 2 : ℚ) ij.1 * gbinom (-1 / 2 : ℚ) ij.2 := by
    rw [mul_sum]
    refine sum_congr rfl fun ij hij => ?_
    rw [← HasAntidiagonal.mem_antidiagonal.1 hij, halfBinom, halfBinom, pow_add]
    ring
  rw [h2, ← h, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem sum_halfBinom_inner (k : ℕ) (hk : 1 ≤ k) :
    2 * halfBinom k + ∑ n ∈ Icc 1 (k - 1), halfBinom n * halfBinom (k - n) = 1 := by
  have h := sum_halfBinom_mul k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => halfBinom i * halfBinom j) k] at h
  have h0 : halfBinom 0 = 1 := by simp [halfBinom, gbinom]
  have hset : range (k + 1) = insert 0 (insert k (Icc 1 (k - 1))) := by
    ext x
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
    sum_insert (by simp only [mem_Icc]; omega), Nat.sub_zero, Nat.sub_self, h0] at h
  linarith

theorem coeff_zero_pd_S0 (n : ℕ) (hn : 1 ≤ n) :
    MvPowerSeries.coeff 0 (pd n S0) = Acoef n := by
  rw [pd, MvPowerSeries.coeff_pderiv]
  have hdeg : (0 + Finsupp.single n.toPNat' 1 : ℕ+ →₀ ℕ).degree = 1 := by simp
  have hsup : (0 + Finsupp.single n.toPNat' 1 : ℕ+ →₀ ℕ).support = {n.toPNat'} := by
    rw [zero_add]
    exact Finsupp.support_single _ one_ne_zero
  show S0 _ * _ = _
  rw [S0, if_pos hdeg, hsup, sum_singleton, Nat.toPNat'_coe, if_pos (by omega)]
  simp

/-- The `σ⁰` component of the order-`λ⁰` equation for `S⁽⁰⁾`. -/
theorem coeff_zero_pdeZero_S0 (k : ℕ) (hk : 1 ≤ k) :
    MvPowerSeries.coeff 0 (pdeZero k S0) = 0 := by
  have hshift : MvPowerSeries.coeff 0 (shiftOp k S0) = 0 := by
    show shiftOp k S0 0 = 0
    simp [shiftOp]
  have hlevel : MvPowerSeries.coeff 0 (levelOp S0) = 0 := by
    show levelOp S0 0 = 0
    simp [levelOp]
  have hprod : ∀ n ∈ Icc 1 (k - 1), MvPowerSeries.coeff 0 (pd n S0 * pd (k - n) S0) =
      Acoef n * Acoef (k - n) := by
    intro n hn
    have := mem_Icc.1 hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_zero_pd_S0 n this.1, coeff_zero_pd_S0 (k - n) (by omega)]
  rw [pdeZero]
  simp only [map_sub, map_add, map_sum, MvPowerSeries.coeff_smul, hshift, hlevel,
    coeff_zero_pd_S0 k hk, MvPowerSeries.coeff_zero_one, smul_eq_mul]
  rw [sum_congr rfl hprod]
  have h := sum_halfBinom_inner k hk
  have hc : (2 * (halfBinom k : ℂ) +
      ∑ n ∈ Icc 1 (k - 1), (halfBinom n : ℂ) * (halfBinom (k - n) : ℂ)) = 1 := by
    exact_mod_cast h
  have hs : ∑ n ∈ Icc 1 (k - 1), Acoef n * Acoef (k - n) =
      -4 * ∑ n ∈ Icc 1 (k - 1), (halfBinom n : ℂ) * (halfBinom (k - n) : ℂ) := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    simp only [Acoef]
    linear_combination (4 * (halfBinom n : ℂ) * (halfBinom (k - n) : ℂ)) * Complex.I_sq
  rw [hs, Acoef]
  linear_combination hc - 2 * (halfBinom k : ℂ) * Complex.I_sq

end Virasoro.Sphere
