import Virasoro.Sphere.Proofs.Sec3RationalC

/-!
# Exponentials, logarithms and roots of power series over `ℂ` (sphere paper Lemma 3.7)

Tools for Step 4 of the proof of Lemma 3.7 (sphere/paper.tex l.1156–1180): `exp(f + g)`,
`exp(g)^k`, `exp(log f) = f`, uniqueness of `k`-th roots with constant term `1`, coefficients of
`f(zR(z))`, and `∏(1 - q^{2m})^e = (∏(1 - q^{2m}))^e`.
-/

namespace Virasoro.Sphere

open PowerSeries

theorem exp_subst_zero : (exp ℂ).subst (0 : PowerSeries ℂ) = 1 :=
  mexp_zero (σ := Unit) (A := ℂ)

theorem exp_subst_add (f g : PowerSeries ℂ) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) :
    (exp ℂ).subst (f + g) = (exp ℂ).subst f * (exp ℂ).subst g :=
  mexp_add (σ := Unit) (A := ℂ) (f := f) (g := g)
    (by rw [show MvPowerSeries.constantCoeff f = 0 from hf]; exact IsNilpotent.zero)
    (by rw [show MvPowerSeries.constantCoeff g = 0 from hg]; exact IsNilpotent.zero)

theorem exp_subst_pow (g : PowerSeries ℂ) (hg : constantCoeff g = 0) (k : ℕ) :
    (exp ℂ).subst g ^ k = (exp ℂ).subst ((k : ℂ) • g) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, exp_subst_zero]
  | succ k ih =>
    have hk : constantCoeff ((k : ℂ) • g) = 0 := by
      rw [smul_eq_C_mul, map_mul, hg, mul_zero]
    rw [pow_succ, ih, ← exp_subst_add _ _ hk hg, Nat.cast_succ, add_smul, one_smul]

/-- Two series with constant term `1` and the same logarithmic derivative are equal. -/
theorem eq_of_deriv_mul_eq {y f : PowerSeries ℂ} (hy : constantCoeff y = 1)
    (hf : constantCoeff f = 1) (h : derivative ℂ y * f = derivative ℂ f * y) : y = f := by
  have hf0 : constantCoeff f ≠ 0 := by rw [hf]; exact one_ne_zero
  have hff : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hf0
  have key : y * f⁻¹ = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, derivative_inv', Derivation.map_one_eq_zero]
      simp only [smul_eq_mul]
      linear_combination (f⁻¹ ^ 2) * h - (derivative ℂ y * f⁻¹) * hff
    · rw [map_mul, hy, constantCoeff_inv, hf, map_one]
      simp
  calc y = y * f⁻¹ * f := by rw [mul_assoc, mul_comm f⁻¹ f, hff, mul_one]
    _ = f := by rw [key, one_mul]

/-- `exp(log f) = f` for a series `f` with constant term `1`. -/
theorem exp_log_subst (f : PowerSeries ℂ) (hf : constantCoeff f = 1) :
    (exp ℂ).subst ((log ℂ).subst (f - 1)) = f := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' h1
  have hL : constantCoeff ((log ℂ).subst (f - 1)) = 0 :=
    constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  refine eq_of_deriv_mul_eq (constantCoeff_exp_subst _ hL) hf ?_
  rw [deriv_exp_subst _ hL, derivative_subst hs1, map_sub, Derivation.map_one_eq_zero, sub_zero]
  have e := deriv_log_subst_mul (τ := Unit) (f - 1) h1
  rw [add_sub_cancel] at e
  linear_combination ((exp ℂ).subst ((log ℂ).subst (f - 1)) * derivative ℂ f) * e

/-- Uniqueness of `k`-th roots with constant term `1`. -/
theorem eq_of_pow_eq {a b : PowerSeries ℂ} (ha : constantCoeff a = 1) (hb : constantCoeff b = 1)
    {k : ℕ} (hk : k ≠ 0) (h : a ^ k = b ^ k) : a = b := by
  have h1 := (Commute.all a b).mul_geom_sum₂ k
  rw [h, sub_self] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact sub_eq_zero.1 h2
  · exfalso
    have h3 := congrArg constantCoeff h2
    rw [map_sum, map_zero] at h3
    simp only [map_mul, map_pow, ha, hb, one_pow, mul_one, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at h3
    exact hk (by exact_mod_cast h3)

/-- A coefficient of a product depends only on the coefficients of the factors up to that
order. -/
theorem coeff_mul_congr_le {A : Type*} [CommRing A] (E : PowerSeries A) {G P : PowerSeries A}
    {N : ℕ} (h : ∀ k ≤ N, coeff k G = coeff k P) : coeff N (E * G) = coeff N (E * P) := by
  have h1 : mkT N A G = mkT N A P := (mkT_eq_iff _ _).2 h
  have h2 : mkT N A (E * G) = mkT N A (E * P) := by rw [map_mul, map_mul, h1]
  exact (mkT_eq_iff _ _).1 h2 N le_rfl

/-- The coefficients of `f(zR(z)) W(z)`. -/
theorem coeff_subst_X_mul (f R W : PowerSeries ℂ) (N : ℕ) :
    coeff N (f.subst (X * R) * W) =
      ∑ n ∈ Finset.range (N + 1), coeff n f * coeff (N - n) (R ^ n * W) := by
  have hg : constantCoeff (X * R) = 0 := by rw [map_mul, constantCoeff_X, zero_mul]
  have hs := HasSubst.of_constantCoeff_zero' hg
  have h1 : ∀ k ≤ N, coeff k (f.subst (X * R)) =
      coeff k (∑ n ∈ Finset.range (N + 1), C (coeff n f) * (X * R) ^ n) := by
    intro k hk
    rw [coeff_subst' hs, map_sum, finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [coeff_C_mul, smul_eq_mul]
    · intro d hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      refine hd ?_
      show coeff d f • coeff k ((X * R) ^ d) = 0
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]
  rw [mul_comm, coeff_mul_congr_le W h1, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  rw [show W * (C (coeff n f) * (X * R) ^ n) = C (coeff n f) * (X ^ n * (R ^ n * W)) by
    rw [mul_pow]; ring, coeff_C_mul, coeff_X_pow_mul', if_pos hn']

/-- `∏(1 - q^{2m})^e = (∏(1 - q^{2m}))^e`. -/
theorem etaSqPow_pow (e : ℕ) : etaSqPow e = etaSqPow 1 ^ e := by
  have hstab : ∀ n : ℕ, mkT n ℚ (etaSqPow 1) =
      mkT n ℚ (∏ m ∈ Finset.Icc 1 n, (1 - (X : PowerSeries ℚ) ^ (2 * m))) := by
    intro n
    rw [mkT_eq_iff]
    intro k hk
    rw [etaSqPow, coeff_mk]
    simp only [pow_one]
    refine (mkT_eq_iff _ _).1 ?_ k le_rfl
    rw [map_prod, map_prod]
    refine Finset.prod_subset (Finset.Icc_subset_Icc_right hk) fun m hm hm' => ?_
    rw [Finset.mem_Icc] at hm hm'
    have h0 : mkT k ℚ ((X : PowerSeries ℚ) ^ (2 * m)) = 0 := by
      rw [mkT_eq_zero_iff]
      intro j hj
      rw [coeff_X_pow, if_neg (by omega)]
    rw [map_sub, map_one, h0, sub_zero]
  ext n
  rw [etaSqPow, coeff_mk]
  have h2 : mkT n ℚ (etaSqPow 1 ^ e) =
      mkT n ℚ (∏ m ∈ Finset.Icc 1 n, (1 - (X : PowerSeries ℚ) ^ (2 * m)) ^ e) := by
    rw [map_pow, hstab n, ← map_pow, Finset.prod_pow]
  exact ((mkT_eq_iff _ _).1 h2 n le_rfl).symm

end Virasoro.Sphere
