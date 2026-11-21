import Virasoro.Sphere.Proofs.Sec3SaddleII

/-!
# Sphere paper Lemma 3.4(iii): the saddle-point equations for `a_m(z)`
(`sphere/paper.tex` l.725–728, l.789–798)

The saddle-point equations at `σ_{*,m} = i a_m z^m/m`, `σ̄_* = -σ_*` read
`a_m = h_m - ∑_n B_{m,n} a_n z^n/n` with `h_m = [x^m](1-x)^{-1/2}`.  With
`a_m = ₂F₁⁻¹ ∑_l h_{m+l} h_l z^l` the coefficient of `z^K` is
`h_{m+K} = h_m h_K - ∑_{n=1}^K (B_{m,n}/n) h_{K-n}`, the coefficient form of
`B(p,q) = -q∂_q(√(1-q) D(p,q))`, `D = ∑ h_{k+m} p^k q^m`.

Consumer: the saddle-point claim in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem alg_saddle {K : Type*} [Field K] [CharZero K]
    (a b u0 u1 p q D B db dD : K)
    (ha : a ^ 2 = 1 - p) (hb : b ^ 2 = 1 - q) (hpq : p - q ≠ 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h1 : u0 * a = 1) (h2 : u1 * b = 1)
    (hD : (p - q) * D = p * u0 - q * u1)
    (hB : B * (2 * a * b * (a + b) ^ 2) = -(p * q))
    (hdb : 2 * b * db = -1)
    (hdD : (p - q) * dD - D = -u1 + q * (u1 * db * u1)) :
    B = -(q * (db * D + b * dD)) := by
  obtain rfl : p = 1 - a ^ 2 := by linear_combination ha
  obtain rfl : q = 1 - b ^ 2 := by linear_combination hb
  have hfac : (b - a) * (a + b) ≠ 0 := by
    intro h
    apply hpq
    linear_combination h
  have hab : a + b ≠ 0 := right_ne_zero_of_mul hfac
  have hba : b - a ≠ 0 := left_ne_zero_of_mul hfac
  have h2' : (2 : K) ≠ 0 := by norm_num
  obtain rfl : u0 = 1 / a := eq_div_of_mul_eq ha0 h1
  obtain rfl : u1 = 1 / b := eq_div_of_mul_eq hb0 h2
  obtain rfl : db = -1 / (2 * b) :=
    eq_div_of_mul_eq (mul_ne_zero h2' hb0) (by linear_combination hdb)
  have hD' : D = ((1 - a ^ 2) * (1 / a) - (1 - b ^ 2) * (1 / b)) / ((b - a) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hD)
  have hden : (2 * a * b * (a + b) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2' ha0) hb0) (pow_ne_zero 2 hab)
  have hB' : B = -((1 - a ^ 2) * (1 - b ^ 2)) / (2 * a * b * (a + b) ^ 2) :=
    eq_div_of_mul_eq hden hB
  have hdD' : dD = (D - 1 / b + (1 - b ^ 2) * (1 / b * (-1 / (2 * b)) * (1 / b))) /
      ((b - a) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hdD)
  rw [hdD', hD', hB']
  field_simp
  ring

/-- `B(p,q) = -q∂_q(√(1-q) D(p,q))`. -/
theorem Bgf_eq_pderiv :
    Bgf = -(MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1 (aS 1 * Dser)) := by
  set δ := MvPowerSeries.pderiv ℚ (1 : Fin 2) with hδ
  have hX0 : δ (MvPowerSeries.X 0) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have hX1 : δ (MvPowerSeries.X 1) = 1 := MvPowerSeries.pderiv_X_self
  have hu0 : δ (uS 0) = 0 := pderiv_one_ne 0 1 (by decide) _
  have hdb : 2 * aS 1 * δ (aS 1) = -1 := by
    have := congrArg δ (show aS (1 : Fin 2) * aS 1 = 1 - MvPowerSeries.X 1 by rw [← sq, aS_sq])
    simp only [Derivation.leibniz, map_sub, hX1, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  have hdu : δ (uS 1) * aS 1 + uS 1 * δ (aS 1) = 0 := by
    have := congrArg δ (uS_mul_aS (1 : Fin 2))
    simp only [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  have hdu' : δ (uS 1) = -(uS 1 * δ (aS 1) * uS 1) := by
    linear_combination uS 1 * hdu - δ (uS 1) * uS_mul_aS (1 : Fin 2)
  have hdD : (MvPowerSeries.X 0 - MvPowerSeries.X 1) * δ Dser - Dser =
      -uS 1 + MvPowerSeries.X 1 * (uS 1 * δ (aS 1) * uS 1) := by
    have := congrArg δ Dser_rel
    simp only [Derivation.leibniz, map_sub, hX0, hX1, hu0, smul_eq_mul] at this
    rw [hdu'] at this
    linear_combination this
  let φ := algebraMap (MvPowerSeries (Fin 2) ℚ) (FractionRing (MvPowerSeries (Fin 2) ℚ))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (MvPowerSeries (Fin 2) ℚ)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hne : ∀ y : MvPowerSeries (Fin 2) ℚ, y ≠ 0 → φ y ≠ 0 :=
    fun y hy => (map_ne_zero_iff φ hφ).2 hy
  have key := alg_saddle (φ (aS 0)) (φ (aS 1)) (φ (uS 0)) (φ (uS 1)) (φ (MvPowerSeries.X 0))
    (φ (MvPowerSeries.X 1)) (φ Dser) (φ Bgf) (φ (δ (aS 1))) (φ (δ Dser))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (0 : Fin 2)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (1 : Fin 2)))
    (by rw [← map_sub]; exact hne _ X0_sub_X1_ne)
    (hne _ (aS_ne_zero 0)) (hne _ (aS_ne_zero 1))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (0 : Fin 2)))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (1 : Fin 2)))
    (by simpa only [map_mul, map_sub] using congrArg φ Dser_rel)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ Bgf_mul_aS)
    (by simpa only [map_mul, map_neg, map_one, map_ofNat] using congrArg φ hdb)
    (by simpa only [map_mul, map_sub, map_neg, map_add] using congrArg φ hdD)
  apply hφ
  simp only [Derivation.leibniz, smul_eq_mul, map_neg, map_mul, map_add]
  linear_combination key

/-- `h_{m+K} = h_m h_K - ∑_{n=1}^K (B_{m,n}/n) h_{K-n}`. -/
theorem halfBinom_add (m K : ℕ) :
    halfBinom (m + K) = halfBinom m * halfBinom K -
      ∑ n ∈ Icc 1 K, Bcoef m n / (n : ℚ) * halfBinom (K - n) := by
  set c : ℕ → ℚ := fun n =>
    MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) (aS 1 * Dser) with hc
  have hB : ∀ n, Bcoef m n = -((n : ℚ) * c n) := by
    intro n
    have h := congrArg (MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n))
      Bgf_eq_pderiv
    have hx1 : (Finsupp.single 0 m + Finsupp.single 1 n : Fin 2 →₀ ℕ) 1 = n := by simp
    rw [map_neg, coeff_X_mul_pderiv, hx1] at h
    exact h
  have hc0 : c 0 = halfBinom m := by
    have hx1 : (Finsupp.single 0 m + Finsupp.single 1 0 : Fin 2 →₀ ℕ) 1 = 0 := by simp
    rw [hc]
    show MvPowerSeries.coeff _ (one 1 sOne * Dser) = _
    rw [coeff_one_mul, hx1, zero_add, sum_range_one, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_sOne, one_mul, coeff_Dser]
    simp
  have hD : Dser = uS 1 * (aS 1 * Dser) := by rw [← mul_assoc, uS_mul_aS, one_mul]
  have h1 : halfBinom (m + K) = ∑ n ∈ range (K + 1), halfBinom n * c (K - n) := by
    have h := congrArg (MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 K)) hD
    have hx1 : (Finsupp.single 0 m + Finsupp.single 1 K : Fin 2 →₀ ℕ) 1 = K := by simp
    have hx0 : (Finsupp.single 0 m + Finsupp.single 1 K : Fin 2 →₀ ℕ) 0 = m := by simp
    rw [coeff_Dser, hx0, hx1, uS, coeff_one_mul, hx1] at h
    rw [h]
    refine sum_congr rfl fun n hn => ?_
    have hn' : n ≤ K := by have := mem_range.1 hn; omega
    rw [hser, PowerSeries.coeff_mk, hc,
      show (Finsupp.single 0 m + Finsupp.single 1 K - Finsupp.single 1 n : Fin 2 →₀ ℕ) =
        Finsupp.single 0 m + Finsupp.single 1 (K - n) from by ext i; fin_cases i <;> simp]
  have h2 : ∑ n ∈ range (K + 1), halfBinom n * c (K - n) =
      ∑ j ∈ range (K + 1), halfBinom (K - j) * c j := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ K := by have := mem_range.1 hj; omega
    rw [show K + 1 - 1 - j = K - j by omega, show K - (K - j) = j by omega]
  rw [h1, h2, sum_range_succ', hc0, Nat.sub_zero, sum_Icc_one_eq_range]
  have h3 : ∀ j ∈ range K, halfBinom (K - (j + 1)) * c (j + 1) =
      -(Bcoef m (j + 1) / ((j + 1 : ℕ) : ℚ) * halfBinom (K - (j + 1))) := by
    intro j _
    have hj : ((j + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    rw [hB (j + 1)]
    field_simp
  rw [sum_congr rfl h3, sum_neg_distrib]
  ring

end Virasoro.Sphere
