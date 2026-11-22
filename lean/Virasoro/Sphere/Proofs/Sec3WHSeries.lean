import Virasoro.Sphere.Proofs.Sec3SaddleTools
import Virasoro.Sphere.Proofs.Sec3SaddlePsi
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Sphere paper Lemma 3.4(iii): the half-pillow variable `w` (proof of Lemma 3.4(iii))

`p(w) = 4w/(1+w)²` and `s(w) = (1-w)/(1+w) = √(1-p(w))` as power series in `w` over `ℚ`.  The
Laurent polynomial `p(w)^{-m} = (1+w)^{2m}/(4w)^m` is handled through `P_m = (1+w)^{2m}`.
- `sW_sq`: `s² = 1 - p`; `hser_subst_mul_sW`: `(1-p(w))^{-1/2} s(w) = 1`.
- `X_deriv_Pm`: `w∂_w p^{-m} = -m s p^{-m}`, in the form `w P_m' = m(P_m - s P_m)`; hence
  `[w^i](s P_m) = ((m-i)/m) binom(2m,i)` (`coeff_sW_Pm`).
- `coeff_change_var`: `[w^0](s p^{-m} G(p(w))) = [x^m] G`, in the form
  `[w^m](P_m s G(p)) = 4^m [x^m] G` (the change of variables `p = p(w)`, `dp/p = s dw/w`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `(1+w)^{-2}`. -/
noncomputable def invSq : PowerSeries ℚ := ((1 + X) ^ 2)⁻¹

theorem invSq_mul : (1 + X : PowerSeries ℚ) ^ 2 * invSq = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp)

/-- `p(w) = 4w/(1+w)²`. -/
noncomputable def pW : PowerSeries ℚ := C 4 * X * invSq

/-- `s(w) = (1-w)/(1+w)`. -/
noncomputable def sW : PowerSeries ℚ := (1 - X) * (1 + X) * invSq

/-- `P_m = (1+w)^{2m} = 4^m w^m p(w)^{-m}`. -/
noncomputable def Pm (m : ℕ) : PowerSeries ℚ := (1 + X) ^ (2 * m)

theorem sW_sq : sW ^ 2 = 1 - pW := by
  have h := invSq_mul
  rw [sW, pW]
  have h4 : (C 4 : PowerSeries ℚ) = 4 := map_ofNat _ 4
  rw [h4]
  linear_combination ((1 - X) ^ 2 * invSq + 1) * h

theorem constantCoeff_pW : constantCoeff pW = 0 := by
  simp [pW]

theorem hasSubst_pW : HasSubst pW :=
  HasSubst.of_constantCoeff_zero' constantCoeff_pW

theorem constantCoeff_sW : constantCoeff sW = 1 := by
  have h := congrArg constantCoeff invSq_mul
  simp only [map_mul, map_pow, map_add, map_one, constantCoeff_X, add_zero, one_pow,
    one_mul] at h
  simp [sW, h]

/-- `(1-p(w))^{-1/2}` squared times `1-p(w)` is `1`. -/
theorem hser_subst_sq : (hser.subst pW) ^ 2 * (1 - pW) = 1 := by
  have := congrArg (substAlgHom hasSubst_pW) hser_sq
  rwa [map_mul, map_pow, map_sub, map_one, coe_substAlgHom, subst_X hasSubst_pW] at this

/-- `(1-p(w))^{-1/2} s(w) = 1`. -/
theorem hser_subst_mul_sW : hser.subst pW * sW = 1 := by
  have hs := hser_subst_sq
  have hc : constantCoeff (hser.subst pW) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hasSubst_pW, finsum_eq_single _ 0]
    · simp only [pow_zero, coeff_one, if_true, smul_eq_mul, mul_one]
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_hser]
      simp
    · intro d hd
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_pW, zero_pow hd, smul_zero]
  have h0 : (hser.subst pW * sW - 1) * (hser.subst pW * sW + 1) = 0 := by
    linear_combination (hser.subst pW) ^ 2 * sW_sq + hs
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have := congrArg constantCoeff h1
    rw [map_add, map_mul, hc, constantCoeff_sW, map_one, map_zero] at this
    norm_num at this

theorem sW_mul_one_add : sW * (1 + X) = 1 - X := by
  rw [sW]
  linear_combination (1 - X) * invSq_mul

theorem coeff_Pm (m i : ℕ) : coeff i (Pm m) = ((2 * m).choose i : ℚ) := by
  have h : Pm m = (((1 + Polynomial.X) ^ (2 * m) : Polynomial ℚ) : PowerSeries ℚ) := by
    rw [Pm, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem Pm_zero : Pm 0 = 1 := by simp [Pm]

/-- `w∂_w p^{-m} = -m s p^{-m}`, multiplied by `4^m w^m`: `w P_m' = m(P_m - s P_m)`. -/
theorem X_deriv_Pm {m : ℕ} (hm : 1 ≤ m) :
    X * d⁄dX ℚ (Pm m) = C (m : ℚ) * (Pm m - sW * Pm m) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * m = n + 1 := ⟨2 * m - 1, by omega⟩
  have hd : d⁄dX ℚ (Pm m) = ((n + 1 : ℕ) : PowerSeries ℚ) * (1 + X) ^ n := by
    rw [Pm, hn, Derivation.leibniz_pow, map_add, derivative_one, derivative_X, zero_add,
      Nat.add_sub_cancel, smul_eq_mul, mul_one, nsmul_eq_mul]
  have hc : ((n + 1 : ℕ) : PowerSeries ℚ) = 2 * C (m : ℚ) := by
    rw [← hn, map_natCast]
    push_cast
    ring
  have hP : Pm m = (1 + X) ^ n * (1 + X) := by rw [Pm, hn, pow_succ]
  rw [hd, hc, hP]
  linear_combination (C (m : ℚ) * (1 + X) ^ n) * sW_mul_one_add

theorem coeff_X_mul_derivQ (f : PowerSeries ℚ) (i : ℕ) :
    coeff i (X * d⁄dX ℚ f) = (i : ℚ) * coeff i f := by
  rcases i with _ | i
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- `[w^i](s P_m) = ((m-i)/m) binom(2m,i)`: the coefficients of `s p^{-m}` from
`w∂_w p^{-m} = -m s p^{-m}`. -/
theorem coeff_sW_Pm {m : ℕ} (hm : 1 ≤ m) (i : ℕ) :
    coeff i (sW * Pm m) = ((m : ℚ) - i) / m * ((2 * m).choose i : ℚ) := by
  have h := congrArg (coeff i) (X_deriv_Pm hm)
  rw [coeff_X_mul_derivQ, coeff_C_mul, map_sub, coeff_Pm] at h
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp
  linear_combination h

theorem pW_pow_mul_Pm {k m : ℕ} (hkm : k ≤ m) :
    pW ^ k * Pm m = C (4 ^ k : ℚ) * X ^ k * Pm (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  rw [Nat.add_sub_cancel_left, Pm, Pm, pW, mul_pow, mul_pow,
    show 2 * (k + j) = 2 * k + 2 * j by ring, pow_add, pow_mul, map_pow]
  have h1 : invSq ^ k * ((1 + X) ^ 2) ^ k = 1 := by
    rw [← mul_pow, mul_comm, invSq_mul, one_pow]
  linear_combination (C (4 : ℚ) ^ k * X ^ k * (1 + X) ^ (2 * j)) * h1

theorem X_pow_dvd_pW_pow (k : ℕ) : X ^ k ∣ pW ^ k :=
  ⟨(C 4 * invSq) ^ k, by rw [pW, ← mul_pow]; ring⟩

/-- The change of variables `p = p(w)`: `[w^0](s p^{-m} G(p(w))) = [x^m] G`, multiplied by
`4^m w^m`. -/
theorem coeff_change_var (G : PowerSeries ℚ) (m : ℕ) :
    coeff m (Pm m * sW * G.subst pW) = 4 ^ m * coeff m G := by
  set T : PowerSeries ℚ := mk fun i => coeff (i + (m + 1)) G with hT
  have hsplit : G = (∑ k ∈ range (m + 1), C (coeff k G) * X ^ k) + X ^ (m + 1) * T := by
    ext i
    rw [map_add, map_sum, coeff_X_pow_mul']
    simp only [coeff_C_mul, coeff_X_pow, hT, coeff_mk, mul_ite, mul_one, mul_zero]
    by_cases hi : i < m + 1
    · rw [if_neg (by omega), add_zero, sum_ite_eq (range (m + 1)) i, if_pos (mem_range.2 hi)]
    · rw [if_pos (by omega), Nat.sub_add_cancel (by omega),
        sum_ite_eq (range (m + 1)) i, if_neg (fun h => hi (mem_range.1 h)), zero_add]
  have hG : G.subst pW = (∑ k ∈ range (m + 1), C (coeff k G) * pW ^ k) +
      pW ^ (m + 1) * T.subst pW := by
    conv_lhs => rw [hsplit]
    rw [subst_add hasSubst_pW, subst_mul hasSubst_pW, subst_pow hasSubst_pW, subst_X hasSubst_pW]
    congr 1
    rw [← coe_substAlgHom hasSubst_pW, map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [coe_substAlgHom, subst_mul hasSubst_pW, subst_pow hasSubst_pW, subst_X hasSubst_pW,
      subst_C]
    rfl
  rw [hG, mul_add, map_add]
  have h2 : coeff m (Pm m * sW * (pW ^ (m + 1) * T.subst pW)) = 0 := by
    obtain ⟨Q, hQ⟩ := X_pow_dvd_pW_pow (m + 1)
    rw [hQ, show Pm m * sW * (X ^ (m + 1) * Q * T.subst pW) =
      X ^ (m + 1) * (Pm m * sW * Q * T.subst pW) by ring, coeff_X_pow_mul', if_neg (by omega)]
  rw [h2, add_zero, mul_sum, map_sum, sum_eq_single m]
  · rw [show Pm m * sW * (C (coeff m G) * pW ^ m) =
        C (coeff m G) * (sW * (pW ^ m * Pm m)) by ring, coeff_C_mul,
      pW_pow_mul_Pm le_rfl, Nat.sub_self, Pm_zero, mul_one,
      show sW * (C (4 ^ m : ℚ) * X ^ m) = C (4 ^ m : ℚ) * (X ^ m * sW) by ring, coeff_C_mul,
      coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_sW]
    ring
  · intro k hk hkm
    have hk' : k < m := by have := mem_range.1 hk; omega
    rw [show Pm m * sW * (C (coeff k G) * pW ^ k) =
        C (coeff k G) * (sW * (pW ^ k * Pm m)) by ring, coeff_C_mul,
      pW_pow_mul_Pm hk'.le,
      show sW * (C (4 ^ k : ℚ) * X ^ k * Pm (m - k)) =
        C (4 ^ k : ℚ) * (X ^ k * (sW * Pm (m - k))) by ring, coeff_C_mul,
      coeff_X_pow_mul', if_pos hk'.le, coeff_sW_Pm (by omega)]
    have : ((m - k : ℕ) : ℚ) - ((m - k : ℕ) : ℚ) = 0 := sub_self _
    rw [this, zero_div, zero_mul, mul_zero, mul_zero]
  · intro h
    exact absurd (mem_range.2 (Nat.lt_succ_self m)) h

end Virasoro.Sphere
