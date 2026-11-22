import Virasoro.Sphere.Proofs.Sec3SaddleUniq
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Sphere paper Lemma 3.6: the coefficients of `g(±1)` by the change of variables `p = p(w)`

`g(±1) = 2i∮ (dw/2πiw) (±w/(1∓w)²) ∑_m σ_m p(w)^{-m}` (proof of Lemma 3.6).  With
`w/(1-w)² = s(w) G₊(p(w))`, `G₊(x) = (x/4)(1-x)^{-3/2}` (`nSer_eq`), and
`-w/(1+w)² = -p(w)/4 = s(w) G₋(p(w))`, `G₋(x) = -(x/4)(1-x)^{-1/2}` (`nAltSer_eq`), the change of
variables (`coeff_change_var`) gives the coefficient of `σ_m` in `g(1)` as `2i[x^m]G₊ = i m h_m`
and in `g(-1)` as `2i[x^m]G₋ = -(i/2)h_{m-1}` (`sum_n_psi`, `sum_n_alt_psi`).

Consumers: `gAt_one_coeff` (`Sec3SaddleValC.lean`), `gAt_neg_one_eq` (`Sec3ExtLinear.lean`).
-/

namespace Virasoro.Sphere

open Finset PowerSeries

theorem two_deriv_hser : derivative ℚ hser + derivative ℚ hser = hser ^ 3 := by
  have hd := congrArg (derivative ℚ) (show hser * hser * (1 - X) = 1 by rw [← sq, hser_sq])
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X,
    smul_eq_mul] at hd
  linear_combination hser * hd - (derivative ℚ hser + derivative ℚ hser) * hser_sq

theorem coeff_X_mul_hser_cube (m : ℕ) : coeff m (X * hser ^ 3) = 2 * (m : ℚ) * halfBinom m := by
  rw [← two_deriv_hser, mul_add, map_add]
  cases m with
  | zero => simp
  | succ j =>
    rw [coeff_succ_X_mul, coeff_derivative, hser, coeff_mk]
    push_cast
    ring

/-- `∑_n n w^n = w/(1-w)²`. -/
noncomputable def nSer : PowerSeries ℚ := mk fun n => (n : ℚ)

/-- `∑_n n(-w)^n = -w/(1+w)²`. -/
noncomputable def nAltSer : PowerSeries ℚ := mk fun n => (n : ℚ) * (-1) ^ n

theorem nSer_mul : nSer * (1 - X) ^ 2 = X := by
  have e : nSer * (1 - X) ^ 2 = nSer - C 2 * (nSer * X) + nSer * X * X := by
    rw [map_ofNat]; ring
  ext j
  rw [e, map_add, map_sub, coeff_C_mul]
  rcases j with _ | _ | j
  · simp [nSer]
  · rw [coeff_succ_mul_X, coeff_succ_mul_X]
    simp [nSer, coeff_X]
  · rw [coeff_succ_mul_X, coeff_succ_mul_X, coeff_succ_mul_X, coeff_X, if_neg (by omega), nSer,
      coeff_mk, coeff_mk, coeff_mk]
    push_cast
    ring

theorem nAltSer_mul : nAltSer * (1 + X) ^ 2 = -X := by
  have e : nAltSer * (1 + X) ^ 2 = nAltSer + C 2 * (nAltSer * X) + nAltSer * X * X := by
    rw [map_ofNat]; ring
  ext j
  rw [e, map_add, map_add, coeff_C_mul, map_neg]
  rcases j with _ | _ | j
  · simp [nAltSer]
  · rw [coeff_succ_mul_X, coeff_succ_mul_X]
    simp [nAltSer, coeff_X]
  · rw [coeff_succ_mul_X, coeff_succ_mul_X, coeff_succ_mul_X, coeff_X, if_neg (by omega),
      nAltSer, coeff_mk, coeff_mk, coeff_mk, pow_succ, pow_succ]
    push_cast
    ring

theorem one_sub_pW : 1 - pW = (1 - X) ^ 2 * invSq := by
  rw [pW, map_ofNat]
  linear_combination -invSq_mul

/-- `w/(1-w)² = s(w) G₊(p(w))` with `G₊(x) = (x/4)(1-x)^{-3/2}`. -/
theorem nSer_eq : nSer = sW * (C (1 / 4 : ℚ) * (X * hser ^ 3)).subst pW := by
  rw [subst_mul hasSubst_pW, subst_C, subst_mul hasSubst_pW, subst_X hasSubst_pW,
    subst_pow hasSubst_pW]
  have hne : (1 - pW : PowerSeries ℚ) ≠ 0 := fun h => by
    have := congrArg constantCoeff h
    rw [map_sub, map_one, constantCoeff_pW, sub_zero, map_zero] at this
    exact one_ne_zero this
  apply mul_right_cancel₀ hne
  have h1 : nSer * (1 - pW) = C (1 / 4 : ℚ) * pW := by
    rw [one_sub_pW, ← mul_assoc, nSer_mul, pW, ← mul_assoc, ← mul_assoc, ← map_mul]
    norm_num
  rw [h1]
  have hu1 := hser_subst_mul_sW
  have hu2 := hser_subst_sq
  have hC : (MvPowerSeries.C (1 / 4 : ℚ) : PowerSeries ℚ) = C (1 / 4 : ℚ) := rfl
  rw [hC]
  linear_combination (-(C (1 / 4 : ℚ) * pW * (hser.subst pW * sW))) * hu2 -
    (C (1 / 4 : ℚ) * pW) * hu1

/-- `-w/(1+w)² = -p(w)/4 = s(w) G₋(p(w))` with `G₋(x) = -(x/4)(1-x)^{-1/2}`. -/
theorem nAltSer_eq : nAltSer = sW * (C (-1 / 4 : ℚ) * (X * hser)).subst pW := by
  rw [subst_mul hasSubst_pW, subst_C, subst_mul hasSubst_pW, subst_X hasSubst_pW]
  have hu1 := hser_subst_mul_sW
  have hC : (MvPowerSeries.C (-1 / 4 : ℚ) : PowerSeries ℚ) = -C (1 / 4 : ℚ) := by
    show (C (-1 / 4 : ℚ) : PowerSeries ℚ) = -C (1 / 4 : ℚ)
    rw [← map_neg]; norm_num
  rw [hC]
  have h1 : nAltSer = -(X * invSq) := by
    have := congrArg (· * invSq) nAltSer_mul
    linear_combination this - nAltSer * invSq_mul
  have h2 : X * invSq = C (1 / 4 : ℚ) * pW := by
    rw [pW, ← mul_assoc, ← mul_assoc, ← map_mul]
    norm_num
  rw [h1, h2]
  linear_combination (C (1 / 4 : ℚ) * pW) * hu1

/-- `∑_{n=1}^m n [p^m]ψ_n = m h_m/2`, by the change of variables `p = p(w)` in
`g(1) = 2i∮ (dw/2πiw) w/(1-w)² ∑_m σ_m p(w)^{-m}` (proof of Lemma 3.6). -/
theorem sum_n_psi (m : ℕ) :
    ∑ n ∈ Icc 1 m, (n : ℚ) * coeff m (psi n) = (m : ℚ) * halfBinom m / 2 := by
  have h := coeff_change_var (C (1 / 4 : ℚ) * (X * hser ^ 3)) m
  rw [mul_assoc, ← nSer_eq, coeff_Pm_mul m nSer (by simp [nSer]), coeff_C_mul,
    coeff_X_mul_hser_cube] at h
  have h4 : (4 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have h' : ∑ n ∈ Icc 1 m, coeff m (psi n) * coeff n nSer = (m : ℚ) * halfBinom m / 2 := by
    apply mul_left_cancel₀ h4
    rw [h]
    ring
  rw [← h']
  refine sum_congr rfl fun n _ => ?_
  rw [nSer, coeff_mk, mul_comm]

/-- `∑_{n=1}^m n(-1)^n [p^m]ψ_n = -h_{m-1}/4` for `m ≥ 1`, by the change of variables in
`g(-1) = 2i∮ (dw/2πiw) (-w)/(1+w)² ∑_m σ_m p(w)^{-m}` (proof of Lemma 3.6). -/
theorem sum_n_alt_psi (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 m, (n : ℚ) * ((-1) ^ n * coeff m (psi n)) = -halfBinom (m - 1) / 4 := by
  have h := coeff_change_var (C (-1 / 4 : ℚ) * (X * hser)) m
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [mul_assoc, ← nAltSer_eq, coeff_Pm_mul _ nAltSer (by simp [nAltSer]),
    coeff_C_mul, coeff_succ_X_mul, hser, coeff_mk] at h
  have h4 : (4 : ℚ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h' : ∑ n ∈ Icc 1 (j + 1), coeff (j + 1) (psi n) * coeff n nAltSer =
      -halfBinom j / 4 := by
    apply mul_left_cancel₀ h4
    rw [h]
    ring
  rw [Nat.add_sub_cancel, ← h']
  refine sum_congr rfl fun n _ => ?_
  rw [nAltSer, coeff_mk]
  ring

end Virasoro.Sphere
