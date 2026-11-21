import Virasoro.Sphere.Proofs.Sec3SaddleTools
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Sphere paper Lemma 3.4(ii): the half-pillow variable (`sphere/paper.tex` l.749–757)

Under `p = 4w/(1+w)²` one has `√(1-p) = (1-w)/(1+w)`, `w = p/(1+√(1-p))²`.  The series
`ψ_n(p) = ∑_m [w^{-n}]p(w)^{-m} p^m = ∑_m binom(2m,m+n)(p/4)^m` equals `w^n/√(1-p)`:
`ψ_n √(1-p) (1+√(1-p))^{2n} = p^n`.  The first formula of l.751,
`(1-w)/(1+w)·A(p(w)) = -4i∑_{n≥1}(-1)^{n-1}w^n`, gives
`∑_{n=1}^m (-1)^n [p^m]ψ_n = -h_m/2`.

Consumer: part (ii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset PowerSeries

/-- `ψ_n(p) = ∑_m binom(2m, m+n) (p/4)^m`. -/
noncomputable def psi (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (Nat.choose (2 * m) (m + n) : ℚ) / 4 ^ m

theorem psi_zero : psi 0 = hser := by
  ext m
  rw [psi, hser, coeff_mk, coeff_mk, halfBinom_eq, Nat.centralBinom, add_zero]

theorem constantCoeff_hser : PowerSeries.constantCoeff hser = 1 := by
  rw [hser, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp [halfBinom, gbinom]

theorem hser_mul_sOne : hser * sOne = 1 := by
  have h2 : (hser * sOne) ^ 2 = 1 := by rw [mul_pow, sOne_sq, hser_sq]
  have h0 : (hser * sOne - 1) * (hser * sOne + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have := congrArg PowerSeries.constantCoeff h1
    rw [map_add, map_mul, constantCoeff_sOne, map_one, map_zero, constantCoeff_hser] at this
    norm_num at this

theorem choose_two_step (N i : ℕ) :
    (N + 2).choose (i + 2) = N.choose i + 2 * N.choose (i + 1) + N.choose (i + 2) := by
  show (N + 1 + 1).choose (i + 1 + 1) = _
  rw [Nat.choose_succ_succ' (N + 1) (i + 1), Nat.choose_succ_succ' N i,
    Nat.choose_succ_succ' N (i + 1)]
  ring

theorem psi_rec (n : ℕ) :
    X * (psi (n + 2) + (psi (n + 1) + psi (n + 1)) + psi n) =
      psi (n + 1) + psi (n + 1) + psi (n + 1) + psi (n + 1) := by
  ext m
  cases m with
  | zero => simp [psi]
  | succ m =>
    rw [coeff_succ_X_mul]
    have key := choose_two_step (2 * m) (m + n)
    have e1 : 2 * (m + 1) = 2 * m + 2 := by ring
    have e2 : m + 1 + (n + 1) = m + n + 2 := by ring
    have e3 : m + (n + 2) = m + n + 2 := by ring
    have e4 : m + (n + 1) = m + n + 1 := by ring
    simp only [map_add, psi, coeff_mk]
    rw [e1, e2, e3, e4, key]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem psi_rec0 :
    X * (psi 1 + psi 1 + psi 0 + psi 0) = psi 0 + psi 0 + psi 0 + psi 0 - 4 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) 4]
  ext m
  cases m with
  | zero =>
    simp [psi]
    norm_num
  | succ m =>
    rw [coeff_succ_X_mul]
    have key0 : (2 * (m + 1)).choose (m + 1) = 2 * ((2 * m).choose m + (2 * m).choose (m + 1)) := by
      have h1 := Nat.choose_symm_half m
      have h2 := Nat.choose_succ_succ' (2 * m) m
      have h3 := Nat.choose_succ_succ' (2 * m + 1) m
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, h3, ← h1, h2]
      ring
    simp only [map_add, map_sub, psi, coeff_mk, coeff_C, if_neg (Nat.succ_ne_zero m), sub_zero,
      add_zero]
    rw [key0]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem X_add_X_ne : (X + X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp at this

/-- `ψ_n √(1-p) (1+√(1-p))^{2n} = p^n`. -/
theorem psi_rel_aux : ∀ n, psi n * sOne * (1 + sOne) ^ (2 * n) = X ^ n ∧
    psi (n + 1) * sOne * (1 + sOne) ^ (2 * (n + 1)) = X ^ (n + 1) := by
  have h : psi 0 * sOne = 1 := by rw [psi_zero, hser_mul_sOne]
  intro n
  induction n with
  | zero =>
    refine ⟨by simpa using h, ?_⟩
    apply mul_left_cancel₀ X_add_X_ne
    linear_combination (sOne * (1 + sOne) ^ 2) * psi_rec0 -
      (2 * X * (1 + sOne) ^ 2 - 4 * (1 + sOne) ^ 2) * h + (-2 * X - 4 * (1 + sOne)) * sOne_sq
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    apply mul_left_cancel₀ (X_ne_zero (R := ℚ))
    linear_combination (sOne * (1 + sOne) ^ (2 * n) * ((1 + sOne) ^ 2) ^ 2) * psi_rec n +
      (4 * (1 + sOne) ^ 2 - 2 * X * (1 + sOne) ^ 2) * ih.2 - (X * ((1 + sOne) ^ 2) ^ 2) * ih.1 +
      (X ^ n * X * (-X - (1 + sOne) * (3 + sOne))) * sOne_sq

theorem psi_rel (n : ℕ) : psi n * sOne * (1 + sOne) ^ (2 * n) = X ^ n := (psi_rel_aux n).1

theorem alt_trunc (N : ℕ) :
    (∑ n ∈ range (N + 1), (-1) ^ n * psi n) *
        (sOne * (1 + sOne) ^ (2 * N) * ((1 + sOne) ^ 2 + X)) =
      (1 + sOne) ^ (2 * (N + 1)) + (-1) ^ N * X ^ (N + 1) := by
  induction N with
  | zero =>
    have h : psi 0 * sOne = 1 := by rw [psi_zero, hser_mul_sOne]
    simp only [zero_add, sum_range_one, pow_zero, one_mul, mul_one, pow_one, mul_zero]
    linear_combination ((1 + sOne) ^ 2 + X) * h
  | succ N ih =>
    rw [sum_range_succ]
    linear_combination (1 + sOne) ^ 2 * ih +
      (-1) ^ (N + 1) * ((1 + sOne) ^ 2 + X) * psi_rel (N + 1)

/-- A series `f` with `f U = X^{N+1} V` for a unit `U` has no coefficient of order `≤ N`. -/
theorem coeff_eq_zero_of_mul_unit {f U V : PowerSeries ℚ} {N m : ℕ}
    (hU : PowerSeries.constantCoeff U ≠ 0) (h : f * U = X ^ (N + 1) * V) (hm : m ≤ N) :
    coeff m f = 0 := by
  have hf : f = X ^ (N + 1) * (V * U⁻¹) := by
    rw [← mul_assoc, ← h, mul_assoc, PowerSeries.mul_inv_cancel _ hU, mul_one]
  rw [hf, coeff_X_pow_mul', if_neg (by omega)]

theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 N, F n = ∑ n ∈ range N, F (n + 1) := by
  refine sum_nbij' (fun n => n - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    have := mem_Icc.1 hn
    exact mem_range.2 (by omega)
  · intro n hn
    have := mem_range.1 hn
    exact mem_Icc.2 (by omega)
  · intro n hn
    have := mem_Icc.1 hn
    show n - 1 + 1 = n
    omega
  · intro n hn
    rfl
  · intro n hn
    have := mem_Icc.1 hn
    show F n = F (n - 1 + 1)
    rw [show n - 1 + 1 = n by omega]

/-- `∑_{n=1}^m (-1)^n [p^m]ψ_n = -h_m/2` for `m ≥ 1`. -/
theorem alt_sum_psi (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 m, (-1 : ℚ) ^ n * coeff m (psi n) = -halfBinom m / 2 := by
  set AS := ∑ n ∈ range (m + 1), (-1) ^ n * psi n with hAS
  set U := sOne * (1 + sOne) ^ (2 * m) * ((1 + sOne) ^ 2 + X) with hU
  have hT : (AS + AS - hser - 1) * U = X ^ (m + 1) * ((-1) ^ m + (-1) ^ m) := by
    rw [hU]
    linear_combination 2 * alt_trunc m -
      ((1 + sOne) ^ (2 * m) * ((1 + sOne) ^ 2 + X)) * hser_mul_sOne -
      ((1 + sOne) * (1 + sOne) ^ (2 * m)) * sOne_sq
  have hUc : PowerSeries.constantCoeff U ≠ 0 := by
    rw [hU]
    simp only [map_mul, map_pow, map_add, map_one, constantCoeff_sOne, constantCoeff_X]
    positivity
  have h0 := coeff_eq_zero_of_mul_unit hUc hT (le_refl m)
  have hc1 : coeff m (1 : PowerSeries ℚ) = 0 := by
    rw [PowerSeries.coeff_one, if_neg (by omega)]
  have hcA : coeff m AS = halfBinom m + ∑ n ∈ Icc 1 m, (-1 : ℚ) ^ n * coeff m (psi n) := by
    rw [hAS, map_sum, sum_range_succ', sum_Icc_one_eq_range, add_comm]
    congr 1
    · rw [pow_zero, one_mul, psi_zero, hser, coeff_mk]
    · refine sum_congr rfl fun n _ => ?_
      rw [show ((-1 : PowerSeries ℚ) ^ (n + 1)) = PowerSeries.C ((-1 : ℚ) ^ (n + 1)) by
        rw [map_pow, map_neg, map_one], coeff_C_mul]
  rw [map_sub, map_sub, map_add, hc1, hcA, hser, coeff_mk] at h0
  linarith

end Virasoro.Sphere
