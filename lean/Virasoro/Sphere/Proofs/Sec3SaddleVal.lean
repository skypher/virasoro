import Virasoro.Sphere.Proofs.Sec3SaddleUniq
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Sphere paper Lemma 3.4(iii): the values `1 - g_*(±1)` over `ℚ` (`sphere/paper.tex` l.729–733)

`g(w) = 2i∑_n n t_n w^n` at `w = ±1`: with `ψ_n = w^n/√(1-p)`,
`∑_n n ψ_n = p/(4(1-p)^{3/2})` and `∑_n n(-1)^n ψ_n = -p/(4√(1-p))`, so the coefficient of
`σ_m` in `g(1)` is `i m h_m` and in `g(-1)` is `-(i/2)h_{m-1}`.  At `σ_{*,m} = i a_m z^m/m`:
`1 - g_*(1) = ∑_m h_m a_m z^m` and `1 - g_*(-1) = ∑_m s_m a_m z^m`, `s_m = [x^m]√(1-x)`, and
`₂F₁ · ∑_m h_m a_m z^m = (1-z)^{-1/2}`, `₂F₁ · ∑_m s_m a_m z^m = 1`.

Consumer: the values of `g_*(±1)` in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset PowerSeries

theorem trunc_sum2 {R : Type*} [CommRing R] (B ab Esq Z : R) (Φ : ℕ → R)
    (hΦ : ∀ n, Φ n * ab * Esq ^ n = Z ^ n) (h0 : B * ab * (Esq - Z) ^ 2 = -4 * Z * Esq)
    (N : ℕ) :
    (B + 4 * ∑ n ∈ range (N + 1), (n : R) * Φ n) * (ab * (Esq - Z) ^ 2 * Esq ^ N) =
      Z ^ (N + 1) * (-4 * ((N : R) + 1) * Esq + 4 * (N : R) * Z) := by
  induction N with
  | zero =>
    simp only [zero_add, sum_range_one, Nat.cast_zero, zero_mul, mul_zero, add_zero, pow_zero,
      mul_one, pow_one]
    linear_combination h0
  | succ N ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination Esq * ih + 4 * ((N : R) + 1) * (Esq - Z) ^ 2 * hΦ (N + 1)

theorem coeff_natCast_mul_sum (Φ : ℕ → PowerSeries ℚ) (N m : ℕ) :
    coeff m (∑ n ∈ range (N + 1), (n : PowerSeries ℚ) * Φ n) =
      ∑ n ∈ range (N + 1), (n : ℚ) * coeff m (Φ n) := by
  rw [map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [show (n : PowerSeries ℚ) = C (n : ℚ) from (map_natCast _ n).symm, coeff_C_mul]

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

/-- `∑_{n=1}^m n [p^m]ψ_n = m h_m/2`. -/
theorem sum_n_psi (m : ℕ) :
    ∑ n ∈ Icc 1 m, (n : ℚ) * coeff m (psi n) = (m : ℚ) * halfBinom m / 2 := by
  have hΦ : ∀ n, psi n * sOne * ((1 + sOne) ^ 2) ^ n = X ^ n := fun n => by
    rw [← pow_mul]
    exact psi_rel n
  have h0 : (-(X * hser ^ 3)) * sOne * ((1 + sOne) ^ 2 - X) ^ 2 = -4 * X * (1 + sOne) ^ 2 := by
    linear_combination
      (-4 * X * (1 + sOne) ^ 2 * ((hser * sOne) ^ 2 + hser * sOne + 1)) * hser_mul_sOne +
      (-X * hser ^ 3 * sOne * ((sOne ^ 2 - 1 + X) - 4 * sOne * (1 + sOne))) * sOne_sq
  have h := trunc_sum2 _ sOne ((1 + sOne) ^ 2) X psi hΦ h0 m
  have hU : PowerSeries.constantCoeff
      (sOne * ((1 + sOne) ^ 2 - X) ^ 2 * ((1 + sOne) ^ 2) ^ m : PowerSeries ℚ) ≠ 0 := by
    simp only [map_mul, map_pow, map_add, map_sub, map_one, constantCoeff_sOne, constantCoeff_X]
    positivity
  have hz := coeff_eq_zero_of_mul_unit hU h (le_refl m)
  have e := sum_Icc_one_eq_range (fun n => ((n : ℕ) : ℚ) * coeff m (psi n)) m
  beta_reduce at e
  rw [map_add, map_neg, coeff_X_mul_hser_cube,
    show (4 : PowerSeries ℚ) = C 4 from (map_ofNat _ 4).symm, coeff_C_mul,
    coeff_natCast_mul_sum, sum_range_succ', ← e, Nat.cast_zero, zero_mul, add_zero] at hz
  linarith

/-- `∑_{n=1}^m n(-1)^n [p^m]ψ_n = -h_{m-1}/4` for `m ≥ 1`. -/
theorem sum_n_alt_psi (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 m, (n : ℚ) * ((-1) ^ n * coeff m (psi n)) = -halfBinom (m - 1) / 4 := by
  have hΦ : ∀ n, ((-1 : PowerSeries ℚ) ^ n * psi n) * sOne * ((1 + sOne) ^ 2) ^ n = (-X) ^ n :=
    fun n => by
      rw [← pow_mul]
      linear_combination (-1 : PowerSeries ℚ) ^ n * psi_rel n
  have h0 : (X * hser) * sOne * ((1 + sOne) ^ 2 - (-X)) ^ 2 = -4 * (-X) * (1 + sOne) ^ 2 := by
    linear_combination (4 * X * (1 + sOne) ^ 2) * hser_mul_sOne +
      (X * hser * sOne * (4 * (1 + sOne) + (sOne ^ 2 - 1 + X))) * sOne_sq
  have h := trunc_sum2 _ sOne ((1 + sOne) ^ 2) (-X)
    (fun n => (-1 : PowerSeries ℚ) ^ n * psi n) hΦ h0 m
  have hU : PowerSeries.constantCoeff
      (sOne * ((1 + sOne) ^ 2 - (-X)) ^ 2 * ((1 + sOne) ^ 2) ^ m : PowerSeries ℚ) ≠ 0 := by
    simp only [map_mul, map_pow, map_add, map_sub, map_neg, map_one, constantCoeff_sOne,
      constantCoeff_X]
    positivity
  have h' : (X * hser + 4 * ∑ n ∈ range (m + 1), (n : PowerSeries ℚ) *
        ((-1 : PowerSeries ℚ) ^ n * psi n)) *
      (sOne * ((1 + sOne) ^ 2 - (-X)) ^ 2 * ((1 + sOne) ^ 2) ^ m) =
      X ^ (m + 1) * ((-1) ^ (m + 1) *
        (-4 * ((m : PowerSeries ℚ) + 1) * (1 + sOne) ^ 2 + 4 * (m : PowerSeries ℚ) * (-X))) := by
    rw [h]
    ring
  have hz := coeff_eq_zero_of_mul_unit hU h' (le_refl m)
  have e := sum_Icc_one_eq_range (fun n => ((n : ℕ) : ℚ) * ((-1) ^ n * coeff m (psi n))) m
  beta_reduce at e
  have hc : ∀ n ∈ range (m + 1), (n : ℚ) * coeff m ((-1 : PowerSeries ℚ) ^ n * psi n) =
      (n : ℚ) * ((-1) ^ n * coeff m (psi n)) := by
    intro n _
    rw [show ((-1 : PowerSeries ℚ) ^ n) = C ((-1 : ℚ) ^ n) by rw [map_pow, map_neg, map_one],
      coeff_C_mul]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [map_add, coeff_succ_X_mul,
    show (4 : PowerSeries ℚ) = C 4 from (map_ofNat _ 4).symm, coeff_C_mul,
    coeff_natCast_mul_sum, sum_congr rfl hc, sum_range_succ', ← e, Nat.cast_zero, zero_mul,
    add_zero, hser, coeff_mk] at hz
  rw [Nat.add_sub_cancel]
  linarith

theorem two_mul_coeff_sOne (j : ℕ) :
    2 * ((j : ℚ) + 1) * coeff (j + 1) sOne = -halfBinom j := by
  have hd := congrArg (derivative ℚ) (show sOne * sOne = 1 - X by rw [← sq, sOne_sq])
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X,
    smul_eq_mul] at hd
  have h2 : derivative ℚ sOne + derivative ℚ sOne = -hser := by
    linear_combination hser * hd - (derivative ℚ sOne + derivative ℚ sOne) * hser_mul_sOne
  have := congrArg (coeff j) h2
  rw [map_add, coeff_derivative, map_neg, hser, coeff_mk] at this
  linear_combination this

theorem sum_sOne_hser (K : ℕ) :
    ∑ m ∈ range (K + 1), coeff m sOne * halfBinom (K - m) = if K = 0 then 1 else 0 := by
  have := congrArg (coeff K) (show sOne * hser = 1 by rw [mul_comm, hser_mul_sOne])
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i sOne * coeff j hser) K, PowerSeries.coeff_one] at this
  simp only [hser, coeff_mk] at this
  exact this

/-- The coefficient of `z^K` in `₂F₁ · ∑_m c_m z^m a_m`. -/
theorem coeff_conv_F (y : PowerSeries ℚ) (c : ℕ → ℚ)
    (hy : ∀ k, coeff k y = ∑ m ∈ range (k + 1), c m * coeff (k - m) (aSer m)) (K : ℕ) :
    coeff K (y * hyp2F1) = ∑ m ∈ range (K + 1), c m * (halfBinom K * halfBinom (K - m)) := by
  set P : PowerSeries ℚ := ∑ m ∈ range (K + 1), C (c m) * (X ^ m * aSer m) with hPdef
  have hP : ∀ k ≤ K, coeff k (y - P) = 0 := by
    intro k hk
    rw [map_sub, hy k, hPdef, map_sum, sub_eq_zero]
    have h1 : ∀ m ∈ range (K + 1), coeff k (C (c m) * (X ^ m * aSer m)) =
        if m ≤ k then c m * coeff (k - m) (aSer m) else 0 := by
      intro m _
      rw [coeff_C_mul, coeff_X_pow_mul']
      split_ifs <;> simp
    rw [sum_congr rfl h1, ← sum_filter,
      show (range (K + 1)).filter (fun m => m ≤ k) = range (k + 1) from by
        ext x; simp only [mem_filter, mem_range]; omega]
  obtain ⟨V, hV⟩ : X ^ (K + 1) ∣ y - P :=
    PowerSeries.X_pow_dvd_iff.2 (fun j hj => hP j (by omega))
  have h0 : coeff K ((y - P) * hyp2F1) = 0 := by
    rw [hV, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  have e : y * hyp2F1 = (y - P) * hyp2F1 + P * hyp2F1 := by ring
  rw [e, map_add, h0, zero_add, hPdef, sum_mul, map_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmK : m ≤ K := by have := mem_range.1 hm; omega
  rw [mul_assoc, mul_assoc, aSer_mul, coeff_C_mul, coeff_X_pow_mul', if_pos hmK, Nser, coeff_mk,
    show m + (K - m) = K by omega]

/-- `∑_m c_m z^m a_m(z)`. -/
noncomputable def ySer (c : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => ∑ m ∈ range (k + 1), c m * coeff (k - m) (aSer m)

/-- `₂F₁ · ∑_m h_m a_m z^m = (1-z)^{-1/2}`. -/
theorem ySer_one : ySer halfBinom * hyp2F1 = hser := by
  ext K
  rw [coeff_conv_F (ySer halfBinom) halfBinom (fun k => coeff_mk _ _) K, hser, coeff_mk]
  have h := sum_halfBinom_mul K
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => halfBinom i * halfBinom j) K] at h
  calc ∑ m ∈ range (K + 1), halfBinom m * (halfBinom K * halfBinom (K - m))
      = halfBinom K * ∑ m ∈ range (K + 1), halfBinom m * halfBinom (K - m) := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ = halfBinom K := by rw [h, mul_one]

/-- `₂F₁ · ∑_m s_m a_m z^m = 1`, `s_m = [x^m]√(1-x)`. -/
theorem ySer_two : ySer (fun m => coeff m sOne) * hyp2F1 = 1 := by
  ext K
  rw [coeff_conv_F (ySer fun m => coeff m sOne) (fun m => coeff m sOne)
    (fun k => coeff_mk _ _) K, PowerSeries.coeff_one]
  have h := sum_sOne_hser K
  calc ∑ m ∈ range (K + 1), coeff m sOne * (halfBinom K * halfBinom (K - m))
      = halfBinom K * ∑ m ∈ range (K + 1), coeff m sOne * halfBinom (K - m) := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ = if K = 0 then 1 else 0 := by
        rw [h]
        split_ifs with h0
        · subst h0
          simp [halfBinom, gbinom]
        · rw [mul_zero]

end Virasoro.Sphere
