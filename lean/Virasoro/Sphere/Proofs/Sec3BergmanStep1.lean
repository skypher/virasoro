import Virasoro.Sphere.Proofs.Sec3SaddlePde1

/-!
# Sphere paper Lemma 3.5, Step 1 (`sphere/paper.tex` l.880–889): the rational twist identity

With `s₁ = √(1-p)`, `s₂ = √(1-q)`:
`√(1-p) (B(p,q) - pq/(p-q)²) = -pq(2-p-q) / (2√(1-q)(p-q)²)`, here multiplied by `2(p-q)²`.
Taking the coefficient of `q^n` and setting `p = 1/X` gives the polynomial
`P_n(X) = √(X(X-1)) f_n(X)`, `f_n(X) = ∑_m B_{m,n} X^{-m-1} - n X^{n-1}`, in the reversed form
`p^n P_n(1/p) = √(1-p) (p^n ∑_m B_{m,n} p^m - n)`:
`2 p^n P_n(1/p) = -((2-p) U_n(p) - p U_{n-1}(p))`, `U_n(p) = ∑_{i<n} (n-i) h_i p^i`,
`h_i = [x^i](1-x)^{-1/2}`, which is the formula
`P_n(X) = -½ [q^{n-1}] ((2X-1) - Xq) / ((1-q)^{1/2} (1-Xq)²)` of l.887–889.

Consumers: Step 2 of Lemma 3.5 and Step 3 of Lemma 3.7.
-/

namespace Virasoro.Sphere

open Finset

local notation "p₀" => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ)
local notation "q₀" => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ)

/-- The rational twist identity (sphere/paper.tex l.882–886), multiplied by `2(p-q)²`. -/
theorem twist_identity :
    2 * (aS 0 * (Bgf * (p₀ - q₀) ^ 2 - p₀ * q₀)) = -(p₀ * q₀ * (2 - p₀ - q₀)) * uS 1 := by
  have hB : Bgf * (2 * aS 0 * aS 1 * (aS 0 + aS 1) ^ 2) = -(p₀ * q₀) := by
    have := Bgf_mul_Bden
    rw [Bden, sqrtOneSub_eq_aS, sqrtOneSub_eq_aS] at this
    exact this
  have e0 : p₀ = 1 - aS 0 ^ 2 := by rw [aS_sq]; ring
  have e1 : q₀ = 1 - aS 1 ^ 2 := by rw [aS_sq]; ring
  have hu := uS_mul_aS (1 : Fin 2)
  have hc : 2 * aS 0 * aS 1 * (Bgf * (p₀ - q₀) ^ 2 - p₀ * q₀) = -(p₀ * q₀ * (2 - p₀ - q₀)) := by
    rw [e0, e1] at hB ⊢
    linear_combination (aS 1 - aS 0) ^ 2 * hB
  linear_combination uS 1 * hc - 2 * aS 0 * (Bgf * (p₀ - q₀) ^ 2 - p₀ * q₀) * hu

/-- The coefficient of `q^n` of a series in `(p,q)`, a series in `p`. -/
noncomputable def coefQ (n : ℕ) : MvPowerSeries (Fin 2) ℚ →ₗ[ℚ] PowerSeries ℚ where
  toFun F :=
    PowerSeries.mk fun a => MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 n) F
  map_add' F G := by ext a; simp
  map_smul' c F := by ext a; simp

theorem coeff_coefQ (n a : ℕ) (F : MvPowerSeries (Fin 2) ℚ) :
    PowerSeries.coeff a (coefQ n F) =
      MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 n) F := by
  simp [coefQ]

theorem coefQ_one0_mul (f : PowerSeries ℚ) (G : MvPowerSeries (Fin 2) ℚ) (n : ℕ) :
    coefQ n (one 0 f * G) = f * coefQ n G := by
  ext a
  have hx0 : (Finsupp.single 0 a + Finsupp.single 1 n : Fin 2 →₀ ℕ) 0 = a := by simp
  rw [coeff_coefQ, coeff_one_mul, hx0, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ a := by have := mem_range.1 hi; omega
  rw [coeff_coefQ,
    show (Finsupp.single 0 a + Finsupp.single 1 n - Finsupp.single 0 i : Fin 2 →₀ ℕ) =
      Finsupp.single 0 (a - i) + Finsupp.single 1 n from by ext j; fin_cases j <;> simp]

theorem coefQ_X1_mul_succ (G : MvPowerSeries (Fin 2) ℚ) (n : ℕ) :
    coefQ (n + 1) (q₀ * G) = coefQ n G := by
  ext a
  rw [coeff_coefQ, coeff_X_mul', if_pos (by simp), coeff_coefQ,
    show (Finsupp.single 0 a + Finsupp.single 1 (n + 1) - Finsupp.single 1 1 : Fin 2 →₀ ℕ) =
      Finsupp.single 0 a + Finsupp.single 1 n from by ext j; fin_cases j <;> simp]

theorem coefQ_X1_mul_zero (G : MvPowerSeries (Fin 2) ℚ) : coefQ 0 (q₀ * G) = 0 := by
  ext a
  rw [coeff_coefQ, coeff_X_mul', if_neg (by simp)]
  simp

theorem coefQ_one1 (f : PowerSeries ℚ) (n : ℕ) :
    coefQ n (one 1 f) = PowerSeries.C (PowerSeries.coeff n f) := by
  ext a
  have hx1 : (Finsupp.single 0 a + Finsupp.single 1 n : Fin 2 →₀ ℕ) 1 = n := by simp
  rw [coeff_coefQ, coeff_one, PowerSeries.coeff_C, hx1]
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [if_neg ha, if_neg]
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
    exact ha this

/-- The column series `∑_m B_{m,n} p^m`. -/
noncomputable def colB (n : ℕ) : PowerSeries ℚ := PowerSeries.mk fun m => Bcoef m n

theorem coefQ_Bgf (n : ℕ) : coefQ n Bgf = colB n := by
  ext a
  rw [coeff_coefQ, colB, PowerSeries.coeff_mk, Bcoef]

theorem colB_zero : colB 0 = 0 := by
  ext a
  rw [colB, PowerSeries.coeff_mk, Bcoef_zero_right, map_zero]

theorem twist_expanded :
    2 * (one 0 sOne * (one 0 (PowerSeries.X ^ 2) * Bgf - 2 * (one 0 PowerSeries.X * (q₀ * Bgf)) +
        q₀ * (q₀ * Bgf) - one 0 PowerSeries.X * (q₀ * one 1 1))) =
      -(2 * (one 0 PowerSeries.X * (q₀ * one 1 hser))) +
        one 0 (PowerSeries.X ^ 2) * (q₀ * one 1 hser) +
        one 0 PowerSeries.X * (q₀ * (q₀ * one 1 hser)) := by
  have h := twist_identity
  rw [aS, uS] at h
  simp only [map_pow, map_one, one_X]
  linear_combination h

/-- The coefficient of `q^{n+2}` of the twist identity. -/
theorem twist_rec (n : ℕ) :
    2 * (sOne * (PowerSeries.X ^ 2 * colB (n + 2) - 2 * (PowerSeries.X * colB (n + 1)) + colB n)) =
      -(2 * (PowerSeries.X * PowerSeries.C (halfBinom (n + 1)))) +
        PowerSeries.X ^ 2 * PowerSeries.C (halfBinom (n + 1)) +
        PowerSeries.X * PowerSeries.C (halfBinom n) := by
  have h := congrArg (coefQ (n + 2)) twist_expanded
  simp only [two_mul, map_add, map_sub, map_neg, coefQ_one0_mul, coefQ_X1_mul_succ, coefQ_one1,
    coefQ_Bgf, hser, PowerSeries.coeff_mk, PowerSeries.coeff_one] at h
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, map_zero, mul_zero,
    sub_zero] at h
  linear_combination h

/-- The coefficient of `q¹` of the twist identity, divided by `p`. -/
theorem twist_one : 2 * (sOne * (PowerSeries.X * colB 1 - 1)) = -(2 - PowerSeries.X) := by
  have h := congrArg (coefQ 1) twist_expanded
  simp only [two_mul, map_add, map_sub, map_neg, coefQ_one0_mul, coefQ_X1_mul_succ,
    coefQ_X1_mul_zero, coefQ_one1, coefQ_Bgf, colB_zero, hser, PowerSeries.coeff_mk] at h
  have h0 : halfBinom 0 = 1 := by simp [halfBinom, gbinom]
  rw [h0, PowerSeries.coeff_zero_one] at h
  simp only [map_one, mul_zero, sub_zero, add_zero, mul_one] at h
  refine mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ)) ?_
  linear_combination h

/-- `U_n(p) = ∑_{i<n} (n-i) h_i p^i`. -/
noncomputable def Useries (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k < n then ((n : ℚ) - k) * halfBinom k else 0

theorem Useries_zero : Useries 0 = 0 := by
  ext k
  simp [Useries]

theorem Useries_diff (n : ℕ) :
    Useries (n + 2) - 2 * Useries (n + 1) + Useries n =
      PowerSeries.C (halfBinom (n + 1)) * PowerSeries.X ^ (n + 1) := by
  ext k
  rw [map_add, map_sub, two_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  simp only [Useries, PowerSeries.coeff_mk]
  by_cases h1 : k < n
  · rw [if_pos (by omega), if_pos (by omega), if_pos h1, if_neg (by omega)]
    push_cast
    ring
  · by_cases h2 : k = n
    · subst h2
      rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      push_cast
      ring
    · by_cases h3 : k = n + 1
      · subst h3
        rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
        push_cast
        ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h3]
        ring

theorem Useries_one : Useries 1 = 1 := by
  ext k
  rw [Useries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hk : k = 0
  · subst hk
    simp [halfBinom, gbinom]
  · rw [if_neg (by omega), if_neg hk]

/-- Step 1 of Lemma 3.5 (sphere/paper.tex l.887–889): `P_n(X) = √(X(X-1)) f_n(X)` is a
polynomial of degree at most `n`, in the reversed form `p^n P_n(1/p)`. -/
theorem step1_poly (n : ℕ) :
    2 * (sOne * (PowerSeries.X ^ n * colB n - (n : PowerSeries ℚ))) =
      -((2 - PowerSeries.X) * Useries n - PowerSeries.X * Useries (n - 1)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [colB_zero, Useries_zero]
  | one =>
    have h := twist_one
    simp only [pow_one, Nat.cast_one, Nat.sub_self, Useries_zero, Useries_one, mul_zero, sub_zero,
      mul_one]
    exact h
  | more n ih0 ih1 =>
    have hr := twist_rec n
    have hU := Useries_diff n
    have hV : Useries (n + 1) - 2 * Useries n + Useries (n - 1) =
        PowerSeries.C (halfBinom n) * PowerSeries.X ^ n := by
      cases n with
      | zero =>
        rw [show (0 : ℕ) - 1 = 0 from rfl, Useries_zero, Useries_one]
        simp [halfBinom, gbinom]
      | succ m => exact Useries_diff m
    simp only [Nat.add_sub_cancel] at ih1 ⊢
    rw [show n + 2 - 1 = n + 1 from rfl]
    push_cast at ih1 ⊢
    linear_combination PowerSeries.X ^ n * hr + 2 * ih1 - ih0 + (2 - PowerSeries.X) * hU -
      PowerSeries.X * hV

theorem coeff_Useries_of_le {n k : ℕ} (h : n ≤ k) : PowerSeries.coeff k (Useries n) = 0 := by
  rw [Useries, PowerSeries.coeff_mk, if_neg (by omega)]

end Virasoro.Sphere
