import Virasoro.Sphere.Proofs.Sec3SaddleI0b
import Virasoro.Sphere.Proofs.Sec3SaddleEnv

/-!
# Sphere paper Lemma 3.4(iii): `z d𝓘₀/dz = 2∑_m a_m² z^m` (`sphere/paper.tex` l.800–804)

By stationarity (`envelope_identity`) and the saddle-point equations (`coeff_aSer`), the
coefficient of `z^K` of `z d/dz` of the truncation `PhiK K` is that of `2∑_m z^m a_m²`.

Consumer: `Sec3SaddleI0e.lean` (the value `𝓘₀ = log(16q/z)` in part (iii) of
`Stmt_lem_saddle`).
-/

namespace Virasoro.Sphere

open Finset PowerSeries

/-- `θ = z d/dz`. -/
noncomputable def theta : Derivation ℚ (PowerSeries ℚ) (PowerSeries ℚ) :=
  (X : PowerSeries ℚ) • derivative ℚ

theorem theta_apply (f : PowerSeries ℚ) : theta f = X * derivative ℚ f := by
  rw [theta, Derivation.smul_apply, smul_eq_mul]

theorem coeff_theta (f : PowerSeries ℚ) (k : ℕ) : coeff k (theta f) = (k : ℚ) * coeff k f := by
  rw [theta_apply]
  cases k with
  | zero => simp
  | succ j =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem theta_C (a : ℚ) : theta (C a) = 0 := by
  rw [theta_apply, derivative_C, mul_zero]

theorem theta_X_pow (n : ℕ) : theta (X ^ n) = (n : PowerSeries ℚ) * X ^ n := by
  ext k
  rw [coeff_theta, show (n : PowerSeries ℚ) = C (n : ℚ) from (map_natCast _ n).symm, coeff_C_mul,
    coeff_X_pow]
  split_ifs with h
  · rw [h]
  · ring

theorem thetaC_mul (a : ℚ) (f : PowerSeries ℚ) : theta (C a * f) = C a * theta f := by
  rw [Derivation.leibniz, theta_C, smul_zero, add_zero, smul_eq_mul]

theorem theta_term (a : ℚ) (n : ℕ) (f : PowerSeries ℚ) :
    theta (C a * (X ^ n * f)) = C a * ((n : PowerSeries ℚ) * X ^ n * f + X ^ n * theta f) := by
  rw [thetaC_mul, Derivation.leibniz, theta_X_pow]
  simp only [smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
/-- `θ(PhiK K)`, by `envelope_identity`. -/
theorem theta_PhiK (K : ℕ) :
    theta (PhiK K) = 2 * ∑ m ∈ Icc 1 K, X ^ m * (aSer m * aSer m) -
      4 * ∑ m ∈ Icc 1 K, X ^ m * (aSer m + C (1 / (m : ℚ)) * theta (aSer m)) *
        (aSer m - C (halfBinom m) +
          ∑ n ∈ Icc 1 K, (C (Bcoef m n) * C (1 / (n : ℚ))) * (X ^ n * aSer n)) := by
  have h := envelope_identity (R := PowerSeries ℚ) (Icc 1 K) (fun m => X ^ m) aSer
    (fun m => theta (aSer m)) (fun m => C (1 / (m : ℚ))) (fun m => C (halfBinom m))
    (fun m => (m : PowerSeries ℚ)) (fun m n => C (Bcoef m n))
    (fun m n => by rw [Bcoef_symm])
    (fun m hm => by
      have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (mem_Icc.1 hm).1; omega)
      rw [show (m : PowerSeries ℚ) = C (m : ℚ) from (map_natCast _ m).symm, ← map_mul,
        mul_one_div_cancel hm0, map_one])
    (fun m n => pow_add _ _ _)
  beta_reduce at h
  have s1 : theta (∑ n ∈ Icc 1 K, C (1 / (n : ℚ)) * (X ^ n * (aSer n * aSer n))) =
      ∑ n ∈ Icc 1 K, C (1 / (n : ℚ)) * ((n : PowerSeries ℚ) * X ^ n * (aSer n * aSer n) +
        X ^ n * (theta (aSer n) * aSer n + aSer n * theta (aSer n))) := by
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [theta_term, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have s2 : theta (∑ n ∈ Icc 1 K, C (2 * halfBinom n * (1 / (n : ℚ))) * (X ^ n * aSer n)) =
      ∑ n ∈ Icc 1 K, (2 * C (halfBinom n) * C (1 / (n : ℚ))) *
        ((n : PowerSeries ℚ) * X ^ n * aSer n + X ^ n * theta (aSer n)) := by
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [theta_term, map_mul, map_mul, map_ofNat]
  have s3 : theta (∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K,
        C (-(Bcoef m n * (1 / (m : ℚ)) * (1 / (n : ℚ)))) * (X ^ (m + n) * (aSer m * aSer n))) =
      ∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K, (-(C (Bcoef m n) * C (1 / (m : ℚ)) * C (1 / (n : ℚ)))) *
        (((m : PowerSeries ℚ) + (n : PowerSeries ℚ)) * X ^ (m + n) * (aSer m * aSer n) +
          X ^ (m + n) * (theta (aSer m) * aSer n + aSer m * theta (aSer n))) := by
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [theta_term, Derivation.leibniz, map_neg, map_mul, map_mul, Nat.cast_add]
    simp only [smul_eq_mul]
    ring
  have hC : theta (PhiK K) =
      -2 * theta (∑ n ∈ Icc 1 K, C (1 / (n : ℚ)) * (X ^ n * (aSer n * aSer n))) +
        2 * (theta (∑ n ∈ Icc 1 K, C (2 * halfBinom n * (1 / (n : ℚ))) * (X ^ n * aSer n)) +
          theta (∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K,
            C (-(Bcoef m n * (1 / (m : ℚ)) * (1 / (n : ℚ)))) *
              (X ^ (m + n) * (aSer m * aSer n)))) := by
    rw [PhiK, map_add, thetaC_mul, thetaC_mul, map_add, map_neg, map_ofNat]
  rw [hC, s1, s2, s3]
  exact h

/-- The saddle-point equation, truncated: `a_m - h_m + ∑_{n≤K} (B_{m,n}/n) z^n a_n` has
`z`-order `> K`. -/
theorem Delta_dvd (m K : ℕ) :
    (X : PowerSeries ℚ) ^ (K + 1) ∣ aSer m - C (halfBinom m) +
      ∑ n ∈ Icc 1 K, (C (Bcoef m n) * C (1 / (n : ℚ))) * (X ^ n * aSer n) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  rw [map_add, map_sub, coeff_C, map_sum, coeff_aSer m j]
  have h1 : ∀ n ∈ Icc 1 K, coeff j ((C (Bcoef m n) * C (1 / (n : ℚ))) * (X ^ n * aSer n)) =
      if n ≤ j then Bcoef m n / (n : ℚ) * coeff (j - n) (aSer n) else 0 := by
    intro n _
    rw [← map_mul, coeff_C_mul, coeff_X_pow_mul']
    split_ifs
    · ring
    · rw [mul_zero]
  rw [sum_congr rfl h1, ← sum_filter,
    show (Icc 1 K).filter (fun n => n ≤ j) = Icc 1 j from by
      ext x; simp only [mem_filter, mem_Icc]; omega]
  ring

/-- `K [z^K]PhiK K = 2∑_{m≤K} [z^K](z^m a_m²)`. -/
theorem coeff_theta_PhiK (K : ℕ) :
    (K : ℚ) * coeff K (PhiK K) = 2 * ∑ m ∈ Icc 1 K, coeff K (X ^ m * (aSer m * aSer m)) := by
  rw [← coeff_theta, theta_PhiK, map_sub,
    show (2 : PowerSeries ℚ) = C 2 from (map_ofNat _ 2).symm,
    show (4 : PowerSeries ℚ) = C 4 from (map_ofNat _ 4).symm, coeff_C_mul, coeff_C_mul, map_sum,
    map_sum]
  have hz : ∀ m ∈ Icc 1 K, coeff K (X ^ m * (aSer m + C (1 / (m : ℚ)) * theta (aSer m)) *
      (aSer m - C (halfBinom m) +
        ∑ n ∈ Icc 1 K, (C (Bcoef m n) * C (1 / (n : ℚ))) * (X ^ n * aSer n))) = 0 := by
    intro m _
    obtain ⟨V, hV⟩ := Delta_dvd m K
    rw [hV, show X ^ m * (aSer m + C (1 / (m : ℚ)) * theta (aSer m)) * (X ^ (K + 1) * V) =
      X ^ (K + 1) * (X ^ m * (aSer m + C (1 / (m : ℚ)) * theta (aSer m)) * V) by ring,
      coeff_X_pow_mul', if_neg (by omega)]
  rw [sum_congr rfl hz, sum_const_zero, mul_zero, sub_zero]

end Virasoro.Sphere
