import Virasoro.Sphere.Proofs.Sec3BergmanInnerRows

/-!
# Sphere paper Lemma 3.5, Step 2, inner patch: `√(x₁(x₁-z)) z^{n-1} f_n(x₁/z) = z^n P_n(x₁/z)`
(`sphere/paper.tex` l.885–887, l.894–896)

Step 1 with `X = x₁/z`, as identities of power series in `z` with `u = 1/x₁`:
`n √(1-zu) - ½ R_n(zu) = (zu)^n √(1-zu) ∑_m B_{m,n} (zu)^m`, where `R_n(p) = -2 p^n P_n(1/p)`.

Consumer: `sub_bergman_inner`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `∑_m B_{m,n} p^m` with complex coefficients. -/
noncomputable def colBC (n : ℕ) : PowerSeries ℂ := (colB n).map (algebraMap ℚ ℂ)

/-- `R_n(p) = -2 p^n P_n(1/p)` with complex coefficients. -/
noncomputable def RrevC (n : ℕ) : PowerSeries ℂ := (Rrev n).map (algebraMap ℚ ℂ)

/-- `∑_m B_{m+1,l+1} z^m x^{-(m+2)}`. -/
noncomputable def Psi (x : ℂ) (l : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => ((Bcoef (m + 1) (l + 1) : ℚ) : ℂ) * x⁻¹ ^ (m + 2)

theorem half_two : (2 : PowerSeries ℂ) * C (1 / 2 : ℂ) = 1 := by
  rw [← map_ofNat (C (R := ℂ)) 2, ← map_mul]
  norm_num

/-- Step 1 rescaled (l.885–887): `n√(1-zu) - ½R_n(zu) = z^n u^n √(1-zu) ∑_m B_{m,n}(zu)^m`. -/
theorem step1_rescaled (u : ℂ) (n : ℕ) :
    C ((n : ℕ) : ℂ) * rescale u sOneC - C (1 / 2 : ℂ) * rescale u (RrevC n) =
      X ^ n * (C (u ^ n) * (rescale u sOneC * rescale u (colBC n))) := by
  have h : 2 * (sOne * (X ^ n * colB n - (n : PowerSeries ℚ))) = -Rrev n := by
    rw [Rrev]
    exact step1_poly n
  have h2 := congrArg (fun f => rescale u (f.map (algebraMap ℚ ℂ))) h
  simp only [map_mul, map_sub, map_neg, map_pow, PowerSeries.map_X, rescale_X, map_ofNat,
    map_natCast] at h2
  have hn : (C ((n : ℕ) : ℂ) : PowerSeries ℂ) = (n : PowerSeries ℂ) := map_natCast _ n
  have hp : (C u * X : PowerSeries ℂ) ^ n = C (u ^ n) * X ^ n := by rw [mul_pow, ← map_pow]
  rw [hp] at h2
  rw [hn, sOneC, colBC, RrevC]
  linear_combination (-(C (1 / 2 : ℂ))) * h2 +
    (rescale u (sOne.map (algebraMap ℚ ℂ)) *
      (C (u ^ n) * X ^ n * rescale u ((colB n).map (algebraMap ℚ ℂ)) - (n : PowerSeries ℂ))) *
      half_two

theorem Psi_identity (x : ℂ) (l : ℕ) :
    X ^ (l + 2) * Psi x l = C x⁻¹ * (X ^ (l + 1) * rescale x⁻¹ (colBC (l + 1))) := by
  ext i
  rw [coeff_X_pow_mul', coeff_C_mul, coeff_X_pow_mul']
  by_cases h : l + 2 ≤ i
  · rw [if_pos h, if_pos (by omega), coeff_rescale, Psi, coeff_mk, colBC, coeff_map, colB,
      coeff_mk, eq_ratCast, show i - (l + 2) + 1 = i - (l + 1) by omega,
      show i - (l + 2) + 2 = (i - (l + 1)) + 1 by omega, pow_succ]
    ring
  · rw [if_neg h]
    by_cases h' : l + 1 ≤ i
    · rw [if_pos h', coeff_rescale, colBC, coeff_map, colB, coeff_mk,
        show i - (l + 1) = 0 by omega, Bcoef_zero_left]
      simp
    · rw [if_neg h', mul_zero]

/-- `x√(1-z/x) · ∑_m B_{m+1,l+1} z^{m+l+2} x^{-(m+2)} = x^{l+1}((l+1)√(1-z/x) - ½R_{l+1}(z/x))`
(l.894–896). -/
theorem inner_K {x : ℂ} (hx : x ≠ 0) (l : ℕ) :
    C x * sqrtZ x * (X ^ (l + 2) * Psi x l) =
      C (x ^ (l + 1)) * (C (((l + 1 : ℕ)) : ℂ) * sqrtZ x -
        C (1 / 2 : ℂ) * rescale x⁻¹ (RrevC (l + 1))) := by
  have hxu : (C x * C x⁻¹ : PowerSeries ℂ) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  have hxn : (C (x ^ (l + 1)) * C (x⁻¹ ^ (l + 1)) : PowerSeries ℂ) = 1 := by
    rw [← map_mul, ← mul_pow, mul_inv_cancel₀ hx, one_pow, map_one]
  rw [Psi_identity, sqrtZ, step1_rescaled]
  linear_combination (rescale x⁻¹ sOneC * X ^ (l + 1) * rescale x⁻¹ (colBC (l + 1))) * hxu -
    (X ^ (l + 1) * rescale x⁻¹ sOneC * rescale x⁻¹ (colBC (l + 1))) * hxn

/-- `(l+1)√(1-z/x) - ½R_{l+1}(z/x) = O(z^{l+1})`. -/
theorem inner_vanish (x : ℂ) (D : PowerSeries ℂ) {j l : ℕ} (h : j ≤ l) :
    coeff j ((C (((l + 1 : ℕ)) : ℂ) * sqrtZ x - C (1 / 2 : ℂ) * rescale x⁻¹ (RrevC (l + 1))) * D)
      = 0 := by
  rw [sqrtZ, step1_rescaled, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

theorem sum_guard (i l : ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ m ∈ range i, (if m + l + 2 ≤ i then f m (i - (m + l + 2)) else 0) =
      if l + 2 ≤ i then ∑ k ∈ range (i - (l + 2) + 1), f k (i - (l + 2) - k) else 0 := by
  by_cases h : l + 2 ≤ i
  · rw [if_pos h, ← Finset.sum_subset (Finset.range_mono (by omega : i - (l + 2) + 1 ≤ i))
      (fun m _ hm => if_neg (by have := Finset.mem_range.not.1 hm; omega))]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [if_pos (by omega), show i - (k + l + 2) = i - (l + 2) - k by omega]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun m _ => if_neg (by omega)

theorem coeff_mul_congr {F G G' : PowerSeries ℂ} {j : ℕ}
    (h : ∀ i ≤ j, coeff i G = coeff i G') : coeff j (F * G) = coeff j (F * G') := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = j := by simpa using hp
  rw [h p.2 (by omega)]

end Virasoro.Sphere
