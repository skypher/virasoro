import Virasoro.Sphere.Proofs.Sec3SaddleI0a

/-!
# Sphere paper Lemma 3.4(iii): the saddle value in terms of `a_m(z)` (`sphere/paper.tex` l.694)

At `σ = σ_*`, `σ̄ = -σ_*`, with `σ_{*,m} = i a_m z^m/m`:
`𝓘₀ = -2∑_m a_m² z^m/m + 2(∑_m 2h_m a_m z^m/m - ∑_{m,n} B_{m,n} a_m a_n z^{m+n}/(mn))`.
The coefficient of `z^k` is that of the truncation `PhiK k` to `m, n ≤ k`.

Consumer: `Sec3SaddleI0c.lean` (the value `𝓘₀ = log(16q/z)` in part (iii) of
`Stmt_lem_saddle`).
-/

namespace Virasoro.Sphere

open Finset

/-- The truncation to `m, n ≤ K` of
`-2∑_m a_m² z^m/m + 2(∑_m 2h_m a_m z^m/m - ∑_{m,n} B_{m,n} a_m a_n z^{m+n}/(mn))`. -/
noncomputable def PhiK (K : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (-2) * ∑ n ∈ Icc 1 K,
      PowerSeries.C (1 / (n : ℚ)) * (PowerSeries.X ^ n * (aSer n * aSer n)) +
    PowerSeries.C 2 *
      (∑ n ∈ Icc 1 K, PowerSeries.C (2 * halfBinom n * (1 / (n : ℚ))) *
          (PowerSeries.X ^ n * aSer n) +
        ∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K,
          PowerSeries.C (-(Bcoef m n * (1 / (m : ℚ)) * (1 / (n : ℚ)))) *
            (PowerSeries.X ^ (m + n) * (aSer m * aSer n)))

theorem sigmaStar_eq (m : ℕ+) :
    sigmaStar m = PowerSeries.C (Complex.I * (1 / ((m : ℕ) : ℂ))) *
      ((aSer m).map (algebraMap ℚ ℂ) * PowerSeries.X ^ (m : ℕ)) := by
  rw [sigmaStar, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, mul_assoc]

theorem coeff_smul_sigmaStar_mul (s t : ℂ) (μ ν : ℕ+) (k : ℕ) :
    PowerSeries.coeff k ((s • sigmaStar μ) * (t • sigmaStar ν)) =
      -(s * t * (1 / ((μ : ℕ) : ℂ)) * (1 / ((ν : ℕ) : ℂ))) *
        (if (μ : ℕ) + ν ≤ k then
          ((PowerSeries.coeff (k - ((μ : ℕ) + ν)) (aSer μ * aSer ν) : ℚ) : ℂ) else 0) := by
  have hI : (-(s * t * (1 / ((μ : ℕ) : ℂ)) * (1 / ((ν : ℕ) : ℂ))) : ℂ) =
      s * (Complex.I * (1 / ((μ : ℕ) : ℂ))) * (t * (Complex.I * (1 / ((ν : ℕ) : ℂ)))) := by
    rw [show s * (Complex.I * (1 / ((μ : ℕ) : ℂ))) * (t * (Complex.I * (1 / ((ν : ℕ) : ℂ)))) =
      (Complex.I * Complex.I) * (s * t * (1 / ((μ : ℕ) : ℂ)) * (1 / ((ν : ℕ) : ℂ))) by ring,
      Complex.I_mul_I]
    ring
  have e : (s • sigmaStar μ) * (t • sigmaStar ν) =
      PowerSeries.C (-(s * t * (1 / ((μ : ℕ) : ℂ)) * (1 / ((ν : ℕ) : ℂ)))) *
        (((aSer μ * aSer ν).map (algebraMap ℚ ℂ)) * PowerSeries.X ^ ((μ : ℕ) + ν)) := by
    rw [sigmaStar_eq, sigmaStar_eq, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, hI,
      map_mul (PowerSeries.map (algebraMap ℚ ℂ))]
    simp only [map_mul, pow_add]
    ring
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  split_ifs
  · rw [PowerSeries.coeff_map]
    rfl
  · rfl

theorem coeff_PhiK (k : ℕ) :
    ((PowerSeries.coeff k (PhiK k) : ℚ) : ℂ) =
      -2 * ∑ n ∈ Icc 1 k, (1 / (n : ℂ)) *
          (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n * aSer n) : ℚ) : ℂ) else 0) +
        2 * (∑ n ∈ Icc 1 k, (2 * (halfBinom n : ℂ) * (1 / (n : ℂ))) *
            (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n) : ℚ) : ℂ) else 0) +
          ∑ m ∈ Icc 1 k, ∑ n ∈ Icc 1 k,
            (-((Bcoef m n : ℂ) * (1 / (m : ℂ)) * (1 / (n : ℂ)))) *
              (if m + n ≤ k then
                ((PowerSeries.coeff (k - (m + n)) (aSer m * aSer n) : ℚ) : ℂ) else 0)) := by
  rw [PhiK]
  simp only [map_add, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one, apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_zero]

set_option maxHeartbeats 800000 in
/-- The coefficient of `z^k` of `𝓘₀` at `(σ_*, -σ_*)`. -/
theorem coeff_I0def_sigmaStar (k : ℕ) :
    PowerSeries.coeff k (I0def sigmaStar (fun m => -sigmaStar m)) =
      ((PowerSeries.coeff k (PhiK k) : ℚ) : ℂ) := by
  have hT1 : PowerSeries.coeff k (PowerSeries.mk fun k =>
      -2 * ∑ᶠ m : ℕ+, ((m : ℕ) : ℂ) *
        PowerSeries.coeff (k + (m : ℕ)) (sigmaStar m * -sigmaStar m)) =
      -2 * ∑ n ∈ Icc 1 k, (1 / (n : ℂ)) *
        (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n * aSer n) : ℚ) : ℂ) else 0) := by
    have hterm : ∀ μ : ℕ+, ((μ : ℕ) : ℂ) *
        PowerSeries.coeff (k + (μ : ℕ)) (sigmaStar μ * -sigmaStar μ) =
        (1 / ((μ : ℕ) : ℂ)) * (if (μ : ℕ) ≤ k then
          ((PowerSeries.coeff (k - (μ : ℕ)) (aSer μ * aSer μ) : ℚ) : ℂ) else 0) := by
      intro μ
      have hμ0 : ((μ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 μ.pos.ne'
      have h := coeff_smul_sigmaStar_mul 1 (-1) μ μ (k + (μ : ℕ))
      simp only [one_smul, neg_smul] at h
      rw [h]
      by_cases hk : (μ : ℕ) ≤ k
      · rw [if_pos (by omega), if_pos hk, show k + (μ : ℕ) - ((μ : ℕ) + μ) = k - μ by omega]
        field_simp
      · rw [if_neg (by omega), if_neg hk]
        simp
    rw [PowerSeries.coeff_mk, finsum_pnat _ k (fun μ hμ => by
      rw [hterm μ, if_neg (by omega), mul_zero]), sum_pIcc]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    have hn1 := mem_Icc.1 hn
    have hcoe : ((n.toPNat' : ℕ+) : ℕ) = n := by rw [Nat.toPNat'_coe, if_pos (by omega)]
    rw [hterm, hcoe]
  have hT2 : ∀ s : ℂ, s * s = 1 →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m => s • sigmaStar m)
        (Sq (fun m => s * Acoef m) (fun m n => (Bcoef m n : ℂ)))) =
      ∑ n ∈ Icc 1 k, (2 * (halfBinom n : ℂ) * (1 / (n : ℂ))) *
          (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n) : ℚ) : ℂ) else 0) +
        ∑ m ∈ Icc 1 k, ∑ n ∈ Icc 1 k,
          (-((Bcoef m n : ℂ) * (1 / (m : ℂ)) * (1 / (n : ℂ)))) *
            (if m + n ≤ k then
              ((PowerSeries.coeff (k - (m + n)) (aSer m * aSer n) : ℚ) : ℂ) else 0) := by
    intro s hs
    rw [coeff_subst_Sq _ (smul_sigmaStar_dvd s), sum_pIcc, sum_pIcc]
    congr 1
    · refine sum_congr rfl fun n hn => ?_
      have hn1 := mem_Icc.1 hn
      have hcoe : ((n.toPNat' : ℕ+) : ℕ) = n := by rw [Nat.toPNat'_coe, if_pos (by omega)]
      rw [PowerSeries.coeff_smul, coeff_sigmaStar, hcoe, Acoef, smul_eq_mul]
      rw [show s * (-2 * Complex.I * (halfBinom n : ℂ)) * (s * (Complex.I * (1 / (n : ℂ)) *
          (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n) : ℚ) : ℂ) else 0))) =
        -((s * s) * (Complex.I * Complex.I)) * (2 * (halfBinom n : ℂ) * (1 / (n : ℂ)) *
          (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n) : ℚ) : ℂ) else 0)) by ring,
        hs, Complex.I_mul_I]
      ring
    · refine sum_congr rfl fun m hm => ?_
      have hm1 := mem_Icc.1 hm
      have hcoem : ((m.toPNat' : ℕ+) : ℕ) = m := by rw [Nat.toPNat'_coe, if_pos (by omega)]
      rw [sum_pIcc]
      refine sum_congr rfl fun n hn => ?_
      have hn1 := mem_Icc.1 hn
      have hcoe : ((n.toPNat' : ℕ+) : ℕ) = n := by rw [Nat.toPNat'_coe, if_pos (by omega)]
      rw [coeff_smul_sigmaStar_mul, hcoem, hcoe]
      rw [show (-(s * s * (1 / (m : ℂ)) * (1 / (n : ℂ))) : ℂ) =
        -((s * s) * ((1 / (m : ℂ)) * (1 / (n : ℂ)))) by ring, hs]
      ring
  have e2 : PowerSeries.coeff k (MvPowerSeries.subst sigmaStar S0) =
      ∑ n ∈ Icc 1 k, (2 * (halfBinom n : ℂ) * (1 / (n : ℂ))) *
          (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n) : ℚ) : ℂ) else 0) +
        ∑ m ∈ Icc 1 k, ∑ n ∈ Icc 1 k,
          (-((Bcoef m n : ℂ) * (1 / (m : ℂ)) * (1 / (n : ℂ)))) *
            (if m + n ≤ k then
              ((PowerSeries.coeff (k - (m + n)) (aSer m * aSer n) : ℚ) : ℂ) else 0) := by
    have h2 := hT2 1 (by norm_num)
    simp only [one_smul, one_mul] at h2
    rw [S0_eq_Sq]
    exact h2
  have e3 : PowerSeries.coeff k
      (MvPowerSeries.subst (fun m => -sigmaStar m) (conjSeries S0)) =
      ∑ n ∈ Icc 1 k, (2 * (halfBinom n : ℂ) * (1 / (n : ℂ))) *
          (if n ≤ k then ((PowerSeries.coeff (k - n) (aSer n) : ℚ) : ℂ) else 0) +
        ∑ m ∈ Icc 1 k, ∑ n ∈ Icc 1 k,
          (-((Bcoef m n : ℂ) * (1 / (m : ℂ)) * (1 / (n : ℂ)))) *
            (if m + n ≤ k then
              ((PowerSeries.coeff (k - (m + n)) (aSer m * aSer n) : ℚ) : ℂ) else 0) := by
    have h3 := hT2 (-1) (by norm_num)
    simp only [neg_smul, one_smul, neg_one_mul] at h3
    rw [conj_S0_eq_Sq]
    exact h3
  rw [I0def, map_add, map_add, hT1, e2, e3, coeff_PhiK]
  ring

end Virasoro.Sphere
