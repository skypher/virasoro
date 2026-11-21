import Virasoro.Sphere.Proofs.Sec3SaddlePde2

/-!
# Sphere paper Lemma 3.4(i), the `σ²` identity in coefficients (`sphere/paper.tex` l.742–745)

`q∂_q(T₁ - U) + r∂_r(T₂ - U) = B(p,q)B(p,r)` and its coefficient of `p^k q^m r^l`, `k ≥ 1`:
`m(B_{k+m,l} - B_{m,l}) + l(B_{k+l,m} - B_{m,l}) = ∑_{n=0}^k B_{n,m}B_{k-n,l}`.

Consumer: the `σ²` component of `pdeZero k S0` in part (i) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

set_option maxHeartbeats 1600000 in
/-- The third identity of l.742–745, as an identity of series in `(p,q,r)`. -/
theorem sigma2_series :
    MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1 (T1 - Uq) +
      MvPowerSeries.X 2 * MvPowerSeries.pderiv ℚ 2 (T2 - Uq) = P1 * P2 := by
  set δq := MvPowerSeries.pderiv ℚ (1 : Fin 3) with hδq
  set δr := MvPowerSeries.pderiv ℚ (2 : Fin 3) with hδr
  have q0 : δq (MvPowerSeries.X 0) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have q1 : δq (MvPowerSeries.X 1) = 1 := MvPowerSeries.pderiv_X_self
  have q2 : δq (MvPowerSeries.X 2) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have r0 : δr (MvPowerSeries.X 0) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have r1 : δr (MvPowerSeries.X 1) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have r2 : δr (MvPowerSeries.X 2) = 1 := MvPowerSeries.pderiv_X_self
  have qa2 : δq (aS 2) = 0 := pderiv_one_ne 2 1 (by decide) _
  have ra1 : δr (aS 1) = 0 := pderiv_one_ne 1 2 (by decide) _
  have qP2 : δq P2 = 0 := pderiv_P2
  have rP1 : δr P1 = 0 := pderiv_P1
  have hdb : 2 * aS 1 * δq (aS 1) = -1 := by
    have := congrArg δq (show aS (1 : Fin 3) * aS 1 = 1 - MvPowerSeries.X 1 by rw [← sq, aS_sq])
    simp only [Derivation.leibniz, map_sub, q1, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  have hdc : 2 * aS 2 * δr (aS 2) = -1 := by
    have := congrArg δr (show aS (2 : Fin 3) * aS 2 = 1 - MvPowerSeries.X 2 by rw [← sq, aS_sq])
    simp only [Derivation.leibniz, map_sub, r2, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  have h3 : P3 * ((aS 1 * aS 2 + aS 1 * aS 2) * ((aS 1 + aS 2) * (aS 1 + aS 2))) =
      -(MvPowerSeries.X 1 * MvPowerSeries.X 2) := by linear_combination P3_rel
  have hdqB3 : δq P3 * (2 * aS 1 * aS 2 * (aS 1 + aS 2) ^ 2) +
      P3 * (2 * δq (aS 1) * aS 2 * (aS 1 + aS 2) ^ 2 +
        2 * aS 1 * aS 2 * (2 * (aS 1 + aS 2) * δq (aS 1))) = -MvPowerSeries.X 2 := by
    have := congrArg δq h3
    simp only [Derivation.leibniz, map_add, map_neg, smul_eq_mul, q1, q2, qa2] at this
    linear_combination this
  have hdrB3 : δr P3 * (2 * aS 1 * aS 2 * (aS 1 + aS 2) ^ 2) +
      P3 * (2 * aS 1 * δr (aS 2) * (aS 1 + aS 2) ^ 2 +
        2 * aS 1 * aS 2 * (2 * (aS 1 + aS 2) * δr (aS 2))) = -MvPowerSeries.X 1 := by
    have := congrArg δr h3
    simp only [Derivation.leibniz, map_add, map_neg, smul_eq_mul, r1, r2, ra1] at this
    linear_combination this
  have hdqT1 : T1 + (MvPowerSeries.X 1 - MvPowerSeries.X 0) * δq T1 =
      MvPowerSeries.X 0 * δq P3 := by
    have := congrArg δq T1_rel
    simp only [Derivation.leibniz, map_sub, smul_eq_mul, q0, q1, qP2] at this
    linear_combination this
  have hdrT2 : T2 + (MvPowerSeries.X 2 - MvPowerSeries.X 0) * δr T2 =
      MvPowerSeries.X 0 * δr P3 := by
    have := congrArg δr T2_rel
    simp only [Derivation.leibniz, map_sub, smul_eq_mul, r0, r2, rP1] at this
    linear_combination this
  have hdqU : (1 - MvPowerSeries.X 0) * δq Uq = MvPowerSeries.X 0 * δq P3 := by
    have := congrArg δq Uq_rel
    simp only [Derivation.leibniz, map_sub, smul_eq_mul, q0, Derivation.map_one_eq_zero] at this
    linear_combination this
  have hdrU : (1 - MvPowerSeries.X 0) * δr Uq = MvPowerSeries.X 0 * δr P3 := by
    have := congrArg δr Uq_rel
    simp only [Derivation.leibniz, map_sub, smul_eq_mul, r0, Derivation.map_one_eq_zero] at this
    linear_combination this
  let φ := algebraMap (MvPowerSeries (Fin 3) ℚ) (FractionRing (MvPowerSeries (Fin 3) ℚ))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (MvPowerSeries (Fin 3) ℚ)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hne : ∀ y : MvPowerSeries (Fin 3) ℚ, y ≠ 0 → φ y ≠ 0 :=
    fun y hy => (map_ne_zero_iff φ hφ).2 hy
  have key := alg_sigma2 (φ (aS 0)) (φ (aS 1)) (φ (aS 2)) (φ (MvPowerSeries.X 0))
    (φ (MvPowerSeries.X 1)) (φ (MvPowerSeries.X 2)) (φ P1) (φ P2) (φ P3) (φ T1) (φ T2) (φ Uq)
    (φ (δq (aS 1))) (φ (δr (aS 2))) (φ (δq P3)) (φ (δr P3)) (φ (δq T1)) (φ (δr T2))
    (φ (δq Uq)) (φ (δr Uq))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (0 : Fin 3)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (1 : Fin 3)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (2 : Fin 3)))
    (by rw [← map_sub]; exact hne _ (X_sub_X_ne 1 0 (by decide)))
    (by rw [← map_sub]; exact hne _ (X_sub_X_ne 2 0 (by decide)))
    (by rw [← map_sub]; exact hne _ (X_sub_X_ne 1 2 (by decide)))
    (hne _ (aS_ne_zero 0)) (hne _ (aS_ne_zero 1)) (hne _ (aS_ne_zero 2))
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ P1_rel)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ P2_rel)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ P3_rel)
    (by simpa only [map_mul, map_sub] using congrArg φ T1_rel)
    (by simpa only [map_mul, map_sub] using congrArg φ T2_rel)
    (by simpa only [map_mul, map_sub, map_one] using congrArg φ Uq_rel)
    (by simpa only [map_mul, map_neg, map_one, map_ofNat] using congrArg φ hdb)
    (by simpa only [map_mul, map_neg, map_one, map_ofNat] using congrArg φ hdc)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ hdqB3)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ hdrB3)
    (by simpa only [map_mul, map_sub, map_add] using congrArg φ hdqT1)
    (by simpa only [map_mul, map_sub, map_add] using congrArg φ hdrT2)
    (by simpa only [map_mul, map_sub, map_one] using congrArg φ hdqU)
    (by simpa only [map_mul, map_sub, map_one] using congrArg φ hdrU)
  exact hφ (by simpa only [map_mul, map_sub, map_add] using key)

/-- The coefficient of `p^k q^m r^l` in the third identity. -/
theorem Bcoef_star (k m l : ℕ) (hk : 1 ≤ k) :
    (m : ℚ) * (Bcoef (k + m) l - Bcoef m l) + (l : ℚ) * (Bcoef (k + l) m - Bcoef m l) =
      ∑ n ∈ range (k + 1), Bcoef n m * Bcoef (k - n) l := by
  set x : Fin 3 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 m + Finsupp.single 2 l with hx
  have hx0 : x 0 = k := by simp [hx]
  have hx1 : x 1 = m := by simp [hx]
  have hx2 : x 2 = l := by simp [hx]
  have h := congrArg (MvPowerSeries.coeff x) sigma2_series
  rw [map_add, coeff_X_mul_pderiv, coeff_X_mul_pderiv, map_sub, map_sub, coeff_T1, coeff_T2,
    coeff_Uq, hx0, hx1, hx2] at h
  simp only [if_pos hk] at h
  rw [h, MvPowerSeries.coeff_mul]
  refine (sum_antidiagonal_eq_range x k (fun n => Finsupp.single 0 n + Finsupp.single 1 m)
    ?_ ?_ (fun a b => MvPowerSeries.coeff a P1 * MvPowerSeries.coeff b P2) ?_).trans
    (sum_congr rfl fun n hn => ?_)
  · intro n n' h
    have := DFunLike.congr_fun h 0
    simpa using this
  · intro n hn
    rw [Finsupp.le_def]
    intro i
    fin_cases i <;> simp [hx, hn]
  · intro a b hab hne
    rw [coeff_P1, coeff_P2]
    by_cases h2 : a 2 = 0
    · by_cases h1 : b 1 = 0
      · exfalso
        have e0 := DFunLike.congr_fun hab 0
        have e1 := DFunLike.congr_fun hab 1
        rw [Finsupp.add_apply] at e0 e1
        refine hne (a 0) (by omega) ?_
        ext i
        fin_cases i
        · simp
        · simp
          omega
        · simpa using h2
      · rw [if_neg h1, mul_zero]
    · rw [if_neg h2, zero_mul]
  · have hn' : n ≤ k := by have := mem_range.1 hn; omega
    rw [coeff_P1, coeff_P2]
    simp [hx]

end Virasoro.Sphere
