import Virasoro.Sphere.Proofs.Sec3SaddleTools
import Virasoro.Sphere.Proofs.Sec3SaddleField
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Sphere paper Lemma 3.4(i), the `σ¹` identity (`sphere/paper.tex` l.739–741)

`(1-p)^{-1/2} B(p,q) = q∂_q(D - V)` with `D = ∑ h_{k+m} p^k q^m`, `(p-q)D = p h(p) - q h(q)`,
and `V = h(q)/(1-p)`; `h_n = [x^n](1-x)^{-1/2}`.  In coefficients:
`∑_{n=0}^k h_n B_{k-n,m} = m(h_{k+m} - h_m)`.

Consumer: the `σ¹` component of `pdeZero k S0` in part (i) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem fin2_single0_iff (x : Fin 2 →₀ ℕ) : x = Finsupp.single 0 (x 0) ↔ x 1 = 0 := by
  constructor
  · intro h
    have := DFunLike.congr_fun h 1
    simpa using this
  · intro h
    ext i
    fin_cases i <;> simp [h]

theorem fin2_single1_iff (x : Fin 2 →₀ ℕ) : x = Finsupp.single 1 (x 1) ↔ x 0 = 0 := by
  constructor
  · intro h
    have := DFunLike.congr_fun h 0
    simpa using this
  · intro h
    ext i
    fin_cases i <;> simp [h]

theorem coeff_one0 (f : PowerSeries ℚ) (x : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff x (one 0 f) = if x 1 = 0 then PowerSeries.coeff (x 0) f else 0 := by
  rw [coeff_one]
  simp only [fin2_single0_iff]

theorem coeff_one1 (f : PowerSeries ℚ) (x : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff x (one 1 f) = if x 0 = 0 then PowerSeries.coeff (x 1) f else 0 := by
  rw [coeff_one]
  simp only [fin2_single1_iff]

/-- `D(p,q) = ∑_{k,m≥0} h_{k+m} p^k q^m`. -/
noncomputable def Dser : MvPowerSeries (Fin 2) ℚ := fun x => halfBinom (x 0 + x 1)

/-- `V(p,q) = ∑_{k,m≥0} h_m p^k q^m`. -/
noncomputable def Vser : MvPowerSeries (Fin 2) ℚ := fun x => halfBinom (x 1)

theorem coeff_Dser (x : Fin 2 →₀ ℕ) : MvPowerSeries.coeff x Dser = halfBinom (x 0 + x 1) := rfl

theorem coeff_Vser (x : Fin 2 →₀ ℕ) : MvPowerSeries.coeff x Vser = halfBinom (x 1) := rfl

theorem fin2_exists (x : Fin 2 →₀ ℕ) :
    ∃ k m, x = Finsupp.single 0 k + Finsupp.single 1 m :=
  ⟨x 0, x 1, by ext i; fin_cases i <;> simp⟩

theorem Dser_rel : (MvPowerSeries.X 0 - MvPowerSeries.X 1) * Dser =
    MvPowerSeries.X 0 * uS 0 - MvPowerSeries.X 1 * uS 1 := by
  ext x
  rw [sub_mul, map_sub, map_sub, coeff_X_mul', coeff_X_mul', coeff_X_mul', coeff_X_mul',
    uS, uS, coeff_one0, coeff_one1]
  obtain ⟨k, m, rfl⟩ := fin2_exists x
  rcases k with _ | k <;> rcases m with _ | m <;>
    simp [coeff_Dser, hser, Finsupp.single_apply]
  rw [show k + 1 + m = k + (m + 1) by omega, sub_self]

theorem Vser_rel : (1 - MvPowerSeries.X 0) * Vser = uS 1 := by
  ext x
  rw [sub_mul, one_mul, map_sub, coeff_X_mul', uS, coeff_one1]
  obtain ⟨k, m, rfl⟩ := fin2_exists x
  rcases k with _ | k <;> simp [coeff_Vser, hser, Finsupp.single_apply]

theorem X0_sub_X1_ne : (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
  simp [MvPowerSeries.coeff_index_single_X] at this

/-- The second identity of l.739–741, as an identity of series in `(p,q)`. -/
theorem uS_mul_Bgf :
    uS 0 * Bgf = MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1 (Dser - Vser) := by
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
  have hdD : (MvPowerSeries.X 0 - MvPowerSeries.X 1) * δ Dser - Dser =
      -uS 1 - MvPowerSeries.X 1 * δ (uS 1) := by
    have := congrArg δ Dser_rel
    simp only [Derivation.leibniz, map_sub, hX0, hX1, hu0, smul_eq_mul] at this
    linear_combination this
  have hdV : (1 - MvPowerSeries.X 0) * δ Vser = δ (uS 1) := by
    have := congrArg δ Vser_rel
    simp only [Derivation.leibniz, map_sub, hX0, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  have hB : Bgf * (2 * aS 0 * aS 1 * (aS 0 + aS 1) ^ 2) =
      -(MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
    have := Bgf_mul_Bden
    rw [Bden, sqrtOneSub_eq_aS, sqrtOneSub_eq_aS] at this
    exact this
  let φ := algebraMap (MvPowerSeries (Fin 2) ℚ) (FractionRing (MvPowerSeries (Fin 2) ℚ))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (MvPowerSeries (Fin 2) ℚ)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hne : ∀ y : MvPowerSeries (Fin 2) ℚ, y ≠ 0 → φ y ≠ 0 :=
    fun y hy => (map_ne_zero_iff φ hφ).2 hy
  have key := alg_sigma1 (φ (aS 0)) (φ (aS 1)) (φ (uS 0)) (φ (uS 1)) (φ (MvPowerSeries.X 0))
    (φ (MvPowerSeries.X 1)) (φ Dser) (φ Vser) (φ Bgf) (φ (δ (aS 1))) (φ (δ (uS 1))) (φ (δ Dser))
    (φ (δ Vser))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (0 : Fin 2)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (1 : Fin 2)))
    (by rw [← map_sub]; exact hne _ X0_sub_X1_ne)
    (hne _ (aS_ne_zero 0)) (hne _ (aS_ne_zero 1))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (0 : Fin 2)))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (1 : Fin 2)))
    (by simpa only [map_mul, map_sub] using congrArg φ Dser_rel)
    (by simpa only [map_mul, map_sub, map_one] using congrArg φ Vser_rel)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ hB)
    (by simpa only [map_mul, map_neg, map_one, map_ofNat] using congrArg φ hdb)
    (by simpa only [map_mul, map_add, map_zero] using congrArg φ hdu)
    (by simpa only [map_mul, map_sub, map_neg] using congrArg φ hdD)
    (by simpa only [map_mul, map_sub, map_one] using congrArg φ hdV)
  exact hφ (by simpa only [map_mul, map_sub] using key)

/-- `∑_{n=0}^k h_n B_{k-n,m} = m(h_{k+m} - h_m)`. -/
theorem sum_halfBinom_Bcoef (k m : ℕ) :
    ∑ n ∈ range (k + 1), halfBinom n * Bcoef (k - n) m =
      (m : ℚ) * (halfBinom (k + m) - halfBinom m) := by
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m)) uS_mul_Bgf
  have hx0 : (Finsupp.single 0 k + Finsupp.single 1 m : Fin 2 →₀ ℕ) 0 = k := by simp
  have hx1 : (Finsupp.single 0 k + Finsupp.single 1 m : Fin 2 →₀ ℕ) 1 = m := by simp
  rw [uS, coeff_one_mul, coeff_X_mul_pderiv, map_sub, coeff_Dser, coeff_Vser, hx0, hx1] at h
  rw [← h]
  refine sum_congr rfl fun n hn => ?_
  have hn' : n ≤ k := by have := mem_range.1 hn; omega
  rw [hser, PowerSeries.coeff_mk, Bcoef,
    show (Finsupp.single 0 k + Finsupp.single 1 m - Finsupp.single 0 n : Fin 2 →₀ ℕ) =
      Finsupp.single 0 (k - n) + Finsupp.single 1 m from by ext i; fin_cases i <;> simp]

end Virasoro.Sphere
