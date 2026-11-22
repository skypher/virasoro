import Virasoro.Sphere.Proofs.Sec3SaddlePde1
import Virasoro.Sphere.Proofs.Sec3SaddleOmega
import Virasoro.Sphere.Proofs.Sec3SaddleLin
import Virasoro.Sphere.Proofs.Sec3LamOrderZero

/-!
# Sphere paper Lemma 3.6, the `σ¹`-part generating functions (proof of Lemma 3.6)

For `C = C_±`, the `σ¹`-part generating function
`q∂_q((pC(q) - qC(p))/(q-p) - p/(1-p) C(q)) - B(p,q) C(p)` equals `p/(2(1-p)²) C_+(q)` for
`g(1)` and `-p/(2(1-p)) C_-(q)` for `g(-1)`.  As in the paper, these are rational identities in
`s₁ = √(1-p)`, `s₂ = √(1-q)` (`alg_ext_plus`, `alg_ext_minus`, with the `q`-derivatives entering
through their differentiated defining relations).  They are transported to series in `(p,q)`
(`ext_sigma1_plus`, `ext_sigma1_minus`) and read off at `p^k q^m`
(`sigma1_plus_Icc`, `sigma1_minus_Icc`), which are the `σ_m`-coefficients of
`L_k^{(0)} g(±1)`.  The factor `i` of `C_±` is left out: `cpS = (1/2) p (1-p)^{-3/2} = ∑ j h_j p^j`
and `cmS = -(1/2) p (1-p)^{-1/2}`.

Consumer: `L0_gAt_one`, `L0_gAt_neg_one` in `Sec3ExtLinear.lean`.
-/

namespace Virasoro.Sphere

open Finset

theorem hb_rec (j : ℕ) :
    2 * ((j : ℚ) + 1) * halfBinom (j + 1) = (2 * j + 1) * halfBinom j := by
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  rw [halfBinom_succ]
  field_simp

/-! ### The rational identities in `(s₁, s₂)` -/

/-- The `σ¹` identity for `g(1)`: with `C(x) = x/(2(1-x)^{3/2})`,
`2(q(E' - p/(1-p) C'(q)) - B C(p)) = p/(1-p)² C(q)`, where `(q-p)E = pC(q) - qC(p)`. -/
theorem alg_ext_plus {K : Type*} [Field K] [CharZero K]
    (a b u0 u1 p q C0 C1 E B db du1 dC1 dE : K)
    (ha : a ^ 2 = 1 - p) (hb : b ^ 2 = 1 - q) (hpq : q - p ≠ 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h1 : u0 * a = 1) (h2 : u1 * b = 1)
    (hC0 : 2 * (1 - p) * C0 = p * u0) (hC1 : 2 * (1 - q) * C1 = q * u1)
    (hE : (q - p) * E = p * C1 - q * C0)
    (hB : B * (2 * a * b * (a + b) ^ 2) = -(p * q))
    (hdb : 2 * b * db = -1) (hdu : du1 * b + u1 * db = 0)
    (hdC : 2 * (1 - q) * dC1 - 2 * C1 = u1 + q * du1)
    (hdE : E + (q - p) * dE = p * dC1 - C0) :
    2 * (q * (dE - p * u0 ^ 2 * dC1) - B * C0) = p * u0 ^ 4 * C1 := by
  obtain rfl : p = 1 - a ^ 2 := by linear_combination ha
  obtain rfl : q = 1 - b ^ 2 := by linear_combination hb
  have hfac : (a - b) * (a + b) ≠ 0 := by
    intro h
    apply hpq
    linear_combination h
  have hba : a - b ≠ 0 := left_ne_zero_of_mul hfac
  have hab : a + b ≠ 0 := right_ne_zero_of_mul hfac
  have h2' : (2 : K) ≠ 0 := by norm_num
  obtain rfl : du1 = 1 / (2 * b ^ 3) :=
    eq_div_of_mul_eq (mul_ne_zero h2' (pow_ne_zero 3 hb0))
      (by linear_combination 2 * b ^ 2 * hdu - (2 * b * db) * h2 - hdb)
  obtain rfl : u0 = 1 / a := eq_div_of_mul_eq ha0 h1
  obtain rfl : u1 = 1 / b := eq_div_of_mul_eq hb0 h2
  have ha2 : 2 * a ^ 2 ≠ 0 := mul_ne_zero h2' (pow_ne_zero 2 ha0)
  have hb2 : 2 * b ^ 2 ≠ 0 := mul_ne_zero h2' (pow_ne_zero 2 hb0)
  have hC0' : C0 = (1 - a ^ 2) * (1 / a) / (2 * a ^ 2) :=
    eq_div_of_mul_eq ha2 (by linear_combination hC0)
  have hC1' : C1 = (1 - b ^ 2) * (1 / b) / (2 * b ^ 2) :=
    eq_div_of_mul_eq hb2 (by linear_combination hC1)
  have hE' : E = ((1 - a ^ 2) * C1 - (1 - b ^ 2) * C0) / ((a - b) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hE)
  have hdC' : dC1 = (1 / b + (1 - b ^ 2) * (1 / (2 * b ^ 3)) + 2 * C1) / (2 * b ^ 2) :=
    eq_div_of_mul_eq hb2 (by linear_combination hdC)
  have hdE' : dE = ((1 - a ^ 2) * dC1 - C0 - E) / ((a - b) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hdE)
  have hden : (2 * a * b * (a + b) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2' ha0) hb0) (pow_ne_zero 2 hab)
  have hB' : B = -((1 - a ^ 2) * (1 - b ^ 2)) / (2 * a * b * (a + b) ^ 2) :=
    eq_div_of_mul_eq hden hB
  rw [hdE', hE', hdC', hC1', hC0', hB']
  field_simp
  ring

/-- The `σ¹` identity for `g(-1)`: with `C(x) = -x/(2(1-x)^{1/2})`,
`2(q(E' - p/(1-p) C'(q)) - B C(p)) = -p/(1-p) C(q)`. -/
theorem alg_ext_minus {K : Type*} [Field K] [CharZero K]
    (a b u0 u1 p q C0 C1 E B db du1 dC1 dE : K)
    (ha : a ^ 2 = 1 - p) (hb : b ^ 2 = 1 - q) (hpq : q - p ≠ 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h1 : u0 * a = 1) (h2 : u1 * b = 1)
    (hC0 : 2 * C0 = -(p * u0)) (hC1 : 2 * C1 = -(q * u1))
    (hE : (q - p) * E = p * C1 - q * C0)
    (hB : B * (2 * a * b * (a + b) ^ 2) = -(p * q))
    (hdb : 2 * b * db = -1) (hdu : du1 * b + u1 * db = 0)
    (hdC : 2 * dC1 = -(u1 + q * du1))
    (hdE : E + (q - p) * dE = p * dC1 - C0) :
    2 * (q * (dE - p * u0 ^ 2 * dC1) - B * C0) = -(p * u0 ^ 2 * C1) := by
  obtain rfl : p = 1 - a ^ 2 := by linear_combination ha
  obtain rfl : q = 1 - b ^ 2 := by linear_combination hb
  have hfac : (a - b) * (a + b) ≠ 0 := by
    intro h
    apply hpq
    linear_combination h
  have hba : a - b ≠ 0 := left_ne_zero_of_mul hfac
  have hab : a + b ≠ 0 := right_ne_zero_of_mul hfac
  have h2' : (2 : K) ≠ 0 := by norm_num
  obtain rfl : du1 = 1 / (2 * b ^ 3) :=
    eq_div_of_mul_eq (mul_ne_zero h2' (pow_ne_zero 3 hb0))
      (by linear_combination 2 * b ^ 2 * hdu - (2 * b * db) * h2 - hdb)
  obtain rfl : u0 = 1 / a := eq_div_of_mul_eq ha0 h1
  obtain rfl : u1 = 1 / b := eq_div_of_mul_eq hb0 h2
  have hC0' : C0 = -((1 - a ^ 2) * (1 / a)) / 2 :=
    eq_div_of_mul_eq h2' (by linear_combination hC0)
  have hC1' : C1 = -((1 - b ^ 2) * (1 / b)) / 2 :=
    eq_div_of_mul_eq h2' (by linear_combination hC1)
  have hE' : E = ((1 - a ^ 2) * C1 - (1 - b ^ 2) * C0) / ((a - b) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hE)
  have hdC' : dC1 = -(1 / b + (1 - b ^ 2) * (1 / (2 * b ^ 3))) / 2 :=
    eq_div_of_mul_eq h2' (by linear_combination hdC)
  have hdE' : dE = ((1 - a ^ 2) * dC1 - C0 - E) / ((a - b) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hdE)
  have hden : (2 * a * b * (a + b) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2' ha0) hb0) (pow_ne_zero 2 hab)
  have hB' : B = -((1 - a ^ 2) * (1 - b ^ 2)) / (2 * a * b * (a + b) ^ 2) :=
    eq_div_of_mul_eq hden hB
  rw [hdE', hE', hdC', hC1', hC0', hB']
  field_simp
  ring

/-! ### The one-variable series `C_±/i` -/

/-- `C_+(p)/i = (1/2) p (1-p)^{-3/2} = ∑_j j h_j p^j`. -/
noncomputable def cpS : PowerSeries ℚ := PowerSeries.mk fun j => (j : ℚ) * halfBinom j

/-- `C_-(p)/i = -(1/2) p (1-p)^{-1/2}`. -/
noncomputable def cmS : PowerSeries ℚ :=
  PowerSeries.mk fun j => if j = 0 then 0 else -(1 / 2) * halfBinom (j - 1)

theorem cpS_rel : 2 * (1 - PowerSeries.X) * cpS = PowerSeries.X * hser := by
  ext n
  rw [two_mul, add_mul, map_add, sub_mul, one_mul, map_sub]
  rcases n with _ | n
  · simp [cpS]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    simp only [cpS, hser, PowerSeries.coeff_mk]
    have := hb_rec n
    push_cast
    linear_combination this

theorem cmS_rel : 2 * cmS = -(PowerSeries.X * hser) := by
  ext n
  rw [two_mul, map_add, map_neg]
  rcases n with _ | n
  · simp [cmS]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [cmS, hser, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    ring

theorem hser_sq_mk : hser ^ 2 = PowerSeries.mk 1 := by
  ext k
  rw [pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  simp only [hser, PowerSeries.coeff_mk]
  exact sum_halfBinom_mul k

theorem mk_one_sq : (PowerSeries.mk (1 : ℕ → ℚ)) ^ 2 = PowerSeries.mk fun n => (n : ℚ) + 1 := by
  ext n
  rw [pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  simp only [PowerSeries.coeff_mk, Pi.one_apply, mul_one, sum_const,
    Finset.Nat.card_antidiagonal, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- `[p^k] p/(1-p) = 1` for `k ≥ 1`. -/
theorem coeff_X_hser_sq (k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.coeff k (PowerSeries.X * hser ^ 2) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [PowerSeries.coeff_succ_X_mul, hser_sq_mk, PowerSeries.coeff_mk, Pi.one_apply]

/-- `[p^k] p/(1-p)² = k`. -/
theorem coeff_X_hser_four (k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.coeff k (PowerSeries.X * hser ^ 4) = (k : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [PowerSeries.coeff_succ_X_mul, show hser ^ 4 = (hser ^ 2) ^ 2 by ring, hser_sq_mk,
    mk_one_sq, PowerSeries.coeff_mk]
  push_cast
  ring

/-! ### The divided difference `(pC(q) - qC(p))/(q-p)` -/

/-- `E(p,q) = ∑_{k,m≥1} c_{k+m} p^k q^m`. -/
noncomputable def EdivS (c : ℕ → ℚ) : MvPowerSeries (Fin 2) ℚ :=
  fun x => if 1 ≤ x 0 ∧ 1 ≤ x 1 then c (x 0 + x 1) else 0

theorem coeff_EdivS (c : ℕ → ℚ) (x : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff x (EdivS c) = if 1 ≤ x 0 ∧ 1 ≤ x 1 then c (x 0 + x 1) else 0 := rfl

theorem EdivS_rel (c : ℕ → ℚ) (hc : c 0 = 0) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * EdivS c =
      MvPowerSeries.X 0 * one 1 (PowerSeries.mk c) -
        MvPowerSeries.X 1 * one 0 (PowerSeries.mk c) := by
  ext x
  rw [sub_mul, map_sub, map_sub, coeff_X_mul', coeff_X_mul', coeff_X_mul', coeff_X_mul',
    coeff_one0, coeff_one1]
  obtain ⟨k, m, rfl⟩ := fin2_exists x
  rcases k with _ | _ | k <;> rcases m with _ | _ | m <;>
    simp [coeff_EdivS, Finsupp.single_apply, hc] <;> ring_nf

/-- `[p^k q^m] (f(p) g(q)) = [p^k] f · [q^m] g`. -/
theorem coeff_one0_mul_one1 (f g : PowerSeries ℚ) (k m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m) (one (0 : Fin 2) f * one (1 : Fin 2) g) =
      PowerSeries.coeff k f * PowerSeries.coeff m g := by
  rw [coeff_one_mul]
  have hx0 : (Finsupp.single 0 k + Finsupp.single 1 m : Fin 2 →₀ ℕ) 0 = k := by simp
  rw [hx0, sum_eq_single k]
  · rw [show (Finsupp.single 0 k + Finsupp.single 1 m - Finsupp.single 0 k : Fin 2 →₀ ℕ) =
        Finsupp.single 1 m from by ext i; fin_cases i <;> simp, coeff_one_single]
  · intro n hn hnk
    have hn' := mem_range.1 hn
    rw [coeff_one1, if_neg, mul_zero]
    simp
    omega
  · intro h
    exact absurd (mem_range.2 (Nat.lt_succ_self k)) h

/-- `[p^k q^m] (C(p) B(p,q)) = ∑_{n=0}^k c_n B_{k-n,m}`. -/
theorem coeff_one0_mul_Bgf (f : PowerSeries ℚ) (k m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m) (one 0 f * Bgf) =
      ∑ n ∈ range (k + 1), PowerSeries.coeff n f * Bcoef (k - n) m := by
  have hx0 : (Finsupp.single 0 k + Finsupp.single 1 m : Fin 2 →₀ ℕ) 0 = k := by simp
  rw [coeff_one_mul, hx0]
  refine sum_congr rfl fun n hn => ?_
  have hn' : n ≤ k := by have := mem_range.1 hn; omega
  rw [Bcoef,
    show (Finsupp.single 0 k + Finsupp.single 1 m - Finsupp.single 0 n : Fin 2 →₀ ℕ) =
      Finsupp.single 0 (k - n) + Finsupp.single 1 m from by ext i; fin_cases i <;> simp]

/-! ### The identities as series in `(p,q)` -/

theorem X1_sub_X0_ne : (MvPowerSeries.X 1 - MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ) ≠ 0 :=
  sub_ne_zero.2 (sub_ne_zero.1 X0_sub_X1_ne).symm

/-- The derivative data common to both signs. -/
theorem ext_deriv_data :
    2 * aS (1 : Fin 2) * MvPowerSeries.pderiv ℚ 1 (aS (1 : Fin 2)) = -1 ∧
      MvPowerSeries.pderiv ℚ 1 (uS (1 : Fin 2)) * aS 1 + uS 1 * MvPowerSeries.pderiv ℚ 1 (aS 1) = 0 ∧
      Bgf * (2 * aS 0 * aS 1 * (aS 0 + aS 1) ^ 2) =
        -(MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
  set δ := MvPowerSeries.pderiv ℚ (1 : Fin 2) with hδ
  have hX1 : δ (MvPowerSeries.X 1) = 1 := MvPowerSeries.pderiv_X_self
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg δ (show aS (1 : Fin 2) * aS 1 = 1 - MvPowerSeries.X 1 by rw [← sq, aS_sq])
    simp only [Derivation.leibniz, map_sub, hX1, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  · have := congrArg δ (uS_mul_aS (1 : Fin 2))
    simp only [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul] at this
    linear_combination this
  · have := Bgf_mul_Bden
    rw [Bden, sqrtOneSub_eq_aS, sqrtOneSub_eq_aS] at this
    exact this

/-- `δ(E - p/(1-p) C(q)) = δE - p/(1-p) δC(q)` for `δ = ∂_q`. -/
theorem pderiv_ext_F (E C1 : MvPowerSeries (Fin 2) ℚ) :
    MvPowerSeries.pderiv ℚ 1 (E - MvPowerSeries.X 0 * uS 0 ^ 2 * C1) =
      MvPowerSeries.pderiv ℚ 1 E -
        MvPowerSeries.X 0 * uS 0 ^ 2 * MvPowerSeries.pderiv ℚ 1 C1 := by
  have hX0 : MvPowerSeries.pderiv ℚ (1 : Fin 2) (MvPowerSeries.X 0) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (by decide)
  have hu0 : MvPowerSeries.pderiv ℚ (1 : Fin 2) (uS 0) = 0 := pderiv_one_ne 0 1 (by decide) _
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, hX0, hu0, smul_zero,
    smul_eq_mul, mul_zero, add_zero, zero_add]

/-- The `σ¹` generating function for `g(1)`, as series in `(p,q)`. -/
theorem ext_sigma1_plus :
    2 * (MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1
          (EdivS (fun j => (j : ℚ) * halfBinom j) - MvPowerSeries.X 0 * uS 0 ^ 2 * one 1 cpS) -
        Bgf * one 0 cpS) =
      MvPowerSeries.X 0 * uS 0 ^ 4 * one 1 cpS := by
  set δ := MvPowerSeries.pderiv ℚ (1 : Fin 2) with hδ
  have hX0 : δ (MvPowerSeries.X 0) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have hX1 : δ (MvPowerSeries.X 1) = 1 := MvPowerSeries.pderiv_X_self
  have hC0d : δ (one 0 cpS) = 0 := pderiv_one_ne 0 1 (by decide) _
  obtain ⟨hdb, hdu, hB⟩ := ext_deriv_data
  have hC0 : (2 : MvPowerSeries (Fin 2) ℚ) * (1 - MvPowerSeries.X 0) * one 0 cpS =
      MvPowerSeries.X 0 * uS 0 := by
    have := congrArg (one (0 : Fin 2)) cpS_rel
    simpa only [map_mul, map_sub, map_one, map_ofNat, one_X, uS] using this
  have hC1 : (2 : MvPowerSeries (Fin 2) ℚ) * (1 - MvPowerSeries.X 1) * one 1 cpS =
      MvPowerSeries.X 1 * uS 1 := by
    have := congrArg (one (1 : Fin 2)) cpS_rel
    simpa only [map_mul, map_sub, map_one, map_ofNat, one_X, uS] using this
  have hC1' : (1 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ) * one 1 cpS +
      (1 - MvPowerSeries.X 1) * one 1 cpS =
      MvPowerSeries.X 1 * uS 1 := by linear_combination hC1
  have hE : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * EdivS (fun j => (j : ℚ) * halfBinom j) =
      MvPowerSeries.X 0 * one 1 cpS - MvPowerSeries.X 1 * one 0 cpS :=
    EdivS_rel _ (by simp)
  have hdC : 2 * (1 - MvPowerSeries.X 1) * δ (one 1 cpS) - 2 * one 1 cpS =
      uS 1 + MvPowerSeries.X 1 * δ (uS 1) := by
    have := congrArg δ hC1'
    simp only [Derivation.leibniz, map_add, map_sub, hX1, Derivation.map_one_eq_zero,
      smul_eq_mul] at this
    linear_combination this
  have hdE : EdivS (fun j => (j : ℚ) * halfBinom j) +
      (MvPowerSeries.X 1 - MvPowerSeries.X 0) * δ (EdivS (fun j => (j : ℚ) * halfBinom j)) =
      MvPowerSeries.X 0 * δ (one 1 cpS) - one 0 cpS := by
    have := congrArg δ hE
    simp only [Derivation.leibniz, map_sub, hX0, hX1, hC0d, smul_eq_mul] at this
    linear_combination this
  rw [hδ, pderiv_ext_F, ← hδ]
  let φ := algebraMap (MvPowerSeries (Fin 2) ℚ) (FractionRing (MvPowerSeries (Fin 2) ℚ))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (MvPowerSeries (Fin 2) ℚ)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hne : ∀ y : MvPowerSeries (Fin 2) ℚ, y ≠ 0 → φ y ≠ 0 :=
    fun y hy => (map_ne_zero_iff φ hφ).2 hy
  have key := alg_ext_plus (φ (aS 0)) (φ (aS 1)) (φ (uS 0)) (φ (uS 1)) (φ (MvPowerSeries.X 0))
    (φ (MvPowerSeries.X 1)) (φ (one 0 cpS)) (φ (one 1 cpS))
    (φ (EdivS (fun j => (j : ℚ) * halfBinom j))) (φ Bgf) (φ (δ (aS 1))) (φ (δ (uS 1)))
    (φ (δ (one 1 cpS))) (φ (δ (EdivS (fun j => (j : ℚ) * halfBinom j))))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (0 : Fin 2)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (1 : Fin 2)))
    (by rw [← map_sub]; exact hne _ X1_sub_X0_ne)
    (hne _ (aS_ne_zero 0)) (hne _ (aS_ne_zero 1))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (0 : Fin 2)))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (1 : Fin 2)))
    (by simpa only [map_mul, map_sub, map_one, map_ofNat] using congrArg φ hC0)
    (by simpa only [map_mul, map_sub, map_one, map_ofNat] using congrArg φ hC1)
    (by simpa only [map_mul, map_sub] using congrArg φ hE)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ hB)
    (by simpa only [map_mul, map_neg, map_one, map_ofNat] using congrArg φ hdb)
    (by simpa only [map_mul, map_add, map_zero] using congrArg φ hdu)
    (by simpa only [map_mul, map_sub, map_add, map_one, map_ofNat] using congrArg φ hdC)
    (by simpa only [map_mul, map_sub, map_add] using congrArg φ hdE)
  exact hφ (by simpa only [map_mul, map_sub, map_pow, map_ofNat] using key)

/-- The `σ¹` generating function for `g(-1)`, as series in `(p,q)`. -/
theorem ext_sigma1_minus :
    2 * (MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1
          (EdivS (fun j => if j = 0 then 0 else -(1 / 2) * halfBinom (j - 1)) -
            MvPowerSeries.X 0 * uS 0 ^ 2 * one 1 cmS) -
        Bgf * one 0 cmS) =
      -(MvPowerSeries.X 0 * uS 0 ^ 2 * one 1 cmS) := by
  set δ := MvPowerSeries.pderiv ℚ (1 : Fin 2) with hδ
  set c : ℕ → ℚ := fun j => if j = 0 then 0 else -(1 / 2) * halfBinom (j - 1) with hc
  have hX0 : δ (MvPowerSeries.X 0) = 0 := MvPowerSeries.pderiv_X_of_ne (by decide)
  have hX1 : δ (MvPowerSeries.X 1) = 1 := MvPowerSeries.pderiv_X_self
  have hC0d : δ (one 0 cmS) = 0 := pderiv_one_ne 0 1 (by decide) _
  obtain ⟨hdb, hdu, hB⟩ := ext_deriv_data
  have hC0 : (2 : MvPowerSeries (Fin 2) ℚ) * one 0 cmS = -(MvPowerSeries.X 0 * uS 0) := by
    have := congrArg (one (0 : Fin 2)) cmS_rel
    simpa only [map_mul, map_neg, map_ofNat, one_X, uS] using this
  have hC1 : (2 : MvPowerSeries (Fin 2) ℚ) * one 1 cmS = -(MvPowerSeries.X 1 * uS 1) := by
    have := congrArg (one (1 : Fin 2)) cmS_rel
    simpa only [map_mul, map_neg, map_ofNat, one_X, uS] using this
  have hC1' : (one 1 cmS : MvPowerSeries (Fin 2) ℚ) + one 1 cmS = -(MvPowerSeries.X 1 * uS 1) := by
    linear_combination hC1
  have hE : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * EdivS c =
      MvPowerSeries.X 0 * one 1 cmS - MvPowerSeries.X 1 * one 0 cmS :=
    EdivS_rel _ (by simp [hc])
  have hdC : 2 * δ (one 1 cmS) = -(uS 1 + MvPowerSeries.X 1 * δ (uS 1)) := by
    have := congrArg δ hC1'
    simp only [Derivation.leibniz, map_add, map_neg, hX1, smul_eq_mul] at this
    linear_combination this
  have hdE : EdivS c + (MvPowerSeries.X 1 - MvPowerSeries.X 0) * δ (EdivS c) =
      MvPowerSeries.X 0 * δ (one 1 cmS) - one 0 cmS := by
    have := congrArg δ hE
    simp only [Derivation.leibniz, map_sub, hX0, hX1, hC0d, smul_eq_mul] at this
    linear_combination this
  rw [hδ, pderiv_ext_F, ← hδ]
  let φ := algebraMap (MvPowerSeries (Fin 2) ℚ) (FractionRing (MvPowerSeries (Fin 2) ℚ))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (MvPowerSeries (Fin 2) ℚ)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hne : ∀ y : MvPowerSeries (Fin 2) ℚ, y ≠ 0 → φ y ≠ 0 :=
    fun y hy => (map_ne_zero_iff φ hφ).2 hy
  have key := alg_ext_minus (φ (aS 0)) (φ (aS 1)) (φ (uS 0)) (φ (uS 1)) (φ (MvPowerSeries.X 0))
    (φ (MvPowerSeries.X 1)) (φ (one 0 cmS)) (φ (one 1 cmS)) (φ (EdivS c)) (φ Bgf)
    (φ (δ (aS 1))) (φ (δ (uS 1))) (φ (δ (one 1 cmS))) (φ (δ (EdivS c)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (0 : Fin 2)))
    (by simpa only [map_pow, map_sub, map_one] using congrArg φ (aS_sq (1 : Fin 2)))
    (by rw [← map_sub]; exact hne _ X1_sub_X0_ne)
    (hne _ (aS_ne_zero 0)) (hne _ (aS_ne_zero 1))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (0 : Fin 2)))
    (by simpa only [map_mul, map_one] using congrArg φ (uS_mul_aS (1 : Fin 2)))
    (by simpa only [map_mul, map_neg, map_ofNat] using congrArg φ hC0)
    (by simpa only [map_mul, map_neg, map_ofNat] using congrArg φ hC1)
    (by simpa only [map_mul, map_sub] using congrArg φ hE)
    (by simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat] using congrArg φ hB)
    (by simpa only [map_mul, map_neg, map_one, map_ofNat] using congrArg φ hdb)
    (by simpa only [map_mul, map_add, map_zero] using congrArg φ hdu)
    (by simpa only [map_mul, map_neg, map_add, map_ofNat] using congrArg φ hdC)
    (by simpa only [map_mul, map_sub, map_add] using congrArg φ hdE)
  exact hφ (by simpa only [map_mul, map_sub, map_neg, map_pow, map_ofNat] using key)

/-! ### Coefficients -/

/-- `[x^α]` of `X₁ ∂_q F` for `x = p^k q^m`. -/
theorem coeff_km_X1_pderiv (F : MvPowerSeries (Fin 2) ℚ) (k m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m)
        (MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1 F) =
      (m : ℚ) * MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m) F := by
  rw [coeff_X_mul_pderiv]
  simp

theorem coeff_km_EdivS (c : ℕ → ℚ) (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m) (EdivS c) = c (k + m) := by
  rw [coeff_EdivS]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply]
  simp [hk, hm]

/-- The coefficient form of a `σ¹` generating-function identity `2(X₁∂_q(E - X₀u₀²C₁) - B C₀) = R`
with `[p^k q^m] R = r_k c_m`. -/
theorem sigma1_coeff_of (c : ℕ → ℚ) (f : PowerSeries ℚ) (hf : f = PowerSeries.mk c)
    (g : PowerSeries ℚ)
    (h : 2 * (MvPowerSeries.X 1 * MvPowerSeries.pderiv ℚ 1
          (EdivS c - MvPowerSeries.X 0 * uS 0 ^ 2 * one 1 f) - Bgf * one 0 f) =
        one 0 g * one 1 f)
    (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    2 * ((m : ℚ) * (c (k + m) - c m) - ∑ n ∈ range (k + 1), c n * Bcoef (k - n) m) =
      PowerSeries.coeff k g * c m := by
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 m)) h
  have hXu : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ) * uS 0 ^ 2 * one 1 f =
      one 0 (PowerSeries.X * hser ^ 2) * one 1 f := by
    rw [map_mul, map_pow, one_X, uS]
  rw [two_mul, map_add, map_sub, coeff_km_X1_pderiv, map_sub, coeff_km_EdivS c k m hk hm, hXu,
    coeff_one0_mul_one1, coeff_X_hser_sq k hk, coeff_one0_mul_one1, mul_comm Bgf,
    coeff_one0_mul_Bgf, hf] at hc
  simp only [PowerSeries.coeff_mk] at hc
  rw [← hc]
  ring

/-- The `σ_m`-coefficient of `L_k^{(0)} g(1)`, from the generating function (`C_+` without `i`):
`m(c_{k+m} - c_m) - ∑_{n=1}^{k-1} B_{n,m} c_{k-n} = (k/2) c_m`, `c_j = j h_j`. -/
theorem sigma1_plus_Icc (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (m : ℚ) * ((((k + m : ℕ) : ℚ) * halfBinom (k + m)) - (m : ℚ) * halfBinom m) -
      ∑ n ∈ Icc 1 (k - 1), Bcoef n m * (((k - n : ℕ) : ℚ) * halfBinom (k - n)) =
      (k : ℚ) / 2 * ((m : ℚ) * halfBinom m) := by
  have hR : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ) * uS 0 ^ 4 * one 1 cpS =
      one 0 (PowerSeries.X * hser ^ 4) * one 1 cpS := by
    rw [map_mul, map_pow, one_X, uS]
  have h := sigma1_coeff_of (fun j => (j : ℚ) * halfBinom j) cpS rfl
    (PowerSeries.X * hser ^ 4) (ext_sigma1_plus.trans hR) k m hk hm
  rw [coeff_X_hser_four k hk,
    sum_range_eq_Icc k hk (fun n => ((n : ℚ) * halfBinom n) * Bcoef (k - n) m) (by simp)
      (by simp [Bcoef_zero_left])] at h
  have h2 := sum_reflect k fun a b => ((a : ℚ) * halfBinom a) * Bcoef b m
  try simp only at h2
  rw [h2] at h
  have h3 : ∑ n ∈ Icc 1 (k - 1), (((k - n : ℕ) : ℚ) * halfBinom (k - n)) * Bcoef n m =
      ∑ n ∈ Icc 1 (k - 1), Bcoef n m * (((k - n : ℕ) : ℚ) * halfBinom (k - n)) :=
    sum_congr rfl fun n _ => mul_comm _ _
  rw [h3] at h
  linear_combination (1 / 2 : ℚ) * h

/-- `d_j = [p^j] C_-(p)/i`: `0` for `j = 0`, `-(1/2) h_{j-1}` for `j ≥ 1`. -/
noncomputable def dM (j : ℕ) : ℚ := if j = 0 then 0 else -(1 / 2) * halfBinom (j - 1)

/-- The `σ_m`-coefficient of `L_k^{(0)} g(-1)`, from the generating function (`C_-` without `i`):
`m(d_{k+m} - d_m) - ∑_{n=1}^{k-1} B_{n,m} d_{k-n} = -(1/2) d_m`. -/
theorem sigma1_minus_Icc (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (m : ℚ) * (dM (k + m) - dM m) - ∑ n ∈ Icc 1 (k - 1), Bcoef n m * dM (k - n) =
      -(1 / 2) * dM m := by
  have hR : -((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ) * uS 0 ^ 2 * one 1 cmS) =
      one 0 (-(PowerSeries.X * hser ^ 2)) * one 1 cmS := by
    rw [map_neg, map_mul, map_pow, one_X, uS, neg_mul]
  have h := sigma1_coeff_of dM cmS rfl (-(PowerSeries.X * hser ^ 2))
    (ext_sigma1_minus.trans hR) k m hk hm
  rw [map_neg, coeff_X_hser_sq k hk,
    sum_range_eq_Icc k hk (fun n => dM n * Bcoef (k - n) m) (by simp [dM])
      (by simp [Bcoef_zero_left])] at h
  have h2 := sum_reflect k fun a b => dM a * Bcoef b m
  try simp only at h2
  rw [h2] at h
  have h3 : ∑ n ∈ Icc 1 (k - 1), dM (k - n) * Bcoef n m =
      ∑ n ∈ Icc 1 (k - 1), Bcoef n m * dM (k - n) :=
    sum_congr rfl fun n _ => mul_comm _ _
  rw [h3] at h
  linear_combination (1 / 2 : ℚ) * h

end Virasoro.Sphere
