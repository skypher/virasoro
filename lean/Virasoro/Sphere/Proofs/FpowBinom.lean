import Virasoro.Sphere.Proofs.FpowLaw
import Virasoro.Sphere.Statements.Sec3b
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The exponent law for `fpow` and `(√(1-p))² = 1-p`

`fpow f a` is the substitution of `f - 1` into Mathlib's binomial series
`PowerSeries.binomialSeries`, whose exponent law `binomialSeries_add` (Chu–Vandermonde) gives
`fpow f (a + b) = fpow f a * fpow f b`.  The two-variable series `sqrtOneSub i` is the
substitution of `-x_i` into the binomial series of exponent `1/2`.

Consumers: sphere paper Lemmas 3.4–3.7 (`Stmt_lem_saddle`, `Stmt_lem_bergman_det`,
`Stmt_lem_ext_exponents`, `Stmt_lem_central_charge`).
-/

namespace Virasoro.Sphere

open PowerSeries

section

variable {A : Type*} [Field A] [CharZero A]

theorem descPochhammer_smeval_eq_prod (a : A) (k : ℕ) :
    (descPochhammer ℤ k).smeval a = ∏ i ∈ Finset.range k, (a - (i : A)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ,
      Polynomial.smeval_sub, Polynomial.smeval_X, pow_one, Polynomial.smeval_natCast]
    simp

theorem gbinom_eq_choose (a : A) (k : ℕ) : gbinom a k = Ring.choose a k := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_prod, gbinom, smul_eq_mul, div_eq_inv_mul]

theorem mk_gbinom (a : A) : PowerSeries.mk (gbinom a) = binomialSeries A a := by
  ext n
  simp [gbinom_eq_choose]

theorem compS_eq_subst (b : ℕ → A) {u : PowerSeries A} (hu : constantCoeff u = 0) :
    compS b u = (PowerSeries.mk b).subst u := by
  ext n
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hu), compS, coeff_mk]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp
  · intro d hd
    by_contra h
    have hlt : n < d := by
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
      omega
    exact hd (by simp [coeff_pow_of_lt hu hlt])

theorem fpow_eq_subst {f : PowerSeries A} (hf : constantCoeff f = 1) (a : A) :
    fpow f a = (binomialSeries A a).subst (f - 1) := by
  have hu : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  rw [fpow_eq_compS, compS_eq_subst _ hu, mk_gbinom]

/-- The exponent law `f^{a+b} = f^a f^b` for the binomial powers of a series with constant
term `1`. -/
theorem fpow_add {f : PowerSeries A} (hf : constantCoeff f = 1) (a b : A) :
    fpow f (a + b) = fpow f a * fpow f b := by
  have hu : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  rw [fpow_eq_subst hf, fpow_eq_subst hf, fpow_eq_subst hf, binomialSeries_add,
    subst_mul (HasSubst.of_constantCoeff_zero' hu)]

theorem fpow_zero {f : PowerSeries A} (hf : constantCoeff f = 1) : fpow f (0 : A) = 1 := by
  have hu : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  rw [fpow_eq_subst hf, binomialSeries_zero,
    ← coe_substAlgHom (HasSubst.of_constantCoeff_zero' hu), map_one]

theorem fpow_one {f : PowerSeries A} (hf : constantCoeff f = 1) : fpow f (1 : A) = f := by
  simpa [fpow_zero hf] using fpow_add_nat hf (0 : A) 1

theorem fpow_neg_mul {f : PowerSeries A} (hf : constantCoeff f = 1) (a : A) :
    fpow f (-a) * fpow f a = 1 := by
  rw [← fpow_add hf, neg_add_cancel, fpow_zero hf]

end

/-! ### The two-variable square root -/

theorem hasSubst_negX (i : Fin 2) :
    PowerSeries.HasSubst (-(MvPowerSeries.X i) : MvPowerSeries (Fin 2) ℚ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

theorem coeff_negX_pow (i : Fin 2) (d : ℕ) (α : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff α ((-(MvPowerSeries.X i) : MvPowerSeries (Fin 2) ℚ) ^ d) =
      if α = Finsupp.single i d then (-1 : ℚ) ^ d else 0 := by
  have h : (-(MvPowerSeries.X i) : MvPowerSeries (Fin 2) ℚ) ^ d =
      MvPowerSeries.C ((-1 : ℚ) ^ d) * MvPowerSeries.X i ^ d := by
    rw [neg_pow, map_pow, map_neg, map_one]
  rw [h, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]
  split_ifs <;> simp

theorem sqrtOneSub_eq_subst (i : Fin 2) :
    sqrtOneSub i = (binomialSeries ℚ (1 / 2 : ℚ)).subst (-(MvPowerSeries.X i)) := by
  ext α
  rw [PowerSeries.coeff_subst (hasSubst_negX i)]
  simp only [coeff_negX_pow, binomialSeries_coeff, smul_eq_mul, mul_one, ← gbinom_eq_choose]
  rw [finsum_eq_single _ (α i)]
  · show (if α = Finsupp.single i (α i) then _ else _) = _
    simp [mul_ite]
  · intro d hd
    have : α ≠ Finsupp.single i d := by
      intro h
      apply hd
      rw [h]
      simp
    simp [this]

/-- `(√(1 - x_i))² = 1 - x_i`. -/
theorem sqrtOneSub_sq (i : Fin 2) : sqrtOneSub i ^ 2 = 1 - MvPowerSeries.X i := by
  have h1 : binomialSeries ℚ (1 / 2 : ℚ) * binomialSeries ℚ (1 / 2 : ℚ) = 1 + PowerSeries.X := by
    rw [← binomialSeries_add]
    have := binomialSeries_nat (R := ℚ) (A := ℚ) 1
    norm_num at this ⊢
    exact this
  rw [sqrtOneSub_eq_subst, pow_two, ← PowerSeries.subst_mul (hasSubst_negX i), h1,
    PowerSeries.subst_add (hasSubst_negX i), PowerSeries.subst_X (hasSubst_negX i)]
  rw [← PowerSeries.coe_substAlgHom (hasSubst_negX i), map_one]
  ring

end Virasoro.Sphere
