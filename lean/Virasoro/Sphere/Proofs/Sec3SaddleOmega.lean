import Virasoro.Sphere.Saddle
import Virasoro.Sphere.Proofs.FpowBinom
import Mathlib.Data.Nat.Choose.Central

/-!
# Sphere paper Lemma 3.4(iii), the Laurent expansion of `Ω(x;z)` (`sphere/paper.tex` l.725–727)

`Ω(x;z) = 1 + ∑_m a_m(z) x^m + ∑_m a_m(z) (z/x)^m`: the coefficient of `x⁰` is `1` and the
coefficient of `x^{-m}` is `a_m(z) z^m`.  Both follow from
`[x^k](1-x)^{-1/2} = binom(2k,k)/4^k`.

Consumer: the third conjunct of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem gbinom_succ_mul {A : Type*} [Field A] [CharZero A] (a : A) (k : ℕ) :
    gbinom a (k + 1) = gbinom a k * (a - k) / (k + 1) := by
  unfold gbinom
  have hk : ((k.factorial : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hk1 : ((k : A) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

theorem halfBinom_succ (k : ℕ) :
    halfBinom (k + 1) = halfBinom k * (2 * k + 1) / (2 * (k + 1)) := by
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [halfBinom, halfBinom, gbinom_succ_mul, pow_succ]
  field_simp
  ring

/-- `[x^k](1-x)^{-1/2} = binom(2k,k)/4^k`. -/
theorem halfBinom_eq (k : ℕ) : halfBinom k = (Nat.centralBinom k : ℚ) / 4 ^ k := by
  induction k with
  | zero => simp [halfBinom, gbinom]
  | succ k ih =>
    have hk1 : ((k : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h := Nat.succ_mul_centralBinom_succ k
    have h' : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
        2 * (2 * k + 1) * (Nat.centralBinom k : ℚ) := by exact_mod_cast h
    have h'' : (Nat.centralBinom (k + 1) : ℚ) =
        2 * (2 * k + 1) * (Nat.centralBinom k : ℚ) / (k + 1) := by
      rw [← h']
      field_simp
    rw [halfBinom_succ, ih, h'', pow_succ]
    field_simp
    norm_num

theorem constantCoeff_hyp2F1 : PowerSeries.constantCoeff hyp2F1 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hyp2F1, PowerSeries.coeff_mk]
  simp

/-- The coefficient of `x⁰` of `Ω(x;z)` is `1`. -/
theorem OmegaCoef_zero : OmegaCoef 0 = 1 := by
  have h : (PowerSeries.mk fun l : ℕ =>
      if 0 ≤ (0 : ℤ) + l then halfBinom ((0 : ℤ) + l).toNat * halfBinom l else 0) = hyp2F1 := by
    ext l
    simp only [hyp2F1, PowerSeries.coeff_mk, zero_add, Int.natCast_nonneg, if_true,
      Int.toNat_natCast, halfBinom_eq]
    ring
  rw [OmegaCoef, h, PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_hyp2F1]; norm_num)]

/-- The coefficient of `x^{-m}` of `Ω(x;z)` is `a_m(z) z^m`. -/
theorem OmegaCoef_neg (m : ℕ) :
    OmegaCoef (-(m : ℤ)) = aSer m * (PowerSeries.X : PowerSeries ℚ) ^ m := by
  have h : (PowerSeries.mk fun l : ℕ =>
      if 0 ≤ -(m : ℤ) + l then halfBinom (-(m : ℤ) + l).toNat * halfBinom l else 0) =
      (PowerSeries.mk fun l : ℕ =>
        if 0 ≤ (m : ℤ) + l then halfBinom ((m : ℤ) + l).toNat * halfBinom l else 0) *
        (PowerSeries.X : PowerSeries ℚ) ^ m := by
    ext l
    rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
    by_cases hml : m ≤ l
    · rw [if_pos (by omega), if_pos hml, PowerSeries.coeff_mk, if_pos (by omega)]
      have e1 : (-(m : ℤ) + l).toNat = l - m := by omega
      have e2 : ((m : ℤ) + ((l - m : ℕ) : ℤ)).toNat = l := by omega
      rw [e1, e2, mul_comm]
    · rw [if_neg (by omega), if_neg hml]
  rw [OmegaCoef, h, aSer, OmegaCoef]
  ring

end Virasoro.Sphere
