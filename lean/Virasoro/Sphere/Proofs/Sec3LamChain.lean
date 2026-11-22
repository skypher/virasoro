import Virasoro.Sphere.Proofs.Sec3LamOps
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# The chain rule for `log F` (sphere paper Lemma 3.3(i))

sphere/paper.tex l.559–561: substituting `F = exp(λ²S)` into the Ward equations uses
`∂F = F ∂(log F)`.  For a series `g` in the `σ_m` with zero constant term and a one-variable
series `f`, `∂_i (f(g)) = f'(g) ∂_i g`; for `f = log(1+x)`, `f'(x)(1+x) = 1`.
-/

namespace Virasoro.Sphere

open Finset

section Chain

variable {A : Type*} [CommRing A]

theorem coeff_subst_trunc {g : MvPowerSeries ℕ+ A} (hg : MvPowerSeries.constantCoeff g = 0)
    (f : PowerSeries A) (e : ℕ+ →₀ ℕ) (N : ℕ) (hN : e.degree < N) :
    MvPowerSeries.coeff e (f.subst g) =
      MvPowerSeries.coeff e ((↑(PowerSeries.trunc N f) : PowerSeries A).subst g) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun d => ?_
  rcases lt_or_ge d N with hd | hd
  · rw [PowerSeries.coeff_coe_trunc_of_lt hd]
  · have h0 : MvPowerSeries.coeff e (g ^ d) = 0 := by
      refine MvPowerSeries.coeff_of_lt_order ?_
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg)
      exact_mod_cast lt_of_lt_of_le hN hd
    rw [h0, smul_zero, smul_zero]

/-- The chain rule `∂_i (f(g)) = f'(g) ∂_i g`. -/
theorem pderiv_subst {g : MvPowerSeries ℕ+ A} (hg : MvPowerSeries.constantCoeff g = 0)
    (f : PowerSeries A) (i : ℕ+) :
    MvPowerSeries.pderiv A i (f.subst g) =
      (PowerSeries.derivative A f).subst g * MvPowerSeries.pderiv A i g := by
  classical
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  ext e
  have h1 : (e + Finsupp.single i 1).degree < e.degree + 2 := by
    rw [map_add, Finsupp.degree_single]
    omega
  rw [MvPowerSeries.coeff_pderiv, coeff_subst_trunc hg f _ (e.degree + 2) h1,
    ← MvPowerSeries.coeff_pderiv, PowerSeries.subst_coe hs, Derivation.comp_aeval_eq,
    smul_eq_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  congr 1
  have hp' : p.1 + p.2 = e := by simpa using hp
  have h2 : p.1.degree < e.degree + 1 := by
    have := congrArg Finsupp.degree hp'
    rw [map_add] at this
    omega
  rw [coeff_subst_trunc hg _ p.1 (e.degree + 1) h2, PowerSeries.trunc_derivative,
    PowerSeries.subst_coe hs]

end Chain

section Log

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem deriv_log_mul : PowerSeries.derivative A (PowerSeries.log A) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rcases n with _ | n
  · simp
  · rw [mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), ← map_add]
    rw [pow_succ]
    simp

/-- `∂_i F = F ∂_i (log F)` for a series `F` with constant term `1`. -/
theorem pderiv_eq_mul_pderiv_log (F : MvPowerSeries ℕ+ A)
    (hF : MvPowerSeries.constantCoeff F = 1) (i : ℕ+) :
    MvPowerSeries.pderiv A i F =
      F * MvPowerSeries.pderiv A i ((PowerSeries.log A).subst (F - 1)) := by
  have hg : MvPowerSeries.constantCoeff (F - 1) = 0 := by
    rw [map_sub, hF, map_one, sub_self]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  have h1 := congrArg (PowerSeries.subst (F - 1)) (deriv_log_mul (A := A))
  rw [← PowerSeries.coe_substAlgHom hs, map_mul, map_add, map_one, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom hs] at h1
  have h2 : (1 : MvPowerSeries ℕ+ A) + (F - 1) = F := by ring
  rw [h2] at h1
  have h3 : MvPowerSeries.pderiv A i (F - 1) = MvPowerSeries.pderiv A i F := by
    rw [map_sub, MvPowerSeries.pderiv_one, sub_zero]
  rw [pderiv_subst hg, h3, ← mul_assoc, mul_comm F, h1, one_mul]

end Log

end Virasoro.Sphere
