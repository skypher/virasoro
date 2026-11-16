import Virasoro.Proofs.Expand
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Laurent coefficients of a quotient of polynomials with coefficients in a subring

If `P` has coefficients in a subring `S`, `Q ≠ 0` has coefficients in a subfield `k₀ ⊆ S`, and
`μ ∈ k₀`, then every Laurent coefficient of `P/Q` at `μ` lies in `S`.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

variable {K : Type*} [Field K]

theorem inv_coeff_mem (k₀ : Subfield K) {φ : PowerSeries K}
    (h : ∀ n, PowerSeries.coeff n φ ∈ k₀) : ∀ n, PowerSeries.coeff n φ⁻¹ ∈ k₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h0 : PowerSeries.constantCoeff φ ∈ k₀ := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h 0
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · exact k₀.inv_mem h0
    · refine k₀.mul_mem (k₀.neg_mem (k₀.inv_mem h0)) (k₀.sum_mem fun x hx => ?_)
      split_ifs with hx2
      · exact k₀.mul_mem (h x.1) (ih x.2 hx2)
      · exact k₀.zero_mem

theorem taylor_coeff_mem (S : Subring K) {P : K[X]} (hP : ∀ n, P.coeff n ∈ S) {μ : K}
    (hμ : μ ∈ S) (n : ℕ) : (taylor μ P).coeff n ∈ S := by
  rw [taylor_coeff, eval_eq_sum_range]
  refine S.sum_mem fun i _ => S.mul_mem ?_ (S.pow_mem hμ i)
  rw [hasseDeriv_coeff]
  exact S.mul_mem (natCast_mem S _) (hP _)

theorem coeff_single_neg_mul (m : ℕ) (x : K⸨X⸩) (n : ℤ) :
    ((HahnSeries.single (-(m : ℤ)) (1 : K)) * x).coeff n = x.coeff (n + m) := by
  have := HahnSeries.coeff_single_mul_add (r := (1 : K)) (x := x) (a := n + m) (b := -(m : ℤ))
  rw [one_mul] at this
  rw [← this]
  congr 1
  ring

/-- Laurent coefficients at `μ` of `P/Q` lie in the subring of the coefficients. -/
theorem lcoeff_div_mem (S : Subring K) (k₀ : Subfield K) (hk : ∀ x ∈ k₀, x ∈ S)
    {P Q : K[X]} (hP : ∀ n, P.coeff n ∈ S) (hQ : ∀ n, Q.coeff n ∈ k₀) (hQ0 : Q ≠ 0)
    {μ : K} (hμ : μ ∈ k₀) (n : ℤ) :
    lcoeff (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) μ n ∈ S := by
  set TP : PowerSeries K := ((taylor μ P : K[X]) : PowerSeries K) with hTP
  set TQ : PowerSeries K := ((taylor μ Q : K[X]) : PowerSeries K) with hTQ
  have hTQ0 : TQ ≠ 0 := by
    intro h0
    have h1 : taylor μ Q = 0 := Polynomial.coe_injective K (by rw [← hTQ, h0]; simp)
    exact hQ0 (taylor_injective μ (by rw [h1, map_zero]))
  set m := TQ.order.toNat with hm
  set u := PowerSeries.divXPowOrder TQ with hu
  have hfac : (PowerSeries.X : PowerSeries K) ^ m * u = TQ := PowerSeries.X_pow_order_mul_divXPowOrder
  have hunit : IsUnit u := PowerSeries.isUnit_divided_by_X_pow_order hTQ0
  have hu0 : PowerSeries.constantCoeff u ≠ 0 :=
    (PowerSeries.isUnit_iff_constantCoeff.mp hunit).ne_zero
  have hTPc : ∀ i, PowerSeries.coeff i TP ∈ S := fun i => by
    rw [hTP, Polynomial.coeff_coe]
    exact taylor_coeff_mem S hP (hk μ hμ) i
  have huc : ∀ i, PowerSeries.coeff i u ∈ k₀ := fun i => by
    rw [hu, PowerSeries.coeff_divXPowOrder, hTQ, Polynomial.coeff_coe]
    exact taylor_coeff_mem k₀.toSubring hQ hμ _
  have huinv : ∀ i, PowerSeries.coeff i u⁻¹ ∈ k₀ := inv_coeff_mem k₀ huc
  set W : PowerSeries K := TP * u⁻¹ with hW
  have hWc : ∀ i, PowerSeries.coeff i W ∈ S := fun i => by
    rw [hW, PowerSeries.coeff_mul]
    exact S.sum_mem fun x _ => S.mul_mem (hTPc _) (hk _ (huinv _))
  -- the expansion
  have hexp : expandAt (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) μ =
      HahnSeries.single (-(m : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K W := by
    unfold expandAt
    rw [RatFunc.laurent_div, RatFunc.algebraMap_apply_div,
      Polynomial.algebraMap_hahnSeries_apply, Polynomial.algebraMap_hahnSeries_apply]
    have hQne : HahnSeries.ofPowerSeries ℤ K TQ ≠ 0 := fun h0 =>
      hTQ0 (HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero]))
    rw [div_eq_iff hQne, ← hfac, hW]
    have h1 : HahnSeries.ofPowerSeries ℤ K ((PowerSeries.X : PowerSeries K) ^ m) =
        HahnSeries.single (m : ℤ) (1 : K) := by
      rw [HahnSeries.ofPowerSeries_X_pow]
    rw [map_mul, map_mul, h1]
    have h2 : HahnSeries.ofPowerSeries ℤ K u⁻¹ * HahnSeries.ofPowerSeries ℤ K u = 1 := by
      rw [← map_mul, PowerSeries.inv_mul_cancel _ hu0, map_one]
    have h3 : HahnSeries.single (-(m : ℤ)) (1 : K) * HahnSeries.single (m : ℤ) (1 : K) = 1 := by
      rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one]
      rfl
    calc HahnSeries.ofPowerSeries ℤ K TP
        = HahnSeries.ofPowerSeries ℤ K TP *
            (HahnSeries.ofPowerSeries ℤ K u⁻¹ * HahnSeries.ofPowerSeries ℤ K u) *
            (HahnSeries.single (-(m : ℤ)) (1 : K) * HahnSeries.single (m : ℤ) (1 : K)) := by
          rw [h2, h3, mul_one, mul_one]
      _ = _ := by ring
  unfold lcoeff
  rw [hexp, coeff_single_neg_mul, PowerSeries.coeff_coe]
  split_ifs
  · exact S.zero_mem
  · exact hWc _

end Virasoro
