import Virasoro.Proofs.Germs
import Virasoro.Proofs.Sec7Val
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The truncated binomial series

For `u ≠ 0` and a germ `y` with `ord_t y ≥ 1`,
`(u - y)^{-(j+1)} = ∑_{i<n} C(j+i, j) u^{-(i+j+1)} y^i + O(t^n)`.
This is the Taylor expansion used in the proofs of Lemmas 7.11 and 7.12 (expansion of
`1/(μ - h_g)^{j+1}` around `μ - w_g`), and for the Laurent coefficients of a simple fraction at
another point.
-/

namespace Virasoro

open scoped LaurentSeries

section Binom

variable {K : Type*} [Field K]

/-- `X^n` divides `trunc_n(∑ C(j+i,j) X^i) · (1 - X)^{j+1} - 1`. -/
theorem binom_trunc_dvd (j n : ℕ) :
    Polynomial.X ^ n ∣
      PowerSeries.trunc n (PowerSeries.mk fun i => (((j + i).choose j : ℕ) : K)) *
        (1 - Polynomial.X) ^ (j + 1) - 1 := by
  set f : PowerSeries K := PowerSeries.mk fun i => (((j + i).choose j : ℕ) : K) with hf
  rw [Polynomial.X_pow_dvd_iff]
  intro e he
  have hone : f * (1 - PowerSeries.X) ^ (j + 1) = 1 := by
    rw [hf]
    exact PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one K j
  have h1 : PowerSeries.trunc n ((PowerSeries.trunc n f : PowerSeries K) *
      (1 - PowerSeries.X) ^ (j + 1)) = PowerSeries.trunc n (1 : PowerSeries K) := by
    rw [PowerSeries.trunc_trunc_mul, hone]
  have h2 := congrArg (fun p : Polynomial K => p.coeff e) h1
  simp only [PowerSeries.coeff_trunc, if_pos he] at h2
  have h3 : ((PowerSeries.trunc n f * (1 - Polynomial.X) ^ (j + 1) : Polynomial K) :
      PowerSeries K) = (PowerSeries.trunc n f : PowerSeries K) * (1 - PowerSeries.X) ^ (j + 1) := by
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_X]
  rw [Polynomial.coeff_sub, ← Polynomial.coeff_coe, h3, h2, PowerSeries.coeff_one,
    Polynomial.coeff_one]
  simp

theorem ordGE_eval₂ {x : K⸨X⸩} (hx : OrdGE x 0) (R : Polynomial K) :
    OrdGE (R.eval₂ HahnSeries.C x) 0 := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine OrdGE.sum fun i _ => ?_
  have := (ordGE_C (R.coeff i)).mul (hx.pow i)
  simpa using this

/-- The truncated binomial series for `(u - y)^{-(j+1)}`. -/
theorem inv_pow_trunc {u : K} (hu : u ≠ 0) {y : K⸨X⸩} (hy : OrdGE y 1) (j n : ℕ) :
    OrdGE ((HahnSeries.C u - y)⁻¹ ^ (j + 1) -
      ∑ i ∈ Finset.range n,
        HahnSeries.C ((((j + i).choose j : ℕ) : K) / u ^ (i + j + 1)) * y ^ i) n := by
  set f : PowerSeries K := PowerSeries.mk fun i => (((j + i).choose j : ℕ) : K) with hf
  obtain ⟨R, hR⟩ := binom_trunc_dvd (K := K) j n
  set x : K⸨X⸩ := y * HahnSeries.C u⁻¹ with hx
  set E : K⸨X⸩ := (HahnSeries.C u - y)⁻¹ with hE
  set S : K⸨X⸩ := (PowerSeries.trunc n f).eval₂ HahnSeries.C x with hS
  set Rx : K⸨X⸩ := R.eval₂ HahnSeries.C x with hRx
  have hreg : RegVal (HahnSeries.C u - y) u := by
    have h0 : RegVal y 0 := ⟨hy.mono (by norm_num), hy.coeff_eq_zero (by norm_num)⟩
    simpa using (regVal_C u).sub h0
  have hne : HahnSeries.C u - y ≠ 0 := by
    intro h
    have := hreg.2
    rw [h, HahnSeries.coeff_zero] at this
    exact hu this.symm
  have hCu : (HahnSeries.C u : K⸨X⸩) * HahnSeries.C u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  -- the polynomial identity, evaluated at `x`
  have hid := congrArg (Polynomial.eval₂RingHom (HahnSeries.C : K →+* K⸨X⸩) x) hR
  simp only [map_sub, map_mul, map_pow, map_one, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X] at hid
  -- hid : S * (1 - x)^(j+1) - 1 = x^n * Rx
  have h1x : 1 - x = (HahnSeries.C u - y) * HahnSeries.C u⁻¹ := by
    rw [hx, sub_mul, hCu]
  rw [← hS, ← hRx, h1x, mul_pow] at hid
  have hEinv : (HahnSeries.C u - y) ^ (j + 1) * E ^ (j + 1) = 1 := by
    rw [← mul_pow, hE, mul_inv_cancel₀ hne, one_pow]
  have hT : ∑ i ∈ Finset.range n,
      HahnSeries.C ((((j + i).choose j : ℕ) : K) / u ^ (i + j + 1)) * y ^ i =
        HahnSeries.C u⁻¹ ^ (j + 1) * S := by
    rw [hS, PowerSeries.eval₂_trunc_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, PowerSeries.coeff_mk, hx, div_eq_mul_inv, map_mul, ← inv_pow, map_pow, mul_pow]
    ring
  have hkey : E ^ (j + 1) - HahnSeries.C u⁻¹ ^ (j + 1) * S = -(E ^ (j + 1) * x ^ n * Rx) := by
    linear_combination (-(E ^ (j + 1))) * hid + (HahnSeries.C u⁻¹ ^ (j + 1) * S) * hEinv
  rw [hT, hkey]
  have hEo : OrdGE E 0 := (hreg.inv hu).1
  have hxo : OrdGE x 1 := by
    have h := hy.mul (ordGE_C u⁻¹)
    rw [add_zero] at h
    exact h
  have := ((hEo.pow (j + 1)).mul (hxo.pow n)).mul (ordGE_eval₂ (hxo.mono (by norm_num)) R)
  simpa using this.neg

/-- Coefficients of `B (u - y)^{-(j+1)}` below the truncation order. -/
theorem coeff_mul_inv_pow {u : K} (hu : u ≠ 0) {y B : K⸨X⸩} (hy : OrdGE y 1) {v : ℤ}
    (hB : OrdGE B v) (j n : ℕ) {m : ℤ} (hm : m < v + n) :
    (B * (HahnSeries.C u - y)⁻¹ ^ (j + 1)).coeff m =
      ∑ i ∈ Finset.range n,
        (((j + i).choose j : ℕ) : K) / u ^ (i + j + 1) * (B * y ^ i).coeff m := by
  set T : K⸨X⸩ := ∑ i ∈ Finset.range n,
    HahnSeries.C ((((j + i).choose j : ℕ) : K) / u ^ (i + j + 1)) * y ^ i with hT
  have h := hB.mul (inv_pow_trunc hu hy j n)
  have hsplit : B * (HahnSeries.C u - y)⁻¹ ^ (j + 1) =
      B * ((HahnSeries.C u - y)⁻¹ ^ (j + 1) - T) + B * T := by ring
  rw [hsplit, HahnSeries.coeff_add, h.coeff_eq_zero hm, zero_add, hT, Finset.mul_sum,
    HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

end Binom

end Virasoro
