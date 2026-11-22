import Virasoro.Sphere.Proofs.Sec3LamOrderZero
import Virasoro.Sphere.Proofs.Sec3SaddleDiag

/-!
# Orders `λ⁻¹` and `λ⁻²` of (3.3) in terms of `L_k^{(0)}` (Lemma 3.3(ii))

sphere/paper.tex l.612–630.  At order `λ⁻¹`: `L_k^{(0)}S^{(1)} + μk∂_k S^{(0)} = 0`.  At order
`λ⁻²`, with `-¼∑_{n<k}∂_n∂_{k-n}S^{(0)} = -½∑_{n<k}B_{n,k-n} = (k-1)/16`:
`L_k^{(0)}S^{(2)} + μk∂_k S^{(1)} - ¼∑(∂_n S^{(1)})(∂_{k-n}S^{(1)}) + (k-1)/16 - μ² - kΔ₂ + Δ₁ = 0`.
-/

namespace Virasoro.Sphere

open Finset

local notation "KK" => RatFunc ℂ

theorem pdA_pdA_S0 (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) :
    pdA n (pdA j S0) = MvPowerSeries.C (2 * (Bcoef j n : ℂ)) := by
  rw [← pd_eq_pdA j, pd_S0' j hj, pdA_add, pdA_C, zero_add]
  unfold pdA
  rw [pderiv_linSeries, cB_eq, PNat.toPNat'_coe hn]

/-- `¼∑_{n<k}∂_n∂_{k-n}S^{(0)} = -(k-1)/16`. -/
theorem quarter_dd (k : ℕ) (hk : 1 ≤ k) :
    (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) S0) =
      MvPowerSeries.C (-(((k : ℂ) - 1) / 16)) := by
  have h1 : ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) S0) =
      MvPowerSeries.C (2 * ((∑ n ∈ Icc 1 (k - 1), Bcoef n (k - n) : ℚ) : ℂ)) := by
    rw [Rat.cast_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Icc.1 hn
    rw [pdA_pdA_S0 n (k - n) hn'.1 (by omega), Bcoef_symm]
  have h2 := sum_Bcoef_diag k hk
  have h3 : ((∑ n ∈ Icc 1 (k - 1), Bcoef n (k - n) : ℚ) : ℂ) = -(((k : ℂ) - 1) / 8) := by
    have h4 : (∑ n ∈ Icc 1 (k - 1), Bcoef n (k - n) : ℚ) = -(((k : ℚ) - 1) / 8) := by
      linarith
    rw [h4]
    push_cast
    ring
  rw [h1, h3, MvPowerSeries.smul_eq_C_mul, ← map_mul]
  congr 1
  ring

section Forms

variable {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
  (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)

include h

/-- Order `λ⁻¹`: `L_k^{(0)}S^{(1)} = -μk∂_k S^{(0)}`. -/
theorem L0_Sord_one (k : ℕ) (hk : 1 ≤ k) :
    L0 k (Sord F 1) = -((μ * (k : ℂ)) • pdA k S0) := by
  have e := order_one_eq h k hk
  rw [Sord_zero_eq h] at e
  have hsym : ∑ n ∈ Icc 1 (k - 1), pdA n (Sord F 1) * pdA (k - n) S0 =
      ∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) (Sord F 1) := by
    rw [sum_reflect k fun a b => pdA a (Sord F 1) * pdA b S0]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [Finset.sum_add_distrib, hsym] at e
  rw [L0_eq]
  simp only [MvPowerSeries.smul_eq_C_mul] at e ⊢
  have h4 : (MvPowerSeries.C (1 / 2 : ℂ) : MvPowerSeries ℕ+ ℂ) =
      MvPowerSeries.C (1 / 4 : ℂ) * 2 := by
    rw [show (2 : MvPowerSeries ℕ+ ℂ) = MvPowerSeries.C (2 : ℂ) from (map_ofNat _ 2).symm,
      ← map_mul]
    norm_num
  rw [h4]
  linear_combination e

/-- Order `λ⁻²`. -/
theorem L0_Sord_two (k : ℕ) (hk : 1 ≤ k) :
    L0 k (Sord F 2) = -((μ * (k : ℂ)) • pdA k (Sord F 1))
      + (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pdA n (Sord F 1) * pdA (k - n) (Sord F 1)
      + MvPowerSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1) - ((k : ℂ) - 1) / 16) := by
  have e := order_two_eq h k hk
  rw [Sord_zero_eq h, quarter_dd k hk] at e
  have hsym : ∑ n ∈ Icc 1 (k - 1), pdA n (Sord F 2) * pdA (k - n) S0 =
      ∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) (Sord F 2) := by
    rw [sum_reflect k fun a b => pdA a (Sord F 2) * pdA b S0]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsym] at e
  rw [L0_eq]
  simp only [MvPowerSeries.smul_eq_C_mul, map_sub, map_add, map_neg] at e ⊢
  have h4 : (MvPowerSeries.C (1 / 2 : ℂ) : MvPowerSeries ℕ+ ℂ) =
      MvPowerSeries.C (1 / 4 : ℂ) * 2 := by
    rw [show (2 : MvPowerSeries ℕ+ ℂ) = MvPowerSeries.C (2 : ℂ) from (map_ofNat _ 2).symm,
      ← map_mul]
    norm_num
  rw [h4]
  linear_combination e

end Forms

end Virasoro.Sphere
