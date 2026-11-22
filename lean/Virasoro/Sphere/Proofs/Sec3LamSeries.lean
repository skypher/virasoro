import Virasoro.Sphere.Proofs.Sec3LamRegular
import Mathlib.RingTheory.HahnSeries.PowerSeries

/-!
# The expansion `S = ∑_r λ^{-r} S^{(r)}` and the orders `λ⁰, λ⁻¹, λ⁻²` of (3.3)

sphere/paper.tex l.515, l.602–630.  By regularity the coefficients of `S` are power series in
`t = 1/λ`; `S^{(r)}` collects the coefficients of `t^r`.  Extracting the coefficients of
`t⁰, t¹, t²` from (3.3) gives the equations for `S^{(0)}, S^{(1)}, S^{(2)}`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

/-- `S(σ;λ)` with its coefficients as power series in `t = 1/λ`. -/
noncomputable def SP (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries ℕ+ PP :=
  fun α => PowerSeries.mk fun r => (MvPowerSeries.coeff α (SL F)).coeff (r : ℤ)

theorem coe_mk_of_ordGE {x : LL} (hx : OrdGE x 0) :
    ((PowerSeries.mk fun r : ℕ => x.coeff (r : ℤ) : PP) : LL) = x := by
  ext n
  rw [PowerSeries.coeff_coe]
  split_ifs with hn
  · exact (hx.coeff_eq_zero hn).symm
  · rw [PowerSeries.coeff_mk]
    congr 1
    omega

theorem map_SP {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F) :
    MvPowerSeries.map (HahnSeries.ofPowerSeries ℤ ℂ) (SP F) = SL F := by
  ext α : 1
  rw [MvPowerSeries.coeff_map]
  exact coe_mk_of_ordGE (SL_regular h α)

/-- Equation (3.3) with coefficients in `ℂ[[t]]`. -/
theorem SP_pde {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)
    (k : ℕ) (hk : 1 ≤ k) :
    pdeLam k (PowerSeries.C Complex.I + PowerSeries.C (μ * (k : ℂ)) * PowerSeries.X)
      (PowerSeries.C (1 / 4 : ℂ)) (PowerSeries.C (1 / 4 : ℂ) * PowerSeries.X ^ 2)
      (1 + PowerSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) * PowerSeries.X ^ 2) (SP F) = 0 := by
  have hinj : Function.Injective
      (MvPowerSeries.map (σ := ℕ+) (HahnSeries.ofPowerSeries ℤ ℂ)) := fun f g hfg => by
    ext α : 1
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    have := congrArg (MvPowerSeries.coeff α) hfg
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this
  apply hinj
  rw [map_pdeLam, map_SP h, map_zero]
  have ea : (HahnSeries.ofPowerSeries ℤ ℂ) (PowerSeries.C Complex.I +
      PowerSeries.C (μ * (k : ℂ)) * PowerSeries.X) =
      HahnSeries.C Complex.I + HahnSeries.C (μ * (k : ℂ)) * tL := by
    rw [map_add, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X]
    rfl
  have eq : (HahnSeries.ofPowerSeries ℤ ℂ) (PowerSeries.C (1 / 4 : ℂ)) =
      HahnSeries.C (1 / 4 : ℂ) := HahnSeries.ofPowerSeries_C _
  have eb : (HahnSeries.ofPowerSeries ℤ ℂ) (PowerSeries.C (1 / 4 : ℂ) * PowerSeries.X ^ 2) =
      HahnSeries.C (1 / 4 : ℂ) * tL ^ 2 := by
    rw [map_mul, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]
    rfl
  have ec : (HahnSeries.ofPowerSeries ℤ ℂ) (1 + PowerSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) *
      PowerSeries.X ^ 2) = 1 + HahnSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) * tL ^ 2 := by
    rw [map_add, map_one, map_mul, map_pow, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X]
    rfl
  rw [ea, eq, eb, ec]
  exact SL_pde h k hk

/-- The coefficient of `t^r`, monomial by monomial. -/
noncomputable def cR (r : ℕ) : MvPowerSeries ℕ+ PP →+ MvPowerSeries ℕ+ ℂ where
  toFun T := fun α => PowerSeries.coeff r (MvPowerSeries.coeff α T)
  map_zero' := by
    ext α
    show PowerSeries.coeff r (MvPowerSeries.coeff α (0 : MvPowerSeries ℕ+ PP)) = 0
    simp
  map_add' T T' := by
    ext α
    show PowerSeries.coeff r (MvPowerSeries.coeff α (T + T')) =
      PowerSeries.coeff r (MvPowerSeries.coeff α T) + PowerSeries.coeff r (MvPowerSeries.coeff α T')
    simp

theorem coeff_cR (r : ℕ) (T : MvPowerSeries ℕ+ PP) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (cR r T) = PowerSeries.coeff r (MvPowerSeries.coeff α T) := rfl

theorem Sord_eq_cR (F : ℕ → MvPolynomial ℕ+ KK) (r : ℕ) : Sord F r = cR r (SP F) := by
  ext α
  rw [Sord_eq, coeff_cR]
  show _ = PowerSeries.coeff r
    (PowerSeries.mk fun r : ℕ => (MvPowerSeries.coeff α (SL F)).coeff (r : ℤ))
  rw [PowerSeries.coeff_mk]

theorem natCast_PP (n : ℕ) : ((n : PP)) = PowerSeries.C (n : ℂ) :=
  (map_natCast (PowerSeries.C : ℂ →+* PP) n).symm

theorem cR_pd (r n : ℕ) (T : MvPowerSeries ℕ+ PP) : cR r (pdA n T) = pdA n (cR r T) := by
  ext α
  rw [coeff_cR, coeff_pdA, coeff_pdA, coeff_cR, natCast_PP,
    show (PowerSeries.C (α n.toPNat' : ℂ) + 1 : PP) = PowerSeries.C ((α n.toPNat' : ℂ) + 1) by
      simp, mul_comm, PowerSeries.coeff_C_mul, mul_comm]

theorem cR_shift (r k : ℕ) (T : MvPowerSeries ℕ+ PP) : cR r (shiftA k T) = shiftA k (cR r T) := by
  ext α
  rw [coeff_cR, coeff_shiftA, coeff_shiftA, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [natCast_PP, PowerSeries.coeff_C_mul, ← cR_pd, coeff_cR]

theorem cR_level (r : ℕ) (T : MvPowerSeries ℕ+ PP) : cR r (levelA T) = levelA (cR r T) := by
  ext α
  rw [coeff_cR, coeff_levelA, coeff_levelA, natCast_PP, PowerSeries.coeff_C_mul, coeff_cR]

theorem cR_C (r : ℕ) (x : PP) :
    cR r (MvPowerSeries.C x) = MvPowerSeries.C (PowerSeries.coeff r x) := by
  classical
  ext α
  rw [coeff_cR, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs <;> simp

theorem cR_smul_C (r : ℕ) (z : ℂ) (T : MvPowerSeries ℕ+ PP) :
    cR r (PowerSeries.C z • T) = z • cR r T := by
  ext α
  rw [coeff_cR, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, PowerSeries.coeff_C_mul,
    coeff_cR]

theorem cR_smul_X_succ (r : ℕ) (T : MvPowerSeries ℕ+ PP) :
    cR (r + 1) ((PowerSeries.X : PP) • T) = cR r T := by
  ext α
  rw [coeff_cR, MvPowerSeries.coeff_smul, PowerSeries.coeff_succ_X_mul, coeff_cR]

theorem cR_smul_X_zero (T : MvPowerSeries ℕ+ PP) : cR 0 ((PowerSeries.X : PP) • T) = 0 := by
  ext α
  rw [coeff_cR, MvPowerSeries.coeff_smul]
  simp

theorem cR_mul (r : ℕ) (f g : MvPowerSeries ℕ+ PP) :
    cR r (f * g) = ∑ p ∈ antidiagonal r, cR p.1 f * cR p.2 g := by
  classical
  ext α
  rw [coeff_cR, MvPowerSeries.coeff_mul, map_sum, map_sum]
  simp_rw [PowerSeries.coeff_mul, MvPowerSeries.coeff_mul, coeff_cR]
  exact Finset.sum_comm

theorem cR_mul_zero (f g : MvPowerSeries ℕ+ PP) : cR 0 (f * g) = cR 0 f * cR 0 g := by
  rw [cR_mul]
  simp

theorem cR_mul_one (f g : MvPowerSeries ℕ+ PP) :
    cR 1 (f * g) = cR 0 f * cR 1 g + cR 1 f * cR 0 g := by
  rw [cR_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem cR_mul_two (f g : MvPowerSeries ℕ+ PP) :
    cR 2 (f * g) = cR 0 f * cR 2 g + cR 1 f * cR 1 g + cR 2 f * cR 0 g := by
  rw [cR_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

section Extract

variable (k : ℕ) (z1 zq : ℂ) (c : PP) (T : MvPowerSeries ℕ+ PP)

theorem smul_split_a (U : MvPowerSeries ℕ+ PP) :
    (PowerSeries.C Complex.I + PowerSeries.C z1 * PowerSeries.X) • U =
      PowerSeries.C Complex.I • U + PowerSeries.C z1 • ((PowerSeries.X : PP) • U) := by
  rw [add_smul, mul_smul]

theorem smul_split_b (V : MvPowerSeries ℕ+ PP) :
    (PowerSeries.C zq * PowerSeries.X ^ 2) • V =
      PowerSeries.C zq • ((PowerSeries.X : PP) • ((PowerSeries.X : PP) • V)) := by
  rw [pow_two, mul_smul, mul_smul]

theorem cR_pdeLam_zero :
    cR 0 (pdeLam k (PowerSeries.C Complex.I + PowerSeries.C z1 * PowerSeries.X)
      (PowerSeries.C zq) (PowerSeries.C zq * PowerSeries.X ^ 2) c T) =
    Complex.I • pdA k (cR 0 T) + shiftA k (cR 0 T) - levelA (cR 0 T)
      - zq • ∑ n ∈ Icc 1 (k - 1), pdA n (cR 0 T) * pdA (k - n) (cR 0 T)
      - MvPowerSeries.C (PowerSeries.coeff 0 c) := by
  rw [pdeLam, smul_split_a, smul_split_b]
  simp only [map_sub, map_add, map_sum, cR_smul_C, cR_smul_X_zero, cR_pd, cR_shift, cR_level,
    cR_C, cR_mul_zero, smul_zero, add_zero, sub_zero]

theorem cR_pdeLam_one :
    cR 1 (pdeLam k (PowerSeries.C Complex.I + PowerSeries.C z1 * PowerSeries.X)
      (PowerSeries.C zq) (PowerSeries.C zq * PowerSeries.X ^ 2) c T) =
    Complex.I • pdA k (cR 1 T) + z1 • pdA k (cR 0 T) + shiftA k (cR 1 T) - levelA (cR 1 T)
      - zq • ∑ n ∈ Icc 1 (k - 1),
          (pdA n (cR 0 T) * pdA (k - n) (cR 1 T) + pdA n (cR 1 T) * pdA (k - n) (cR 0 T))
      - MvPowerSeries.C (PowerSeries.coeff 1 c) := by
  have hX1 : ∀ U : MvPowerSeries ℕ+ PP, cR 1 ((PowerSeries.X : PP) • U) = cR 0 U :=
    cR_smul_X_succ 0
  rw [pdeLam, smul_split_a, smul_split_b]
  simp only [map_sub, map_add, map_sum, cR_smul_C, hX1, cR_smul_X_zero, cR_pd, cR_shift,
    cR_level, cR_C, cR_mul_one, smul_zero, sub_zero]

theorem cR_pdeLam_two :
    cR 2 (pdeLam k (PowerSeries.C Complex.I + PowerSeries.C z1 * PowerSeries.X)
      (PowerSeries.C zq) (PowerSeries.C zq * PowerSeries.X ^ 2) c T) =
    Complex.I • pdA k (cR 2 T) + z1 • pdA k (cR 1 T) + shiftA k (cR 2 T) - levelA (cR 2 T)
      - zq • ∑ n ∈ Icc 1 (k - 1),
          (pdA n (cR 0 T) * pdA (k - n) (cR 2 T) + pdA n (cR 1 T) * pdA (k - n) (cR 1 T) +
            pdA n (cR 2 T) * pdA (k - n) (cR 0 T))
      - zq • ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) (cR 0 T))
      - MvPowerSeries.C (PowerSeries.coeff 2 c) := by
  have hX1 : ∀ U : MvPowerSeries ℕ+ PP, cR 1 ((PowerSeries.X : PP) • U) = cR 0 U :=
    cR_smul_X_succ 0
  have hX2 : ∀ U : MvPowerSeries ℕ+ PP, cR 2 ((PowerSeries.X : PP) • U) = cR 1 U :=
    cR_smul_X_succ 1
  rw [pdeLam, smul_split_a, smul_split_b]
  simp only [map_sub, map_add, map_sum, cR_smul_C, hX1, hX2, cR_pd, cR_shift, cR_level, cR_C,
    cR_mul_two]

theorem coeff_c_zero (c2 : ℂ) :
    PowerSeries.coeff 0 (1 + PowerSeries.C c2 * PowerSeries.X ^ 2 : PP) = 1 := by
  simp

theorem coeff_c_one (c2 : ℂ) :
    PowerSeries.coeff 1 (1 + PowerSeries.C c2 * PowerSeries.X ^ 2 : PP) = 0 := by
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  norm_num

theorem coeff_c_two (c2 : ℂ) :
    PowerSeries.coeff 2 (1 + PowerSeries.C c2 * PowerSeries.X ^ 2 : PP) = c2 := by
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  norm_num

end Extract

section Orders

variable {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
  (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)

include h

/-- Order `λ⁰` of (3.3). -/
theorem order_zero_eq (k : ℕ) (hk : 1 ≤ k) : pdeZero k (Sord F 0) = 0 := by
  have e := congrArg (cR 0) (SP_pde h k hk)
  rw [cR_pdeLam_zero, map_zero, coeff_c_zero, ← Sord_eq_cR] at e
  rw [pdeZero_eq_pdeLam, pdeLam, zero_smul, sub_zero]
  exact e

/-- Order `λ⁻¹` of (3.3). -/
theorem order_one_eq (k : ℕ) (hk : 1 ≤ k) :
    Complex.I • pdA k (Sord F 1) + (μ * (k : ℂ)) • pdA k (Sord F 0) + shiftA k (Sord F 1)
      - levelA (Sord F 1)
      - (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1),
          (pdA n (Sord F 0) * pdA (k - n) (Sord F 1) +
            pdA n (Sord F 1) * pdA (k - n) (Sord F 0)) = 0 := by
  have e := congrArg (cR 1) (SP_pde h k hk)
  rw [cR_pdeLam_one, map_zero, coeff_c_one, ← Sord_eq_cR, ← Sord_eq_cR, map_zero,
    sub_zero] at e
  exact e

/-- Order `λ⁻²` of (3.3). -/
theorem order_two_eq (k : ℕ) (hk : 1 ≤ k) :
    Complex.I • pdA k (Sord F 2) + (μ * (k : ℂ)) • pdA k (Sord F 1) + shiftA k (Sord F 2)
      - levelA (Sord F 2)
      - (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1),
          (pdA n (Sord F 0) * pdA (k - n) (Sord F 2) +
            pdA n (Sord F 1) * pdA (k - n) (Sord F 1) +
            pdA n (Sord F 2) * pdA (k - n) (Sord F 0))
      - (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) (Sord F 0))
      - MvPowerSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) = 0 := by
  have e := congrArg (cR 2) (SP_pde h k hk)
  rw [cR_pdeLam_two, map_zero, coeff_c_two, ← Sord_eq_cR, ← Sord_eq_cR, ← Sord_eq_cR] at e
  exact e

end Orders

end Virasoro.Sphere
