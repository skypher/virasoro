import Virasoro.Sphere.Proofs.Sec3LamWard
import Virasoro.Sphere.Proofs.Sec3LamChain

/-!
# Equation (3.3) (sphere paper Lemma 3.3(i))

sphere/paper.tex l.559–568: substituting `F(λσ) = exp(λ²S(σ;λ))` into the Ward equations and
dividing by `λ²F` gives, for every `k ≥ 1`,
`(i + μk/λ)∂_k S + ∑_n nσ_n(∂_{n+k}S - ∂_n S) - ¼∑_{n<k}(∂_n S)(∂_{k-n}S)
 - (1/4λ²)∑_{n<k}∂_n∂_{k-n}S + (Δ₁ - kΔ₂ - μ²)/λ² - 1 = 0`.
First the equation for `T = log F` in the variables `u_m`, then the rescaling `u_m = λσ_m`,
which multiplies the coefficient of a monomial of polynomial degree `d` by `λ^d`.
-/

namespace Virasoro.Sphere

open Finset

/-- The left side of (3.3) with general coefficients: `a ∂_k S + ∑_n nσ_n(∂_{n+k}S - ∂_n S)
- q∑_{n<k}(∂_n S)(∂_{k-n}S) - b∑_{n<k}∂_n∂_{k-n}S - c`.  Equation (3.3) has `a = i + μk/λ`,
`q = 1/4`, `b = 1/(4λ²)`, `c = 1 + (μ² + kΔ₂ - Δ₁)/λ²`. -/
noncomputable def pdeLam {A : Type*} [CommRing A] (k : ℕ) (a q b c : A)
    (S : MvPowerSeries ℕ+ A) : MvPowerSeries ℕ+ A :=
  a • pdA k S + shiftA k S - levelA S
    - q • ∑ n ∈ Icc 1 (k - 1), pdA n S * pdA (k - n) S
    - b • ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) S) - MvPowerSeries.C c

theorem pdeZero_eq_pdeLam (k : ℕ) (S : MvPowerSeries ℕ+ ℂ) :
    pdeZero k S = pdeLam k Complex.I (1 / 4) 0 1 S := by
  rw [pdeZero, pdeLam]
  simp only [zero_smul, sub_zero, map_one]
  rfl

local notation "KK" => RatFunc ℂ

section LogEquation

variable {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}

/-- The Ward equations for `T = log F`, in the variables `u_m`. -/
theorem log_ward_eq (h : IsWardSeries μ lam Δa Δb F) (k : ℕ) (hk : 1 ≤ k) :
    shiftA k ((PowerSeries.log KK).subst (wardSeries F - 1))
      - algebraMap ℂ KK (1 / 4) • ∑ n ∈ Icc 1 (k - 1),
          (pdA n (pdA (k - n) ((PowerSeries.log KK).subst (wardSeries F - 1))) +
            pdA n ((PowerSeries.log KK).subst (wardSeries F - 1)) *
              pdA (k - n) ((PowerSeries.log KK).subst (wardSeries F - 1)))
      + (μ * (k : KK) + algebraMap ℂ KK Complex.I * lam) •
          pdA k ((PowerSeries.log KK).subst (wardSeries F - 1))
      - levelA ((PowerSeries.log KK).subst (wardSeries F - 1))
      - MvPowerSeries.C (lam ^ 2 + μ ^ 2 + ((k : KK) * Δb - Δa)) = 0 := by
  set G := wardSeries F with hG
  set T := (PowerSeries.log KK).subst (G - 1) with hT
  have h1 : MvPowerSeries.constantCoeff G = 1 := constantCoeff_wardSeries h
  have hpd : ∀ j, pdA j G = G * pdA j T := fun j => pderiv_eq_mul_pderiv_log G h1 _
  have hW := ward_series_eq h k hk
  rw [← hG, shiftA_of_pd k G G T hpd, levelA_of_pd G G T hpd] at hW
  have h2 : ∀ n j, pdA n (pdA j G) = G * (pdA n (pdA j T) + pdA n T * pdA j T) := by
    intro n j
    rw [hpd j]
    have e : pdA n (G * pdA j T) = G * pdA n (pdA j T) + pdA j T * pdA n G := by
      unfold pdA
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [e, hpd n]
    ring
  simp_rw [h2, hpd k] at hW
  rw [← Finset.mul_sum] at hW
  have hG0 : G ≠ 0 := fun h0 => by
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  apply mul_left_cancel₀ hG0
  simp only [MvPowerSeries.smul_eq_C_mul] at hW ⊢
  linear_combination hW

end LogEquation

section Rescaling

variable (lam : KK)

/-- Multiplication of the coefficient of a monomial of polynomial degree `d` by `λ^{d+e}`. -/
noncomputable def rho (e : ℤ) : MvPowerSeries ℕ+ KK →ₗ[KK] MvPowerSeries ℕ+ KK where
  toFun T := fun α => lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α T
  map_add' T T' := by
    ext α
    show lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α (T + T') =
      lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α T +
        lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α T'
    rw [map_add, mul_add]
  map_smul' c T := by
    ext α
    show lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α (c • T) =
      c * (lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α T)
    rw [MvPowerSeries.coeff_smul]
    ring

theorem coeff_rho (e : ℤ) (T : MvPowerSeries ℕ+ KK) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (rho lam e T) =
      lam ^ ((α.degree : ℤ) + e) * MvPowerSeries.coeff α T := rfl

theorem Slam_eq_rho (F : ℕ → MvPolynomial ℕ+ KK) :
    Slam F = rho RatFunc.X (-2) ((PowerSeries.log KK).subst (wardSeries F - 1)) := rfl

variable {lam} (hlam : lam ≠ 0)

include hlam

theorem rho_shift_exp (e e' : ℤ) (T : MvPowerSeries ℕ+ KK) :
    rho lam e T = lam ^ (e - e') • rho lam e' T := by
  ext α
  rw [MvPowerSeries.coeff_smul, coeff_rho, coeff_rho, ← mul_assoc, ← zpow_add₀ hlam]
  congr 2
  ring

theorem rho_mul (a b : ℤ) (f g : MvPowerSeries ℕ+ KK) :
    rho lam a f * rho lam b g = rho lam (a + b) (f * g) := by
  classical
  ext α
  rw [coeff_rho, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  have hd : ((α.degree : ℕ) : ℤ) + (a + b) =
      ((p.1.degree : ℤ) + a) + ((p.2.degree : ℤ) + b) := by
    rw [← hp', map_add]
    push_cast
    ring
  rw [coeff_rho, coeff_rho, hd, zpow_add₀ hlam ((p.1.degree : ℤ) + a) ((p.2.degree : ℤ) + b)]
  ring

omit hlam in
theorem rho_pd (e : ℤ) (n : ℕ) (T : MvPowerSeries ℕ+ KK) :
    pdA n (rho lam e T) = rho lam (e + 1) (pdA n T) := by
  ext α
  rw [coeff_pdA, coeff_rho, coeff_rho, coeff_pdA]
  have hd : (((α + Finsupp.single n.toPNat' 1).degree : ℕ) : ℤ) + e =
      (α.degree : ℤ) + (e + 1) := by
    rw [map_add, Finsupp.degree_single]
    push_cast
    ring
  rw [hd]
  ring

theorem rho_shift (e : ℤ) (k : ℕ) (T : MvPowerSeries ℕ+ KK) :
    shiftA k (rho lam e T) = rho lam e (shiftA k T) := by
  ext α
  rw [coeff_shiftA, coeff_rho, coeff_shiftA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [rho_pd, coeff_rho]
  have hd : (((α - Finsupp.single j 1 : ℕ+ →₀ ℕ).degree : ℕ) : ℤ) + (e + 1) =
      (α.degree : ℤ) + e := by
    have e1 := congrArg Finsupp.degree (sub_add_single hj)
    rw [map_add, Finsupp.degree_single] at e1
    rw [← e1]
    push_cast
    ring
  rw [hd]
  ring

omit hlam in
theorem rho_level (e : ℤ) (T : MvPowerSeries ℕ+ KK) :
    levelA (rho lam e T) = rho lam e (levelA T) := by
  ext α
  rw [coeff_levelA, coeff_rho, coeff_rho, coeff_levelA]
  ring

omit hlam in
theorem rho_C (e : ℤ) (c : KK) : rho lam e (MvPowerSeries.C c) = MvPowerSeries.C (lam ^ e * c) := by
  classical
  ext α
  rw [coeff_rho, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs with h0
  · rw [h0]
    simp
  · rw [mul_zero]

end Rescaling

/-- Equation (3.3) for `S(σ;λ) = λ⁻² log F(λσ;λ)`. -/
theorem S_pde {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK} (hlam : lam ≠ 0)
    (h : IsWardSeries μ lam Δa Δb F) (k : ℕ) (hk : 1 ≤ k) :
    pdeLam k ((μ * (k : KK) + algebraMap ℂ KK Complex.I * lam) * lam ^ (-1 : ℤ))
      (algebraMap ℂ KK (1 / 4)) (algebraMap ℂ KK (1 / 4) * lam ^ (-2 : ℤ))
      (lam ^ (-2 : ℤ) * (lam ^ 2 + μ ^ 2 + ((k : KK) * Δb - Δa)))
      (rho lam (-2) ((PowerSeries.log KK).subst (wardSeries F - 1))) = 0 := by
  set T := (PowerSeries.log KK).subst (wardSeries F - 1) with hT
  set S := rho lam (-2) T with hS
  have h0 := congrArg (rho lam (-2)) (log_ward_eq h k hk)
  rw [← hT] at h0
  simp only [map_sub, map_add, map_smul, map_sum, map_zero] at h0
  have e1 : ∀ n j, rho lam (-2) (pdA n (pdA j T)) = lam ^ (-2 : ℤ) • pdA n (pdA j S) := by
    intro n j
    rw [hS, rho_pd, rho_pd, rho_shift_exp hlam (-2) (-2 + 1 + 1)]
    norm_num
  have e2 : ∀ n j, rho lam (-2) (pdA n T * pdA j T) = pdA n S * pdA j S := by
    intro n j
    rw [hS, rho_pd, rho_pd, rho_mul hlam]
    norm_num
  have e3 : rho lam (-2) (pdA k T) = lam ^ (-1 : ℤ) • pdA k S := by
    rw [hS, rho_pd, rho_shift_exp hlam (-2) (-2 + 1)]
    norm_num
  simp only [e1, e2, e3, ← rho_shift hlam, ← rho_level, rho_C] at h0
  rw [pdeLam]
  simp only [MvPowerSeries.smul_eq_C_mul, map_mul, map_add, map_sub, Finset.sum_add_distrib,
    ← Finset.mul_sum] at h0 ⊢
  linear_combination h0

end Virasoro.Sphere
