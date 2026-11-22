import Virasoro.Sphere.Proofs.Sec3LamSeries
import Virasoro.Sphere.Proofs.Sec3LamOrderZero
import Virasoro.Sphere.Proofs.Sec3GaussExp

/-!
# The Ward solution as `exp(λ² S(u/λ; λ))` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.559 (`F(λσ) = exp(λ² S(σ;λ))`) and l.641–650: in the variable `t = 1/λ`,
`log F(u) = λ² S⁽⁰⁾(tu) + λ T(tu)` with `S = S⁽⁰⁾ + t T`, `T = ∑_{r≥1} t^{r-1} S⁽ʳ⁾` a series with
coefficients in `ℂ[[t]]`; the second term is the logarithm of the factor `R` of l.647–650.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

/-- `log F` for the formal series `F = ∑_m F_m`. -/
noncomputable def logW (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries ℕ+ KK :=
  (PowerSeries.log KK).subst (wardSeries F - 1)

theorem constantCoeff_logW {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) : constantCoeff (logW F) = 0 := by
  have hg : constantCoeff (wardSeries F - 1) = 0 := by
    rw [map_sub, constantCoeff_wardSeries h, map_one, sub_self]
  exact PowerSeries.constantCoeff_subst_eq_zero hg _ PowerSeries.constantCoeff_log

/-- `F = exp(log F)`. -/
theorem wardSeries_eq_mexp {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) : wardSeries F = mexp (logW F) :=
  ext_of_pderiv (fun i => pderiv KK i (logW F))
    (by rw [constantCoeff_wardSeries h, constantCoeff_mexp (constantCoeff_logW h)])
    (fun i => pderiv_eq_mul_pderiv_log _ (constantCoeff_wardSeries h) i)
    (fun i => pderiv_mexp_zero (constantCoeff_logW h) i)

/-- `T = (S - S⁽⁰⁾)/t = ∑_{r≥1} t^{r-1} S⁽ʳ⁾`, with coefficients in `ℂ[[t]]`. -/
noncomputable def SPtail (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries ℕ+ PP :=
  fun α => PowerSeries.mk fun r => PowerSeries.coeff (r + 1) (coeff α (SP F))

theorem coeff_SPtail (F : ℕ → MvPolynomial ℕ+ KK) (α : ℕ+ →₀ ℕ) (r : ℕ) :
    PowerSeries.coeff r (coeff α (SPtail F)) = PowerSeries.coeff (r + 1) (coeff α (SP F)) := by
  show PowerSeries.coeff r (PowerSeries.mk fun r => PowerSeries.coeff (r + 1) (coeff α (SP F))) = _
  rw [PowerSeries.coeff_mk]

theorem prod_const_pow {σ R : Type*} [CommMonoid R] (r : R) (α : σ →₀ ℕ) :
    (α.prod fun _ m => r ^ m) = r ^ α.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

section Split

variable {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
  (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)

include h

/-- `S = S⁽⁰⁾ + t T`. -/
theorem SP_split (α : ℕ+ →₀ ℕ) :
    coeff α (SP F) = PowerSeries.C (coeff α S0) + PowerSeries.X * coeff α (SPtail F) := by
  ext r
  cases r with
  | zero =>
    have h0 := congrArg (coeff α) (Sord_eq_cR F 0)
    rw [Sord_zero_eq h, coeff_cR] at h0
    simp [h0]
  | succ r =>
    rw [map_add, PowerSeries.coeff_succ_X_mul, coeff_SPtail, PowerSeries.coeff_C,
      if_neg (Nat.succ_ne_zero r), zero_add]

/-- The coefficients of `log F` at `λ = ∞`: `λ^{2-|α|} (S⁽⁰⁾_α + t T_α)`. -/
theorem EInf_coeff_logW (α : ℕ+ →₀ ℕ) :
    EInf (coeff α (logW F)) = (tL⁻¹) ^ 2 * tL ^ α.degree *
      (HahnSeries.C (coeff α S0) +
        tL * HahnSeries.ofPowerSeries ℤ ℂ (coeff α (SPtail F))) := by
  have h1 : coeff α (SL F) =
      EInf ((RatFunc.X : KK) ^ ((α.degree : ℤ) - 2) * coeff α (logW F)) := by
    rw [SL, coeff_map]
    rfl
  have h2 := congrArg (coeff α) (map_SP h)
  rw [coeff_map, SP_split h, map_add, map_mul, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X, h1, map_mul, map_zpow₀, EInf_X] at h2
  have ht := tL_ne_zero
  have e1 : tL ^ ((α.degree : ℤ) - 2) * (tL⁻¹) ^ ((α.degree : ℤ) - 2) = 1 := by
    rw [inv_zpow, mul_inv_cancel₀ (zpow_ne_zero _ ht)]
  have e2 : tL ^ ((α.degree : ℤ) - 2) = (tL⁻¹) ^ 2 * tL ^ α.degree := by
    rw [zpow_sub₀ ht, zpow_natCast, zpow_ofNat, div_eq_mul_inv, inv_pow, mul_comm]
  rw [← e2]
  change _ = tL ^ ((α.degree : ℤ) - 2) *
    (HahnSeries.C (coeff α S0) +
      HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ ℂ (coeff α (SPtail F)))
  rw [h2, ← mul_assoc, e1, one_mul]

/-- `log F(u) = λ² S⁽⁰⁾(tu) + λ T(tu)`, in any ring under `ℂ((t))`. -/
theorem map_logW {R' : Type*} [CommRing R'] (ψ : LL →+* R') :
    map (ψ.comp EInf) (logW F) =
      ψ (tL⁻¹) ^ 2 • rescale (fun _ => ψ tL) (map (ψ.comp HahnSeries.C) S0) +
        ψ (tL⁻¹) • rescale (fun _ => ψ tL)
          (map (ψ.comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F)) := by
  ext α
  have hu : ψ tL⁻¹ * ψ tL = 1 := by
    rw [← map_mul, inv_mul_cancel₀ tL_ne_zero, map_one]
  rw [coeff_map, RingHom.comp_apply, EInf_coeff_logW h, map_add, coeff_smul, coeff_smul,
    coeff_rescale, coeff_rescale, coeff_map, coeff_map, prod_const_pow]
  simp only [map_mul, map_add, map_pow, RingHom.comp_apply, smul_eq_mul]
  linear_combination (ψ tL⁻¹ * ψ tL ^ α.degree *
    ψ (HahnSeries.ofPowerSeries ℤ ℂ (coeff α (SPtail F)))) * hu

end Split

end Virasoro.Sphere
