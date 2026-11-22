import Virasoro.Sphere.Proofs.Sec3LamPde
import Virasoro.Proofs.Expand
import Virasoro.Proofs.Germs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Expansion at `λ = ∞` (sphere paper Lemma 3.3(i))

sphere/paper.tex l.513–515.  The substitution `λ = 1/t` followed by the Laurent expansion at
`t = 0` is a ring homomorphism `ℂ(λ) → ℂ((t))` with `λ ↦ t⁻¹`; a rational function is regular
at `λ = ∞` when its image has no negative power of `t`, and `S^{(r)}` collects the coefficients
of `t^r`.  Equation (3.3) is transported to `ℂ((t))`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

theorem aeval_inv_injective :
    Function.Injective (Polynomial.aeval (RatFunc.X⁻¹ : KK) : Polynomial ℂ →ₐ[ℂ] KK) := by
  rw [← transcendental_iff_injective, transcendental_iff]
  intro p hp
  haveI : Invertible (RatFunc.X⁻¹ : KK) := invertibleOfNonzero (inv_ne_zero RatFunc.X_ne_zero)
  have h := Polynomial.eval₂_reverse_mul_pow (algebraMap ℂ KK) (RatFunc.X⁻¹ : KK) p
  rw [invOf_eq_inv, inv_inv] at h
  rw [Polynomial.aeval_def] at hp
  rw [hp] at h
  have h2 : Polynomial.aeval (RatFunc.X : KK) p.reverse = 0 := by
    rw [Polynomial.aeval_def]
    exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero))
  exact Polynomial.reverse_eq_zero.1 ((transcendental_iff.1 RatFunc.transcendental_X) _ h2)

/-- `r(λ) ↦ r(1/t)` as a ring homomorphism. -/
noncomputable def inftyHom : KK →+* KK :=
  RatFunc.liftRingHom (Polynomial.aeval (RatFunc.X⁻¹ : KK) : Polynomial ℂ →ₐ[ℂ] KK).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ aeval_inv_injective)

theorem inftyHom_div (p q : Polynomial ℂ) :
    inftyHom (algebraMap _ KK p / algebraMap _ KK q) =
      Polynomial.aeval (RatFunc.X⁻¹ : KK) p / Polynomial.aeval (RatFunc.X⁻¹ : KK) q :=
  RatFunc.liftRingHom_apply_div _ _ p q

theorem atInfty_eq (r : KK) : atInfty r = inftyHom r := by
  conv_rhs => rw [← RatFunc.num_div_denom r]
  rw [inftyHom_div]
  rfl

theorem inftyHom_C (c : ℂ) : inftyHom (RatFunc.C c) = RatFunc.C c := by
  have h := inftyHom_div (Polynomial.C c) 1
  rw [map_one, div_one, RatFunc.algebraMap_C] at h
  rw [h]
  simp

theorem inftyHom_X : inftyHom (RatFunc.X : KK) = RatFunc.X⁻¹ := by
  have h := inftyHom_div Polynomial.X 1
  rw [map_one, div_one, RatFunc.algebraMap_X] at h
  rw [h]
  simp

/-- The expansion at `λ = ∞` in the variable `t = 1/λ`. -/
noncomputable def EInf : KK →+* LL := (expandHom (0 : ℂ)).comp inftyHom

theorem inftyCoeff_eq (r : KK) (n : ℤ) : inftyCoeff r n = (EInf r).coeff n := by
  rw [inftyCoeff, lcoeff, expandAt_eq, atInfty_eq]
  rfl

theorem EInf_C (c : ℂ) : EInf (RatFunc.C c) = HahnSeries.C c := by
  rw [EInf, RingHom.comp_apply, inftyHom_C, expandHom_C]

/-- `t = 1/λ`. -/
noncomputable def tL : LL := HahnSeries.single 1 1

theorem tL_mul_inv : tL * (HahnSeries.single (-1) (1 : ℂ) : LL) = 1 := by
  rw [tL, HahnSeries.single_mul_single]
  simp

theorem tL_ne_zero : tL ≠ 0 := fun h => by
  have := tL_mul_inv
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem EInf_X : EInf (RatFunc.X : KK) = tL⁻¹ := by
  rw [EInf, RingHom.comp_apply, inftyHom_X, map_inv₀, expandHom_X]
  simp [tL]

theorem EInf_X_inv : EInf ((RatFunc.X : KK) ^ (-1 : ℤ)) = tL := by
  rw [zpow_neg_one, map_inv₀, EInf_X, inv_inv]

theorem regularAtInfty_iff (r : KK) : RegularAtInfty r ↔ OrdGE (EInf r) 0 := by
  rw [ordGE_iff, RegularAtInfty]
  exact forall₂_congr fun n _ => by rw [inftyCoeff_eq]

theorem ordGE_tL : OrdGE tL 1 :=
  ordGE_iff.2 fun m hm => HahnSeries.coeff_single_of_ne (by omega)

theorem regVal_tL : RegVal tL 0 :=
  ⟨ordGE_tL.mono (by norm_num), HahnSeries.coeff_single_of_ne (by norm_num)⟩

/-! ### Base change of the left side of (3.3) -/

theorem map_pdeLam {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') (k : ℕ)
    (a q b c : A) (S : MvPowerSeries ℕ+ A) :
    MvPowerSeries.map f (pdeLam k a q b c S) =
      pdeLam k (f a) (f q) (f b) (f c) (MvPowerSeries.map f S) := by
  have hs : ∀ (r : A) (T : MvPowerSeries ℕ+ A),
      MvPowerSeries.map f (r • T) = f r • MvPowerSeries.map f T := fun r T => by
    ext α
    simp
  rw [pdeLam, pdeLam]
  simp only [map_sub, map_add, hs, map_sum, map_mul, map_pdA, map_shiftA, map_levelA,
    MvPowerSeries.map_C]

/-- `S(σ;λ)` with its coefficients expanded at `λ = ∞`. -/
noncomputable def SL (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries ℕ+ LL :=
  MvPowerSeries.map EInf (Slam F)

theorem Sord_eq (F : ℕ → MvPolynomial ℕ+ KK) (r : ℕ) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (Sord F r) = (MvPowerSeries.coeff α (SL F)).coeff r := by
  rw [SL, MvPowerSeries.coeff_map]
  exact inftyCoeff_eq _ _

/-- Equation (3.3) in the variable `t = 1/λ`:
`(i + μk t)∂_k S + ∑_n nσ_n(∂_{n+k}S - ∂_n S) - ¼∑(∂_n S)(∂_{k-n}S) - (t²/4)∑∂_n∂_{k-n}S
- 1 - (μ² + kΔ₂ - Δ₁)t² = 0`. -/
theorem SL_pde {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)
    (k : ℕ) (hk : 1 ≤ k) :
    pdeLam k (HahnSeries.C Complex.I + HahnSeries.C (μ * (k : ℂ)) * tL)
      (HahnSeries.C (1 / 4 : ℂ)) (HahnSeries.C (1 / 4 : ℂ) * tL ^ 2)
      (1 + HahnSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) * tL ^ 2) (SL F) = 0 := by
  have h0 := congrArg (MvPowerSeries.map EInf) (S_pde RatFunc.X_ne_zero h k hk)
  rw [map_pdeLam, map_zero, ← Slam_eq_rho] at h0
  have hX2 : EInf ((RatFunc.X : KK) ^ (-2 : ℤ)) = tL ^ 2 := by
    rw [show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add₀ RatFunc.X_ne_zero, map_mul, EInf_X_inv]
    ring
  have ea : EInf ((RatFunc.C μ * (k : KK) + algebraMap ℂ KK Complex.I * RatFunc.X) *
      RatFunc.X ^ (-1 : ℤ)) = HahnSeries.C Complex.I + HahnSeries.C (μ * (k : ℂ)) * tL := by
    rw [map_mul, map_add, map_mul, map_mul, EInf_X_inv, EInf_X, RatFunc.algebraMap_eq_C, EInf_C,
      EInf_C, map_natCast, map_mul, map_natCast]
    field_simp [tL_ne_zero]
    ring
  have eb : EInf (algebraMap ℂ KK (1 / 4) * (RatFunc.X : KK) ^ (-2 : ℤ)) =
      HahnSeries.C (1 / 4 : ℂ) * tL ^ 2 := by
    rw [map_mul, hX2, RatFunc.algebraMap_eq_C, EInf_C]
  have ec : EInf ((RatFunc.X : KK) ^ (-2 : ℤ) * (RatFunc.X ^ 2 + RatFunc.C μ ^ 2 +
      ((k : KK) * RatFunc.C Δ2 - RatFunc.C Δ1))) =
      1 + HahnSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) * tL ^ 2 := by
    rw [map_mul, hX2, map_add, map_add, map_sub, map_mul, map_pow, map_pow, EInf_X, EInf_C,
      EInf_C, EInf_C, map_natCast, map_add, map_sub, map_mul, map_pow, map_natCast]
    field_simp [tL_ne_zero]
    ring
  have eq : EInf (algebraMap ℂ KK (1 / 4)) = HahnSeries.C (1 / 4 : ℂ) := by
    rw [RatFunc.algebraMap_eq_C, EInf_C]
  rw [ea, eb, ec, eq] at h0
  exact h0

end Virasoro.Sphere
