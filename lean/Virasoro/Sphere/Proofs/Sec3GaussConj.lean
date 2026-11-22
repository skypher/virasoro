import Virasoro.Sphere.Proofs.Sec3GaussSubs
import Virasoro.Sphere.Proofs.Sec3LamInfty
import Mathlib.RingTheory.LaurentSeries

/-!
# Complex conjugation and the expansion at `λ = ∞`

The second factor of the pairing of Lemma 3.2(ii) is the Ward solution with conjugated
coefficients (`i ↦ -i` at real `λ`; sphere/paper.tex l.641, `S̃`).  Conjugating the coefficients
of a rational function of `λ` commutes with the expansion in `t = 1/λ`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

/-- Complex conjugation of the coefficients of a Laurent series in `t`. -/
noncomputable def cL : LL →+* LL :=
  IsLocalization.map (M := nonZeroDivisors PP) (T := nonZeroDivisors PP) LL
    (PowerSeries.map (starRingEnd ℂ))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (PowerSeries.map_injective _ (starRingEnd ℂ).injective))

theorem cL_ofPowerSeries (p : PP) :
    cL (HahnSeries.ofPowerSeries ℤ ℂ p) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map (starRingEnd ℂ) p) := by
  have h := IsLocalization.map_eq (M := nonZeroDivisors PP) (T := nonZeroDivisors PP) (Q := LL)
    (S := LL) (g := PowerSeries.map (starRingEnd ℂ))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (PowerSeries.map_injective _ (starRingEnd ℂ).injective)) p
  rw [LaurentSeries.coe_algebraMap] at h
  exact h

theorem cL_C (c : ℂ) : cL (HahnSeries.C c) = HahnSeries.C ((starRingEnd ℂ) c) := by
  rw [← HahnSeries.ofPowerSeries_C, cL_ofPowerSeries, PowerSeries.map_C,
    HahnSeries.ofPowerSeries_C]

theorem cL_tL : cL tL = tL := by
  have h : tL = HahnSeries.ofPowerSeries ℤ ℂ PowerSeries.X := HahnSeries.ofPowerSeries_X.symm
  rw [h, cL_ofPowerSeries, PowerSeries.map_X]

/-- Conjugation of the coefficients commutes with the expansion at `λ = ∞`. -/
theorem EInf_conjK (x : KK) : EInf (conjK x) = cL (EInf x) := by
  have key : (EInf.comp conjK).comp (algebraMap (Polynomial ℂ) KK) =
      (cL.comp EInf).comp (algebraMap (Polynomial ℂ) KK) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · have h1 := conjK_div (Polynomial.C c) 1
      simp only [Polynomial.map_one, map_one, div_one, Polynomial.map_C,
        RatFunc.algebraMap_C] at h1
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C, h1, EInf_C, cL_C]
    · have h1 := conjK_div Polynomial.X 1
      simp only [Polynomial.map_one, map_one, div_one, Polynomial.map_X,
        RatFunc.algebraMap_X] at h1
      simp only [RingHom.comp_apply, RatFunc.algebraMap_X, h1, EInf_X, map_inv₀, cL_tL]
  exact RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ)) key) x

end Virasoro.Sphere
