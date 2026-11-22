import Virasoro.Sphere.Proofs.Sec3GaussReduce
import Virasoro.Sphere.Proofs.Sec3GaussEuler

/-!
# The expectation of the shifted factor at `t = 0` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.698–706.  When the shifted factor `R(x + λ(σ_*, σ̄_*))` is the exponential of a
series `E` with coefficients in `ℂ[[t]][[z]]/(z^{n+1})` ("`O(λ⁻¹)` coefficientwise in `z`"), its
Gaussian expectation has coefficients in `ℂ[[t]]`, and the value at `t = 0` is the expectation of
the exponential of `E|_{t=0}`.  When `E|_{t=0}` is a linear form plus a constant,
`E|_{t=0} = L·x + c`, that expectation is `det(I - M²)^{-1/2} e^{c + ½ L·CL}` ("evaluating the
finite centered Gaussian expectation of the linear-in-`(U,V)` exponential").
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

section Expect

variable (n : ℕ)

/-- `ℚ[[z]] → A[[z]]/(z^{n+1})`. -/
noncomputable def phiA (A : Type*) [CommRing A] [Algebra ℚ A] : PowerSeries ℚ →+* TR n A :=
  (mkT n A).comp (PowerSeries.map (algebraMap ℚ A))

theorem phiA_X_pow (A : Type*) [CommRing A] [Algebra ℚ A] :
    phiA n A PowerSeries.X ^ (n + 1) = 0 := by
  rw [phiA, RingHom.comp_apply, PowerSeries.map_X]
  exact mkT_X_pow

theorem mapT_phiA {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (ψ : A →+* B) (f : PowerSeries ℚ) : mapT ψ (phiA n A f) = phiA n B f := by
  rw [phiA, phiA, RingHom.comp_apply, RingHom.comp_apply, mapT_mkT]
  refine congrArg _ (PowerSeries.ext fun k => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, map_algebraMap_rat]

/-- `ℂ[[t]][[z]]/(z^{n+1}) → ℂ((t))[[z]]/(z^{n+1})`. -/
noncomputable def rhoT : TR n PP →+* TR n LL := mapT (HahnSeries.ofPowerSeries ℤ ℂ)

/-- The value at `t = 0`: `ℂ[[t]][[z]]/(z^{n+1}) → ℂ[[z]]/(z^{n+1})`. -/
noncomputable def epsT : TR n PP →+* TR n ℂ := mapT (PowerSeries.constantCoeff (R := ℂ))

/-- The Gaussian expectation of `exp(E)` for `E` with coefficients in `ℂ[[t]][[z]]/(z^{n+1})`
and `E|_{t=0} = L·x + c` (sphere/paper.tex l.698–706). -/
theorem gauss_expect_of_lift (EP : MvPowerSeries (Modes n) (TR n PP))
    (hnil : IsNilpotent (constantCoeff EP)) (L : Modes n → TR n ℂ) (c : TR n ℂ)
    (hc : IsNilpotent c) (hred : map (epsT n) EP = linForm L + C c) :
    ∃ w : PP,
      HahnSeries.ofPowerSeries ℤ ℂ w =
        cfT n (fockP n n (phiL n PowerSeries.X)
          (mexp (quadB n (TR n LL)) * map (rhoT n) (mexp EP))) ∧
      PowerSeries.constantCoeff w =
        cfT n (IsNilpotent.exp c *
          (IsNilpotent.exp ((1 / 2 : ℚ) • ∑ a, ∑ b, L a * covN n (phiA n ℂ) n a b * L b) *
            phiA n ℂ detInvSqrt)) := by
  have hq0 : IsNilpotent (constantCoeff (quadB n (TR n PP))) := by
    rw [constantCoeff_quadB]
    exact IsNilpotent.zero
  have hq0' : IsNilpotent (constantCoeff (quadB n (TR n ℂ))) := by
    rw [constantCoeff_quadB]
    exact IsNilpotent.zero
  have hl0 : IsNilpotent (constantCoeff (linForm L)) := by
    rw [constantCoeff_linForm]
    exact IsNilpotent.zero
  have hc' : IsNilpotent (constantCoeff (C c : MvPowerSeries (Modes n) (TR n ℂ))) := by
    rw [constantCoeff_C]
    exact hc
  refine ⟨cfT n (fockP n n (phiA n PP PowerSeries.X) (mexp (quadB n (TR n PP)) * mexp EP)),
    ?_, ?_⟩
  · rw [← cf_mapT (HahnSeries.ofPowerSeries ℤ ℂ) le_rfl]
    show cfT n (rhoT n (fockP n n (phiA n PP PowerSeries.X)
      (mexp (quadB n (TR n PP)) * mexp EP))) = _
    rw [map_fockP, map_mul, map_mexp _ hq0, map_quadB]
    show cfT n (fockP n n (mapT (HahnSeries.ofPowerSeries ℤ ℂ) (phiA n PP PowerSeries.X)) _) = _
    rw [mapT_phiA]
    rfl
  · have h1 := cf_mapT (PowerSeries.constantCoeff (R := ℂ)) (N := n) (j := n) le_rfl
      (fockP n n (phiA n PP PowerSeries.X) (mexp (quadB n (TR n PP)) * mexp EP))
    rw [← h1]
    show cfT n (epsT n (fockP n n (phiA n PP PowerSeries.X)
      (mexp (quadB n (TR n PP)) * mexp EP))) = _
    rw [map_fockP, map_mul, map_mexp _ hq0, map_quadB, map_mexp _ hnil, hred]
    show cfT n (fockP n n (mapT (PowerSeries.constantCoeff (R := ℂ)) (phiA n PP PowerSeries.X)) _)
      = _
    rw [mapT_phiA, mexp_add hl0 hc', mexp_C hc, ← mul_assoc, mul_comm _ (C _), apply_C_mul,
      ← mexp_add hq0' hl0, fockP_gauss_linear (phiA n ℂ) le_rfl (phiA_X_pow n ℂ) L]

end Expect

end Virasoro.Sphere
