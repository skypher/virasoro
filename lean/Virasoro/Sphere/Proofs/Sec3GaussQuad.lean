import Virasoro.Sphere.Proofs.Sec3GaussShift
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Absorbing the quadratic part into the Gaussian weight (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.642–661.  Let `W` be a centered algebraic Gaussian expectation with covariance
`C₀` and `q` a quadratic form with gradient `∂_j q = ∑_k H_{jk} x_k`.  If `C₀H` is nilpotent,
then `Φ ↦ W(e^q Φ)` satisfies the Wick rule with mean zero and the covariance `C` determined by
`(1 - C₀H) C = C₀`, the Neumann inverse of the perturbed Hessian.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries

section Quad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [Algebra ℚ R]

theorem eq_zero_of_one_sub_mulVec {N : Matrix ι ι R} (hN : IsNilpotent N) {x : ι → R}
    (hx : ∀ i, x i = ∑ l, N i l * x l) : x = 0 := by
  obtain ⟨u, hu⟩ := hN.isUnit_one_sub
  have h1 : (1 - N).mulVec x = 0 := by
    funext i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact hx i
  have h2 : ((↑u⁻¹ : Matrix ι ι R) * (1 - N)).mulVec x = 0 := by
    rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rwa [← hu, Units.inv_mul, Matrix.one_mulVec] at h2

/-- Absorbing a quadratic form into the Gaussian weight: the Wick rule for `Φ ↦ W(e^q Φ)` with
the covariance `C`, `(1 - C₀H) C = C₀`. -/
theorem ibp_quadratic {W : MvPowerSeries ι R →ₗ[R] R} {C0 : ι → ι → R} (hI : IBP W 0 C0)
    (q : MvPowerSeries ι R) (hq0 : constantCoeff q = 0) (H : ι → ι → R)
    (hq : ∀ j, pderiv R j q = ∑ k, MvPowerSeries.C (H j k) * X k)
    (hN : IsNilpotent (Matrix.of fun i l => ∑ k, C0 i k * H k l : Matrix ι ι R))
    (C : ι → ι → R) (hC : ∀ i j, C i j = C0 i j + ∑ l, (∑ k, C0 i k * H k l) * C l j) :
    IBP (W.comp (LinearMap.mulLeft R (mexp q))) 0 C := by
  intro i Φ
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Pi.zero_apply, zero_mul, zero_add]
  set w : ι → R := fun i => W (mexp q * (X i * Φ)) with hw
  set g : ι → R := fun j => W (mexp q * pderiv R j Φ) with hg
  have hrec : ∀ i, w i = ∑ l, (∑ k, C0 i k * H k l) * w l + ∑ j, C0 i j * g j := by
    intro i
    have h1 : ∀ j, W (pderiv R j (mexp q * Φ)) = g j + ∑ k, H j k * w k := by
      intro j
      have h2 : pderiv R j (mexp q * Φ) =
          mexp q * pderiv R j Φ + ∑ k, MvPowerSeries.C (H j k) * (mexp q * (X k * Φ)) := by
        rw [Derivation.leibniz, pderiv_mexp_zero hq0, hq, smul_eq_mul, smul_eq_mul,
          Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [h2, map_add, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => apply_C_mul W _ _
    have h3 : w i = ∑ j, C0 i j * W (pderiv R j (mexp q * Φ)) := by
      rw [hw]
      simp only
      rw [mul_left_comm, hI, Pi.zero_apply, zero_mul, zero_add]
    rw [h3]
    simp only [h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [add_comm, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hx : (fun i => w i - ∑ j, C i j * g j) = 0 := by
    refine eq_zero_of_one_sub_mulVec hN fun i => ?_
    simp only [Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hrec i]
    have h4 : ∑ j, C i j * g j =
        ∑ j, C0 i j * g j + ∑ l, (∑ k, C0 i k * H k l) * ∑ j, C l j * g j := by
      conv_lhs => simp only [hC i]
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h4]
    ring
  have := congrFun hx i
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact this

end Quad

end Virasoro.Sphere
