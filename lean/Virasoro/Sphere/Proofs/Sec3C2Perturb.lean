import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# A finite-dimensional perturbation lemma (sphere paper, Lemma 3.7, Step 2)

sphere/paper.tex l.1084–1090: a rectangular linear system that is injective at `λ^{-2} = 0`
has a left inverse there, which stays invertible for all sufficiently large `λ`; the solution
is regular at `λ^{-2} = 0`.  For `S(s) = S₀ + s S₁` on a finite-dimensional space with `S₀`
injective and `L S₀ = id`: `L S(s) = id + s L S₁` has determinant tending to `1`, so `S(s)` is
injective for small `s`, and a family of solutions `S(s) y = r₀` converges to a solution of
`S₀ r = r₀`.
-/

namespace Virasoro.Sphere

open Filter Topology

theorem tendsto_inv_one_add_smul {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) {T : Type*}
    (l : Filter T) (σ : T → ℂ) (hσ : Tendsto σ l (𝓝 0)) :
    (∀ᶠ t in l, (1 + σ t • M).det ≠ 0) ∧
      ∀ i j, Tendsto (fun t => (1 + σ t • M)⁻¹ i j) l (𝓝 ((1 : Matrix (Fin d) (Fin d) ℂ) i j)) := by
  have hf : Continuous fun s : ℂ => (1 + s • M : Matrix (Fin d) (Fin d) ℂ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdet : Continuous fun s : ℂ => (1 + s • M).det := hf.matrix_det
  have hd0 : (1 + (0 : ℂ) • M).det = 1 := by rw [zero_smul, add_zero, Matrix.det_one]
  have h1 : Tendsto (fun t => (1 + σ t • M).det) l (𝓝 1) := by
    have h := (hdet.tendsto 0).comp hσ
    rwa [hd0] at h
  refine ⟨h1.eventually_ne one_ne_zero, fun i j => ?_⟩
  have hg : ContinuousAt (fun s : ℂ => ((1 + s • M).det)⁻¹ • (1 + s • M).adjugate) 0 :=
    (hdet.continuousAt.inv₀ (by rw [hd0]; exact one_ne_zero)).smul hf.matrix_adjugate.continuousAt
  have hg0 : ((1 + (0 : ℂ) • M).det)⁻¹ • (1 + (0 : ℂ) • M).adjugate = 1 := by
    rw [hd0, zero_smul, add_zero, Matrix.adjugate_one, inv_one, one_smul]
  have h2 : Tendsto (fun t => ((1 + σ t • M).det)⁻¹ • (1 + σ t • M).adjugate) l (𝓝 1) := by
    have h := hg.tendsto.comp hσ
    rwa [hg0] at h
  have h3 := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h2 i)) j
  refine h3.congr fun t => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X] [AddCommGroup Y]
  [Module ℂ Y]

set_option maxHeartbeats 800000 in
theorem perturb_limit (S0 S1 : X →ₗ[ℂ] Y) (hS : LinearMap.ker S0 = ⊥) {T : Type*} (l : Filter T)
    [l.NeBot] (σ : T → ℂ) (hσ : Tendsto σ l (𝓝 0)) :
    (∀ᶠ t in l, LinearMap.ker (S0 + σ t • S1) = ⊥) ∧
    ∀ (y : T → X) (r0 : Y), (∀ᶠ t in l, S0 (y t) + σ t • S1 (y t) = r0) →
      ∃ r : X, S0 r = r0 ∧ ∀ φ : X →ₗ[ℂ] ℂ, Tendsto (fun t => φ (y t)) l (𝓝 (φ r)) := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective S0 hS
  obtain ⟨hdet, hinv⟩ := tendsto_inv_one_add_smul
    (LinearMap.toMatrix (Module.finBasis ℂ X) (Module.finBasis ℂ X) (L ∘ₗ S1)) l σ hσ
  have hA : ∀ s : ℂ, LinearMap.toMatrix (Module.finBasis ℂ X) (Module.finBasis ℂ X)
      (L ∘ₗ (S0 + s • S1)) =
      1 + s • LinearMap.toMatrix (Module.finBasis ℂ X) (Module.finBasis ℂ X) (L ∘ₗ S1) := by
    intro s
    rw [LinearMap.comp_add, hL, LinearMap.comp_smul, map_add, map_smul, LinearMap.toMatrix_id]
  have hcoord : ∀ (s : ℂ) (x : X),
      (1 + s • LinearMap.toMatrix (Module.finBasis ℂ X) (Module.finBasis ℂ X) (L ∘ₗ S1)).mulVec
        (fun i => (Module.finBasis ℂ X).repr x i) =
      fun i => (Module.finBasis ℂ X).repr (L (S0 x + s • S1 x)) i := by
    intro s x
    rw [← hA]
    exact LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ X) (Module.finBasis ℂ X)
      (L ∘ₗ (S0 + s • S1)) x
  have hphi : ∀ (φ : X →ₗ[ℂ] ℂ) (x : X),
      φ x = ∑ i, (Module.finBasis ℂ X).repr x i * φ (Module.finBasis ℂ X i) := by
    intro φ x
    conv_lhs => rw [← (Module.finBasis ℂ X).sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · filter_upwards [hdet] with t ht
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hcoord (σ t) x
    have hx' : S0 x + σ t • S1 x = 0 := hx
    rw [hx', map_zero] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero ht (h1.trans (by funext i; simp))
    exact (Module.finBasis ℂ X).repr.map_eq_zero_iff.mp (Finsupp.ext fun i => congrFun h2 i)
  · intro y r0 hy
    have hrep : ∀ i, Tendsto (fun t => (Module.finBasis ℂ X).repr (y t) i) l
        (𝓝 ((Module.finBasis ℂ X).repr (L r0) i)) := by
      intro i
      have h1 : Tendsto (fun t => ∑ j,
          (1 + σ t • LinearMap.toMatrix (Module.finBasis ℂ X) (Module.finBasis ℂ X)
            (L ∘ₗ S1))⁻¹ i j * (Module.finBasis ℂ X).repr (L r0) j) l
          (𝓝 (∑ j, (1 : Matrix _ _ ℂ) i j * (Module.finBasis ℂ X).repr (L r0) j)) :=
        tendsto_finsetSum _ fun j _ => (hinv i j).mul tendsto_const_nhds
      have h2 : (∑ j, (1 : Matrix (Fin (Module.finrank ℂ X)) (Fin (Module.finrank ℂ X)) ℂ) i j *
          (Module.finBasis ℂ X).repr (L r0) j) = (Module.finBasis ℂ X).repr (L r0) i := by
        have h := congrFun (Matrix.one_mulVec (fun j => (Module.finBasis ℂ X).repr (L r0) j)) i
        simpa [Matrix.mulVec, dotProduct] using h
      rw [h2] at h1
      refine h1.congr' ?_
      filter_upwards [hdet, hy] with t ht hyt
      have h3 := hcoord (σ t) (y t)
      rw [hyt] at h3
      have h4 := congrArg (fun v => ((1 + σ t • LinearMap.toMatrix (Module.finBasis ℂ X)
        (Module.finBasis ℂ X) (L ∘ₗ S1))⁻¹).mulVec v) h3
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht),
        Matrix.one_mulVec] at h4
      have h5 := congrFun h4 i
      simp only [Matrix.mulVec, dotProduct] at h5
      exact h5.symm
    have hlim : ∀ φ : X →ₗ[ℂ] ℂ, Tendsto (fun t => φ (y t)) l (𝓝 (φ (L r0))) := by
      intro φ
      rw [hphi φ (L r0)]
      have h1 : Tendsto (fun t => ∑ i, (Module.finBasis ℂ X).repr (y t) i *
          φ (Module.finBasis ℂ X i)) l
          (𝓝 (∑ i, (Module.finBasis ℂ X).repr (L r0) i * φ (Module.finBasis ℂ X i))) :=
        tendsto_finsetSum _ fun i _ => (hrep i).mul tendsto_const_nhds
      exact h1.congr fun t => (hphi φ (y t)).symm
    refine ⟨L r0, ?_, hlim⟩
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro ψ
    have h1 : Tendsto (fun t => (ψ ∘ₗ S0) (y t) + σ t * (ψ ∘ₗ S1) (y t)) l
        (𝓝 ((ψ ∘ₗ S0) (L r0) + 0 * (ψ ∘ₗ S1) (L r0))) :=
      (hlim (ψ ∘ₗ S0)).add (hσ.mul (hlim (ψ ∘ₗ S1)))
    have h2 : Tendsto (fun t => (ψ ∘ₗ S0) (y t) + σ t * (ψ ∘ₗ S1) (y t)) l (𝓝 (ψ r0)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hy] with t hyt
      rw [← hyt, map_add, map_smul, smul_eq_mul]
      rfl
    have h3 := tendsto_nhds_unique h1 h2
    rw [zero_mul, add_zero] at h3
    rw [map_sub, sub_eq_zero]
    exact h3

end Virasoro.Sphere
