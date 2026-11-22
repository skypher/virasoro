import Virasoro.Sphere.Proofs.Sec3GaussFock
import Virasoro.Sphere.Proofs.Sec3GaussQuad
import Virasoro.Sphere.Proofs.Sec3SaddlePde2
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Ring.GeomSum

/-!
# The perturbed Hessian and its Neumann inverse (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.642–661.  The quadratic part of `S^{(0)}(z^• u) + S̃^{(0)}(ū)` is
`q = ∑ B_{m,n} (u_m u_n + ū_m ū_n)` (with `z^m` carried by the pairing).  With
`N = Q₀⁻¹(Q₀ - Q) = (0, M; M, 0)`, `M_{m,n} = z^m B_{m,n}/m`, which is nilpotent when
`z^{K+1} = 0`, the covariance of the perturbed Gaussian is the finite Neumann sum
`(∑_{r ≤ K} N^r) C₀`, and `Φ ↦ P(e^q Φ)` satisfies the Wick rule with this covariance.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries Matrix

section Cov

variable (n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R]

/-- `q = ∑_{m,n} B_{m,n} (u_m u_n + ū_m ū_n)`. -/
noncomputable def quadB : MvPowerSeries (Modes n) R :=
  ∑ i : Fin n, ∑ j : Fin n,
    MvPowerSeries.C (algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1))) *
      (X (Sum.inl i) * X (Sum.inl j) + X (Sum.inr i) * X (Sum.inr j))

/-- The Hessian of `q`. -/
noncomputable def hessB : Modes n → Modes n → R
  | Sum.inl i, Sum.inl j => algebraMap ℚ R (2 * Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1))
  | Sum.inr i, Sum.inr j => algebraMap ℚ R (2 * Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1))
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

theorem constantCoeff_quadB : constantCoeff (quadB n R) = 0 := by
  simp [quadB]

theorem pderiv_quad_term (a p q r s : Modes n) (c : R) :
    pderiv R a (MvPowerSeries.C c * (X p * X q + X r * X s)) =
      MvPowerSeries.C c * ((if p = a then X q else 0) + (if q = a then X p else 0) +
        ((if r = a then X s else 0) + (if s = a then X r else 0))) := by
  rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, map_add, Derivation.leibniz,
    Derivation.leibniz, pderiv_X, pderiv_X, pderiv_X, pderiv_X]
  simp only [Pi.single_apply, smul_eq_mul]
  congr 1
  by_cases hp : p = a <;> by_cases hq : q = a <;> by_cases hr : r = a <;> by_cases hs : s = a <;>
    simp [hp, hq, hr, hs] <;> ring

theorem pderiv_quadB (a : Modes n) :
    pderiv R a (quadB n R) = ∑ k, MvPowerSeries.C (hessB n R a k) * X k := by
  rw [quadB, map_sum, Fintype.sum_sum_type]
  simp only [map_sum, pderiv_quad_term]
  rcases a with m | m
  · simp only [hessB, map_zero, zero_mul, Finset.sum_const_zero, add_zero, Sum.inl.injEq,
      reduceCtorEq, if_false]
    have h1 : ∀ i : Fin n, ∑ j : Fin n,
        MvPowerSeries.C (algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1))) *
          ((if i = m then (X (Sum.inl j) : MvPowerSeries (Modes n) R) else 0) +
            (if j = m then X (Sum.inl i) else 0)) =
        (if i = m then ∑ j : Fin n,
          MvPowerSeries.C (algebraMap ℚ R (Bcoef ((m : ℕ) + 1) ((j : ℕ) + 1))) *
            X (Sum.inl j) else 0) +
        MvPowerSeries.C (algebraMap ℚ R (Bcoef ((m : ℕ) + 1) ((i : ℕ) + 1))) *
          X (Sum.inl i) := by
      intro i
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Bcoef_symm ((i : ℕ) + 1) ((m : ℕ) + 1)]
      congr 1
      by_cases hi : i = m
      · subst hi
        simp
      · simp [hi]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_mul, ← map_add, ← map_add]
    congr 3
    ring
  · simp only [hessB, map_zero, zero_mul, Finset.sum_const_zero, zero_add, Sum.inr.injEq,
      reduceCtorEq, if_false]
    have h1 : ∀ i : Fin n, ∑ j : Fin n,
        MvPowerSeries.C (algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1))) *
          ((if i = m then (X (Sum.inr j) : MvPowerSeries (Modes n) R) else 0) +
            (if j = m then X (Sum.inr i) else 0)) =
        (if i = m then ∑ j : Fin n,
          MvPowerSeries.C (algebraMap ℚ R (Bcoef ((m : ℕ) + 1) ((j : ℕ) + 1))) *
            X (Sum.inr j) else 0) +
        MvPowerSeries.C (algebraMap ℚ R (Bcoef ((m : ℕ) + 1) ((i : ℕ) + 1))) *
          X (Sum.inr i) := by
      intro i
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Bcoef_symm ((i : ℕ) + 1) ((m : ℕ) + 1)]
      congr 1
      by_cases hi : i = m
      · subst hi
        simp
      · simp [hi]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_mul, ← map_add, ← map_add]
    congr 3
    ring

variable {R} (φ : PowerSeries ℚ →+* R)

theorem phi_C (q : ℚ) : φ (PowerSeries.C q) = algebraMap ℚ R q :=
  RingHom.congr_fun (Subsingleton.elim (φ.comp PowerSeries.C) (algebraMap ℚ R)) q

/-- `M(z)_{m,n} = z^m B_{m,n}/m` over `R`. -/
noncomputable def MR : Matrix (Fin n) (Fin n) R := (Mmat n).map φ

/-- `E = diag(z^m/(2m))`, the covariance `Cov(u_m, ū_m)` of `Q₀`. -/
noncomputable def ER : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i =>
    algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * φ PowerSeries.X ^ ((i : ℕ) + 1)

/-- `N = Q₀⁻¹(Q₀ - Q)`: the block matrix `(0, M; M, 0)`. -/
noncomputable def NR : Matrix (Modes n) (Modes n) R :=
  Matrix.fromBlocks 0 (MR n φ) (MR n φ) 0

/-- The Neumann inverse `(∑_{r ≤ K} N^r) C₀`: the covariance of the perturbed Gaussian. -/
noncomputable def covN (K : ℕ) : Matrix (Modes n) (Modes n) R :=
  (∑ r ∈ range (K + 1), NR n φ ^ r) * Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0

theorem MR_apply (i j : Fin n) :
    MR n φ i j = algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) *
      φ PowerSeries.X ^ ((i : ℕ) + 1) := by
  rw [MR, Matrix.map_apply, Mmat, Matrix.of_apply, map_mul, map_pow, phi_C]

theorem cov0_eq :
    Matrix.of (cov0 n (φ PowerSeries.X)) = Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [cov0, ER, Matrix.diagonal_apply]

theorem NR_eq :
    (Matrix.of fun i l => ∑ k, cov0 n (φ PowerSeries.X) i k * hessB n R k l) = NR n φ := by
  ext i l
  rw [Matrix.of_apply, Fintype.sum_sum_type]
  have hE : ∀ a b : Fin n,
      algebraMap ℚ R (1 / (2 * (((a : ℕ) + 1 : ℕ) : ℚ))) * φ PowerSeries.X ^ ((a : ℕ) + 1) *
        algebraMap ℚ R (2 * Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1)) = MR n φ a b := by
    intro a b
    rw [MR_apply, mul_right_comm, ← map_mul]
    congr 2
    have : ((((a : ℕ) + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    field_simp
  rcases i with a | a <;> rcases l with b | b
  · simp [cov0, hessB, NR]
  · simp only [cov0, hessB, zero_mul, Finset.sum_const_zero, zero_add, NR,
      Matrix.fromBlocks_apply₁₂]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, hE]
    · intro k _ hk
      rw [if_neg (Ne.symm hk), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · simp only [cov0, hessB, zero_mul, Finset.sum_const_zero, add_zero, NR,
      Matrix.fromBlocks_apply₂₁]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, hE]
    · intro k _ hk
      rw [if_neg (Ne.symm hk), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · simp [cov0, hessB, NR]

variable {n φ} {K : ℕ}

theorem NR_pow_eq_zero (hz : φ PowerSeries.X ^ (K + 1) = 0) : NR n φ ^ (K + 1) = 0 := by
  have h1 : MR n φ = φ PowerSeries.X •
      (Matrix.of fun i j : Fin n =>
        algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) *
          φ PowerSeries.X ^ (i : ℕ)) := by
    ext i j
    rw [MR_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, pow_succ]
    ring
  have h2 : NR n φ = φ PowerSeries.X • Matrix.fromBlocks 0
      (Matrix.of fun i j : Fin n =>
        algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) *
          φ PowerSeries.X ^ (i : ℕ))
      (Matrix.of fun i j : Fin n =>
        algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) *
          φ PowerSeries.X ^ (i : ℕ)) 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero, ← h1, NR]
  rw [h2, smul_pow, hz, zero_smul]

theorem covN_eq (hz : φ PowerSeries.X ^ (K + 1) = 0) :
    covN n φ K = Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 + NR n φ * covN n φ K := by
  have hg := mul_geom_sum (NR n φ) (K + 1)
  rw [NR_pow_eq_zero hz, zero_sub, sub_mul, one_mul] at hg
  have hS : ∑ r ∈ range (K + 1), NR n φ ^ r =
      1 + NR n φ * ∑ r ∈ range (K + 1), NR n φ ^ r := by
    have h3 : 1 + NR n φ * ∑ r ∈ range (K + 1), NR n φ ^ r -
        ∑ r ∈ range (K + 1), NR n φ ^ r = 0 := by
      rw [show (1 : Matrix (Modes n) (Modes n) R) + NR n φ * ∑ r ∈ range (K + 1), NR n φ ^ r -
          ∑ r ∈ range (K + 1), NR n φ ^ r =
        (NR n φ * ∑ r ∈ range (K + 1), NR n φ ^ r - ∑ r ∈ range (K + 1), NR n φ ^ r) + 1 by
          abel, hg, neg_add_cancel]
    exact (sub_eq_zero.1 h3).symm
  rw [covN, ← Matrix.mul_assoc]
  conv_lhs => rw [hS]
  rw [add_mul, one_mul]

/-- Absorbing the quadratic part (sphere/paper.tex l.642–661): `Φ ↦ P(e^q Φ)` satisfies the Wick
rule with the Neumann covariance. -/
theorem fockP_quad_ibp (hz : φ PowerSeries.X ^ (K + 1) = 0) :
    IBP ((fockP n K (φ PowerSeries.X)).comp (LinearMap.mulLeft R (mexp (quadB n R)))) 0
      (fun i j => covN n φ K i j) := by
  refine ibp_quadratic (fockP_ibp hz) (quadB n R) (constantCoeff_quadB n R) (hessB n R)
    (pderiv_quadB n R) ?_ _ fun i j => ?_
  · rw [NR_eq]
    exact ⟨K + 1, NR_pow_eq_zero hz⟩
  · have h1 := congrFun (congrFun (covN_eq (n := n) (φ := φ) hz) i) j
    rw [Matrix.add_apply, Matrix.mul_apply, ← cov0_eq, Matrix.of_apply] at h1
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← NR_eq, Matrix.of_apply]

end Cov

end Virasoro.Sphere
