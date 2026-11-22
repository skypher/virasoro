import Virasoro.Sphere.Proofs.Sec3GaussCov
import Virasoro.Sphere.Proofs.Sec3GaussQuad

/-!
# The saddle point as `C J` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.656–668.  With `C` the Neumann covariance of the perturbed Hessian, the
shift `x = C J` produced by completing the square is the unique solution of the saddle-point
equations `x_{u,m} = (z^m/2m) J_{ū,m} + ∑_n (B_{m,n}/m) z^m x_{ū,n}` and its mirror image:
uniqueness because `Q₀⁻¹(Q - Q₀)` is nilpotent modulo `z^{K+1}`.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries Matrix

section SaddleCov

variable {n K : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R] (φ : PowerSeries ℚ →+* R)

/-- `Cov(u_m, ū_m) = z^m/(2m)` for `Q₀`. -/
noncomputable def e0 (i : Fin n) : R :=
  algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * φ PowerSeries.X ^ ((i : ℕ) + 1)

variable {φ}

theorem covN_mulVec_eq (hz : φ PowerSeries.X ^ (K + 1) = 0) (J : Modes n → R) (a : Modes n) :
    ∑ b, covN n φ K a b * J b =
      ∑ b, (Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 : Matrix (Modes n) (Modes n) R) a b * J b +
        ∑ c, NR n φ a c * ∑ b, covN n φ K c b * J b := by
  have h := covN_eq (n := n) (φ := φ) (K := K) hz
  have h1 : ∀ b, covN n φ K a b =
      (Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 : Matrix (Modes n) (Modes n) R) a b +
        ∑ c, NR n φ a c * covN n φ K c b := fun b => by
    conv_lhs => rw [h]
    rw [Matrix.add_apply, Matrix.mul_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h1 b, add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The saddle-point equations satisfied by `x = C J`. -/
theorem covN_mulVec_inl (hz : φ PowerSeries.X ^ (K + 1) = 0) (J : Modes n → R) (i : Fin n) :
    ∑ b, covN n φ K (Sum.inl i) b * J b = e0 φ i * J (Sum.inr i) +
      ∑ j, MR n φ i j * ∑ b, covN n φ K (Sum.inr j) b * J b := by
  rw [covN_mulVec_eq hz J (Sum.inl i), NR]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, ER, Matrix.diagonal_apply,
    ite_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, e0]

theorem covN_mulVec_inr (hz : φ PowerSeries.X ^ (K + 1) = 0) (J : Modes n → R) (i : Fin n) :
    ∑ b, covN n φ K (Sum.inr i) b * J b = e0 φ i * J (Sum.inl i) +
      ∑ j, MR n φ i j * ∑ b, covN n φ K (Sum.inl j) b * J b := by
  rw [covN_mulVec_eq hz J (Sum.inr i), NR]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, ER, Matrix.diagonal_apply,
    ite_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, e0]

/-- Uniqueness of the saddle point (sphere/paper.tex l.663–666): a solution of the saddle-point
equations is `C J`. -/
theorem covN_mulVec_unique (hz : φ PowerSeries.X ^ (K + 1) = 0) (J y : Modes n → R)
    (hl : ∀ i, y (Sum.inl i) = e0 φ i * J (Sum.inr i) + ∑ j, MR n φ i j * y (Sum.inr j))
    (hr : ∀ i, y (Sum.inr i) = e0 φ i * J (Sum.inl i) + ∑ j, MR n φ i j * y (Sum.inl j))
    (a : Modes n) : ∑ b, covN n φ K a b * J b = y a := by
  have hN : IsNilpotent (NR n φ) := ⟨K + 1, NR_pow_eq_zero hz⟩
  have h0 := eq_zero_of_one_sub_mulVec hN
    (x := fun a => ∑ b, covN n φ K a b * J b - y a) (by
      intro a
      rcases a with i | i
      · rw [covN_mulVec_inl hz, hl, NR]
        simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, mul_sub,
          Finset.sum_sub_distrib]
        ring
      · rw [covN_mulVec_inr hz, hr, NR]
        simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mul_sub,
          Finset.sum_sub_distrib]
        ring)
  exact sub_eq_zero.1 (congrFun h0 a)

end SaddleCov

end Virasoro.Sphere
