import Virasoro.Proofs.TransverseBasis
import Virasoro.Proofs.PartEnum
import Virasoro.Proofs.VecSimp
import Virasoro.Proofs.Sec4Core1

/-!
# Auxiliary facts for the explicit Ising computations

Small Euler coefficients, the coefficients `F_0`, `F_1` and `H_1`, `H_2`, `H_3`, `H_4`, root
multiplicities of factored polynomials, and residues of sums.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

section Euler

theorem eta_one : eta 1 = -1 := by
  have h : (∏ m ∈ Finset.Icc 1 1, (1 - (X : ℤ[X]) ^ m)) = 1 - X := by simp
  rw [eta, h]
  simp [coeff_one, coeff_X]

theorem eta_two : eta 2 = -1 := by
  have h : (∏ m ∈ Finset.Icc 1 2, (1 - (X : ℤ[X]) ^ m)) = 1 - X - X ^ 2 + X ^ 3 := by
    rw [show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} from by decide,
      Finset.prod_pair (by norm_num)]
    ring
  rw [eta, h]
  simp [coeff_one, coeff_X, coeff_X_pow]

theorem eta_three : eta 3 = 0 := by
  have h : (∏ m ∈ Finset.Icc 1 3, (1 - (X : ℤ[X]) ^ m))
      = 1 - X - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by
    rw [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} from by decide,
      Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)]
    ring
  rw [eta, h]
  simp [coeff_one, coeff_X, coeff_X_pow]

theorem eta_four : eta 4 = 0 := by
  have h : (∏ m ∈ Finset.Icc 1 4, (1 - (X : ℤ[X]) ^ m))
      = 1 - X - X ^ 2 + 2 * X ^ 5 - X ^ 8 - X ^ 9 + X ^ 10 := by
    rw [show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} from by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)]
    ring
  rw [eta, h]
  simp [coeff_one, coeff_X, coeff_X_pow]

end Euler

variable {K : Type*} [Field K] [CharZero K]

theorem Hrat_three (c d : K) : Hrat c d 3 = Frat c d 3 - Frat c d 2 - Frat c d 1 := by
  simp [Hrat, Finset.sum_range_succ, eta_zero, eta_one, eta_two, eta_three]
  ring

theorem Hrat_four (c d : K) : Hrat c d 4 = Frat c d 4 - Frat c d 3 - Frat c d 2 := by
  simp [Hrat, Finset.sum_range_succ, eta_zero, eta_one, eta_two, eta_three, eta_four]
  ring

theorem gram_zero (c z : K) : gram c z 0 = 1 := by
  ext Y Y'
  rw [Subsingleton.elim Y Y']
  simp [gram, partition_zero_word, gramWord, vac]

theorem Fval_zero (c d z : K) : Fval c d z 0 = 1 := by
  have ht : ∀ Y Y' : Nat.Partition 0, torus c z d 0 Y Y' = 1 := by
    intro Y Y'
    simp [torus, partition_zero_word, torusWord, phi]
  unfold Fval
  rw [gram_zero, Matrix.det_one, Matrix.adjugate_one]
  simp [ht, Matrix.one_apply]

theorem Hval_one (c d z : K) : Hval c d z 1 = Fval c d z 1 - 1 := by
  simp [Hval, Finset.sum_range_succ, eta_zero, eta_one, Fval_zero]
  ring

theorem Hval_two (c d z : K) : Hval c d z 2 = Fval c d z 2 - Fval c d z 1 - 1 := by
  simp [Hval, Finset.sum_range_succ, eta_zero, eta_one, eta_two, Fval_zero]
  ring

/-- The partition of `1`. -/
noncomputable def e1 : Nat.Partition 1 ≃ Fin 1 := isEnum_one.equiv

theorem word_one' (Y : Nat.Partition 1) : Y.word = [1] := by
  have := isEnum_one.word_mem Y
  simpa using this

/-- `F_1(c,z,d) = ρ_1(c,z,d)/G_1(c,z)`. -/
theorem Fval_one (c d z : K) :
    Fval c d z 1 = torusWord c z d [1] [1] / gramWord c z [1] [1] := by
  have : Unique (Nat.Partition 1) := e1.unique
  unfold Fval
  rw [Fintype.sum_unique, Fintype.sum_unique, Matrix.adjugate_subsingleton, Matrix.det_unique,
    Matrix.one_apply_eq, one_mul]
  simp only [gram, torus, Matrix.of_apply, word_one']

theorem gram_one_det (c z : K) : (gram c z 1).det = 2 * z := by
  have : Unique (Nat.Partition 1) := e1.unique
  rw [Matrix.det_unique]
  simp [gram, word_one', gramWord, actSt, actWord, vac]

omit [CharZero K] in
theorem rootMultiplicity_of_factor {p q : K[X]} {a : K} {n : ℕ} (hp : p = (X - C a) ^ n * q)
    (hq : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  have hne : (X - C a) ^ n * q ≠ 0 := mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a)) hq0
  rw [hp, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hq,
    add_zero]

/-- If `G_N(c,h)` is invertible then `G_N(c,h+x)⁻¹` has no pole. -/
theorem poleOrderInv_le_one_of_det_ne (c h : K) (N : ℕ) (hdet : (gram c h N).det ≠ 0) :
    poleOrderInv (gramLocal c h N) ≤ 1 := by
  refine ((cross1_main (gramLocal_isSymm c h N) (gramLocal_det_ne_zero c h N)).1 ?_).1
  intro v hv _
  rw [mem_ker0, coeffMat_zero_gramLocal] at hv
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hv

theorem ppCoeff_add (f g : RatFunc K) (a : K) (k : ℕ) :
    ppCoeff (f + g) a k = ppCoeff f a k + ppCoeff g a k := by
  unfold ppCoeff lcoeff
  rw [expandAt_eq, expandAt_eq, expandAt_eq, map_add, HahnSeries.coeff_add]

theorem ppCoeff_sub (f g : RatFunc K) (a : K) (k : ℕ) :
    ppCoeff (f - g) a k = ppCoeff f a k - ppCoeff g a k := by
  unfold ppCoeff lcoeff
  rw [expandAt_eq, expandAt_eq, expandAt_eq, map_sub, HahnSeries.coeff_sub]

/-- A rational function regular at `a` has no principal part there. -/
theorem ppCoeff_eq_zero_of_regAt {f : RatFunc K} {a : K} (h : RegAt a f) {k : ℕ} (hk : 1 ≤ k) :
    ppCoeff f a k = 0 := by
  unfold ppCoeff lcoeff
  have hf : expandAt f a = expandHom a
      (algebraMap K[X] (RatFunc K) (RatFunc.num f)
        / algebraMap K[X] (RatFunc K) (RatFunc.denom f)) := by
    rw [RatFunc.num_div_denom, expandAt_eq]
  rw [hf, map_div₀, expandHom_algebraMap, expandHom_algebraMap]
  have h1 := regVal_ofPowerSeries (shiftPS a (RatFunc.num f))
  have h2 := regVal_ofPowerSeries (shiftPS a (RatFunc.denom f))
  rw [constantCoeff_shiftPS] at h2
  exact (h1.div h2 h).1.coeff_eq_zero (by omega)

end Virasoro
