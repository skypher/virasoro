import Virasoro.Sphere.Proofs.Sec3GaussCov
import Virasoro.Sphere.Saddle
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing

/-!
# The Neumann block inverse (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.656–661: the block inverse
`Q(z)⁻¹ = ½ (K₂₁M₂D⁻¹, K₂₁D⁻¹; K₁₂D⁻¹, K₁₂M₁D⁻¹)`, `K₂₁ = (I - M₂M₁)⁻¹`,
`K₁₂ = (I - M₁M₂)⁻¹`.  In the variables `U_m = z^m ξ_m`, `V_m = ξ̄_m` the covariance blocks are
`covUU`, `covUV`, `covVV`; here they are shown to invert `1 - N`, `N = (0, M; M, 0)`, against the
unperturbed covariance `(0, E; E, 0)`, over `ℂ[[z]]`.
-/

namespace Virasoro.Sphere

open Matrix

section Abstract

variable {A : Type*} [Ring A] (z d m2 k21 k12 : A)

/-- The four block identities of `(1 - N) C = C₀`, with `M = z m₂`, `M₁ = z m₂ z`, `M₂ = m₂`,
`k₂₁ = (1 - M₂M₁)⁻¹`, `k₁₂ = (1 - M₁M₂)⁻¹`. -/
theorem cov_alg (hzd : z * d = d * z)
    (h21 : (1 - m2 * z * (m2 * z)) * k21 = 1) (h21' : k21 * (1 - m2 * z * (m2 * z)) = 1)
    (h12' : k12 * (1 - z * m2 * (z * m2)) = 1) :
    z * (k21 * m2 * d) * z = z * m2 * (z * (k21 * d)) ∧
    z * (k21 * d) - z * m2 * (k12 * (z * m2 * z) * d) = z * d ∧
    z * (k21 * d) - z * m2 * (z * (k21 * m2 * d) * z) = z * d ∧
    k12 * (z * m2 * z) * d = z * m2 * (z * (k21 * d)) := by
  have hc : k21 * (m2 * z) = m2 * z * k21 := by
    calc k21 * (m2 * z) = k21 * (m2 * z) * ((1 - m2 * z * (m2 * z)) * k21) := by
          rw [h21, mul_one]
      _ = k21 * (1 - m2 * z * (m2 * z)) * (m2 * z) * k21 := by noncomm_ring
      _ = m2 * z * k21 := by rw [h21', one_mul]
  have hb : k12 * (z * m2 * z) = z * m2 * z * k21 := by
    calc k12 * (z * m2 * z) = k12 * (z * m2 * z) * ((1 - m2 * z * (m2 * z)) * k21) := by
          rw [h21, mul_one]
      _ = k12 * (1 - z * m2 * (z * m2)) * (z * m2 * z) * k21 := by noncomm_ring
      _ = z * m2 * z * k21 := by rw [h12', one_mul]
  have hw : z * (m2 * z * (m2 * z)) * k21 * d = z * (k21 * d) - z * d := by
    calc z * (m2 * z * (m2 * z)) * k21 * d
        = z * (k21 * d) - z * ((1 - m2 * z * (m2 * z)) * k21) * d := by noncomm_ring
      _ = z * (k21 * d) - z * d := by rw [h21, mul_one]
  have e1 : z * (k21 * m2 * d) * z = z * m2 * (z * (k21 * d)) := by
    calc z * (k21 * m2 * d) * z = z * (k21 * m2) * (d * z) := by noncomm_ring
      _ = z * (k21 * (m2 * z)) * d := by rw [← hzd]; noncomm_ring
      _ = z * m2 * (z * (k21 * d)) := by rw [hc]; noncomm_ring
  refine ⟨e1, ?_, ?_, ?_⟩
  · have : z * m2 * (k12 * (z * m2 * z) * d) = z * (m2 * z * (m2 * z)) * k21 * d := by
      rw [hb]
      noncomm_ring
    rw [this, hw]
    noncomm_ring
  · have : z * m2 * (z * (k21 * m2 * d) * z) = z * (m2 * z * (m2 * z)) * k21 * d := by
      rw [e1]
      noncomm_ring
    rw [this, hw]
    noncomm_ring
  · rw [hb]
    noncomm_ring

end Abstract

section Mat

variable (N : ℕ)

local notation "P" => PowerSeries ℂ

/-- `ℚ[[z]] → ℂ[[z]]`. -/
noncomputable def phiP : PowerSeries ℚ →+* P := PowerSeries.map (algebraMap ℚ ℂ)

/-- `Z = diag(z, …, z^N)`. -/
noncomputable def ZP : Matrix (Fin N) (Fin N) P :=
  Matrix.diagonal fun i => (PowerSeries.X : P) ^ ((i : ℕ) + 1)

theorem M1mat_eq : M1mat N = ZP N * M2mat N * ZP N := by
  ext i j
  rw [ZP, Matrix.mul_diagonal, Matrix.diagonal_mul, M1mat, M2mat, Matrix.of_apply,
    Matrix.of_apply, pow_add]
  ring

theorem MR_phiP : MR N phiP = ZP N * M2mat N := by
  ext i j
  rw [MR_apply, ZP, Matrix.diagonal_mul, M2mat, Matrix.of_apply, ← phi_C phiP, phiP,
    PowerSeries.map_C, PowerSeries.map_X,
    show (algebraMap ℚ ℂ) (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) =
      (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) : ℂ) / (((i : ℕ) + 1 : ℕ) : ℂ) by simp, mul_comm]

theorem ER_phiP : ER N phiP = PowerSeries.C (1 / 2 : ℂ) • (ZP N * DinvMat N) := by
  rw [ER, ZP, DinvMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  rw [Pi.smul_apply, smul_eq_mul, ← phi_C phiP, phiP, PowerSeries.map_C, PowerSeries.map_X,
    show (algebraMap ℚ ℂ) (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) =
      (1 / 2 : ℂ) * (1 / (((i : ℕ) + 1 : ℕ) : ℂ)) by
        rw [eq_ratCast]; push_cast; rw [div_mul_div_comm, one_mul], map_mul]
  ring

theorem ZP_Dinv_comm : ZP N * DinvMat N = DinvMat N * ZP N := by
  rw [ZP, DinvMat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem isUnit_det_one_sub (A : Matrix (Fin N) (Fin N) P)
    (hA : ∀ i j, PowerSeries.constantCoeff (A i j) = 0) : IsUnit (1 - A).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have h : (PowerSeries.constantCoeff (R := ℂ)).mapMatrix (1 - A) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, hA, sub_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h, Matrix.det_one]
  exact isUnit_one

theorem constantCoeff_ZP_mul (A : Matrix (Fin N) (Fin N) P) (i j : Fin N) :
    PowerSeries.constantCoeff ((ZP N * A) i j) = 0 := by
  rw [ZP, Matrix.diagonal_mul, map_mul, map_pow, PowerSeries.constantCoeff_X,
    zero_pow (Nat.succ_ne_zero _), zero_mul]

theorem constantCoeff_mul_ZP (A : Matrix (Fin N) (Fin N) P) (i j : Fin N) :
    PowerSeries.constantCoeff ((A * ZP N) i j) = 0 := by
  rw [ZP, Matrix.mul_diagonal, map_mul, map_pow, PowerSeries.constantCoeff_X,
    zero_pow (Nat.succ_ne_zero _), mul_zero]

theorem covUU_eq : covUU N = PowerSeries.C (1 / 2 : ℂ) •
    (ZP N * ((1 - M2mat N * ZP N * (M2mat N * ZP N))⁻¹ * M2mat N * DinvMat N) * ZP N) := by
  ext i j
  rw [covUU, Matrix.of_apply, Matrix.smul_apply, ZP, Matrix.mul_diagonal, Matrix.diagonal_mul,
    ← ZP, M1mat_eq, smul_eq_mul, pow_add,
    show M2mat N * (ZP N * M2mat N * ZP N) = M2mat N * ZP N * (M2mat N * ZP N) by
      simp only [Matrix.mul_assoc]]
  ring

theorem covUV_eq : covUV N = PowerSeries.C (1 / 2 : ℂ) •
    (ZP N * ((1 - M2mat N * ZP N * (M2mat N * ZP N))⁻¹ * DinvMat N)) := by
  ext i j
  rw [covUV, Matrix.of_apply, Matrix.smul_apply, ZP, Matrix.diagonal_mul,
    ← ZP, M1mat_eq, smul_eq_mul,
    show M2mat N * (ZP N * M2mat N * ZP N) = M2mat N * ZP N * (M2mat N * ZP N) by
      simp only [Matrix.mul_assoc]]
  ring

theorem covVV_eq : covVV N = PowerSeries.C (1 / 2 : ℂ) •
    ((1 - ZP N * M2mat N * (ZP N * M2mat N))⁻¹ * (ZP N * M2mat N * ZP N) * DinvMat N) := by
  ext i j
  rw [covVV, Matrix.of_apply, Matrix.smul_apply, M1mat_eq, smul_eq_mul,
    show ZP N * M2mat N * ZP N * M2mat N = ZP N * M2mat N * (ZP N * M2mat N) by
      simp only [Matrix.mul_assoc]]

/-- The Neumann block inverse (sphere/paper.tex l.656–661): the covariance blocks of `(U, V)`
invert `1 - N` against the unperturbed covariance. -/
theorem cand_eq :
    (1 - NR N phiP) * Matrix.fromBlocks (covUU N) (covUV N) (covUV N) (covVV N) =
      Matrix.fromBlocks 0 (ER N phiP) (ER N phiP) 0 := by
  have hu1 : IsUnit (1 - M2mat N * ZP N * (M2mat N * ZP N)).det :=
    isUnit_det_one_sub N _ fun i j => by
      rw [← Matrix.mul_assoc]
      exact constantCoeff_mul_ZP N _ i j
  have hu2 : IsUnit (1 - ZP N * M2mat N * (ZP N * M2mat N)).det :=
    isUnit_det_one_sub N _ fun i j => by
      rw [Matrix.mul_assoc]
      exact constantCoeff_ZP_mul N _ i j
  obtain ⟨e1, e2, e3, e4⟩ := cov_alg (ZP N) (DinvMat N) (M2mat N)
    (1 - M2mat N * ZP N * (M2mat N * ZP N))⁻¹ (1 - ZP N * M2mat N * (ZP N * M2mat N))⁻¹
    (ZP_Dinv_comm N) (Matrix.mul_nonsing_inv _ hu1) (Matrix.nonsing_inv_mul _ hu1)
    (Matrix.nonsing_inv_mul _ hu2)
  have b1 : covUU N = MR N phiP * covUV N := by
    rw [MR_phiP, covUU_eq, covUV_eq, Matrix.mul_smul, e1]
  have b4 : covVV N = MR N phiP * covUV N := by
    rw [MR_phiP, covVV_eq, covUV_eq, Matrix.mul_smul, e4]
  have b2 : covUV N - MR N phiP * covVV N = ER N phiP := by
    rw [MR_phiP, covUV_eq, covVV_eq, ER_phiP, Matrix.mul_smul, ← smul_sub, e2]
  have b3 : covUV N - MR N phiP * covUU N = ER N phiP := by
    rw [MR_phiP, covUV_eq, covUU_eq, ER_phiP, Matrix.mul_smul, ← smul_sub, e3]
  have hN : NR N phiP * Matrix.fromBlocks (covUU N) (covUV N) (covUV N) (covVV N) =
      Matrix.fromBlocks (MR N phiP * covUV N) (MR N phiP * covVV N) (MR N phiP * covUU N)
        (MR N phiP * covUV N) := by
    rw [NR, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, zero_add, add_zero]
  rw [sub_mul, one_mul, hN, sub_eq_iff_eq_add, Matrix.fromBlocks_add]
  congr 1
  · rw [zero_add]
    exact b1
  · rw [← b2, sub_add_cancel]
  · rw [← b3, sub_add_cancel]
  · rw [zero_add]
    exact b4

end Mat

end Virasoro.Sphere
