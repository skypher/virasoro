import Virasoro.Proofs.ResidueCore3

/-!
# The residue of `F_{ℓ+M}` at a singular weight: the trace computation
-/

namespace Virasoro

open Polynomial Module

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem sum_mul_eq_trace {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n K) :
    ∑ i, ∑ j, A i j * B i j = Matrix.trace (A * B.transpose) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

variable (c h : K) (ℓ M : ℕ) (p : Nat.Partition ℓ → K)

/-- The pulled-back torus form: `ιᵀ ρ_{ℓ+M}(c,h,d) ι = ⟨χ|V_d(1)|χ⟩ ρ_M(c,h+ℓ,d)`. -/
theorem iota_torus_matrix (d : K)
    (hχ : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) ℓ p) ℓ) :
    (iotaMat c h ℓ M p).transpose * torus c h d (ℓ + M) * iotaMat c h ℓ M p
      = torusForm c h d ℓ p p • torus c (h + (ℓ : K)) d M := by
  have hT := Verma.isPrimaryPairing_pairing (c := c) (h := h) d
  refine Matrix.ext fun Z Z' => ?_
  have h1 : ((iotaMat c h ℓ M p).transpose * torus c h d (ℓ + M) * iotaMat c h ℓ M p) Z Z'
      = torusForm c h d (ℓ + M) (fun Y => iotaMat c h ℓ M p Y Z)
          (fun Y => iotaMat c h ℓ M p Y Z') := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, torusForm, dotProduct, Matrix.mulVec,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => by ring
  rw [h1, ← Verma.primary_pbwCoord hT, pbwCoord_iotaMat_col, pbwCoord_iotaMat_col,
    Verma.singular_factorization hT hχ.2.1 hχ.2.2 M Z Z', Verma.primary_pbwCoord hT,
    Matrix.smul_apply, smul_eq_mul]

/-- `Res_{Δ=h} F_{ℓ+M}(c,Δ,d) = ⟨χ|V_d(1)|χ⟩ / β_χ · F_M(c,h+ℓ,d)` for a singular vector
`χ` of level `ℓ ≥ 1` in `M(c,h)`, when `G_M(c,h+ℓ)` is invertible, `β_χ ≠ 0` and
`ord_x det G_{ℓ+M}(c,h+x) = p(M)`; the pole is simple. -/
theorem residue_Frat (d : K) (hℓ : 1 ≤ ℓ)
    (hχ : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) ℓ p) ℓ)
    (hβ : crossScalar c h p ≠ 0) (hg : (gram c (h + (ℓ : K)) M).det ≠ 0)
    (hord : (gramLocal c h (ℓ + M)).det.order
      = ((Fintype.card (Nat.Partition M) : ℕ) : ℕ∞)) :
    poleOrder (Frat c d (ℓ + M)) h ≤ 1 ∧
      ppCoeff (Frat c d (ℓ + M)) h 1
        = torusForm c h d ℓ p p / crossScalar c h p * Fval c d (h + (ℓ : K)) M := by
  classical
  obtain ⟨hpole, hR⟩ := residue_inverse c h ℓ M p hℓ hχ hβ hg hord
  obtain ⟨h1, h2⟩ := ppCoeff_Frat_of_simple c d h (ℓ + M) hpole
  refine ⟨h1, ?_⟩
  set ι := iotaMat c h ℓ M p with hι
  set g := gram c (h + (ℓ : K)) M with hgdef
  set β := crossScalar c h p with hβdef
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have hA : (β • g)⁻¹ = β⁻¹ • g⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hβ, one_smul,
      Matrix.mul_nonsing_inv _ hgu]
  have hginv : g⁻¹ = g.det⁻¹ • g.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h2, hR, sum_mul_eq_trace, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc]
  have e1 : ι.transpose * ((torus c h d (ℓ + M)).transpose * ι)
      = (ι.transpose * torus c h d (ℓ + M) * ι).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e1, iota_torus_matrix c h ℓ M p d hχ, ← sum_mul_eq_trace, hA, hginv]
  rw [show Fval c d (h + (ℓ : K)) M
      = (∑ Y, ∑ Y', g.adjugate Y Y' * torus c (h + (ℓ : K)) d M Y Y') / g.det from rfl]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have e2 : ∀ x x1 : Nat.Partition M,
      β⁻¹ * (g.det⁻¹ * g.adjugate x x1)
          * (torusForm c h d ℓ p p * torus c (h + (ℓ : K)) d M x x1)
        = (β⁻¹ * g.det⁻¹ * torusForm c h d ℓ p p)
          * (g.adjugate x x1 * torus c (h + (ℓ : K)) d M x x1) := fun x x1 => by ring
  simp only [e2, ← Finset.mul_sum]
  field_simp

end Virasoro
