import Virasoro.Proofs.Family
import Virasoro.Proofs.JantzenLevel
import Virasoro.Proofs.Sec5Cross
import Virasoro.Proofs.SmithExist

/-!
# The kernel of the Shapovalov matrix at a singular weight and the residue of its inverse

Let `χ = P|h⟩` be singular of level `ℓ ≥ 1` in `M(c,h)`, and let `ι` be the matrix of
`u|h+ℓ⟩ ↦ u χ` from level `M` of `M(c,h+ℓ)` to level `ℓ + M` of `M(c,h)`.  The image of `ι` lies
in `ker G_{ℓ+M}(c,h)`, and the first crossing form on it is `β_χ G_M(c,h+ℓ)`.  If
`G_M(c,h+ℓ)` is invertible, `β_χ ≠ 0` and `ord_x det G_{ℓ+M}(c,h+x) = p(M)`, then `G_{ℓ+M}⁻¹`
has a simple pole at `h` with residue `ι (β_χ G_M(c,h+ℓ))⁻¹ ιᵀ`.
-/

namespace Virasoro

open Polynomial Module

variable {K : Type*} [Field K] [CharZero K] (c h : K) (ℓ M : ℕ) (p : Nat.Partition ℓ → K)

/-- The matrix `ι` of `u|h+ℓ⟩ ↦ u χ`, `χ = ∑ p_W L_{-W}|h⟩`, from level `M` to level `ℓ + M`. -/
noncomputable def iotaMat : Matrix (Nat.Partition (ℓ + M)) (Nat.Partition M) K :=
  Matrix.of fun Y Z =>
    Verma.comp (ℓ + M) (VirEnv.negOp c Z.word • Verma.pbwCoord (c := c) (h := h) ℓ p) Y

theorem pbwCoord_iotaMat_col (Z : Nat.Partition M) :
    Verma.pbwCoord (c := c) (h := h) (ℓ + M) (fun Y => iotaMat c h ℓ M p Y Z)
      = VirEnv.negOp c Z.word • Verma.pbwCoord (c := c) (h := h) ℓ p := by
  have hmem := Verma.negOp_smul_mem_level (c := c) (h := h) (ℓ := ℓ)
    (v := Verma.pbwCoord ℓ p) ⟨p, rfl⟩ Z.word
  rw [Verma.word_sum'] at hmem
  exact Verma.pbwCoord_comp_of_mem_level hmem

theorem gramLocal_isSymm (N : ℕ) : (gramLocal c h N).IsSymm := by
  refine Matrix.ext fun Y Y' => ?_
  rw [Matrix.transpose_apply]
  exact gramWord_symm (PowerSeries.C c) (PowerSeries.C h + PowerSeries.X)
    (Verma.posWord_word Y') (Verma.posWord_word Y)

section Singular

variable (hℓ : 1 ≤ ℓ) (hχ : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) ℓ p) ℓ)

include hℓ hχ

/-- The columns of `ι` lie in the kernel of `G_{ℓ+M}(c,h)`. -/
theorem gram_mulVec_iotaMat_col (Z : Nat.Partition M) :
    (gram c h (ℓ + M)).mulVec (fun Y => iotaMat c h ℓ M p Y Z) = 0 := by
  funext Y
  rw [← Verma.shap_neg_pbwCoord, pbwCoord_iotaMat_col, Verma.isShapovalov_shap.symm,
    Verma.shap_singular c h hχ hℓ Z.word]
  rfl

theorem iotaMat_col_mem_ker0 (Z : Nat.Partition M) :
    (fun Y => iotaMat c h ℓ M p Y Z) ∈ ker0 (gramLocal c h (ℓ + M)) := by
  rw [mem_ker0, coeffMat_zero_gramLocal]
  exact gram_mulVec_iotaMat_col c h ℓ M p hℓ hχ Z

omit hℓ hχ in
theorem dAt_gramForm (N : ℕ) (u v : Nat.Partition N → K) :
    dAt h (gramForm (C c) (X : K[X]) N (fun Y => C (u Y)) (fun Y => C (v Y)))
      = cross1 (gramLocal c h N) u v := by
  unfold dAt gramForm cross1
  simp only [dotProduct, Matrix.mulVec, derivative_sum, derivative_mul, derivative_C, zero_mul,
    zero_add, mul_zero, add_zero, eval_finsetSum, eval_mul, eval_C, coeffMat_one_gramLocal,
    Finset.mul_sum]
  rfl

/-- The first crossing form on the image of `ι` is `β_χ G_M(c,h+ℓ)`. -/
theorem cross1_iotaMat (Z Z' : Nat.Partition M) :
    cross1 (gramLocal c h (ℓ + M)) (fun Y => iotaMat c h ℓ M p Y Z)
        (fun Y => iotaMat c h ℓ M p Y Z')
      = crossScalar c h p * gram c (h + (ℓ : K)) M Z Z' := by
  set χX : Verma K[X] (C c) X := Verma.pbwCoord ℓ fun W => C (p W) with hχX
  set χ : Verma K c h := Verma.pbwCoord ℓ p with hχdef
  have hBX := Verma.isShapovalov_shap (c := C c) (h := (X : K[X]))
  have hevχ : evX c h χX = χ := by
    rw [hχX, evX_pbwCoord]
    simp only [eval_C]
    rfl
  have key : ∀ Z : Nat.Partition M, ∃ ψ : Verma K[X] (C c) X,
      Verma.pbwCoord (c := C c) (h := (X : K[X])) (ℓ + M) (fun Y => C (iotaMat c h ℓ M p Y Z))
        = VirEnv.negOp (C c) Z.word • χX + (X - C h) • ψ := by
    intro Z
    have h0 : evX c h (Verma.pbwCoord (c := C c) (h := (X : K[X])) (ℓ + M)
        (fun Y => C (iotaMat c h ℓ M p Y Z)) - VirEnv.negOp (C c) Z.word • χX) = 0 := by
      rw [map_sub, evX_pbwCoord, evX_negOp_smul, hevχ]
      simp only [eval_C]
      rw [pbwCoord_iotaMat_col, sub_self]
    obtain ⟨ψ, hψ⟩ := evX_eq_zero c h _ h0
    exact ⟨ψ, by rw [← hψ]; abel⟩
  have hrad : ∀ (W : List ℕ) (u : Verma K[X] (C c) X),
      (Verma.shap (C c) X (VirEnv.negOp (C c) W • χX) u).eval h = 0 := by
    intro W u
    rw [← shap_evX, evX_negOp_smul, hevχ]
    exact Verma.shap_singular c h hχ hℓ W _
  obtain ⟨ψ, hψ⟩ := key Z
  obtain ⟨ψ', hψ'⟩ := key Z'
  have h1 := crossing_words c h ℓ p hℓ hχ Z.word (Verma.posWord_word Z) Z'.word
    (Verma.posWord_word Z')
  have h2 : dAt h (Verma.shap (C c) (X : K[X]) χX χX) = crossScalar c h p := by
    rw [hχX, Verma.shap_pbwCoord]
    rfl
  rw [h2] at h1
  rw [← dAt_gramForm, ← Verma.shap_pbwCoord, hψ, hψ']
  have e : Verma.shap (C c) (X : K[X]) (VirEnv.negOp (C c) Z.word • χX + (X - C h) • ψ)
        (VirEnv.negOp (C c) Z'.word • χX + (X - C h) • ψ')
      = Verma.shap (C c) X (VirEnv.negOp (C c) Z.word • χX) (VirEnv.negOp (C c) Z'.word • χX)
        + (X - C h) * Verma.shap (C c) X (VirEnv.negOp (C c) Z.word • χX) ψ'
        + (X - C h) * Verma.shap (C c) X (VirEnv.negOp (C c) Z'.word • χX) ψ
        + (X - C h) * ((X - C h) * Verma.shap (C c) X ψ ψ') := by
    have e1 := (Verma.shap (C c) (X : K[X]) (VirEnv.negOp (C c) Z.word • χX)).map_smul
      (X - C h) ψ'
    have e2 := (Verma.shap (C c) (X : K[X]) ψ).map_smul (X - C h) ψ'
    have e3 := (Verma.shap (C c) (X : K[X])).map_smul (X - C h) ψ
    have e4 := hBX.symm ψ (VirEnv.negOp (C c) Z'.word • χX)
    have E1 := (Verma.shap (C c) (X : K[X]) (VirEnv.negOp (C c) Z.word • χX + (X - C h) • ψ)).map_add
      (VirEnv.negOp (C c) Z'.word • χX) ((X - C h) • ψ')
    have E2 := (Verma.shap (C c) (X : K[X])).map_add (VirEnv.negOp (C c) Z.word • χX)
      ((X - C h) • ψ)
    rw [E1, E2, e3, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, e1, e2, e4]
    simp only [smul_eq_mul]
    ring
  rw [e, dAt_add, dAt_add, dAt_add, dAt_X_sub_C_mul, dAt_X_sub_C_mul, dAt_X_sub_C_mul, hrad,
    hrad, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, add_zero, add_zero,
    h1]
  rfl

end Singular

end Virasoro
