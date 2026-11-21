import Virasoro.Proofs.TopLayerInv
import Virasoro.Proofs.ResidueCore4
import Virasoro.Proofs.EvalLemmas
import Virasoro.Statements.Sec5c

/-!
# Theorem 5.9 of `paper.tex` at 70bac53: the trace of a block against the torus matrix

Paper.tex l.874–888.  For a singular vector `χ` of level `ℓ` with coordinates `p`,
`∑_{Y,Y'} (γ⁻¹ U G_M(c,h+ℓ)⁻¹ Uᵀ)_{Y,Y'} ρ_{ℓ+M}(c,h,d)_{Y,Y'} = τ(d)/γ · F_M(c,h+ℓ,d)` by
Lemma 5.6, as polynomials in `d`; multiplying by the Euler coefficients and summing gives
`τ(d)/γ · H_{N-ℓ}(c,h+ℓ,d)`.
-/

namespace Virasoro

open scoped LaurentSeries
open Verma Module Polynomial

variable (c h : ℂ)

/-- `τ(d)/γ · F_{N'-ℓ}(c,h+ℓ,d)` as a polynomial in `d`; `0` when `ℓ > N'`. -/
noncomputable def blockPoly (k ℓ : ℕ) (x : Nat.Partition ℓ → ℂ) (N' : ℕ) : ℂ[X] :=
  if ℓ ≤ N' then
    C (jform c h ℓ k x x)⁻¹ * torusPolyForm c h x * FpolyD c (h + ℓ) (N' - ℓ)
  else 0

theorem eval_torus_poly (Δ d : ℂ) (M : ℕ) (Y Y' : Nat.Partition M) :
    (torus (C c) (C Δ) (X : ℂ[X]) M Y Y').eval d = torus c Δ d M Y Y' := by
  have := torus_map (Polynomial.evalRingHom d) (C c) (C Δ) (X : ℂ[X]) M
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  rw [this]
  rfl

theorem jv_pbwCoord (k ℓ : ℕ) (p : Nat.Partition ℓ → ℂ) :
    jv c h k ℓ (pbwCoord ℓ p) (pbwCoord ℓ p) = jform c h ℓ k p p := by
  unfold jv
  rw [comp_pbwCoord_same]

/-- The trace of the block of `χ` against `ρ_{N'}(c,h,d)`. -/
theorem topBlock_trace (k : ℕ) {ℓ : ℕ} (p : Nat.Partition ℓ → ℂ)
    (hχ : IsSingular (pbwCoord (c := c) (h := h) ℓ p) ℓ) (N' : ℕ) :
    ∑ Y, ∑ Y', C (topBlock k ℓ (pbwCoord (c := c) (h := h) ℓ p) N' (N' - ℓ) Y Y') *
        torus (C c) (C h) (X : ℂ[X]) N' Y Y' = blockPoly c h k ℓ p N' := by
  classical
  unfold blockPoly
  by_cases hle : ℓ ≤ N'
  · rw [if_pos hle]
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hle
    generalize hM' : ℓ + M - ℓ = M'
    obtain rfl : M = M' := by omega
    refine Polynomial.funext fun d => ?_
    have hτ : (torusPolyForm c h p).eval d = torusForm c h d ℓ p p := by
      simp only [torusPolyForm, torusForm, dotProduct, Matrix.mulVec, eval_finsetSum, eval_mul,
        eval_C, eval_torus_poly]
    have hF : (FpolyD c (h + (ℓ : ℂ)) M).eval d =
        ∑ Z, ∑ Z', (gram c (h + (ℓ : ℂ)) M)⁻¹ Z Z' * torus c (h + (ℓ : ℂ)) d M Z Z' := by
      simp only [FpolyD, eval_finsetSum, eval_mul, eval_C, eval_torus_poly]
    have hU : Umat (pbwCoord (c := c) (h := h) ℓ p) (ℓ + M) M = iotaMat c h ℓ M p := rfl
    simp only [eval_finsetSum, eval_mul, eval_C, eval_torus_poly, hτ, hF]
    rw [topBlock, hU, jv_pbwCoord]
    have e0 : ∀ Y Y' : Nat.Partition (ℓ + M),
        ((jform c h ℓ k p p)⁻¹ • (iotaMat c h ℓ M p * (gram c (h + (ℓ : ℂ)) M)⁻¹ *
          (iotaMat c h ℓ M p).transpose)) Y Y' * torus c h d (ℓ + M) Y Y' =
        (jform c h ℓ k p p)⁻¹ * ((iotaMat c h ℓ M p * (gram c (h + (ℓ : ℂ)) M)⁻¹ *
          (iotaMat c h ℓ M p).transpose) Y Y' * torus c h d (ℓ + M) Y Y') := fun Y Y' => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
    simp only [e0, ← Finset.mul_sum]
    rw [sum_mul_eq_trace, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : (iotaMat c h ℓ M p).transpose *
        ((torus c h d (ℓ + M)).transpose * iotaMat c h ℓ M p)
        = ((iotaMat c h ℓ M p).transpose * torus c h d (ℓ + M) * iotaMat c h ℓ M p).transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [e1, iota_torus_matrix c h ℓ M p d hχ, ← sum_mul_eq_trace]
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
    ring
  · rw [if_neg hle]
    have hU : Umat (pbwCoord (c := c) (h := h) ℓ p) N' (N' - ℓ) = 0 := by
      ext Y Z
      have hl := negOp_smul_mem_level (c := c) (h := h) (ℓ := ℓ) (v := pbwCoord ℓ p) ⟨p, rfl⟩
        Z.word
      rw [word_sum'] at hl
      simp only [Umat, Matrix.of_apply, Matrix.zero_apply]
      rw [comp_of_mem_level_ne (by omega) hl]
      rfl
    simp [topBlock, hU]

/-- `F_M(c,μ,d)` over `ℂ(d)` at a complex point `μ` is the image of the polynomial `FpolyD`. -/
theorem Fval_Kd (μ : ℂ) (M : ℕ) :
    Fval (RatFunc.C c : Kd) dvar (pt μ) M = algebraMap ℂ[X] Kd (FpolyD c μ M) := by
  classical
  have hg : gram (RatFunc.C c : Kd) (pt μ) M = (gram c μ M).map (RatFunc.C : ℂ →+* Kd) :=
    gram_map (RatFunc.C : ℂ →+* Kd) c μ M
  have ht : torus (RatFunc.C c : Kd) (pt μ) dvar M =
      (torus (C c) (C μ) (X : ℂ[X]) M).map (algebraMap ℂ[X] Kd) := by
    have := torus_map (algebraMap ℂ[X] Kd) (C c) (C μ) (X : ℂ[X]) M
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X] at this
    exact this
  have hadj : ((gram c μ M).map (RatFunc.C : ℂ →+* Kd)).adjugate =
      ((gram c μ M).adjugate).map (RatFunc.C : ℂ →+* Kd) :=
    (RingHom.map_adjugate (RatFunc.C : ℂ →+* Kd) (gram c μ M)).symm
  have hdet : ((gram c μ M).map (RatFunc.C : ℂ →+* Kd)).det =
      (RatFunc.C : ℂ →+* Kd) (gram c μ M).det :=
    (RingHom.map_det (RatFunc.C : ℂ →+* Kd) (gram c μ M)).symm
  unfold Fval FpolyD
  rw [hg, ht, hadj, hdet, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_mul, RatFunc.algebraMap_C, Matrix.map_apply, Matrix.map_apply, Matrix.inv_def,
    Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, div_eq_inv_mul]
  ring

/-- `[(Δ-a)^{-k}] H_N = ∑_j η_j [(Δ-a)^{-k}] F_{N-j}`. -/
theorem ppCoeff_HN_eq (a : Kd) (N k : ℕ) :
    ppCoeff (HN c N) a k =
      ∑ j ∈ Finset.range (N + 1), ((eta j : ℤ) : Kd) * ppCoeff (FN c (N - j)) a k := by
  unfold ppCoeff lcoeff
  rw [expandAt_eq, HN, Hrat, map_sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_intCast, ← map_intCast (HahnSeries.C : Kd →+* Kd⸨X⸩), mul_comm, coeff_mul_C,
    mul_comm]
  rfl

/-- Summing the blocks with the Euler coefficients gives the summand of equation (5.1). -/
theorem block_sum (k ℓ : ℕ) (x : Nat.Partition ℓ → ℂ) (N : ℕ)
    (hdet : ℓ ≤ N → ∀ M : ℕ, M ≤ N - ℓ → (gram c (h + (ℓ : ℂ)) M).det ≠ 0) :
    ∑ j ∈ Finset.range (N + 1),
        ((eta j : ℤ) : Kd) * algebraMap ℂ[X] Kd (blockPoly c h k ℓ x (N - j)) =
      topTerm c h N ℓ k x := by
  classical
  unfold topTerm
  by_cases hle : ℓ ≤ N
  · rw [if_pos hle]
    have hdetK : ∀ M ≤ N - ℓ, (gram (RatFunc.C c : Kd) (pt (h + (ℓ : ℂ))) M).det ≠ 0 := by
      intro M hM
      have hg : gram (RatFunc.C c : Kd) (pt (h + (ℓ : ℂ))) M =
          (gram c (h + (ℓ : ℂ)) M).map (RatFunc.C : ℂ →+* Kd) :=
        gram_map (RatFunc.C : ℂ →+* Kd) c (h + (ℓ : ℂ)) M
      have hd : ((gram c (h + (ℓ : ℂ)) M).map (RatFunc.C : ℂ →+* Kd)).det =
          (RatFunc.C : ℂ →+* Kd) (gram c (h + (ℓ : ℂ)) M).det :=
        (RingHom.map_det (RatFunc.C : ℂ →+* Kd) (gram c (h + (ℓ : ℂ)) M)).symm
      rw [hg, hd]
      exact (map_ne_zero (RatFunc.C : ℂ →+* Kd)).2 (hdet hle M hM)
    have hev : RatFunc.eval (RingHom.id Kd) (pt (h + (ℓ : ℂ))) (HN c (N - ℓ)) =
        Hval (RatFunc.C c : Kd) dvar (pt (h + (ℓ : ℂ))) (N - ℓ) :=
      evalAt_Hrat hdetK
    rw [hev, Hval, ← Finset.sum_subset (Finset.range_subset_range.2 (by omega : N - ℓ + 1 ≤ N + 1))
      (fun j hj0 hj => by
        rw [Finset.mem_range] at hj hj0
        rw [blockPoly, if_neg (by omega), map_zero, mul_zero]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [blockPoly, if_pos (by omega), Fval_Kd, map_mul, map_mul, RatFunc.algebraMap_C,
      show N - j - ℓ = N - ℓ - j by omega]
    ring
  · rw [if_neg hle]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [blockPoly, if_neg (by omega), map_zero, mul_zero]

end Virasoro
