import Virasoro.Proofs.Sec6H13Final
import Virasoro.Proofs.Sec6DDeriv

/-!
# Proposition 6.8(iii) of `paper.tex` at 70bac53: specialization (l.1380–1384)

"Specialize to `t⋆ = -p'/p` and `Δ = μ`": at a rational `t₀ ≠ 0` and a weight `μ` at which no
Shapovalov determinant of level at most `M` vanishes,
`P_M^{(ν)}(t₀, t₀²μ) = M! ∏_{u=1}^M t₀² (2μ - 2h_{u,1}) · H_M(c, μ, d_ν)`.
-/

namespace Virasoro

open Polynomial

/-- The specialization `t ↦ t₀`, `Y ↦ y₀`, `ℚ[t][Y] → ℚ`. -/
noncomputable def sig (t₀ y₀ : ℚ) : PS →+* ℚ := eval₂RingHom (evalRingHom t₀) y₀

theorem sig_tS (t₀ y₀ : ℚ) : sig t₀ y₀ tS = t₀ := by simp [sig, tS]

theorem sig_X (t₀ y₀ : ℚ) : sig t₀ y₀ X = y₀ := by simp [sig]

theorem sig_C (t₀ y₀ : ℚ) (p : ℚ[X]) : sig t₀ y₀ (C p) = p.eval t₀ := by simp [sig]

/-- `d_ν` at `t = t₀`. -/
noncomputable def dval (ν : Fin 2) (t₀ : ℚ) : ℚ := if ν = 0 then -1 - 2 / t₀ else 2 - 2 / t₀

theorem sig_cS {t₀ : ℚ} (ht : t₀ ≠ 0) (y₀ : ℚ) : sig t₀ y₀ cS = t₀ * cT t₀ := by
  rw [cS, sig_C]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, cT]
  field_simp
  ring

theorem sig_dS {t₀ : ℚ} (ht : t₀ ≠ 0) (y₀ : ℚ) (ν : Fin 2) :
    sig t₀ y₀ (dS ν) = t₀ * dval ν t₀ := by
  rw [dS, sig_C, dval]
  split_ifs
  · simp only [eval_sub, eval_neg, eval_X, eval_ofNat]
    field_simp
    ring
  · simp only [eval_add, eval_mul, eval_neg, eval_X, eval_ofNat]
    field_simp
    ring

/-- `∏_{λ ⊢ n} t₀^{ℓ(λ)}`. -/
noncomputable def tauQ (t₀ : ℚ) (n : ℕ) : ℚ := ∏ Y : Nat.Partition n, t₀ ^ Y.word.length

theorem tauQ_ne_zero {t₀ : ℚ} (ht : t₀ ≠ 0) (n : ℕ) : tauQ t₀ n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ ht

theorem GsM_sig {t₀ : ℚ} (ht : t₀ ≠ 0) (μ : ℚ) (n : ℕ) :
    (GsM n).map (sig t₀ (t₀ ^ 2 * μ)) =
      Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) * gram (cT t₀) μ n *
        Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) := by
  ext Y Y'
  rw [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [GsM, Matrix.of_apply]
  rw [← gramT_map, sig_tS, sig_cS ht, sig_X, gramT_eq _ _ _ _ _ (word_pos Y)]
  simp only [gram, Matrix.of_apply]
  ring

theorem RsM_sig {t₀ : ℚ} (ht : t₀ ≠ 0) (μ : ℚ) (ν : Fin 2) (n : ℕ) :
    (RsM ν n).map (sig t₀ (t₀ ^ 2 * μ)) =
      Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) *
        torus (cT t₀) μ (dval ν t₀) n *
        Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) := by
  ext Y Y'
  rw [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [RsM, Matrix.of_apply]
  rw [← torusWordT_map, sig_tS, sig_cS ht, sig_X, sig_dS ht,
    torusWordT_eq _ _ _ _ _ _ (word_pos Y)]
  simp only [torus, Matrix.of_apply]
  ring

theorem sig_det {t₀ : ℚ} (ht : t₀ ≠ 0) (μ : ℚ) (n : ℕ) :
    sig t₀ (t₀ ^ 2 * μ) (GsM n).det = tauQ t₀ n ^ 2 * (gram (cT t₀) μ n).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, GsM_sig ht, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, tauQ]
  ring

theorem sig_numS {t₀ : ℚ} (ht : t₀ ≠ 0) (μ : ℚ) (ν : Fin 2) (n : ℕ)
    (hdet : (gram (cT t₀) μ n).det ≠ 0) :
    sig t₀ (t₀ ^ 2 * μ) (numS ν n) =
      sig t₀ (t₀ ^ 2 * μ) (GsM n).det * Fval (cT t₀) (dval ν t₀) μ n := by
  have h1 : sig t₀ (t₀ ^ 2 * μ) (numS ν n) =
      ∑ Y, ∑ Y', ((GsM n).map (sig t₀ (t₀ ^ 2 * μ))).adjugate Y Y' *
        (RsM ν n).map (sig t₀ (t₀ ^ 2 * μ)) Y Y' := by
    rw [numS, map_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    rfl
  rw [h1, GsM_sig ht, RsM_sig ht, adj_scale, sig_det ht, Fval, ← tauQ, mul_assoc]
  congr 1
  rw [mul_comm]
  exact (div_mul_cancel₀ _ hdet).symm

/-- `M! ∏ (2Y - 2t²h_{u,1})` at `t = t₀`, `Y = t₀²μ`. -/
theorem sig_prefS (t₀ μ : ℚ) (ht : t₀ ≠ 0) (M : ℕ) :
    sig t₀ (t₀ ^ 2 * μ) (prefS M) =
      (M.factorial : ℚ) * ∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀)) := by
  rw [prefS, map_mul, map_natCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [map_sub, map_mul, map_ofNat, sig_X, sig_C, polH]
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C, eval_one, hT]
  push_cast
  field_simp
  ring

/-- The specialization of `P_M^{(ν)}` (paper.tex l.1380–1384). -/
theorem spec_formula {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) {t₀ μ : ℚ}
    (ht : t₀ ≠ 0) (hdet : ∀ n ≤ M, (gram (cT t₀) μ n).det ≠ 0) :
    sig t₀ (t₀ ^ 2 * μ) Q =
      (M.factorial : ℚ) * (∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀))) *
        Hval (cT t₀) (dval ν t₀) μ M := by
  have k := congrArg (sig t₀ (t₀ ^ 2 * μ)) (key_PS h)
  rw [map_mul, map_mul, sig_prefS t₀ μ ht] at k
  have hB : sig t₀ (t₀ ^ 2 * μ) (Bden M) ≠ 0 := by
    rw [Bden, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [sig_det ht]
    exact mul_ne_zero (pow_ne_zero _ (tauQ_ne_zero ht _)) (hdet _ (Nat.sub_le M j))
  have hA : sig t₀ (t₀ ^ 2 * μ) (Anum ν M) =
      Hval (cT t₀) (dval ν t₀) μ M * sig t₀ (t₀ ^ 2 * μ) (Bden M) := by
    rw [Anum, Hval, Bden, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_mul, map_mul, map_intCast, map_prod, sig_numS ht μ ν _ (hdet _ (Nat.sub_le M j)),
      ← Finset.mul_prod_erase _ (fun i => sig t₀ (t₀ ^ 2 * μ) (GsM (M - i)).det) hj]
    ring
  apply mul_right_cancel₀ hB
  rw [k, hA]
  ring

/-- `P(t₀, y₀)` for `P ∈ ℚ[t,Y]` and its image in `ℚ[t][Y]`. -/
theorem sig_thetaInv (t₀ y₀ : ℚ) (P : MvPolynomial (Fin 2) ℚ) :
    sig t₀ y₀ (thetaInv P) = MvPolynomial.eval (![t₀, y₀] : Fin 2 → ℚ) P := by
  have h : (sig t₀ y₀).comp thetaInv = MvPolynomial.eval (![t₀, y₀] : Fin 2 → ℚ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · exact RingHom.congr_fun (RingHom.ext_rat (((sig t₀ y₀).comp thetaInv).comp MvPolynomial.C)
        ((MvPolynomial.eval (![t₀, y₀] : Fin 2 → ℚ)).comp MvPolynomial.C)) r
    · fin_cases i <;> simp [thetaInv, sig, tS]
  exact RingHom.congr_fun h P

end Virasoro
