import Virasoro.Proofs.Sec6H13Spec

/-!
# Proposition 6.8(i): `P_M^{(ν)}` at a point of a field of characteristic zero

The identity `P · ∏ det G̃ = M! ∏(2Y − 2t²h_{u,1}) · numerator` in `ℚ[t][Y]` (`key_PS`), evaluated
at `t = t₀`, `Y = t₀² μ` in a field `K` of characteristic zero, with `G̃ = t^{ℓ(λ)+ℓ(μ)} G`:
`P(t₀, t₀²μ) ∏_j det G_{M-j} = M! ∏_u t₀²(2μ − 2h_{u,1}) ∑_j η_j (∑ adj(G_{M-j}) ρ_{M-j})
∏_{i ≠ j} det G_{M-i}`.  It is used at `K = ℚ(q₀, t, α)` in the proof of the integrality
(paper.tex l.1261–1291).
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The specialization `t ↦ t₀`, `Y ↦ y₀`, `ℚ[t][Y] → K`. -/
noncomputable def sigK (t₀ y₀ : K) : PS →+* K :=
  eval₂RingHom (eval₂RingHom (algebraMap ℚ K) t₀) y₀

theorem sigK_tS (t₀ y₀ : K) : sigK t₀ y₀ tS = t₀ := by simp [sigK, tS]

theorem sigK_X (t₀ y₀ : K) : sigK t₀ y₀ X = y₀ := by simp [sigK]

theorem sigK_C (t₀ y₀ : K) (p : ℚ[X]) :
    sigK t₀ y₀ (C p) = eval₂RingHom (algebraMap ℚ K) t₀ p := by simp [sigK]

/-- `d_ν` at `t = t₀`. -/
noncomputable def dvalK (ν : Fin 2) (t₀ : K) : K := if ν = 0 then -1 - 2 / t₀ else 2 - 2 / t₀

theorem sigK_cS {t₀ : K} (ht : t₀ ≠ 0) (y₀ : K) : sigK t₀ y₀ cS = t₀ * cT t₀ := by
  rw [cS, sigK_C]
  simp only [map_add, map_mul, map_pow, map_ofNat, coe_eval₂RingHom, eval₂_X, cT]
  field_simp
  ring

theorem sigK_dS {t₀ : K} (ht : t₀ ≠ 0) (y₀ : K) (ν : Fin 2) :
    sigK t₀ y₀ (dS ν) = t₀ * dvalK ν t₀ := by
  rw [dS, sigK_C, dvalK]
  split_ifs
  · simp only [map_sub, map_neg, map_ofNat, coe_eval₂RingHom, eval₂_X]
    field_simp
    ring
  · simp only [map_add, map_mul, map_neg, map_ofNat, coe_eval₂RingHom, eval₂_X]
    field_simp
    ring

/-- `∏_{λ ⊢ n} t₀^{ℓ(λ)}`. -/
noncomputable def tauK (t₀ : K) (n : ℕ) : K := ∏ Y : Nat.Partition n, t₀ ^ Y.word.length

omit [CharZero K] in
theorem tauK_ne_zero {t₀ : K} (ht : t₀ ≠ 0) (n : ℕ) : tauK t₀ n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ ht

theorem GsM_sigK {t₀ : K} (ht : t₀ ≠ 0) (μ : K) (n : ℕ) :
    (GsM n).map (sigK t₀ (t₀ ^ 2 * μ)) =
      Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) * gram (cT t₀) μ n *
        Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) := by
  ext Y Y'
  rw [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [GsM, Matrix.of_apply]
  rw [← gramT_map, sigK_tS, sigK_cS ht, sigK_X, gramT_eq _ _ _ _ _ (word_pos Y)]
  simp only [gram, Matrix.of_apply]
  ring

theorem RsM_sigK {t₀ : K} (ht : t₀ ≠ 0) (μ : K) (ν : Fin 2) (n : ℕ) :
    (RsM ν n).map (sigK t₀ (t₀ ^ 2 * μ)) =
      Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) *
        torus (cT t₀) μ (dvalK ν t₀) n *
        Matrix.diagonal (fun Y : Nat.Partition n => t₀ ^ Y.word.length) := by
  ext Y Y'
  rw [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [RsM, Matrix.of_apply]
  rw [← torusWordT_map, sigK_tS, sigK_cS ht, sigK_X, sigK_dS ht,
    torusWordT_eq _ _ _ _ _ _ (word_pos Y)]
  simp only [torus, Matrix.of_apply]
  ring

theorem sigK_det {t₀ : K} (ht : t₀ ≠ 0) (μ : K) (n : ℕ) :
    sigK t₀ (t₀ ^ 2 * μ) (GsM n).det = tauK t₀ n ^ 2 * (gram (cT t₀) μ n).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, GsM_sigK ht, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, tauK]
  ring

/-- `∑ adj(G_n) ρ_n` at the point. -/
noncomputable def AK (ν : Fin 2) (t₀ μ : K) (n : ℕ) : K :=
  ∑ Y, ∑ Y', (gram (cT t₀) μ n).adjugate Y Y' * torus (cT t₀) μ (dvalK ν t₀) n Y Y'

theorem sigK_numS {t₀ : K} (ht : t₀ ≠ 0) (μ : K) (ν : Fin 2) (n : ℕ) :
    sigK t₀ (t₀ ^ 2 * μ) (numS ν n) = tauK t₀ n ^ 2 * AK ν t₀ μ n := by
  have h1 : sigK t₀ (t₀ ^ 2 * μ) (numS ν n) =
      ∑ Y, ∑ Y', ((GsM n).map (sigK t₀ (t₀ ^ 2 * μ))).adjugate Y Y' *
        (RsM ν n).map (sigK t₀ (t₀ ^ 2 * μ)) Y Y' := by
    rw [numS, map_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    rfl
  rw [h1, GsM_sigK ht, RsM_sigK ht, adj_scale, ← tauK, AK]

theorem sigK_prefS (t₀ μ : K) (ht : t₀ ≠ 0) (M : ℕ) :
    sigK t₀ (t₀ ^ 2 * μ) (prefS M) =
      (M.factorial : K) * ∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀)) := by
  rw [prefS, map_mul, map_natCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [map_sub, map_mul, map_ofNat, sigK_X, sigK_C, polH]
  simp only [map_mul, map_sub, map_add, map_pow, map_one, coe_eval₂RingHom, eval₂_X, eval₂_C,
    map_div₀, map_ofNat, map_natCast, hT]
  push_cast
  field_simp
  ring

/-- `P_M^{(ν)}(t₀, t₀²μ) ∏_j det G_{M-j}` (paper.tex l.1249–1257, at a point). -/
theorem specK {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) {t₀ : K} (ht : t₀ ≠ 0)
    (μ : K) :
    sigK t₀ (t₀ ^ 2 * μ) Q * ∏ j ∈ Finset.range (M + 1), (gram (cT t₀) μ (M - j)).det =
      ((M.factorial : K) * ∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀))) *
        ∑ j ∈ Finset.range (M + 1), (eta j : K) * AK ν t₀ μ (M - j) *
          ∏ i ∈ (Finset.range (M + 1)).erase j, (gram (cT t₀) μ (M - i)).det := by
  have k := congrArg (sigK t₀ (t₀ ^ 2 * μ)) (key_PS h)
  rw [map_mul, map_mul, sigK_prefS t₀ μ ht] at k
  set T : K := ∏ j ∈ Finset.range (M + 1), tauK t₀ (M - j) ^ 2 with hT
  have hT0 : T ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (tauK_ne_zero ht _)
  have hB : sigK t₀ (t₀ ^ 2 * μ) (Bden M) =
      T * ∏ j ∈ Finset.range (M + 1), (gram (cT t₀) μ (M - j)).det := by
    rw [Bden, map_prod, hT, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => sigK_det ht μ _
  have hA : sigK t₀ (t₀ ^ 2 * μ) (Anum ν M) =
      T * ∑ j ∈ Finset.range (M + 1), (eta j : K) * AK ν t₀ μ (M - j) *
          ∏ i ∈ (Finset.range (M + 1)).erase j, (gram (cT t₀) μ (M - i)).det := by
    rw [Anum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_mul, map_mul, map_intCast, map_prod, sigK_numS ht,
      Finset.prod_congr rfl fun i _ => sigK_det ht μ (M - i), Finset.prod_mul_distrib, hT,
      ← Finset.mul_prod_erase _ (fun i => tauK t₀ (M - i) ^ 2) hj]
    ring
  rw [hB, hA] at k
  apply mul_left_cancel₀ hT0
  linear_combination k

end Virasoro
