import Virasoro.Sphere.Proofs.Sec3LamKernel
import Virasoro.Sphere.Saddle
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.Naturality
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The Ward solution over `ℂ(λ)` (sphere paper Lemma 3.3(i))

sphere/paper.tex l.513–514 with Lemma 3.2(ii): the coefficients of the Ward solution `F_N` are
rational functions of `λ`.  By Lemma 3.2 the solution at real `λ > 0` is
`F_N = ∑_Y (G_N⁻¹ γ)_Y l_{-Y}1`, with `G_N` the Gram matrix at `Δ = λ² + μ²`; the same formula
with `λ` an indeterminate (Cramer's rule, denominator `det G_N(λ² + μ²)`) defines `F_N` over
`ℂ(λ)`.  The Ward equations over `ℂ[λ]`, cleared of denominators, hold at every real `λ > 0`,
hence identically.
-/

namespace Virasoro.Sphere

open MvPolynomial

theorem gammaY_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Δ Δa Δb : R)
    (w : List ℕ) : gammaY (f Δ) (f Δa) (f Δb) w = f (gammaY Δ Δa Δb w) := by
  induction w with
  | nil => simp [gammaY]
  | cons y w ih => simp only [gammaY, ih, map_mul, map_add, map_sub, map_natCast]

/-- A polynomial vanishing at every real `λ > 0` is zero. -/
theorem poly_eq_zero_of_pos (p : Polynomial ℂ) (h : ∀ a : ℝ, 0 < a → p.eval (a : ℂ) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p
    (((Set.Ioi_infinite (0 : ℝ)).image Complex.ofReal_injective.injOn).mono ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

/-- Evaluation at `λ = a`. -/
noncomputable abbrev evA (a : ℝ) : Polynomial ℂ →ₐ[ℂ] ℂ := Polynomial.aeval (a : ℂ)

theorem mv_eq_zero_of_pos (Q : MvPolynomial ℕ+ (Polynomial ℂ))
    (h : ∀ a : ℝ, 0 < a → map (evA a : Polynomial ℂ →+* ℂ) Q = 0) : Q = 0 := by
  refine MvPolynomial.ext _ _ fun γ => ?_
  rw [coeff_zero]
  refine poly_eq_zero_of_pos _ fun a ha => ?_
  have h1 := congrArg (coeff γ) (h a ha)
  rw [coeff_map, coeff_zero] at h1
  simpa using h1

theorem coeff_specialize (lam : ℂ) (f : MvPolynomial ℕ+ (RatFunc ℂ)) (γ : ℕ+ →₀ ℕ) :
    coeff γ (specialize lam f) = RatFunc.eval (RingHom.id ℂ) lam (coeff γ f) := by
  classical
  rw [specialize, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hγ
  · rfl
  · rw [notMem_support_iff.mp hγ]
    simp [RatFunc.eval]

section Construction

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) (μ : ℝ) (hμ : 0 < μ)
  (Δa Δb : ℂ)

/-- The Gram matrix at `c = 1 + 24μ²`, `Δ = λ² + μ²` over `ℂ[λ]`. -/
noncomputable def gramX (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) (Polynomial ℂ) :=
  gram (Polynomial.C (1 + 24 * (μ : ℂ) ^ 2)) (Polynomial.X ^ 2 + Polynomial.C ((μ : ℂ) ^ 2)) N

/-- `det G_N(λ² + μ²)`. -/
noncomputable def detX (N : ℕ) : Polynomial ℂ := (gramX μ N).det

/-- `γ_Y(λ² + μ²; Δ_a, Δ_b)`. -/
noncomputable def gamX (N : ℕ) (Y : Nat.Partition N) : Polynomial ℂ :=
  gammaY (Polynomial.X ^ 2 + Polynomial.C ((μ : ℂ) ^ 2)) (Polynomial.C Δa) (Polynomial.C Δb)
    Y.word

/-- `det G_N · F_N = ∑_Y (adj(G_N) γ)_Y l_{-Y}1` over `ℂ[λ]`. -/
noncomputable def wardNum (N : ℕ) : MvPolynomial ℕ+ (Polynomial ℂ) :=
  ∑ Y : Nat.Partition N, ((gramX μ N).adjugate.mulVec (gamX μ Δa Δb N)) Y •
    fockWordR (Polynomial.C (μ : ℂ)) (Polynomial.X : Polynomial ℂ) Y.word

theorem gramX_map (a : ℝ) (N : ℕ) :
    (gramX μ N).map (evA a : Polynomial ℂ →+* ℂ) =
      gram (1 + 24 * (μ : ℂ) ^ 2) ((a : ℂ) ^ 2 + (μ : ℂ) ^ 2) N := by
  rw [gramX, ← gram_map]
  simp

theorem gamX_map (a : ℝ) (N : ℕ) (Y : Nat.Partition N) :
    (evA a : Polynomial ℂ →+* ℂ) (gamX μ Δa Δb N Y) =
      gammaY ((a : ℂ) ^ 2 + (μ : ℂ) ^ 2) Δa Δb Y.word := by
  rw [gamX, ← gammaY_map]
  simp

theorem detX_eval (a : ℝ) (N : ℕ) :
    (detX μ N).eval (a : ℂ) =
      (gram (1 + 24 * (μ : ℂ) ^ 2) ((a : ℂ) ^ 2 + (μ : ℂ) ^ 2) N).det := by
  rw [← gramX_map, detX]
  have h := RingHom.map_det (evA a : Polynomial ℂ →+* ℂ) (gramX μ N)
  simpa using h

include hK hμ in
theorem detX_eval_ne_zero (a : ℝ) (ha : 0 < a) (N : ℕ) : (detX μ N).eval (a : ℂ) ≠ 0 := by
  rw [detX_eval]
  exact gram_det_ne_zero_fock hK μ a hμ ha N

include hF hK hμ

/-- For a vector `y` with `G_N y = d γ`, `∑_Y y_Y l_{-Y}1 = d F_N` (Lemma 3.2(ii)). -/
theorem sum_fw_eq (a : ℝ) (ha : 0 < a) (N : ℕ) (y : Nat.Partition N → ℂ) (d : ℂ)
    (hy : (gram (1 + 24 * (μ : ℂ) ^ 2) ((a : ℂ) ^ 2 + (μ : ℂ) ^ 2) N).mulVec y =
      fun Y => d * gammaY ((a : ℂ) ^ 2 + (μ : ℂ) ^ 2) Δa Δb Y.word) :
    ∑ Y, y Y • fockWord (μ : ℂ) (a : ℂ) Y.word = d • gammaVec hF hK μ a hμ ha Δa Δb N := by
  rw [← sub_eq_zero]
  refine level_orth hF hK μ a hμ ha N _
    (Submodule.sub_mem _ (Submodule.sum_mem _ fun Y _ =>
      Submodule.smul_mem _ _ (fw_mem_level μ a Y))
      (Submodule.smul_mem _ _ (gammaVec_mem hF hK μ a hμ ha Δa Δb N))) fun Z => ?_
  rw [fockForm_sub_right, fockForm_sum_right, fockForm_smul_right,
    gammaVec_pair hF hK μ a hμ ha Δa Δb N Z.word (Verma.posWord_word Z) (Verma.word_sum' Z)]
  simp only [fockForm_smul_right, fock_gram_iso hF μ a]
  have h1 := congrFun hy Z
  rw [Matrix.mulVec, dotProduct] at h1
  rw [← h1, sub_eq_zero]
  exact Finset.sum_congr rfl fun Y _ => mul_comm _ _

/-- The value of `det G_N · F_N` at real `λ = a > 0`. -/
theorem map_wardNum (a : ℝ) (ha : 0 < a) (N : ℕ) :
    map (evA a : Polynomial ℂ →+* ℂ) (wardNum μ Δa Δb N) =
      (detX μ N).eval (a : ℂ) • gammaVec hF hK μ a hμ ha Δa Δb N := by
  rw [wardNum, map_sum]
  simp_rw [map_smulR, map_fockWordR]
  have e : fockWordR ((evA a) (Polynomial.C (μ : ℂ))) ((evA a) (Polynomial.X : Polynomial ℂ)) =
      fockWord (μ : ℂ) (a : ℂ) := by
    funext w
    rw [fockWord_eq_fockWordR]
    simp
  rw [e]
  refine sum_fw_eq hF hK μ hμ Δa Δb a ha N _ _ ?_
  funext Z
  have h1 := RingHom.map_mulVec (evA a : Polynomial ℂ →+* ℂ) (gramX μ N)
    ((gramX μ N).adjugate.mulVec (gamX μ Δa Δb N)) Z
  rw [gramX_map] at h1
  have h2 : (fun Y => (evA a) (((gramX μ N).adjugate.mulVec (gamX μ Δa Δb N)) Y)) =
      (evA a : Polynomial ℂ →+* ℂ) ∘ ((gramX μ N).adjugate.mulVec (gamX μ Δa Δb N)) := rfl
  rw [h2, ← h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, gamX_map]
  rfl

/-- The Ward equations over `ℂ[λ]`, cleared of denominators. -/
theorem wardNum_ward (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    detX μ m • ffOpR (Polynomial.C (μ : ℂ)) (Polynomial.X : Polynomial ℂ) (k : ℤ)
        (wardNum μ Δa Δb (m + k)) =
      detX μ (m + k) • (ffOpR (Polynomial.C (μ : ℂ)) (Polynomial.X : Polynomial ℂ) 0
        (wardNum μ Δa Δb m) + C (Polynomial.C ((k : ℂ) * Δb - Δa)) * wardNum μ Δa Δb m) := by
  rw [← sub_eq_zero]
  refine mv_eq_zero_of_pos _ fun a ha => ?_
  rw [map_sub, map_smulR, map_smulR, map_ffOpR, map_add, map_ffOpR, map_mul, map_C,
    map_wardNum hF hK μ hμ Δa Δb a ha, map_wardNum hF hK μ hμ Δa Δb a ha]
  have e1 : (evA a) (Polynomial.C (μ : ℂ)) = (μ : ℂ) := by simp
  have e2 : (evA a) (Polynomial.X : Polynomial ℂ) = (a : ℂ) := by simp
  have e3 : (evA a : Polynomial ℂ →+* ℂ) (Polynomial.C ((k : ℂ) * Δb - Δa)) =
      (k : ℂ) * Δb - Δa := by simp
  have e4 : ∀ p : Polynomial ℂ, (evA a) p = p.eval (a : ℂ) := fun p => by simp
  rw [e1, e2, e3, e4, e4, ← ffOp_eq_ffOpR, ← ffOp_eq_ffOpR, map_smul, map_smul,
    gammaVec_ward hF hK μ a hμ ha Δa Δb k hk m, mul_smul_comm, ← smul_add, smul_comm, sub_self]

omit hF in
theorem detX_ne_zero (N : ℕ) : detX μ N ≠ 0 := fun h => by
  have h1 := detX_eval_ne_zero hK μ hμ 1 one_pos N
  rw [h] at h1
  simp at h1

theorem wardNum_zero : wardNum μ Δa Δb 0 = C (detX μ 0) := by
  rw [← sub_eq_zero]
  refine mv_eq_zero_of_pos _ fun a ha => ?_
  rw [map_sub, map_wardNum hF hK μ hμ Δa Δb a ha, gammaVec_zero, map_C, sub_eq_zero,
    smul_eq_C_mul, mul_one]
  simp

theorem wardNum_homog (N : ℕ) : IsWeightedHomogeneous fockWeight (wardNum μ Δa Δb N) N := by
  intro γ hγ
  by_contra hw
  refine hγ (poly_eq_zero_of_pos _ fun a ha => ?_)
  have h1 := congrArg (coeff γ) (map_wardNum hF hK μ hμ Δa Δb a ha N)
  rw [coeff_map, coeff_smul,
    (gammaVec_mem hF hK μ a hμ ha Δa Δb N).coeff_eq_zero γ hw, smul_zero] at h1
  simpa using h1

/-- The Ward solution over `ℂ(λ)`. -/
noncomputable def wardRat (N : ℕ) : MvPolynomial ℕ+ (RatFunc ℂ) :=
  C ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (detX μ N))⁻¹) *
    map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (wardNum μ Δa Δb N)

omit hF hK hμ in
theorem coeff_wardRat (N : ℕ) (γ : ℕ+ →₀ ℕ) :
    coeff γ (wardRat μ Δa Δb N) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (coeff γ (wardNum μ Δa Δb N)) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (detX μ N) := by
  rw [wardRat, coeff_C_mul, coeff_map, div_eq_mul_inv, mul_comm]

theorem wardRat_isWard :
    IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C Δa) (RatFunc.C Δb)
      (wardRat μ Δa Δb) := by
  have hd : ∀ N, algebraMap (Polynomial ℂ) (RatFunc ℂ) (detX μ N) ≠ 0 := fun N => by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
    exact detX_ne_zero hK μ hμ N
  refine ⟨?_, fun m => ?_, fun k hk m => ?_⟩
  · rw [wardRat, wardNum_zero hF hK μ hμ, map_C, ← C_mul, inv_mul_cancel₀ (hd 0), C_1]
  · intro γ hγ
    rw [coeff_wardRat] at hγ
    refine wardNum_homog hF hK μ hμ Δa Δb m fun h0 => hγ ?_
    rw [h0, map_zero, zero_div]
  · have e := congrArg (map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))
      (wardNum_ward hF hK μ hμ Δa Δb k hk m)
    have hmap := fun (r : Polynomial ℂ) (p : MvPolynomial ℕ+ (Polynomial ℂ)) =>
      map_smulR (IsScalarTower.toAlgHom ℂ (Polynomial ℂ) (RatFunc ℂ)) r p
    have hop := fun (j : ℤ) (p : MvPolynomial ℕ+ (Polynomial ℂ)) =>
      map_ffOpR (IsScalarTower.toAlgHom ℂ (Polynomial ℂ) (RatFunc ℂ)) (Polynomial.C (μ : ℂ))
        (Polynomial.X : Polynomial ℂ) j p
    simp only [IsScalarTower.coe_toAlgHom, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] at hmap hop
    rw [hmap, hmap, hop, map_add, hop, map_mul, map_C, RatFunc.algebraMap_C,
      ← ffOp_eq_ffOpR, ← ffOp_eq_ffOpR] at e
    have ec : RatFunc.C ((k : ℂ) * Δb - Δa) =
        ((k : RatFunc ℂ)) * RatFunc.C Δb - RatFunc.C Δa := by
      simp
    rw [ec] at e
    simp only [wardRat, C_mul', map_smul]
    rw [C_mul'] at e
    have e' : ffOp (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (k : ℤ)
        (map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (wardNum μ Δa Δb (m + k))) =
        ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (detX μ m))⁻¹ *
          algebraMap (Polynomial ℂ) (RatFunc ℂ) (detX μ (m + k))) •
        (ffOp (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) 0
          (map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (wardNum μ Δa Δb m)) +
          ((k : RatFunc ℂ) * RatFunc.C Δb - RatFunc.C Δa) •
            map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (wardNum μ Δa Δb m)) := by
      rw [mul_smul, ← e, smul_smul, inv_mul_cancel₀ (hd m), one_smul]
    rw [e', smul_comm ((k : RatFunc ℂ) * RatFunc.C Δb - RatFunc.C Δa), ← smul_add, smul_smul]
    congr 1
    have h1 := hd m
    have h2 := hd (m + k)
    field_simp

/-- At real `λ = a > 0` the solution over `ℂ(λ)` has no pole and its value is the `F` of
Lemma 3.2(ii). -/
theorem wardRat_specialize (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∀ γ : ℕ+ →₀ ℕ, RegAt (a : ℂ) (coeff γ (wardRat μ Δa Δb N))) ∧
      specialize (a : ℂ) (wardRat μ Δa Δb N) = gammaVec hF hK μ a hμ ha Δa Δb N := by
  have hq := detX_eval_ne_zero hK μ hμ a ha N
  refine ⟨fun γ => ?_, ?_⟩
  · rw [coeff_wardRat]
    exact regAt_div _ _ hq
  · ext γ
    rw [coeff_specialize, coeff_wardRat]
    have h1 := evalAt_div (a : ℂ) (coeff γ (wardNum μ Δa Δb N)) hq
    rw [evalAt] at h1
    rw [h1]
    have h2 := congrArg (coeff γ) (map_wardNum hF hK μ hμ Δa Δb a ha N)
    rw [coeff_map, coeff_smul, smul_eq_mul] at h2
    have h3 : (evA a : Polynomial ℂ →+* ℂ) (coeff γ (wardNum μ Δa Δb N)) =
        (coeff γ (wardNum μ Δa Δb N)).eval (a : ℂ) := by simp
    rw [← h3, h2, mul_div_cancel_left₀ _ hq]

end Construction

end Virasoro.Sphere
