import Virasoro.Proofs.P2Sec13Laurent
import Virasoro.Proofs.Sec6Norm
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.Crossing

/-!
# Lemma 13.1, Step 2: the descendants of `χ_{R,S}(b⋆+X)` lie in the kernels
(paper.tex l.2893–2897, 2906–2910)

The normalized singular vector has Laurent coefficients in `b` (Proposition 10.2(i), cited).
Its descendants are vectors of the Verma module over `Lam = ℂ[b,b⁻¹]`.  At every `b' ≠ 0` they
lie in the radical of the Shapovalov form, and at generic `b'` in the radical of `ρ` (Step 1), so
the corresponding identities hold over `Lam`, hence over `ℂ⟦X⟧` after `b ↦ b⋆ + X`.
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial

open scoped PowerSeries

/-- Evaluation of a polynomial in a regular rational function. -/
theorem evTo_aeval {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] {b : 𝔽} (f : ℚ[X]) {x : RatFunc ℚ} {v : 𝔽}
    (hx : EvTo b x v) : EvTo b (Polynomial.aeval x f) (f.eval₂ (algebraMap ℚ 𝔽) v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, eval₂_add]
    exact hp.add hq
  | monomial n a =>
    rw [aeval_monomial, eval₂_monomial]
    have e : algebraMap ℚ (RatFunc ℚ) a = RatFunc.C a :=
      RingHom.congr_fun (Subsingleton.elim _ _) a
    rw [e]
    exact (evTo_C a).mul (hx.pow n)

section Maps

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*} [Fintype ι]

theorem map_mulVec_apply (M : Matrix ι ι R) (d : ι → R) (Y : ι) :
    (M.map f).mulVec (fun Z => f (d Z)) Y = f (M.mulVec d Y) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem map_vecMul_apply (M : Matrix ι ι R) (d : ι → R) (Y : ι) :
    Matrix.vecMul (fun Z => f (d Z)) (M.map f) Y = f (Matrix.vecMul d M Y) := by
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply]

end Maps

section Forms

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem gram_mulVec_eq_gramForm (c h : R) (N : ℕ) (d : Nat.Partition N → R)
    (Y : Nat.Partition N) :
    (gram c h N).mulVec d Y = gramForm c h N d (Pi.single Y 1) := by
  classical
  have e : (gram c h N).mulVec (Pi.single Y 1) = fun Z => gram c h N Z Y := by
    funext Z
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [gramForm, e]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have ht := congrFun (congrFun (gram_transpose c h N) Y) Z
  rw [Matrix.transpose_apply] at ht
  rw [ht, mul_comm]

theorem torus_mulVec_eq_torusForm (c h d₀ : R) (N : ℕ) (d : Nat.Partition N → R)
    (Y : Nat.Partition N) :
    (torus c h d₀ N).mulVec d Y = torusForm c h d₀ N (Pi.single Y 1) d := by
  classical
  rw [torusForm]
  simp [dotProduct, Pi.single_apply]

theorem torus_vecMul_eq_torusForm (c h d₀ : R) (N : ℕ) (d : Nat.Partition N → R)
    (Y : Nat.Partition N) :
    Matrix.vecMul d (torus c h d₀ N) Y = torusForm c h d₀ N d (Pi.single Y 1) := by
  classical
  have e : (torus c h d₀ N).mulVec (Pi.single Y 1) = fun Z => torus c h d₀ N Z Y := by
    funext Z
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [torusForm, e]
  rfl

end Forms

/-- `U(Vir_-)χ` lies in the left radical of the Shapovalov form. -/
theorem shap_negSpan_left {c h : ℂ} {χ : Verma ℂ c h} {ℓ : ℕ} (hχ : IsSingular χ ℓ) (hℓ : 1 ≤ ℓ)
    {z : Verma ℂ c h} (hz : z ∈ negSpan χ) (u : Verma ℂ c h) : shap c h z u = 0 := by
  unfold negSpan at hz
  refine Submodule.span_induction (p := fun z _ => shap c h z u = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨w, rfl⟩
    exact shap_singular c h hχ hℓ _ u
  · rw [map_zero, LinearMap.zero_apply]
  · intro x y _ _ hx hy
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  · intro a x _ hx
    rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

set_option maxHeartbeats 1600000 in
/-- `Stmt_sub_tau_kernel_lift` (paper.tex l.2893–2897, 2906–2910). -/
theorem sub_tau_kernel_lift_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) : Stmt_sub_tau_kernel_lift := by
  classical
  intro b hb R S hR hS χ hχ N v hv
  have hRS : 1 ≤ R * S := Nat.mul_pos hR hS
  obtain ⟨p, ⟨hp1, hsing⟩, -, -, -, hspec⟩ := normalization_at hH R S hR hS
  choose f n hf using hLau R S hR hS p hp1 hsing
  have hLay := sub_generic_layers_of_cited hK hE hH hU hF
  -- the values of the family
  have hxs : ∀ (b' : ℂ) (hb' : b' ≠ 0), IsSingular (pbwCoord (c := kacC b') (h := kacH R S b')
      (R * S) fun Y => RatFunc.eval (algebraMap ℚ ℂ) b' (p Y)) (R * S) := fun b' hb' =>
    (hspec ℂ b' hb' fun Y => regular_of_normalized hR hS p hp1 hsing hb' Y).1
  -- the Laurent coordinates
  set xLam : Nat.Partition (R * S) → Lam := fun Y =>
    algebraMap ℂ[X] Lam (((f Y).map (algebraMap ℚ ℂ)).comp (X ^ 2)) * lamXi ^ (2 * n Y) with hxLam
  have hxev : ∀ (b' : ℂ) (hb' : b' ≠ 0) (Y : Nat.Partition (R * S)),
      evLam b' hb' (xLam Y) = RatFunc.eval (algebraMap ℚ ℂ) b' (p Y) := by
    intro b' hb' Y
    have h1 : EvTo b' (p Y)
        ((f Y).eval₂ (algebraMap ℚ ℂ) (b' ^ 2) / b' ^ (2 * n Y)) := by
      rw [hf Y]
      exact (evTo_aeval (f Y) (evTo_X.pow 2)).div (evTo_X.pow (2 * n Y)) (pow_ne_zero _ hb')
    rw [h1.2, hxLam]
    simp only [map_mul, map_pow, evLam_algebraMap, evLam_lamXi, eval_comp, eval_pow, eval_X,
      eval_map]
    rw [div_eq_mul_inv, inv_pow]
  -- base change to `b'`
  have hBCχ : ∀ (b' : ℂ) (hb' : b' ≠ 0),
      Verma.baseChange (evLam b' hb') (evLam_cLam hb') (evLam_hLam hb' R S)
        (pbwCoord (R * S) xLam) =
      pbwCoord (R * S) fun Y => RatFunc.eval (algebraMap ℚ ℂ) b' (p Y) := by
    intro b' hb'
    rw [Verma.baseChange_pbwCoord]
    congr 1
    funext Y
    exact hxev b' hb' Y
  -- `χ` is proportional to the value of the family
  obtain ⟨a, ha⟩ := hU _ _ _ _ χ (hxs b hb) hχ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hχ.1 (ha.trans (zero_smul ℂ (pbwCoord (c := kacC b) (h := kacH R S b) (R * S)
      fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (p Y))))
  rw [ha, negSpan_smul _ ha0] at hv
  -- lift to `Lam`
  have key : ∀ y ∈ negSpan (pbwCoord (c := kacC b) (h := kacH R S b) (R * S)
      fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (p Y)),
      ∃ W : Verma Lam cLam (hLam R S), W ∈ negSpan (pbwCoord (R * S) xLam) ∧
        Verma.baseChange (evLam b hb) (evLam_cLam hb) (evLam_hLam hb R S) W = y := by
    intro y hy
    unfold negSpan at hy
    refine Submodule.span_induction (p := fun y _ =>
      ∃ W : Verma Lam cLam (hLam R S), W ∈ negSpan (pbwCoord (R * S) xLam) ∧
        Verma.baseChange (evLam b hb) (evLam_cLam hb) (evLam_hLam hb R S) W = y) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨w, rfl⟩
      refine ⟨VirEnv.negOp cLam (w.map (↑)) • pbwCoord (R * S) xLam,
        Submodule.subset_span ⟨w, rfl⟩, ?_⟩
      dsimp only
      rw [Verma.baseChange_negOp_smul, hBCχ b hb]
    · exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    · rintro _ _ _ _ ⟨W₁, hW₁, rfl⟩ ⟨W₂, hW₂, rfl⟩
      exact ⟨W₁ + W₂, Submodule.add_mem _ hW₁ hW₂, map_add _ _ _⟩
    · rintro e _ _ ⟨W, hW, rfl⟩
      refine ⟨algebraMap ℂ[X] Lam (C e) • W, Submodule.smul_mem _ _ hW, ?_⟩
      rw [LinearMap.map_smulₛₗ, evLam_algebraMap, eval_C]
  obtain ⟨W, hWmem, hWev⟩ := key _ hv
  set D : Nat.Partition N → Lam := Verma.comp N W with hD
  -- the values of `D` at `b'` lie in the kernel of the Gram matrix
  have hker : ∀ (b' : ℂ) (hb' : b' ≠ 0),
      (gram (kacC b') (kacH R S b') N).mulVec (fun Y => evLam b' hb' (D Y)) = 0 := by
    intro b' hb'
    have hz := baseChange_mem_negSpan (evLam b' hb') (evLam_cLam hb') (evLam_hLam hb' R S) hWmem
    rw [hBCχ b' hb'] at hz
    have hz' := level_part_mem (hxs b' hb') N hz
    have e : (fun Y => evLam b' hb' (D Y)) = Verma.comp N
        (Verma.baseChange (evLam b' hb') (evLam_cLam hb') (evLam_hLam hb' R S) W) := by
      funext Y
      exact (comp_baseChange _ _ _ N W Y).symm
    rw [e]
    funext Y
    rw [gram_mulVec_eq_gramForm, ← shap_pbwCoord]
    exact shap_negSpan_left (hxs b' hb') hRS hz' _
  have hG : (gram cLam (hLam R S) N).mulVec D = 0 := by
    funext Y
    refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' _ => ?_
    have h1 := map_mulVec_apply (evLam b' hb') (gram cLam (hLam R S) N) D Y
    rw [← gram_map, evLam_cLam hb', evLam_hLam hb' R S, hker b' hb'] at h1
    exact h1.symm
  have hT : ∀ k m : ℕ, k < R → m < S →
      (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) N).mulVec D = 0 ∧
        Matrix.vecMul D
          (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) N) = 0 := by
    intro k m hk hm
    have hgen : ∀ (b' : ℂ) (hb' : b' ≠ 0), (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → ∀ Y,
        (torus (kacC b') (kacH R S b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b') N).mulVec
            (fun Y => evLam b' hb' (D Y)) Y = 0 ∧
          Matrix.vecMul (fun Y => evLam b' hb' (D Y))
            (torus (kacC b') (kacH R S b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b') N) Y
              = 0 := by
      intro b' hb' hirr Y
      have hd := generic_descends hH hU hF hLay hb' hirr hR hS hk hm
      have h2 := torusForm_ker_of_descends hd (hker b' hb') (Pi.single Y 1)
      rw [torus_mulVec_eq_torusForm, torus_vecMul_eq_torusForm]
      exact ⟨h2.2, h2.1⟩
    constructor
    · funext Y
      refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' hG' => ?_
      have h1 := map_mulVec_apply (evLam b' hb')
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) N) D Y
      rw [← torus_map, evLam_cLam hb', evLam_hLam hb' R S, evLam_hLam hb',
        (hgen b' hb' hG'.2.1 Y).1] at h1
      exact h1.symm
    · funext Y
      refine lam_eq_zero_of_infinite (generic_infinite ∅) fun b' hb' hG' => ?_
      have h1 := map_vecMul_apply (evLam b' hb')
        (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) N) D Y
      rw [← torus_map, evLam_cLam hb', evLam_hLam hb' R S, evLam_hLam hb',
        (hgen b' hb' hG'.2.1 Y).2] at h1
      exact h1.symm
  -- the family over `ℂ⟦X⟧`
  refine ⟨fun Y => locLam b hb (D Y), fun Y => ?_, ?_, fun k m hk hm => ⟨?_, ?_⟩⟩
  · rw [constantCoeff_locLam, hD, ← comp_baseChange _ (evLam_cLam hb) (evLam_hLam hb R S), hWev,
      comp_pbwCoord_same]
  · funext Y
    have h1 := map_mulVec_apply (locLam b hb) (gram cLam (hLam R S) N) D Y
    rw [← gram_map, locLam_cLam hb, locLam_hLam hb R S, hG] at h1
    rw [h1]
    exact map_zero _
  · funext Y
    have h1 := map_mulVec_apply (locLam b hb)
      (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) N) D Y
    rw [← torus_map, locLam_cLam hb, locLam_hLam hb R S, locLam_hLam hb, (hT k m hk hm).1] at h1
    rw [h1]
    exact map_zero _
  · funext Y
    have h1 := map_vecMul_apply (locLam b hb)
      (torus cLam (hLam R S) (hLam (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) N) D Y
    rw [← torus_map, locLam_cLam hb, locLam_hLam hb R S, locLam_hLam hb, (hT k m hk hm).2] at h1
    rw [h1]
    exact map_zero _

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) : Stmt_sub_tau_kernel_lift :=
  sub_tau_kernel_lift_of_cited hK hE hH hU hF hLau

end Virasoro.P2
