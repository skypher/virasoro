import Virasoro.Proofs.P2Sec13GenVertex
import Virasoro.Proofs.P2Sec11LayerBasis

/-!
# Lemma 13.1, Step 1: the trace of the layer `1` of the generic module (l.2899–2903)

The one-summand analogue of the layer formula of Proposition 11.2(ii) (l.2487–2495): if
`J^{i+1}(c,μ) = U(Vir_-)χ ≅ M(c,μ+ℓ)`, `J^{i+2}_N = 0` and `G_M(c,μ+ℓ)` is invertible, then in
the basis `{L_{-Z}χ : |Z| = M}` of `J^{i+1}_{ℓ+M}`, `B^{(i+1)} = γ G_M(c,μ+ℓ)` and
`ρ^{(i+1)} = σ ρ_M(c,μ+ℓ,d)`, so the trace of the layer is `σ/γ · F_M(c,μ+ℓ,d)`.  For the
generic module (`i = 0`), `γ = ∂_Δ B_Δ(χ,χ)`, `σ = ∂_Δ ρ_{Δ,d}(χ,χ)` and `σ/γ` is the box ratio
of Theorem 9.2.
-/

namespace Virasoro.P2

open Virasoro Polynomial Verma

variable {c μ d : ℂ} {i : ℕ}

theorem span_single_eq_top (M : ℕ) :
    Submodule.span ℂ (Set.range fun Z : Nat.Partition M =>
      (Pi.single Z (1 : ℂ) : Nat.Partition M → ℂ)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro a _
  have e : a = ∑ Z, a Z • (Pi.single Z (1 : ℂ) : Nat.Partition M → ℂ) := by
    funext Y
    simp [Pi.single_apply]
  rw [e]
  exact Submodule.sum_mem _ fun Z _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Z, rfl⟩)

theorem gramForm_single (c h : ℂ) (M : ℕ) (Z Z' : Nat.Partition M) :
    gramForm c h M (Pi.single Z 1) (Pi.single Z' 1) = gram c h M Z Z' := by
  classical
  simp [gramForm, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem torusForm_single (c h d : ℂ) (M : ℕ) (Z Z' : Nat.Partition M) :
    torusForm c h d M (Pi.single Z 1) (Pi.single Z' 1) = torus c h d M Z Z' := by
  classical
  simp [torusForm, Matrix.mulVec, dotProduct, Pi.single_apply]

set_option maxHeartbeats 800000 in
/-- The trace of the layer `i + 1` at level `ℓ + M` when `J^{i+1} = U(Vir_-)χ`, `J^{i+2} = 0`
and `G_M(c,μ+ℓ)` is invertible. -/
theorem layer_trace_one (hI : Cited_VermaHomInjective) (HV : VertexPartI c μ d) {ℓ M : ℕ}
    {χ : Verma ℂ c μ} (hχ : IsSingular χ ℓ) (hJ : jantzen c μ (i + 1) = negSpan χ)
    (hJ2 : jantzenLayer c μ (ℓ + M) (i + 1 + 1) = ⊥) (x : Nat.Partition ℓ → ℂ)
    (hx : pbwCoord ℓ x = χ) (hγ : jform c μ ℓ (i + 1) x x ≠ 0)
    (hg : (gram c (μ + (ℓ : ℂ)) M).det ≠ 0) :
    IsLayerTrace c μ d (ℓ + M) (i + 1)
      (vform c μ d ℓ (i + 1) x x / jform c μ ℓ (i + 1) x x * Fval c d (μ + (ℓ : ℂ)) M) := by
  classical
  have hsub : negSpan χ ≤ jantzen c μ (i + 1) := hJ.ge
  obtain ⟨j, -, hjhw, hjL, hjr, hjl, hjneg⟩ := exists_emb hI hχ
  let Φ : (Nat.Partition M → ℂ) →ₗ[ℂ] (Nat.Partition (ℓ + M) → ℂ) :=
    (Verma.comp (ℓ + M)) ∘ₗ j ∘ₗ (pbwCoord M)
  have hΦ : ∀ a, pbwCoord (ℓ + M) (Φ a) = j (pbwCoord M a) :=
    fun a => pbwCoord_comp_of_mem_level (hjl M _ ⟨a, rfl⟩)
  have hΦl : ∀ a, Φ a ∈ jantzenLayer c μ (ℓ + M) (i + 1) :=
    fun a => comp_mem_layer (hsub (hjr _)) (hjl M _ ⟨a, rfl⟩)
  have hχJ : χ ∈ jantzen c μ (i + 1) := by rw [← hjhw]; exact hsub (hjr _)
  have hxl : x ∈ jantzenLayer c μ ℓ (i + 1) := by
    have := comp_mem_layer hχJ (mem_level_of_L_zero hχ.2.1)
    rwa [← hx, comp_pbwCoord_same] at this
  have hγ' : jv c μ (i + 1) ℓ χ χ = jform c μ ℓ (i + 1) x x := by
    unfold jv
    rw [← hx, comp_pbwCoord_same]
  have hσ : rhoJ (pairing (C c) (C μ + X) (C d)) (i + 1) χ χ = vform c μ d ℓ (i + 1) x x := by
    rw [← hx]
    exact rhoJ_pbwCoord HV hxl hxl
  set γ := jform c μ ℓ (i + 1) x x with hγdef
  set σ := vform c μ d ℓ (i + 1) x x with hσdef
  set G := gram c (μ + (ℓ : ℂ)) M with hG
  let F : Nat.Partition M → Nat.Partition (ℓ + M) → ℂ := fun Z => Φ (Pi.single Z 1)
  have jf : ∀ Z Z', jform c μ (ℓ + M) (i + 1) (F Z) (F Z') = γ * G Z Z' := by
    intro Z Z'
    have h := jv_emb_coord j hjl hχ hsub hjhw hjL hjr (Pi.single Z (1 : ℂ))
      (Pi.single Z' (1 : ℂ))
    rw [gramForm_single, hγ'] at h
    exact h
  have vf : ∀ Z Z', vform c μ d (ℓ + M) (i + 1) (F Z) (F Z') = σ * torus c (μ + (ℓ : ℂ)) d M Z Z' := by
    intro Z Z'
    rw [← rhoJ_pbwCoord HV (hΦl _) (hΦl _), hΦ, hΦ,
      rhoJ_emb_coord j hjl hsub hjhw hjL hjr HV, hσ, torusForm_single]
  have hA : (Matrix.of fun Z Z' => jform c μ (ℓ + M) (i + 1) (F Z) (F Z')) = γ • G :=
    Matrix.ext fun Z Z' => by simp [jf]
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hg
  have hAinv : (γ • G)⁻¹ = γ⁻¹ • G⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hγ, one_smul,
      Matrix.mul_nonsing_inv _ hGu]
  have hAdet : (γ • G).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hγ) hg
  have hzero : ∀ cc : Nat.Partition M → ℂ, (∑ Z, cc Z • F Z) = 0 → ∀ Z, cc Z = 0 := by
    intro cc h0
    have hp : cc = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero hAdet
      funext Z₀
      have h1 := jform_sum_left cc F (fun Z => hΦl _) (hΦl (Pi.single Z₀ 1))
      rw [h0, jform_zero_left' (hΦl _)] at h1
      simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [h1]
      exact Finset.sum_congr rfl fun Z _ => by rw [jf]
    intro Z
    rw [hp]
    rfl
  refine ⟨Nat.Partition M, inferInstance, inferInstance, F, fun Z => hΦl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fintype.linearIndependent_iff.2 hzero
  · rw [hJ2]
    exact disjoint_bot_right
  · rw [hJ2, sup_bot_eq]
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨Z, rfl⟩; exact hΦl _)
    · intro u hu
      have huJ : pbwCoord (c := c) (h := μ) (ℓ + M) u ∈ jantzen c μ (i + 1) :=
        pbwCoord_mem_jantzen hu
      rw [hJ, negSpan_eq_range j hjneg] at huJ
      obtain ⟨y, hy⟩ := huJ
      have e : u = Φ (Verma.comp M y) := by
        have h1 := congrArg (Verma.comp (c := c) (h := μ) (ℓ + M)) (emb_level_comp j hjl M y)
        rw [comp_pbwCoord_same, hy, comp_pbwCoord_same] at h1
        rw [h1]
        rfl
      rw [e]
      have h1 : Φ (Verma.comp M y) ∈ (Submodule.span ℂ (Set.range fun Z : Nat.Partition M =>
          (Pi.single Z (1 : ℂ) : Nat.Partition M → ℂ))).map Φ := by
        rw [span_single_eq_top]
        exact Submodule.mem_map_of_mem trivial
      rw [Submodule.map_span, ← Set.range_comp] at h1
      exact h1
  · rw [hA]
    exact hAdet
  · rw [hA, hAinv]
    have hsym : ∀ a b, G.adjugate a b = G.adjugate b a := by
      intro a b
      have h1 : G.adjugate = G.adjugate.transpose := by
        have := Matrix.adjugate_transpose G
        rw [hG, gram_transpose] at this
        exact this.symm
      have h2 := congrFun (congrFun h1 a) b
      rw [Matrix.transpose_apply] at h2
      exact h2
    have hinv : ∀ a b, G⁻¹ a b = G.det⁻¹ * G.adjugate a b := by
      intro a b
      rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    have e1 : ∑ a, ∑ b, (γ⁻¹ • G⁻¹) a b * vform c μ d (ℓ + M) (i + 1) (F b) (F a) =
        σ / γ * (G.det⁻¹ * ∑ a, ∑ b, G.adjugate a b * torus c (μ + (ℓ : ℂ)) d M b a) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, vf, hinv]
      ring
    have e2 : Fval c d (μ + (ℓ : ℂ)) M =
        G.det⁻¹ * ∑ a, ∑ b, G.adjugate a b * torus c (μ + (ℓ : ℂ)) d M b a := by
      show (∑ Y, ∑ Y', G.adjugate Y Y' * torus c (μ + (ℓ : ℂ)) d M Y Y') / G.det = _
      rw [div_eq_inv_mul, Finset.sum_comm]
      refine congrArg (fun z => G.det⁻¹ * z) ?_
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hsym]
    rw [e1, e2]

/-- Below the level of `χ` the layer `i + 1` is zero and its trace is `0`. -/
theorem layer_trace_one_below {N : ℕ} (hJ0 : jantzenLayer c μ N (i + 1) = ⊥) :
    IsLayerTrace c μ d N (i + 1) 0 := by
  classical
  have hJ1 : jantzenLayer c μ N (i + 1 + 1) = ⊥ := by
    rw [eq_bot_iff, ← hJ0]
    exact jantzenLayer_succ_le N (i + 1)
  refine ⟨Fin 0, inferInstance, inferInstance, fun α => α.elim0, fun α => α.elim0,
    linearIndependent_empty_type, ?_, ?_, ?_, ?_⟩
  · rw [hJ1]
    exact disjoint_bot_right
  · rw [hJ1, hJ0]
    simp
  · rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · simp

end Virasoro.P2
