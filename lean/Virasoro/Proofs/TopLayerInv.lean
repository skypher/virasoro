import Virasoro.Proofs.TopLayerForm

/-!
# Theorem 5.9 of `paper.tex` at 70bac53: `[x^{-k}] G_{N'}(c,h+x)⁻¹` in the basis `L_{-Z}w^±`

Paper.tex l.871–876.  With `U^±` the matrix whose columns are the level-`N'` coordinates of
`L_{-Z}w^±_k`, Lemma 5.4(ii) in this basis reads
`[x^{-k}] G_{N'}⁻¹ = ∑_± (γ^±)⁻¹ U^± G_{N'-ℓ^±}(c,μ^±)⁻¹ (U^±)ᵀ`:
both sides map `w` into `J^k_{N'}` and pair to `uᵀw` with every `u ∈ J^k_{N'}` under `B^k`, which
is nondegenerate.
-/

namespace Virasoro

open Verma Module

variable {c h : ℂ}

/-- The matrix whose column `Z` is the level-`N'` coordinate vector of `L_{-Z}χ`. -/
noncomputable def Umat (χ : Verma ℂ c h) (N' M : ℕ) :
    Matrix (Nat.Partition N') (Nat.Partition M) ℂ :=
  Matrix.of fun Y Z => comp N' (VirEnv.negOp c Z.word • χ) Y

theorem Umat_mulVec (χ : Verma ℂ c h) (N' M : ℕ) {ℓ : ℕ}
    (j : Verma ℂ c (h + ℓ) →ₗ[ℂ] Verma ℂ c h)
    (hjneg : ∀ w : List ℕ, j (neg w) = VirEnv.negOp c w • χ) (b : Nat.Partition M → ℂ) :
    (Umat χ N' M).mulVec b = comp N' (j (pbwCoord M b)) := by
  funext Y
  rw [pbwCoord_apply, map_sum, map_sum, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Umat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [LinearMap.map_smul j, LinearMap.map_smul (comp N'), hjneg, Pi.smul_apply, smul_eq_mul,
    mul_comm]

/-- The block `γ⁻¹ U G_M(c,h+ℓ)⁻¹ Uᵀ` of a singular vector `χ` of level `ℓ`, `γ = B^k(χ,χ)`. -/
noncomputable def topBlock (k ℓ : ℕ) (χ : Verma ℂ c h) (N' M : ℕ) :
    Matrix (Nat.Partition N') (Nat.Partition N') ℂ :=
  (jv c h k ℓ χ χ)⁻¹ • (Umat χ N' M * (gram c (h + ℓ) M)⁻¹ * (Umat χ N' M).transpose)

/-- The vector `topBlock w` and its `B^k`-pairings with the spanning vectors of `J^k_{N'}`. -/
theorem topBlock_vec (hI : Cited_VermaHomInjective) {k ℓ ℓ' : ℕ} {χ χ' : Verma ℂ c h}
    (hχ : IsSingular χ ℓ) (hχ' : IsSingular χ' ℓ') (hne : ℓ ≠ ℓ')
    (hsub : negSpan χ ≤ jantzen c h k) (hsub' : negSpan χ' ≤ jantzen c h k) (N' M : ℕ)
    (hM : ℓ ≤ N' → ℓ + M = N') (hγ : ℓ ≤ N' → jv c h k ℓ χ χ ≠ 0)
    (hdet : ℓ ≤ N' → (gram c (h + ℓ) M).det ≠ 0) (w : Nat.Partition N' → ℂ) :
    ∃ v : Verma ℂ c h, v ∈ jantzen c h k ∧ v ∈ level N' ∧
      (topBlock k ℓ χ N' M).mulVec w = comp N' v ∧
      (∀ w0 : List ℕ, PosWord w0 → ℓ + w0.sum = N' →
        jv c h k N' (VirEnv.negOp c w0 • χ) v = comp N' (VirEnv.negOp c w0 • χ) ⬝ᵥ w) ∧
      (∀ w0 : List ℕ, PosWord w0 → ℓ' + w0.sum = N' →
        jv c h k N' (VirEnv.negOp c w0 • χ') v = 0) := by
  obtain ⟨j, -, hjhw, hjL, hjr, hjl, hjneg⟩ := exists_emb hI hχ
  obtain ⟨j', -, hjhw', hjL', hjr', hjl', hjneg'⟩ := exists_emb hI hχ'
  obtain ⟨b, hb⟩ : ∃ b : Nat.Partition M → ℂ, b = (jv c h k ℓ χ χ)⁻¹ •
      ((gram c (h + ℓ) M)⁻¹).mulVec ((Umat χ N' M).transpose.mulVec w) := ⟨_, rfl⟩
  have hblk : (topBlock k ℓ χ N' M).mulVec w = comp N' (j (pbwCoord M b)) := by
    rw [← Umat_mulVec χ N' M j hjneg, hb, topBlock, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hyl : pbwCoord (c := c) (h := h + ℓ) M b ∈ level M := ⟨b, rfl⟩
  by_cases hle : ℓ ≤ N'
  · have hN := hM hle
    subst hN
    refine ⟨j (pbwCoord M b), hsub (hjr _), hjl M _ hyl, hblk, ?_, ?_⟩
    · intro w0 hw0 hsum
      have hwM : w0.sum = M := by omega
      have h1 := jv_emb hχ hsub j hjhw hjL hjr hjl w0 hw0 (pbwCoord M b)
        (by rw [hwM]; exact hyl)
      rw [hwM, hjneg] at h1
      rw [h1]
      have hnw : neg (c := c) (h := h + ℓ) w0 ∈ level M := by
        rw [← hwM]
        exact neg_mem_level _ w0 hw0 le_rfl
      obtain ⟨e, he⟩ := hnw
      have hU : comp (ℓ + M) (VirEnv.negOp c w0 • χ) = (Umat χ (ℓ + M) M).mulVec e := by
        rw [Umat_mulVec χ (ℓ + M) M j hjneg, he, hjneg]
      have hG : (gram c (h + ℓ) M).mulVec b =
          (jv c h k ℓ χ χ)⁻¹ • (Umat χ (ℓ + M) M).transpose.mulVec w := by
        rw [hb, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet hle)), Matrix.one_mulVec]
      have hs : shap c (h + ℓ) (neg w0) (pbwCoord M b) =
          e ⬝ᵥ (gram c (h + ℓ) M).mulVec b := by
        rw [← he, pbwCoord_apply, map_sum, LinearMap.sum_apply, dotProduct]
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [map_smul, LinearMap.smul_apply, shap_neg_pbwCoord, smul_eq_mul]
      rw [hs, hG, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose, ← hU, ← mul_assoc, mul_inv_cancel₀ (hγ hle), one_mul]
    · intro w0 hw0 hsum
      rw [← hjneg', ← hsum]
      exact jv_orth hχ' hne.symm hsub' hsub j' hjhw' hjL' hjr' hjl' j hjL hjr hjl w0 hw0 M hsum
        _ hyl
  · refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_, ?_, ?_⟩
    · rw [hblk, comp_of_mem_level_ne (by omega) (hjl M _ hyl), map_zero]
    · intro w0 _ hsum
      omega
    · intro w0 hw0 hsum
      refine jv_zero_right ?_ ?_
      · rw [← hjneg']
        exact hsub' (hjr' _)
      · rw [← hjneg', ← hsum]
        exact hjl' _ _ (neg_mem_level _ w0 hw0 le_rfl)

/-- Lemma 5.4(ii) in the basis `L_{-Z}χ`, `L_{-Z}χ'` of `J^k_{N'}`. -/
theorem invCoeff_top_eq (hI : Cited_VermaHomInjective) {k ℓ ℓ' : ℕ} {χ χ' : Verma ℂ c h}
    (hχ : IsSingular χ ℓ) (hχ' : IsSingular χ' ℓ') (hne : ℓ ≠ ℓ')
    (hJ : jantzen c h k = negSpan χ ⊔ negSpan χ') (N' M M' : ℕ)
    (hM : ℓ ≤ N' → ℓ + M = N') (hM' : ℓ' ≤ N' → ℓ' + M' = N')
    (htop : ∃ s : Multiset ℕ, IsSmith (gramLocal c h N') s ∧ s.sup = k)
    (hγ : ℓ ≤ N' → jv c h k ℓ χ χ ≠ 0) (hγ' : ℓ' ≤ N' → jv c h k ℓ' χ' χ' ≠ 0)
    (hdet : ℓ ≤ N' → (gram c (h + ℓ) M).det ≠ 0)
    (hdet' : ℓ' ≤ N' → (gram c (h + ℓ') M').det ≠ 0) :
    invCoeff (gramLocal c h N') (-(k : ℤ)) = topBlock k ℓ χ N' M + topBlock k ℓ' χ' N' M' := by
  classical
  have hsub : negSpan χ ≤ jantzen c h k := by
    rw [hJ]
    exact le_sup_left
  have hsub' : negSpan χ' ≤ jantzen c h k := by
    rw [hJ]
    exact le_sup_right
  obtain ⟨s, hs, hsup⟩ := htop
  have hnd := jform_top c h (gramLocal_det_ne_zero c h N') hs hsup
  have hvec : ∀ w : Nat.Partition N' → ℂ,
      (invCoeff (gramLocal c h N') (-(k : ℤ))).mulVec w =
        (topBlock k ℓ χ N' M + topBlock k ℓ' χ' N' M').mulVec w := by
    intro w
    obtain ⟨v1, h1J, h1l, h1c, h1a, h1b⟩ :=
      topBlock_vec hI hχ hχ' hne hsub hsub' N' M hM hγ hdet w
    obtain ⟨v2, h2J, h2l, h2c, h2a, h2b⟩ :=
      topBlock_vec hI hχ' hχ hne.symm hsub' hsub N' M' hM' hγ' hdet' w
    have hVJ : v1 + v2 ∈ jantzen c h k := Submodule.add_mem _ h1J h2J
    have hVl : v1 + v2 ∈ level N' := Submodule.add_mem _ h1l h2l
    rw [Matrix.add_mulVec, h1c, h2c, ← map_add]
    obtain ⟨j, -, -, -, hjr, hjl, hjneg⟩ := exists_emb hI hχ
    obtain ⟨j', -, -, -, hjr', hjl', hjneg'⟩ := exists_emb hI hχ'
    let φ : Verma ℂ c h →ₗ[ℂ] ℂ :=
      { toFun := fun t => comp N' t ⬝ᵥ w
        map_add' := fun x y => by rw [map_add, add_dotProduct]
        map_smul' := fun a x => by rw [map_smul, smul_dotProduct]; rfl }
    have hφ : ∀ t, φ t = comp N' t ⬝ᵥ w := fun _ => rfl
    have hall : ∀ u ∈ jantzenLayer c h N' k,
        jform c h N' k u (comp N' (v1 + v2)) = u ⬝ᵥ w := by
      intro u hu
      have huJ : pbwCoord (c := c) (h := h) N' u ∈ jantzen c h k := pbwCoord_mem_jantzen hu
      rw [hJ] at huJ
      obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.1 huJ
      have hdec : pbwCoord (c := c) (h := h) N' u =
          pbwCoord N' (comp N' b) + pbwCoord N' (comp N' b') := by
        rw [← map_add, ← map_add, hbb, comp_pbwCoord_same]
      obtain ⟨g1, g2, g3⟩ := jv_span hVJ hVl φ (by
        rintro t ⟨w0, hw0, hsum, rfl⟩
        have htJ : VirEnv.negOp c w0 • χ ∈ jantzen c h k := by
          rw [← hjneg]
          exact hsub (hjr _)
        have htl : VirEnv.negOp c w0 • χ ∈ level N' := by
          rw [← hjneg, ← hsum]
          exact hjl _ _ (neg_mem_level _ w0 hw0 le_rfl)
        refine ⟨htJ, htl, ?_⟩
        rw [jv_add_right htJ htl h1J h1l h2J h2l, h1a w0 hw0 hsum, h2b w0 hw0 hsum, add_zero,
          hφ]) _
        (pbwCoord_comp_negSpan_mem_span (mem_level_of_L_zero hχ.2.1) N' hb)
      obtain ⟨g4, g5, g6⟩ := jv_span hVJ hVl φ (by
        rintro t ⟨w0, hw0, hsum, rfl⟩
        have htJ : VirEnv.negOp c w0 • χ' ∈ jantzen c h k := by
          rw [← hjneg']
          exact hsub' (hjr' _)
        have htl : VirEnv.negOp c w0 • χ' ∈ level N' := by
          rw [← hjneg', ← hsum]
          exact hjl' _ _ (neg_mem_level _ w0 hw0 le_rfl)
        refine ⟨htJ, htl, ?_⟩
        rw [jv_add_right htJ htl h1J h1l h2J h2l, h1b w0 hw0 hsum, h2a w0 hw0 hsum, zero_add,
          hφ]) _
        (pbwCoord_comp_negSpan_mem_span (mem_level_of_L_zero hχ'.2.1) N' hb')
      have h7 := jv_add_left g1 g2 g4 g5 hVJ hVl
      rw [g3, g6, ← hdec, ← LinearMap.map_add φ, ← hdec, hφ, comp_pbwCoord_same] at h7
      unfold jv at h7
      rwa [comp_pbwCoord_same] at h7
    obtain ⟨hSmem, hSpair⟩ := hnd.2 w
    have hVmem : comp N' (v1 + v2) ∈ jantzenLayer c h N' k := comp_mem_layer hVJ hVl
    have hD : (-1 : ℂ) • comp N' (v1 + v2) +
        (invCoeff (gramLocal c h N') (-(k : ℤ))).mulVec w = 0 := by
      refine hnd.1 _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hVmem) hSmem) fun u hu => ?_
      rw [jform_symm c h hu (Submodule.add_mem _ (Submodule.smul_mem _ _ hVmem) hSmem),
        jform_add_smul_left (-1) hVmem hSmem hu, jform_symm c h hVmem hu,
        jform_symm c h hSmem hu, hall u hu, hSpair u hu]
      ring
    rw [neg_one_smul, neg_add_eq_zero] at hD
    exact hD.symm
  refine Matrix.ext fun Y Y' => ?_
  have h1 := congrFun (hvec (Pi.single Y' 1)) Y
  simpa using h1

end Virasoro
