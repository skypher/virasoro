import Virasoro.Proofs.TopLayerForm
import Virasoro.Proofs.Sec5TopLayer

/-!
# Theorem 5.9 of `paper.tex` at 70bac53: `γ^±_k ≠ 0` and `det G_M(c⋆, μ^±_k) ≠ 0`

Paper.tex l.850–869.  `B^k` is nondegenerate on `J^k_{N'}` (Lemma 5.4(ii)); in the basis
`L_{-Z}w^±_k` its matrix on `(W^±_k)_{N'}` is `γ^±_k G_{N'-ℓ^±_k}(c⋆,μ^±_k)`, and the two summands
are orthogonal.  A kernel vector `a` of `γ G_M(c,h+ℓ)` gives `j_χ(∑ a_Z L_{-Z}|h+ℓ⟩)` in the
radical of `B^k`, so it vanishes, and `a = 0` because `j_χ` is injective
(Cited_VermaHomInjective).
-/

namespace Virasoro

open Verma Module

variable {c h : ℂ}

/-- If `γ = B^k(χ,χ) = 0` or `G_M(c,h+ℓ) a = 0`, then `a = 0`. -/
theorem top_kernel_trivial (hI : Cited_VermaHomInjective) {k ℓ ℓ' : ℕ}
    {χ χ' : Verma ℂ c h} (hχ : IsSingular χ ℓ) (hχ' : IsSingular χ' ℓ') (hne : ℓ ≠ ℓ')
    (hJ : jantzen c h k = negSpan χ ⊔ negSpan χ') {M : ℕ}
    (htop : ∃ s : Multiset ℕ, IsSmith (gramLocal c h (ℓ + M)) s ∧ s.sup = k)
    (a : Nat.Partition M → ℂ)
    (ha : jv c h k ℓ χ χ = 0 ∨ (gram c (h + ℓ) M).mulVec a = 0) : a = 0 := by
  obtain ⟨j, hjinj, hjhw, hjL, hjr, hjl, hjneg⟩ := exists_emb hI hχ
  obtain ⟨j', -, hjhw', hjL', hjr', hjl', hjneg'⟩ := exists_emb hI hχ'
  have hsub : negSpan χ ≤ jantzen c h k := by
    rw [hJ]
    exact le_sup_left
  have hsub' : negSpan χ' ≤ jantzen c h k := by
    rw [hJ]
    exact le_sup_right
  obtain ⟨s, hs, hsup⟩ := htop
  obtain ⟨y, hy⟩ : ∃ y : Verma ℂ c (h + ℓ), y = pbwCoord M a := ⟨_, rfl⟩
  have hyl : y ∈ level M := ⟨a, hy.symm⟩
  have hvJ : j y ∈ jantzen c h k := hsub (hjr y)
  have hvl : j y ∈ level (ℓ + M) := hjl M y hyl
  have hgen : ∀ w : List ℕ, PosWord w → ℓ + w.sum = ℓ + M →
      jv c h k (ℓ + M) (VirEnv.negOp c w • χ) (j y) = 0 := by
    intro w hw hsum
    have hwM : w.sum = M := by omega
    have h1 := jv_emb hχ hsub j hjhw hjL hjr hjl w hw y (by rw [hwM]; exact hyl)
    rw [hwM, hjneg] at h1
    rw [h1]
    rcases ha with ha | ha
    · rw [ha, zero_mul]
    · have hnw : neg (c := c) (h := h + ℓ) w ∈ level M := by
        rw [← hwM]
        exact neg_mem_level _ w hw le_rfl
      obtain ⟨e, he⟩ := hnw
      rw [← he, hy, pbwCoord_apply, map_sum, LinearMap.sum_apply, Finset.sum_eq_zero, mul_zero]
      intro Y _
      rw [map_smul, LinearMap.smul_apply, shap_neg_pbwCoord, ha, Pi.zero_apply, smul_zero]
  have hgen' : ∀ w : List ℕ, PosWord w → ℓ' + w.sum = ℓ + M →
      jv c h k (ℓ + M) (VirEnv.negOp c w • χ') (j y) = 0 := by
    intro w hw hsum
    rw [← hjneg', ← hsum]
    exact jv_orth hχ' hne.symm hsub' hsub j' hjhw' hjL' hjr' hjl' j hjL hjr hjl w hw M hsum y hyl
  have key : ∀ T : Set (Verma ℂ c h),
      (∀ t ∈ T, t ∈ jantzen c h k ∧ t ∈ level (ℓ + M) ∧ jv c h k (ℓ + M) t (j y) = 0) →
      ∀ z ∈ Submodule.span ℂ T,
        z ∈ jantzen c h k ∧ z ∈ level (ℓ + M) ∧ jv c h k (ℓ + M) z (j y) = 0 := by
    intro T hT z hz
    refine Submodule.span_induction (p := fun z _ => z ∈ jantzen c h k ∧ z ∈ level (ℓ + M) ∧
      jv c h k (ℓ + M) z (j y) = 0) (fun t ht => hT t ht)
      ⟨Submodule.zero_mem _, Submodule.zero_mem _, jv_zero_left hvJ hvl⟩ ?_ ?_ hz
    · rintro x1 x2 _ _ ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
      refine ⟨Submodule.add_mem _ h1 h4, Submodule.add_mem _ h2 h5, ?_⟩
      rw [jv_add_left h1 h2 h4 h5 hvJ hvl, h3, h6, add_zero]
    · rintro b x _ ⟨h1, h2, h3⟩
      refine ⟨Submodule.smul_mem _ _ h1, Submodule.smul_mem _ _ h2, ?_⟩
      exact (jv_smul_left b h1 h2 hvJ hvl).trans (by rw [h3, mul_zero])
  have hall : ∀ u ∈ jantzenLayer c h (ℓ + M) k,
      jform c h (ℓ + M) k u (comp (ℓ + M) (j y)) = 0 := by
    intro u hu
    have huJ : pbwCoord (c := c) (h := h) (ℓ + M) u ∈ jantzen c h k := pbwCoord_mem_jantzen hu
    have hul : pbwCoord (c := c) (h := h) (ℓ + M) u ∈ level (ℓ + M) := ⟨u, rfl⟩
    rw [hJ] at huJ
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.1 huJ
    have hdec : pbwCoord (c := c) (h := h) (ℓ + M) u =
        pbwCoord (ℓ + M) (comp (ℓ + M) b) + pbwCoord (ℓ + M) (comp (ℓ + M) b') := by
      rw [← map_add, ← map_add, hbb, comp_pbwCoord_same]
    obtain ⟨h1, h2, h3⟩ := key _ (by
      rintro t ⟨w, hw, hsum, rfl⟩
      refine ⟨?_, ?_, hgen w hw hsum⟩
      · rw [← hjneg]
        exact hsub (hjr _)
      · rw [← hjneg, ← hsum]
        exact hjl _ _ (neg_mem_level _ w hw le_rfl)) _
      (pbwCoord_comp_negSpan_mem_span (mem_level_of_L_zero hχ.2.1) (ℓ + M) hb)
    obtain ⟨h4, h5, h6⟩ := key _ (by
      rintro t ⟨w, hw, hsum, rfl⟩
      refine ⟨?_, ?_, hgen' w hw hsum⟩
      · rw [← hjneg']
        exact hsub' (hjr' _)
      · rw [← hjneg', ← hsum]
        exact hjl' _ _ (neg_mem_level _ w hw le_rfl)) _
      (pbwCoord_comp_negSpan_mem_span (mem_level_of_L_zero hχ'.2.1) (ℓ + M) hb')
    have h7 := jv_add_left h1 h2 h4 h5 hvJ hvl
    rw [h3, h6, add_zero, ← hdec] at h7
    unfold jv at h7
    rwa [comp_pbwCoord_same] at h7
  have hz := (jform_top c h (gramLocal_det_ne_zero c h (ℓ + M)) hs hsup).1
    (comp (ℓ + M) (j y)) (comp_mem_layer hvJ hvl) hall
  have hjy : j y = 0 := by
    rw [← pbwCoord_comp_of_mem_level hvl, hz, map_zero]
  have hy0 : y = 0 := hjinj (hjy.trans (map_zero j).symm)
  rw [hy] at hy0
  exact pbwCoord_injective M (hy0.trans (map_zero _).symm)

/-- The sub-statement `Stmt_sub_top_layer_nondeg` of Theorem 5.9, from the cited injectivity of
the singular embedding. -/
theorem sub_top_layer_nondeg_of_cited (hI : Cited_VermaHomInjective) :
    Stmt_sub_top_layer_nondeg := by
  intro p p' r s b hset wp wm hT k N hk hN1 hN2
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  have hJ := hT.2 k hk
  have hsing := hT.1 k hk
  have htop : ∀ N' : ℕ, ellMin p p' r s k ≤ N' → N' ≤ N →
      ∃ s' : Multiset ℕ, IsSmith (gramLocal (kacC b) (kacH r s b) N') s' ∧ s'.sup = k := by
    intro N' h1 h2
    obtain ⟨e, he⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH r s b) N')
    refine ⟨e, he, ?_⟩
    rw [← (smith_main he).2.2, poleOrderInv_eq_jDepth hset' hT N']
    exact jDepth_eq_of_range hp hp' hr hrp hs hsp hk h1 (lt_of_le_of_lt h2 hN2)
  have main : ∀ (ℓ ℓ' : ℕ) (χ χ' : Verma ℂ (kacC b) (kacH r s b)), IsSingular χ ℓ →
      IsSingular χ' ℓ' → ℓ ≠ ℓ' →
      jantzen (kacC b) (kacH r s b) k = negSpan χ ⊔ negSpan χ' → ellMin p p' r s k ≤ ℓ →
      ∀ x : Nat.Partition ℓ → ℂ, pbwCoord ℓ x = χ → ℓ ≤ N →
        jform (kacC b) (kacH r s b) ℓ k x x ≠ 0 ∧
        ∀ M : ℕ, M ≤ N - ℓ → (gram (kacC b) (kacH r s b + (ℓ : ℂ)) M).det ≠ 0 := by
    intro ℓ ℓ' χ χ' hχ hχ' hne hJ hmin x hx hle
    have hγ : jv (kacC b) (kacH r s b) k ℓ χ χ = jform (kacC b) (kacH r s b) ℓ k x x := by
      unfold jv
      rw [← hx, comp_pbwCoord_same]
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 := top_kernel_trivial hI hχ hχ' hne hJ (M := 0)
        (htop (ℓ + 0) (by omega) (by omega)) (fun _ => 1) (Or.inl (hγ.trans h0))
      exact one_ne_zero (congrFun h1 (Nat.Partition.indiscrete 0))
    · intro M hM hdet
      obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      exact ha0 (top_kernel_trivial hI hχ hχ' hne hJ (htop (ℓ + M) (by omega) (by omega)) a
        (Or.inr ha))
  exact ⟨fun xp hxp hle => main _ _ _ _ hsing.1 hsing.2 hne hJ (min_le_left _ _) xp hxp hle,
    fun xm hxm hle => main _ _ _ _ hsing.2 hsing.1 hne.symm (by rw [hJ, sup_comm])
      (min_le_right _ _) xm hxm hle⟩

end Virasoro
