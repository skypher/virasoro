import Virasoro.Proofs.P2Sec11LayerZero
import Virasoro.Proofs.Sec5TopNondeg
import Virasoro.Proofs.Sec8Ising11

/-!
# Proposition 11.2(ii): nondegeneracy of `B̄^{(i)}` and `γ^±_i ≠ 0` (paper.tex l.2470–2472, 2492)

* `B̄^{(i)}_N` is nondegenerate on `J^i_N/J^{i+1}_N`: a vector of `J^i_N` that is
  `B^{(i)}`-orthogonal to `J^i_N` lies in `J^{i+1}_N` (the basis `{v_a(0) : e_a = i}`
  diagonalizes `B̄^{(i)}_N` with entries `u_a(0) ≠ 0`).
* For `J^i = U(Vir_-)χ + U(Vir_-)χ'` with singular vectors of different levels, a vector
  `j_χ(a)` with `B^{(i)}(χ,χ) = 0` or `a ∈ ker G(c,h+ℓ)` lies in `J^{i+1}`.
* `γ^±_i(μ) ≠ 0` (`Stmt_sub_vertex_gamma`).
-/

namespace Virasoro

open Verma Matrix

variable {c h : ℂ}

/-- `B̄^{(i)}_N` is nondegenerate on `J^i_N/J^{i+1}_N`. -/
theorem jform_rad {N i : ℕ} {v : Nat.Partition N → ℂ} (hv : v ∈ jantzenLayer c h N i)
    (h0 : ∀ u ∈ jantzenLayer c h N i, jform c h N i u v = 0) :
    v ∈ jantzenLayer c h N (i + 1) := by
  obtain ⟨w, e, u, hw, hu, hd, ho⟩ :=
    exists_orth_basis (gramLocal_isSymm c h N) (gramLocal_det_ne_zero c h N)
  have hB : OrthBasis (gramLocal c h N) w e u := ⟨hw, hu, hd, ho⟩
  have hv' := hv
  rw [jantzenLayer_eq_layer] at hv'
  obtain ⟨V, hV0, hdvd⟩ := hv'
  have hWT : IsUnit ((Matrix.of w)ᵀ).det := by rw [det_transpose]; exact hw
  set y : Nat.Partition N → PowerSeries ℂ := ((Matrix.of w)ᵀ)⁻¹ *ᵥ V with hy
  have hVy : (Matrix.of w)ᵀ *ᵥ y = V := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hWT, Matrix.one_mulVec]
  have hbf : ∀ b, bf (gramLocal c h N) (w b) V =
      (PowerSeries.X : PowerSeries ℂ) ^ e b * u b * y b := fun b => by
    have := hB.bf_coord y b
    rwa [hVy] at this
  have hy0 : ∀ b, e b < i + 1 → PowerSeries.constantCoeff (y b) = 0 := by
    intro b hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hlt | heq
    · have h1 : (PowerSeries.X : PowerSeries ℂ) ^ i ∣ PowerSeries.X ^ e b * u b * y b := by
        rw [← hbf b]
        exact dvd_dot_right hdvd
      have h2 : (PowerSeries.X : PowerSeries ℂ) ^ e b * PowerSeries.X ∣
          PowerSeries.X ^ e b * (u b * y b) := by
        rw [← pow_succ, ← mul_assoc]
        exact (pow_dvd_pow _ hlt).trans h1
      have h3 : (PowerSeries.X : PowerSeries ℂ) ∣ u b * y b :=
        (mul_dvd_mul_iff_left (pow_ne_zero _ PowerSeries.X_ne_zero)).1 h2
      have h4 : (PowerSeries.X : PowerSeries ℂ) ∣ y b := ((hu b).dvd_mul_left).1 h3
      rw [PowerSeries.X_dvd_iff] at h4
      exact h4
    · have hmem : val0 w b ∈ jantzenLayer c h N i := by
        rw [jantzenLayer_eq_span hB]
        exact Submodule.subset_span ⟨b, heq.ge, rfl⟩
      have h1 := h0 _ hmem
      rw [jform_eq_psForm c h (hB.psFam b heq.ge) ⟨hV0, hdvd⟩, psForm] at h1
      have h2 : V ⬝ᵥ (gramLocal c h N).mulVec (w b) =
          (PowerSeries.X : PowerSeries ℂ) ^ i * (u b * y b) := by
        have e1 : V ⬝ᵥ (gramLocal c h N).mulVec (w b) = bf (gramLocal c h N) V (w b) := rfl
        rw [e1, bf_symm (gramLocal_isSymm c h N), hbf, heq, mul_assoc]
      have h3 := PowerSeries.coeff_X_pow_mul (u b * y b) i 0
      rw [zero_add] at h3
      rw [h2, h3, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left (PowerSeries.isUnit_iff_constantCoeff.1 (hu b)).ne_zero
  have hvsum : v = ∑ a, PowerSeries.constantCoeff (y a) • val0 w a := by
    funext Y
    rw [← hV0 Y, ← hVy]
    simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, val0]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [jantzenLayer_eq_span hB, hvsum]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : i + 1 ≤ e a
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  · rw [hy0 a (not_le.1 ha), zero_smul]
    exact Submodule.zero_mem _

/-- If `γ = B^k(χ,χ) = 0` or `G_M(c,h+ℓ) a = 0`, then `j_χ(a) ∈ J^{k+1}`. -/
theorem layer_kernel (hI : Cited_VermaHomInjective) {k ℓ ℓ' : ℕ}
    {χ χ' : Verma ℂ c h} (hχ : IsSingular χ ℓ) (hχ' : IsSingular χ' ℓ') (hne : ℓ ≠ ℓ')
    (hJ : jantzen c h k = negSpan χ ⊔ negSpan χ') {M : ℕ} (a : Nat.Partition M → ℂ)
    (ha : jv c h k ℓ χ χ = 0 ∨ (gram c (h + ℓ) M).mulVec a = 0)
    (j : Verma ℂ c (h + ℓ) →ₗ[ℂ] Verma ℂ c h) (hjhw : j hw = χ)
    (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v)) (hjr : ∀ x, j x ∈ negSpan χ)
    (hjl : ∀ (n : ℕ) (x : Verma ℂ c (h + ℓ)), x ∈ level n → j x ∈ level (ℓ + n))
    (hjneg : ∀ w : List ℕ, j (neg w) = VirEnv.negOp c w • χ) :
    j (pbwCoord M a) ∈ jantzen c h (k + 1) := by
  obtain ⟨j', -, hjhw', hjL', hjr', hjl', hjneg'⟩ := exists_emb hI hχ'
  have hsub : negSpan χ ≤ jantzen c h k := by
    rw [hJ]
    exact le_sup_left
  have hsub' : negSpan χ' ≤ jantzen c h k := by
    rw [hJ]
    exact le_sup_right
  obtain ⟨y, hy⟩ : ∃ y : Verma ℂ c (h + ℓ), y = pbwCoord M a := ⟨_, rfl⟩
  rw [← hy]
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
  have hz := jform_rad (comp_mem_layer hvJ hvl) hall
  rw [← pbwCoord_comp_of_mem_level hvl]
  exact pbwCoord_mem_jantzen hz

/-- `Stmt_sub_vertex_gamma` (paper.tex l.2395, 2492–2493). -/
theorem sub_vertex_gamma (hJ : Cited_JantzenLayersOrbit) (hU : Cited_SingularUnique)
    (hI : Cited_VermaHomInjective) : Stmt_sub_vertex_gamma := by
  intro p p' r s b hset ε k₀ c μ lev wp wm hw xp xm hx i hi
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  obtain ⟨wp₀, wm₀, ⟨hsing₀, -⟩, hint⟩ := hJ p p' r s b hset ε k₀
  obtain ⟨hsing, hlayer⟩ := hw
  obtain ⟨hsp, hsm⟩ := hsing i hi
  obtain ⟨hsp₀, hsm₀⟩ := hsing₀ i hi
  have span_eq : ∀ {ℓ : ℕ} {χ χ₀ : Verma ℂ c μ}, IsSingular χ ℓ → IsSingular χ₀ ℓ →
      negSpan χ = negSpan χ₀ := by
    intro ℓ χ χ₀ hχ hχ₀
    obtain ⟨a, ha⟩ := hU _ _ _ χ₀ χ hχ₀ hχ
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hχ.1 (ha.trans (by module))
    rw [ha, negSpan_smul _ ha0]
  have ep := span_eq hsp hsp₀
  have em := span_eq hsm hsm₀
  obtain ⟨hinf, hnep, hnem, -⟩ := hint i hi
  rw [← ep, ← em] at hinf
  rw [← ep] at hnep
  rw [← em] at hnem
  have hne : ellOrb p p' r s true (k₀ + i) - ellOrb p p' r s ε k₀ ≠
      ellOrb p p' r s false (k₀ + i) - ellOrb p p' r s ε k₀ := by
    have h1 := ellOrb_lt_add (by omega) (by omega) hr0 hr hs0 hs ε k₀ i hi true
    have h2 := ellOrb_lt_add (by omega) (by omega) hr0 hr hs0 hs ε k₀ i hi false
    have hk : k₀ + i ≠ 0 := by omega
    have h3 : ellOrb p p' r s true (k₀ + i) ≠ ellOrb p p' r s false (k₀ + i) := by
      have := ellPlus_ne_ellMinus hcop hr0 hr hs hn1 (k := k₀ + i) (by omega)
      unfold ellOrb
      rw [if_neg hk, if_neg hk]
      simpa using this
    omega
  have main : ∀ (ℓ ℓ' : ℕ) (χ χ' : Verma ℂ c μ), IsSingular χ ℓ → IsSingular χ' ℓ' → ℓ ≠ ℓ' →
      jantzen c μ i = negSpan χ ⊔ negSpan χ' → negSpan χ ⊓ negSpan χ' = jantzen c μ (i + 1) →
      negSpan χ ≠ jantzen c μ (i + 1) → ∀ x : Nat.Partition ℓ → ℂ, pbwCoord ℓ x = χ →
        jform c μ ℓ i x x ≠ 0 := by
    intro ℓ ℓ' χ χ' hχ hχ' hne hJi hinf hneq x hx h0
    obtain ⟨j, hjinj, hjhw, hjL, hjr, hjl, hjneg⟩ := exists_emb hI hχ
    have hγ : jv c μ i ℓ χ χ = 0 := by
      unfold jv
      rw [← hx, comp_pbwCoord_same]
      exact h0
    have hhw : (Verma.hw : Verma ℂ c (μ + ℓ)) ∈ level 0 := by
      have := neg_mem_level (c := c) (h := μ + ℓ) 0 [] (fun _ h => absurd h List.not_mem_nil)
        le_rfl
      rwa [neg_nil] at this
    have h1 := layer_kernel hI hχ hχ' hne hJi (M := 0)
      (comp 0 (Verma.hw : Verma ℂ c (μ + (ℓ : ℂ)))) (Or.inl hγ) j hjhw hjL
      hjr hjl hjneg
    rw [pbwCoord_comp_of_mem_level hhw, hjhw] at h1
    have hle : negSpan χ ≤ jantzen c μ (i + 1) := by
      rw [negSpan_eq_range j hjneg]
      rintro _ ⟨v, rfl⟩
      refine induction_neg (P := fun v => j v ∈ jantzen c μ (i + 1)) (fun w hw => ?_)
        (fun u v hu hv => by rw [map_add]; exact Submodule.add_mem _ hu hv)
        (fun r v hv => by rw [map_smul]; exact Submodule.smul_mem _ _ hv) v
      induction w with
      | nil => rw [neg_nil, hjhw]; exact h1
      | cons m w ih =>
        rw [Verma.neg_cons, hjL]
        exact L_mem_jantzen c μ (i + 1) _ (ih fun z hz => hw z (List.mem_cons_of_mem _ hz))
    exact hneq (le_antisymm hle (hinf.ge.trans inf_le_left))
  exact ⟨main _ _ _ _ hsp hsm hne (hlayer i hi) hinf hnep (xp i) (hx i hi).1,
    main _ _ _ _ hsm hsp hne.symm (by rw [hlayer i hi, sup_comm]) (by rw [inf_comm]; exact hinf)
      hnem (xm i) (hx i hi).2⟩

example (hJ : Cited_JantzenLayersOrbit) (hU : Cited_SingularUnique)
    (hI : Cited_VermaHomInjective) : Stmt_sub_vertex_gamma := sub_vertex_gamma hJ hU hI

end Virasoro
