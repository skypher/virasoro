import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Proofs.Singular
import Virasoro.Proofs.LevelComp
import Virasoro.Proofs.JantzenLevel
import Virasoro.Proofs.Shapovalov
import Virasoro.Proofs.Levels
import Virasoro.Proofs.PBWBasis
import Virasoro.Cited

/-!
# Singular submodules: lowest vectors and pullbacks

For a singular vector `χ` of level `ℓ` in `M(c,h)`, `U(Vir_-)χ` is the image of the embedding
`j_χ : M(c,h+ℓ) → M(c,h)`.  A nonzero singular vector of `U(Vir_-)χ` of level `N` pulls back
to a singular vector of `M(c,h+ℓ)` of level `N - ℓ` (Cited_VermaHomInjective), and there is no
singular vector of level `n ≥ 1` where `det G_n ≠ 0`.
-/

namespace Virasoro

open Verma Module

variable {c h : ℂ}

theorem sum_pnat_pos {w : List ℕ+} (hw : w ≠ []) : 0 < (w.map (fun x : ℕ+ => (x : ℕ))).sum := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a w =>
    simp only [List.map_cons, List.sum_cons]
    have := a.pos
    omega

/-- The level-`ℓ` part of `U(Vir_-)χ`, for `χ` of level `ℓ`, is `ℂ χ`. -/
theorem pbwCoord_comp_negSpan_mem {χ : Verma ℂ c h} {ℓ : ℕ} (hχ : χ ∈ level ℓ)
    {b : Verma ℂ c h} (hb : b ∈ negSpan χ) :
    pbwCoord ℓ (comp ℓ b) ∈ Submodule.span ℂ {χ} := by
  unfold negSpan at hb
  refine Submodule.span_induction
    (p := fun b _ => pbwCoord ℓ (comp ℓ b) ∈ Submodule.span ℂ {χ}) ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨w, rfl⟩
    dsimp only
    by_cases hw : w = []
    · subst hw
      rw [List.map_nil, negOp_nil_smul, pbwCoord_comp_of_mem_level hχ]
      exact Submodule.mem_span_singleton_self χ
    · have hlev := negOp_smul_mem_level hχ (w.map (fun x : ℕ+ => (x : ℕ)))
      have hpos := sum_pnat_pos hw
      rw [comp_of_mem_level_ne (by omega) hlev, map_zero]
      exact zero_mem _
  · rw [map_zero, map_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [map_add, map_add]
    exact add_mem hx hy
  · intro a x _ hx
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ a hx

/-- A nonzero vector of lowest level in a submodule stable under the modes is singular. -/
theorem isSingular_of_lowest {W : Submodule ℂ (Verma ℂ c h)} (hW : IsVirSubmodule W) {N : ℕ}
    (hlow : ∀ M < N, W ⊓ level M = ⊥) {v : Verma ℂ c h} (hv : v ∈ W) (hvl : v ∈ level N)
    (hv0 : v ≠ 0) : IsSingular v N := by
  refine ⟨hv0, L_zero_of_mem_level hvl, fun n hn => ?_⟩
  by_cases hnN : (N : ℤ) < n
  · exact L_eq_zero_of_level hnN hvl
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = N - n := ⟨(N - n).toNat, by omega⟩
    have hmN : m < N := by omega
    have hmem : L n v ∈ W ⊓ level m := ⟨hW n v hv, L_mem_level hm hvl⟩
    rw [hlow m hmN] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem

theorem isVirSubmodule_inf {W W' : Submodule ℂ (Verma ℂ c h)} (hW : IsVirSubmodule W)
    (hW' : IsVirSubmodule W') : IsVirSubmodule (W ⊓ W') :=
  fun n v hv => ⟨hW n v hv.1, hW' n v hv.2⟩

/-- `U(Vir_-)χ` is the image of `j_χ`. -/
theorem negSpan_eq_range {χ : Verma ℂ c h} {h' : ℂ} (j : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c h)
    (hj : ∀ w : List ℕ, j (neg w) = VirEnv.negOp c w • χ) : negSpan χ = LinearMap.range j := by
  apply le_antisymm
  · unfold negSpan
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨neg _, hj _⟩
  · rintro _ ⟨u, rfl⟩
    have hu : u ∈ Submodule.span ℂ (Set.range fun Y : (Σ N : ℕ, Nat.Partition N) =>
        neg (c := c) (h := h') Y.2.word) := by
      rw [span_neg_word_eq_top]
      trivial
    refine Submodule.span_induction (p := fun u _ => j u ∈ negSpan χ) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨Y, rfl⟩
      rw [hj]
      have hpos : ∀ y ∈ Y.2.word, 0 < y := by
        intro y hy
        refine Y.2.parts_pos ?_
        rw [← Verma.word_coe]
        exact Multiset.mem_coe.2 hy
      have hmap : (Y.2.word.map Nat.toPNat').map PNat.val = Y.2.word := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id Y.2.word]
        refine List.map_congr_left fun y hy => ?_
        simp [Nat.toPNat'_coe, hpos y hy]
      refine Submodule.subset_span ⟨Y.2.word.map Nat.toPNat', ?_⟩
      show VirEnv.negOp c (List.map PNat.val _) • χ = _
      rw [hmap]
    · rw [map_zero]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ a hx

/-- `U(Vir_-)χ` is stable under the modes for a singular `χ`. -/
theorem negSpan_isVir {χ : Verma ℂ c h} {ℓ : ℕ} (hχ : IsSingular χ ℓ) :
    IsVirSubmodule (negSpan χ) := by
  obtain ⟨j, -, hjL, hjneg⟩ := exists_singularHom hχ.2.1 hχ.2.2
  rw [negSpan_eq_range j hjneg]
  rintro n _ ⟨u, rfl⟩
  exact ⟨L n u, hjL n u⟩

/-- A nonzero singular vector of `U(Vir_-)χ` pulls back along `j_χ`. -/
theorem singular_pullback (hI : Cited_VermaHomInjective) {χ : Verma ℂ c h} {ℓ : ℕ}
    (hχ : IsSingular χ ℓ) {v : Verma ℂ c h} (hv : v ∈ negSpan χ) {N : ℕ}
    (hvs : IsSingular v N) :
    ℓ ≤ N ∧ ∃ u : Verma ℂ c (h + ℓ), IsSingular u (N - ℓ) := by
  classical
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hχ.2.1 hχ.2.2
  have hj0 : j ≠ 0 := by
    intro h0
    apply hχ.1
    rw [← hjhw, h0]
    rfl
  have hinj : Function.Injective j := hI c h (h + ℓ) j hjL hj0
  rw [negSpan_eq_range j hjneg] at hv
  obtain ⟨u, rfl⟩ := hv
  have hχl : χ ∈ level ℓ := mem_level_of_L_zero hχ.2.1
  have hjlev : ∀ (n : ℕ) (x : Verma ℂ c (h + ℓ)), x ∈ level n → j x ∈ level (ℓ + n) := by
    intro n x hx
    obtain ⟨a, rfl⟩ := hx
    rw [pbwCoord_apply, map_sum]
    refine Submodule.sum_mem _ fun Y _ => ?_
    rw [map_smul, hjneg]
    have := negOp_smul_mem_level hχl Y.word
    rw [word_sum'] at this
    exact Submodule.smul_mem _ _ this
  have hvl : j u ∈ level N := mem_level_of_L_zero hvs.2.1
  obtain ⟨T, hT⟩ := exists_decomp u
  set u₁ := ∑ M ∈ T.filter (fun M => ℓ + M = N), pbwCoord (c := c) (h := h + ℓ) M (comp M u)
  set u₂ := ∑ M ∈ T.filter (fun M => ¬ ℓ + M = N), pbwCoord (c := c) (h := h + ℓ) M (comp M u)
  have hu : u = u₁ + u₂ := by rw [hT, Finset.sum_filter_add_sum_filter_not]
  have hc2 : comp N (j u₂) = 0 := by
    simp only [u₂, map_sum]
    refine Finset.sum_eq_zero fun M hM => ?_
    exact comp_of_mem_level_ne (Finset.mem_filter.1 hM).2 (hjlev M _ ⟨_, rfl⟩)
  have hl1 : j u₁ ∈ level N := by
    simp only [u₁, map_sum]
    refine Submodule.sum_mem _ fun M hM => ?_
    have := hjlev M _ ⟨comp M u, rfl⟩
    rwa [(Finset.mem_filter.1 hM).2] at this
  have hu2 : u₂ = 0 := by
    apply hinj
    rw [map_zero]
    have e1 : j u = pbwCoord N (comp N (j u)) := (pbwCoord_comp_of_mem_level hvl).symm
    have e2 : j u₁ = pbwCoord N (comp N (j u₁)) := (pbwCoord_comp_of_mem_level hl1).symm
    have : j u = j u₁ := by
      rw [e1, hu, map_add, map_add, hc2, add_zero, ← e2]
    rw [hu, map_add] at this
    exact add_eq_left.1 this
  rw [hu2, add_zero] at hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hvs.1
    rw [h0, map_zero]
  have hle : ℓ ≤ N := by
    by_contra hlt
    apply hu0
    rw [hu]
    refine Finset.sum_eq_zero fun M hM => ?_
    exact absurd (Finset.mem_filter.1 hM).2 (by omega)
  refine ⟨hle, u, hu0, ?_, fun n hn => ?_⟩
  · have hul : u ∈ level (N - ℓ) := by
      rw [hu]
      refine Submodule.sum_mem _ fun M hM => ?_
      have hMN : M = N - ℓ := by have := (Finset.mem_filter.1 hM).2; omega
      rw [hMN]
      exact ⟨_, rfl⟩
    exact L_zero_of_mem_level hul
  · apply hinj
    rw [hjL, hvs.2.2 n hn, map_zero]

/-- There is no singular vector of level `n ≥ 1` where `det G_n ≠ 0`. -/
theorem not_isSingular_of_det_ne {n : ℕ} (hn : 1 ≤ n) (hdet : (gram c h n).det ≠ 0)
    (u : Verma ℂ c h) : ¬ IsSingular u n := by
  intro hu
  obtain ⟨x, hx⟩ := mem_level_of_L_zero hu.2.1
  have hG : (gram c h n).mulVec x = 0 := by
    funext Y
    rw [← shap_neg_pbwCoord, hx, Pi.zero_apply]
    obtain ⟨y, rest, hY⟩ : ∃ y rest, Y.word = y :: rest := by
      cases hw : Y.word with
      | nil =>
        have := word_sum' Y
        rw [hw] at this
        simp at this
        omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    have hy : 0 < y := by
      refine Y.parts_pos ?_
      rw [← Verma.word_coe, hY]
      simp
    rw [hY, neg_cons, shap_neg (by exact_mod_cast hy), hu.2.2 _ (by exact_mod_cast hy), map_zero]
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hG
  apply hu.1
  rw [← hx, this, map_zero]

end Virasoro
