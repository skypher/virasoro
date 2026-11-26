import Virasoro.Proofs.Sec8DiagBridgeAux

/-!
# Lemma 8.3(iii), last assertion: `c^{(k)}_{a→μ,j}` is the sum over the node chains

The labels of weight `ν` and level at most `ℓ_μ - ℓ_ν` are the labels `nodeLabel ν θ`,
`θ ∈ FS(ν → μ)`, and labels to the other node `ν'` of the layer of `μ` (`ℓ_{ν'} < ℓ_μ`), from which
no chain continues to `μ`.  Strong induction on the remaining level.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

theorem mem_labels_iff {D : ℕ} {g : Label} :
    g ∈ labels D ↔ 1 ≤ g.1 ∧ 1 ≤ g.2 ∧ g.lvl ≤ D := by
  unfold labels Label.lvl
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h3⟩
    · calc g.1 ≤ g.1 * g.2 := Nat.le_mul_of_pos_right _ h2
        _ ≤ D := h3
    · calc g.2 ≤ g.1 * g.2 := Nat.le_mul_of_pos_left _ h1
        _ ≤ D := h3

theorem firstSteps_props {ν μ θ : Node} (hθ : θ ∈ firstSteps ν μ) :
    ν.2 < θ.2 ∧ (θ.2 - ν.2) % 2 = 1 := by
  rcases mem_firstSteps.1 hθ with ⟨h1, -, h3⟩ | ⟨ho, rfl⟩
  · exact ⟨h1, h3⟩
  · exact ⟨by omega, ho⟩

section Reindex

variable (hset : MinimalSetting p p' r s b) {ν μ : Node}
  (hlev : nodeLev p p' r s ν < nodeLev p p' r s μ)
include hset hlev

/-- The labels `nodeLabel ν θ`, `θ ∈ FS(ν → μ)`, have weight `ν` and level `≤ ℓ_μ - ℓ_ν`. -/
theorem nodeLabel_mem {θ : Node} (hθ : θ ∈ firstSteps ν μ) :
    nodeLabel p p' r s ν θ ∈
      labelsAt (bsC b) (nodeLev p p' r s μ - nodeLev p p' r s ν) (pt (nodeWt p p' r s ν)) := by
  have hθ' := mem_firstSteps.1 hθ
  have hlt : ν.2 < θ.2 := by rcases hθ' with ⟨h, -, -⟩ | ⟨ho, rfl⟩ <;> omega
  have hodd : (θ.2 - ν.2) % 2 = 1 := by rcases hθ' with ⟨-, -, h⟩ | ⟨ho, rfl⟩ <;> assumption
  obtain ⟨hiff, h1, h2, -⟩ := node_labels_ii hset ν θ hlt hodd
  have hl := lvl_nodeLabel hset hlt hodd
  have hle : nodeLev p p' r s θ ≤ nodeLev p p' r s μ := by
    rcases hθ' with ⟨-, h, -⟩ | ⟨-, rfl⟩
    · exact (nodeLev_lt_of_lt hset h).le
    · exact le_rfl
  rw [mem_labelsAt_node, mem_labels_iff]
  exact ⟨⟨h1, h2, by omega⟩, ((hiff _ h1 h2).2 rfl).1⟩

theorem nodeLabel_injOn : Set.InjOn (nodeLabel p p' r s ν) (firstSteps ν μ) := by
  intro θ hθ θ' hθ' h
  obtain ⟨hlt, hodd⟩ := firstSteps_props hθ
  obtain ⟨hlt', hodd'⟩ := firstSteps_props hθ'
  have e1 := lvl_nodeLabel hset hlt hodd
  have e2 := lvl_nodeLabel hset hlt' hodd'
  rw [h] at e1
  exact node_eq_of_lev hset (by omega) (by omega) (by omega)

/-- A label of weight `ν` and level `≤ ℓ_μ - ℓ_ν` that is not `nodeLabel ν θ` for a first step
`θ` leads to the other node `ν'` of the layer of `μ`, with `ℓ_{ν'} < ℓ_μ`. -/
theorem dead_label {g : Label}
    (hg : g ∈ labelsAt (bsC b) (nodeLev p p' r s μ - nodeLev p p' r s ν) (pt (nodeWt p p' r s ν)))
    (hnot : ∀ θ ∈ firstSteps ν μ, g ≠ nodeLabel p p' r s ν θ) :
    ∃ ν' : Node, ν'.2 = μ.2 ∧ nodeLev p p' r s ν' < nodeLev p p' r s μ ∧
      g.lvl + nodeLev p p' r s ν = nodeLev p p' r s ν' ∧ 1 ≤ g.lvl ∧
      pt (nodeWt p p' r s ν) + (g.lvl : Kd) = pt (nodeWt p p' r s ν') := by
  rw [mem_labelsAt_node, mem_labels_iff] at hg
  obtain ⟨⟨h1, h2, hl⟩, hw⟩ := hg
  obtain ⟨ν', hlt, hodd, hw'⟩ := node_labels_iii hset ν g (by omega) (by omega) hw
  obtain ⟨hiff, -, -, -⟩ := node_labels_ii hset ν ν' hlt hodd
  have hgeq : g = nodeLabel p p' r s ν ν' := (hiff g (by omega) (by omega)).1 ⟨hw, hw'⟩
  have hlv := lvl_nodeLabel hset hlt hodd
  rw [← hgeq] at hlv
  have hle : nodeLev p p' r s ν' ≤ nodeLev p p' r s μ := by omega
  have hν'μ : ν'.2 ≤ μ.2 := by
    by_contra h
    push_neg at h
    have := nodeLev_lt_of_lt hset h
    omega
  have hnotFS : ν' ∉ firstSteps ν μ := fun h => hnot ν' h hgeq
  rw [mem_firstSteps] at hnotFS
  push_neg at hnotFS
  have heq : ν'.2 = μ.2 := by
    rcases Nat.lt_or_ge ν'.2 μ.2 with h | h
    · exact absurd hodd (hnotFS.1 hlt h)
    · omega
  have hne : ν' ≠ μ := fun h => hnotFS.2 (by rw [← heq]; exact hodd) h
  have hlvne : nodeLev p p' r s ν' ≠ nodeLev p p' r s μ := fun h =>
    hne (node_eq_of_lev hset (by omega) (by omega) h)
  have hpos : 1 ≤ g.lvl := by unfold Label.lvl; exact Nat.mul_pos (by omega) (by omega)
  refine ⟨ν', heq, lt_of_le_of_ne hle hlvne, hlv, hpos, ?_⟩
  rw [nodeWt_add_lev hset ν', nodeWt_add_lev hset ν]
  simp only [pt, map_add, map_natCast]
  rw [← hlv]
  push_cast
  ring

end Reindex

/-- The tail: `chainTail` from a node `ν` with `ℓ_ν < ℓ_μ` is the sum over the node chains. -/
theorem tail_bridge (hset : MinimalSetting p p' r s b) (μ : Node) (j : ℕ) :
    ∀ D : ℕ, ∀ ν : Node, nodeLev p p' r s ν < nodeLev p p' r s μ →
      D = nodeLev p p' r s μ - nodeLev p p' r s ν → ∀ y : Kd⸨X⸩,
      chainTail (bsC b) dvar j D (pt (nodeWt p p' r s ν)) y =
        ∑ γ ∈ nodeChains ν μ, chainTailProd p p' r s b j y ν γ.tail := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro ν hlev hD y
  subst hD
  rw [chainTail_eq]
  set D := nodeLev p p' r s μ - nodeLev p p' r s ν with hDdef
  -- reduce to the first steps
  have hsub : (firstSteps ν μ).image (nodeLabel p p' r s ν) ⊆
      labelsAt (bsC b) D (pt (nodeWt p p' r s ν)) := by
    intro g hg
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hg
    exact nodeLabel_mem hset hlev hθ
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image (nodeLabel_injOn hset hlev)]
  swap
  · intro g hg hgn
    have hnot : ∀ θ ∈ firstSteps ν μ, g ≠ nodeLabel p p' r s ν θ := fun θ hθ h =>
      hgn (Finset.mem_image.2 ⟨θ, hθ, h.symm⟩)
    obtain ⟨ν', heq, hlt', hlv, hpos, hpt⟩ := dead_label hset hlev hg hnot
    have hne : g.lvl ≠ D := by omega
    rw [if_neg hne, hpt, ih (D - g.lvl) (by omega) ν' hlt' (by omega),
      nodeChains_of_le (by omega), Finset.sum_empty, mul_zero]
  -- the first steps against the chains
  rcases Nat.lt_or_ge ν.2 μ.2 with hνμ | hνμ
  · rw [nodeChains_of_lt hνμ]
    rw [Finset.sum_union ?_]
    swap
    · rw [Finset.disjoint_left]
      intro γ h1 h2
      split_ifs at h1
      · rw [Finset.mem_singleton.1 h1] at h2
        obtain ⟨θ, -, h3⟩ := Finset.mem_biUnion.1 h2
        obtain ⟨γ', hγ', h4⟩ := Finset.mem_image.1 h3
        obtain ⟨x, l, rfl⟩ := nodeChains_head hγ'
        simp only [List.cons.injEq] at h4
        obtain ⟨-, h5, h6⟩ := h4
        exact absurd h6 (List.cons_ne_nil _ _)
      · simp at h1
    rw [Finset.sum_biUnion ?_]
    swap
    · intro θ _ θ' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro γ h1 h2
      obtain ⟨γ1, hγ1, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨γ2, hγ2, h3⟩ := Finset.mem_image.1 h2
      obtain ⟨x1, l1, rfl⟩ := nodeChains_head hγ1
      obtain ⟨x2, l2, rfl⟩ := nodeChains_head hγ2
      simp only [List.cons.injEq] at h3
      exact hne (Subtype.ext h3.2.1).symm
    -- split FS into μ and the rest
    have hsplit := Finset.sum_filter_add_sum_filter_not (firstSteps ν μ) (· ≠ μ)
      (fun θ => RG (bsC b) dvar (nodeLabel p p' r s ν θ) / (y - delG (bsC b) (nodeLabel p p' r s ν θ)) *
        (if (nodeLabel p p' r s ν θ).lvl = D then
          delG (bsC b) (nodeLabel p p' r s ν θ) ^ j / (j.factorial : Kd⸨X⸩)
        else chainTail (bsC b) dvar j (D - (nodeLabel p p' r s ν θ).lvl)
          (pt (nodeWt p p' r s ν) + ((nodeLabel p p' r s ν θ).lvl : Kd))
          (delG (bsC b) (nodeLabel p p' r s ν θ))))
    rw [← hsplit, add_comm]
    congr 1
    · -- θ = μ
      have hfilt : (firstSteps ν μ).filter (fun θ => ¬ θ ≠ μ) =
          if (μ.2 - ν.2) % 2 = 1 then {μ} else ∅ := by
        ext θ
        simp only [Finset.mem_filter, not_not, mem_firstSteps]
        split_ifs with ho
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨-, h⟩; exact h
          · rintro rfl; exact ⟨Or.inr ⟨ho, rfl⟩, rfl⟩
        · simp only [Finset.notMem_empty, iff_false]
          rintro ⟨h | h, rfl⟩
          · omega
          · exact ho h.1
      rw [hfilt]
      split_ifs with ho
      · rw [Finset.sum_singleton, Finset.sum_singleton]
        have hl := lvl_nodeLabel hset hνμ ho
        rw [if_pos (by omega)]
        simp [chainTailProd, nodeR, nodeDel]
      · simp
    · -- θ ≠ μ
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl fun θ _ => ?_
      have hθ := (Finset.mem_filter.1 θ.2)
      have hθ' := mem_firstSteps.1 hθ.1
      have hlt : ν.2 < θ.1.2 := by rcases hθ' with ⟨h, -, -⟩ | ⟨-, h⟩ <;> [omega; exact absurd h hθ.2]
      have hθμ : θ.1.2 < μ.2 := by rcases hθ' with ⟨-, h, -⟩ | ⟨-, h⟩ <;> [exact h; exact absurd h hθ.2]
      have hodd : (θ.1.2 - ν.2) % 2 = 1 := by
        rcases hθ' with ⟨-, -, h⟩ | ⟨-, h⟩ <;> [exact h; exact absurd h hθ.2]
      have hl := lvl_nodeLabel hset hlt hodd
      have hlθ := nodeLev_lt_of_lt hset hθμ
      have hlν := nodeLev_lt_of_lt hset hlt
      have hne : (nodeLabel p p' r s ν θ.1).lvl ≠ D := by omega
      have hpt : pt (nodeWt p p' r s ν) + ((nodeLabel p p' r s ν θ.1).lvl : Kd) =
          pt (nodeWt p p' r s θ.1) := by
        rw [nodeWt_add_lev hset θ.1, nodeWt_add_lev hset ν]
        simp only [pt, map_add, map_natCast]
        rw [← hl]
        push_cast
        ring
      rw [if_neg hne, hpt, ih _ (by omega) θ.1 hlθ (by omega), Finset.sum_image, Finset.mul_sum]
      · refine Finset.sum_congr rfl fun γ' hγ' => ?_
        obtain ⟨x, l, rfl⟩ := nodeChains_head hγ'
        simp [chainTailProd, nodeR, nodeDel]
      · intro γ1 _ γ2 _ h
        exact List.cons_injective h
  · rw [nodeChains_of_le hνμ, Finset.sum_empty]
    refine Finset.sum_eq_zero fun θ hθ => ?_
    exfalso
    rcases mem_firstSteps.1 hθ with ⟨h1, h2, -⟩ | ⟨ho, rfl⟩
    · omega
    · omega

/-- The head: `c^{(k)}_{a→μ,j} = ∑_{γ ∈ nodeChains a μ} P^{(k)}_γ δ_{g_n}^j/j!` (Lemma 8.3(iii)). -/
theorem head_bridge (hset : MinimalSetting p p' r s b) {a μ : Node} (haμ : a.2 < μ.2) (k j : ℕ) :
    nodeChain p p' r s b a μ k j = ∑ γ ∈ nodeChains a μ, chainProd p p' r s b k j γ := by
  have hlev := nodeLev_lt_of_lt hset haμ
  unfold nodeChain chainFnC chainFn
  set D := nodeLev p p' r s μ - nodeLev p p' r s a with hDdef
  have hsub : (firstSteps a μ).image (nodeLabel p p' r s a) ⊆
      labelsAt (bsC b) D (pt (nodeWt p p' r s a)) := by
    intro g hg
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hg
    exact nodeLabel_mem hset hlev hθ
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image (nodeLabel_injOn hset hlev)]
  swap
  · intro g hg hgn
    have hnot : ∀ θ ∈ firstSteps a μ, g ≠ nodeLabel p p' r s a θ := fun θ hθ h =>
      hgn (Finset.mem_image.2 ⟨θ, hθ, h.symm⟩)
    obtain ⟨ν', heq, hlt', hlv, hpos, hpt⟩ := dead_label hset hlev hg hnot
    have hne : g.lvl ≠ D := by omega
    rw [if_neg hne, hpt, tail_bridge hset μ j (D - g.lvl) ν' hlt' (by omega),
      nodeChains_of_le (by omega), Finset.sum_empty, mul_zero]
  rw [nodeChains_of_lt haμ]
  rw [Finset.sum_union ?_]
  swap
  · rw [Finset.disjoint_left]
    intro γ h1 h2
    split_ifs at h1
    · rw [Finset.mem_singleton.1 h1] at h2
      obtain ⟨θ, -, h3⟩ := Finset.mem_biUnion.1 h2
      obtain ⟨γ', hγ', h4⟩ := Finset.mem_image.1 h3
      obtain ⟨x, l, rfl⟩ := nodeChains_head hγ'
      simp only [List.cons.injEq] at h4
      obtain ⟨-, h5, h6⟩ := h4
      exact absurd h6 (List.cons_ne_nil _ _)
    · simp at h1
  rw [Finset.sum_biUnion ?_]
  swap
  · intro θ _ θ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro γ h1 h2
    obtain ⟨γ1, hγ1, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨γ2, hγ2, h3⟩ := Finset.mem_image.1 h2
    obtain ⟨x1, l1, rfl⟩ := nodeChains_head hγ1
    obtain ⟨x2, l2, rfl⟩ := nodeChains_head hγ2
    simp only [List.cons.injEq] at h3
    exact hne (Subtype.ext h3.2.1).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (firstSteps a μ) (· ≠ μ)
    (fun θ => RG (bsC b) dvar (nodeLabel p p' r s a θ) *
      delG (bsC b) (nodeLabel p p' r s a θ) ^ (k - 1) *
      (if (nodeLabel p p' r s a θ).lvl = D then
        delG (bsC b) (nodeLabel p p' r s a θ) ^ j / (j.factorial : Kd⸨X⸩)
      else chainTail (bsC b) dvar j (D - (nodeLabel p p' r s a θ).lvl)
        (pt (nodeWt p p' r s a) + ((nodeLabel p p' r s a θ).lvl : Kd))
        (delG (bsC b) (nodeLabel p p' r s a θ))))
  rw [← hsplit, add_comm]
  congr 1
  · have hfilt : (firstSteps a μ).filter (fun θ => ¬ θ ≠ μ) =
        if (μ.2 - a.2) % 2 = 1 then {μ} else ∅ := by
      ext θ
      simp only [Finset.mem_filter, not_not, mem_firstSteps]
      split_ifs with ho
      · simp only [Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; exact h
        · rintro rfl; exact ⟨Or.inr ⟨ho, rfl⟩, rfl⟩
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨h | h, rfl⟩
        · omega
        · exact ho h.1
    rw [hfilt]
    split_ifs with ho
    · rw [Finset.sum_singleton, Finset.sum_singleton]
      have hl := lvl_nodeLabel hset haμ ho
      rw [if_pos (by omega)]
      simp [chainProd, chainTailProd, nodeR, nodeDel]
    · simp
  · rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun θ _ => ?_
    have hθ := (Finset.mem_filter.1 θ.2)
    have hθ' := mem_firstSteps.1 hθ.1
    obtain ⟨hlt, hodd⟩ := firstSteps_props hθ.1
    have hθμ : θ.1.2 < μ.2 := by
      rcases hθ' with ⟨-, h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hθ.2
    have hl := lvl_nodeLabel hset hlt hodd
    have hlθ := nodeLev_lt_of_lt hset hθμ
    have hlν := nodeLev_lt_of_lt hset hlt
    have hne : (nodeLabel p p' r s a θ.1).lvl ≠ D := by omega
    have hpt : pt (nodeWt p p' r s a) + ((nodeLabel p p' r s a θ.1).lvl : Kd) =
        pt (nodeWt p p' r s θ.1) := by
      rw [nodeWt_add_lev hset θ.1, nodeWt_add_lev hset a]
      simp only [pt, map_add, map_natCast]
      rw [← hl]
      push_cast
      ring
    rw [if_neg hne, hpt, tail_bridge hset μ j _ θ.1 hlθ (by omega), Finset.sum_image,
      Finset.mul_sum]
    · refine Finset.sum_congr rfl fun γ' hγ' => ?_
      obtain ⟨x, l, rfl⟩ := nodeChains_head hγ'
      simp [chainProd, chainTailProd, nodeR, nodeDel]
    · intro γ1 _ γ2 _ h
      exact List.cons_injective h

/-- Lemma 8.3 (`lem:node-labels`).
Paper label: lem:node-labels -/
theorem lem_node_labels : Stmt_lem_node_labels := by
  intro p p' r s b hset
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  refine ⟨fun g _ _ => node_slope hp hp' hset.2.2.2.2.2.2.2.2 g,
    fun ν ν' hlt hodd => node_labels_ii hset ν ν' hlt hodd,
    fun ν g h1 h2 hw => node_labels_iii hset ν g h1 h2 hw,
    fun a μ k j haμ _ => head_bridge hset haμ k j⟩

end Virasoro
