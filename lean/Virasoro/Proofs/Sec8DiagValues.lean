import Virasoro.Proofs.Sec8DiagTop
import Virasoro.Proofs.Sec7ChainValues

/-!
# Lemma 8.7(i) (`lem:diagonal-values`)

(7.10) at a node `a` with `ν = μ`: the terms of the sum over the intermediate points `a + n` vanish
unless `a + n` is a node of layer `L_a + k`.  From a node every label leads to a node of larger
layer (Lemma 8.3(iii)), so the chain functions to a point that is no such node vanish; at a node
`ν` of layer `≠ L_a + k` one of the two factors vanishes at `b⋆` by Lemma 8.5(i).
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

section Dead

variable (hset : MinimalSetting p p' r s b)
include hset

/-- The chain tails from a node `ν` of total level `D` vanish if no node of larger layer has
level `ℓ_ν + D`. -/
theorem chainTail_dead (j : ℕ) : ∀ D : ℕ, ∀ ν : Node,
    (∀ μ : Node, ν.2 < μ.2 → nodeLev p p' r s μ ≠ nodeLev p p' r s ν + D) → ∀ y : Kd⸨X⸩,
    chainTail (bsC b) dvar j D (pt (nodeWt p p' r s ν)) y = 0 := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro ν hno y
  rw [chainTail_eq]
  refine Finset.sum_eq_zero fun g hg => ?_
  rw [mem_labelsAt_node, mem_labels_iff] at hg
  obtain ⟨⟨h1, h2, hl⟩, hw⟩ := hg
  obtain ⟨ν', hlt, hodd, hw'⟩ := node_labels_iii hset ν g (by omega) (by omega) hw
  obtain ⟨hiff, -, -, -⟩ := node_labels_ii hset ν ν' hlt hodd
  have hgeq : g = nodeLabel p p' r s ν ν' := (hiff g (by omega) (by omega)).1 ⟨hw, hw'⟩
  have hlv := lvl_nodeLabel hset hlt hodd
  rw [← hgeq] at hlv
  have hpos : 1 ≤ g.lvl := by unfold Label.lvl; exact Nat.mul_pos (by omega) (by omega)
  have hne : g.lvl ≠ D := by intro h; exact hno ν' hlt (by omega)
  have hpt : pt (nodeWt p p' r s ν) + (g.lvl : Kd) = pt (nodeWt p p' r s ν') := by
    rw [nodeWt_add_lev hset ν', nodeWt_add_lev hset ν]
    simp only [pt, map_add, map_natCast]
    rw [← hlv]
    push_cast
    ring
  rw [if_neg hne, hpt, ih (D - g.lvl) (by omega) ν'
    (fun μ hμ => by have := hno μ (hlt.trans hμ); omega), mul_zero]

/-- The chain functions from a node `ν` of total level `D` vanish if no node of larger layer has
level `ℓ_ν + D`. -/
theorem chainFn_dead (ν : Node) (D k j : ℕ)
    (hno : ∀ μ : Node, ν.2 < μ.2 → nodeLev p p' r s μ ≠ nodeLev p p' r s ν + D) :
    chainFnC b (nodeWt p p' r s ν) D k j = 0 := by
  unfold chainFnC chainFn
  refine Finset.sum_eq_zero fun g hg => ?_
  rw [mem_labelsAt_node, mem_labels_iff] at hg
  obtain ⟨⟨h1, h2, hl⟩, hw⟩ := hg
  obtain ⟨ν', hlt, hodd, hw'⟩ := node_labels_iii hset ν g (by omega) (by omega) hw
  obtain ⟨hiff, -, -, -⟩ := node_labels_ii hset ν ν' hlt hodd
  have hgeq : g = nodeLabel p p' r s ν ν' := (hiff g (by omega) (by omega)).1 ⟨hw, hw'⟩
  have hlv := lvl_nodeLabel hset hlt hodd
  rw [← hgeq] at hlv
  have hpos : 1 ≤ g.lvl := by unfold Label.lvl; exact Nat.mul_pos (by omega) (by omega)
  have hne : g.lvl ≠ D := by intro h; exact hno ν' hlt (by omega)
  have hpt : pt (nodeWt p p' r s ν) + (g.lvl : Kd) = pt (nodeWt p p' r s ν') := by
    rw [nodeWt_add_lev hset ν', nodeWt_add_lev hset ν]
    simp only [pt, map_add, map_natCast]
    rw [← hlv]
    push_cast
    ring
  rw [if_neg hne, hpt, chainTail_dead hset j (D - g.lvl) ν'
    (fun μ hμ => by have := hno μ (hlt.trans hμ); omega), mul_zero]

/-- `c^{(k)}_{a→μ,j}(b⋆) = 0` for `k + j > D(a,μ)` (Lemma 8.5(i)). -/
theorem nodeChain_coeff_zero {a μ : Node} (haμ : a.2 < μ.2) (k j : ℕ) (hk : 1 ≤ k)
    (h : μ.2 - a.2 < k + j) : (nodeChain p p' r s b a μ k j).coeff 0 = 0 := by
  rw [head_bridge hset haμ k j, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun γ hγ => ?_
  exact (chainProd_lead hset hγ k j hk).1.coeff_eq_zero (by omega)

end Dead

/-- Lemma 8.7(i). -/
theorem diag_values_i (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hset : MinimalSetting p p' r s b) {a μ : Node} (haμ : a.2 < μ.2) (k j : ℕ) (hk : 1 ≤ k)
    (hj : 1 ≤ j) (hkj : k + j = μ.2 - a.2) :
    (j : Kd) * (nodeChain p p' r s b a μ k j).coeff 0 =
      (nodeChain p p' r s b a μ (k + 1) (j - 1)).coeff 0 -
        ∑ ε : Bool, nodeTop p p' r s b a (ε, a.2 + k) *
          (nodeChain p p' r s b (ε, a.2 + k) μ 1 (j - 1)).coeff 0 := by
  have hb0 := b_ne_zero_of hset
  have hlev := nodeLev_lt_of_lt hset haμ
  have hcut := (cor_chain_values_of_cited hK hH b hb0).2.1 (nodeWt p p' r s a)
    (nodeLev p p' r s μ - nodeLev p p' r s a) k j (by omega) hk hj
  unfold nodeChain
  rw [hcut]
  congr 1
  have hlk : ∀ ε : Bool, nodeLev p p' r s a < nodeLev p p' r s (ε, a.2 + k) := fun ε =>
    nodeLev_lt_of_lt hset (show a.2 < a.2 + k by omega)
  have hkm : ∀ ε : Bool, nodeLev p p' r s (ε, a.2 + k) < nodeLev p p' r s μ := fun ε =>
    nodeLev_lt_of_lt hset (show a.2 + k < μ.2 by omega)
  have hsub : (Finset.univ : Finset Bool).image
      (fun ε => nodeLev p p' r s (ε, a.2 + k) - nodeLev p p' r s a) ⊆
      Finset.Ioo 0 (nodeLev p p' r s μ - nodeLev p p' r s a) := by
    intro n hn
    obtain ⟨ε, -, rfl⟩ := Finset.mem_image.1 hn
    have h1 := hlk ε
    have h2 := hkm ε
    rw [Finset.mem_Ioo]
    omega
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun ε _ => ?_
      have h1 := hlk ε
      have h2 := hkm ε
      have hw : nodeWt p p' r s a +
          ((nodeLev p p' r s (ε, a.2 + k) - nodeLev p p' r s a : ℕ) : ℂ) =
          nodeWt p p' r s (ε, a.2 + k) := by
        rw [nodeWt_add_lev hset (ε, a.2 + k), nodeWt_add_lev hset a, Nat.cast_sub h1.le]
        ring
      rw [hw, show nodeLev p p' r s μ - nodeLev p p' r s a -
          (nodeLev p p' r s (ε, a.2 + k) - nodeLev p p' r s a) =
          nodeLev p p' r s μ - nodeLev p p' r s (ε, a.2 + k) by omega]
      simp only [nodeTop, nodeChain, Nat.add_sub_cancel_left]
    · intro ε _ ε' _ h
      have h1 := hlk ε
      have h1' := hlk ε'
      have he : nodeLev p p' r s (ε, a.2 + k) = nodeLev p p' r s (ε', a.2 + k) := by
        simp only at h; omega
      have := node_eq_of_lev hset (show 1 ≤ (ε, a.2 + k).2 by show 1 ≤ a.2 + k; omega)
        (show 1 ≤ (ε', a.2 + k).2 by show 1 ≤ a.2 + k; omega) he
      exact (Prod.ext_iff.1 this).1
  · intro n hn hnot
    rw [Finset.mem_Ioo] at hn
    by_cases hex : ∃ ν : Node, a.2 < ν.2 ∧ nodeLev p p' r s ν = nodeLev p p' r s a + n
    · obtain ⟨ν, hν, hνl⟩ := hex
      have hνk : ν.2 ≠ a.2 + k := by
        intro h
        apply hnot
        refine Finset.mem_image.2 ⟨ν.1, Finset.mem_univ _, ?_⟩
        have : ((ν.1, a.2 + k) : Node) = ν := Prod.ext rfl h.symm
        rw [this]
        omega
      rcases lt_or_gt_of_ne hνk with h1 | h1
      · have hz := nodeChain_coeff_zero hset hν k 0 hk (by omega)
        unfold nodeChain at hz
        rw [show nodeLev p p' r s ν - nodeLev p p' r s a = n by omega] at hz
        rw [hz, zero_mul]
      · have hw : nodeWt p p' r s a + (n : ℂ) = nodeWt p p' r s ν := by
          rw [nodeWt_add_lev hset ν, nodeWt_add_lev hset a, hνl]
          push_cast
          ring
        rw [hw]
        have hz : (chainFnC b (nodeWt p p' r s ν)
            (nodeLev p p' r s μ - nodeLev p p' r s a - n) 1 (j - 1)).coeff 0 = 0 := by
          rcases Nat.lt_or_ge ν.2 μ.2 with h2 | h2
          · have hz := nodeChain_coeff_zero hset h2 1 (j - 1) le_rfl (by omega)
            unfold nodeChain at hz
            rwa [show nodeLev p p' r s μ - nodeLev p p' r s ν =
              nodeLev p p' r s μ - nodeLev p p' r s a - n by omega] at hz
          · rw [chainFn_dead hset ν _ 1 (j - 1) ?_, HahnSeries.coeff_zero]
            intro μ' hμ' heq
            have := nodeLev_lt_of_lt hset (show μ.2 < μ'.2 by omega)
            omega
        rw [hz, mul_zero]
    · push_neg at hex
      rw [chainFn_dead hset a n k 0 (fun μ' hμ' => hex μ' hμ'), HahnSeries.coeff_zero, zero_mul]

end Virasoro
