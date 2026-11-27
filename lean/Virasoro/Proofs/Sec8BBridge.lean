import Virasoro.Proofs.Sec8BLabels3
import Virasoro.Proofs.Sec8DiagBridge

/-!
# Section 8.2: the chains between boundary nodes

By Lemma 8.10 the labels of weight `μ_i` and level at most `ℓ_k - ℓ_i` are the labels to `μ_m`,
`i < m ≤ k`, one each; so `c^{(k')}_{μ_i→μ_k,j}` is the sum over the increasing sequences of
layers from `i` to `k` (strong induction on the remaining level, as for Lemma 8.3(iii)).
-/

namespace Virasoro

open scoped LaurentSeries

/-- The chains from `μ_i` to `μ_k`: increasing lists of layers `[i, x₁, …, k]`. -/
def bChains (i k : ℕ) : Finset (List ℕ) :=
  if i < k then
    {[i, k]} ∪ (Finset.Ioo i k).attach.biUnion fun θ => (bChains θ.1 k).image (i :: ·)
  else ∅
termination_by k - i
decreasing_by have := Finset.mem_Ioo.1 θ.2; omega

section Defs

variable (p p' x₀ : ℕ) (b : ℂ)

/-- The germ `δ_g` of the label from `μ_i` to `μ_m`. -/
noncomputable def bDel (i m : ℕ) : Kd⸨X⸩ := delG (bsC b) (bLabel p p' x₀ i m)

/-- `∏ R_{g}/(δ_{prev} - δ_g) · δ_{last}^j/j!` along the tail of a chain. -/
noncomputable def bTailProd (j : ℕ) : Kd⸨X⸩ → ℕ → List ℕ → Kd⸨X⸩
  | y, _, [] => y ^ j / (j.factorial : Kd⸨X⸩)
  | y, ν, ν' :: l => bR p p' x₀ b ν ν' / (y - bDel p p' x₀ b ν ν') *
      bTailProd j (bDel p p' x₀ b ν ν') ν' l

/-- `P^{(k')}_γ δ_{g_n}^j/j!` for a chain `γ = [y₀, y₁, …]`. -/
noncomputable def bProd (k' j : ℕ) : List ℕ → Kd⸨X⸩
  | y₀ :: y₁ :: l => bR p p' x₀ b y₀ y₁ * bDel p p' x₀ b y₀ y₁ ^ (k' - 1) *
      bTailProd p p' x₀ b j (bDel p p' x₀ b y₀ y₁) y₁ l
  | _ => 0

end Defs

theorem bChains_of_lt {i k : ℕ} (h : i < k) :
    bChains i k = {[i, k]} ∪ (Finset.Ioo i k).attach.biUnion fun θ =>
      (bChains θ.1 k).image (i :: ·) := by
  rw [bChains]; simp [h]

theorem bChains_of_le {i k : ℕ} (h : k ≤ i) : bChains i k = ∅ := by
  rw [bChains]; simp [show ¬ i < k by omega]

theorem bChains_head {i k : ℕ} {γ : List ℕ} (hγ : γ ∈ bChains i k) : ∃ x l, γ = i :: x :: l := by
  rcases Nat.lt_or_ge i k with h | h
  · rw [bChains_of_lt h] at hγ
    rcases Finset.mem_union.1 hγ with h1 | h1
    · rw [Finset.mem_singleton.1 h1]; exact ⟨k, [], rfl⟩
    · obtain ⟨θ, -, h2⟩ := Finset.mem_biUnion.1 h1
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h2
      obtain ⟨x, l, rfl⟩ := bChains_head hγ'
      exact ⟨θ.1, x :: l, rfl⟩
  · rw [bChains_of_le h] at hγ; simp at hγ
termination_by k - i
decreasing_by have := Finset.mem_Ioo.1 θ.2; omega

variable {p p' x₀ : ℕ} {b : ℂ}

section Bridge

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem lvl_bLabel {i m : ℕ} (him : i < m) :
    (bLabel p p' x₀ i m).lvl + bLev p p' x₀ i = bLev p p' x₀ m := by
  obtain ⟨h1, h2, -, -⟩ := bLabel_xy hB him
  obtain ⟨hw, hw'⟩ := (label_iff hB him _ h1 h2).2 rfl
  rw [hw, bWt_add_lev hB m, bWt_add_lev hB i] at hw'
  have : ((bLabel p p' x₀ i m).lvl : ℂ) + bLev p p' x₀ i = bLev p p' x₀ m := by
    linear_combination hw'
  exact_mod_cast this

/-- The labels of weight `μ_i` and level at most `ℓ_k - ℓ_i` are the labels to `μ_m`, `i < m ≤ k`. -/
theorem labelsAt_b {i k : ℕ} :
    labelsAt (bsC b) (bLev p p' x₀ k - bLev p p' x₀ i) (pt (bWt p p' x₀ i)) =
      (Finset.Ioc i k).image (bLabel p p' x₀ i) := by
  ext g
  rw [mem_labelsAt_node, mem_labels_iff, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2, hl⟩, hw⟩
    have hpos : 1 ≤ g.lvl := by unfold Label.lvl; exact Nat.mul_pos (by omega) (by omega)
    obtain ⟨m, him, hw'⟩ := label_leads hB i g (by omega) (by omega) hw
    have hg := (label_iff hB him g (by omega) (by omega)).1 ⟨hw, hw'⟩
    have hlv := lvl_bLabel hB him
    rw [← hg] at hlv
    have hmk : m ≤ k := by
      by_contra hc
      have := bLev_strictMono hB (show k < m by omega)
      omega
    exact ⟨m, Finset.mem_Ioc.2 ⟨him, hmk⟩, hg.symm⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨him, hmk⟩ := Finset.mem_Ioc.1 hm
    obtain ⟨h1, h2, -, -⟩ := bLabel_xy hB him
    obtain ⟨hw, -⟩ := (label_iff hB him _ h1 h2).2 rfl
    have hlv := lvl_bLabel hB him
    have hle : bLev p p' x₀ m ≤ bLev p p' x₀ k := (bLev_strictMono hB).monotone hmk
    exact ⟨⟨h1, h2, by omega⟩, hw⟩

theorem bLabel_injOn (i : ℕ) : Set.InjOn (bLabel p p' x₀ i) (Set.Ioi i) := by
  intro m hm m' hm' h
  have h1 := lvl_bLabel hB (Set.mem_Ioi.1 hm)
  have h2 := lvl_bLabel hB (Set.mem_Ioi.1 hm')
  rw [h] at h1
  exact (bLev_strictMono hB).injective (by omega)

theorem pt_bWt_add {i m : ℕ} (him : i < m) :
    pt (bWt p p' x₀ i) + ((bLabel p p' x₀ i m).lvl : Kd) = pt (bWt p p' x₀ m) := by
  have hl := lvl_bLabel hB him
  rw [bWt_add_lev hB m, bWt_add_lev hB i]
  simp only [pt, map_add, map_natCast]
  rw [← hl]
  push_cast
  ring

/-- The tail: `chainTail` from `μ_ν` with `ν < k` is the sum over the chains from `ν` to `k`. -/
theorem b_tail_bridge (k j : ℕ) : ∀ D : ℕ, ∀ ν : ℕ, ν < k →
    D = bLev p p' x₀ k - bLev p p' x₀ ν → ∀ y : Kd⸨X⸩,
    chainTail (bsC b) dvar j D (pt (bWt p p' x₀ ν)) y =
      ∑ γ ∈ bChains ν k, bTailProd p p' x₀ b j y ν γ.tail := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro ν hνk hD y
  subst hD
  rw [chainTail_eq, labelsAt_b hB,
    Finset.sum_image (fun m hm m' hm' h => bLabel_injOn hB ν
      (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hm).1) (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hm').1) h),
    ← Finset.Ioo_insert_right hνk, Finset.sum_insert (by simp), bChains_of_lt hνk,
    Finset.sum_union ?_, Finset.sum_biUnion ?_, Finset.sum_singleton]
  · have hl := lvl_bLabel hB hνk
    rw [if_pos (by omega)]
    congr 1
    rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun θ _ => ?_
    obtain ⟨hθ1, hθ2⟩ := Finset.mem_Ioo.1 θ.2
    have hlθ := lvl_bLabel hB hθ1
    have hlk := bLev_strictMono hB hθ2
    have hlν := bLev_strictMono hB hθ1
    rw [if_neg (by omega), pt_bWt_add hB hθ1, ih _ (by omega) θ.1 hθ2 (by omega),
      Finset.sum_image (fun γ1 _ γ2 _ h => List.cons_injective h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ' hγ' => ?_
    obtain ⟨x, l, rfl⟩ := bChains_head hγ'
    simp [bTailProd, bR, bDel]
  · intro θ _ θ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro γ h1 h2
    obtain ⟨γ1, hγ1, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨γ2, hγ2, h3⟩ := Finset.mem_image.1 h2
    obtain ⟨x1, l1, rfl⟩ := bChains_head hγ1
    obtain ⟨x2, l2, rfl⟩ := bChains_head hγ2
    simp only [List.cons.injEq] at h3
    exact hne (Subtype.ext h3.2.1).symm
  · rw [Finset.disjoint_left]
    intro γ h1 h2
    rw [Finset.mem_singleton.1 h1] at h2
    obtain ⟨θ, -, h3⟩ := Finset.mem_biUnion.1 h2
    obtain ⟨γ', hγ', h4⟩ := Finset.mem_image.1 h3
    obtain ⟨x, l, rfl⟩ := bChains_head hγ'
    simp only [List.cons.injEq] at h4
    exact absurd h4.2.2 (List.cons_ne_nil _ _)

/-- The head: `c^{(k')}_{μ_i→μ_k,j} = ∑_γ P^{(k')}_γ δ_{g_n}^j/j!`. -/
theorem b_head_bridge {i k : ℕ} (hik : i < k) (k' j : ℕ) :
    bChain p p' x₀ b i k k' j = ∑ γ ∈ bChains i k, bProd p p' x₀ b k' j γ := by
  unfold bChain chainFnC chainFn
  rw [labelsAt_b hB,
    Finset.sum_image (fun m hm m' hm' h => bLabel_injOn hB i
      (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hm).1) (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hm').1) h),
    ← Finset.Ioo_insert_right hik, Finset.sum_insert (by simp), bChains_of_lt hik,
    Finset.sum_union ?_, Finset.sum_biUnion ?_, Finset.sum_singleton]
  · have hl := lvl_bLabel hB hik
    rw [if_pos (by omega)]
    congr 1
    rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun θ _ => ?_
    obtain ⟨hθ1, hθ2⟩ := Finset.mem_Ioo.1 θ.2
    have hlθ := lvl_bLabel hB hθ1
    have hlk := bLev_strictMono hB hθ2
    have hlν := bLev_strictMono hB hθ1
    rw [if_neg (by omega), pt_bWt_add hB hθ1, b_tail_bridge hB k j _ θ.1 hθ2 (by omega),
      Finset.sum_image (fun γ1 _ γ2 _ h => List.cons_injective h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ' hγ' => ?_
    obtain ⟨x, l, rfl⟩ := bChains_head hγ'
    simp [bProd, bTailProd, bR, bDel]
  · intro θ _ θ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro γ h1 h2
    obtain ⟨γ1, hγ1, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨γ2, hγ2, h3⟩ := Finset.mem_image.1 h2
    obtain ⟨x1, l1, rfl⟩ := bChains_head hγ1
    obtain ⟨x2, l2, rfl⟩ := bChains_head hγ2
    simp only [List.cons.injEq] at h3
    exact hne (Subtype.ext h3.2.1).symm
  · rw [Finset.disjoint_left]
    intro γ h1 h2
    rw [Finset.mem_singleton.1 h1] at h2
    obtain ⟨θ, -, h3⟩ := Finset.mem_biUnion.1 h2
    obtain ⟨γ', hγ', h4⟩ := Finset.mem_image.1 h3
    obtain ⟨x, l, rfl⟩ := bChains_head hγ'
    simp only [List.cons.injEq] at h4
    exact absurd h4.2.2 (List.cons_ne_nil _ _)

end Bridge

end Virasoro
