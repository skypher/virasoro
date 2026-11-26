import Virasoro.Proofs.Sec8DiagLabels3
import Virasoro.Proofs.Sec7ChainValues
import Virasoro.Proofs.P2Sec11VertexStep
import Virasoro.Proofs.P2Sec11VertexZero
import Virasoro.Proofs.P2Sec9GenRC4
import Virasoro.Proofs.P2Sec9GenRC2

/-!
# Section 8.1: levels of the nodes and the shape of the node chains

`μ^ε_k = λ + ℓ^ε_k`; levels increase strictly with the layer and determine the node; the label
from `ν` to `θ` has level `ℓ_θ - ℓ_ν`; node chains from `a` start with `a`.
-/

namespace Virasoro

variable {p p' r s : ℕ} {b : ℂ}

theorem mem_labelsAt_node {D : ℕ} {w : ℂ} {g : Label} :
    g ∈ labelsAt (bsC b) D (pt w) ↔ g ∈ labels D ∧ kacHL g b = w := by
  rw [mem_labelsAt]
  simp only [bsC, pt, kacHL_ratC]
  exact and_congr_right fun _ => (RatFunc.C : ℂ →+* Kd).injective.eq_iff

theorem nodeWt_add_lev (hset : MinimalSetting p p' r s b) (ν : Node) :
    nodeWt p p' r s ν = nodeWt p p' r s (true, 0) + (nodeLev p p' r s ν : ℂ) := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have h4 := four_ellOrb (p := p) (p' := p') (r := r) (s := s) hset.2.2.2.2.1
    hset.2.2.2.2.2.2.1 ν.1 ν.2
  have h4c : 4 * (p : ℂ) * p' * (ellOrb p p' r s ν.1 ν.2 : ℂ) =
      ((nOrb p p' r s ν.1 ν.2 : ℤ) : ℂ) ^ 2 - ((((p' : ℤ) * r - p * s) : ℤ) : ℂ) ^ 2 := by
    exact_mod_cast h4
  unfold nodeWt muOrb momWt nodeLev
  have h0 : nOrb p p' r s true 0 = (p' : ℤ) * r - p * s := by simp [nOrb]
  rw [h0]
  have h4ne : (4 : ℂ) * p * p' ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpc) hpc'
  rw [div_add' _ _ _ h4ne]
  congr 1
  linear_combination (-1 : ℂ) * h4c

theorem nodeLev_lt_of_lt (hset : MinimalSetting p p' r s b) {ν ν' : Node} (h : ν.2 < ν'.2) :
    nodeLev p p' r s ν < nodeLev p p' r s ν' := by
  obtain ⟨hp2, hp2', -, hr0, hr, hs0, hs, -, -⟩ := hset
  have := ellOrb_lt_add (p := p) (p' := p') (r := r) (s := s) (by omega) (by omega) hr0 hr hs0 hs
    ν.1 ν.2 (ν'.2 - ν.2) (by omega) ν'.1
  rw [show ν.2 + (ν'.2 - ν.2) = ν'.2 by omega] at this
  exact this

theorem node_eq_of_lev (hset : MinimalSetting p p' r s b) {ν ν' : Node} (h1 : 1 ≤ ν.2)
    (h1' : 1 ≤ ν'.2) (h : nodeLev p p' r s ν = nodeLev p p' r s ν') : ν = ν' := by
  obtain ⟨he, hk⟩ := P2.ellOrb_inj hset h1 h1' h
  exact Prod.ext he hk

theorem nodeLev_zero (ε : Bool) : nodeLev p p' r s (ε, 0) = 0 := P2.ellOrb_zero' p p' r s ε

/-- The level of the label from `ν` to `θ` is `ℓ_θ - ℓ_ν`. -/
theorem lvl_nodeLabel (hset : MinimalSetting p p' r s b) {ν θ : Node} (hlt : ν.2 < θ.2)
    (hodd : (θ.2 - ν.2) % 2 = 1) :
    (nodeLabel p p' r s ν θ).lvl + nodeLev p p' r s ν = nodeLev p p' r s θ := by
  obtain ⟨hiff, h1, h2, -⟩ := node_labels_ii hset ν θ hlt hodd
  obtain ⟨hw, hw'⟩ := (hiff _ h1 h2).2 rfl
  rw [hw, nodeWt_add_lev hset ν, nodeWt_add_lev hset θ] at hw'
  have : ((nodeLabel p p' r s ν θ).lvl : ℂ) + nodeLev p p' r s ν = nodeLev p p' r s θ := by
    linear_combination hw'
  exact_mod_cast this

theorem nodeChains_of_le {a μ : Node} (h : μ.2 ≤ a.2) : nodeChains a μ = ∅ := by
  rw [nodeChains]
  simp [show ¬ a.2 < μ.2 by omega]

theorem nodeChains_of_lt {a μ : Node} (h : a.2 < μ.2) :
    nodeChains a μ =
      (if (μ.2 - a.2) % 2 = 1 then {[a, μ]} else ∅) ∪
        ((firstSteps a μ).filter (· ≠ μ)).attach.biUnion fun θ =>
          (nodeChains θ.1 μ).image (a :: ·) := by
  rw [nodeChains]
  simp [h]

/-- Every node chain from `a` is `a :: γ'` with `γ'` nonempty. -/
theorem nodeChains_head {a μ : Node} {γ : List Node} (hγ : γ ∈ nodeChains a μ) :
    ∃ x l, γ = a :: x :: l := by
  rcases Nat.lt_or_ge a.2 μ.2 with h | h
  · rw [nodeChains_of_lt h] at hγ
    rcases Finset.mem_union.1 hγ with h1 | h1
    · split_ifs at h1
      · rw [Finset.mem_singleton.1 h1]; exact ⟨μ, [], rfl⟩
      · simp at h1
    · obtain ⟨θ, -, h2⟩ := Finset.mem_biUnion.1 h1
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h2
      obtain ⟨x, l, rfl⟩ := nodeChains_head hγ'
      exact ⟨θ.1, x :: l, rfl⟩
  · rw [nodeChains_of_le h] at hγ; simp at hγ
termination_by μ.2 - a.2
decreasing_by
  have hm := (Finset.mem_filter.1 θ.2).1
  simp only [firstSteps, Finset.mem_union, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_Ioo] at hm
  rcases hm with hm | hm
  · omega
  · split_ifs at hm <;> simp_all

theorem mem_firstSteps {a μ θ : Node} :
    θ ∈ firstSteps a μ ↔ (a.2 < θ.2 ∧ θ.2 < μ.2 ∧ (θ.2 - a.2) % 2 = 1) ∨
      ((μ.2 - a.2) % 2 = 1 ∧ θ = μ) := by
  unfold firstSteps
  rw [Finset.mem_union]
  constructor
  · rintro (h | h)
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_Ioo] at h
      exact Or.inl ⟨h.1.1, h.1.2, h.2⟩
    · split_ifs at h with ho
      · exact Or.inr ⟨ho, Finset.mem_singleton.1 h⟩
      · simp at h
  · rintro (⟨h1, h2, h3⟩ | ⟨ho, rfl⟩)
    · left
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨h1, h2⟩, h3⟩
    · right; simp [ho]

end Virasoro
