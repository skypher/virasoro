import Virasoro.Proofs.Sec6H13TGF
import Virasoro.Proofs.Sec5Spin
import Virasoro.Proofs.PartEnum

/-!
# Proposition 6.8(ii): partitions `(1^a, μ)` (paper.tex l.1306–1309)

"Write each `λ ⊢ M` as `λ = (1^a, μ)` with all parts of `μ` at least `2`": the partitions of `M`
correspond to the weakly decreasing words `μ` with all parts at least `2` and `|μ| ≤ M`, through
`λ.word = μ ++ 1^{M − |μ|}`.
-/

namespace Virasoro.H13T

open Virasoro.H13D Finset

/-- A weakly decreasing word with all parts at least `2`. -/
def Adm (μ : List ℕ) : Prop := μ.Pairwise (· ≥ ·) ∧ ∀ y ∈ μ, 2 ≤ y

/-- The partition `(1^{M−|μ|}, μ)` of `M` (any partition if `μ` is not admissible or too big). -/
noncomputable def lamOf (μ : List ℕ) (M : ℕ) : Nat.Partition M := by
  classical
  exact if h : (∀ y ∈ μ, 0 < y) ∧ μ.sum ≤ M then
    ⟨((μ ++ List.replicate (M - μ.sum) 1 : List ℕ) : Multiset ℕ), by
      intro i hi
      rw [Multiset.mem_coe, List.mem_append] at hi
      rcases hi with hi | hi
      · exact h.1 i hi
      · rw [List.eq_of_mem_replicate hi]; exact one_pos, by
      rw [Multiset.sum_coe, List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
      omega⟩
  else Nat.Partition.indiscrete M

theorem lamOf_word {μ : List ℕ} (hμ : Adm μ) {M : ℕ} (hM : μ.sum ≤ M) :
    (lamOf μ M).word = μ ++ List.replicate (M - μ.sum) 1 := by
  have hpos : ∀ y ∈ μ, 0 < y := fun y hy => by have := hμ.2 y hy; omega
  apply word_eq_of_parts
  · rw [List.pairwise_append]
    refine ⟨hμ.1, List.pairwise_replicate.2 (Or.inr le_rfl), fun a ha b hb => ?_⟩
    rw [List.eq_of_mem_replicate hb]
    have := hμ.2 a ha
    omega
  · unfold lamOf
    rw [dif_pos ⟨hpos, hM⟩]

/-- The admissible words of size at most `B`. -/
noncomputable def admSet (B : ℕ) : Finset (List ℕ) := by
  classical
  exact (range (B + 1)).biUnion fun w =>
    ((univ : Finset (Nat.Partition w)).image fun Y => Y.word).filter fun μ => ∀ y ∈ μ, 2 ≤ y

theorem mem_admSet {B : ℕ} {μ : List ℕ} : μ ∈ admSet B ↔ Adm μ ∧ μ.sum ≤ B := by
  classical
  unfold admSet
  constructor
  · intro h
    obtain ⟨w, hw, h⟩ := mem_biUnion.1 h
    obtain ⟨h1, h2⟩ := mem_filter.1 h
    obtain ⟨Y, _, rfl⟩ := mem_image.1 h1
    refine ⟨⟨word_pairwise Y, h2⟩, ?_⟩
    rw [word_sum_eq]
    exact Nat.lt_succ_iff.1 (mem_range.1 hw)
  · rintro ⟨hμ, hB⟩
    have hpos : ∀ y ∈ μ, 0 < y := fun y hy => by have := hμ.2 y hy; omega
    refine mem_biUnion.2 ⟨μ.sum, mem_range.2 (Nat.lt_succ_of_le hB), mem_filter.2 ⟨?_, hμ.2⟩⟩
    refine mem_image.2 ⟨⟨(μ : Multiset ℕ), fun {i} hi => hpos i (Multiset.mem_coe.1 hi),
      by rw [Multiset.sum_coe]⟩, mem_univ _, ?_⟩
    exact word_eq_of_parts _ μ hμ.1 rfl

theorem admSet_mono {B B' : ℕ} (h : B ≤ B') : admSet B ⊆ admSet B' := fun μ hμ => by
  rw [mem_admSet] at hμ ⊢
  exact ⟨hμ.1, hμ.2.trans h⟩

/-- The parts at least `2` of a partition, in weakly decreasing order. -/
def big {M : ℕ} (Y : Nat.Partition M) : List ℕ := Y.word.filter fun y => decide (2 ≤ y)

theorem big_adm {M : ℕ} (Y : Nat.Partition M) : Adm (big Y) :=
  ⟨(word_pairwise Y).filter _, fun y hy => by simpa using (List.mem_filter.1 hy).2⟩

theorem word_eq_big_ones {M : ℕ} (Y : Nat.Partition M) :
    Y.word = big Y ++ List.replicate (M - (big Y).sum) 1 ∧ (big Y).sum ≤ M := by
  set n := (Y.word.filter fun y => !decide (2 ≤ y)).length with hn
  have hones : (Y.word.filter fun y => !decide (2 ≤ y)) = List.replicate n 1 := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    have h1 := List.mem_filter.1 hb
    have h2 := word_pos Y b h1.1
    simp at h1
    omega
  have hperm := List.filter_append_perm (fun y => decide (2 ≤ y)) Y.word
  rw [hones] at hperm
  have hsum : (big Y).sum + n = M := by
    have := hperm.sum_eq
    rw [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, word_sum_eq] at this
    exact this
  refine ⟨?_, by omega⟩
  rw [show M - (big Y).sum = n by omega]
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hba hab) (word_pairwise Y)
  · rw [List.pairwise_append]
    refine ⟨(big_adm Y).1, List.pairwise_replicate.2 (Or.inr le_rfl), fun a ha b hb => ?_⟩
    rw [List.eq_of_mem_replicate hb]
    have := (big_adm Y).2 a ha
    omega
  · exact hperm.symm

theorem big_lamOf {μ : List ℕ} (hμ : Adm μ) {M : ℕ} (hM : μ.sum ≤ M) : big (lamOf μ M) = μ := by
  rw [big, lamOf_word hμ hM, List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2,
    List.append_nil]
  · intro a ha
    rw [List.eq_of_mem_replicate ha]
    decide
  · intro a ha
    simpa using hμ.2 a ha

theorem lamOf_big {M : ℕ} (Y : Nat.Partition M) : lamOf (big Y) M = Y := by
  obtain ⟨h1, h2⟩ := word_eq_big_ones Y
  apply word_injective
  rw [lamOf_word (big_adm Y) h2, ← h1]

/-- `∑_{λ ⊢ M} f(λ) = ∑_{μ admissible, |μ| ≤ M} f((1^{M−|μ|}, μ))`. -/
theorem sum_partition_eq {α : Type*} [AddCommMonoid α] (M : ℕ) (f : Nat.Partition M → α) :
    ∑ Y, f Y = ∑ μ ∈ admSet M, f (lamOf μ M) := by
  refine Finset.sum_nbij' (fun Y => big Y) (fun μ => lamOf μ M) ?_ ?_ ?_ ?_ ?_
  · intro Y _
    exact mem_admSet.2 ⟨big_adm Y, (word_eq_big_ones Y).2⟩
  · intro μ _
    exact mem_univ _
  · intro Y _
    exact lamOf_big Y
  · intro μ hμ
    obtain ⟨h1, h2⟩ := mem_admSet.1 hμ
    exact big_lamOf h1 h2
  · intro Y _
    rw [lamOf_big]

end Virasoro.H13T
