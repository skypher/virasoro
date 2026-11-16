import Virasoro.Proofs.PBWIndep
import Virasoro.Proofs.PBWSpan
import Virasoro.Proofs.LargeWeightCore

/-!
# Enumerating the partitions of a small integer

A list `ws` of weakly decreasing words of positive integers enumerates the partitions of `N` if
it has no repetition and contains every such word of sum `N`.  It gives an explicit bijection
between `Nat.Partition N` and `Fin ws.length`, through which the Shapovalov and torus matrices
become explicit matrices of normal-ordered matrix elements.
-/

namespace Virasoro

/-- The partition of `N` with a given word. -/
def partOf {N : ℕ} (w : List ℕ) (hw : PosWord w) (hs : w.sum = N) : Nat.Partition N where
  parts := (w : Multiset ℕ)
  parts_pos := fun {i} hi => hw i (Multiset.mem_coe.1 hi)
  parts_sum := by rw [Multiset.sum_coe, hs]

theorem word_pairwise {N : ℕ} (Y : Nat.Partition N) : Y.word.Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

theorem partOf_word {N : ℕ} {w : List ℕ} (hw : PosWord w) (hs : w.sum = N)
    (hsort : w.Pairwise (· ≥ ·)) : (partOf w hw hs).word = w := by
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hba hab)
    (word_pairwise _) hsort ?_
  exact Multiset.coe_eq_coe.1 (Verma.word_coe _)

/-- `ws` enumerates the partitions of `N`. -/
structure IsEnum (N : ℕ) (ws : List (List ℕ)) : Prop where
  nodup : ws.Nodup
  pos : ∀ w ∈ ws, PosWord w
  sum : ∀ w ∈ ws, w.sum = N
  sorted : ∀ w ∈ ws, w.Pairwise (· ≥ ·)
  complete : ∀ w : List ℕ, PosWord w → w.sum = N → w.Pairwise (· ≥ ·) → w ∈ ws

namespace IsEnum

variable {N : ℕ} {ws : List (List ℕ)}

theorem word_mem (h : IsEnum N ws) (Y : Nat.Partition N) : Y.word ∈ ws :=
  h.complete _ (Verma.posWord_word Y) (word_sum Y) (word_pairwise Y)

/-- The bijection between partitions of `N` and positions in the enumerating list. -/
def equiv (h : IsEnum N ws) : Nat.Partition N ≃ Fin ws.length where
  toFun Y := ⟨ws.idxOf Y.word, List.idxOf_lt_length_of_mem (h.word_mem Y)⟩
  invFun i := partOf (ws[i.1]'i.2) (h.pos _ (List.getElem_mem i.2))
    (h.sum _ (List.getElem_mem i.2))
  left_inv Y := by
    apply Nat.Partition.ext
    show ((ws[ws.idxOf Y.word]'(List.idxOf_lt_length_of_mem (h.word_mem Y)) : List ℕ) :
      Multiset ℕ) = Y.parts
    rw [List.getElem_idxOf, Verma.word_coe]
  right_inv i := by
    apply Fin.ext
    have hw := partOf_word (h.pos _ (List.getElem_mem i.2)) (h.sum _ (List.getElem_mem i.2))
      (h.sorted _ (List.getElem_mem i.2))
    show ws.idxOf (partOf (ws[i.1]'i.2) (h.pos _ (List.getElem_mem i.2))
      (h.sum _ (List.getElem_mem i.2))).word = i
    rw [hw]
    exact h.nodup.idxOf_getElem i i.2

theorem word_symm (h : IsEnum N ws) (i : Fin ws.length) :
    (h.equiv.symm i).word = ws[i.1]'i.2 :=
  partOf_word (h.pos _ (List.getElem_mem i.2)) (h.sum _ (List.getElem_mem i.2))
    (h.sorted _ (List.getElem_mem i.2))

theorem getElem_equiv (h : IsEnum N ws) (Y : Nat.Partition N) :
    ws[(h.equiv Y).1]'(h.equiv Y).2 = Y.word :=
  List.getElem_idxOf _

end IsEnum

/-- The weakly decreasing words of positive integers of sum `1`. -/
theorem isEnum_one : IsEnum 1 [[1]] where
  nodup := by decide
  pos := by simp [PosWord]
  sum := by decide
  sorted := by decide
  complete := by
    intro w hw hs _
    match w, hw, hs with
    | [], _, hs => simp at hs
    | [a], _, hs =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      subst hs
      simp
    | a :: b :: t, hw, hs =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      simp only [List.sum_cons] at hs
      omega

/-- The weakly decreasing words of positive integers of sum `2`. -/
theorem isEnum_two : IsEnum 2 [[2], [1, 1]] where
  nodup := by decide
  pos := by simp [PosWord]
  sum := by decide
  sorted := by decide
  complete := by
    intro w hw hs hp
    match w, hw, hs, hp with
    | [], _, hs, _ => simp at hs
    | [a], _, hs, _ =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      subst hs
      simp
    | [a, b], hw, hs, hp =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 1 := by omega
      simp
    | a :: b :: c :: t, hw, hs, _ =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      have hc := hw c (by simp)
      simp only [List.sum_cons] at hs
      omega

/-- The weakly decreasing words of positive integers of sum `3`. -/
theorem isEnum_three : IsEnum 3 [[3], [2, 1], [1, 1, 1]] where
  nodup := by decide
  pos := by simp [PosWord]
  sum := by decide
  sorted := by decide
  complete := by
    intro w hw hs hp
    match w, hw, hs, hp with
    | [], _, hs, _ => simp at hs
    | [a], _, hs, _ =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      subst hs
      simp
    | [a, b], hw, hs, hp =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hp
      obtain ⟨rfl, rfl⟩ : a = 2 ∧ b = 1 := by omega
      simp
    | [a, b, c], hw, hs, hp =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      have hc := hw c (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      obtain ⟨rfl, rfl, rfl⟩ : a = 1 ∧ b = 1 ∧ c = 1 := by omega
      simp
    | a :: b :: c :: e :: t, hw, hs, _ =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      have hc := hw c (by simp)
      have he := hw e (by simp)
      simp only [List.sum_cons] at hs
      omega

/-- The weakly decreasing words of positive integers of sum `4`. -/
theorem isEnum_four : IsEnum 4 [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]] where
  nodup := by decide
  pos := by simp [PosWord]
  sum := by decide
  sorted := by decide
  complete := by
    intro w hw hs hp
    match w, hw, hs, hp with
    | [], _, hs, _ => simp at hs
    | [a], _, hs, _ =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      subst hs
      simp
    | [a, b], hw, hs, hp =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true] at hp
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 3 ∧ b = 1) ∨ (a = 2 ∧ b = 2) := by omega
      · simp
      · simp
    | [a, b, c], hw, hs, hp =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      have hc := hw c (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true, forall_eq_or_imp] at hp
      obtain ⟨rfl, rfl, rfl⟩ : a = 2 ∧ b = 1 ∧ c = 1 := by omega
      simp
    | [a, b, c, e], hw, hs, hp =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      have hc := hw c (by simp)
      have he := hw e (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      obtain ⟨rfl, rfl, rfl, rfl⟩ : a = 1 ∧ b = 1 ∧ c = 1 ∧ e = 1 := by omega
      simp
    | a :: b :: c :: e :: f :: t, hw, hs, _ =>
      have ha := hw a (by simp)
      have hb := hw b (by simp)
      have hc := hw c (by simp)
      have he := hw e (by simp)
      have hf := hw f (by simp)
      simp only [List.sum_cons] at hs
      omega

end Virasoro
