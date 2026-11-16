import Virasoro.Proofs.Crossing
import Virasoro.Statements.Sec5a

/-!
# The frozen reading of Lemma 5.10 fails at level zero

For `ℓ = 0` and `P = 1` the vector `|h₀⟩` satisfies the hypotheses of Lemma 5.10 as written, the
crossing scalar is `d/dh ⟨h|h⟩ = 0`, and the conclusion at `m = 1` would read
`d/dh ⟨h|L_1 L_{-1}|h⟩ = d/dh (2h) = 0`.
-/

namespace Virasoro

open Polynomial

theorem word_default_zero : (default : Nat.Partition 0).word = [] := by
  have h : (((default : Nat.Partition 0).word : List ℕ) : Multiset ℕ) = 0 := by
    rw [Verma.word_coe]
    rfl
  exact (Multiset.coe_eq_zero _).1 h

theorem word_default_one : (default : Nat.Partition 1).word = [1] := by
  have h : (((default : Nat.Partition 1).word : List ℕ) : Multiset ℕ) = {1} := by
    rw [Verma.word_coe]
    rfl
  have h2 : (default : Nat.Partition 1).word.Perm [1] := Multiset.coe_eq_coe.1 h
  exact List.perm_singleton.1 h2

theorem gramWord_one_one (c h : ℂ[X]) : gramWord c h [1] [1] = 2 * h := by
  simp [gramWord, actSt, actWord, vac, centralTerm]

theorem gramWord_nil_nil (c h : ℂ[X]) : gramWord c h [] [] = 1 := by
  simp [gramWord, vac]

/-- The literal reading of Lemma 5.10, with level `ℓ = 0` allowed, is false. -/
theorem not_stmt_lem_singular_crossing : ¬ Stmt_lem_singular_crossing := by
  intro hS
  have hpbw : Verma.pbwCoord (c := (0 : ℂ)) (h := (0 : ℂ)) 0 (fun _ => 1) = Verma.hw := by
    rw [Verma.pbwCoord_apply, Fintype.sum_unique, one_smul, word_default_zero, Verma.neg_nil]
  have hsing : Verma.IsSingular
      (Verma.pbwCoord (c := (0 : ℂ)) (h := (0 : ℂ)) 0 (fun _ => 1)) 0 := by
    rw [hpbw]
    refine ⟨?_, ?_, fun n hn => Verma.L_hw_pos hn⟩
    · intro h0
      have := (Verma.isVacuum_vacuum (c := (0 : ℂ)) (h := (0 : ℂ))).1
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · rw [Verma.L_hw_zero]
      simp
  have key := hS 0 0 0 (fun _ => 1) hsing 1 default default
  simp only [Fintype.sum_unique, word_default_zero, word_default_one, List.append_nil,
    gramWord_one_one, crossScalar, gramForm, dotProduct, Matrix.mulVec, gram, Matrix.of_apply,
    gramWord_nil_nil] at key
  simp at key

end Virasoro
