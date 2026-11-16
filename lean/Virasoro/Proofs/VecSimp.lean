import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Evaluating explicit vectors and matrices at numeral indices
-/

/-- Evaluate entries `![a, b, …] i` and `!![a, b; c, d] i j` at numeral indices. -/
syntax "vec_simp" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| vec_simp $[$loc]?) =>
    `(tactic| simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] $[$loc]?)

example : (![1, 2, 3] : Fin 3 → ℕ) 2 = 3 := by vec_simp
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℕ) 1 0 = 3 := by vec_simp
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) 4 = 5 := by vec_simp
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) 3 = 4 := by vec_simp
example (h : (![1, 2, 3] : Fin 3 → ℕ) 1 = 7) : (2 : ℕ) = 7 := by
  vec_simp at h
  exact h
