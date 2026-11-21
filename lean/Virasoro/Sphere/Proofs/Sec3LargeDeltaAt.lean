import Virasoro.Sphere.Statements.Sec3a

/-!
# Theorem 3.1 of `sphere/paper.tex` level by level

`Stmt_thm_large_delta` is the conjunction over all levels of `LargeDeltaAt`, the form in which
Lemma 3.2(iii) delivers it.
-/

namespace Virasoro.Sphere

theorem thm_large_delta_iff : Stmt_thm_large_delta ↔ ∀ N : ℕ, LargeDeltaAt N := Iff.rfl

end Virasoro.Sphere
