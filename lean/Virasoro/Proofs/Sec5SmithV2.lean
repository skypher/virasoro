import Virasoro.Proofs.Sec5Smith
import Virasoro.Statements.Sec5c

/-!
# Lemma 5.1 of `paper.tex` at 70bac53

The three identities are those of the earlier form of the lemma; its special case with
`k = dim ker G(0)` gives the last clause.
-/

namespace Virasoro

open Module

/-- Paper label: lem:smith -/
theorem lem_smith_v2 : V2.Stmt_lem_smith := by
  intro m G s hdet hs
  obtain ⟨h1, h2, h3, h4⟩ := lem_smith m G s hdet hs
  exact ⟨h1, h2, h3, fun h => (h4 (finrank ℂ (ker0 G)) h rfl).1⟩

example : V2.Stmt_lem_smith := lem_smith_v2

end Virasoro
