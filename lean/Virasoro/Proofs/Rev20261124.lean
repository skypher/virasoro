import Virasoro.Statements.Rev20261124
import Virasoro.Proofs.P2Sec11WardInd
import Virasoro.Proofs.Sec6Final

/-!
# Proofs of the statements of `paper.tex` added or restated after 70bac53

Lemma 11.2 is the Ward induction already used in the proof of Proposition 11.3
(`Verma.ward_induction`, Proofs/P2Sec11WardInd.lean), which follows the paper's two inductions.
Theorem 7.6 in its current form consists of clauses of the 70bac53 form.
-/

namespace Virasoro

open Verma

/-- Lemma 11.2: the two inductions of the paper's proof (`Verma.ward_induction`); no cited input.

Paper label: lem:ward-induction -/
theorem lem_ward_induction : Stmt_lem_ward_induction := by
  intro p p' b _ _ _ _ ν d ψ hsym hW w ℓ hw h0
  exact ward_induction (d := d) hW hsym hw h0

/-- The current form of Theorem 7.6 follows from the 70bac53 form. -/
theorem thm_general_confluence_paper_of (h : Stmt_thm_general_confluence) :
    Stmt_thm_general_confluence_paper := by
  intro b hb N hN
  obtain ⟨hmain, _, _, hirr⟩ := h b hb
  obtain ⟨hH, hA, hm⟩ := hmain N hN
  exact ⟨fun lam hl k hk => (hA lam hl k hk).1.symm, hm, hH, fun hq => hirr hq N hN⟩

/-- Theorem 7.6, from the two cited results.

Paper label: thm:general-confluence -/
theorem thm_general_confluence_paper_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_thm_general_confluence_paper :=
  thm_general_confluence_paper_of (thm_general_confluence_of_cited hK hH)

end Virasoro
