import Virasoro.Statements.Rev20261125
import Virasoro.Proofs.Rev20261124
import Virasoro.Proofs.Sec4Thm

/-!
# Proofs of the statements of `paper.tex` restated on 2026-11-25

Theorem 7.3 and Corollary 7.6 in their current form follow from the form of 2026-11-24
(`Stmt_thm_general_confluence_paper`) and the vanishing of the collision moments beyond the a
priori bound (`Atilde_eq_zero`).
-/

namespace Virasoro

theorem AtildeC_eq_zero {b : ℂ} (hb : b ≠ 0) (N : ℕ) (lam : ℂ) {k : ℕ}
    (hk : MhatC b N lam < k) : AtildeC b N lam k = 0 := by
  have hbs : (RatFunc.C b : Kd) ≠ 0 := by simpa using hb
  exact Atilde_eq_zero hbs dvar N (pt lam) (by unfold MhatC at hk; omega)

/-- Corollary 7.6 from the form of 2026-11-24 of Theorem 7.3. -/
theorem cor_pole_bound_of (h : Stmt_thm_general_confluence_paper) : Stmt_cor_pole_bound := by
  intro b hb N hN lam hlam
  exact ⟨fun k hk => AtildeC_eq_zero hb N lam hk, (h b hb N hN).2.1 lam hlam⟩

/-- Theorem 7.3 in its current form, from the form of 2026-11-24. -/
theorem thm_general_confluence_rev25_of (h : Stmt_thm_general_confluence_paper) :
    Stmt_thm_general_confluence_rev25 := by
  classical
  intro b hb N hN
  obtain ⟨hA, _, hH, hirr⟩ := h b hb N hN
  refine ⟨hA, ⟨(Lam N b).sup (MhatC b N), fun lam hlam k hk => ?_, ?_⟩, fun hq => ?_⟩
  · exact AtildeC_eq_zero hb N lam (lt_of_le_of_lt (Finset.le_sup hlam) hk)
  · rw [hH]
    refine Finset.sum_congr rfl fun lam hlam => ?_
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, le_trans hk.2 (Finset.le_sup (f := MhatC b N) hlam)⟩
    · intro k hkK hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hkK).1
      simp only [Finset.mem_Icc, not_and, not_le] at hk
      rw [AtildeC_eq_zero hb N lam (hk hk1)]
      simp [poleTerm]
  · obtain ⟨hcl, hrec⟩ := hirr hq
    refine ⟨fun lam hlam => ⟨(hcl lam hlam).1, fun k hk => ?_⟩, hrec⟩
    exact AtildeC_eq_zero hb N lam (by rw [(hcl lam hlam).2]; omega)

/-- Theorem 7.3, from the two cited results.

Paper label: thm:general-confluence -/
theorem thm_general_confluence_rev25_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_thm_general_confluence_rev25 :=
  thm_general_confluence_rev25_of (thm_general_confluence_paper_of_cited hK hH)

/-- Corollary 7.6, from the two cited results.

Paper label: cor:pole-bound -/
theorem cor_pole_bound_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_cor_pole_bound :=
  cor_pole_bound_of (thm_general_confluence_paper_of_cited hK hH)

end Virasoro
