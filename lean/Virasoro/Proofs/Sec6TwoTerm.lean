import Virasoro.Proofs.Sec5TopLayerFinal
import Virasoro.Proofs.Sec4Ising
import Virasoro.Statements.Sec6c

/-!
# Proposition 6.9 of `paper.tex` at 70bac53: reduction to `P_N ≢ 0`

The clause "`H_N(c⋆,Δ,d)` has a pole of order exactly `k` at `Δ = λ`" (paper.tex l.1424–1425)
follows from `P_N ≢ 0` and Theorem 5.9: the pole order is at most `k` and the coefficient of
`(Δ-λ)^{-k}` is `P_N`.  The nonvanishing itself (proof l.1428–1565) is the frozen sub-statement
`Stmt_sub_two_term_nonzero`.
-/

namespace Virasoro

/-- A pole of order at most `k` whose coefficient of `(Δ-a)^{-k}` is nonzero has order `k`. -/
theorem poleOrder_eq_of_ppCoeff_ne {K : Type*} [Field K] {f : RatFunc K} {a : K} {k : ℕ}
    (hle : poleOrder f a ≤ k) (hne : ppCoeff f a k ≠ 0) : poleOrder f a = k :=
  le_antisymm hle (not_lt.1 fun hlt => hne (ppCoeff_eq_zero_of_gt f a hlt))

/-- Frozen sub-statement of Proposition 6.9 (paper.tex l.1422–1423, proof l.1428–1565): on a
two-vector level `max(ℓ⁺_k, ℓ⁻_k) < N < ℓ_{k+1}` the right side `P_N(d)` of (5.1) is not zero.
Demand sheet: the hypotheses and the first clause of `Stmt_prop_two_term_criteria`, word for
word; the pole-order clause is omitted. -/
def Stmt_sub_two_term_nonzero : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → max (ellPlus p p' r s k) (ellMinus p p' r s k) < N →
        N < ellMin p p' r s (k + 1) →
        ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            topTerm (kacC b) (kacH r s b) N (ellPlus p p' r s k) k xp +
                topTerm (kacC b) (kacH r s b) N (ellMinus p p' r s k) k xm ≠ 0

/-- Proposition 6.9 from `P_N ≢ 0` and Theorem 5.9 (through the cited injectivity of the singular
embedding). -/
theorem prop_two_term_criteria_of_sub (hI : Cited_VermaHomInjective)
    (h : Stmt_sub_two_term_nonzero) : Stmt_prop_two_term_criteria := by
  intro p p' r s b hset wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  have hne := h p p' r s b hset wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  refine ⟨hne, ?_⟩
  have hmin : ellMin p p' r s k ≤ N :=
    le_trans (le_trans (min_le_left _ _) (le_max_left _ _)) hN1.le
  obtain ⟨hpo, hpc⟩ :=
    (thm_top_layer_of_cited hI p p' r s b hset wp wm hT k N hk hmin hN2).2.2.2 xp xm hxp hxm
  exact poleOrder_eq_of_ppCoeff_ne hpo (by rw [hpc]; exact hne)

end Virasoro
