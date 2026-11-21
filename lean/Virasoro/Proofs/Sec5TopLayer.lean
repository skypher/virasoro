import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Proofs.SingularOnes
import Virasoro.Proofs.TopLayerArith
import Virasoro.Statements.Sec5c

/-!
# Theorem 5.9 of `paper.tex` at 70bac53: reduction to two frozen sub-statements

Proved here: `j_N(λ) = k` for `ℓ_k ≤ N < ℓ_{k+1}` (paper.tex l.838–846), the degree of
`τ^±_k` (Lemma 5.7), and the bound `k` for the pole order of `H_N` (Theorem 5.8).  The
remaining steps of the paper's proof are the frozen sub-statements
`Stmt_sub_top_layer_nondeg` (paper.tex l.850–869: `γ^±_k ≠ 0` and
`det G_M(c⋆, μ^±_k) ≠ 0`) and `Stmt_sub_top_layer_coeff` (paper.tex l.871–888: the
coefficient of `(Δ-λ)^{-k}`).
-/

namespace Virasoro

open Module

/-- In the setting of Theorem 5.8, for every family `w^±_k` with its properties, the pole order
of `G_N(c⋆,Δ)⁻¹` at `Δ = λ` is `j_N(λ)`. -/
theorem poleOrderInv_eq_jDepth {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)} (hT : TopLayerSetting p p' r s b wp wm) (N : ℕ) :
    poleOrderInv (gramLocal (kacC b) (kacH r s b) N) = jDepth p p' r s N := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  obtain ⟨hsing, hjan⟩ := hT
  have hcount : ∀ (N : ℕ) (e : Multiset ℕ), IsSmith (gramLocal (kacC b) (kacH r s b) N) e →
      ∀ i : ℕ, 1 ≤ i → (e.filter fun x => i ≤ x).card =
        finrank ℂ ↥((Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i)) ⊓ Verma.level N) := by
    intro N e he i hi
    rw [← hjan i hi, finrank_jantzen_inf_level, (jantzen_dim (kacC b) (kacH r s b) N e he).1 i]
  obtain ⟨e, he⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH r s b) N)
  rw [(smith_main he).2.2]
  have hE : ∀ i : ℕ, 1 ≤ i →
      ((∃ x ∈ e, i ≤ x) ↔ min (ellPlus p p' r s i) (ellMinus p p' r s i) ≤ N) := by
    intro i hi
    rw [← inf_level_ne_bot_iff (hsing i hi).1 (hsing i hi).2, ← not_iff_not, not_not,
      ← Submodule.finrank_eq_zero, ← hcount N e he i hi, Multiset.card_eq_zero,
      Multiset.filter_eq_nil]
    push Not
    rfl
  apply le_antisymm
  · refine Multiset.sup_le.2 fun x hx => ?_
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Nat.zero_le _
    · have h1 : 1 ≤ x := by omega
      have h2 := (hE x h1).1 ⟨x, hx, le_rfl⟩
      have h3 := le_ellPlus (r := r) hp hp' hr hs hsp h1
      have h4 := le_ellMinus (r := r) hp hp' hrp hs hsp h1
      have h5 : x ≤ N := by
        rcases min_le_iff.1 h2 with h6 | h6 <;> omega
      exact Finset.le_sup (f := id)
        (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h5⟩, h2⟩)
  · unfold jDepth
    refine Finset.sup_le fun k hk => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨x, hx, hkx⟩ := (hE k hk.1.1).2 hk.2
    exact le_trans hkx (Multiset.le_sup hx)

/-- Frozen sub-statement of Theorem 5.9 (paper.tex l.850–869).  In the setting of Theorem 5.8,
for `k ≥ 1`, `ℓ_k ≤ N < ℓ_{k+1}` and each sign with `ℓ^±_k ≤ N`: `γ^±_k ≠ 0` and
`det G_M(c⋆, μ^±_k) ≠ 0` for `M ≤ N - ℓ^±_k`.
Demand sheet: the hypotheses and the two clauses are those of `Stmt_thm_top_layer`, word for
word. -/
def Stmt_sub_top_layer_nondeg : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → ellMin p p' r s k ≤ N → N < ellMin p p' r s (k + 1) →
        (∀ xp : Nat.Partition (ellPlus p p' r s k) → ℂ,
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k → ellPlus p p' r s k ≤ N →
            jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp ≠ 0 ∧
            (∀ M : ℕ, M ≤ N - ellPlus p p' r s k →
              (gram (kacC b) (kacH r s b + (ellPlus p p' r s k : ℂ)) M).det ≠ 0)) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s k) → ℂ,
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k → ellMinus p p' r s k ≤ N →
            jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm ≠ 0 ∧
            (∀ M : ℕ, M ≤ N - ellMinus p p' r s k →
              (gram (kacC b) (kacH r s b + (ellMinus p p' r s k : ℂ)) M).det ≠ 0))

/-- Frozen sub-statement of Theorem 5.9 (paper.tex l.871–888): the coefficient of
`(Δ-λ)^{-k}` in `H_N(c⋆,Δ,d)` is the right side of equation (5.1).
Demand sheet: the hypotheses and the identity are those of the last clause of
`Stmt_thm_top_layer`, word for word. -/
def Stmt_sub_top_layer_coeff : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → ellMin p p' r s k ≤ N → N < ellMin p p' r s (k + 1) →
        ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            ppCoeff (HN (kacC b) N) (pt (kacH r s b)) k =
              topTerm (kacC b) (kacH r s b) N (ellPlus p p' r s k) k xp +
                topTerm (kacC b) (kacH r s b) N (ellMinus p p' r s k) k xm

/-- Theorem 5.9 from its two frozen sub-statements. -/
theorem thm_top_layer_of_subs (h1 : Stmt_sub_top_layer_nondeg)
    (h2 : Stmt_sub_top_layer_coeff) : Stmt_thm_top_layer := by
  intro p p' r s b hset wp wm hT k N hk hN1 hN2
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hj : jDepth p p' r s N = k := jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2
  obtain ⟨hnp, hnm⟩ := h1 p p' r s b hset' wp wm hT k N hk hN1 hN2
  refine ⟨hj, ?_, ?_, ?_⟩
  · intro xp hxp hle
    obtain ⟨hγ, hdet⟩ := hnp xp hxp hle
    refine ⟨hγ, hdet, ?_⟩
    have hsg : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b)
        (ellPlus p p' r s k) xp) (ellPlus p p' r s k) := by
      rw [hxp]
      exact (hT.1 k hk).1
    exact (lem_singular_degree _ _ _ (hk.trans (le_ellPlus (r := r) hp hp' hr hs hsp hk)) xp
      hsg).2.1
  · intro xm hxm hle
    obtain ⟨hγ, hdet⟩ := hnm xm hxm hle
    refine ⟨hγ, hdet, ?_⟩
    have hsg : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b)
        (ellMinus p p' r s k) xm) (ellMinus p p' r s k) := by
      rw [hxm]
      exact (hT.1 k hk).2
    exact (lem_singular_degree _ _ _ (hk.trans (le_ellMinus (r := r) hp hp' hrp hs hsp hk)) xm
      hsg).2.1
  · intro xp xm hxp hxm
    refine ⟨?_, h2 p p' r s b hset' wp wm hT k N hk hN1 hN2 xp xm hxp hxm⟩
    rw [← hj]
    refine poleOrder_HN_le (kacC b) (kacH r s b) N _ fun M hM => ?_
    rw [poleOrderInv_eq_jDepth hset' hT M]
    exact jDepth_mono p p' r s hM

end Virasoro
