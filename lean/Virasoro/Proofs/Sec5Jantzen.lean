import Virasoro.Proofs.JantzenLevel
import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.SmithExist
import Virasoro.Cited
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Theorem 5.7: Smith layers at minimal-model charges, from the cited Jantzen layers
-/

namespace Virasoro

open Module

variable {K : Type*} [Field K] [CharZero K] {c h : K}

instance levelFiniteDimensional (N : ℕ) :
    FiniteDimensional K ↥(Verma.level (c := c) (h := h) N) := by
  unfold Verma.level
  infer_instance

/-- The level-`N` part of `U(Vir_-) w⁺ + U(Vir_-) w⁻`, for singular vectors of levels `ℓ⁺`,
`ℓ⁻`, is nonzero exactly when `min(ℓ⁺, ℓ⁻) ≤ N`. -/
theorem inf_level_ne_bot_iff {wp wm : Verma K c h} {lp lm N : ℕ}
    (hp : Verma.IsSingular wp lp) (hm : Verma.IsSingular wm lm) :
    (Verma.negSpan wp ⊔ Verma.negSpan wm) ⊓ Verma.level N ≠ ⊥ ↔ min lp lm ≤ N := by
  have hwp : wp ∈ Verma.level lp := Verma.mem_level_of_L_zero hp.2.1
  have hwm : wm ∈ Verma.level lm := Verma.mem_level_of_L_zero hm.2.1
  constructor
  · intro hne
    by_contra hlt
    apply hne
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv1
    have h0 : Verma.comp N (a + b) = 0 := by
      rw [map_add, Verma.comp_negSpan_eq_zero hwp (by omega) ha,
        Verma.comp_negSpan_eq_zero hwm (by omega) hb, add_zero]
    have h1 := Verma.pbwCoord_comp_of_mem_level hv2
    rw [h0, map_zero] at h1
    rw [Submodule.mem_bot]
    exact h1.symm
  · intro hmin
    rw [Submodule.ne_bot_iff]
    rcases min_le_iff.1 hmin with hle | hle
    · obtain ⟨v, hv0, hv1, hv2⟩ := Verma.exists_ne_zero_negSpan_level hp.1 hwp hle
      exact ⟨v, ⟨Submodule.mem_sup_left hv1, hv2⟩, hv0⟩
    · obtain ⟨v, hv0, hv1, hv2⟩ := Verma.exists_ne_zero_negSpan_level hm.1 hwm hle
      exact ⟨v, ⟨Submodule.mem_sup_right hv1, hv2⟩, hv0⟩

theorem jDepth_mono (p p' r s : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    jDepth p p' r s M ≤ jDepth p p' r s N := by
  unfold jDepth
  refine Finset.sup_mono fun k hk => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
  exact ⟨⟨hk.1.1, hk.1.2.trans hMN⟩, hk.2.trans hMN⟩

/-- Theorem 5.7, with the Jantzen layers taken from the literature. -/
theorem thm_jantzen_smith (hJ : Cited_JantzenLayers) : Stmt_thm_jantzen_smith := by
  intro p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  obtain ⟨wp, wm, hsing, hjan⟩ := hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hcount : ∀ (N : ℕ) (e : Multiset ℕ), IsSmith (gramLocal (kacC b) (kacH r s b) N) e →
      ∀ i : ℕ, 1 ≤ i → (e.filter fun x => i ≤ x).card =
        finrank ℂ ↥((Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i)) ⊓ Verma.level N) := by
    intro N e he i hi
    rw [← hjan i hi, finrank_jantzen_inf_level, (jantzen_dim (kacC b) (kacH r s b) N e he).1 i]
  have hpole : ∀ N : ℕ,
      poleOrderInv (gramLocal (kacC b) (kacH r s b) N) = jDepth p p' r s N := by
    intro N
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
  refine ⟨wp, wm, hsing, hjan, hcount, fun N => ⟨hpole N, ?_, ?_⟩⟩
  · rw [← hpole N]
    exact poleOrder_FN_le (kacC b) (kacH r s b) N
  · refine poleOrder_HN_le (kacC b) (kacH r s b) N _ fun M hM => ?_
    rw [hpole M]
    exact jDepth_mono p p' r s hM

example (hJ : Cited_JantzenLayers) : Stmt_thm_jantzen_smith := thm_jantzen_smith hJ

end Virasoro
