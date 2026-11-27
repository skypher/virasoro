import Virasoro.Proofs.Sec8BTop
import Virasoro.Proofs.Sec8DiagValues

/-!
# Section 8.2: Lemma 8.7(i) at the boundary

(7.10) at `μ_i`: from a node every label leads to a node of larger layer (Lemma 8.10), so the
chain values to a point that is no node vanish; at a node of layer `≠ i + k'` one of the two factors
vanishes at `b⋆`; one node per layer remains.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' x₀ : ℕ} {b : ℂ}

section Dead

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem b_chainTail_dead (j : ℕ) : ∀ D : ℕ, ∀ ν : ℕ,
    (∀ m : ℕ, ν < m → bLev p p' x₀ m ≠ bLev p p' x₀ ν + D) → ∀ y : Kd⸨X⸩,
    chainTail (bsC b) dvar j D (pt (bWt p p' x₀ ν)) y = 0 := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro ν hno y
  rw [chainTail_eq]
  refine Finset.sum_eq_zero fun g hg => ?_
  rw [mem_labelsAt_node, mem_labels_iff] at hg
  obtain ⟨⟨h1, h2, hl⟩, hw⟩ := hg
  obtain ⟨m, hνm, hw'⟩ := label_leads hB ν g (by omega) (by omega) hw
  have hgeq := (label_iff hB hνm g (by omega) (by omega)).1 ⟨hw, hw'⟩
  have hlv := lvl_bLabel hB hνm
  rw [← hgeq] at hlv
  have hpos : 1 ≤ g.lvl := by unfold Label.lvl; exact Nat.mul_pos (by omega) (by omega)
  have hne : g.lvl ≠ D := by intro h; exact hno m hνm (by omega)
  have hpt : pt (bWt p p' x₀ ν) + (g.lvl : Kd) = pt (bWt p p' x₀ m) := by
    rw [hgeq]; exact pt_bWt_add hB hνm
  rw [if_neg hne, hpt, ih (D - g.lvl) (by omega) m
    (fun m' hm' => by have := hno m' (hνm.trans hm'); omega), mul_zero]

theorem b_chainFn_dead (ν D k' j : ℕ)
    (hno : ∀ m : ℕ, ν < m → bLev p p' x₀ m ≠ bLev p p' x₀ ν + D) :
    chainFnC b (bWt p p' x₀ ν) D k' j = 0 := by
  unfold chainFnC chainFn
  refine Finset.sum_eq_zero fun g hg => ?_
  rw [mem_labelsAt_node, mem_labels_iff] at hg
  obtain ⟨⟨h1, h2, hl⟩, hw⟩ := hg
  obtain ⟨m, hνm, hw'⟩ := label_leads hB ν g (by omega) (by omega) hw
  have hgeq := (label_iff hB hνm g (by omega) (by omega)).1 ⟨hw, hw'⟩
  have hlv := lvl_bLabel hB hνm
  rw [← hgeq] at hlv
  have hpos : 1 ≤ g.lvl := by unfold Label.lvl; exact Nat.mul_pos (by omega) (by omega)
  have hne : g.lvl ≠ D := by intro h; exact hno m hνm (by omega)
  have hpt : pt (bWt p p' x₀ ν) + (g.lvl : Kd) = pt (bWt p p' x₀ m) := by
    rw [hgeq]; exact pt_bWt_add hB hνm
  rw [if_neg hne, hpt, b_chainTail_dead hB j (D - g.lvl) m
    (fun m' hm' => by have := hno m' (hνm.trans hm'); omega), mul_zero]

end Dead

/-- Lemma 8.7(i) at the boundary. -/
theorem b_values_i (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hB : BoundarySetting p p' x₀ b) {i k : ℕ} (hik : i < k) (k' j : ℕ) (hk : 1 ≤ k')
    (hj : 1 ≤ j) (hkj : k' + j = k - i) :
    (j : Kd) * (bChain p p' x₀ b i k k' j).coeff 0 =
      (bChain p p' x₀ b i k (k' + 1) (j - 1)).coeff 0 -
        bTop p p' x₀ b i (i + k') * (bChain p p' x₀ b (i + k') k 1 (j - 1)).coeff 0 := by
  have hb0 := b_ne_zero_of (bSetting_minimal hB)
  have hlev := bLev_strictMono hB hik
  have hcut := (cor_chain_values_of_cited hK hH b hb0).2.1 (bWt p p' x₀ i)
    (bLev p p' x₀ k - bLev p p' x₀ i) k' j (by omega) hk hj
  have hν1 := bLev_strictMono hB (show i < i + k' by omega)
  have hν2 := bLev_strictMono hB (show i + k' < k by omega)
  unfold bChain
  rw [hcut]
  congr 1
  rw [← Finset.sum_subset (s₁ := {bLev p p' x₀ (i + k') - bLev p p' x₀ i})
    (by intro n hn; rw [Finset.mem_singleton.1 hn, Finset.mem_Ioo]; omega) ?_,
    Finset.sum_singleton]
  · have hw : bWt p p' x₀ i + ((bLev p p' x₀ (i + k') - bLev p p' x₀ i : ℕ) : ℂ) =
        bWt p p' x₀ (i + k') := by
      rw [bWt_add_lev hB (i + k'), bWt_add_lev hB i, Nat.cast_sub hν1.le]; ring
    rw [hw, show bLev p p' x₀ k - bLev p p' x₀ i - (bLev p p' x₀ (i + k') - bLev p p' x₀ i) =
      bLev p p' x₀ k - bLev p p' x₀ (i + k') by omega]
    simp only [bTop, bChain, Nat.add_sub_cancel_left]
  · intro n hn hnot
    rw [Finset.mem_Ioo] at hn
    rw [Finset.mem_singleton] at hnot
    by_cases hex : ∃ m : ℕ, i < m ∧ bLev p p' x₀ m = bLev p p' x₀ i + n
    · obtain ⟨m, him, hml⟩ := hex
      have hmk : m ≠ i + k' := by intro h; apply hnot; rw [← h]; omega
      rcases lt_or_gt_of_ne hmk with h1 | h1
      · have hz := b_chain_coeff_zero hB him k' 0 hk (by omega)
        unfold bChain at hz
        rw [show bLev p p' x₀ m - bLev p p' x₀ i = n by omega] at hz
        rw [hz, zero_mul]
      · have hw : bWt p p' x₀ i + (n : ℂ) = bWt p p' x₀ m := by
          rw [bWt_add_lev hB m, bWt_add_lev hB i, hml]; push_cast; ring
        rw [hw]
        have hmk' : m < k := by
          by_contra hc
          have : bLev p p' x₀ k ≤ bLev p p' x₀ m := (bLev_strictMono hB).monotone (by omega)
          omega
        have hz := b_chain_coeff_zero hB hmk' 1 (j - 1) le_rfl (by omega)
        unfold bChain at hz
        rw [show bLev p p' x₀ k - bLev p p' x₀ m =
          bLev p p' x₀ k - bLev p p' x₀ i - n by omega] at hz
        rw [hz, mul_zero]
    · push_neg at hex
      rw [b_chainFn_dead hB i n k' 0 (fun m hm => hex m hm), HahnSeries.coeff_zero, zero_mul]

end Virasoro
