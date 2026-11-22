import Virasoro.Proofs.Sec6ChainEvenBase

/-!
# Proposition 6.7, `k = 2q + 2`: the second steps after `κ = g_q` (paper.tex l.1167–1169)

From `g_q` (momentum `X = n₁ + qN₀`), a step `b` of level at most that of the endpoint
`m = σ₀n₀ + (q+1)N₀` (`σ₀ = ±1` for `ℓ^±`) either reaches `m` and is the paper's step
`(r + (2q+1)p, p' − s)` (`σ₀ = 1`) or `(p − r, s + (2q+1)p')` (`σ₀ = −1`), or lands at
`−σ₀n₀ + (q+1)N₀` with `σ₀n₀ > 0`, from where no further step stays within the level.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

/-- The paper's last step to the endpoint of `ℓ^±_{2(q+1)}` (l.1167–1168). -/
def gEnd (p p' r s q : ℕ) (σ : ℤ) : Label :=
  if σ = 1 then (r + (2 * q + 1) * p, p' - s) else (p - r, s + (2 * q + 1) * p')

/-- The steps after `g_q` within the level of `m = σ₀n₀ + (q+1)N₀`. -/
theorem Setup.second_step (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (b : Label)
    (hc : ((p' : ℤ) * b.1 - (p : ℤ) * b.2) ^ 2 =
      ((p' : ℤ) * (gL p p' r s q).1 + (p : ℤ) * (gL p p' r s q).2) ^ 2)
    (hlo : n1 p p' r s + q * N0 p p' < (p' : ℤ) * b.1 + (p : ℤ) * b.2)
    (hhi : (p' : ℤ) * b.1 + (p : ℤ) * b.2 ≤ σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') :
    ((p' : ℤ) * b.1 + (p : ℤ) * b.2 = σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' ∧
        b = gEnd p p' r s q σ) ∨
      ((p' : ℤ) * b.1 + (p : ℤ) * b.2 = -σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' ∧
        0 < σ * n0 p p' r s) := by
  have hN := h.N0_pos
  have hd := h.diff_pos
  have hs := h.sum_pos
  have h1 := h.two_n0_lt
  have h2 := h.neg_two_n0_lt
  have hn0 := h.n0_ne
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  obtain ⟨hu1, hv1⟩ := gL_nonneg (p := p) (p' := p') (r := r) (s := s) (i := (q : ℤ)) hq
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hp0' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  obtain ⟨i, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := h.next_step hc
  · -- `y = n₀ + iN₀`
    have hy : (p' : ℤ) * b.1 + (p : ℤ) * b.2 = n0 p p' r s + i * N0 p p' := by
      rw [e1, e2, hu1, hv1]; unfold n0 N0; ring
    rw [hy] at hlo hhi ⊢
    have hi1 : (q : ℤ) + 1 ≤ i := by
      by_contra hc'
      have hc' : i ≤ q := by omega
      have : i * N0 p p' ≤ q * N0 p p' := mul_le_mul_of_nonneg_right hc' hN.le
      linarith
    have hi2 : i ≤ (q : ℤ) + 1 := by
      by_contra hc'
      have hc' : (q : ℤ) + 2 ≤ i := by omega
      have : ((q : ℤ) + 2) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right hc' hN.le
      rcases hσ with rfl | rfl <;> linarith
    have hi : i = (q : ℤ) + 1 := le_antisymm hi2 hi1
    subst hi
    rcases hσ with rfl | rfl
    · left
      refine ⟨by ring, ?_⟩
      rw [gEnd, if_pos rfl]
      have hsp : s ≤ p' := h.hsp.le
      refine Prod.ext ?_ ?_
      · have : (b.1 : ℤ) = r + (2 * q + 1) * p := by rw [e1, hu1]; ring
        exact_mod_cast this
      · have : (b.2 : ℤ) = ((p' - s : ℕ) : ℤ) := by rw [e2, hv1, Nat.cast_sub hsp]; ring
        exact_mod_cast this
    · right
      refine ⟨by ring, ?_⟩
      have : n0 p p' r s < 0 := by
        rcases lt_or_gt_of_ne hn0 with h' | h'
        · exact h'
        · linarith
      linarith
  · -- `y = −n₀ + iN₀`
    have hy : (p' : ℤ) * b.1 + (p : ℤ) * b.2 = -n0 p p' r s + i * N0 p p' := by
      rw [e1, e2, hu1, hv1]; unfold n0 N0; ring
    rw [hy] at hlo hhi ⊢
    have hi1 : (q : ℤ) + 1 ≤ i := by
      by_contra hc'
      have hc' : i ≤ q := by omega
      have : i * N0 p p' ≤ q * N0 p p' := mul_le_mul_of_nonneg_right hc' hN.le
      linarith
    have hi2 : i ≤ (q : ℤ) + 1 := by
      by_contra hc'
      have hc' : (q : ℤ) + 2 ≤ i := by omega
      have : ((q : ℤ) + 2) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right hc' hN.le
      rcases hσ with rfl | rfl <;> linarith
    have hi : i = (q : ℤ) + 1 := le_antisymm hi2 hi1
    subst hi
    rcases hσ with rfl | rfl
    · right
      refine ⟨by ring, ?_⟩
      have : 0 < n0 p p' r s := by
        rcases lt_or_gt_of_ne hn0 with h' | h'
        · linarith
        · exact h'
      linarith
    · left
      refine ⟨by ring, ?_⟩
      rw [gEnd, if_neg (by norm_num)]
      have hrp : r ≤ p := h.hrp.le
      refine Prod.ext ?_ ?_
      · have : (b.1 : ℤ) = ((p - r : ℕ) : ℤ) := by rw [e1, hu1, Nat.cast_sub hrp]; ring
        exact_mod_cast this
      · have : (b.2 : ℤ) = s + (2 * q + 1) * p' := by rw [e2, hv1]; ring
        exact_mod_cast this

/-- No momentum `τn₁ + tN₀` lies in `(−σ₀n₀ + (q+1)N₀, σ₀n₀ + (q+1)N₀]` when `σ₀n₀ > 0`. -/
theorem Setup.no_mom_gap2 (h : Setup p p' r s) (q : ℕ) (σ τ t : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hτ : τ = 1 ∨ τ = -1) (hpos : 0 < σ * n0 p p' r s)
    (h1 : -σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' < τ * n1 p p' r s + t * N0 p p')
    (h2 : τ * n1 p p' r s + t * N0 p p' ≤ σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') :
    False := by
  have hN := h.N0_pos
  have hd := h.diff_pos
  have hd' := h.diff_lt
  have hs := h.sum_pos
  have hs' := h.sum_lt
  rcases hτ with rfl | rfl
  · have ht : (q : ℤ) + 1 ≤ t := by
      by_contra hc
      have hc : t ≤ q := by omega
      have : t * N0 p p' ≤ q * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      rcases hσ with rfl | rfl <;> linarith
    have : ((q : ℤ) + 1) * N0 p p' ≤ t * N0 p p' := mul_le_mul_of_nonneg_right ht hN.le
    rcases hσ with rfl | rfl <;> linarith
  · have ht : (q : ℤ) + 2 ≤ t := by
      by_contra hc
      have hc : t ≤ q + 1 := by omega
      have : t * N0 p p' ≤ ((q : ℤ) + 1) * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      rcases hσ with rfl | rfl <;> linarith
    have : ((q : ℤ) + 2) * N0 p p' ≤ t * N0 p p' := mul_le_mul_of_nonneg_right ht hN.le
    rcases hσ with rfl | rfl <;> linarith

end Virasoro.ChainEval
