import Virasoro.Proofs.Sec6ChainOddMinus

/-!
# Proposition 6.7, the evaluation for `k = 2q + 2`: levels and first steps (paper.tex l.1157–1169)

For `k = 2j`, `j = q + 1`, the endpoints are `±n₀ + jN₀` (`ℓ^±_{2j} = j(jpp' ± n₀)`), of the class
of `n₀`; the first steps of the chains of that level are the `g_i`, `−j ≤ i ≤ j−1` (l.1159–1160),
with no condition `n₁ < pp'`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

theorem Setup.n0_ne (h : Setup p p' r s) : n0 p p' r s ≠ 0 := by
  intro h0
  unfold n0 at h0
  have h1 : (p : ℤ) ∣ (p' : ℤ) * r := ⟨s, by linarith⟩
  have h2 : (p : ℤ) ∣ r := h.isCoprime.dvd_of_dvd_mul_left h1
  have h3 : p ∣ r := by exact_mod_cast h2
  have := Nat.le_of_dvd h.hr h3
  have := h.hrp
  omega

theorem Setup.two_n0_lt (h : Setup p p' r s) : 2 * n0 p p' r s < N0 p p' := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hs : (0 : ℤ) < s := by exact_mod_cast h.hs
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have hp' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  unfold n0 N0
  nlinarith

theorem Setup.neg_two_n0_lt (h : Setup p p' r s) : -(2 * n0 p p' r s) < N0 p p' := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hsp : (s : ℤ) < p' := by exact_mod_cast h.hsp
  have hp' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  unfold n0 N0
  nlinarith

/-- `2n₀ ≠ iN₀` for every integer `i`. -/
theorem Setup.two_n0_ne_mul (h : Setup p p' r s) (i : ℤ) : 2 * n0 p p' r s ≠ i * N0 p p' := by
  intro he
  have hN := h.N0_pos
  have h1 := h.two_n0_lt
  have h2 := h.neg_two_n0_lt
  have hn := h.n0_ne
  rcases lt_trichotomy i 0 with hi | hi | hi
  · have : i * N0 p p' ≤ -1 * N0 p p' := mul_le_mul_of_nonneg_right (by omega) hN.le
    linarith
  · subst hi
    apply hn
    linarith
  · have : 1 * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right (by omega) hN.le
    linarith

/-- The value of `ℓ^σ_{2(q+1)}` with `σ = ±1`: `(q+1)((q+1)pp' + σn₀)`, and
`2N₀ ℓ = (σn₀ + (q+1)N₀)² − n₀²`. -/
theorem Setup.ell_even (_h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (L : ℕ) (hL : (L : ℤ) = ((q : ℤ) + 1) * (((q : ℤ) + 1) * p * p' + σ * n0 p p' r s)) :
    2 * N0 p p' * (L : ℤ) = (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - n0 p p' r s ^ 2 := by
  rw [hL]
  unfold N0
  rcases hσ with rfl | rfl <;> ring

theorem ellPlus_even (p p' r s q : ℕ) (h : Setup p p' r s) :
    ((ellPlus p p' r s (2 * q + 2) : ℕ) : ℤ) =
      ((q : ℤ) + 1) * (((q : ℤ) + 1) * p * p' + 1 * n0 p p' r s) := by
  have h1 := h.neg_two_n0_lt
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  unfold ellPlus
  rw [if_pos (by omega), show (2 * q + 2) / 2 = q + 1 by omega]
  rw [Int.toNat_of_nonneg]
  · unfold n0
    push_cast
    ring
  · unfold n0 N0 at *
    push_cast
    have hpp : (0 : ℤ) ≤ (q : ℤ) * p * p' := by positivity
    apply mul_nonneg (by positivity)
    nlinarith

theorem ellMinus_even (p p' r s q : ℕ) (h : Setup p p' r s) :
    ((ellMinus p p' r s (2 * q + 2) : ℕ) : ℤ) =
      ((q : ℤ) + 1) * (((q : ℤ) + 1) * p * p' + (-1) * n0 p p' r s) := by
  have h1 := h.two_n0_lt
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  unfold ellMinus
  rw [if_pos (by omega), show (2 * q + 2) / 2 = q + 1 by omega]
  rw [Int.toNat_of_nonneg]
  · unfold n0
    push_cast
    ring
  · unfold n0 N0 at *
    push_cast
    have hpp : (0 : ℤ) ≤ (q : ℤ) * p * p' := by positivity
    apply mul_nonneg (by positivity)
    nlinarith

/-- The first steps at the level `L` of `±n₀ + (q+1)N₀` are the `g_i`, `−(q+1) ≤ i ≤ q`. -/
theorem Setup.mem_firstSteps_even (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (L : ℕ) (hL : 2 * N0 p p' * (L : ℤ) =
      (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - n0 p p' r s ^ 2) (i : ℤ) :
    gL p p' r s i ∈ firstSteps p p' L (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) ↔
      -((q : ℤ) + 1) ≤ i ∧ i ≤ q := by
  rw [h.gL_mem]
  have hN := h.N0_pos
  have hn := h.n1_pos
  have hd := h.diff_pos
  have hd' := h.diff_lt
  have hs := h.sum_pos
  have hs' := h.sum_lt
  have h1 := h.two_n0_lt
  have h2 := h.neg_two_n0_lt
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have key : (n1 p p' r s + i * N0 p p') ^ 2 ≤ n0 p p' r s ^ 2 + 2 * N0 p p' * (L : ℤ) ↔
      (n1 p p' r s + i * N0 p p') ^ 2 ≤ (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 := by
    rw [hL]
    constructor <;> intro hh <;> linarith
  rw [key]
  have hb : 0 ≤ σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' := by
    have : N0 p p' ≤ ((q : ℤ) + 1) * N0 p p' := by nlinarith
    rcases hσ with rfl | rfl <;> linarith
  constructor
  · intro hh
    obtain ⟨h3, h4⟩ := abs_le_of_sq_le_sq' hh hb
    constructor
    · by_contra hc
      have hc : i + ((q : ℤ) + 1) ≤ -1 := by omega
      have : (i + ((q : ℤ) + 1)) * N0 p p' ≤ -1 * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      rcases hσ with rfl | rfl <;> linarith
    · by_contra hc
      have hc : (q : ℤ) + 1 ≤ i := by omega
      have : ((q : ℤ) + 1) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      rcases hσ with rfl | rfl <;> linarith
  · rintro ⟨h3, h4⟩
    have h5 : i * N0 p p' ≤ q * N0 p p' := mul_le_mul_of_nonneg_right h4 hN.le
    have h6 : -((q : ℤ) + 1) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right h3 hN.le
    apply sq_le_sq'
    · rcases hσ with rfl | rfl <;> linarith
    · rcases hσ with rfl | rfl <;> linarith

end Virasoro.ChainEval
