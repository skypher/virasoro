import Virasoro.Statements.Sec8Boundary
import Virasoro.Proofs.Sec8DiagLabels

/-!
# Section 8.2: arithmetic of the boundary nodes

`π_{2j} = j`, `π_{2j+1} = -(j+1)`; `M_{2j} = x₀ + jN₀`, `M_{2j+1} = (j+1)N₀ - x₀`; the `M_k` increase
strictly, `T_k > 0` for even `k` and `T_k < 0` for odd `k`; the positive elements of
`±x₀ + N₀ℤ` are the `M_k`; `μ_k = λ + ℓ_k` with `ℓ_k = π_k (x₀ + pp' π_k)`.
-/

namespace Virasoro

variable {p p' x₀ : ℕ} {b : ℂ}

theorem bPi_even (j : ℕ) : bPi (2 * j) = j := by
  unfold bPi
  rw [pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow, one_mul,
    show (2 * j + 1) / 2 = j by omega]

theorem bPi_odd (j : ℕ) : bPi (2 * j + 1) = -((j : ℤ) + 1) := by
  unfold bPi
  rw [pow_succ, pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow, one_mul,
    show (2 * j + 1 + 1) / 2 = j + 1 by omega]
  push_cast; ring

theorem bT_even (j : ℕ) : bT p p' x₀ (2 * j) = x₀ + j * (2 * p * p') := by
  unfold bT; rw [bPi_even]

theorem bT_odd (j : ℕ) : bT p p' x₀ (2 * j + 1) = x₀ - ((j : ℤ) + 1) * (2 * p * p') := by
  unfold bT; rw [bPi_odd]; ring

section Setting

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem bT_pos_even (j : ℕ) : 0 < bT p p' x₀ (2 * j) := by
  have := hB.2.2.2.1
  rw [bT_even]
  have : (0 : ℤ) ≤ (j : ℤ) * (2 * p * p') := by positivity
  omega

theorem bT_neg_odd (j : ℕ) : bT p p' x₀ (2 * j + 1) < 0 := by
  have h1 := hB.2.2.2.2.1
  have h1' : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
  rw [bT_odd]
  have : (0 : ℤ) ≤ (j : ℤ) * (2 * p * p') := by positivity
  have : (0 : ℤ) < (p : ℤ) * p' := by
    have := hB.1; have := hB.2.1; positivity
  nlinarith

theorem bT_ne (k : ℕ) : bT p p' x₀ k ≠ 0 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · exact (bT_pos_even hB j).ne'
  · exact (bT_neg_odd hB j).ne

/-- `M_k = sgn(T_k) T_k`. -/
theorem bM_sgn (k : ℕ) :
    (bM p p' x₀ k : ℤ) = (if 0 < bT p p' x₀ k then 1 else -1) * bT p p' x₀ k := by
  unfold bM
  split_ifs with h
  · rw [one_mul]; exact Int.natAbs_of_nonneg h.le
  · push_neg at h
    rw [Int.ofNat_natAbs_of_nonpos h]; ring

theorem bM_int (k : ℕ) : (bM p p' x₀ k : ℤ) =
    if k % 2 = 0 then (x₀ : ℤ) + ((k / 2 : ℕ) : ℤ) * (2 * p * p')
    else (((k + 1) / 2 : ℕ) : ℤ) * (2 * p * p') - x₀ := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [if_pos (by omega), bM_sgn hB, if_pos (bT_pos_even hB j), one_mul, bT_even,
      show 2 * j / 2 = j by omega]
  · rw [if_neg (by omega), bM_sgn hB, if_neg (not_lt.2 (bT_neg_odd hB j).le), bT_odd,
      show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    push_cast; ring

theorem bM_succ (k : ℕ) : (bM p p' x₀ k : ℤ) < bM p p' x₀ (k + 1) := by
  have h0 := hB.2.2.2.1
  have h1 := hB.2.2.2.2.1
  have h1' : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
  have h0' : (0 : ℤ) < x₀ := by exact_mod_cast h0
  rw [bM_int hB, bM_int hB]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [if_pos (by omega), if_neg (by omega), show 2 * j / 2 = j by omega,
      show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    push_cast; nlinarith
  · rw [if_neg (by omega), if_pos (by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    push_cast; nlinarith

theorem bM_strictMono : StrictMono (bM p p' x₀) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact_mod_cast bM_succ hB k

theorem bM_zero : (bM p p' x₀ 0 : ℤ) = x₀ := by
  rw [bM_int hB, if_pos rfl]; simp

/-- The positive elements of `x₀ + N₀ℤ` and of `-x₀ + N₀ℤ` are the `M_k`. -/
theorem exists_bM {y : ℤ} (hy : 0 < y) (h : (2 * p * p' : ℤ) ∣ y - x₀ ∨ (2 * p * p' : ℤ) ∣ y + x₀) :
    ∃ m : ℕ, y = bM p p' x₀ m := by
  have h0 := hB.2.2.2.1
  have h1 := hB.2.2.2.2.1
  have h1' : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
  have hN : (0 : ℤ) < 2 * p * p' := by have := hB.1; have := hB.2.1; positivity
  rcases h with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hq0 : 0 ≤ q := by
      by_contra hc; push_neg at hc
      have : (2 * p * p' : ℤ) * q ≤ (2 * p * p') * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) hN.le
      have : (x₀ : ℤ) < 2 * p * p' := by linarith
      linarith
    refine ⟨2 * q.toNat, ?_⟩
    rw [bM_int hB, if_pos (by omega), show 2 * q.toNat / 2 = q.toNat by omega, Int.toNat_of_nonneg hq0]
    linarith
  · have hq1 : 1 ≤ q := by
      by_contra hc; push_neg at hc
      have : (2 * p * p' : ℤ) * q ≤ (2 * p * p') * 0 :=
        mul_le_mul_of_nonneg_left (by omega) hN.le
      have : (0 : ℤ) ≤ x₀ := by positivity
      linarith
    refine ⟨2 * (q.toNat - 1) + 1, ?_⟩
    rw [bM_int hB, if_neg (by omega), show (2 * (q.toNat - 1) + 1 + 1) / 2 = q.toNat by omega,
      Int.toNat_of_nonneg (by omega)]
    linarith

/-- `μ_k = λ + ℓ_k`. -/
theorem bWt_add_lev (k : ℕ) : bWt p p' x₀ k = bWt p p' x₀ 0 + (bLev p p' x₀ k : ℂ) := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have h0 := hB.2.2.2.1
  have hlev : (bLev p p' x₀ k : ℤ) = bPi k * ((x₀ : ℤ) + p * p' * bPi k) := by
    unfold bLev
    apply Int.toNat_of_nonneg
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [bPi_even]; positivity
    · rw [bPi_odd]
      have h1 := hB.2.2.2.2.1
      have h1' : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
      have hj : (0 : ℤ) ≤ (p : ℤ) * p' * j := by positivity
      rw [show -((j : ℤ) + 1) * ((x₀ : ℤ) + p * p' * -((j : ℤ) + 1)) =
        ((j : ℤ) + 1) * ((p : ℤ) * p' * j + p * p' - x₀) by ring]
      exact mul_nonneg (by positivity) (by linarith)
  have hsq : ((bM p p' x₀ k : ℤ) : ℂ) ^ 2 = ((bT p p' x₀ k : ℤ) : ℂ) ^ 2 := by
    have : (bM p p' x₀ k : ℤ) ^ 2 = bT p p' x₀ k ^ 2 := by
      rw [bM_sgn hB]; split_ifs <;> ring
    exact_mod_cast this
  have hl : ((bLev p p' x₀ k : ℕ) : ℂ) = ((bPi k : ℤ) : ℂ) * ((x₀ : ℂ) + p * p' * (bPi k : ℂ)) := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hlev
    push_cast at this
    exact this
  unfold bWt momWt
  rw [show ((bM p p' x₀ k : ℕ) : ℤ) = (bM p p' x₀ k : ℤ) from rfl]
  push_cast
  rw [show ((bM p p' x₀ k : ℕ) : ℂ) = (((bM p p' x₀ k : ℕ) : ℤ) : ℂ) by push_cast; rfl, hsq,
    show ((bM p p' x₀ 0 : ℕ) : ℂ) = (((bM p p' x₀ 0 : ℕ) : ℤ) : ℂ) by push_cast; rfl,
    bM_zero hB, hl]
  unfold bT
  push_cast
  field_simp
  ring

theorem bLev_strictMono : StrictMono (bLev p p' x₀) := by
  intro i k hik
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have hM := bM_strictMono hB hik
  have e1 := bWt_add_lev hB i
  have e2 := bWt_add_lev hB k
  -- `4pp' ℓ_k = M_k² - x₀²`
  have hsq : ∀ m : ℕ, (4 * p * p' * bLev p p' x₀ m : ℤ) = (bM p p' x₀ m : ℤ) ^ 2 - (x₀ : ℤ) ^ 2 := by
    intro m
    have hlev : (bLev p p' x₀ m : ℤ) = bPi m * ((x₀ : ℤ) + p * p' * bPi m) := by
      unfold bLev
      apply Int.toNat_of_nonneg
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · rw [bPi_even]; positivity
      · rw [bPi_odd]
        have h1 := hB.2.2.2.2.1
        have h1' : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
        have hj : (0 : ℤ) ≤ (p : ℤ) * p' * j := by positivity
        rw [show -((j : ℤ) + 1) * ((x₀ : ℤ) + p * p' * -((j : ℤ) + 1)) =
          ((j : ℤ) + 1) * ((p : ℤ) * p' * j + p * p' - x₀) by ring]
        exact mul_nonneg (by positivity) (by linarith)
    rw [hlev]
    have : (bM p p' x₀ m : ℤ) ^ 2 = bT p p' x₀ m ^ 2 := by rw [bM_sgn hB]; split_ifs <;> ring
    rw [this]; unfold bT; ring
  have a1 := hsq i
  have a2 := hsq k
  have hMi : (0 : ℤ) ≤ bM p p' x₀ i := by positivity
  have hMk : (bM p p' x₀ i : ℤ) < bM p p' x₀ k := by exact_mod_cast hM
  have : (4 * p * p' * bLev p p' x₀ i : ℤ) < 4 * p * p' * bLev p p' x₀ k := by nlinarith
  have h4 : (0 : ℤ) < 4 * p * p' := by positivity
  have := lt_of_mul_lt_mul_left this h4.le
  exact_mod_cast this

end Setting

end Virasoro
