import Virasoro.Proofs.Naturality
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Degree in the internal weight of the normal-ordering step

Over `𝔽[X]` with `h = X`: a positive mode applied to a word produces coefficients of degree at
most `1` in the internal weight, and a factor of the weight is produced only when the length of
the word drops.  The terms of degree one with exactly one deleted letter come from the
contraction of `L_k` with an equal letter `L_{-k}`, with coefficient `2k`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem centralTerm_C (c₀ : 𝔽) (k : ℤ) :
    centralTerm (C c₀ : 𝔽[X]) k = C (centralTerm c₀ k) :=
  (map_centralTerm (C : 𝔽 →+* 𝔽[X]) c₀ k).symm

/-- Degree and length bookkeeping for one step: every term `(w', a')` of `L_k w` has
`deg a' ≤ 1` and `deg a' + |w'| ≤ |w|`, plus one if `k ≤ 0`. -/
theorem actWord_degree (c₀ : 𝔽) : ∀ (w : List ℕ) (k : ℤ),
    ∀ t ∈ actWord (C c₀ : 𝔽[X]) X k w,
      t.2.natDegree ≤ 1 ∧ t.2.natDegree + t.1.length ≤ w.length + (if 0 < k then 0 else 1)
  | [], k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2
    · simp only [List.mem_singleton] at ht
      subst ht
      simp [show ¬ (0 < k) by omega]
    · simp only [List.mem_singleton] at ht
      subst ht
      simp [show ¬ (0 < k) by omega]
    · simp at ht
  | y :: w, k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2 h3
    · simp only [List.mem_singleton] at ht
      subst ht
      simp [show ¬ (0 < k) by omega]
    · simp only [List.mem_singleton] at ht
      subst ht
      have hd : (X + (((y + w.sum : ℕ) : 𝔽[X]))).natDegree ≤ 1 := by
        rw [← C_eq_natCast]
        exact (natDegree_X_add_C _).le
      simp only [show ¬ (0 < k) by omega, if_false, List.length_cons]
      exact ⟨hd, by omega⟩
    · have hk : 0 < k := by omega
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at ht
      rcases ht with (⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩) | rfl
      · have := actWord_degree c₀ w k t' ht'
        simp only [hk, if_true, add_zero] at this ⊢
        simp only [List.length_cons]
        exact ⟨this.1, by omega⟩
      · have := actWord_degree c₀ w (k - y) t' ht'
        have hmul : (((k + y : ℤ) : 𝔽[X]) * t'.2).natDegree ≤ t'.2.natDegree := by
          rw [← C_eq_intCast]
          exact natDegree_C_mul_le _ _
        simp only [hk, if_true, add_zero, List.length_cons]
        refine ⟨le_trans hmul this.1, ?_⟩
        have h2' := this.2
        split_ifs at h2' <;> omega
      · rw [centralTerm_C]
        simp [hk]
    · have hk : 0 < k := by omega
      simp only [List.append_nil, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
      · have := actWord_degree c₀ w k t' ht'
        simp only [hk, if_true, add_zero] at this ⊢
        simp only [List.length_cons]
        exact ⟨this.1, by omega⟩
      · have := actWord_degree c₀ w (k - y) t' ht'
        have hmul : (((k + y : ℤ) : 𝔽[X]) * t'.2).natDegree ≤ t'.2.natDegree := by
          rw [← C_eq_intCast]
          exact natDegree_C_mul_le _ _
        simp only [hk, if_true, add_zero, List.length_cons]
        refine ⟨le_trans hmul this.1, ?_⟩
        have h2' := this.2
        split_ifs at h2' <;> omega

/-- For a positive mode: `deg a' ≤ 1` and `deg a' + |w'| ≤ |w|`. -/
theorem actWord_degree_pos (c₀ : 𝔽) (w : List ℕ) {k : ℤ} (hk : 0 < k)
    {t : List ℕ × 𝔽[X]} (ht : t ∈ actWord (C c₀ : 𝔽[X]) X k w) :
    t.2.natDegree ≤ 1 ∧ t.2.natDegree + t.1.length ≤ w.length := by
  have := actWord_degree c₀ w k t ht
  simpa [hk] using this

/-- The words obtained from `w` by deleting one occurrence of the letter `k`. -/
def delOne (k : ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | y :: w => (if y = k then [w] else []) ++ (delOne k w).map fun u => y :: u

/-- `L_0` multiplies a word by a polynomial of the form `X + const`. -/
theorem actWord_zero (c₀ : 𝔽) (w : List ℕ) :
    ∃ a : 𝔽[X], actWord (C c₀ : 𝔽[X]) X 0 w = [(w, a)] ∧ a.coeff 1 = 1 := by
  cases w with
  | nil => exact ⟨X, by simp [actWord], by simp⟩
  | cons y w =>
    refine ⟨X + ((y + w.sum : ℕ) : 𝔽[X]), by simp [actWord], ?_⟩
    rw [← C_eq_natCast]
    simp

theorem actWord_neg (c₀ : 𝔽) (w : List ℕ) {k : ℤ} (hk : k < 0) :
    actWord (C c₀ : 𝔽[X]) X k w = [(k.natAbs :: w, 1)] := by
  cases w with
  | nil => simp [actWord, hk]
  | cons y w => simp [actWord, hk]

/-- The degree-one part of `L_k w` with exactly one deleted letter: it is the sum over the
occurrences of `k` in `w` of `2k` times the word with that occurrence deleted. -/
theorem actWord_top (c₀ : 𝔽) : ∀ (w : List ℕ) (k : ℕ), 0 < k → ∀ φ : List ℕ → 𝔽,
    ((actWord (C c₀ : 𝔽[X]) X (k : ℤ) w).map fun t =>
        if t.1.length + 1 = w.length then t.2.coeff 1 * φ t.1 else 0).sum =
      ((delOne k w).map fun u => 2 * (k : 𝔽) * φ u).sum
  | [], k, hk, φ => by
    have : ¬ ((k : ℤ) < 0) := by omega
    have h2 : ¬ ((k : ℤ) = 0) := by omega
    simp [actWord, delOne, this, h2]
  | y :: w, k, hk, φ => by
    have h1 : ¬ ((k : ℤ) < 0) := by omega
    have h2 : ¬ ((k : ℤ) = 0) := by omega
    have ih := actWord_top c₀ w k hk (fun u => φ (y :: u))
    -- first part: `L_k` passes `L_{-y}`
    have e1 : ((actWord (C c₀ : 𝔽[X]) X (k : ℤ) w).map fun t : List ℕ × 𝔽[X] =>
          if t.1.length + 1 + 1 = w.length + 1 then t.2.coeff 1 * φ (y :: t.1) else 0).sum =
        ((delOne k w).map fun u => 2 * (k : 𝔽) * φ (y :: u)).sum := by
      rw [← ih]
      congr 1
      apply List.map_congr_left
      intro t _
      simp
    -- second part: the commutator `(k + y) L_{k-y}`
    have e2 : ((actWord (C c₀ : 𝔽[X]) X ((k : ℤ) - y) w).map fun t : List ℕ × 𝔽[X] =>
          if t.1.length + 1 = w.length + 1 then
            ((((k : ℤ) + y : ℤ) : 𝔽[X]) * t.2).coeff 1 * φ t.1 else 0).sum =
        if y = k then 2 * (k : 𝔽) * φ w else 0 := by
      rcases lt_trichotomy y k with hlt | heq | hgt
      · -- `k - y > 0`: no tight term of degree one
        rw [if_neg (by omega)]
        apply List.sum_eq_zero
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        have hd := actWord_degree_pos c₀ w (show (0 : ℤ) < (k : ℤ) - y by omega) ht
        split_ifs with hlen
        · have h0 : t.2.natDegree = 0 := by omega
          have : ((((k : ℤ) + y : ℤ) : 𝔽[X]) * t.2).natDegree < 1 := by
            have hmul : ((((k : ℤ) + y : ℤ) : 𝔽[X]) * t.2).natDegree ≤ t.2.natDegree := by
              rw [← C_eq_intCast]
              exact natDegree_C_mul_le _ _
            omega
          rw [coeff_eq_zero_of_natDegree_lt this, zero_mul]
        · rfl
      · subst heq
        have hz : (y : ℤ) - y = 0 := by omega
        obtain ⟨a, ha, ha1⟩ := actWord_zero c₀ w
        rw [hz, if_pos rfl, ha]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, if_true]
        rw [← C_eq_intCast, coeff_C_mul, ha1]
        push_cast
        ring
      · -- `k - y < 0`: a letter is lowered, no deletion
        rw [if_neg (by omega), actWord_neg c₀ w (show (k : ℤ) - y < 0 by omega)]
        simp
    unfold actWord
    simp only [h1, h2, if_false, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.length_cons]
    rw [e1, e2]
    by_cases hky : (k : ℤ) = (y : ℤ)
    · have hyk : y = k := by omega
      rw [if_pos hky, if_pos hyk]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, if_true]
      rw [centralTerm_C, coeff_C, if_neg (by norm_num), zero_mul, add_zero]
      simp [delOne, hyk, Function.comp_def]
      ring
    · have hyk : ¬ y = k := by omega
      rw [if_neg hky, if_neg hyk]
      simp [delOne, hyk, Function.comp_def]

end Virasoro
