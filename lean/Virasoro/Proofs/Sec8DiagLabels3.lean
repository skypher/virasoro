import Virasoro.Proofs.Sec8DiagLabels

/-!
# Lemma 8.3(iii), first assertion: labels from a node lead to nodes

A label of weight `ν` has `x = ±S_ν` and `y > |x|`; `y ≡ x (mod 2p)`, `y ≡ -x (mod 2p')`, so `y`
lies in the other class `±n₁` or `±n₀` modulo `2pp'`, every positive integer of which (above
`|n₀|`) is `|S|` of a node of layer `≥ 1`; that node has the other parity of layer, and a larger
layer since `|S|` increases with it.
-/

namespace Virasoro

variable {p p' r s : ℕ} {b : ℂ}

/-- `2p ∣ z` and `2p' ∣ z` give `2pp' ∣ z` for coprime `p, p'`. -/
theorem dvd_two_mul_mul_of_coprime (hcop : Nat.Coprime p p') {z : ℤ}
    (h1 : (2 * (p : ℤ)) ∣ z) (h2 : (2 * (p' : ℤ)) ∣ z) : (2 * (p : ℤ) * p') ∣ z := by
  obtain ⟨a, rfl⟩ := h1
  have h3 : (p' : ℤ) ∣ (p : ℤ) * a := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by linarith⟩
  have hcop' : IsCoprime (p' : ℤ) p := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop.symm
  obtain ⟨d, rfl⟩ := hcop'.dvd_of_dvd_mul_left h3
  exact ⟨d, by ring⟩

/-- `|S_ν| ≥ |n₀| = |S_λ|` for every node. -/
theorem nodeS_abs_ge (hset : MinimalSetting p p' r s b) (ν : Node) :
    |nodeS p p' r s (true, 0)| ≤ |nodeS p p' r s ν| := by
  rcases Nat.eq_zero_or_pos ν.2 with h0 | h0
  · obtain ⟨ε, k⟩ := ν
    simp only at h0
    subst h0
    cases ε <;> simp [nodeS, nOrb]
  · rcases Nat.mod_two_eq_zero_or_one ν.2 with h | h
    · have h1 := node_abs_lt (ν := (true, 0)) (ν' := (true, 1)) hset (by simp) (by simp)
      have h2 := node_abs_lt (ν := (true, 1)) (ν' := ν) hset (by simp; omega) (by simp; omega)
      linarith
    · exact (node_abs_lt (ν := (true, 0)) (ν' := ν) hset (by simpa using h0) (by simpa using h)).le

/-- Every positive integer `y > |n₀|` with `y ≡ c (mod 2pp')`, `c ∈ {±n₀, ±n₁}`, is `|S|` of a
node of layer `≥ 1`, of even layer exactly for `c = ±n₀`. -/
theorem node_of_class (hset : MinimalSetting p p' r s b) {y : ℤ}
    (hy : |((p' : ℤ) * r - p * s)| < y) (c : ℤ)
    (hc : c = (p' : ℤ) * r - p * s ∨ c = -((p' : ℤ) * r - p * s) ∨
      c = (p' : ℤ) * r + p * s ∨ c = -((p' : ℤ) * r + p * s))
    (hcl : (2 * (p : ℤ) * p') ∣ y - c) :
    ∃ ν : Node, 1 ≤ ν.2 ∧ |nodeS p p' r s ν| = y ∧
      (ν.2 % 2 = 0 ↔ (c = (p' : ℤ) * r - p * s ∨ c = -((p' : ℤ) * r - p * s))) := by
  obtain ⟨hp2, hp2', -, hr0, hr, hs0, hs, hint, -⟩ := hset
  have a1 : (0 : ℤ) < (p' : ℤ) * r := by exact_mod_cast Nat.mul_pos (by omega) hr0
  have a2 : (0 : ℤ) < (p : ℤ) * s := by exact_mod_cast Nat.mul_pos (by omega) hs0
  have a3 : (p' : ℤ) * r + p * s < p * p' := by exact_mod_cast hint
  have hpp : (0 : ℤ) < p * p' := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hn0 := abs_lt.2 (show -(p * p' : ℤ) < (p' : ℤ) * r - p * s ∧
    (p' : ℤ) * r - p * s < p * p' from ⟨by linarith, by linarith⟩)
  have hle := le_abs_self ((p' : ℤ) * r - p * s)
  have hle' := neg_abs_le ((p' : ℤ) * r - p * s)
  have hab := abs_lt.1 hn0
  obtain ⟨j, hj⟩ := hcl
  have hne1 : (p' : ℤ) * r + p * s ≠ (p' : ℤ) * r - p * s := by linarith
  have hne2 : (p' : ℤ) * r + p * s ≠ -((p' : ℤ) * r - p * s) := by linarith
  have hne3 : -((p' : ℤ) * r + p * s) ≠ (p' : ℤ) * r - p * s := by linarith
  have hne4 : -((p' : ℤ) * r + p * s) ≠ -((p' : ℤ) * r - p * s) := by linarith
  rcases hc with rfl | rfl | rfl | rfl
  · have hj1 : 1 ≤ j := by
      by_contra h
      have : j ≤ 0 := by omega
      nlinarith
    refine ⟨(true, 2 * j.toNat), by omega, ?_, by simp⟩
    have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
    simp only [nodeS, ↓reduceIte, nOrb_even_true, hjn]
    rw [abs_of_pos (by nlinarith)]
    linarith
  · have hj1 : 1 ≤ j := by
      by_contra h
      have : j ≤ 0 := by omega
      nlinarith
    refine ⟨(false, 2 * j.toNat), by omega, ?_, by simp⟩
    have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
    simp only [nodeS, Bool.false_eq_true, ↓reduceIte, nOrb_even_false, hjn, abs_neg]
    rw [abs_of_pos (by nlinarith)]
    linarith
  · have hj0 : 0 ≤ j := by
      by_contra h
      have : j ≤ -1 := by omega
      nlinarith
    refine ⟨(true, 2 * j.toNat + 1), by omega, ?_, ?_⟩
    · have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
      simp only [nodeS, ↓reduceIte, nOrb_odd_true, hjn]
      rw [abs_of_pos (by nlinarith)]
      linarith
    · simp only [hne1, hne2, or_self, iff_false]; omega
  · have hj1 : 1 ≤ j := by
      by_contra h
      have : j ≤ 0 := by omega
      nlinarith
    refine ⟨(false, 2 * (j - 1).toNat + 1), by omega, ?_, ?_⟩
    · have hjn : (((j - 1).toNat : ℕ) : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
      simp only [nodeS, Bool.false_eq_true, ↓reduceIte, nOrb_odd_false, hjn, abs_neg]
      rw [abs_of_pos (by nlinarith)]
      linarith
    · simp only [hne3, hne4, or_self, iff_false]; omega

/-- Lemma 8.3(iii), first assertion. -/
theorem node_labels_iii (hset : MinimalSetting p p' r s b) (ν : Node) (g : Label) (hg1 : 0 < g.1)
    (hg2 : 0 < g.2) (hw : kacHL g b = nodeWt p p' r s ν) :
    ∃ ν' : Node, ν.2 < ν'.2 ∧ (ν'.2 - ν.2) % 2 = 1 ∧
      kacHL g b + (g.lvl : ℂ) = nodeWt p p' r s ν' := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  have hcop := hset.2.2.1
  have a1 : (0 : ℤ) < (p' : ℤ) * r := by exact_mod_cast Nat.mul_pos hp' hset.2.2.2.1
  have a2 : (0 : ℤ) < (p : ℤ) * s := by exact_mod_cast Nat.mul_pos hp hset.2.2.2.2.2.1
  rw [kacHL_eq_momWt hp hp' hb, nodeWt_eq, momWt_eq_iff hp hp'] at hw
  have hxy : |(p' : ℤ) * g.1 - p * g.2| < (p' : ℤ) * g.1 + p * g.2 := by
    have h1 : (0 : ℤ) < p' * g.1 := by exact_mod_cast Nat.mul_pos hp' hg1
    have h2 : (0 : ℤ) < p * g.2 := by exact_mod_cast Nat.mul_pos hp hg2
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  obtain ⟨m, hm⟩ := nodeS_mod (p := p) (p' := p') (r := r) (s := s) ν
  have hxS := sq_eq_sq_iff_eq_or_eq_neg.1 hw
  have hSabs : |nodeS p p' r s ν| = |(p' : ℤ) * g.1 - p * g.2| := by
    rcases hxS with h | h <;> rw [h]; simp
  -- the class of y
  have key : ∃ c : ℤ, (c = (p' : ℤ) * r - p * s ∨ c = -((p' : ℤ) * r - p * s) ∨
      c = (p' : ℤ) * r + p * s ∨ c = -((p' : ℤ) * r + p * s)) ∧
      (2 * (p : ℤ) * p') ∣ ((p' : ℤ) * g.1 + p * g.2) - c ∧
      (ν.2 % 2 = 0 ↔ (c = (p' : ℤ) * r + p * s ∨ c = -((p' : ℤ) * r + p * s))) := by
    rcases Nat.mod_two_eq_zero_or_one ν.2 with hpar | hpar
    · simp only [hpar, ↓reduceIte] at hm
      rcases hxS with h | h
      · refine ⟨(p' : ℤ) * r + p * s, Or.inr (Or.inr (Or.inl rfl)), dvd_two_mul_mul_of_coprime hcop
          ⟨(g.2 : ℤ) - s + m * p', by linarith⟩ ⟨(g.1 : ℤ) - r - m * p, by linarith⟩,
          by simp [hpar]⟩
      · refine ⟨-((p' : ℤ) * r + p * s), Or.inr (Or.inr (Or.inr rfl)), dvd_two_mul_mul_of_coprime hcop
          ⟨(g.2 : ℤ) + s - m * p', by linarith⟩ ⟨(g.1 : ℤ) + r + m * p, by linarith⟩,
          by simp [hpar]⟩
    · simp only [hpar, one_ne_zero, ↓reduceIte] at hm
      have hne1 : (p' : ℤ) * r - p * s ≠ (p' : ℤ) * r + p * s := by linarith
      have hne2 : (p' : ℤ) * r - p * s ≠ -((p' : ℤ) * r + p * s) := by linarith
      have hne3 : -((p' : ℤ) * r - p * s) ≠ (p' : ℤ) * r + p * s := by linarith
      have hne4 : -((p' : ℤ) * r - p * s) ≠ -((p' : ℤ) * r + p * s) := by linarith
      rcases hxS with h | h
      · refine ⟨(p' : ℤ) * r - p * s, Or.inl rfl, dvd_two_mul_mul_of_coprime hcop
          ⟨(g.2 : ℤ) + s + m * p', by linarith⟩ ⟨(g.1 : ℤ) - r - m * p, by linarith⟩, ?_⟩
        simp only [hpar, one_ne_zero, false_iff, hne1, hne2, or_self, not_false_eq_true]
      · refine ⟨-((p' : ℤ) * r - p * s), Or.inr (Or.inl rfl), dvd_two_mul_mul_of_coprime hcop
          ⟨(g.2 : ℤ) - s - m * p', by linarith⟩ ⟨(g.1 : ℤ) + r + m * p, by linarith⟩, ?_⟩
        simp only [hpar, one_ne_zero, false_iff, hne3, hne4, or_self, not_false_eq_true]
  obtain ⟨c, hc, hcl, hcpar⟩ := key
  have hS0 : |nodeS p p' r s (true, 0)| = |((p' : ℤ) * r - p * s)| := by simp [nodeS, nOrb]
  have hn0 : |((p' : ℤ) * r - p * s)| < (p' : ℤ) * g.1 + p * g.2 := by
    have := nodeS_abs_ge hset ν
    rw [hS0, hSabs] at this
    linarith
  obtain ⟨ν', -, hν'y, hν'par⟩ := node_of_class hset hn0 c hc hcl
  have hexcl : ¬ ((c = (p' : ℤ) * r - p * s ∨ c = -((p' : ℤ) * r - p * s)) ∧
      (c = (p' : ℤ) * r + p * s ∨ c = -((p' : ℤ) * r + p * s))) := by
    rintro ⟨h1 | h1, h2 | h2⟩ <;> rw [h1] at h2 <;> linarith
  have hpar : (ν'.2 % 2 = 0 ↔ ¬ ν.2 % 2 = 0) := by
    rw [hν'par, hcpar]
    constructor
    · intro h1 h2; exact hexcl ⟨h1, h2⟩
    · intro h; rcases hc with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd (Or.inl h1) h
      · exact absurd (Or.inr h1) h
  have hlt : ν.2 < ν'.2 := by
    by_contra hle
    push_neg at hle
    have hlt' : ν'.2 < ν.2 := by
      rcases Nat.lt_or_ge ν'.2 ν.2 with h | h
      · exact h
      · exfalso
        have : ν'.2 = ν.2 := le_antisymm hle h
        rw [this] at hpar
        by_cases hh : ν.2 % 2 = 0
        · exact hpar.1 hh hh
        · exact hh (hpar.2 hh)
    have hodd' : (ν.2 - ν'.2) % 2 = 1 := by omega
    have := node_abs_lt hset hlt' hodd'
    rw [hν'y, hSabs] at this
    linarith
  refine ⟨ν', hlt, by omega, ?_⟩
  rw [kacH_add_lvl hp hp' hb, nodeWt_eq, momWt_eq_iff hp hp', ← hν'y, sq_abs]

end Virasoro
