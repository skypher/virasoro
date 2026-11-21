import Virasoro.Proofs.SingularDegreeD

/-!
# Lemma 5.7 of `paper.tex` at 70bac53: torus norm of a singular vector

The second assertion (degree `2ℓ` in `d`, leading coefficient `a_w²`) is proved here for every
vector whose `L_{-1}^ℓ`-coefficient `a_w` is nonzero, from the degree bound on the torus
entries: in `⟨w|V_d(1)|w⟩ = ∑ a_Y a_{Y'} ρ_ℓ(c,h,d)_{Y,Y'}` the only pair with
`ℓ(Y) + ℓ(Y') = 2ℓ` is `Y = Y' = (1^ℓ)`.  The first assertion (`a_w ≠ 0` for a singular vector)
is the frozen sub-statement `Stmt_sub_singular_ones_coeff`.
-/

namespace Virasoro

open Polynomial

/-- A word of positive letters is no longer than its sum. -/
theorem length_le_sum_of_pos : ∀ w : List ℕ, (∀ y ∈ w, 0 < y) → w.length ≤ w.sum
  | [], _ => by simp
  | y :: w, hw => by
    have h1 := length_le_sum_of_pos w fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have h2 := hw y List.mem_cons_self
    simp only [List.length_cons, List.sum_cons]
    omega

/-- A word of positive letters whose length equals its sum consists of ones. -/
theorem eq_replicate_of_length_eq_sum : ∀ w : List ℕ, (∀ y ∈ w, 0 < y) → w.length = w.sum →
    w = List.replicate w.length 1
  | [], _, _ => by simp
  | y :: w, hw, h => by
    have hw' : ∀ z ∈ w, 0 < z := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have h1 := length_le_sum_of_pos w hw'
    have h2 := hw y List.mem_cons_self
    simp only [List.length_cons, List.sum_cons] at h
    have hy : y = 1 := by omega
    have hlen : w.length = w.sum := by omega
    have ih := eq_replicate_of_length_eq_sum w hw' hlen
    rw [List.length_cons, List.replicate_succ, hy, ← ih]

theorem word_sum_eq {N : ℕ} (Y : Nat.Partition N) : Y.word.sum = N := by
  have h : ((Y.word : List ℕ) : Multiset ℕ).sum = N := by rw [Verma.word_coe, Y.parts_sum]
  rwa [Multiset.sum_coe] at h

theorem word_length_le {N : ℕ} (Y : Nat.Partition N) : Y.word.length ≤ N := by
  have := length_le_sum_of_pos Y.word (Verma.posWord_word Y)
  rwa [word_sum_eq] at this

theorem word_length_lt {N : ℕ} (Y : Nat.Partition N) (hY : Y ≠ onesPartition N) :
    Y.word.length < N := by
  rcases (word_length_le Y).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hY
    apply Nat.Partition.ext
    have h1 := eq_replicate_of_length_eq_sum Y.word (Verma.posWord_word Y)
      (by rw [word_sum_eq, h])
    rw [← Verma.word_coe, ← Verma.word_coe, h1, h, word_onesPartition]

/-- The torus norm of a vector with level-`ℓ` coordinates `p` has degree at most `2ℓ` in `d`,
and its coefficient of `d^{2ℓ}` is the square of the coefficient of `L_{-1}^ℓ`. -/
theorem torusPolyForm_top (c h : ℂ) (ℓ : ℕ) (p : Nat.Partition ℓ → ℂ) :
    (torusPolyForm c h p).natDegree ≤ 2 * ℓ ∧
    (torusPolyForm c h p).coeff (2 * ℓ) = p (onesPartition ℓ) ^ 2 := by
  have hterm : ∀ Y Y' : Nat.Partition ℓ,
      (C (p Y) * (torus (C c) (C h) (X : ℂ[X]) ℓ Y Y' * C (p Y'))).natDegree ≤ 2 * ℓ ∧
      (C (p Y) * (torus (C c) (C h) (X : ℂ[X]) ℓ Y Y' * C (p Y'))).coeff (2 * ℓ) =
        if Y = onesPartition ℓ ∧ Y' = onesPartition ℓ then p Y * p Y' else 0 := by
    intro Y Y'
    obtain ⟨h1, h2⟩ := torusWord_degree_d c h Y.word Y'.word
    have hY := word_length_le Y
    have hY' := word_length_le Y'
    have hdeg : (C (p Y) * (torus (C c) (C h) (X : ℂ[X]) ℓ Y Y' * C (p Y'))).natDegree ≤
        Y.word.length + Y'.word.length := by
      refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_C_le _ _).trans ?_)
      simpa [torus] using h1
    refine ⟨hdeg.trans (by omega), ?_⟩
    split_ifs with hones
    · obtain ⟨rfl, rfl⟩ := hones
      have hlen : (onesPartition ℓ).word.length = ℓ := by simp [word_onesPartition]
      have h2' : (torus (C c) (C h) (X : ℂ[X]) ℓ (onesPartition ℓ) (onesPartition ℓ)).coeff
          (2 * ℓ) = 1 := by
        have : 2 * ℓ = (onesPartition ℓ).word.length + (onesPartition ℓ).word.length := by
          rw [hlen]; ring
        rw [this]
        simp only [torus, Matrix.of_apply]
        rw [h2]
        simp [wprod, word_onesPartition]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, h2']
      ring
    · refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg ?_)
      by_cases hY1 : Y = onesPartition ℓ
      · have hY'1 : Y' ≠ onesPartition ℓ := fun h => hones ⟨hY1, h⟩
        have := word_length_lt Y' hY'1
        omega
      · have := word_length_lt Y hY1
        omega
  have hexp : torusPolyForm c h p =
      ∑ Y : Nat.Partition ℓ, ∑ Y' : Nat.Partition ℓ,
        C (p Y) * (torus (C c) (C h) (X : ℂ[X]) ℓ Y Y' * C (p Y')) := by
    simp only [torusPolyForm, torusForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hexp]
  constructor
  · refine natDegree_sum_le_of_forall_le _ _ fun Y _ => ?_
    exact natDegree_sum_le_of_forall_le _ _ fun Y' _ => (hterm Y Y').1
  · simp only [finsetSum_coeff, (hterm _ _).2]
    rw [Finset.sum_eq_single (onesPartition ℓ)]
    · rw [Finset.sum_eq_single (onesPartition ℓ)]
      · simp [pow_two]
      · intro Y' _ hY'
        simp [hY']
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro Y _ hY
      simp [hY]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The first assertion of Lemma 5.7 (paper.tex l.712–714), kept as a frozen sub-statement: the
coefficient of `L_{-1}^ℓ|h⟩` in a singular vector of level `ℓ ≥ 1` is nonzero.
Demand sheet: complex `c, h`; `ℓ ≥ 1`; the vector in level-`ℓ` coordinates; `IsSingular`
contains `w ≠ 0`; conclusion `a_w ≠ 0`. -/
def Stmt_sub_singular_ones_coeff : Prop :=
  ∀ (c h : ℂ) (ℓ : ℕ), 1 ≤ ℓ → ∀ p : Nat.Partition ℓ → ℂ,
    Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) ℓ p) ℓ → p (onesPartition ℓ) ≠ 0

/-- Lemma 5.7 from its first assertion. -/
theorem lem_singular_degree_of_sub (hsub : Stmt_sub_singular_ones_coeff) :
    Stmt_lem_singular_degree := by
  intro c h ℓ hℓ p hp
  have ha := hsub c h ℓ hℓ p hp
  obtain ⟨h1, h2⟩ := torusPolyForm_top c h ℓ p
  have hne : (torusPolyForm c h p).coeff (2 * ℓ) ≠ 0 := by rw [h2]; exact pow_ne_zero 2 ha
  have hdeg : (torusPolyForm c h p).natDegree = 2 * ℓ :=
    le_antisymm h1 (le_natDegree_of_ne_zero hne)
  exact ⟨ha, hdeg, by rw [leadingCoeff, hdeg, h2]⟩

end Virasoro
