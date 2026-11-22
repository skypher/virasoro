import Virasoro.Proofs.Sec6TTVal

/-!
# Proposition 6.9, Case 2: the pairing of factors for `ℓ ≥ 5` (paper.tex l.1478–1488)

"If `ℓ ≥ 5`, the odd indices `1 ≤ l < 2S` with `l ≡ ±3 (mod ℓ)` pair bijectively with those with
`l ≡ ±1 (mod ℓ)` via `(2jℓ+3ε, 2jℓ+ε)`": with `A = p'−βp`, `B = p'a' + σp(2jℓ+βε)`,
`A² − B² = (A+εσB)(A−εσB)`, the first factor independent of `β ∈ {1,3}` and the second
`≡ −2βp ≢ 0 (mod ℓ)`, so the paired factors share the same `ℓ`-adic valuation (both `0` when they
vanish, the convention `v_ℓ(0) = 0` matching "skipped").  The other indices contribute `0`.
Hence, for every factor `𝒫_{R,S}` with `S ≢ ±1 (mod ℓ)`,
`∑ v_ℓ(x² − x₁²) = ∑ v_ℓ(x² − x₀²)` (`x₁ = p'−3p`, `x₀ = p'−p`).
-/

namespace Virasoro

namespace TT

open Finset

section Pair

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem val_mul_unit (U V : ℤ) (hV : ¬ (ℓ : ℤ) ∣ V) :
    padicValInt ℓ (U * V) = padicValInt ℓ U := by
  by_cases hU : U = 0
  · rw [hU, zero_mul]
  · have hV0 : V ≠ 0 := fun h => hV (h ▸ dvd_zero _)
    rw [padicValInt.mul hU hV0, padicValInt.eq_zero_of_not_dvd hV, add_zero]

theorem not_dvd_lin (hℓ5 : 5 ≤ ℓ) {V A p : ℤ} (c : ℤ) (hc : c = 2 ∨ c = -2 ∨ c = 6 ∨ c = -6)
    (hA : (ℓ : ℤ) ∣ A) (hV : V = A + c * p) (hp : ¬ (ℓ : ℤ) ∣ p) : ¬ (ℓ : ℤ) ∣ V := by
  intro h
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ.out
  have h1 : (ℓ : ℤ) ∣ c * p := by
    have := dvd_sub h hA
    rwa [hV, add_sub_cancel_left] at this
  rcases hpr.dvd_or_dvd h1 with h2 | h2
  · have h3 : ℓ ∣ c.natAbs := Int.natCast_dvd.1 h2
    have h4 : c.natAbs = 2 ∨ c.natAbs = 6 := by rcases hc with rfl | rfl | rfl | rfl <;> simp
    rcases h4 with h4 | h4 <;> rw [h4] at h3
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      interval_cases ℓ
      · omega
      · exact absurd hℓ.out (by decide)
  · exact hp h2

/-- The paired factors (paper.tex l.1481–1486). -/
theorem pair_val (hℓ5 : 5 ≤ ℓ) {p p' : ℤ} (hℓp' : (ℓ : ℤ) ∣ p') (hℓp : ¬ (ℓ : ℤ) ∣ p)
    (a τ ε L : ℤ) (hτ : τ = 1 ∨ τ = -1) (hε : ε = 1 ∨ ε = -1) (hL : (ℓ : ℤ) ∣ L) :
    padicValInt ℓ ((a * p' - τ * (L + 3 * ε) * p) ^ 2 - (p' - 3 * p) ^ 2) =
      padicValInt ℓ ((a * p' - τ * (L + ε) * p) ^ 2 - (p' - p) ^ 2) := by
  have hA : ∀ u v : ℤ, (ℓ : ℤ) ∣ p' * u + L * v := fun u v =>
    dvd_add (dvd_mul_of_dvd_left hℓp' u) (dvd_mul_of_dvd_left hL v)
  rcases hτ with rfl | rfl <;> rcases hε with rfl | rfl
  · -- τε = 1: common factor `(a−1)p' − Lp`
    have e1 : (a * p' - 1 * (L + 3 * 1) * p) ^ 2 - (p' - 3 * p) ^ 2 =
        ((a - 1) * p' - L * p) * ((a + 1) * p' - L * p - 6 * p) := by ring
    have e0 : (a * p' - 1 * (L + 1) * p) ^ 2 - (p' - p) ^ 2 =
        ((a - 1) * p' - L * p) * ((a + 1) * p' - L * p - 2 * p) := by ring
    rw [e1, e0, val_mul_unit _ _ (not_dvd_lin hℓ5 (-6) (by norm_num) (hA (a + 1) (-p))
        (by ring) hℓp),
      val_mul_unit _ _ (not_dvd_lin hℓ5 (-2) (by norm_num) (hA (a + 1) (-p)) (by ring) hℓp)]
  · -- τε = −1: common factor `(a+1)p' − Lp`
    have e1 : (a * p' - 1 * (L + 3 * -1) * p) ^ 2 - (p' - 3 * p) ^ 2 =
        ((a + 1) * p' - L * p) * ((a - 1) * p' - L * p + 6 * p) := by ring
    have e0 : (a * p' - 1 * (L + -1) * p) ^ 2 - (p' - p) ^ 2 =
        ((a + 1) * p' - L * p) * ((a - 1) * p' - L * p + 2 * p) := by ring
    rw [e1, e0, val_mul_unit _ _ (not_dvd_lin hℓ5 6 (by norm_num) (hA (a - 1) (-p))
        (by ring) hℓp),
      val_mul_unit _ _ (not_dvd_lin hℓ5 2 (by norm_num) (hA (a - 1) (-p)) (by ring) hℓp)]
  · have e1 : (a * p' - -1 * (L + 3 * 1) * p) ^ 2 - (p' - 3 * p) ^ 2 =
        ((a + 1) * p' + L * p) * ((a - 1) * p' + L * p + 6 * p) := by ring
    have e0 : (a * p' - -1 * (L + 1) * p) ^ 2 - (p' - p) ^ 2 =
        ((a + 1) * p' + L * p) * ((a - 1) * p' + L * p + 2 * p) := by ring
    rw [e1, e0, val_mul_unit _ _ (not_dvd_lin hℓ5 6 (by norm_num) (hA (a - 1) p)
        (by ring) hℓp),
      val_mul_unit _ _ (not_dvd_lin hℓ5 2 (by norm_num) (hA (a - 1) p) (by ring) hℓp)]
  · have e1 : (a * p' - -1 * (L + 3 * -1) * p) ^ 2 - (p' - 3 * p) ^ 2 =
        ((a - 1) * p' + L * p) * ((a + 1) * p' + L * p - 6 * p) := by ring
    have e0 : (a * p' - -1 * (L + -1) * p) ^ 2 - (p' - p) ^ 2 =
        ((a - 1) * p' + L * p) * ((a + 1) * p' + L * p - 2 * p) := by ring
    rw [e1, e0, val_mul_unit _ _ (not_dvd_lin hℓ5 (-6) (by norm_num) (hA (a + 1) p)
        (by ring) hℓp),
      val_mul_unit _ _ (not_dvd_lin hℓ5 (-2) (by norm_num) (hA (a + 1) p) (by ring) hℓp)]

/-- Off the residues `±3` (resp. `±1`) the factor is an `ℓ`-adic unit. -/
theorem val_off {p p' : ℤ} (hℓp' : (ℓ : ℤ) ∣ p') (hℓp : ¬ (ℓ : ℤ) ∣ p) (a τ l : ℤ)
    (hτ : τ = 1 ∨ τ = -1) (β : ℤ) (h1 : ¬ (ℓ : ℤ) ∣ l - β) (h2 : ¬ (ℓ : ℤ) ∣ l + β) :
    padicValInt ℓ ((a * p' - τ * l * p) ^ 2 - (p' - β * p) ^ 2) = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  intro h
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ.out
  have e : (a * p' - τ * l * p) ^ 2 - (p' - β * p) ^ 2 =
      p' * (a ^ 2 * p' - 2 * a * τ * l * p - p' + 2 * β * p) + (τ * τ) * (l - β) * (l + β) * p * p +
        ((τ * τ) - 1) * β ^ 2 * p * p := by ring
  have hττ : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
  rw [e, hττ, sub_self, zero_mul, zero_mul, zero_mul, add_zero, one_mul] at h
  have h3 : (ℓ : ℤ) ∣ (l - β) * (l + β) * p * p := by
    have := dvd_sub h (dvd_mul_of_dvd_left hℓp' (a ^ 2 * p' - 2 * a * τ * l * p - p' + 2 * β * p))
    rwa [add_sub_cancel_left] at this
  rcases hpr.dvd_or_dvd h3 with h4 | h4
  · rcases hpr.dvd_or_dvd h4 with h5 | h5
    · rcases hpr.dvd_or_dvd h5 with h6 | h6
      · exact h1 h6
      · exact h2 h6
    · exact hℓp h5
  · exact hℓp h4

end Pair

section Sum

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem small_not_dvd (hℓ5 : 5 ≤ ℓ) {c : ℤ} (hc : c = 2 ∨ c = 4 ∨ c = 6) : ¬ (ℓ : ℤ) ∣ c := by
  intro h
  have h3 : ℓ ∣ c.natAbs := Int.natCast_dvd.1 h
  rcases hc with rfl | rfl | rfl
  · have := Nat.le_of_dvd (by norm_num) h3
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    interval_cases ℓ
    · omega
    · exact absurd hℓ.out (by decide)

theorem dvd_two_mul {n : ℤ} (h : (ℓ : ℤ) ∣ 2 * n) (hℓ2 : ¬ (ℓ : ℤ) ∣ 2) : (ℓ : ℤ) ∣ n := by
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ.out
  rcases hpr.dvd_or_dvd h with h1 | h1
  · exact absurd h1 hℓ2
  · exact h1

theorem xv_tau (p p' a l : ℕ) (σ : Bool) :
    xv p p' ((a, l), σ) = (a : ℤ) * p' - (if σ then 1 else -1) * (l : ℤ) * p := by
  cases σ <;> simp [xv] <;> ring

/-- `∑_l v_ℓ(x² − x₁²) = ∑_l v_ℓ(x² − x₀²)` for fixed `(a', σ)` (paper.tex l.1478–1488). -/
theorem sum_l_five (hℓ5 : 5 ≤ ℓ) {p p' : ℕ} (hℓp' : (ℓ : ℤ) ∣ p') (hℓp : ¬ (ℓ : ℤ) ∣ p)
    (a : ℕ) (σ : Bool) {S : ℕ} (hS1 : ¬ (ℓ : ℤ) ∣ (S : ℤ) - 1) (hS2 : ¬ (ℓ : ℤ) ∣ (S : ℤ) + 1) :
    ∑ l ∈ oddsBelow S, padicValInt ℓ (xv p p' ((a, l), σ) ^ 2 - ((p' : ℤ) - 3 * p) ^ 2) =
      ∑ l ∈ oddsBelow S, padicValInt ℓ (xv p p' ((a, l), σ) ^ 2 - ((p' : ℤ) - p) ^ 2) := by
  classical
  set τ : ℤ := if σ then 1 else -1 with hτd
  have hτ : τ = 1 ∨ τ = -1 := by cases σ <;> simp [hτd]
  simp only [xv_tau, ← hτd]
  have h2 := small_not_dvd hℓ5 (c := 2) (by norm_num)
  have h4 := small_not_dvd hℓ5 (c := 4) (by norm_num)
  have h6 := small_not_dvd hℓ5 (c := 6) (by norm_num)
  set f1 : ℕ → ℕ := fun l => padicValInt ℓ (((a : ℤ) * p' - τ * (l : ℤ) * p) ^ 2 -
    ((p' : ℤ) - 3 * p) ^ 2) with hf1
  set f0 : ℕ → ℕ := fun l => padicValInt ℓ (((a : ℤ) * p' - τ * (l : ℤ) * p) ^ 2 -
    ((p' : ℤ) - p) ^ 2) with hf0
  set L3 := (oddsBelow S).filter (fun l : ℕ => (ℓ : ℤ) ∣ (l : ℤ) - 3 ∨ (ℓ : ℤ) ∣ (l : ℤ) + 3)
  set L1 := (oddsBelow S).filter (fun l : ℕ => (ℓ : ℤ) ∣ (l : ℤ) - 1 ∨ (ℓ : ℤ) ∣ (l : ℤ) + 1)
  have hz1 : ∑ l ∈ L3, f1 l = ∑ l ∈ oddsBelow S, f1 l := by
    refine sum_subset (filter_subset _ _) fun l hl hl' => ?_
    have h' : ¬ ((ℓ : ℤ) ∣ (l : ℤ) - 3 ∨ (ℓ : ℤ) ∣ (l : ℤ) + 3) := fun h => hl' (mem_filter.2 ⟨hl, h⟩)
    push_neg at h'
    exact val_off hℓp' hℓp a τ l hτ 3 h'.1 h'.2
  have hz0 : ∑ l ∈ L1, f0 l = ∑ l ∈ oddsBelow S, f0 l := by
    refine sum_subset (filter_subset _ _) fun l hl hl' => ?_
    have h' : ¬ ((ℓ : ℤ) ∣ (l : ℤ) - 1 ∨ (ℓ : ℤ) ∣ (l : ℤ) + 1) := fun h => hl' (mem_filter.2 ⟨hl, h⟩)
    push_neg at h'
    have := val_off hℓp' hℓp a τ l hτ 1 h'.1 h'.2
    rw [one_mul] at this
    exact this
  have hmain : ∑ l ∈ L3, f1 l = ∑ l ∈ L1, f0 l := by
    refine sum_nbij' (fun l : ℕ => if (ℓ : ℤ) ∣ (l : ℤ) - 3 then l - 2 else l + 2)
      (fun l : ℕ => if (ℓ : ℤ) ∣ (l : ℤ) - 1 then l + 2 else l - 2) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      obtain ⟨hl0, hl3⟩ := mem_filter.1 hl
      obtain ⟨hlS, hlo⟩ := mem_oddsBelow.1 hl0
      split_ifs with hA
      · have hl1 : 3 ≤ l := by
          by_contra hc
          have : l = 1 := by omega
          subst this
          exact h2 (by have := dvd_neg.2 hA; norm_num at this ⊢; exact this)
        refine mem_filter.2 ⟨mem_oddsBelow.2 ⟨by omega, by omega⟩, Or.inl ?_⟩
        rw [Nat.cast_sub (by omega)]
        convert hA using 1
        push_cast
        ring
      · have hB : (ℓ : ℤ) ∣ (l : ℤ) + 3 := hl3.resolve_left hA
        have hl2 : l + 2 < 2 * S := by
          by_contra hc
          have : l = 2 * S - 1 := by omega
          apply hS2
          refine dvd_two_mul (n := (S : ℤ) + 1) ?_ h2
          convert hB using 1
          rw [this, Nat.cast_sub (by omega)]
          push_cast
          ring
        refine mem_filter.2 ⟨mem_oddsBelow.2 ⟨hl2, by omega⟩, Or.inr ?_⟩
        convert hB using 1
        push_cast
        ring
    · intro l hl
      obtain ⟨hl0, hl1⟩ := mem_filter.1 hl
      obtain ⟨hlS, hlo⟩ := mem_oddsBelow.1 hl0
      split_ifs with hC
      · have hl2 : l + 2 < 2 * S := by
          by_contra hc
          have : l = 2 * S - 1 := by omega
          apply hS1
          refine dvd_two_mul (n := (S : ℤ) - 1) ?_ h2
          convert hC using 1
          rw [this, Nat.cast_sub (by omega)]
          push_cast
          ring
        refine mem_filter.2 ⟨mem_oddsBelow.2 ⟨hl2, by omega⟩, Or.inl ?_⟩
        convert hC using 1
        push_cast
        ring
      · have hD : (ℓ : ℤ) ∣ (l : ℤ) + 1 := hl1.resolve_left hC
        have hl3 : 3 ≤ l := by
          by_contra hc
          have : l = 1 := by omega
          subst this
          exact h2 (by norm_num at hD ⊢; exact hD)
        refine mem_filter.2 ⟨mem_oddsBelow.2 ⟨by omega, by omega⟩, Or.inr ?_⟩
        rw [Nat.cast_sub (by omega)]
        convert hD using 1
        push_cast
        ring
    · intro l hl
      obtain ⟨hl0, hl3⟩ := mem_filter.1 hl
      obtain ⟨hlS, hlo⟩ := mem_oddsBelow.1 hl0
      try beta_reduce
      split_ifs with hA hC hC
      · have hl1 : 3 ≤ l := by
          by_contra hc
          have : l = 1 := by omega
          subst this
          exact h2 (by have := dvd_neg.2 hA; norm_num at this ⊢; exact this)
        omega
      · exfalso
        apply hC
        rw [Nat.cast_sub (by
          by_contra hc
          have : l ≤ 1 := by omega
          interval_cases l
          · omega
          · exact h2 (by have := dvd_neg.2 hA; norm_num at this ⊢; exact this))]
        convert hA using 1
        push_cast
        ring
      · exfalso
        have hB : (ℓ : ℤ) ∣ (l : ℤ) + 3 := hl3.resolve_left hA
        have h := dvd_sub hB hC
        push_cast at h
        rw [show (l : ℤ) + 3 - ((l : ℤ) + 2 - 1) = 2 by ring] at h
        exact h2 h
      · omega
    · intro l hl
      obtain ⟨hl0, hl1⟩ := mem_filter.1 hl
      obtain ⟨hlS, hlo⟩ := mem_oddsBelow.1 hl0
      try beta_reduce
      split_ifs with hC hA hA
      · omega
      · exfalso
        apply hA
        convert hC using 1
        push_cast
        ring
      · have hD : (ℓ : ℤ) ∣ (l : ℤ) + 1 := hl1.resolve_left hC
        exfalso
        apply h6
        have hl3 : 3 ≤ l := by
          by_contra hc
          have : l = 1 := by omega
          subst this
          exact h2 (by norm_num at hD ⊢; exact hD)
        rw [Nat.cast_sub (by omega)] at hA
        have h := dvd_sub hD hA
        push_cast at h
        rw [show (l : ℤ) + 1 - ((l : ℤ) - 2 - 3) = 6 by ring] at h
        exact h
      · have hD : (ℓ : ℤ) ∣ (l : ℤ) + 1 := hl1.resolve_left hC
        have hl3 : 3 ≤ l := by
          by_contra hc
          have : l = 1 := by omega
          subst this
          exact h2 (by norm_num at hD ⊢; exact hD)
        omega
    · intro l hl
      obtain ⟨hl0, hl3⟩ := mem_filter.1 hl
      obtain ⟨hlS, hlo⟩ := mem_oddsBelow.1 hl0
      simp only [hf1, hf0]
      split_ifs with hA
      · have hl1 : 3 ≤ l := by
          by_contra hc
          have : l = 1 := by omega
          subst this
          exact h2 (by have := dvd_neg.2 hA; norm_num at this ⊢; exact this)
        have := pair_val hℓ5 hℓp' hℓp a τ 1 ((l : ℤ) - 3) hτ (Or.inl rfl) hA
        rw [Nat.cast_sub (by omega)]
        convert this using 3 <;> push_cast <;> ring
      · have hB : (ℓ : ℤ) ∣ (l : ℤ) + 3 := hl3.resolve_left hA
        have := pair_val hℓ5 hℓp' hℓp a τ (-1) ((l : ℤ) + 3) hτ (Or.inr rfl) hB
        convert this using 3 <;> push_cast <;> ring
  exact hz1.symm.trans (hmain.trans hz0)

end Sum

/-- For `ℓ ≥ 5` and `S ≢ ±1 (mod ℓ)`: the `x₁`-sum and the `x₀`-sum of `𝒫_{R,S}` agree
(paper.tex l.1478–1488). -/
theorem W_five {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) {p p' : ℕ} (hℓp' : (ℓ : ℤ) ∣ p')
    (hℓp : ¬ (ℓ : ℤ) ∣ p) (R S : ℕ) (hS1 : ¬ (ℓ : ℤ) ∣ (S : ℤ) - 1)
    (hS2 : ¬ (ℓ : ℤ) ∣ (S : ℤ) + 1) :
    ∑ i ∈ idx R S, padicValInt ℓ (xv p p' i ^ 2 - ((p' : ℤ) - 3 * p) ^ 2) =
      ∑ i ∈ idx R S, padicValInt ℓ (xv p p' i ^ 2 - ((p' : ℤ) - p) ^ 2) := by
  rw [idx, sum_product, sum_product, sum_product, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm, sum_comm (s := oddsBelow S)]
  exact sum_congr rfl fun σ _ => sum_l_five hℓ5 hℓp' hℓp a σ hS1 hS2

end TT

end Virasoro
