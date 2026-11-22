import Virasoro.Proofs.Sec6TTTriple

/-!
# Proposition 6.9, Case 2: preparations (paper.tex l.1464–1477, l.1504–1508)

* the order of a split is unique (it is the root multiplicity);
* two branches of the same order `e` at `z` do not cancel if the `[(d−z)^e]` coefficient of the
  sum is nonzero;
* every factor `𝒫_{R,S}` of `τ^±_k` has `S ≡ ±s (mod p')` ("`S ≡ ±s ≢ ±1 (mod ℓ)`", l.1478);
* `m^±_k ≡ ±ps (mod p')`, so `(m^±_k)² − (p'u−p)² ≡ p²(s²−1) ≢ 0 (mod ℓ)` (l.1504–1506);
* `v_ℓ` of the cofactor value `∏_{d_x ≠ d_y}(d_x − d_y)` (l.1466–1472).
-/

namespace Virasoro

namespace TT

open Polynomial Finset

theorem split_unique {z : ℚ} {P Q Q' : ℚ[X]} {e e' : ℕ} (h : SplitAt z P e Q)
    (h' : SplitAt z P e' Q') : e = e' := by
  have hQ : Q ≠ 0 := fun h0 => h.2 (by rw [h0, eval_zero])
  have hQ' : Q' ≠ 0 := fun h0 => h'.2 (by rw [h0, eval_zero])
  have r : ∀ {e : ℕ} {Q : ℚ[X]}, Q ≠ 0 → Q.eval z ≠ 0 →
      ((X - C z) ^ e * Q).rootMultiplicity z = e := by
    intro e Q hQ hz
    rw [mul_comm, rootMultiplicity_mul_X_sub_C_pow hQ, rootMultiplicity_eq_zero hz, zero_add]
  have h1 := r (e := e) hQ h.2
  have h2 := r (e := e') hQ' h'.2
  rw [← h.1] at h1
  rw [← h'.1] at h2
  rw [← h1, ← h2]

theorem same_order_ne {z : ℚ} {A₁ A₂ Q₁ Q₂ G₁ G₂ : ℚ[X]} {e : ℕ} (h₁ : SplitAt z A₁ e Q₁)
    (h₂ : SplitAt z A₂ e Q₂) (hB : (Q₁ * G₁ + Q₂ * G₂).eval z ≠ 0) : A₁ * G₁ + A₂ * G₂ ≠ 0 := by
  rw [h₁.1, h₂.1]
  intro h0
  have h1 : (X - C z) ^ e * (Q₁ * G₁ + Q₂ * G₂) = 0 := by rw [← h0]; ring
  have h2 := (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (X_sub_C_ne_zero z))
  exact hB (by rw [h2, eval_zero])

/-- Every factor `(R, S)` of `τ^ε_k` has `S = p't ± s`. -/
theorem facs_S {p p' r s : ℕ} (hsp : s < p') (ε : Bool) {k : ℕ} (hk : 1 ≤ k) :
    ∀ RS ∈ facs p p' r s ε k, ∃ t σ : ℤ, (σ = 1 ∨ σ = -1) ∧ (RS.2 : ℤ) = p' * t + σ * s := by
  intro RS hRS
  unfold facs at hRS
  split_ifs at hRS with hodd hε hε
  · simp only [List.mem_singleton] at hRS
    subst hRS
    exact ⟨(k / 2 : ℕ), 1, Or.inl rfl, by push_cast; ring⟩
  · simp only [List.mem_singleton] at hRS
    subst hRS
    refine ⟨(k / 2 + 1 : ℕ), -1, Or.inr rfl, ?_⟩
    have : s ≤ (k / 2 + 1) * p' := le_trans hsp.le (Nat.le_mul_of_pos_left p' (by omega))
    push_cast [Nat.cast_sub this]
    ring
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hRS
    rcases hRS with rfl | rfl
    · exact ⟨(k / 2 - 1 : ℕ), 1, Or.inl rfl, by push_cast; ring⟩
    · exact ⟨1, -1, Or.inr rfl, by push_cast [Nat.cast_sub hsp.le]; ring⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hRS
    rcases hRS with rfl | rfl
    · exact ⟨(k / 2 - 1 : ℕ), 1, Or.inl rfl, by push_cast; ring⟩
    · exact ⟨(k - 1 : ℕ), 1, Or.inl rfl, by push_cast; ring⟩

theorem S_not_pm1 {ℓ : ℕ} {p' s S : ℤ} (hℓp' : (ℓ : ℤ) ∣ p') (hs1 : ¬ (ℓ : ℤ) ∣ s - 1)
    (hs2 : ¬ (ℓ : ℤ) ∣ s + 1) {t σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hS : S = p' * t + σ * s) :
    ¬ (ℓ : ℤ) ∣ S - 1 ∧ ¬ (ℓ : ℤ) ∣ S + 1 := by
  have hA : (ℓ : ℤ) ∣ p' * t := dvd_mul_of_dvd_left hℓp' t
  rcases hσ with rfl | rfl
  · refine ⟨fun h => hs1 ?_, fun h => hs2 ?_⟩
    · rw [show s - 1 = (S - 1) - p' * t by rw [hS]; ring]
      exact dvd_sub h hA
    · rw [show s + 1 = (S + 1) - p' * t by rw [hS]; ring]
      exact dvd_sub h hA
  · refine ⟨fun h => hs2 ?_, fun h => hs1 ?_⟩
    · rw [show s + 1 = -((S - 1) - p' * t) by rw [hS]; ring]
      exact dvd_neg.2 (dvd_sub h hA)
    · rw [show s - 1 = -((S + 1) - p' * t) by rw [hS]; ring]
      exact dvd_neg.2 (dvd_sub h hA)

/-- `m^ε_k = p't ± ps` (paper.tex l.1504). -/
theorem nOrb_mod (p p' r s : ℕ) (ε : Bool) (k : ℕ) :
    ∃ t σ : ℤ, (σ = 1 ∨ σ = -1) ∧ nOrb p p' r s ε k = p' * t + σ * p * s := by
  unfold nOrb
  simp only
  split_ifs
  · exact ⟨k * p + r, -1, Or.inr rfl, by ring⟩
  · exact ⟨k * p - r, 1, Or.inl rfl, by ring⟩
  · exact ⟨(k - 1) * p + r, 1, Or.inl rfl, by ring⟩
  · exact ⟨(k + 1) * p - r, -1, Or.inr rfl, by ring⟩

/-- The last sum of `V^±_ℓ(N)` vanishes (paper.tex l.1504–1506). -/
theorem lastsum_zero {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {p p' r s : ℕ} (hℓp' : (ℓ : ℤ) ∣ p')
    (hℓp : ¬ (ℓ : ℤ) ∣ p) (hs1 : ¬ (ℓ : ℤ) ∣ (s : ℤ) - 1) (hs2 : ¬ (ℓ : ℤ) ∣ (s : ℤ) + 1)
    (ε : Bool) (k u : ℕ) :
    padicValInt ℓ (nOrb p p' r s ε k ^ 2 - ((p' : ℤ) * u - p) ^ 2) = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  obtain ⟨t, σ, hσ, he⟩ := nOrb_mod p p' r s ε k
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ.out
  intro h
  rw [he] at h
  have e : ((p' : ℤ) * t + σ * p * s) ^ 2 - ((p' : ℤ) * u - p) ^ 2 =
      p' * (p' * t ^ 2 + 2 * t * σ * p * s - p' * u ^ 2 + 2 * u * p) +
        (σ * σ) * (s - 1) * (s + 1) * p * p + ((σ * σ) - 1) * p * p := by ring
  rw [e, hσσ, sub_self, zero_mul, zero_mul, add_zero, one_mul] at h
  have h3 : (ℓ : ℤ) ∣ ((s : ℤ) - 1) * (s + 1) * p * p := by
    have := dvd_sub h (dvd_mul_of_dvd_left hℓp'
      ((p' : ℤ) * t ^ 2 + 2 * t * σ * p * s - p' * u ^ 2 + 2 * u * p))
    rwa [add_sub_cancel_left] at this
  rcases hpr.dvd_or_dvd h3 with h4 | h4
  · rcases hpr.dvd_or_dvd h4 with h5 | h5
    · rcases hpr.dvd_or_dvd h5 with h6 | h6
      · exact hs1 h6
      · exact hs2 h6
    · exact hℓp h5
  · exact hℓp h4

/-- `v_ℓ` of the cofactor value at `d_y` (paper.tex l.1466–1472). -/
theorem val_cof {ℓ : ℕ} [Fact ℓ.Prime] {p p' : ℕ} (hℓ2 : ℓ ≠ 2) (hp : 0 < p) (hp' : 0 < p')
    (hℓp : ¬ ℓ ∣ p) (RS : ℕ × ℕ) (y : ℤ) :
    padicValRat ℓ (cof p p' (dQ p p' y) RS) =
      (∑ i ∈ idx RS.1 RS.2, (padicValInt ℓ (xv p p' i ^ 2 - y ^ 2) : ℤ)) -
        (padicValNat ℓ p' : ℤ) * ((idx RS.1 RS.2).card - cnt p p' (dQ p p' y) RS : ℤ) := by
  unfold cof cnt
  rw [padicValRat_prod _ _ fun i hi => sub_ne_zero.2 (mem_filter.1 hi).2]
  have h1 : ∀ i ∈ (idx RS.1 RS.2).filter (fun i => ¬ dQ p p' (xv p p' i) = dQ p p' y),
      padicValRat ℓ (dQ p p' (xv p p' i) - dQ p p' y) =
        (padicValInt ℓ (xv p p' i ^ 2 - y ^ 2) : ℤ) - (padicValNat ℓ p' : ℤ) := by
    intro i hi
    exact val_dQ_sub hℓ2 hp hp' hℓp fun h => (mem_filter.1 hi).2 ((dQ_eq_iff hp hp' _ _).2 h)
  rw [sum_congr rfl h1, sum_sub_distrib, sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ (idx RS.1 RS.2).filter (fun i => ¬ dQ p p' (xv p p' i) = dQ p p' y),
      (padicValInt ℓ (xv p p' i ^ 2 - y ^ 2) : ℤ) =
      ∑ i ∈ idx RS.1 RS.2, (padicValInt ℓ (xv p p' i ^ 2 - y ^ 2) : ℤ) := by
    refine sum_subset (filter_subset _ _) fun i hi hi' => ?_
    have : dQ p p' (xv p p' i) = dQ p p' y := by
      by_contra hc
      exact hi' (mem_filter.2 ⟨hi, hc⟩)
    rw [(dQ_eq_iff hp hp' _ _).1 this, sub_self]
    simp
  have h3 := card_filter_add_card_filter_not
    (s := idx RS.1 RS.2) (fun i => dQ p p' (xv p p' i) = dQ p p' y)
  rw [h2]
  have h4 : (((idx RS.1 RS.2).filter (fun i => ¬ dQ p p' (xv p p' i) = dQ p p' y)).card : ℤ) =
      (idx RS.1 RS.2).card - ((idx RS.1 RS.2).filter
        (fun i => dQ p p' (xv p p' i) = dQ p p' y)).card := by
    rw [← h3]
    push_cast
    ring
  rw [h4]
  ring

end TT

end Virasoro
