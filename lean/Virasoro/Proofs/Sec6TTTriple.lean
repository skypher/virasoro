import Virasoro.Proofs.Sec6TTPair

/-!
# Proposition 6.9, Case 2: the triples for `ℓ = 3` (paper.tex l.1489–1503)

"If `ℓ = 3`, then `3 ∣ s` and `3 ∣ S`, so the odd indices `1 ≤ l < 2S` partition into triples
`{6j+1, 6j+3, 6j+5}`."  At `l = 6j+3` the two factors `x² − x₁²` are `G₁G₂` and `G₃G₄`; at
`l = 6j+1` and `6j+5` the factors `x² − x₀²` are `G₁E₁`, `E₂G₄`, `E₃G₂`, `G₃E₄` with `3`-adic units
`E_i`; the other factors are `3`-adic units.  Since `G₂ = G₁ + 2x₁` and `G₄ = G₃ + 2x₁`
(`x₁ = p'−3p`), a vanishing `G` (a root `d₁`) contributes `−v₃(x₁)` and nothing else does:
`∑ v₃(x² − x₁²) − ∑ v₃(x² − x₀²) = −m₁(R,S) v₃(p'−3p)`.
-/

namespace Virasoro

namespace TT

open Finset

section Three

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem not_dvd3 {E A c p : ℤ} (hA : (3 : ℤ) ∣ A) (hE : E = A + c * p) (hc : ¬ (3 : ℤ) ∣ c)
    (hp : ¬ (3 : ℤ) ∣ p) : ¬ (3 : ℤ) ∣ E := by
  intro h
  have hpr : Prime (3 : ℤ) := Int.prime_three
  have h1 : (3 : ℤ) ∣ c * p := by
    have := dvd_sub h hA
    rwa [hE, add_sub_cancel_left] at this
  rcases hpr.dvd_or_dvd h1 with h2 | h2
  · exact hc h2
  · exact hp h2

theorem not_dvd_off {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {p p' : ℤ} (hℓp' : (ℓ : ℤ) ∣ p')
    (hℓp : ¬ (ℓ : ℤ) ∣ p) (a τ l : ℤ) (hτ : τ = 1 ∨ τ = -1) (β : ℤ) (h1 : ¬ (ℓ : ℤ) ∣ l - β)
    (h2 : ¬ (ℓ : ℤ) ∣ l + β) : ¬ (ℓ : ℤ) ∣ ((a * p' - τ * l * p) ^ 2 - (p' - β * p) ^ 2) := by
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

/-- A pair `G, G' = G + 2x₁`: `v(GG') − v(G) − v(G') + v(x₁)[GG' = 0] = 0`. -/
theorem pair3 {G G' x : ℤ} (hx : x ≠ 0) (h : G' = G + 2 * x) :
    (padicValInt 3 (G * G') : ℤ) - padicValInt 3 G - padicValInt 3 G' +
      (padicValInt 3 x : ℤ) * (if G * G' = 0 then 1 else 0) = 0 := by
  have h2 : padicValInt 3 (2 : ℤ) = 0 := padicValInt.eq_zero_of_not_dvd (by decide)
  by_cases hG : G = 0
  · have : G' = 2 * x := by rw [h, hG, zero_add]
    rw [hG, zero_mul, if_pos rfl, this, padicValInt.mul (by norm_num) hx, h2]
    simp
  · by_cases hG' : G' = 0
    · have : G = -(2 * x) := by linarith
      have hneg : padicValInt 3 (-(2 * x)) = padicValInt 3 (2 * x) := by
        simp only [padicValInt, Int.natAbs_neg]
      rw [hG', mul_zero, if_pos rfl, this, hneg, padicValInt.mul (by norm_num) hx, h2]
      simp
    · rw [padicValInt.mul hG hG', if_neg (mul_ne_zero hG hG')]
      push_cast
      ring

/-- `∑_{l odd < 6T} F l = ∑_{j < T} (F(6j+1) + F(6j+3) + F(6j+5))`. -/
theorem sum_odds_three (F : ℕ → ℤ) (T : ℕ) :
    ∑ l ∈ oddsBelow (3 * T), F l = ∑ j ∈ range T, (F (6 * j + 1) + F (6 * j + 3) + F (6 * j + 5)) := by
  induction T with
  | zero => simp [oddsBelow]
  | succ T ih =>
    have hs : oddsBelow (3 * (T + 1)) =
        oddsBelow (3 * T) ∪ {6 * T + 1, 6 * T + 3, 6 * T + 5} := by
      ext l
      simp only [oddsBelow, mem_filter, mem_range, mem_union, mem_insert, mem_singleton]
      omega
    have hd : Disjoint (oddsBelow (3 * T)) {6 * T + 1, 6 * T + 3, 6 * T + 5} := by
      rw [disjoint_left]
      intro l hl hl'
      simp only [oddsBelow, mem_filter, mem_range] at hl
      simp only [mem_insert, mem_singleton] at hl'
      omega
    rw [hs, sum_union hd, ih, sum_range_succ, sum_insert (by simp), sum_insert (by simp),
      sum_singleton]
    ring

variable {p p' : ℕ}

theorem triple_zero (hp3 : (3 : ℤ) ∣ p') (hp : ¬ (3 : ℤ) ∣ p) (hx1 : (p' : ℤ) - 3 * p ≠ 0)
    (a j : ℕ) :
    let F : ℕ → ℤ := fun l => ∑ σ : Bool,
      ((padicValInt 3 (xv p p' ((a, l), σ) ^ 2 - ((p' : ℤ) - 3 * p) ^ 2) : ℤ) -
        padicValInt 3 (xv p p' ((a, l), σ) ^ 2 - ((p' : ℤ) - p) ^ 2) +
        (padicValInt 3 ((p' : ℤ) - 3 * p) : ℤ) *
          (if xv p p' ((a, l), σ) ^ 2 = ((p' : ℤ) - 3 * p) ^ 2 then 1 else 0))
    F (6 * j + 1) + F (6 * j + 3) + F (6 * j + 5) = 0 := by
  intro F
  set A : ℤ := (a : ℤ) with hAd
  set J : ℤ := (j : ℤ) with hJd
  set P : ℤ := (p : ℤ) with hPd
  set P' : ℤ := (p' : ℤ) with hP'd
  set x1 : ℤ := P' - 3 * P
  set G1 := (A - 1) * P' - 6 * J * P
  set G2 := (A + 1) * P' - (6 * J + 6) * P
  set G3 := (A - 1) * P' + (6 * J + 6) * P
  set G4 := (A + 1) * P' + 6 * J * P
  have hA : ∀ u : ℤ, (3 : ℤ) ∣ P' * u := fun u => dvd_mul_of_dvd_left hp3 u
  have hE1 := not_dvd3 (hA (A + 1)) (E := (A + 1) * P' - (6 * J + 2) * P)
    (c := -(6 * J + 2)) (by ring) (by omega) hp
  have hE2 := not_dvd3 (hA (A - 1)) (E := (A - 1) * P' + (6 * J + 2) * P)
    (c := 6 * J + 2) (by ring) (by omega) hp
  have hE3 := not_dvd3 (hA (A - 1)) (E := (A - 1) * P' - (6 * J + 4) * P)
    (c := -(6 * J + 4)) (by ring) (by omega) hp
  have hE4 := not_dvd3 (hA (A + 1)) (E := (A + 1) * P' + (6 * J + 4) * P)
    (c := 6 * J + 4) (by ring) (by omega) hp
  -- the twelve factors
  have xt : ∀ l : ℕ, xv p p' ((a, l), true) = A * P' - (l : ℤ) * P := fun l => by simp [xv, A, P, P']
  have xf : ∀ l : ℕ, xv p p' ((a, l), false) = A * P' + (l : ℤ) * P := fun l => by simp [xv, A, P, P']
  have c1 : ((6 * j + 1 : ℕ) : ℤ) = 6 * J + 1 := by push_cast; rfl
  have c3 : ((6 * j + 3 : ℕ) : ℤ) = 6 * J + 3 := by push_cast; rfl
  have c5 : ((6 * j + 5 : ℕ) : ℤ) = 6 * J + 5 := by push_cast; rfl
  have off1 : ∀ (l : ℕ) (σ : Bool), ¬ (3 : ℤ) ∣ (l : ℤ) →
      padicValInt 3 (xv p p' ((a, l), σ) ^ 2 - (P' - 3 * P) ^ 2) = 0 := by
    intro l σ hl
    rw [xv_tau]
    have := val_off (ℓ := 3) hp3 hp a (if σ then 1 else -1) l (by cases σ <;> simp) 3
      (fun h => hl (by have := dvd_add h (dvd_refl 3); simpa using this))
      (fun h => hl (by have := dvd_sub h (dvd_refl 3); simpa using this))
    exact this
  have off0 : ∀ (σ : Bool), padicValInt 3 (xv p p' ((a, 6 * j + 3), σ) ^ 2 - (P' - P) ^ 2) = 0 := by
    intro σ
    rw [xv_tau]
    have := val_off (ℓ := 3) hp3 hp a (if σ then 1 else -1) (6 * j + 3) (by cases σ <;> simp) 1
      (by push_cast; omega) (by push_cast; omega)
    rw [one_mul] at this
    exact this
  have nind : ∀ (l : ℕ) (σ : Bool), ¬ (3 : ℤ) ∣ (l : ℤ) →
      xv p p' ((a, l), σ) ^ 2 ≠ (P' - 3 * P) ^ 2 := by
    intro l σ hl h0
    apply not_dvd_off (ℓ := 3) hp3 hp a (if σ then 1 else -1) l (by cases σ <;> simp) 3
      (fun h => hl (by have := dvd_add h (dvd_refl 3); simpa using this))
      (fun h => hl (by have := dvd_sub h (dvd_refl 3); simpa using this))
    rw [← xv_tau, h0, sub_self]
    exact dvd_zero _
  have u1 : ¬ (3 : ℤ) ∣ ((6 * j + 1 : ℕ) : ℤ) := by push_cast; omega
  have u5 : ¬ (3 : ℤ) ∣ ((6 * j + 5 : ℕ) : ℤ) := by push_cast; omega
  -- evaluate the three terms
  have F1 : F (6 * j + 1) = -(padicValInt 3 G1 : ℤ) - padicValInt 3 G4 := by
    simp only [F, Fintype.sum_bool]
    rw [off1 _ true u1, off1 _ false u1, if_neg (nind _ true u1),
      if_neg (nind _ false u1), xt, xf, c1]
    rw [show (A * P' - (6 * J + 1) * P) ^ 2 - (P' - P) ^ 2 =
        G1 * ((A + 1) * P' - (6 * J + 2) * P) by simp only [G1]; ring,
      show (A * P' + (6 * J + 1) * P) ^ 2 - (P' - P) ^ 2 =
        G4 * ((A - 1) * P' + (6 * J + 2) * P) by simp only [G4]; ring,
      val_mul_unit _ _ hE1, val_mul_unit _ _ hE2]
    push_cast
    ring
  have F5 : F (6 * j + 5) = -(padicValInt 3 G2 : ℤ) - padicValInt 3 G3 := by
    simp only [F, Fintype.sum_bool]
    rw [off1 _ true u5, off1 _ false u5, if_neg (nind _ true u5),
      if_neg (nind _ false u5), xt, xf, c5]
    rw [show (A * P' - (6 * J + 5) * P) ^ 2 - (P' - P) ^ 2 =
        G2 * ((A - 1) * P' - (6 * J + 4) * P) by simp only [G2]; ring,
      show (A * P' + (6 * J + 5) * P) ^ 2 - (P' - P) ^ 2 =
        G3 * ((A + 1) * P' + (6 * J + 4) * P) by simp only [G3]; ring,
      val_mul_unit _ _ hE3, val_mul_unit _ _ hE4]
    push_cast
    ring
  have F3 : F (6 * j + 3) = ((padicValInt 3 (G1 * G2) : ℤ) +
      (padicValInt 3 x1 : ℤ) * (if G1 * G2 = 0 then 1 else 0)) +
      ((padicValInt 3 (G3 * G4) : ℤ) + (padicValInt 3 x1 : ℤ) * (if G3 * G4 = 0 then 1 else 0)) := by
    simp only [F, Fintype.sum_bool]
    rw [off0 true, off0 false, xt, xf, c3]
    have e1 : (A * P' - (6 * J + 3) * P) ^ 2 - (P' - 3 * P) ^ 2 = G1 * G2 := by
      simp only [G1, G2]; ring
    have e2 : (A * P' + (6 * J + 3) * P) ^ 2 - (P' - 3 * P) ^ 2 = G3 * G4 := by
      simp only [G3, G4]; ring
    have i1 : ((A * P' - (6 * J + 3) * P) ^ 2 = (P' - 3 * P) ^ 2) ↔ G1 * G2 = 0 := by
      rw [← e1, sub_eq_zero]
    have i2 : ((A * P' + (6 * J + 3) * P) ^ 2 = (P' - 3 * P) ^ 2) ↔ G3 * G4 = 0 := by
      rw [← e2, sub_eq_zero]
    rw [e1, e2, if_congr i1 rfl rfl, if_congr i2 rfl rfl]
    push_cast
    ring
  rw [F1, F3, F5]
  have p1 := pair3 hx1 (G := G1) (G' := G2) (by simp only [G1, G2, x1]; ring)
  have p2 := pair3 hx1 (G := G3) (G' := G4) (by simp only [G3, G4, x1]; ring)
  linear_combination p1 + p2

/-- For `ℓ = 3` and `3 ∣ S`: `∑ v₃(x² − x₁²) − ∑ v₃(x² − x₀²) = −m₁(R,S) v₃(p'−3p)`
(paper.tex l.1489–1503). -/
theorem W_three {p p' : ℕ} (hp3 : (3 : ℤ) ∣ p') (hp : ¬ (3 : ℤ) ∣ p)
    (hx1 : (p' : ℤ) - 3 * p ≠ 0) (R T : ℕ) :
    (∑ i ∈ idx R (3 * T), (padicValInt 3 (xv p p' i ^ 2 - ((p' : ℤ) - 3 * p) ^ 2) : ℤ)) -
      ∑ i ∈ idx R (3 * T), (padicValInt 3 (xv p p' i ^ 2 - ((p' : ℤ) - p) ^ 2) : ℤ) =
      -(padicValInt 3 ((p' : ℤ) - 3 * p) : ℤ) * (m1 p p' R (3 * T) : ℤ) := by
  have hsum : ∑ i ∈ idx R (3 * T),
      ((padicValInt 3 (xv p p' i ^ 2 - ((p' : ℤ) - 3 * p) ^ 2) : ℤ) -
        padicValInt 3 (xv p p' i ^ 2 - ((p' : ℤ) - p) ^ 2) +
        (padicValInt 3 ((p' : ℤ) - 3 * p) : ℤ) *
          (if xv p p' i ^ 2 = ((p' : ℤ) - 3 * p) ^ 2 then 1 else 0)) = 0 := by
    rw [idx, sum_product, sum_product]
    refine sum_eq_zero fun a _ => ?_
    rw [sum_odds_three]
    exact sum_eq_zero fun j _ => triple_zero hp3 hp hx1 a j
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hsum
  rw [m1, card_filter]
  push_cast
  linear_combination hsum

end Three

end TT

end Virasoro
