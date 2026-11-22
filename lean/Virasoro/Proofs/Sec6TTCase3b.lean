import Virasoro.Proofs.Sec6TTCase3a

/-!
# Proposition 6.9, Case 3: `v_ℓ(T_k − 1)` (paper.tex l.1546–1553)

`m⁺_k + m⁻_k = 2kpp'` gives
`T_k − 1 = −2kpp'(3(m⁺)² − p² − 6kpp'm⁺ + 4k²p²p'²)/(m⁺((m⁺)²−p²))`; since `m⁺_k ≡ ±p (mod ℓ)`
(`s ≡ ±1`) and `ℓ ∤ 2p`, `m⁺` and the parenthesized factor (`≡ 2p²`) are `ℓ`-adic units while
`v_ℓ((m⁺)²−p²) ≥ 1`, so `v_ℓ(T_k − 1) = v_ℓ(k) + a − v_ℓ((m⁺)²−p²) ≤ v_ℓ(k) + a − 1`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

section TVal

variable {p p' r s : ℕ}

theorem nOrb_sum (p p' r s k : ℕ) :
    nOrb p p' r s true k + nOrb p p' r s false k = 2 * k * p * p' := by
  unfold nOrb
  simp only [if_true, Bool.false_eq_true, if_false]
  split_ifs <;> ring

theorem nOrb_gt (hp : 2 ≤ p) (hp' : 2 ≤ p') (hr : 0 < r) (hrp : r < p) (hs : 0 < s)
    (hsp : s < p') (hlt : p' * r + p * s < p * p') (ε : Bool) {k : ℕ} (hk : 1 ≤ k) :
    (p : ℤ) < nOrb p p' r s ε k := by
  have hp0 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hp0' : (2 : ℤ) ≤ p' := by exact_mod_cast hp'
  have hr0 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (1 : ℤ) ≤ s := by exact_mod_cast hs
  have hrp' : (r : ℤ) + 1 ≤ p := by exact_mod_cast hrp
  have hsp' : (s : ℤ) + 1 ≤ p' := by exact_mod_cast hsp
  have hlt' : (p' : ℤ) * r + p * s + 1 ≤ p * p' := by exact_mod_cast hlt
  unfold nOrb
  simp only
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hj : (1 : ℤ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    rw [if_pos (by omega)]
    have hpp : (0 : ℤ) ≤ (j - 1) * p * p' := by
      have : (0 : ℤ) ≤ j - 1 := by linarith
      positivity
    cases ε
    · simp only [Bool.false_eq_true, if_false]
      push_cast
      nlinarith
    · simp only [if_true]
      push_cast
      nlinarith
  · rw [if_neg (by omega)]
    have hj : (0 : ℤ) ≤ j := by positivity
    have hpp : (0 : ℤ) ≤ j * p * p' := by positivity
    cases ε
    · simp only [Bool.false_eq_true, if_false]
      push_cast
      nlinarith
    · simp only [if_true]
      push_cast
      nlinarith

theorem not_dvd_of_sq {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {x : ℤ} (h : ¬ (ℓ : ℤ) ∣ x) :
    ¬ (ℓ : ℤ) ∣ x ^ 2 := fun h2 =>
  h ((Nat.prime_iff_prime_int.1 hℓ.out).dvd_of_dvd_pow h2)

/-- `v_ℓ(T_k − 1) ≤ v_ℓ(k) + a − 1` and `T_k ≠ 1` (paper.tex l.1546–1553). -/
theorem T_val {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hp : 2 ≤ p) (hp' : 2 ≤ p')
    (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p) (hs : 0 < s) (hsp : s < p')
    (hlt : p' * r + p * s < p * p') (hℓp' : ℓ ∣ p')
    (hsl : (ℓ : ℤ) ∣ (s : ℤ) - 1 ∨ (ℓ : ℤ) ∣ (s : ℤ) + 1) {k : ℕ} (hk : 1 ≤ k) :
    -((nOrb p p' r s false k : ℚ) * ((nOrb p p' r s false k : ℚ) ^ 2 - (p : ℚ) ^ 2)) /
        ((nOrb p p' r s true k : ℚ) * ((nOrb p p' r s true k : ℚ) ^ 2 - (p : ℚ) ^ 2)) - 1 ≠ 0 ∧
      padicValRat ℓ (-((nOrb p p' r s false k : ℚ) * ((nOrb p p' r s false k : ℚ) ^ 2 -
          (p : ℚ) ^ 2)) / ((nOrb p p' r s true k : ℚ) * ((nOrb p p' r s true k : ℚ) ^ 2 -
          (p : ℚ) ^ 2)) - 1) ≤ (padicValNat ℓ k : ℤ) + padicValNat ℓ p' - 1 := by
  have hpr : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ.out
  have hℓpz : ¬ (ℓ : ℤ) ∣ p := by
    intro h
    have h1 : ℓ ∣ p := Int.natCast_dvd_natCast.1 h
    have := Nat.dvd_gcd h1 hℓp'
    rw [hcop] at this
    exact hℓ.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hℓ2z : ¬ (ℓ : ℤ) ∣ 2 := by
    intro h
    have : ℓ ∣ 2 := by exact_mod_cast Int.natCast_dvd_natCast.1 h
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 this)
  have hℓp'z : (ℓ : ℤ) ∣ p' := Int.natCast_dvd_natCast.2 hℓp'
  set mP := nOrb p p' r s true k with hmP
  set mM := nOrb p p' r s false k with hmM
  have hsum := nOrb_sum p p' r s k
  rw [← hmP, ← hmM] at hsum
  set σ : ℤ := 2 * k * p * p' with hσ
  set W : ℤ := mP ^ 2 - mP * mM + mM ^ 2 - p ^ 2 with hW
  -- `ℓ ∣ (m⁺)² − p²`
  obtain ⟨t, σ', hσ', he⟩ := nOrb_mod p p' r s true k
  rw [← hmP] at he
  have hdq : (ℓ : ℤ) ∣ mP ^ 2 - (p : ℤ) ^ 2 := by
    have hσσ : σ' * σ' = 1 := by rcases hσ' with rfl | rfl <;> norm_num
    have e : mP ^ 2 - (p : ℤ) ^ 2 =
        p' * (p' * t ^ 2 + 2 * t * σ' * p * s) + (σ' * σ') * ((s - 1) * (s + 1)) * p * p +
          ((σ' * σ') - 1) * p * p := by rw [he]; ring
    rw [e, hσσ, sub_self, zero_mul, zero_mul, add_zero, one_mul]
    refine dvd_add (dvd_mul_of_dvd_left hℓp'z _) ?_
    rcases hsl with h | h
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _) _
  have hmPu : ¬ (ℓ : ℤ) ∣ mP := by
    intro h
    have h2 := dvd_sub (dvd_pow h two_ne_zero) hdq
    rw [show mP ^ 2 - (mP ^ 2 - (p : ℤ) ^ 2) = (p : ℤ) ^ 2 by ring] at h2
    exact not_dvd_of_sq hℓpz h2
  have hσd : (ℓ : ℤ) ∣ σ := dvd_mul_of_dvd_right hℓp'z _
  have hWu : ¬ (ℓ : ℤ) ∣ W := by
    intro h
    have hmM : mM = σ - mP := by rw [hσ]; linarith
    have e : W = 3 * (mP ^ 2 - (p : ℤ) ^ 2) - 3 * σ * mP + σ ^ 2 + 2 * (p : ℤ) ^ 2 := by
      rw [hW, hmM]; ring
    have h2 : (ℓ : ℤ) ∣ 2 * (p : ℤ) ^ 2 := by
      have e2 : 2 * (p : ℤ) ^ 2 = W - 3 * (mP ^ 2 - (p : ℤ) ^ 2) + 3 * σ * mP - σ ^ 2 := by
        rw [e]; ring
      rw [e2]
      exact dvd_sub (dvd_add (dvd_sub h (dvd_mul_of_dvd_right hdq 3))
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hσd 3) mP)) (dvd_pow hσd two_ne_zero)
    rcases hpr.dvd_or_dvd h2 with h3 | h3
    · exact hℓ2z h3
    · exact not_dvd_of_sq hℓpz h3
  -- nonvanishing
  have hmP0 : (p : ℤ) < mP := nOrb_gt hp hp' hr hrp hs hsp hlt true hk
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
  have hmPne : (mP : ℚ) ≠ 0 := by exact_mod_cast (show mP ≠ 0 by omega)
  have hdne : ((mP ^ 2 - (p : ℤ) ^ 2 : ℤ) : ℚ) ≠ 0 := by
    have : mP ^ 2 - (p : ℤ) ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hσne : (σ : ℚ) ≠ 0 := by
    have : σ ≠ 0 := by
      rw [hσ]
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk
      positivity
    exact_mod_cast this
  have hWne : (W : ℚ) ≠ 0 := by
    have : W ≠ 0 := fun h => hWu (h ▸ dvd_zero _)
    exact_mod_cast this
  -- the identity for `T − 1`
  have hT1 : -((mM : ℚ) * ((mM : ℚ) ^ 2 - (p : ℚ) ^ 2)) / ((mP : ℚ) * ((mP : ℚ) ^ 2 - (p : ℚ) ^ 2))
      - 1 = -((σ : ℚ) * W) / ((mP : ℚ) * ((mP ^ 2 - (p : ℤ) ^ 2 : ℤ) : ℚ)) := by
    have hsumQ : (mP : ℚ) + mM = σ := by rw [hσ]; exact_mod_cast hsum
    have hd : (mP : ℚ) * ((mP : ℚ) ^ 2 - (p : ℚ) ^ 2) ≠ 0 := by
      refine mul_ne_zero hmPne ?_
      push_cast at hdne
      exact hdne
    rw [div_sub_one hd]
    congr 1
    · rw [hW, ← hsumQ]
      push_cast
      ring
    · push_cast
      ring
  -- `v(σ) = v(k) + a`
  have hvσ : padicValRat ℓ (σ : ℚ) = (padicValNat ℓ k : ℤ) + padicValNat ℓ p' := by
    have h2 : padicValRat ℓ (2 : ℚ) = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd
        (fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 h))
    have hpv : padicValRat ℓ (p : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun h => hℓpz (Int.natCast_dvd_natCast.2 h))
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hp0' : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hp0'' : (p' : ℚ) ≠ 0 := by exact_mod_cast (show p' ≠ 0 by omega)
    rw [hσ]
    push_cast
    rw [padicValRat.mul (by positivity) hp0'', padicValRat.mul (by positivity) hp0',
      padicValRat.mul (by norm_num) hk0, h2, hpv, padicValRat.of_nat, padicValRat.of_nat]
    ring
  have hv1 : 1 ≤ padicValInt ℓ (mP ^ 2 - (p : ℤ) ^ 2) := by
    have hne : (mP ^ 2 - (p : ℤ) ^ 2).natAbs ≠ 0 := by
      have : mP ^ 2 - (p : ℤ) ^ 2 ≠ 0 := by nlinarith
      exact Int.natAbs_ne_zero.2 this
    exact one_le_padicValNat_of_dvd hne (Int.natCast_dvd.1 hdq)
  rw [hT1]
  refine ⟨div_ne_zero (neg_ne_zero.2 (mul_ne_zero hσne hWne)) (mul_ne_zero hmPne hdne), ?_⟩
  rw [padicValRat.div (neg_ne_zero.2 (mul_ne_zero hσne hWne)) (mul_ne_zero hmPne hdne),
    padicValRat.neg, padicValRat.mul hσne hWne, padicValRat.mul hmPne hdne, hvσ,
    padicValRat.of_int, padicValRat.of_int, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd hWu, padicValInt.eq_zero_of_not_dvd hmPu]
  push_cast
  omega

end TVal

end TT

end Virasoro
