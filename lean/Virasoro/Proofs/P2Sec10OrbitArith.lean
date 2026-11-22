import Virasoro.Proofs.P2Sec11Fusion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Arithmetic of the braided orbit and its primitive arrows (paper Lemma 10.3(ii)–(iv))

The momenta (10.5), the consecutive-layer formulas that supply the Kac label of each primitive
arrow (paper.tex l.2240–2248), and the congruences and bounds (10.11)–(10.13) (l.2250–2262).
-/

namespace Virasoro

section Momenta

variable (p p' r s : ℕ)

theorem nOrb_even_true (j : ℕ) :
    nOrb p p' r s true (2 * j) = 2 * (j : ℤ) * p * p' + ((p' : ℤ) * r - p * s) := by
  simp [nOrb]

theorem nOrb_even_false (j : ℕ) :
    nOrb p p' r s false (2 * j) = 2 * (j : ℤ) * p * p' - ((p' : ℤ) * r - p * s) := by
  simp [nOrb]

theorem nOrb_odd_true (j : ℕ) :
    nOrb p p' r s true (2 * j + 1) = 2 * (j : ℤ) * p * p' + ((p' : ℤ) * r + p * s) := by
  have h : (2 * j + 1) % 2 ≠ 0 := by omega
  simp only [nOrb, h, ↓reduceIte]
  push_cast
  ring

theorem nOrb_odd_false (j : ℕ) :
    nOrb p p' r s false (2 * j + 1) =
      (2 * (j : ℤ) + 2) * p * p' - ((p' : ℤ) * r + p * s) := by
  have h : (2 * j + 1) % 2 ≠ 0 := by omega
  simp only [nOrb, h, ↓reduceIte, Bool.false_eq_true]
  push_cast
  ring

end Momenta

variable {p p' r s : ℕ} {b : ℂ}

/-- The consecutive-layer formulas (l.2247–2248, 2254–2259): each primitive arrow
`μ^ε_k → μ^{ε'}_{k+1}` has a positive pair `(R,S)` with `p'R + pS = n_ν`, `p'R - pS = ±n_μ`,
`R ≡ r` or `p-r (mod p)`, `S ≡ s` or `p'-s (mod p')`, and `R < p` or `S < p'`. -/
theorem arrow_data (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s) (hs : s < p') (ε : Bool) (k : ℕ)
    (ε' : Bool) :
    ∃ R S : ℕ, 0 < R ∧ 0 < S ∧
      (p' : ℤ) * R + p * S = nOrb p p' r s ε' (k + 1) ∧
      ((p' : ℤ) * R - p * S = nOrb p p' r s ε k ∨
        (p' : ℤ) * R - p * S = -nOrb p p' r s ε k) ∧
      (∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r)) ∧
      (∃ a : ℕ, S = a * p' + s ∨ S = a * p' + (p' - s)) ∧ (R < p ∨ S < p') := by
  have cr : ((p - r : ℕ) : ℤ) = p - r := Nat.cast_sub hr.le
  have cs : ((p' - s : ℕ) : ℤ) = p' - s := Nat.cast_sub hs.le
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · cases ε <;> cases ε'
    · -- `μ⁻_{2j} → μ⁻_{2j+1}`
      refine ⟨2 * j * p + (p - r), p' - s, by omega, by omega, ?_, Or.inl ?_,
        ⟨2 * j, Or.inr rfl⟩, ⟨0, Or.inr (by simp)⟩, Or.inr (by omega)⟩
      · rw [nOrb_odd_false]; push_cast [cr, cs]; ring
      · rw [nOrb_even_false]; push_cast [cr, cs]; ring
    · -- `μ⁻_{2j} → μ⁺_{2j+1}`
      refine ⟨r, 2 * j * p' + s, by omega, by omega, ?_, Or.inr ?_,
        ⟨0, Or.inl (by simp)⟩, ⟨2 * j, Or.inl rfl⟩, Or.inl hr⟩
      · rw [nOrb_odd_true]; push_cast; ring
      · rw [nOrb_even_false]; push_cast; ring
    · -- `μ⁺_{2j} → μ⁻_{2j+1}`
      refine ⟨p - r, 2 * j * p' + (p' - s), by omega, by omega, ?_, Or.inr ?_,
        ⟨0, Or.inr (by simp)⟩, ⟨2 * j, Or.inr rfl⟩, Or.inl (by omega)⟩
      · rw [nOrb_odd_false]; push_cast [cr, cs]; ring
      · rw [nOrb_even_true]; push_cast [cr, cs]; ring
    · -- `μ⁺_{2j} → μ⁺_{2j+1}`
      refine ⟨2 * j * p + r, s, by omega, by omega, ?_, Or.inl ?_,
        ⟨2 * j, Or.inl rfl⟩, ⟨0, Or.inl (by simp)⟩, Or.inr hs⟩
      · rw [nOrb_odd_true]; push_cast; ring
      · rw [nOrb_even_true]; push_cast; ring
  · have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e]
    cases ε <;> cases ε'
    · -- `μ⁻_{2j+1} → μ⁻_{2j+2}`
      refine ⟨(2 * j + 1) * p + (p - r), s, by omega, by omega, ?_, Or.inl ?_,
        ⟨2 * j + 1, Or.inr rfl⟩, ⟨0, Or.inl (by simp)⟩, Or.inr hs⟩
      · rw [nOrb_even_false]; push_cast [cr, cs]; ring
      · rw [nOrb_odd_false]; push_cast [cr, cs]; ring
    · -- `μ⁻_{2j+1} → μ⁺_{2j+2}`
      refine ⟨r, (2 * j + 1) * p' + (p' - s), by omega, by omega, ?_, Or.inr ?_,
        ⟨0, Or.inl (by simp)⟩, ⟨2 * j + 1, Or.inr rfl⟩, Or.inl hr⟩
      · rw [nOrb_even_true]; push_cast [cr, cs]; ring
      · rw [nOrb_odd_false]; push_cast [cr, cs]; ring
    · -- `μ⁺_{2j+1} → μ⁻_{2j+2}`
      refine ⟨p - r, (2 * j + 1) * p' + s, by omega, by omega, ?_, Or.inr ?_,
        ⟨0, Or.inr (by simp)⟩, ⟨2 * j + 1, Or.inl rfl⟩, Or.inl (by omega)⟩
      · rw [nOrb_even_false]; push_cast [cr, cs]; ring
      · rw [nOrb_odd_true]; push_cast [cr, cs]; ring
    · -- `μ⁺_{2j+1} → μ⁺_{2j+2}`
      refine ⟨(2 * j + 1) * p + r, p' - s, by omega, by omega, ?_, Or.inl ?_,
        ⟨2 * j + 1, Or.inl rfl⟩, ⟨0, Or.inr (by simp)⟩, Or.inr (by omega)⟩
      · rw [nOrb_even_true]; push_cast [cr, cs]; ring
      · rw [nOrb_odd_true]; push_cast [cr, cs]; ring

/-- `R ≡ ±r (mod p)` with `0 < r < p` is not divisible by `p`. -/
theorem not_dvd_of_congr {p r R : ℕ} (hr0 : 0 < r) (hr : r < p)
    (h : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r)) : ¬ (p : ℤ) ∣ (R : ℤ) := by
  intro hd
  rw [Int.natCast_dvd_natCast] at hd
  obtain ⟨a, rfl | rfl⟩ := h
  · have := (Nat.dvd_add_right (Dvd.intro_left a rfl)).1 hd
    have := Nat.le_of_dvd hr0 this
    omega
  · have := (Nat.dvd_add_right (Dvd.intro_left a rfl)).1 hd
    have := Nat.le_of_dvd (by omega) this
    omega

/-- `p ∤ n_μ` and `p' ∤ n_μ` for every momentum of the orbit (l.2244–2245): `n_μ` is
`±p'r ± ps` modulo `pp'`. -/
theorem nOrb_not_dvd (hcop : Nat.Coprime p p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') (ε : Bool) (k : ℕ) :
    ¬ (p : ℤ) ∣ nOrb p p' r s ε k ∧ ¬ (p' : ℤ) ∣ nOrb p p' r s ε k := by
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hpr : ¬ (p : ℤ) ∣ (p' : ℤ) * r := fun h =>
    not_dvd_of_congr hr0 hr ⟨0, Or.inl (by simp)⟩ (hc.dvd_of_dvd_mul_left h)
  have hps : ¬ (p' : ℤ) ∣ (p : ℤ) * s := fun h =>
    not_dvd_of_congr hs0 hs ⟨0, Or.inl (by simp)⟩ (hc.symm.dvd_of_dvd_mul_left h)
  have key : ∀ (q x : ℤ) (A B : ℤ), x = q * A + B → q ∣ x → q ∣ B := fun q x A B e h => by
    rw [e] at h
    exact (dvd_add_right (dvd_mul_right _ _)).1 h
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k <;> cases ε
  · rw [nOrb_even_false]
    exact ⟨fun h => hpr (dvd_neg.1 (key _ _ (2 * j * p' + s) _ (by ring) h)),
      fun h => hps (key _ _ (2 * j * p - r) _ (by ring) h)⟩
  · rw [nOrb_even_true]
    exact ⟨fun h => hpr (key _ _ (2 * j * p' - s) _ (by ring) h),
      fun h => hps (dvd_neg.1 (key _ _ (2 * j * p + r) _ (by ring) h))⟩
  · rw [nOrb_odd_false]
    exact ⟨fun h => hpr (dvd_neg.1 (key _ _ ((2 * j + 2) * p' - s) _ (by ring) h)),
      fun h => hps (dvd_neg.1 (key _ _ ((2 * j + 2) * p - r) _ (by ring) h))⟩
  · rw [nOrb_odd_true]
    exact ⟨fun h => hpr (key _ _ (2 * j * p' + s) _ (by ring) h),
      fun h => hps (key _ _ (2 * j * p + r) _ (by ring) h)⟩

/-- `n_μ ≡ ±p'r (mod p)` and `n_μ ≡ ±ps (mod p')` (from (10.5), l.2250–2251). -/
theorem nOrb_mod (ε : Bool) (k : ℕ) :
    (∃ u : ℤ, (u = 1 ∨ u = -1) ∧ (p : ℤ) ∣ nOrb p p' r s ε k - u * (p' * r)) ∧
      (∃ v : ℤ, (v = 1 ∨ v = -1) ∧ (p' : ℤ) ∣ nOrb p p' r s ε k - v * (p * s)) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k <;> cases ε
  · rw [nOrb_even_false]
    exact ⟨⟨-1, Or.inr rfl, ⟨2 * j * p' + s, by ring⟩⟩, ⟨1, Or.inl rfl, ⟨2 * j * p - r, by ring⟩⟩⟩
  · rw [nOrb_even_true]
    exact ⟨⟨1, Or.inl rfl, ⟨2 * j * p' - s, by ring⟩⟩, ⟨-1, Or.inr rfl, ⟨2 * j * p + r, by ring⟩⟩⟩
  · rw [nOrb_odd_false]
    exact ⟨⟨-1, Or.inr rfl, ⟨(2 * j + 2) * p' - s, by ring⟩⟩,
      ⟨-1, Or.inr rfl, ⟨(2 * j + 2) * p - r, by ring⟩⟩⟩
  · rw [nOrb_odd_true]
    exact ⟨⟨1, Or.inl rfl, ⟨2 * j * p' + s, by ring⟩⟩, ⟨1, Or.inl rfl, ⟨2 * j * p + r, by ring⟩⟩⟩

/-- `R ≡ ±r (mod p)` from `p ∣ R ∓ r`. -/
theorem exists_of_dvd_pm {p r R : ℕ} (hr0 : 0 < r) (hr : r < p)
    (h : (p : ℤ) ∣ (R : ℤ) - r ∨ (p : ℤ) ∣ (R : ℤ) + r) :
    ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r) := by
  refine ⟨R / p, ?_⟩
  have hdm := Nat.div_add_mod' R p
  rcases h with h | h
  · have hm : r % p = R % p := (Nat.modEq_iff_dvd.2 h)
    rw [Nat.mod_eq_of_lt hr] at hm
    left
    omega
  · have h' : (p : ℤ) ∣ (R : ℤ) - ((p - r : ℕ) : ℤ) := by
      rw [Nat.cast_sub hr.le]
      have := dvd_sub h (dvd_refl (p : ℤ))
      rwa [show (R : ℤ) + r - p = R - (p - r) by ring] at this
    have hm : (p - r) % p = R % p := (Nat.modEq_iff_dvd.2 h')
    rw [Nat.mod_eq_of_lt (by omega : p - r < p)] at hm
    right
    omega

/-- Reduction of `p'R - pS = ±n_μ` modulo `p` and modulo `p'` (l.2250–2253): `R ≡ ±r (mod p)`
and `S ≡ ±s (mod p')`. -/
theorem congr_of_reduce (hcop : Nat.Coprime p p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') {R S : ℕ} {n : ℤ}
    (hn : (∃ u : ℤ, (u = 1 ∨ u = -1) ∧ (p : ℤ) ∣ n - u * (p' * r)) ∧
      (∃ v : ℤ, (v = 1 ∨ v = -1) ∧ (p' : ℤ) ∣ n - v * (p * s)))
    (hdiff : (p' : ℤ) * R - p * S = n ∨ (p' : ℤ) * R - p * S = -n) :
    (∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r)) ∧
      (∃ a : ℕ, S = a * p' + s ∨ S = a * p' + (p' - s)) := by
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨⟨u, hu, hdu⟩, ⟨v, hv, hdv⟩⟩ := hn
  -- modulo `p`: `p ∣ p' (R - w r)` with `w = ±1`
  have hR : ∃ w : ℤ, (w = 1 ∨ w = -1) ∧ (p : ℤ) ∣ (p' : ℤ) * ((R : ℤ) - w * r) := by
    rcases hdiff with h | h
    · refine ⟨u, hu, ?_⟩
      rw [show (p' : ℤ) * ((R : ℤ) - u * r) = (n - u * (p' * r)) + p * S by linear_combination h]
      exact dvd_add hdu (dvd_mul_right _ _)
    · refine ⟨-u, by rcases hu with rfl | rfl <;> simp, ?_⟩
      rw [show (p' : ℤ) * ((R : ℤ) - -u * r) = -(n - u * (p' * r)) + p * S by
        linear_combination h]
      exact dvd_add (dvd_neg.2 hdu) (dvd_mul_right _ _)
  -- modulo `p'`: `p' ∣ p (S - w s)` with `w = ±1`
  have hS : ∃ w : ℤ, (w = 1 ∨ w = -1) ∧ (p' : ℤ) ∣ (p : ℤ) * ((S : ℤ) - w * s) := by
    rcases hdiff with h | h
    · refine ⟨-v, by rcases hv with rfl | rfl <;> simp, ?_⟩
      rw [show (p : ℤ) * ((S : ℤ) - -v * s) = p' * R - (n - v * (p * s)) by linear_combination -h]
      exact dvd_sub (dvd_mul_right _ _) hdv
    · refine ⟨v, hv, ?_⟩
      rw [show (p : ℤ) * ((S : ℤ) - v * s) = p' * R + (n - v * (p * s)) by linear_combination -h]
      exact dvd_add (dvd_mul_right _ _) hdv
  obtain ⟨w, hw, hdw⟩ := hR
  obtain ⟨w', hw', hdw'⟩ := hS
  have h1 := hc.dvd_of_dvd_mul_left hdw
  have h2 := hc.symm.dvd_of_dvd_mul_left hdw'
  refine ⟨exists_of_dvd_pm hr0 hr ?_, exists_of_dvd_pm hs0 hs ?_⟩
  · rcases hw with rfl | rfl
    · exact Or.inl (by simpa using h1)
    · exact Or.inr (by simpa using h1)
  · rcases hw' with rfl | rfl
    · exact Or.inl (by simpa using h2)
    · exact Or.inr (by simpa using h2)

/-- `0 < n_ν - |n_μ| < 2pp'` for every primitive arrow `μ → ν` (l.2254–2259). -/
theorem nOrb_gap (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s) (hs : s < p') (hp : 0 < p)
    (hp' : 0 < p') (ε : Bool) (k : ℕ) (ε' : Bool) :
    0 < nOrb p p' r s ε' (k + 1) - |nOrb p p' r s ε k| ∧
      nOrb p p' r s ε' (k + 1) - |nOrb p p' r s ε k| < 2 * p * p' := by
  have a1 : (0 : ℤ) < (p' : ℤ) * r := by positivity
  have a2 : (0 : ℤ) < (p : ℤ) * s := by positivity
  have a3 : (p' : ℤ) * r < p * p' := by
    have : (r : ℤ) < p := by exact_mod_cast hr
    nlinarith
  have a4 : (p : ℤ) * s < p * p' := by
    have : (s : ℤ) < p' := by exact_mod_cast hs
    nlinarith
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have a5 : (0 : ℤ) ≤ (j : ℤ) * p * p' := by positivity
    have hle := le_abs_self (nOrb p p' r s ε (2 * j))
    cases ε <;> cases ε' <;>
      simp only [nOrb_even_false, nOrb_even_true, nOrb_odd_false, nOrb_odd_true] at hle ⊢ <;>
      exact ⟨sub_pos.2 (abs_lt.2 ⟨by linarith, by linarith⟩), by linarith⟩
  · have a5 : (0 : ℤ) ≤ (j : ℤ) * p * p' := by positivity
    have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e]
    have hpos1 : 0 < 2 * (j : ℤ) * p * p' + ((p' : ℤ) * r + p * s) := by linarith
    have hpos2 : 0 < (2 * (j : ℤ) + 2) * p * p' - ((p' : ℤ) * r + p * s) := by linarith
    cases ε <;> cases ε' <;>
      simp only [nOrb_even_false, nOrb_even_true, nOrb_odd_false, nOrb_odd_true,
        abs_of_pos hpos1, abs_of_pos hpos2] <;> push_cast <;> constructor <;> linarith

/-- `R < p` or `S < p'` from `n_ν - |n_μ| < 2pp'` (l.2259–2262). -/
theorem small_of_gap (hp : 0 < p) (hp' : 0 < p') {R S : ℕ} {nμ nν : ℤ}
    (hsum : (p' : ℤ) * R + p * S = nν)
    (hdiff : (p' : ℤ) * R - p * S = nμ ∨ (p' : ℤ) * R - p * S = -nμ)
    (hgap : nν - |nμ| < 2 * p * p') : R < p ∨ S < p' := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hpz' : (0 : ℤ) < p' := by exact_mod_cast hp'
  have hR : (p' : ℤ) * R < p' * p → R < p := fun h => by
    exact_mod_cast lt_of_mul_lt_mul_left h hpz'.le
  have hS : (p : ℤ) * S < p * p' → S < p' := fun h => by
    exact_mod_cast lt_of_mul_lt_mul_left h hpz.le
  rcases abs_cases nμ with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at hgap <;> rcases hdiff with h | h
  · exact Or.inr (hS (by linarith))
  · exact Or.inl (hR (by linarith))
  · exact Or.inl (hR (by linarith))
  · exact Or.inr (hS (by linarith))

theorem mod_of_congr {p r R : ℕ} (h : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r)) :
    R % p = r % p ∨ R % p = (p - r) % p := by
  obtain ⟨a, rfl | rfl⟩ := h
  · left; rw [Nat.mul_add_mod_self_right]
  · right; rw [Nat.mul_add_mod_self_right]

theorem min_le_of_congr {p r R : ℕ} (h : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r)) :
    min r (p - r) ≤ R := by
  obtain ⟨a, rfl | rfl⟩ := h
  · exact (min_le_left _ _).trans (Nat.le_add_left _ _)
  · exact (min_le_right _ _).trans (Nat.le_add_left _ _)

/-- The label of Lemma 10.3(ii) is `arrowLabel` (l.2242–2247). -/
theorem arrowLabel_eq (hcop : Nat.Coprime p p') (hp : 0 < p) (hp' : 0 < p') {R S : ℕ}
    {nμ nν : ℤ} (hsum : (p' : ℤ) * R + p * S = nν)
    (hdiff : (p' : ℤ) * R - p * S = nμ ∨ (p' : ℤ) * R - p * S = -nμ)
    (hS : ¬ (p' : ℤ) ∣ (S : ℤ)) : arrowLabel p p' nμ nν = ((R : ℤ), (S : ℤ)) := by
  have hp2 : (2 * (p : ℤ)) ≠ 0 := by positivity
  have hp2' : (2 * (p' : ℤ)) ≠ 0 := by positivity
  unfold arrowLabel
  rcases hdiff with h | h
  · have e1 : nν + nμ = 2 * (p' : ℤ) * R := by linarith
    have e2 : nν - nμ = 2 * (p : ℤ) * S := by linarith
    rw [if_pos ⟨R, e1⟩, e1, e2, Int.mul_ediv_cancel_left _ hp2', Int.mul_ediv_cancel_left _ hp2]
  · have e1 : nν + nμ = 2 * (p : ℤ) * S := by linarith
    have e2 : nν - nμ = 2 * (p' : ℤ) * R := by linarith
    have hnd : ¬ (2 * (p' : ℤ)) ∣ nν + nμ := by
      rw [e1, mul_assoc, mul_dvd_mul_iff_left (two_ne_zero)]
      intro hd
      have hc : IsCoprime (p' : ℤ) (p : ℤ) := (Nat.isCoprime_iff_coprime.2 hcop).symm
      exact hS (hc.dvd_of_dvd_mul_left hd)
    rw [if_neg hnd, e1, e2, Int.mul_ediv_cancel_left _ hp2', Int.mul_ediv_cancel_left _ hp2]

/-- The label of Lemma 10.3(ii) is `arrowLabel`, by the paper's argument (l.2242–2247): if
both signs made `n_ν ± n_μ` divisible by `2p'`, then `p' ∣ n_μ`. -/
theorem arrowLabel_eq_of_not_dvd (hp : 0 < p) (hp' : 0 < p') {R S : ℕ} {nμ nν : ℤ}
    (hsum : (p' : ℤ) * R + p * S = nν)
    (hdiff : (p' : ℤ) * R - p * S = nμ ∨ (p' : ℤ) * R - p * S = -nμ)
    (hμ : ¬ (p' : ℤ) ∣ nμ) : arrowLabel p p' nμ nν = ((R : ℤ), (S : ℤ)) := by
  have hp2 : (2 * (p : ℤ)) ≠ 0 := by positivity
  have hp2' : (2 * (p' : ℤ)) ≠ 0 := by positivity
  unfold arrowLabel
  rcases hdiff with h | h
  · have e1 : nν + nμ = 2 * (p' : ℤ) * R := by linarith
    have e2 : nν - nμ = 2 * (p : ℤ) * S := by linarith
    rw [if_pos ⟨R, e1⟩, e1, e2, Int.mul_ediv_cancel_left _ hp2', Int.mul_ediv_cancel_left _ hp2]
  · have e1 : nν + nμ = 2 * (p : ℤ) * S := by linarith
    have e2 : nν - nμ = 2 * (p' : ℤ) * R := by linarith
    have hnd : ¬ (2 * (p' : ℤ)) ∣ nν + nμ := by
      intro hd
      have h2 : 2 * (p' : ℤ) ∣ 2 * nμ := by
        have h3 := dvd_sub hd (⟨R, e2⟩ : 2 * (p' : ℤ) ∣ nν - nμ)
        rwa [show nν + nμ - (nν - nμ) = 2 * nμ by ring] at h3
      exact hμ ((mul_dvd_mul_iff_left two_ne_zero).1 h2)
    rw [if_neg hnd, e1, e2, Int.mul_ediv_cancel_left _ hp2', Int.mul_ediv_cancel_left _ hp2]

theorem momWt_neg (p p' : ℕ) (n : ℤ) : momWt p p' (-n) = momWt p p' n := by
  simp [momWt]

/-- Paper equation (10.4). -/
theorem kacH_momWt (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (u v : ℤ) :
    kacH u v b = momWt p p' ((p' : ℤ) * u - p * v) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  rw [momWt, kacH, kacH_minimal p p' hpc hpc' b hb u v]
  push_cast
  rfl

/-- No pair `(qp, qp')`, `q ≠ 0`, lies in `[1-R,R] × [1-S,S]` when `R < p` or `S < p'`
(l.2262–2263, 2206–2207). -/
theorem box_clause (hp : 0 < p) (hp' : 0 < p') {R S : ℕ} (hsmall : R < p ∨ S < p') (q : ℤ)
    (hq : q ≠ 0) : (q * p, q * p') ∉ boxSet (R : ℤ) (S : ℤ) := by
  intro hmem
  simp only [boxSet, Finset.mem_product, Finset.mem_Icc] at hmem
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hmem
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hpz' : (0 : ℤ) < p' := by exact_mod_cast hp'
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have hq1 : q ≤ -1 := by omega
    rcases hsmall with h | h
    · have : q * p ≤ -1 * p := mul_le_mul_of_nonneg_right hq1 hpz.le
      have hR : (R : ℤ) < p := by exact_mod_cast h
      linarith
    · have : q * p' ≤ -1 * p' := mul_le_mul_of_nonneg_right hq1 hpz'.le
      have hS : (S : ℤ) < p' := by exact_mod_cast h
      linarith
  · have hq1 : 1 ≤ q := by omega
    rcases hsmall with h | h
    · have : 1 * (p : ℤ) ≤ q * p := mul_le_mul_of_nonneg_right hq1 hpz.le
      have hR : (R : ℤ) < p := by exact_mod_cast h
      linarith
    · have : 1 * (p' : ℤ) ≤ q * p' := mul_le_mul_of_nonneg_right hq1 hpz'.le
      have hS : (S : ℤ) < p' := by exact_mod_cast h
      linarith

/-- `max(ℓ⁺₁,ℓ⁻₁) < min(ℓ⁺₂,ℓ⁻₂)` (l.2283–2285). -/
theorem ell_one_lt_two (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s) (hs : s < p') :
    max (ellPlus p p' r s 1) (ellMinus p p' r s 1) <
      min (ellPlus p p' r s 2) (ellMinus p p' r s 2) := by
  have e1 : ellPlus p p' r s 1 = r * s := by simp [ellPlus]
  have e2 : ellMinus p p' r s 1 = (p - r) * (p' - s) := by simp [ellMinus]
  have e3 : ellPlus p p' r s 2 =
      ((p : ℤ) * p' + ((p' : ℤ) * r - p * s)).toNat := by simp [ellPlus]
  have e4 : ellMinus p p' r s 2 =
      ((p : ℤ) * p' - ((p' : ℤ) * r - p * s)).toNat := by simp [ellMinus]
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr0
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs0
  have hrp : (0 : ℤ) < (p : ℤ) - r := by have : (r : ℤ) < p := by exact_mod_cast hr
                                         linarith
  have hsp : (0 : ℤ) < (p' : ℤ) - s := by have : (s : ℤ) < p' := by exact_mod_cast hs
                                          linarith
  have h1 := mul_pos hsp (by linarith : (0 : ℤ) < (p : ℤ) + r)
  have h2 := mul_pos hrp (by linarith : (0 : ℤ) < (p' : ℤ) + s)
  have h3 := mul_pos hrz (by linarith : (0 : ℤ) < 2 * (p' : ℤ) - s)
  have h4 := mul_pos hsz (by linarith : (0 : ℤ) < 2 * (p : ℤ) - r)
  rw [e1, e2, e3, e4]
  refine max_lt (lt_min ?_ ?_) (lt_min ?_ ?_) <;> rw [Int.lt_toNat] <;>
    push_cast [Nat.cast_sub hr.le, Nat.cast_sub hs.le] <;> nlinarith

end Virasoro
