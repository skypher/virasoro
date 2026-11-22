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
