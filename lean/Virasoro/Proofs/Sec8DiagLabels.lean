import Virasoro.Proofs.Sec8DiagNodes
import Virasoro.Proofs.Sec8DiagJets

/-!
# Lemma 8.3(ii): the label between two nodes at odd distance

For nodes `ν, ν'` with `L_{ν'} - L_ν` odd and positive, `|S_{ν'}| > |S_ν|`, the integers
`U = ε(S_{ν'} + S_ν)/(2p')`, `V = ε(S_{ν'} - S_ν)/(2p)` (`ε = sgn S_{ν'}`) are positive, the label
`(U, V)` has `x = ε S_ν`, `y = |S_{ν'}|`, and it is the only positive label of weight `ν` leading
to `ν'`: the other sign `x = -ε S_ν` would need `2p' ∣ S_{ν'} - S_ν ≡ ±2ps (mod 2pp')`.
-/

namespace Virasoro

variable {p p' r s : ℕ} {b : ℂ}

theorem nodeWt_eq (a : Node) : nodeWt p p' r s a = momWt p p' (nodeS p p' r s a) := by
  obtain ⟨ε, k⟩ := a
  cases ε <;> simp [nodeWt, muOrb, nodeS, momWt_neg]

theorem kacHL_eq_momWt (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (g : Label) :
    kacHL g b = momWt p p' ((p' : ℤ) * g.1 - p * g.2) := kacH_momWt hp hp' hb _ _

section Pair

variable (hset : MinimalSetting p p' r s b) {ν ν' : Node} (hlt : ν.2 < ν'.2)
  (hodd : (ν'.2 - ν.2) % 2 = 1)
include hset hlt hodd

theorem node_abs_lt : |nodeS p p' r s ν| < |nodeS p p' r s ν'| := by
  obtain ⟨hp2, hp2', -, hr0, hr, hs0, hs, hint, -⟩ := hset
  obtain ⟨e, he, hgap⟩ := nodeS_gap hr0 hr hs0 hs hint ν ν' hlt hodd
  have hpp : (0 : ℤ) < p * p' := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hΔ : (1 : ℤ) ≤ (ν'.2 : ℤ) - ν.2 := by omega
  have : ((ν'.2 : ℤ) - ν.2) * p * p' ≥ p * p' := by nlinarith
  have := abs_lt.1 he
  linarith

/-- `S_{ν'} ± S_ν` are divisible by `2p'` and `2p`. -/
theorem node_dvd :
    (2 * (p' : ℤ)) ∣ nodeS p p' r s ν' + nodeS p p' r s ν ∧
      (2 * (p : ℤ)) ∣ nodeS p p' r s ν' - nodeS p p' r s ν := by
  obtain ⟨m, hm⟩ := nodeS_mod (p := p) (p' := p') (r := r) (s := s) ν
  obtain ⟨m', hm'⟩ := nodeS_mod (p := p) (p' := p') (r := r) (s := s) ν'
  rw [hm, hm']
  rcases Nat.mod_two_eq_zero_or_one ν.2 with h | h
  · have h' : ν'.2 % 2 = 1 := by omega
    simp only [h, h', ↓reduceIte, one_ne_zero]
    exact ⟨⟨r + (m' + m) * p, by ring⟩, ⟨s + (m' - m) * p', by ring⟩⟩
  · have h' : ν'.2 % 2 = 0 := by omega
    simp only [h, h', ↓reduceIte, one_ne_zero]
    exact ⟨⟨r + (m' + m) * p, by ring⟩, ⟨-s + (m' - m) * p', by ring⟩⟩

/-- `2p'` does not divide `S_{ν'} - S_ν`. -/
theorem node_not_dvd : ¬ (2 * (p' : ℤ)) ∣ nodeS p p' r s ν' - nodeS p p' r s ν := by
  obtain ⟨-, hp2', hcop, -, -, hs0, hs, -, -⟩ := hset
  obtain ⟨m, hm⟩ := nodeS_mod (p := p) (p' := p') (r := r) (s := s) ν
  obtain ⟨m', hm'⟩ := nodeS_mod (p := p) (p' := p') (r := r) (s := s) ν'
  rw [hm, hm']
  intro hd
  have key : (p' : ℤ) ∣ (p : ℤ) * s := by
    rcases Nat.mod_two_eq_zero_or_one ν.2 with h | h
    · have h' : ν'.2 % 2 = 1 := by omega
      simp only [h, h', ↓reduceIte, one_ne_zero] at hd
      obtain ⟨c, hc⟩ := hd
      exact ⟨c - (m' - m) * p, by linarith⟩
    · have h' : ν'.2 % 2 = 0 := by omega
      simp only [h, h', ↓reduceIte, one_ne_zero] at hd
      obtain ⟨c, hc⟩ := hd
      exact ⟨-c + (m' - m) * p, by linarith⟩
  have hcop' : IsCoprime (p' : ℤ) p := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop.symm
  have := hcop'.dvd_of_dvd_mul_left key
  have hs' : (s : ℤ) < p' := by exact_mod_cast hs
  have hs0' : (0 : ℤ) < s := by exact_mod_cast hs0
  exact absurd (Int.le_of_dvd hs0' this) (by omega)

end Pair

/-- Lemma 8.3(ii). -/
theorem node_labels_ii (hset : MinimalSetting p p' r s b) (ν ν' : Node) (hlt : ν.2 < ν'.2)
    (hodd : (ν'.2 - ν.2) % 2 = 1) :
    (∀ g : Label, 0 < g.1 → 0 < g.2 →
      (kacHL g b = nodeWt p p' r s ν ∧ kacHL g b + (g.lvl : ℂ) = nodeWt p p' r s ν' ↔
        g = nodeLabel p p' r s ν ν')) ∧
    0 < (nodeLabel p p' r s ν ν').1 ∧ 0 < (nodeLabel p p' r s ν ν').2 ∧
    ((p' : ℤ) * (nodeLabel p p' r s ν ν').1 - p * (nodeLabel p p' r s ν ν').2) *
        ((p' : ℤ) * (nodeLabel p p' r s ν ν').1 + p * (nodeLabel p p' r s ν ν').2) =
      nodeS p p' r s ν * nodeS p p' r s ν' := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  set S := nodeS p p' r s ν with hS
  set S' := nodeS p p' r s ν' with hS'
  have habs : |S| < |S'| := node_abs_lt hset hlt hodd
  have hS'0 : S' ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    linarith [abs_nonneg S]
  obtain ⟨⟨U, hU⟩, ⟨V, hV⟩⟩ := node_dvd hset hlt hodd
  have hU' : S' + S = 2 * (p' : ℤ) * U := hU
  have hV' : S' - S = 2 * (p : ℤ) * V := hV
  set e : ℤ := if 0 < S' then 1 else -1 with he
  have he2 : e * e = 1 := by rw [he]; split_ifs <;> norm_num
  have heS' : e * S' = |S'| := by
    rw [he]; split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_nonpos (not_lt.1 h)]; ring
  have heS : |e * S| = |S| := by
    rw [abs_mul, he]; split_ifs <;> simp
  -- the label
  have hL1 : (nodeLabel p p' r s ν ν').1 = (e * U).toNat := by
    simp only [nodeLabel, ← hS, ← hS', ← he]
    rw [show e * (S' + S) = 2 * (p' : ℤ) * (e * U) by rw [hU']; ring,
      Int.mul_ediv_cancel_left _ (by positivity)]
  have hL2 : (nodeLabel p p' r s ν ν').2 = (e * V).toNat := by
    simp only [nodeLabel, ← hS, ← hS', ← he]
    rw [show e * (S' - S) = 2 * (p : ℤ) * (e * V) by rw [hV']; ring,
      Int.mul_ediv_cancel_left _ (by positivity)]
  have hpos1 : 0 < e * U := by
    have h1 : 2 * (p' : ℤ) * (e * U) = |S'| + e * S := by
      rw [← heS']; linear_combination (-e) * hU'
    have h2 : -|S| ≤ e * S := by rw [← heS]; exact neg_abs_le _
    have : 0 < 2 * (p' : ℤ) * (e * U) := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  have hpos2 : 0 < e * V := by
    have h1 : 2 * (p : ℤ) * (e * V) = |S'| - e * S := by
      rw [← heS']; linear_combination (-e) * hV'
    have h2 : e * S ≤ |S| := by rw [← heS]; exact le_abs_self _
    have : 0 < 2 * (p : ℤ) * (e * V) := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  have hc1 : ((nodeLabel p p' r s ν ν').1 : ℤ) = e * U := by rw [hL1, Int.toNat_of_nonneg hpos1.le]
  have hc2 : ((nodeLabel p p' r s ν ν').2 : ℤ) = e * V := by rw [hL2, Int.toNat_of_nonneg hpos2.le]
  have hx : (p' : ℤ) * (e * U) - p * (e * V) = e * S := by
    have h1 : 2 * ((p' : ℤ) * (e * U) - p * (e * V)) = 2 * (e * S) := by
      linear_combination (-e) * hU' + e * hV'
    linarith
  have hy : (p' : ℤ) * (e * U) + p * (e * V) = e * S' := by
    have h1 : 2 * ((p' : ℤ) * (e * U) + p * (e * V)) = 2 * (e * S') := by
      linear_combination (-e) * hU' + (-e) * hV'
    linarith
  refine ⟨?_, by omega, by omega, ?_⟩
  · intro g hg1 hg2
    constructor
    · rintro ⟨hw, hw'⟩
      rw [kacHL_eq_momWt hp hp' hb, nodeWt_eq, ← hS, momWt_eq_iff hp hp'] at hw
      rw [kacH_add_lvl hp hp' hb, nodeWt_eq, ← hS', momWt_eq_iff hp hp'] at hw'
      have hy0 : 0 < (p' : ℤ) * g.1 + p * g.2 := by positivity
      have hyv : (p' : ℤ) * g.1 + p * g.2 = e * S' := by
        rw [heS']
        have := (sq_eq_sq_iff_abs_eq_abs _ _).1 hw'
        rw [abs_of_pos hy0] at this
        exact this
      have hxv : (p' : ℤ) * g.1 - p * g.2 = e * S := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hw with h | h
        · rcases (show e = 1 ∨ e = -1 by rw [he]; split_ifs <;> simp) with h1 | h1
          · rw [h, h1]; ring
          · exfalso
            apply node_not_dvd hset hlt hodd
            refine ⟨-(g.1 : ℤ), ?_⟩
            rw [h1] at hyv
            linarith
        · rcases (show e = 1 ∨ e = -1 by rw [he]; split_ifs <;> simp) with h1 | h1
          · exfalso
            apply node_not_dvd hset hlt hodd
            refine ⟨(g.1 : ℤ), ?_⟩
            rw [h1] at hyv
            linarith
          · rw [h, h1]; ring
      have hu : (g.1 : ℤ) = e * U := by
        have : 2 * (p' : ℤ) * g.1 = 2 * (p' : ℤ) * (e * U) := by linarith
        exact mul_left_cancel₀ (by positivity) this
      have hv : (g.2 : ℤ) = e * V := by
        have : 2 * (p : ℤ) * g.2 = 2 * (p : ℤ) * (e * V) := by linarith
        exact mul_left_cancel₀ (by positivity) this
      ext
      · exact_mod_cast hu.trans hc1.symm
      · exact_mod_cast hv.trans hc2.symm
    · rintro rfl
      rw [kacH_add_lvl hp hp' hb, kacHL_eq_momWt hp hp' hb, nodeWt_eq, nodeWt_eq, ← hS, ← hS',
        hc1, hc2, hx, hy, momWt_eq_iff hp hp', momWt_eq_iff hp hp']
      exact ⟨by linear_combination S ^ 2 * he2, by linear_combination S' ^ 2 * he2⟩
  · rw [hc1, hc2, hx, hy]
    linear_combination (S * S') * he2

end Virasoro
