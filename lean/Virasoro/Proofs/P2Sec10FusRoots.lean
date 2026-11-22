import Virasoro.Statements.Sec11b
import Virasoro.Proofs.Sec3
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Roots of the fusion polynomials (paper Proposition 10.2(ii), root list (10.10); Lemma 11.1)

The roots in `d` of `P_{R,S}(b;h_{R,S}(b),d)` are `h_{u,v}(b)`, `u ∈ {1,3,…,2R-1}`,
`v ∈ {1,3,…,2S-1}` (paper.tex l.2139–2143, 2155–2159), and the roots of `𝒫_{R,S}(b,d)` are
`h_{u,±v}(b)` (l.2338–2340).
-/

namespace Virasoro

theorem mem_stepRange {r : ℕ} {x : ℤ} :
    x ∈ stepRange r ↔ ∃ i : ℕ, i < r ∧ x = 2 * (i : ℤ) + 1 - r := by
  simp only [stepRange, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem neg_mem_stepRange {r : ℕ} {x : ℤ} (hx : x ∈ stepRange r) : -x ∈ stepRange r := by
  obtain ⟨i, hi, rfl⟩ := mem_stepRange.1 hx
  exact mem_stepRange.2 ⟨r - 1 - i, by omega, by omega⟩

theorem mem_oddsBelow {n k : ℕ} : k ∈ oddsBelow n ↔ k < 2 * n ∧ k % 2 = 1 := by
  simp [oddsBelow]

/-- One paired factor of `P_{R,S}(b;h_{R,S}(b),d)`: with `λ₁ = Rb + Sb⁻¹` it vanishes iff
`λ₂ = ±(λ₁ + jb + lb⁻¹)` or `λ₂ = ±(λ₁ - jb - lb⁻¹)` (l.2155–2159). -/
theorem fus_factor_zero (b d : ℂ) (R S j l : ℤ) :
    ((((R : ℂ) * b + (S : ℂ) * b⁻¹) ^ 2 - ((b + b⁻¹) ^ 2 - 4 * d) +
          ((j : ℂ) * b + (l : ℂ) * b⁻¹) ^ 2) ^ 2 -
        4 * ((R : ℂ) * b + (S : ℂ) * b⁻¹) ^ 2 * ((j : ℂ) * b + (l : ℂ) * b⁻¹) ^ 2) / 16 = 0 ↔
      d = kacH (R + j) (S + l) b ∨ d = kacH (R - j) (S - l) b := by
  have hfac : (((R : ℂ) * b + (S : ℂ) * b⁻¹) ^ 2 - ((b + b⁻¹) ^ 2 - 4 * d) +
          ((j : ℂ) * b + (l : ℂ) * b⁻¹) ^ 2) ^ 2 -
        4 * ((R : ℂ) * b + (S : ℂ) * b⁻¹) ^ 2 * ((j : ℂ) * b + (l : ℂ) * b⁻¹) ^ 2 =
      ((((R : ℂ) + j) * b + ((S : ℂ) + l) * b⁻¹) ^ 2 - ((b + b⁻¹) ^ 2 - 4 * d)) *
        ((((R : ℂ) - j) * b + ((S : ℂ) - l) * b⁻¹) ^ 2 - ((b + b⁻¹) ^ 2 - 4 * d)) := by ring
  rw [hfac, div_eq_zero_iff, mul_eq_zero]
  simp only [kacH, Int.cast_add, Int.cast_sub]
  constructor
  · rintro ((h | h) | h)
    · left; linear_combination h / 4
    · right; linear_combination h / 4
    · norm_num at h
  · rintro (h | h)
    · left; left; linear_combination 4 * h
    · left; right; linear_combination 4 * h

/-- The root list (10.10): the roots in `d` of `P_{R,S}(b;h_{R,S}(b),d)` are `h_{u,v}(b)` with
`u ∈ {1,3,…,2R-1}`, `v ∈ {1,3,…,2S-1}`. -/
theorem fusP_roots (R S : ℕ) (b d : ℂ) :
    fusP R S b (kacH R S b) d = 0 ↔
      ∃ u ∈ oddsBelow R, ∃ v ∈ oddsBelow S, d = kacH (u : ℤ) (v : ℤ) b := by
  have hA : (b + b⁻¹) ^ 2 - 4 * kacH (R : ℤ) (S : ℤ) b = ((R : ℂ) * b + (S : ℂ) * b⁻¹) ^ 2 := by
    simp only [kacH, Int.cast_natCast]; ring
  have hmain : fusP R S b (kacH R S b) d = 0 ↔
      (((0 : ℤ) ∈ stepRange R ∧ (0 : ℤ) ∈ stepRange S) ∧ d = kacH R S b) ∨
      ∃ x ∈ (stepRange R ×ˢ stepRange S).filter
          (fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2)),
        d = kacH (R + x.1) (S + x.2) b ∨ d = kacH (R - x.1) (S - x.2) b := by
    simp only [fusP, hA]
    rw [mul_eq_zero, Finset.prod_eq_zero_iff]
    refine or_congr ?_ ?_
    · by_cases h0 : (0 : ℤ) ∈ stepRange R ∧ (0 : ℤ) ∈ stepRange S
      · rw [if_pos h0]
        simp only [h0, true_and]
        rw [div_eq_zero_iff]
        simp only [kacH, Int.cast_natCast]
        constructor
        · rintro (h | h)
          · linear_combination h / 4
          · norm_num at h
        · intro h; left; linear_combination 4 * h
      · rw [if_neg h0]; simp [h0]
    · refine exists_congr fun x => and_congr_right fun _ => ?_
      have := fus_factor_zero b d R S x.1 x.2
      simpa only [Int.cast_natCast] using this
  rw [hmain]
  constructor
  · rintro (⟨⟨hR, hS⟩, rfl⟩ | ⟨x, hx, hd⟩)
    · obtain ⟨i, hi, hRi⟩ := mem_stepRange.1 hR
      obtain ⟨i', hi', hSi⟩ := mem_stepRange.1 hS
      exact ⟨R, mem_oddsBelow.2 ⟨by omega, by omega⟩, S, mem_oddsBelow.2 ⟨by omega, by omega⟩, rfl⟩
    · rw [Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨i, hi, hxi⟩ := mem_stepRange.1 hx.1.1
      obtain ⟨i', hi', hxi'⟩ := mem_stepRange.1 hx.1.2
      rcases hd with rfl | rfl
      · refine ⟨2 * i + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * i' + 1,
          mem_oddsBelow.2 ⟨by omega, by omega⟩, ?_⟩
        congr 1 <;> push_cast <;> omega
      · refine ⟨2 * (R - 1 - i) + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * (S - 1 - i') + 1,
          mem_oddsBelow.2 ⟨by omega, by omega⟩, ?_⟩
        congr 1 <;> omega
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [mem_oddsBelow] at hu hv
    have hj : (u : ℤ) - R ∈ stepRange R := mem_stepRange.2 ⟨u / 2, by omega, by omega⟩
    have hl : (v : ℤ) - S ∈ stepRange S := mem_stepRange.2 ⟨v / 2, by omega, by omega⟩
    by_cases h00 : (u : ℤ) - R = 0 ∧ (v : ℤ) - S = 0
    · left
      refine ⟨⟨h00.1 ▸ hj, h00.2 ▸ hl⟩, ?_⟩
      congr 1 <;> omega
    · right
      by_cases hpos : 0 < (u : ℤ) - R ∨ ((u : ℤ) - R = 0 ∧ 0 < (v : ℤ) - S)
      · refine ⟨((u : ℤ) - R, (v : ℤ) - S), ?_, Or.inl ?_⟩
        · rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hj, hl⟩, hpos⟩
        · congr 1 <;> ring
      · refine ⟨(-((u : ℤ) - R), -((v : ℤ) - S)), ?_, Or.inr ?_⟩
        · rw [Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨neg_mem_stepRange hj, neg_mem_stepRange hl⟩, ?_⟩
          show 0 < -((u : ℤ) - R) ∨ (-((u : ℤ) - R) = 0 ∧ 0 < -((v : ℤ) - S))
          omega
        · congr 1 <;> ring

/-- The roots in `d` of `𝒫_{R,S}(b,d)` are `h_{u,±v}(b)`, `u ∈ {1,3,…,2R-1}`,
`v ∈ {1,3,…,2S-1}` (l.2338–2340). -/
theorem genP_roots (R S : ℕ) (b d : ℂ) :
    genP R S b d = 0 ↔
      ∃ u ∈ oddsBelow R, ∃ v ∈ oddsBelow S,
        d = kacH (u : ℤ) (v : ℤ) b ∨ d = kacH (u : ℤ) (-(v : ℤ)) b := by
  simp only [genP, Finset.prod_eq_zero_iff, mul_eq_zero, div_eq_zero_iff, lamSq]
  refine exists_congr fun u => and_congr_right fun _ => exists_congr fun v =>
    and_congr_right fun _ => ?_
  simp only [kacH, Int.cast_natCast, Int.cast_neg]
  constructor
  · rintro ((h | h) | (h | h))
    · left; linear_combination -h / 4
    · norm_num at h
    · right; linear_combination -h / 4
    · norm_num at h
  · rintro (h | h)
    · left; left; linear_combination -4 * h
    · right; left; linear_combination -4 * h

/-- Paper equation (10.4): at `b⋆² = -p'/p`, `h_{u,v}(b⋆) = h_{u',v'}(b⋆)` iff
`p'u - pv = ±(p'u' - pv')`. -/
theorem kacH_eq_iff {p p' : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p')
    (hb : b ^ 2 = -(p' : ℂ) / p) (u v u' v' : ℤ) :
    kacH u v b = kacH u' v' b ↔
      ((p' : ℤ) * u - p * v = p' * u' - p * v' ∨ (p' : ℤ) * u - p * v = -(p' * u' - p * v')) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have e := fun r s : ℤ => kacH_minimal p p' hpc hpc' b hb r s
  unfold kacH
  rw [e, e, div_left_inj' (by simp [hpc, hpc'] : (4 * (p : ℂ) * p') ≠ 0), sub_left_inj,
    sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rintro (h | h)
    · left; exact_mod_cast h
    · right; exact_mod_cast h

end Virasoro
