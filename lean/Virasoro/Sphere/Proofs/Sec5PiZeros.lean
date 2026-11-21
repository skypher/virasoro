import Virasoro.Irreducible
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Data.Complex.Basic

/-!
# Sphere paper Lemma 5.2 (iii): the zero locus of `P_{R,S}(b⋆,Δ_a,Δ_b)`

`sphere/paper.tex` l.1539–1547.  With `b⋆² = -p'/p`, `Δ_a = (a_a² - (p'-p)²)/(4pp')` and
`Δ_b` likewise, the factor of `P_{R,S}` for `(j,l)` is
`(a_b-a_a-n)(a_b+a_a+n)(a_b-a_a+n)(a_b+a_a-n)/(16 (pp')²)` with `n = jp' - lp`, so the zeros
are the hyperplanes `a_a ± a_b = ±(jp'-lp)`, and `|jp'-lp| ≤ (R-1)p' + (S-1)p`, attained at
`(j,l) = (R-1,-(S-1))`.
-/

namespace Virasoro.Sphere

/-- The weight `(a² - (p'-p)²)/(4pp')`. -/
noncomputable def wtOf (p p' : ℕ) (a : ℂ) : ℂ := (a ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')

theorem mem_stepRange_bound {r : ℕ} {x : ℤ} (hx : x ∈ stepRange r) :
    1 - (r : ℤ) ≤ x ∧ x ≤ (r : ℤ) - 1 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  have := Finset.mem_range.1 hi
  constructor <;> omega

section

variable {p p' : ℕ} {b : ℂ}

/-- One factor of `P_{R,S}(b⋆)` in the momentum variables. -/
theorem fus_factor (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (aa ab : ℂ)
    (x1 x2 : ℤ) :
    ((((b + b⁻¹) ^ 2 - 4 * wtOf p p' aa) - ((b + b⁻¹) ^ 2 - 4 * wtOf p p' ab) +
          ((x1 : ℂ) * b + (x2 : ℂ) * b⁻¹) ^ 2) ^ 2 -
        4 * ((b + b⁻¹) ^ 2 - 4 * wtOf p p' aa) * ((x1 : ℂ) * b + (x2 : ℂ) * b⁻¹) ^ 2) =
      (ab - aa - ((x1 : ℂ) * p' - x2 * p)) * (ab + aa + ((x1 : ℂ) * p' - x2 * p)) *
        (ab - aa + ((x1 : ℂ) * p' - x2 * p)) * (ab + aa - ((x1 : ℂ) * p' - x2 * p)) /
          ((p : ℂ) * p') ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0] at hb
    have : (0 : ℂ) = -(p' : ℂ) / p := by simpa using hb
    field_simp at this
    exact hp'0 (by linear_combination this)
  have hbi : (b⁻¹) ^ 2 = -(p : ℂ) / p' := by
    rw [inv_pow, hb]
    field_simp
  have h1 : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
  have hA : ∀ a : ℂ, (b + b⁻¹) ^ 2 - 4 * wtOf p p' a = -a ^ 2 / (p * p') := by
    intro a
    have e : (b + b⁻¹) ^ 2 = b ^ 2 + 2 * (b * b⁻¹) + (b⁻¹) ^ 2 := by ring
    rw [e, hb, hbi, h1, wtOf]
    field_simp
    ring
  have ht : ((x1 : ℂ) * b + (x2 : ℂ) * b⁻¹) ^ 2 =
      -((x1 : ℂ) * p' - x2 * p) ^ 2 / (p * p') := by
    have e : ((x1 : ℂ) * b + (x2 : ℂ) * b⁻¹) ^ 2 =
        (x1 : ℂ) ^ 2 * b ^ 2 + 2 * x1 * x2 * (b * b⁻¹) + (x2 : ℂ) ^ 2 * (b⁻¹) ^ 2 := by ring
    rw [e, hb, hbi, h1]
    field_simp
    ring
  rw [hA, hA, ht]
  field_simp
  ring

theorem fus_pref (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (aa ab : ℂ) :
    ((b + b⁻¹) ^ 2 - 4 * wtOf p p' aa) - ((b + b⁻¹) ^ 2 - 4 * wtOf p p' ab) =
      (ab - aa) * (ab + aa) / ((p : ℂ) * p') := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [wtOf]
  field_simp
  ring

/-- Every zero of `P_{R,S}(b⋆)` lies on a hyperplane `a_a ± a_b = c₀` with
`|c₀| ≤ (R-1)p' + (S-1)p`. -/
theorem fusP_zero_bound (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) {R S : ℕ}
    (hR : 0 < R) (hS : 0 < S) (aa ab : ℂ)
    (h0 : fusP R S b (wtOf p p' aa) (wtOf p p' ab) = 0) :
    ∃ c₀ : ℤ, |c₀| ≤ (R : ℤ) * p' + S * p - p' - p ∧
      (aa + ab = (c₀ : ℂ) ∨ aa - ab = (c₀ : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpp : ((p : ℂ) * p') ≠ 0 := mul_ne_zero hp0 hp'0
  have hbnd : (0 : ℤ) ≤ (R : ℤ) * p' + S * p - p' - p := by
    have h1 : (p' : ℤ) ≤ (R : ℤ) * p' := by nlinarith
    have h2 : (p : ℤ) ≤ (S : ℤ) * p := by nlinarith
    linarith
  simp only [fusP] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · split_ifs at h with hc
    · rw [fus_pref hp hp' hb, div_div, div_eq_zero_iff] at h
      rcases h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact ⟨0, by simpa using hbnd, Or.inr (by push_cast; linear_combination -h)⟩
        · exact ⟨0, by simpa using hbnd, Or.inl (by push_cast; linear_combination h)⟩
      · exact absurd h (mul_ne_zero hpp (by norm_num))
    · exact absurd h one_ne_zero
  · obtain ⟨x, hx, hx0⟩ := Finset.prod_eq_zero_iff.1 h
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 (Finset.mem_filter.1 hx).1
    obtain ⟨a1, a2⟩ := mem_stepRange_bound hx1
    obtain ⟨a3, a4⟩ := mem_stepRange_bound hx2
    have hn : |x.1 * (p' : ℤ) - x.2 * p| ≤ (R : ℤ) * p' + S * p - p' - p := by
      rw [abs_le]
      constructor <;> nlinarith
    have hn' : |-(x.1 * (p' : ℤ) - x.2 * p)| ≤ (R : ℤ) * p' + S * p - p' - p := by
      rwa [abs_neg]
    rw [div_eq_zero_iff] at hx0
    rcases hx0 with hx0 | hx0
    swap
    · norm_num at hx0
    rw [fus_factor hp hp' hb, div_eq_zero_iff] at hx0
    rcases hx0 with hx0 | hx0
    swap
    · exact absurd hx0 (pow_ne_zero 2 hpp)
    rcases mul_eq_zero.1 hx0 with hx0 | h4
    · rcases mul_eq_zero.1 hx0 with hx0 | h3
      · rcases mul_eq_zero.1 hx0 with h1 | h2
        · exact ⟨_, hn', Or.inr (by push_cast; linear_combination -h1)⟩
        · exact ⟨_, hn', Or.inl (by push_cast; linear_combination h2)⟩
      · exact ⟨_, hn, Or.inr (by push_cast; linear_combination -h3)⟩
    · exact ⟨_, hn, Or.inl (by push_cast; linear_combination h4)⟩

/-- Both hyperplanes `a_a - a_b = ±((R-1)p' + (S-1)p)` lie in the zero locus of `P_{R,S}(b⋆)`. -/
theorem fusP_zero_of_extremal (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p)
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) (aa ab : ℂ)
    (h : aa - ab = (((R : ℤ) * p' + S * p - p' - p : ℤ) : ℂ) ∨
      aa - ab = -(((R : ℤ) * p' + S * p - p' - p : ℤ) : ℂ)) :
    fusP R S b (wtOf p p' aa) (wtOf p p' ab) = 0 := by
  have hm0 : ∀ r : ℕ, 0 < r → ((r : ℤ) - 1) ∈ stepRange r := fun r hr =>
    Finset.mem_image.2 ⟨r - 1, Finset.mem_range.2 (by omega), by omega⟩
  have hm1 : ∀ r : ℕ, 0 < r → (1 - (r : ℤ)) ∈ stepRange r := fun r hr =>
    Finset.mem_image.2 ⟨0, Finset.mem_range.2 hr, by simp⟩
  simp only [fusP]
  have hfac : ∀ x : ℤ × ℤ, x ∈ ((stepRange R ×ˢ stepRange S).filter fun x : ℤ × ℤ =>
        0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2)) →
      (aa - ab = ((x.1 : ℂ) * p' - x.2 * p) ∨ aa - ab = -((x.1 : ℂ) * p' - x.2 * p)) →
      (if (0 : ℤ) ∈ stepRange R ∧ (0 : ℤ) ∈ stepRange S then
          ((b + b⁻¹) ^ 2 - 4 * wtOf p p' aa - ((b + b⁻¹) ^ 2 - 4 * wtOf p p' ab)) / 4 else 1) *
        ∏ x ∈ (stepRange R ×ˢ stepRange S).filter fun x : ℤ × ℤ =>
            0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
          (((b + b⁻¹) ^ 2 - 4 * wtOf p p' aa - ((b + b⁻¹) ^ 2 - 4 * wtOf p p' ab) +
                ((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2) ^ 2 -
              4 * ((b + b⁻¹) ^ 2 - 4 * wtOf p p' aa) *
                ((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2) / 16 = 0 := by
    intro x hx hxa
    rw [Finset.prod_eq_zero hx, mul_zero]
    rw [fus_factor hp hp' hb]
    rcases hxa with hxa | hxa
    · have : ab - aa + ((x.1 : ℂ) * p' - x.2 * p) = 0 := by linear_combination -hxa
      rw [this]
      simp
    · have : ab - aa - ((x.1 : ℂ) * p' - x.2 * p) = 0 := by linear_combination -hxa
      rw [this]
      simp
  by_cases hR2 : 2 ≤ R
  · refine hfac ((R : ℤ) - 1, 1 - (S : ℤ)) (Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hm0 R hR, hm1 S hS⟩, Or.inl (by simp; omega)⟩) ?_
    rcases h with h | h
    · exact Or.inl (by rw [h]; push_cast; ring)
    · exact Or.inr (by rw [h]; push_cast; ring)
  · have hR1 : R = 1 := by omega
    subst hR1
    by_cases hS2 : 2 ≤ S
    · refine hfac ((0 : ℤ), (S : ℤ) - 1) (Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨by simpa using hm0 1 one_pos, hm0 S hS⟩,
          Or.inr ⟨rfl, by simp; omega⟩⟩) ?_
      rcases h with h | h
      · exact Or.inr (by rw [h]; push_cast; ring)
      · exact Or.inl (by rw [h]; push_cast; ring)
    · have hS1 : S = 1 := by omega
      subst hS1
      have hab : aa - ab = 0 := by
        rcases h with h | h <;> rw [h] <;> push_cast <;> ring
      have h00 : (0 : ℤ) ∈ stepRange 1 := by simpa using hm0 1 one_pos
      rw [if_pos ⟨h00, h00⟩, fus_pref hp hp' hb]
      have : ab - aa = 0 := by linear_combination -hab
      rw [this]
      simp

end

end Virasoro.Sphere
