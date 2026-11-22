import Virasoro.Proofs.Sec6TTEps

/-!
# Proposition 6.9, Case 3: the closed form of `T_k` (paper.tex l.1534–1546)

Multiplying the per-factor relations over the factors of `τ^±_k` (all have `p ∤ R`):
`∏cof(d₁) · (−2x₁)^k · ∏Λ_den = ∏cof(d₂) · (2x₂)^k · ∏Λ_num`, with
`Λ_num(R,S) = 8D(D²−p²)`, `Λ_den(R,S) = 8m(m²−p²)`, `D = Rp'−Sp`, `m = Rp'+Sp`.  The common
factor (`k` even) cancels in the branch ratio; the other factors have `m = m^±_k` and
`D⁻ = −D⁺ ∉ {0, ±p}`, so
`T_k = −m⁻((m⁻)²−p²)/(m⁺((m⁺)²−p²))`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

section Tk

variable {p p' r s : ℕ}

/-- `Λ_num/Λ_den` of a factor. -/
def lamF (p p' : ℕ) (RS : ℕ × ℕ) : ℚ :=
  (Hw p p' RS.1 (2 * RS.2 - 2) * Hw p p' RS.1 (2 * RS.2) * Hw p p' RS.1 (2 * RS.2 + 2)) /
    (Hw p p' RS.1 (2 - 2 * RS.2) * Hw p p' RS.1 (-2 * RS.2) * Hw p p' RS.1 (-2 * RS.2 - 2))

theorem lamF_eq (p p' : ℕ) (RS : ℕ × ℕ) :
    lamF p p' RS =
      (((RS.1 : ℚ) * p' - RS.2 * p) * (((RS.1 : ℚ) * p' - RS.2 * p) ^ 2 - (p : ℚ) ^ 2)) /
        (((RS.1 : ℚ) * p' + RS.2 * p) * (((RS.1 : ℚ) * p' + RS.2 * p) ^ 2 - (p : ℚ) ^ 2)) := by
  unfold lamF Hw
  push_cast
  rw [show (2 * (RS.1 : ℚ) * p' - p * (2 * RS.2 - 2)) * (2 * RS.1 * p' - p * (2 * RS.2)) *
      (2 * RS.1 * p' - p * (2 * RS.2 + 2)) = 8 * (((RS.1 : ℚ) * p' - RS.2 * p) *
        (((RS.1 : ℚ) * p' - RS.2 * p) ^ 2 - (p : ℚ) ^ 2)) by ring,
    show (2 * (RS.1 : ℚ) * p' - p * (2 - 2 * RS.2)) * (2 * RS.1 * p' - p * (-2 * RS.2)) *
      (2 * RS.1 * p' - p * (-2 * RS.2 - 2)) = 8 * (((RS.1 : ℚ) * p' + RS.2 * p) *
        (((RS.1 : ℚ) * p' + RS.2 * p) ^ 2 - (p : ℚ) ^ 2)) by ring,
    mul_div_mul_left _ _ (by norm_num : (8 : ℚ) ≠ 0)]

theorem facs_R {p p' r s : ℕ} (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p) (ε : Bool)
    {k : ℕ} (hk : 1 ≤ k) : ∀ RS ∈ facs p p' r s ε k, ¬ (p : ℤ) ∣ RS.1 := by
  have hr' : ¬ (p : ℤ) ∣ r := by
    intro h
    have := Int.le_of_dvd (by exact_mod_cast hr) h
    omega
  intro RS hRS
  unfold facs at hRS
  split_ifs at hRS with hodd hε hε
  · simp only [List.mem_singleton] at hRS
    subst hRS
    intro h
    apply hr'
    have : (p : ℤ) ∣ ((r + k / 2 * p : ℕ) : ℤ) - (k / 2 : ℕ) * p := dvd_sub h (dvd_mul_left _ _)
    push_cast at this
    simpa using this
  · simp only [List.mem_singleton] at hRS
    subst hRS
    intro h
    apply hr'
    have hle : r ≤ (k / 2 + 1) * p := le_trans hrp.le (Nat.le_mul_of_pos_left p (by omega))
    have : (p : ℤ) ∣ ((k / 2 + 1 : ℕ) : ℤ) * p - (((k / 2 + 1) * p - r : ℕ) : ℤ) :=
      dvd_sub (dvd_mul_left _ _) h
    push_cast [Nat.cast_sub hle] at this
    simpa using this
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hRS
    rcases hRS with rfl | rfl
    · intro h
      apply hr'
      have : (p : ℤ) ∣ ((r + (k / 2 - 1) * p : ℕ) : ℤ) - ((k / 2 - 1 : ℕ) : ℤ) * p :=
        dvd_sub h (dvd_mul_left _ _)
      push_cast at this
      simpa using this
    · intro h
      apply hr'
      have : (p : ℤ) ∣ (((k - 1) * p + r : ℕ) : ℤ) - ((k - 1 : ℕ) : ℤ) * p :=
        dvd_sub h (dvd_mul_left _ _)
      push_cast at this
      simpa using this
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hRS
    rcases hRS with rfl | rfl
    · intro h
      apply hr'
      have : (p : ℤ) ∣ ((r + (k / 2 - 1) * p : ℕ) : ℤ) - ((k / 2 - 1 : ℕ) : ℤ) * p :=
        dvd_sub h (dvd_mul_left _ _)
      push_cast at this
      simpa using this
    · intro h
      apply hr'
      have : (p : ℤ) ∣ (p : ℤ) - ((p - r : ℕ) : ℤ) := dvd_sub (dvd_refl _) h
      push_cast [Nat.cast_sub hrp.le] at this
      simpa using this

end Tk

section TkList

variable {p p' r s : ℕ}

/-- `Λ_den`, `Λ_num` of a factor. -/
def lamD (p p' : ℕ) (RS : ℕ × ℕ) : ℚ :=
  Hw p p' RS.1 (2 - 2 * RS.2) * Hw p p' RS.1 (-2 * RS.2) * Hw p p' RS.1 (-2 * RS.2 - 2)

def lamN (p p' : ℕ) (RS : ℕ × ℕ) : ℚ :=
  Hw p p' RS.1 (2 * RS.2 - 2) * Hw p p' RS.1 (2 * RS.2) * Hw p p' RS.1 (2 * RS.2 + 2)

theorem lamD_ne (hcop : Nat.Coprime p p') (hp : 0 < p) {RS : ℕ × ℕ} (hR : ¬ (p : ℤ) ∣ RS.1) :
    lamD p p' RS ≠ 0 := by
  unfold lamD
  refine mul_ne_zero (mul_ne_zero (Hw_ne hcop hp hR ⟨1 - RS.2, by ring⟩)
    (Hw_ne hcop hp hR ⟨-RS.2, by ring⟩)) (Hw_ne hcop hp hR ⟨-RS.2 - 1, by ring⟩)

theorem lamN_ne (hcop : Nat.Coprime p p') (hp : 0 < p) {RS : ℕ × ℕ} (hR : ¬ (p : ℤ) ∣ RS.1) :
    lamN p p' RS ≠ 0 := by
  unfold lamN
  refine mul_ne_zero (mul_ne_zero (Hw_ne hcop hp hR ⟨RS.2 - 1, by ring⟩)
    (Hw_ne hcop hp hR ⟨RS.2, by ring⟩)) (Hw_ne hcop hp hR ⟨RS.2 + 1, by ring⟩)

/-- The product over a list of factors (paper.tex l.1534–1538). -/
theorem list_ratio (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (L : List (ℕ × ℕ))
    (hL : ∀ RS ∈ L, ¬ (p : ℤ) ∣ RS.1) :
    (L.map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum =
        (L.map (cnt p p' (dQ p p' ((p' : ℤ) + 3 * p)))).sum ∧
      (L.map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod *
          ((-1) ^ (L.map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum *
            (2 * ((p' : ℚ) - 3 * p)) ^ (L.map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum) *
          (L.map (lamD p p')).prod =
        (L.map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod *
          (2 * ((p' : ℚ) + 3 * p)) ^ (L.map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum *
          (L.map (lamN p p')).prod := by
  induction L with
  | nil => simp
  | cons RS L ih =>
    obtain ⟨h1, h2⟩ := ih fun RS' h => hL RS' (List.mem_cons_of_mem _ h)
    obtain ⟨g1, g2⟩ := factor_ratio hp hp' hcop RS.1 RS.2 (hL RS (List.mem_cons_self))
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    refine ⟨by rw [← g1, h1], ?_⟩
    rw [pow_add, pow_add, pow_add]
    have g2' : cof p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS *
        ((-1) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS *
          (2 * ((p' : ℚ) - 3 * p)) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS) * lamD p p' RS =
        cof p p' (dQ p p' ((p' : ℤ) + 3 * p)) RS *
          (2 * ((p' : ℚ) + 3 * p)) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS * lamN p p' RS := by
      simpa [lamD, lamN] using g2
    linear_combination
      (((L.map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod *
          ((-1) ^ (L.map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum *
            (2 * ((p' : ℚ) - 3 * p)) ^ (L.map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum) *
          (L.map (lamD p p')).prod)) * g2' +
      (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)) RS *
          (2 * ((p' : ℚ) + 3 * p)) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS * lamN p p' RS) * h2

end TkList

end TT

end Virasoro
