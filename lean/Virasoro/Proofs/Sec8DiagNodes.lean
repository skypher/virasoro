import Virasoro.Statements.Sec8Diagonal
import Virasoro.Proofs.P2Sec10OrbitArith

/-!
# Section 8.1: arithmetic of the nodes

Signed momenta: `S ≡ n₀` (even layers) or `S ≡ n₁` (odd layers) modulo `N₀ = 2pp'`;
`|S(ε,k)| = k p p' + c` with `|c| < p p'` (for `k ≥ 1`, and `|S_λ| = |n₀|`); `d_x = d_y` iff
`x² = y²`; `h_g(b⋆) = d_{x_g}` and `h_g(b⋆) + ℓ_g = d_{y_g}`.
-/

namespace Virasoro

variable {p p' r s : ℕ}

section Arith

/-- The class of a signed momentum modulo `2pp'`. -/
theorem nodeS_mod (a : Node) :
    ∃ m : ℤ, nodeS p p' r s a =
      (if a.2 % 2 = 0 then (p' : ℤ) * r - p * s else (p' : ℤ) * r + p * s) + m * (2 * p * p') := by
  obtain ⟨ε, k⟩ := a
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k <;> cases ε
  · refine ⟨-(j : ℤ), ?_⟩
    simp only [nodeS, Bool.false_eq_true, ↓reduceIte, nOrb_even_false]
    simp
    ring
  · refine ⟨(j : ℤ), ?_⟩
    simp only [nodeS, ↓reduceIte, nOrb_even_true]
    simp
    ring
  · refine ⟨-((j : ℤ) + 1), ?_⟩
    have h : (2 * j + 1) % 2 = 1 := by omega
    simp only [nodeS, Bool.false_eq_true, ↓reduceIte, nOrb_odd_false, h]
    simp
    ring
  · refine ⟨(j : ℤ), ?_⟩
    have h : (2 * j + 1) % 2 = 1 := by omega
    simp only [nodeS, ↓reduceIte, nOrb_odd_true, h]
    simp
    ring

/-- `|S(ε,k)| = k p p' + c` with `|c| < p p'`; for `k = 0`, `c = |n₀|`. -/
theorem nodeS_abs (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s) (hs : s < p')
    (hint : p' * r + p * s < p * p') (a : Node) :
    ∃ c : ℤ, |c| < p * p' ∧ |nodeS p p' r s a| = (a.2 : ℤ) * p * p' + c ∧
      (a.2 % 2 = 0 → c = (p' : ℤ) * r - p * s ∨ c = -((p' : ℤ) * r - p * s)) ∧
      (a.2 % 2 = 1 → c = (p' : ℤ) * r + p * s - p * p' ∨ c = p * p' - ((p' : ℤ) * r + p * s)) := by
  have hp0 : 0 < p := by omega
  have hp0' : 0 < p' := by omega
  have a1 : (0 : ℤ) < (p' : ℤ) * r := by exact_mod_cast Nat.mul_pos hp0' hr0
  have a2 : (0 : ℤ) < (p : ℤ) * s := by exact_mod_cast Nat.mul_pos hp0 hs0
  have hpp : (0 : ℤ) < p * p' := by exact_mod_cast Nat.mul_pos hp0 hp0'
  have a3 : (p' : ℤ) * r + p * s < p * p' := by exact_mod_cast hint
  obtain ⟨ε, k⟩ := a
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h0 : (2 * j) % 2 = 0 := by omega
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · refine ⟨|(p' : ℤ) * r - p * s|, ?_, ?_, ?_, ?_⟩
      · rw [abs_abs]; exact abs_lt.2 ⟨by linarith, by linarith⟩
      · cases ε <;> simp [nodeS, nOrb]
      · intro _; rcases abs_choice ((p' : ℤ) * r - p * s) with h | h <;> simp [h]
      · intro h; simp at h
    · have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
      cases ε
      · refine ⟨-((p' : ℤ) * r - p * s), ?_, ?_, ?_, ?_⟩
        · rw [abs_neg]; exact abs_lt.2 ⟨by linarith, by linarith⟩
        · have hpos : 0 < 2 * (j : ℤ) * p * p' - ((p' : ℤ) * r - p * s) := by nlinarith
          simp only [nodeS, Bool.false_eq_true, ↓reduceIte, nOrb_even_false, abs_neg,
            abs_of_pos hpos]
          push_cast; ring
        · intro _; right; rfl
        · intro h; omega
      · refine ⟨(p' : ℤ) * r - p * s, ?_, ?_, ?_, ?_⟩
        · exact abs_lt.2 ⟨by linarith, by linarith⟩
        · have hpos : 0 < 2 * (j : ℤ) * p * p' + ((p' : ℤ) * r - p * s) := by nlinarith
          simp only [nodeS, ↓reduceIte, nOrb_even_true, abs_of_pos hpos]
          push_cast; ring
        · intro _; left; rfl
        · intro h; omega
  · have h1 : (2 * j + 1) % 2 = 1 := by omega
    have hj0 : (0 : ℤ) ≤ j := by positivity
    cases ε
    · refine ⟨p * p' - ((p' : ℤ) * r + p * s), ?_, ?_, ?_, ?_⟩
      · exact abs_lt.2 ⟨by linarith, by linarith⟩
      · have hpos : 0 < (2 * (j : ℤ) + 2) * p * p' - ((p' : ℤ) * r + p * s) := by nlinarith
        simp only [nodeS, Bool.false_eq_true, ↓reduceIte, nOrb_odd_false, abs_neg,
          abs_of_pos hpos]
        push_cast; ring
      · intro h; omega
      · intro _; right; rfl
    · refine ⟨(p' : ℤ) * r + p * s - p * p', ?_, ?_, ?_, ?_⟩
      · exact abs_lt.2 ⟨by linarith, by linarith⟩
      · have hpos : 0 < 2 * (j : ℤ) * p * p' + ((p' : ℤ) * r + p * s) := by nlinarith
        simp only [nodeS, ↓reduceIte, nOrb_odd_true, abs_of_pos hpos]
        push_cast; ring
      · intro h; omega
      · intro _; left; rfl

/-- `|S_{ν'}| - |S_ν| = Δ p p' + e` with `|e| < p p'` when `Δ = L_{ν'} - L_ν` is odd. -/
theorem nodeS_gap (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s) (hs : s < p')
    (hint : p' * r + p * s < p * p') (ν ν' : Node) (hlt : ν.2 < ν'.2)
    (hodd : (ν'.2 - ν.2) % 2 = 1) :
    ∃ e : ℤ, |e| < p * p' ∧
      |nodeS p p' r s ν'| - |nodeS p p' r s ν| = ((ν'.2 : ℤ) - ν.2) * p * p' + e := by
  obtain ⟨c, hc, hS, hce, hco⟩ := nodeS_abs hr0 hr hs0 hs hint ν
  obtain ⟨c', hc', hS', hce', hco'⟩ := nodeS_abs hr0 hr hs0 hs hint ν'
  refine ⟨c' - c, ?_, by rw [hS, hS']; ring⟩
  have hp0 : 0 < p := by omega
  have hp0' : 0 < p' := by omega
  have a1 : (0 : ℤ) < (p' : ℤ) * r := by exact_mod_cast Nat.mul_pos hp0' hr0
  have a2 : (0 : ℤ) < (p : ℤ) * s := by exact_mod_cast Nat.mul_pos hp0 hs0
  have hpp : (0 : ℤ) < p * p' := by exact_mod_cast Nat.mul_pos hp0 hp0'
  have a3 : (p' : ℤ) * r + p * s < p * p' := by exact_mod_cast hint
  have hr' : (p' : ℤ) * r < p * p' := by
    have : (r : ℤ) < p := by exact_mod_cast hr
    nlinarith
  have hs' : (p : ℤ) * s < p * p' := by
    have : (s : ℤ) < p' := by exact_mod_cast hs
    nlinarith
  rcases Nat.mod_two_eq_zero_or_one ν.2 with h | h
  · have h' : ν'.2 % 2 = 1 := by omega
    rcases hce h with e1 | e1 <;> rcases hco' h' with e2 | e2 <;> rw [e1, e2] <;>
      exact abs_lt.2 ⟨by linarith, by linarith⟩
  · have h' : ν'.2 % 2 = 0 := by omega
    rcases hco h with e1 | e1 <;> rcases hce' h' with e2 | e2 <;> rw [e1, e2] <;>
      exact abs_lt.2 ⟨by linarith, by linarith⟩

end Arith

section Weights

/-- `d_x = d_y` iff `x² = y²`. -/
theorem momWt_eq_iff (hp : 0 < p) (hp' : 0 < p') (x y : ℤ) :
    momWt p p' x = momWt p p' y ↔ x ^ 2 = y ^ 2 := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  unfold momWt
  constructor
  · intro h
    have h4 : (4 : ℂ) * p * p' ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpc) hpc'
    have := (div_left_inj' h4).1 h
    have h2 : ((x : ℂ)) ^ 2 = ((y : ℂ)) ^ 2 := by linear_combination this
    exact_mod_cast h2
  · intro h
    have h2 : ((x : ℂ)) ^ 2 = ((y : ℂ)) ^ 2 := by exact_mod_cast h
    rw [h2]

/-- `z_g(b⋆) = h_g(b⋆) + ℓ_g = d_{p'u + pv}`. -/
theorem kacH_add_lvl {b : ℂ} (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p)
    (g : Label) :
    kacHL g b + (g.lvl : ℂ) = momWt p p' ((p' : ℤ) * g.1 + p * g.2) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  unfold kacHL
  rw [kacH_momWt hp hp' hb]
  unfold momWt Label.lvl
  push_cast
  field_simp
  ring

end Weights

end Virasoro
