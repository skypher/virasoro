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

section TkClosed

variable {p p' r s : ℕ}

theorem lamN_eq (p p' : ℕ) (RS : ℕ × ℕ) :
    lamN p p' RS = 8 * (((RS.1 : ℚ) * p' - RS.2 * p) *
      (((RS.1 : ℚ) * p' - RS.2 * p) ^ 2 - (p : ℚ) ^ 2)) := by
  unfold lamN Hw
  push_cast
  ring

theorem lamD_eq (p p' : ℕ) (RS : ℕ × ℕ) :
    lamD p p' RS = 8 * (((RS.1 : ℚ) * p' + RS.2 * p) *
      (((RS.1 : ℚ) * p' + RS.2 * p) ^ 2 - (p : ℚ) ^ 2)) := by
  unfold lamD Hw
  push_cast
  ring

/-- The factor of `τ^ε_k` other than the common one. -/
def oth (p p' r s : ℕ) (ε : Bool) (k : ℕ) : ℕ × ℕ :=
  if k % 2 = 1 then
    (if ε then (r + k / 2 * p, s + k / 2 * p') else ((k / 2 + 1) * p - r, (k / 2 + 1) * p' - s))
  else (if ε then ((k - 1) * p + r, p' - s) else (p - r, (k - 1) * p' + s))

theorem facs_oth (p p' r s : ℕ) (ε : Bool) (k : ℕ) :
    facs p p' r s ε k = (if k % 2 = 1 then [] else [(r + (k / 2 - 1) * p, s + (k / 2 - 1) * p')])
      ++ [oth p p' r s ε k] := by
  unfold facs oth
  split_ifs <;> rfl

theorem oth_m {hr : r < p} {hs : s < p'} (ε : Bool) {k : ℕ} (hk : 1 ≤ k) :
    ((oth p p' r s ε k).1 : ℚ) * p' + (oth p p' r s ε k).2 * p = (nOrb p p' r s ε k : ℚ) := by
  unfold oth nOrb
  by_cases hodd : k % 2 = 1
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [if_pos hodd]
    simp only [h2, show (2 * j + 1) % 2 ≠ 0 by omega, if_false]
    cases ε
    · simp only [Bool.false_eq_true, if_false]
      have h1 : r ≤ (j + 1) * p := le_trans hr.le (Nat.le_mul_of_pos_left p (by omega))
      have h1' : s ≤ (j + 1) * p' := le_trans hs.le (Nat.le_mul_of_pos_left p' (by omega))
      push_cast [Nat.cast_sub h1, Nat.cast_sub h1']
      ring
    · simp only [if_true]
      push_cast
      ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    rw [if_neg hodd]
    simp only [show 2 * j % 2 = 0 by omega, if_true]
    have hj : 1 ≤ j := by omega
    cases ε
    · simp only [Bool.false_eq_true, if_false]
      push_cast [Nat.cast_sub hr.le, Nat.cast_sub (show 1 ≤ 2 * j by omega)]
      ring
    · simp only [if_true]
      push_cast [Nat.cast_sub hs.le, Nat.cast_sub (show 1 ≤ 2 * j by omega)]
      ring

theorem oth_D {hr : r < p} {hs : s < p'} {k : ℕ} (hk : 1 ≤ k) :
    ((oth p p' r s false k).1 : ℚ) * p' - (oth p p' r s false k).2 * p =
      -(((oth p p' r s true k).1 : ℚ) * p' - (oth p p' r s true k).2 * p) := by
  unfold oth
  by_cases hodd : k % 2 = 1
  · rw [if_pos hodd, if_pos hodd]
    simp only [Bool.false_eq_true, if_false, if_true]
    have h1 : r ≤ (k / 2 + 1) * p := le_trans hr.le (Nat.le_mul_of_pos_left p (by omega))
    have h1' : s ≤ (k / 2 + 1) * p' := le_trans hs.le (Nat.le_mul_of_pos_left p' (by omega))
    push_cast [Nat.cast_sub h1, Nat.cast_sub h1']
    ring
  · rw [if_neg hodd, if_neg hodd]
    simp only [Bool.false_eq_true, if_false, if_true]
    push_cast [Nat.cast_sub hr.le, Nat.cast_sub hs.le, Nat.cast_sub (show 1 ≤ k by omega)]
    ring

/-- `T_k = −m⁻((m⁻)²−p²)/(m⁺((m⁺)²−p²))` (paper.tex l.1534–1546). -/
theorem T_closed (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (hr0 : 0 < r) (hr : r < p)
    (hs : s < p') {k : ℕ} (hk : 1 ≤ k)
    (hSig : ∀ ε : Bool, ((facs p p' r s ε k).map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum = k) :
    ((facs p p' r s true k).map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod *
        ((facs p p' r s false k).map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod /
      (((facs p p' r s true k).map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod *
        ((facs p p' r s false k).map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod) =
      -((nOrb p p' r s false k : ℚ) * ((nOrb p p' r s false k : ℚ) ^ 2 - (p : ℚ) ^ 2)) /
        ((nOrb p p' r s true k : ℚ) * ((nOrb p p' r s true k : ℚ) ^ 2 - (p : ℚ) ^ 2)) := by
  have h0p : 0 < p := by omega
  obtain ⟨-, hT⟩ := list_ratio hp hp' hcop (facs p p' r s true k) (facs_R hcop hr0 hr true hk)
  obtain ⟨-, hF⟩ := list_ratio hp hp' hcop (facs p p' r s false k) (facs_R hcop hr0 hr false hk)
  rw [hSig true] at hT
  rw [hSig false] at hF
  set x1 : ℚ := (p' : ℚ) - 3 * p
  set x2 : ℚ := (p' : ℚ) + 3 * p
  have hx1 : x1 ≠ 0 := by
    intro h0
    have h3p : (p' : ℤ) = 3 * p := by
      have : ((p' : ℤ) : ℚ) = ((3 * p : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have h3p' : p' = 3 * p := by exact_mod_cast h3p
    have := Nat.Coprime.coprime_dvd_right (show p ∣ p' by rw [h3p']; exact dvd_mul_left p 3) hcop
    rw [Nat.coprime_self] at this
    omega
  have hx2 : x2 ≠ 0 := by positivity
  have hcne : ∀ (ε : Bool) (z : ℚ), ((facs p p' r s ε k).map (cof p p' z)).prod ≠ 0 :=
    fun ε z => List.prod_ne_zero fun h => by
      obtain ⟨x, -, hx0⟩ := List.mem_map.1 h
      exact cof_ne_zero _ _ _ _ hx0
  have hDne : ∀ ε : Bool, ((facs p p' r s ε k).map (lamD p p')).prod ≠ 0 :=
    fun ε => List.prod_ne_zero fun h => by
      obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
      exact lamD_ne hcop h0p (facs_R hcop hr0 hr ε hk x hx) hx0
  have hNne : ∀ ε : Bool, ((facs p p' r s ε k).map (lamN p p')).prod ≠ 0 :=
    fun ε => List.prod_ne_zero fun h => by
      obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
      exact lamN_ne hcop h0p (facs_R hcop hr0 hr ε hk x hx) hx0
  -- the ratio of the cofactor products
  have hm1 : ((-1 : ℚ) ^ k) ≠ 0 := by simp
  have hstep : ((facs p p' r s true k).map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod *
        ((facs p p' r s false k).map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod /
      (((facs p p' r s true k).map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod *
        ((facs p p' r s false k).map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod) =
      ((facs p p' r s true k).map (lamN p p')).prod * ((facs p p' r s false k).map (lamD p p')).prod /
        (((facs p p' r s true k).map (lamD p p')).prod *
          ((facs p p' r s false k).map (lamN p p')).prod) := by
    rw [div_eq_div_iff (mul_ne_zero (hcne _ _) (hcne _ _)) (mul_ne_zero (hDne _) (hNne _))]
    have hA : ((-1) ^ k * (2 * x1) ^ k) ≠ 0 := mul_ne_zero hm1 (pow_ne_zero _ (mul_ne_zero
      two_ne_zero hx1))
    have hB : (2 * x2) ^ k ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hx2)
    apply mul_left_cancel₀ (mul_ne_zero hA hB)
    linear_combination
      ((2 * x2) ^ k * ((facs p p' r s false k).map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod *
        ((facs p p' r s false k).map (lamN p p')).prod) * hT -
      ((2 * x2) ^ k * ((facs p p' r s true k).map (lamN p p')).prod *
        ((facs p p' r s true k).map (cof p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod) * hF
  rw [hstep, facs_oth, facs_oth]
  -- the common factor cancels
  have hcom : ∀ (c : List (ℕ × ℕ)) (ht hf : ℕ × ℕ),
      (∀ RS ∈ c, lamD p p' RS ≠ 0 ∧ lamN p p' RS ≠ 0) →
      ((c ++ [ht]).map (lamN p p')).prod * ((c ++ [hf]).map (lamD p p')).prod /
        (((c ++ [ht]).map (lamD p p')).prod * ((c ++ [hf]).map (lamN p p')).prod) =
      lamN p p' ht * lamD p p' hf / (lamD p p' ht * lamN p p' hf) := by
    intro c ht hf hc
    have h1 : (c.map (lamN p p')).prod ≠ 0 := List.prod_ne_zero fun h => by
      obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
      exact (hc x hx).2 hx0
    have h2 : (c.map (lamD p p')).prod ≠ 0 := List.prod_ne_zero fun h => by
      obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
      exact (hc x hx).1 hx0
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rw [show (c.map (lamN p p')).prod * lamN p p' ht * ((c.map (lamD p p')).prod * lamD p p' hf) =
        ((c.map (lamN p p')).prod * (c.map (lamD p p')).prod) * (lamN p p' ht * lamD p p' hf) by
          ring,
      show (c.map (lamD p p')).prod * lamD p p' ht * ((c.map (lamN p p')).prod * lamN p p' hf) =
        ((c.map (lamN p p')).prod * (c.map (lamD p p')).prod) * (lamD p p' ht * lamN p p' hf) by
          ring,
      mul_div_mul_left _ _ (mul_ne_zero h1 h2)]
  rw [hcom]
  · have hRt := facs_R (s := s) hcop hr0 hr true hk (oth p p' r s true k)
      (by rw [facs_oth]; simp)
    have hRf := facs_R (s := s) hcop hr0 hr false hk (oth p p' r s false k)
      (by rw [facs_oth]; simp)
    rw [lamN_eq, lamN_eq, lamD_eq, lamD_eq, oth_D (hr := hr) (hs := hs) hk,
      oth_m (hr := hr) (hs := hs) true hk, oth_m (hr := hr) (hs := hs) false hk]
    have hN := lamN_ne hcop h0p hRt
    rw [lamN_eq] at hN
    have hDt := lamD_ne hcop h0p hRt
    rw [lamD_eq, oth_m (hr := hr) (hs := hs) true hk] at hDt
    have hDf := lamD_ne hcop h0p hRf
    rw [lamD_eq, oth_m (hr := hr) (hs := hs) false hk] at hDf
    have hN' : (((oth p p' r s true k).1 : ℚ) * p' - (oth p p' r s true k).2 * p) *
        ((((oth p p' r s true k).1 : ℚ) * p' - (oth p p' r s true k).2 * p) ^ 2 - (p : ℚ) ^ 2) ≠ 0 := by
      intro h0; apply hN; rw [h0, mul_zero]
    have hDt' : (nOrb p p' r s true k : ℚ) * ((nOrb p p' r s true k : ℚ) ^ 2 - (p : ℚ) ^ 2) ≠ 0 := by
      intro h0; apply hDt; rw [h0, mul_zero]
    have hDf' : (nOrb p p' r s false k : ℚ) * ((nOrb p p' r s false k : ℚ) ^ 2 - (p : ℚ) ^ 2) ≠ 0 := by
      intro h0; apply hDf; rw [h0, mul_zero]
    rw [show ∀ x : ℚ, (-x) * ((-x) ^ 2 - (p : ℚ) ^ 2) = -(x * (x ^ 2 - (p : ℚ) ^ 2)) from
      fun x => by ring]
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hDt')
      (mul_ne_zero (by norm_num) (neg_ne_zero.2 hN'))) hDt']
    ring
  · intro RS hRS
    have hR : ¬ (p : ℤ) ∣ RS.1 := by
      split_ifs at hRS
      · simp at hRS
      · simp only [List.mem_singleton] at hRS
        subst hRS
        exact facs_R (s := s) hcop hr0 hr true hk _ (by rw [facs_oth]; simp_all)
    exact ⟨lamD_ne hcop h0p hR, lamN_ne hcop h0p hR⟩

end TkClosed

end TT

end Virasoro
