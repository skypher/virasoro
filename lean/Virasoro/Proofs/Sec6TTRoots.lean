import Virasoro.Proofs.Sec6TTFrame

/-!
# Proposition 6.9: the roots of `𝒫_{R,S}(b⋆, d)` (paper.tex l.1441–1452)

`𝒫_{R,S}(b⋆, d) = ∏ (d_x − d)` over `x = p'a' ∓ pl`, odd `1 ≤ a' < 2R`, odd `1 ≤ l < 2S`.  A root
`z` of multiplicity `e` splits off as `(d − z)^e`, the cofactor taking the value
`∏_{d_x ≠ z} (d_x − z)` at `z`.  `d_x = d_y` iff `x² = y²`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

/-- `P = (X − z)^e Q` with `Q(z) ≠ 0`. -/
def SplitAt (z : ℚ) (P : ℚ[X]) (e : ℕ) (Q : ℚ[X]) : Prop := P = (X - C z) ^ e * Q ∧ Q.eval z ≠ 0

theorem SplitAt.mul {z : ℚ} {P₁ P₂ Q₁ Q₂ : ℚ[X]} {e₁ e₂ : ℕ} (h₁ : SplitAt z P₁ e₁ Q₁)
    (h₂ : SplitAt z P₂ e₂ Q₂) : SplitAt z (P₁ * P₂) (e₁ + e₂) (Q₁ * Q₂) := by
  refine ⟨?_, ?_⟩
  · rw [h₁.1, h₂.1, pow_add]
    ring
  · rw [eval_mul]
    exact mul_ne_zero h₁.2 h₂.2

/-- A product of linear factors `∏ (f i − X)` splits at `z` with multiplicity the number of
`i` with `f i = z`. -/
theorem splitAt_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (z : ℚ) [DecidablePred (f · = z)] :
    SplitAt z (∏ i ∈ s, (C (f i) - X)) (s.filter (f · = z)).card
      (C ((-1) ^ (s.filter (f · = z)).card) * ∏ i ∈ s.filter (¬ f · = z), (C (f i) - X)) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [← prod_filter_mul_prod_filter_not s (f · = z)]
    have h1 : ∏ i ∈ s.filter (f · = z), (C (f i) - X) =
        C ((-1) ^ (s.filter (f · = z)).card) * (X - C z) ^ (s.filter (f · = z)).card := by
      rw [prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]]
      rw [prod_const, show (C z - X) = C (-1) * (X - C z) by rw [map_neg, map_one]; ring,
        mul_pow, ← map_pow]
    rw [h1]
    ring
  · rw [eval_mul, eval_C, eval_prod]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_ne_zero_iff.2 fun i hi => ?_)
    rw [eval_sub, eval_C, eval_X]
    exact sub_ne_zero.2 (mem_filter.1 hi).2

theorem eval_cofactor {ι : Type*} (s : Finset ι) (f : ι → ℚ) (z : ℚ) (e : ℕ) :
    (C ((-1) ^ e) * ∏ i ∈ s, (C (f i) - X)).eval z = (-1) ^ e * ∏ i ∈ s, (f i - z) := by
  rw [eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_C, eval_X]

/-! ### `𝒫_{R,S}` as a product over `(a', l, σ)` -/

/-- `x = p'a' − pl` (`σ = true`) or `p'a' + pl` (`σ = false`). -/
def xv (p p' : ℕ) (i : (ℕ × ℕ) × Bool) : ℤ :=
  if i.2 then (i.1.1 : ℤ) * p' - (i.1.2 : ℤ) * p else (i.1.1 : ℤ) * p' + (i.1.2 : ℤ) * p

/-- The index set of `𝒫_{R,S}`. -/
def idx (R S : ℕ) : Finset ((ℕ × ℕ) × Bool) := (oddsBelow R ×ˢ oddsBelow S) ×ˢ univ

theorem PQ_eq (p p' R S : ℕ) :
    PQ p p' R S = ∏ i ∈ idx R S, (C (dQ p p' (xv p p' i)) - X) := by
  rw [PQ, idx, prod_product, prod_product]
  refine prod_congr rfl fun a _ => prod_congr rfl fun l _ => ?_
  rw [Fintype.prod_bool]
  simp [xv]

theorem dQ_eq_iff {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') (x y : ℤ) :
    dQ p p' x = dQ p p' y ↔ x ^ 2 = y ^ 2 := by
  have h4 : (4 * (p : ℚ) * p') ≠ 0 := by positivity
  rw [dQ, dQ, div_left_inj' h4, sub_left_inj]
  exact_mod_cast Iff.rfl

theorem dQ_sub {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') (x y : ℤ) :
    dQ p p' x - dQ p p' y = ((x ^ 2 - y ^ 2 : ℤ) : ℚ) / (4 * p * p') := by
  rw [dQ, dQ]
  push_cast
  ring

theorem mem_oddsBelow {n a : ℕ} : a ∈ oddsBelow n ↔ a < 2 * n ∧ a % 2 = 1 := by
  rw [oddsBelow, mem_filter, mem_range]

/-! ### Coprimality: the solutions of `p'X = pY` -/

theorem coprime_lin {p p' : ℕ} (hcop : Nat.Coprime p p') (hp : 0 < p) {X Y : ℤ}
    (h : (p' : ℤ) * X = p * Y) : ∃ t : ℤ, X = p * t ∧ Y = p' * t := by
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (p : ℤ) ∣ p' * X := ⟨Y, h⟩
  obtain ⟨t, ht⟩ := hc.dvd_of_dvd_mul_left h1
  refine ⟨t, ht, ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  apply mul_left_cancel₀ hp0
  rw [← h, ht]
  ring

theorem even_of_coprime {p p' : ℕ} (hcop : Nat.Coprime p p') {t : ℤ} (h1 : Even ((p : ℤ) * t))
    (h2 : Even ((p' : ℤ) * t)) : Even t := by
  rcases Int.even_mul.1 h1 with h | h
  · rcases Int.even_mul.1 h2 with h' | h'
    · exfalso
      have e1 : 2 ∣ p := by exact_mod_cast (even_iff_two_dvd.1 h)
      have e2 : 2 ∣ p' := by exact_mod_cast (even_iff_two_dvd.1 h')
      have := Nat.dvd_gcd e1 e2
      rw [hcop] at this
      omega
    · exact h'
  · exact h

/-! ### The multiplicity of `d₁ = d_{p'−3p}` in `𝒫_{R,S}` (paper.tex l.1448–1456) -/

theorem not_dvd_two_of {p p' : ℕ} (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') {a : ℤ}
    (h : (p' : ℤ) * a = 2 * p) : False := by
  have hc : IsCoprime (p' : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have h1 : (p' : ℤ) ∣ 2 * p := ⟨a, h.symm⟩
  have h2 : (p' : ℤ) ∣ 2 := hc.dvd_of_dvd_mul_right h1
  have h3 := Int.le_of_dvd (by norm_num) h2
  omega

/-- The plus sign: `|p'a' + pl| = |p'−3p|` has no solution (paper.tex l.1449–1451). -/
theorem sol1_plus {p p' : ℕ} (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') {a l : ℕ}
    (ha : 1 ≤ a) (hl : 1 ≤ l) (hl2 : l % 2 = 1)
    (hx : ((a : ℤ) * p' + (l : ℤ) * p) ^ 2 = ((p' : ℤ) - 3 * p) ^ 2) : False := by
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hl' : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hp0 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hp0' : (0 : ℤ) ≤ p' := by positivity
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hx with hx | hx
  · have h1 : (p' : ℤ) ≤ a * p' := by nlinarith
    have h2 : (p : ℤ) ≤ l * p := by nlinarith
    linarith
  · rcases Nat.lt_or_ge l 3 with hl3 | hl3
    · have hl1 : l = 1 := by omega
      subst hl1
      exact not_dvd_two_of hp' hcop (a := (a : ℤ) + 1) (by push_cast at hx; linarith)
    · have : (3 : ℤ) ≤ l := by exact_mod_cast hl3
      nlinarith

/-- `p'a' − pl = p' − 3p` with odd `a', l ≥ 1`: `a' = 1 + 2mp`, `l = 3 + 2mp'` (paper.tex l.1452). -/
theorem sol1_minus_a {p p' : ℕ} (hp : 2 ≤ p) (hcop : Nat.Coprime p p') {a l : ℕ} (ha : 1 ≤ a)
    (ha2 : a % 2 = 1) (hl2 : l % 2 = 1) (hx : (a : ℤ) * p' - (l : ℤ) * p = p' - 3 * p) :
    ∃ m : ℕ, a = 1 + 2 * (m * p) ∧ l = 3 + 2 * (m * p') := by
  obtain ⟨t, ht1, ht2⟩ := coprime_lin hcop (by omega) (X := (a : ℤ) - 1) (Y := (l : ℤ) - 3)
    (by linarith)
  have hev : Even t := even_of_coprime hcop
    (by rw [← ht1]; exact ⟨((a : ℤ) - 1) / 2, by omega⟩)
    (by rw [← ht2]; exact ⟨((l : ℤ) - 3) / 2, by omega⟩)
  obtain ⟨u, hu⟩ := hev
  have hpz : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
  have hu0 : 0 ≤ u := by
    have h1 : (0 : ℤ) ≤ (p : ℤ) * t := by rw [← ht1]; omega
    by_contra hc
    nlinarith
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hu0
  refine ⟨m, ?_, ?_⟩
  · zify
    linear_combination ht1 + (p : ℤ) * hu
  · zify
    linear_combination ht2 + (p' : ℤ) * hu

/-- `p'a' − pl = 3p − p'` with odd `a', l ≥ 1`: `a' = 2mp − 1`, `l = 2mp' − 3`, `m ≥ 1`
(paper.tex l.1452–1453). -/
theorem sol1_minus_b {p p' : ℕ} (hp : 2 ≤ p) (hcop : Nat.Coprime p p') {a l : ℕ}
    (ha2 : a % 2 = 1) (hl2 : l % 2 = 1) (hx : (a : ℤ) * p' - (l : ℤ) * p = 3 * p - p') :
    ∃ m : ℕ, 1 ≤ m ∧ a + 1 = 2 * (m * p) ∧ l + 3 = 2 * (m * p') := by
  obtain ⟨t, ht1, ht2⟩ := coprime_lin hcop (by omega) (X := (a : ℤ) + 1) (Y := (l : ℤ) + 3)
    (by linarith)
  have hev : Even t := even_of_coprime hcop
    (by rw [← ht1]; exact ⟨((a : ℤ) + 1) / 2, by omega⟩)
    (by rw [← ht2]; exact ⟨((l : ℤ) + 3) / 2, by omega⟩)
  obtain ⟨u, hu⟩ := hev
  have hpz : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
  have hu0 : 1 ≤ u := by
    have h1 : (1 : ℤ) ≤ (p : ℤ) * t := by rw [← ht1]; omega
    by_contra hc
    nlinarith
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ u)
  refine ⟨m, by exact_mod_cast hu0, ?_, ?_⟩
  · zify
    linear_combination ht1 + (p : ℤ) * hu
  · zify
    linear_combination ht2 + (p' : ℤ) * hu

/-- The factors of `𝒫_{R,S}` with `x² = (p'−3p)²` are `(1+2mp, 3+2mp', −)`, `m ≥ 0`, and
`(2mp−1, 2mp'−3, −)`, `m ≥ 1` (paper.tex l.1449–1455). -/
theorem mult1_eq {p p' : ℕ} (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (R S : ℕ) :
    ((idx R S).filter (fun i => xv p p' i ^ 2 = ((p' : ℤ) - 3 * p) ^ 2)).card =
      ((range (R + 1)).filter (fun m => m * p + 1 ≤ R ∧ m * p' + 2 ≤ S)).card +
      ((range (R + 1)).filter (fun m => 1 ≤ m ∧ m * p ≤ R ∧ m * p' ≤ S + 1)).card := by
  classical
  set S1 := (range (R + 1)).filter (fun m => m * p + 1 ≤ R ∧ m * p' + 2 ≤ S) with hS1
  set S2 := (range (R + 1)).filter (fun m => 1 ≤ m ∧ m * p ≤ R ∧ m * p' ≤ S + 1) with hS2
  let f1 : ℕ → (ℕ × ℕ) × Bool := fun m => ((1 + 2 * (m * p), 3 + 2 * (m * p')), true)
  let f2 : ℕ → (ℕ × ℕ) × Bool := fun m => ((2 * (m * p) - 1, 2 * (m * p') - 3), true)
  have hle : ∀ m, m ≤ m * p := fun m => Nat.le_mul_of_pos_right m (by omega)
  have hle' : ∀ m, m ≤ m * p' := fun m => Nat.le_mul_of_pos_right m (by omega)
  have hx1 : ∀ m, xv p p' (f1 m) = (p' : ℤ) - 3 * p := by
    intro m
    simp only [f1, xv, if_true]
    push_cast
    ring
  have hx2 : ∀ m, 1 ≤ m → xv p p' (f2 m) = 3 * (p : ℤ) - p' := by
    intro m hm
    have h1 : 1 ≤ 2 * (m * p) := by have := hle m; omega
    have h2 : 3 ≤ 2 * (m * p') := by
      have : 2 ≤ m * p' := le_trans (by omega) (Nat.mul_le_mul_left m (show 2 ≤ p' by omega))
      omega
    simp only [f2, xv, if_true]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  have hF : (idx R S).filter (fun i => xv p p' i ^ 2 = ((p' : ℤ) - 3 * p) ^ 2) =
      S1.image f1 ∪ S2.image f2 := by
    ext ⟨⟨a, l⟩, σ⟩
    simp only [mem_filter, mem_union, mem_image, idx, mem_product, mem_univ, and_true,
      mem_oddsBelow]
    constructor
    · rintro ⟨⟨⟨ha, ha2⟩, ⟨hl, hl2⟩⟩, hx⟩
      cases σ
      · exfalso
        simp only [xv, Bool.false_eq_true, if_false] at hx
        exact sol1_plus hp hp' hcop (by omega) (by omega) hl2 hx
      · simp only [xv, if_true] at hx
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hx with hx | hx
        · obtain ⟨m, rfl, rfl⟩ := sol1_minus_a hp hcop (by omega) ha2 hl2 hx
          have := hle m
          exact Or.inl ⟨m, mem_filter.2 ⟨mem_range.2 (by omega), by omega, by omega⟩, rfl⟩
        · obtain ⟨m, hm1, e1, e2⟩ := sol1_minus_b hp hcop ha2 hl2 (by linarith)
          have := hle m
          refine Or.inr ⟨m, mem_filter.2 ⟨mem_range.2 (by omega), hm1, by omega, by omega⟩, ?_⟩
          simp only [f2, Prod.mk.injEq, and_true]
          omega
    · rintro (⟨m, hm, he⟩ | ⟨m, hm, he⟩)
      · obtain ⟨-, hm1, hm2⟩ := mem_filter.1 hm
        simp only [f1, Prod.mk.injEq] at he
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
        refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
        rw [show xv p p' ((1 + 2 * (m * p), 3 + 2 * (m * p')), true) = (p' : ℤ) - 3 * p
          from hx1 m]
      · obtain ⟨-, hm0, hm1, hm2⟩ := mem_filter.1 hm
        have h1 : 1 ≤ m * p := le_trans hm0 (hle m)
        have h2 : 2 ≤ m * p' :=
          le_trans (by omega) (Nat.mul_le_mul_left m (show 2 ≤ p' by omega))
        simp only [f2, Prod.mk.injEq] at he
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
        refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
        rw [show xv p p' ((2 * (m * p) - 1, 2 * (m * p') - 3), true) = 3 * (p : ℤ) - p'
          from hx2 m hm0]
        ring
  have hne : (p' : ℤ) - 3 * p ≠ 3 * p - p' := by
    intro h0
    have h3 : p' = 3 * p := by omega
    have := Nat.Coprime.coprime_dvd_right (show p ∣ p' by rw [h3]; exact dvd_mul_left p 3) hcop
    rw [Nat.coprime_self] at this
    omega
  rw [hF, card_union_of_disjoint, card_image_of_injective, card_image_of_injOn]
  · intro m hm m' hm' he
    simp only [f2, Prod.mk.injEq] at he
    have h1 : 1 ≤ m * p := le_trans (mem_filter.1 hm).2.1 (hle m)
    have h1' : 1 ≤ m' * p := le_trans (mem_filter.1 hm').2.1 (hle m')
    exact Nat.eq_of_mul_eq_mul_right (show 0 < p by omega) (by omega)
  · intro m m' he
    simp only [f1, Prod.mk.injEq] at he
    exact Nat.eq_of_mul_eq_mul_right (show 0 < p by omega) (by omega)
  · rw [disjoint_left]
    rintro x hx hx'
    obtain ⟨m, _, rfl⟩ := mem_image.1 hx
    obtain ⟨m', hm', he⟩ := mem_image.1 hx'
    have := hx2 m' (mem_filter.1 hm').2.1
    rw [he, hx1] at this
    exact hne this

/-! ### Evaluating the count on the factors of `τ^±_k` (paper.tex l.1456–1460) -/

theorem le_iff_A {m j p c d : ℕ} (hp : 0 < p) (h1 : c ≤ d) (h2 : d < c + p) :
    m * p + c ≤ j * p + d ↔ m ≤ j := by
  constructor
  · intro h
    by_contra hc
    have h3 : (j + 1) * p ≤ m * p := Nat.mul_le_mul_right p (by omega)
    rw [Nat.succ_mul] at h3
    omega
  · intro h
    have := Nat.mul_le_mul_right p h
    omega

theorem le_iff_B {m j p c d : ℕ} (h1 : d < c) (h2 : c ≤ d + p) :
    m * p + c ≤ j * p + d ↔ m + 1 ≤ j := by
  constructor
  · intro h
    by_contra hc
    have := Nat.mul_le_mul_right p (show j ≤ m by omega)
    omega
  · intro h
    have h3 := Nat.mul_le_mul_right p h
    rw [Nat.succ_mul] at h3
    omega

theorem card_filter_lt {B n : ℕ} {P : ℕ → Prop} [DecidablePred P] (hn : n ≤ B + 1)
    (h : ∀ m, m ≤ B → (P m ↔ m < n)) : ((range (B + 1)).filter P).card = n := by
  have : (range (B + 1)).filter P = range n := by
    ext m
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact (h m (by omega)).1 h2
    · intro h2
      exact ⟨by omega, (h m (by omega)).2 h2⟩
  rw [this, card_range]

theorem card_filter_Icc {B n : ℕ} {P : ℕ → Prop} [DecidablePred P] (hn : n ≤ B)
    (h : ∀ m, m ≤ B → (P m ↔ 1 ≤ m ∧ m ≤ n)) : ((range (B + 1)).filter P).card = n := by
  have : (range (B + 1)).filter P = Icc 1 n := by
    ext m
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact (h m (by omega)).1 h2
    · intro h2
      exact ⟨by omega, (h m (by omega)).2 h2⟩
  rw [this, Nat.card_Icc]
  omega

section Counts

variable {p p' r s : ℕ}

/-- `m₁(R,S)`: the multiplicity of `d₁` in `𝒫_{R,S}`. -/
def m1 (p p' R S : ℕ) : ℕ :=
  ((idx R S).filter (fun i => xv p p' i ^ 2 = ((p' : ℤ) - 3 * p) ^ 2)).card

theorem le_mul_self' {m p : ℕ} (hp : 0 < p) : m ≤ m * p := Nat.le_mul_of_pos_right m hp

/-- `(R,S) = (r+jp, s+jp')`: `m₁ = 2j + [s ≥ 2]`. -/
theorem m1_a (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p)
    (hs : 0 < s) (hsp : s < p') (j : ℕ) :
    m1 p p' (r + j * p) (s + j * p') = 2 * j + (if 2 ≤ s then 1 else 0) := by
  rw [m1, mult1_eq hp hp' hcop]
  have hjp := le_mul_self' (m := j) (show 0 < p by omega)
  rw [card_filter_lt (n := j + (if 2 ≤ s then 1 else 0)) (by split_ifs <;> omega),
    card_filter_Icc (n := j) (by omega)]
  · split_ifs <;> ring
  · intro m _
    constructor
    · rintro ⟨h0, h1, -⟩
      exact ⟨h0, (le_iff_A (c := 0) (show 0 < p by omega) (Nat.zero_le r) (by omega)).1
        (by rw [add_zero, add_comm]; exact h1)⟩
    · rintro ⟨h0, h1⟩
      have := Nat.mul_le_mul_right p h1
      have := Nat.mul_le_mul_right p' h1
      exact ⟨h0, by omega, by omega⟩
  · intro m _
    have e1 : m * p + 1 ≤ r + j * p ↔ m ≤ j := by
      rw [add_comm r]
      exact le_iff_A (show 0 < p by omega) (by omega) (by omega)
    rw [e1]
    split_ifs with hs2
    · have e2 : m * p' + 2 ≤ s + j * p' ↔ m ≤ j := by
        rw [add_comm s]
        exact le_iff_A (show 0 < p' by omega) hs2 (by omega)
      rw [e2]
      omega
    · have e2 : m * p' + 2 ≤ s + j * p' ↔ m + 1 ≤ j := by
        rw [add_comm s]
        exact le_iff_B (by omega) (by omega)
      rw [e2]
      omega

/-- `(R,S) = ((j+1)p−r, (j+1)p'−s)`: `m₁ = 2j + [s ≤ p'−2]`. -/
theorem m1_b (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p)
    (hs : 0 < s) (hsp : s < p') (j : ℕ) :
    m1 p p' ((j + 1) * p - r) ((j + 1) * p' - s) = 2 * j + (if s + 2 ≤ p' then 1 else 0) := by
  have eR : (j + 1) * p - r = j * p + (p - r) := by rw [Nat.succ_mul]; omega
  have eS : (j + 1) * p' - s = j * p' + (p' - s) := by rw [Nat.succ_mul]; omega
  rw [m1, mult1_eq hp hp' hcop, eR, eS]
  have hjp := le_mul_self' (m := j) (show 0 < p by omega)
  rw [card_filter_lt (n := j + (if s + 2 ≤ p' then 1 else 0)) (by split_ifs <;> omega),
    card_filter_Icc (n := j) (by omega)]
  · split_ifs <;> ring
  · intro m _
    constructor
    · rintro ⟨h0, h1, -⟩
      exact ⟨h0, (le_iff_A (m := m) (j := j) (c := 0) (d := p - r) (show 0 < p by omega)
        (Nat.zero_le _) (by omega)).1 (by rw [add_zero]; exact h1)⟩
    · rintro ⟨h0, h1⟩
      have := Nat.mul_le_mul_right p h1
      have := Nat.mul_le_mul_right p' h1
      exact ⟨h0, by omega, by omega⟩
  · intro m _
    have e1 : m * p + 1 ≤ j * p + (p - r) ↔ m ≤ j :=
      le_iff_A (show 0 < p by omega) (by omega) (by omega)
    rw [e1]
    split_ifs with hs2
    · have e2 : m * p' + 2 ≤ j * p' + (p' - s) ↔ m ≤ j :=
        le_iff_A (show 0 < p' by omega) (by omega) (by omega)
      rw [e2]
      omega
    · have e2 : m * p' + 2 ≤ j * p' + (p' - s) ↔ m + 1 ≤ j := le_iff_B (by omega) (by omega)
      rw [e2]
      omega

/-- `(R,S) = ((2j−1)p+r, p'−s)`, `j ≥ 1`: `m₁ = [s ≤ p'−2] + [s = 1]`. -/
theorem m1_c (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p)
    (hs : 0 < s) (hsp : s < p') {j : ℕ} (hj : 1 ≤ j) :
    m1 p p' ((2 * j - 1) * p + r) (p' - s) =
      (if s + 2 ≤ p' then 1 else 0) + (if s = 1 then 1 else 0) := by
  rw [m1, mult1_eq hp hp' hcop]
  have hjp := le_mul_self' (m := 2 * j - 1) (show 0 < p by omega)
  rw [card_filter_lt (n := if s + 2 ≤ p' then 1 else 0) (by split_ifs <;> omega),
    card_filter_Icc (n := if s = 1 then 1 else 0) (by split_ifs <;> omega)]
  · intro m _
    have e1 : m * p ≤ (2 * j - 1) * p + r ↔ m ≤ 2 * j - 1 := by
      have := le_iff_A (m := m) (j := 2 * j - 1) (c := 0) (d := r) (show 0 < p by omega)
        (Nat.zero_le r) (by omega)
      rwa [add_zero] at this
    rw [e1]
    split_ifs with hs1
    · subst hs1
      have e2 : m * p' ≤ p' - 1 + 1 ↔ m ≤ 1 := by
        have := le_iff_A (m := m) (j := 1) (c := 0) (d := 0) (show 0 < p' by omega) le_rfl
          (by omega)
        rw [add_zero, add_zero, one_mul] at this
        rw [show p' - 1 + 1 = p' by omega]
        exact this
      rw [e2]
      omega
    · have e2 : m * p' ≤ p' - s + 1 ↔ m ≤ 0 := by
        have := le_iff_A (m := m) (j := 0) (c := 0) (d := p' - s + 1) (show 0 < p' by omega)
          (Nat.zero_le _) (by omega)
        rwa [add_zero, zero_mul, zero_add] at this
      rw [e2]
      omega
  · intro m _
    have e1 : m * p + 1 ≤ (2 * j - 1) * p + r ↔ m ≤ 2 * j - 1 :=
      le_iff_A (show 0 < p by omega) (by omega) (by omega)
    rw [e1]
    split_ifs with hs2
    · have e2 : m * p' + 2 ≤ p' - s ↔ m ≤ 0 := by
        have := le_iff_A (m := m) (j := 0) (c := 2) (d := p' - s) (show 0 < p' by omega)
          (by omega) (by omega)
        rwa [zero_mul, zero_add] at this
      rw [e2]
      omega
    · have : ¬ m * p' + 2 ≤ p' - s := by omega
      simp only [this, and_false, false_iff, not_lt, Nat.le_zero]
      omega

/-- `(R,S) = (p−r, (2j−1)p'+s)`, `j ≥ 1`: `m₁ = 1`. -/
theorem m1_d (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p)
    (hs : 0 < s) (hsp : s < p') {j : ℕ} (hj : 1 ≤ j) :
    m1 p p' (p - r) ((2 * j - 1) * p' + s) = 1 := by
  rw [m1, mult1_eq hp hp' hcop]
  have hjp' := le_mul_self' (m := 2 * j - 1) (show 0 < p' by omega)
  rw [card_filter_lt (n := 1) (by omega), card_filter_Icc (n := 0) (by omega)]
  · intro m _
    have e1 : m * p ≤ p - r ↔ m ≤ 0 := by
      have := le_iff_A (m := m) (j := 0) (c := 0) (d := p - r) (show 0 < p by omega)
        (Nat.zero_le _) (by omega)
      rwa [add_zero, zero_mul, zero_add] at this
    rw [e1]
    omega
  · intro m _
    have e1 : m * p + 1 ≤ p - r ↔ m ≤ 0 := by
      have := le_iff_A (m := m) (j := 0) (c := 1) (d := p - r) (show 0 < p by omega)
        (by omega) (by omega)
      rwa [zero_mul, zero_add] at this
    rw [e1]
    constructor
    · rintro ⟨h1, -⟩
      omega
    · intro h1
      have hm : m = 0 := by omega
      subst hm
      exact ⟨le_rfl, by rw [zero_mul]; omega⟩

end Counts

/-! ### The split of `τ^±_k` at `d₁` (paper.tex l.1456–1460) -/

theorem splitAt_PQ (p p' : ℕ) (z : ℚ) (R S : ℕ) :
    SplitAt z (PQ p p' R S) ((idx R S).filter (fun i => dQ p p' (xv p p' i) = z)).card
      (C ((-1) ^ ((idx R S).filter (fun i => dQ p p' (xv p p' i) = z)).card) *
        ∏ i ∈ (idx R S).filter (fun i => ¬ dQ p p' (xv p p' i) = z), (C (dQ p p' (xv p p' i)) - X)) := by
  rw [PQ_eq]
  exact splitAt_prod (idx R S) (fun i => dQ p p' (xv p p' i)) z

theorem card_d1 {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') (R S : ℕ) :
    ((idx R S).filter (fun i => dQ p p' (xv p p' i) = dQ p p' ((p' : ℤ) - 3 * p))).card =
      m1 p p' R S := by
  rw [m1]
  congr 1
  exact filter_congr fun i _ => dQ_eq_iff hp hp' _ _

theorem splitAt_PQ_d1 {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') (R S : ℕ) :
    ∃ Q, SplitAt (dQ p p' ((p' : ℤ) - 3 * p)) (PQ p p' R S) (m1 p p' R S) Q :=
  ⟨_, card_d1 hp hp' R S ▸ splitAt_PQ p p' _ R S⟩

/-- `ord_{d₁} τ^±_k`: `e₊ = k−1+[s≥2]`, `e₋ = k−1+[s≤p'−2]` (`k` odd) and the two exchanged
(`k` even) (paper.tex l.1456–1460). -/
def e1 (p' s : ℕ) (ε : Bool) (k : ℕ) : ℕ :=
  k - 1 + (if (k % 2 = 1 ∧ ε = true) ∨ (k % 2 = 0 ∧ ε = false) then (if 2 ≤ s then 1 else 0)
    else (if s + 2 ≤ p' then 1 else 0))

theorem tau_split_d1 {p p' r s : ℕ} (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p')
    (hr : 0 < r) (hrp : r < p) (hs : 0 < s) (hsp : s < p') (ε : Bool) {k : ℕ} (hk : 1 ≤ k) :
    ∃ Q, SplitAt (dQ p p' ((p' : ℤ) - 3 * p)) (tauQ p p' r s ε k) (e1 p' s ε k) Q := by
  have h0p : 0 < p := by omega
  have h0p' : 0 < p' := by omega
  unfold tauQ
  by_cases hodd : k % 2 = 1
  · obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    have hk2 : k / 2 = j := by omega
    rw [if_pos hodd, hk2]
    cases ε
    · have he : e1 p' s false k = 2 * j + (if s + 2 ≤ p' then 1 else 0) := by
        rw [e1, if_neg (by simp [hodd])]
        omega
      rw [he, if_neg Bool.false_ne_true]
      obtain ⟨Q, hQ⟩ := splitAt_PQ_d1 h0p h0p' ((j + 1) * p - r) ((j + 1) * p' - s)
      rw [m1_b hp hp' hcop hr hrp hs hsp j] at hQ
      exact ⟨Q, hQ⟩
    · have he : e1 p' s true k = 2 * j + (if 2 ≤ s then 1 else 0) := by
        rw [e1, if_pos (Or.inl ⟨hodd, rfl⟩)]
        omega
      rw [he, if_pos rfl]
      obtain ⟨Q, hQ⟩ := splitAt_PQ_d1 h0p h0p' (r + j * p) (s + j * p')
      rw [m1_a hp hp' hcop hr hrp hs hsp j] at hQ
      exact ⟨Q, hQ⟩
  · obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hk2 : k / 2 = j := by omega
    rw [if_neg hodd, hk2]
    obtain ⟨Q0, hQ0⟩ := splitAt_PQ_d1 h0p h0p' (r + (j - 1) * p) (s + (j - 1) * p')
    rw [m1_a hp hp' hcop hr hrp hs hsp (j - 1)] at hQ0
    have hk1 : k - 1 = 2 * j - 1 := by omega
    cases ε
    · have he : e1 p' s false k =
          2 * (j - 1) + (if 2 ≤ s then 1 else 0) + 1 := by
        rw [e1, if_pos (Or.inr ⟨by omega, rfl⟩)]
        omega
      rw [he, if_neg Bool.false_ne_true, hk1]
      obtain ⟨Q, hQ⟩ := splitAt_PQ_d1 h0p h0p' (p - r) ((2 * j - 1) * p' + s)
      rw [m1_d hp hp' hcop hr hrp hs hsp hj1] at hQ
      exact ⟨_, hQ0.mul hQ⟩
    · have he : e1 p' s true k = 2 * (j - 1) + (if 2 ≤ s then 1 else 0) +
          ((if s + 2 ≤ p' then 1 else 0) + (if s = 1 then 1 else 0)) := by
        rw [e1, if_neg (by simp [hodd])]
        split_ifs <;> omega
      rw [he, if_pos rfl, hk1]
      obtain ⟨Q, hQ⟩ := splitAt_PQ_d1 h0p h0p' ((2 * j - 1) * p + r) (p' - s)
      rw [m1_c hp hp' hcop hr hrp hs hsp hj1] at hQ
      exact ⟨_, hQ0.mul hQ⟩

end TT

end Virasoro
