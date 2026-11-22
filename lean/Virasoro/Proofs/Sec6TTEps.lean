import Virasoro.Proofs.Sec6TTCase2

/-!
# Proposition 6.9, Case 3: the ratio `𝒫_{R,S}(d_{x₁(ε)})/𝒫_{R,S}(d_{x₂(ε)})` (paper.tex l.1514–1534)

With `x₁(ε) = p'−3p+ε`, `x₂(ε) = p'+3p−ε`, the factors of `𝒫_{R,S}` at `d_{x₁(ε)}` and
`d_{x₂(ε)}` are `∏_A ∏_l (p'A − p(3±l) + ε)` and `∏_A ∏_l (p'A + p(3±l) − ε)`, `A ∈ {1−a', 1+a'}`
running once over `{0, ±2, …, ±2(R−1), 2R}`.  Sending `A ↦ −A` in the denominator cancels every
`A` but `2R` (an identity of polynomials in `ε`); at `ε = 0` the values `3 ± l` form
`{4−2S, …, 2S+2}` and cancelling `v ↦ −v` leaves `{2S−2, 2S, 2S+2}`.
Here: the two reindexings as identities in any commutative monoid.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

theorem oddsBelow_succ (R : ℕ) : oddsBelow (R + 1) = insert (2 * R + 1) (oddsBelow R) := by
  ext a
  simp only [oddsBelow, mem_filter, mem_range, mem_insert]
  omega

theorem not_mem_oddsBelow_self (R : ℕ) : 2 * R + 1 ∉ oddsBelow R := by
  simp only [oddsBelow, mem_filter, mem_range]
  omega

/-- `A ↦ −A`: `∏_{a'} G(1−a')G(1+a') · G(−2R) = ∏_{a'} G(a'−1)G(−1−a') · G(2R)`. -/
theorem A_reindex {M : Type*} [CommMonoid M] (G : ℤ → M) (R : ℕ) :
    (∏ a ∈ oddsBelow R, (G (1 - a) * G (1 + a))) * G (-2 * R) =
      (∏ a ∈ oddsBelow R, (G (a - 1) * G (-1 - a))) * G (2 * R) := by
  induction R with
  | zero => simp [oddsBelow]
  | succ R ih =>
    rw [oddsBelow_succ, prod_insert (not_mem_oddsBelow_self R),
      prod_insert (not_mem_oddsBelow_self R)]
    have e1 : (1 : ℤ) - ((2 * R + 1 : ℕ) : ℤ) = -2 * R := by push_cast; ring
    have e2 : (1 : ℤ) + ((2 * R + 1 : ℕ) : ℤ) = 2 * ((R + 1 : ℕ) : ℤ) := by push_cast; ring
    have e3 : (((2 * R + 1 : ℕ) : ℤ)) - 1 = 2 * R := by push_cast; ring
    have e4 : (-1 : ℤ) - ((2 * R + 1 : ℕ) : ℤ) = -2 * ((R + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, e3, e4]
    calc G (-2 * R) * G (2 * ((R + 1 : ℕ) : ℤ)) * (∏ a ∈ oddsBelow R, (G (1 - a) * G (1 + a))) *
          G (-2 * ((R + 1 : ℕ) : ℤ))
        = ((∏ a ∈ oddsBelow R, (G (1 - a) * G (1 + a))) * G (-2 * R)) *
            (G (2 * ((R + 1 : ℕ) : ℤ)) * G (-2 * ((R + 1 : ℕ) : ℤ))) := by ac_rfl
      _ = ((∏ a ∈ oddsBelow R, (G (a - 1) * G (-1 - a))) * G (2 * R)) *
            (G (2 * ((R + 1 : ℕ) : ℤ)) * G (-2 * ((R + 1 : ℕ) : ℤ))) := by rw [ih]
      _ = G (2 * R) * G (-2 * ((R + 1 : ℕ) : ℤ)) * (∏ a ∈ oddsBelow R, (G (a - 1) * G (-1 - a))) *
            G (2 * ((R + 1 : ℕ) : ℤ)) := by ac_rfl

/-- `v ↦ −v`: `∏_l H(3+l)H(3−l) · H(2−2S)H(−2S)H(−2S−2) =
∏_l H(−3−l)H(l−3) · H(2S−2)H(2S)H(2S+2)`. -/
theorem v_reindex {M : Type*} [CommMonoid M] (H : ℤ → M) (S : ℕ) :
    (∏ l ∈ oddsBelow S, (H (3 + l) * H (3 - l))) * (H (2 - 2 * S) * H (-2 * S) * H (-2 * S - 2)) =
      (∏ l ∈ oddsBelow S, (H (-3 - l) * H (l - 3))) * (H (2 * S - 2) * H (2 * S) * H (2 * S + 2)) := by
  induction S with
  | zero =>
    simp only [oddsBelow, Nat.cast_zero, mul_zero, zero_sub, sub_zero, neg_zero, zero_add]
    simp only [range_zero, filter_empty, prod_empty, one_mul]
    norm_num
    ac_rfl
  | succ S ih =>
    rw [oddsBelow_succ, prod_insert (not_mem_oddsBelow_self S),
      prod_insert (not_mem_oddsBelow_self S)]
    have c : (((2 * S + 1 : ℕ) : ℤ)) = 2 * S + 1 := by push_cast; ring
    have cS : (((S + 1 : ℕ) : ℤ)) = S + 1 := by push_cast; ring
    rw [c, cS]
    have f1 : (3 : ℤ) + (2 * S + 1) = 2 * S + 4 := by ring
    have f2 : (3 : ℤ) - (2 * S + 1) = 2 - 2 * S := by ring
    have f3 : (-3 : ℤ) - (2 * S + 1) = -2 * S - 4 := by ring
    have f4 : (2 * (S : ℤ) + 1) - 3 = 2 * S - 2 := by ring
    have g1 : (2 : ℤ) - 2 * (S + 1) = -2 * S := by ring
    have g2 : (-2 : ℤ) * (S + 1) = -2 * S - 2 := by ring
    have g3 : (-2 : ℤ) * (S + 1) - 2 = -2 * S - 4 := by ring
    have g4 : (2 : ℤ) * (S + 1) - 2 = 2 * S := by ring
    have g5 : (2 : ℤ) * (S + 1) = 2 * S + 2 := by ring
    have g6 : (2 : ℤ) * (S + 1) + 2 = 2 * S + 4 := by ring
    rw [f1, f2, f3, f4, g1, g3, g4, g6, g2, g5]
    calc H (2 * S + 4) * H (2 - 2 * S) * (∏ l ∈ oddsBelow S, (H (3 + l) * H (3 - l))) *
          (H (-2 * S) * H (-2 * S - 2) * H (-2 * S - 4))
        = ((∏ l ∈ oddsBelow S, (H (3 + l) * H (3 - l))) *
            (H (2 - 2 * S) * H (-2 * S) * H (-2 * S - 2))) * (H (2 * S + 4) * H (-2 * S - 4)) := by
          ac_rfl
      _ = ((∏ l ∈ oddsBelow S, (H (-3 - l) * H (l - 3))) *
            (H (2 * S - 2) * H (2 * S) * H (2 * S + 2))) * (H (2 * S + 4) * H (-2 * S - 4)) := by
          rw [ih]
      _ = H (-2 * S - 4) * H (2 * S - 2) * (∏ l ∈ oddsBelow S, (H (-3 - l) * H (l - 3))) *
            (H (2 * S) * H (2 * S + 2) * H (2 * S + 4)) := by ac_rfl

/-! ### The `ε`-identity for one factor `𝒫_{R,S}` (paper.tex l.1514–1534) -/

section Eps

variable (p p' : ℕ)

/-- `x² − x₁(ε)²`, `x₁(ε) = p'−3p+ε`. -/
noncomputable def f1e (i : (ℕ × ℕ) × Bool) : ℚ[X] :=
  C ((xv p p' i : ℚ) ^ 2) - (C ((p' : ℚ) - 3 * p) + X) ^ 2

/-- `x² − x₂(ε)²`, `x₂(ε) = p'+3p−ε`. -/
noncomputable def f2e (i : (ℕ × ℕ) × Bool) : ℚ[X] :=
  C ((xv p p' i : ℚ) ^ 2) - (C ((p' : ℚ) + 3 * p) - X) ^ 2

/-- `(p'A − p(3+l) + ε)(p'A − p(3−l) + ε)`. -/
noncomputable def numL (A : ℤ) (l : ℕ) : ℚ[X] :=
  (C ((p' : ℚ) * A - p * (3 + l)) + X) * (C ((p' : ℚ) * A - p * (3 - l)) + X)

/-- `∏_l (p'A − p(3+l) + ε)(p'A − p(3−l) + ε)`. -/
noncomputable def GA (S : ℕ) (A : ℤ) : ℚ[X] := ∏ l ∈ oddsBelow S, numL p p' A l

theorem pair1 (a l : ℕ) :
    f1e p p' ((a, l), true) * f1e p p' ((a, l), false) =
      numL p p' (1 - a) l * numL p p' (1 + a) l := by
  simp only [f1e, numL, xv, if_true, Bool.false_eq_true, if_false]
  push_cast
  simp only [map_sub, map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one]
  ring

theorem pair2 (a l : ℕ) :
    f2e p p' ((a, l), true) * f2e p p' ((a, l), false) =
      numL p p' (a - 1) l * numL p p' (-1 - a) l := by
  simp only [f2e, numL, xv, if_true, Bool.false_eq_true, if_false]
  push_cast
  simp only [map_sub, map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one, map_neg]
  ring

theorem F1_eq (R S : ℕ) :
    ∏ i ∈ idx R S, f1e p p' i = ∏ a ∈ oddsBelow R, (GA p p' S (1 - a) * GA p p' S (1 + a)) := by
  rw [idx, prod_product, prod_product]
  refine prod_congr rfl fun a _ => ?_
  rw [GA, GA, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  rw [Fintype.prod_bool, pair1]

theorem F2_eq (R S : ℕ) :
    ∏ i ∈ idx R S, f2e p p' i = ∏ a ∈ oddsBelow R, (GA p p' S (a - 1) * GA p p' S (-1 - a)) := by
  rw [idx, prod_product, prod_product]
  refine prod_congr rfl fun a _ => ?_
  rw [GA, GA, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  rw [Fintype.prod_bool, pair2]

/-- The `A ↦ −A` cancellation: `F₁(ε) G(−2R) = F₂(ε) G(2R)` (paper.tex l.1521–1523). -/
theorem F_identity (R S : ℕ) :
    (∏ i ∈ idx R S, f1e p p' i) * GA p p' S (-2 * R) =
      (∏ i ∈ idx R S, f2e p p' i) * GA p p' S (2 * R) := by
  rw [F1_eq, F2_eq]
  exact A_reindex (GA p p' S) R

end Eps

/-! ### Consequences at `ε = 0` (paper.tex l.1523–1534) -/

section Ratio

variable {p p' : ℕ}

/-- `2Rp' − pv`. -/
def Hw (p p' R : ℕ) (v : ℤ) : ℚ := 2 * R * p' - p * v

theorem Hw_ne (hcop : Nat.Coprime p p') (hp : 0 < p) {R : ℕ} (hR : ¬ (p : ℤ) ∣ R) {v : ℤ}
    (hv : Even v) : Hw p p' R v ≠ 0 := by
  obtain ⟨w, rfl⟩ := hv
  intro h0
  apply hR
  have h1 : (R : ℤ) * p' = p * w := by
    have : (2 * R * p' : ℚ) = p * (w + w) := by unfold Hw at h0; push_cast at h0; linarith
    have h2 : ((R * p' : ℤ) : ℚ) = ((p * w : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  exact hc.dvd_of_dvd_mul_right ⟨w, h1⟩

theorem GA_eval (S : ℕ) (A : ℤ) :
    (GA p p' S A).eval 0 =
      ∏ l ∈ oddsBelow S, (((p' : ℚ) * A - p * (3 + l)) * ((p' : ℚ) * A - p * (3 - l))) := by
  rw [GA, eval_prod]
  refine prod_congr rfl fun l _ => ?_
  simp [numL]

theorem GA_pos (S R : ℕ) : (GA p p' S (2 * R)).eval 0 =
    ∏ l ∈ oddsBelow S, (Hw p p' R (3 + l) * Hw p p' R (3 - l)) := by
  rw [GA_eval]
  refine prod_congr rfl fun l _ => ?_
  simp only [Hw]
  push_cast
  ring

theorem GA_neg (S R : ℕ) : (GA p p' S (-2 * R)).eval 0 =
    ∏ l ∈ oddsBelow S, (Hw p p' R (-3 - l) * Hw p p' R (l - 3)) := by
  rw [GA_eval]
  refine prod_congr rfl fun l _ => ?_
  simp only [Hw]
  push_cast
  ring

theorem odd_l {l : ℕ} (hl : l ∈ oddsBelow S) (c : ℤ) (hc : Odd c) : Even (c + l) ∧ Even (c - l) := by
  have h := (mem_oddsBelow.1 hl).2
  have hl' : Odd (l : ℤ) := by
    rw [Int.odd_iff]
    exact_mod_cast (show (l : ℤ) % 2 = 1 by omega)
  exact ⟨hc.add_odd hl', hc.sub_odd hl'⟩

/-- For one factor `𝒫_{R,S}` with `p ∤ R`: the orders at `d₁` and `d₂` agree, and
`cof(d₁)·(−2x₁)^e·∏(2Rp'+pw) = cof(d₂)·(2x₂)^e·∏(2Rp'−pw)`, `w ∈ {2S−2, 2S, 2S+2}`
(paper.tex l.1523–1534). -/
theorem factor_ratio (hp : 2 ≤ p) (hp' : 3 ≤ p') (hcop : Nat.Coprime p p') (R S : ℕ)
    (hR : ¬ (p : ℤ) ∣ R) :
    cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) (R, S) = cnt p p' (dQ p p' ((p' : ℤ) + 3 * p)) (R, S) ∧
    cof p p' (dQ p p' ((p' : ℤ) - 3 * p)) (R, S) *
        ((-1) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) (R, S) *
          (2 * ((p' : ℚ) - 3 * p)) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) (R, S)) *
        (Hw p p' R (2 - 2 * S) * Hw p p' R (-2 * S) * Hw p p' R (-2 * S - 2)) =
      cof p p' (dQ p p' ((p' : ℤ) + 3 * p)) (R, S) *
        (2 * ((p' : ℚ) + 3 * p)) ^ cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) (R, S) *
        (Hw p p' R (2 * S - 2) * Hw p p' R (2 * S) * Hw p p' R (2 * S + 2)) := by
  have h0p : 0 < p := by omega
  have h0p' : 0 < p' := by omega
  set z1 := dQ p p' ((p' : ℤ) - 3 * p) with hz1
  set z2 := dQ p p' ((p' : ℤ) + 3 * p) with hz2
  set x1 : ℚ := (p' : ℚ) - 3 * p with hx1
  set x2 : ℚ := (p' : ℚ) + 3 * p with hx2
  have hx1ne : x1 ≠ 0 := by
    intro h0
    have h3p : (p' : ℤ) = 3 * p := by
      have : ((p' : ℤ) : ℚ) = ((3 * p : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have h3p' : p' = 3 * p := by exact_mod_cast h3p
    have := Nat.Coprime.coprime_dvd_right (show p ∣ p' by rw [h3p']; exact dvd_mul_left p 3) hcop
    rw [Nat.coprime_self] at this
    omega
  have hx2ne : x2 ≠ 0 := by
    have : (0 : ℚ) < x2 := by rw [hx2]; positivity
    exact this.ne'
  set I := idx R S
  set e1 := cnt p p' z1 (R, S) with he1
  set e2 := cnt p p' z2 (R, S) with he2
  -- the roots split off
  have hf1 : ∀ i ∈ I.filter (fun i => dQ p p' (xv p p' i) = z1),
      f1e p p' i = -X * (C (2 * x1) + X) := by
    intro i hi
    have h := (dQ_eq_iff h0p h0p' _ _).1 (mem_filter.1 hi).2
    have h' : ((xv p p' i : ℚ)) ^ 2 = x1 ^ 2 := by
      rw [hx1]
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h
    rw [f1e, h', ← hx1]
    simp only [map_mul, map_ofNat, map_pow]
    ring
  have hf2 : ∀ i ∈ I.filter (fun i => dQ p p' (xv p p' i) = z2),
      f2e p p' i = X * (C (2 * x2) - X) := by
    intro i hi
    have h := (dQ_eq_iff h0p h0p' _ _).1 (mem_filter.1 hi).2
    have h' : ((xv p p' i : ℚ)) ^ 2 = x2 ^ 2 := by
      rw [hx2]
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h
    rw [f2e, h', ← hx2]
    simp only [map_mul, map_ofNat, map_pow]
    ring
  have hF1 : ∏ i ∈ I, f1e p p' i = X ^ e1 * ((-1) ^ e1 * (C (2 * x1) + X) ^ e1 *
      ∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1), f1e p p' i) := by
    rw [← prod_filter_mul_prod_filter_not I (fun i => dQ p p' (xv p p' i) = z1),
      prod_congr rfl hf1, prod_const]
    rw [show (-X * (C (2 * x1) + X)) ^ (I.filter fun i => dQ p p' (xv p p' i) = z1).card =
      X ^ e1 * ((-1) ^ e1 * (C (2 * x1) + X) ^ e1) by
        rw [he1, cnt, neg_mul, neg_eq_neg_one_mul, mul_pow, mul_pow]; ring]
    ring
  have hF2 : ∏ i ∈ I, f2e p p' i = X ^ e2 * ((C (2 * x2) - X) ^ e2 *
      ∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2), f2e p p' i) := by
    rw [← prod_filter_mul_prod_filter_not I (fun i => dQ p p' (xv p p' i) = z2),
      prod_congr rfl hf2, prod_const, mul_pow]
    rw [show (I.filter fun i => dQ p p' (xv p p' i) = z2).card = e2 by rw [he2, cnt]]
    ring
  have hid := F_identity p p' R S
  rw [hF1, hF2] at hid
  -- values at `0`
  have hP1 : (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1), f1e p p' i).eval 0 =
      ∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1), (((xv p p' i : ℚ)) ^ 2 - x1 ^ 2) := by
    rw [eval_prod]
    refine prod_congr rfl fun i _ => ?_
    simp [f1e, hx1]
  have hP2 : (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2), f2e p p' i).eval 0 =
      ∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2), (((xv p p' i : ℚ)) ^ 2 - x2 ^ 2) := by
    rw [eval_prod]
    refine prod_congr rfl fun i _ => ?_
    simp [f2e, hx2]
  have hPi1 : ∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1),
      (((xv p p' i : ℚ)) ^ 2 - x1 ^ 2) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 fun h => (mem_filter.1 hi).2 ?_
    apply (dQ_eq_iff h0p h0p' _ _).2
    have : ((xv p p' i ^ 2 : ℤ) : ℚ) = (((p' : ℤ) - 3 * p) ^ 2 : ℤ) := by
      push_cast; rw [h, hx1]
    exact_mod_cast this
  have hPi2 : ∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2),
      (((xv p p' i : ℚ)) ^ 2 - x2 ^ 2) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 fun h => (mem_filter.1 hi).2 ?_
    apply (dQ_eq_iff h0p h0p' _ _).2
    have : ((xv p p' i ^ 2 : ℤ) : ℚ) = (((p' : ℤ) + 3 * p) ^ 2 : ℤ) := by
      push_cast; rw [h, hx2]
    exact_mod_cast this
  have hGn : (GA p p' S (-2 * R)).eval 0 ≠ 0 := by
    rw [GA_neg]
    refine prod_ne_zero_iff.2 fun l hl => mul_ne_zero (Hw_ne hcop h0p hR ?_) (Hw_ne hcop h0p hR ?_)
    · have := (odd_l hl (-3) (by decide)).2
      convert this using 1
    · have := (odd_l hl (-3) (by decide)).1
      convert this using 1
      ring
  have hGp : (GA p p' S (2 * R)).eval 0 ≠ 0 := by
    rw [GA_pos]
    exact prod_ne_zero_iff.2 fun l hl => mul_ne_zero (Hw_ne hcop h0p hR
      (odd_l hl 3 (by decide)).1) (Hw_ne hcop h0p hR (odd_l hl 3 (by decide)).2)
  -- the orders agree
  set U1 := (-1) ^ e1 * (C (2 * x1) + X) ^ e1 *
    (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1), f1e p p' i) * GA p p' S (-2 * R)
    with hU1
  set U2 := (C (2 * x2) - X) ^ e2 *
    (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2), f2e p p' i) * GA p p' S (2 * R)
    with hU2
  have hU1v : U1.eval 0 = (-1) ^ e1 * (2 * x1) ^ e1 *
      (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1), (((xv p p' i : ℚ)) ^ 2 - x1 ^ 2)) *
        (GA p p' S (-2 * R)).eval 0 := by
    rw [hU1, eval_mul, eval_mul, eval_mul, hP1]
    simp
  have hU2v : U2.eval 0 = (2 * x2) ^ e2 *
      (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2), (((xv p p' i : ℚ)) ^ 2 - x2 ^ 2)) *
        (GA p p' S (2 * R)).eval 0 := by
    rw [hU2, eval_mul, eval_mul, hP2]
    simp
  have hs1 : SplitAt 0 (X ^ e1 * U1) e1 U1 := ⟨by rw [map_zero, sub_zero], by
    rw [hU1v]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (mul_ne_zero two_ne_zero hx1ne))) hPi1) hGn⟩
  have hs2 : SplitAt 0 (X ^ e2 * U2) e2 U2 := ⟨by rw [map_zero, sub_zero], by
    rw [hU2v]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hx2ne)) hPi2) hGp⟩
  have hid' : X ^ e1 * U1 = X ^ e2 * U2 := by
    rw [hU1, hU2]
    linear_combination hid
  rw [hid'] at hs1
  have he : e1 = e2 := split_unique hs1 hs2
  refine ⟨he, ?_⟩
  rw [← he] at hid' hU2v
  have hU : U1 = U2 := mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) hid'
  have hv := congrArg (eval 0) hU
  rw [hU1v, hU2v] at hv
  -- the `v ↦ −v` cancellation
  have hvr := v_reindex (Hw p p' R) S
  rw [← GA_pos, ← GA_neg] at hvr
  -- the cofactors
  have hcof : ∀ y : ℤ, cof p p' (dQ p p' y) (R, S) =
      (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = dQ p p' y),
        (((xv p p' i : ℚ)) ^ 2 - (y : ℚ) ^ 2)) /
        (4 * (p : ℚ) * p') ^ (I.filter (fun i => ¬ dQ p p' (xv p p' i) = dQ p p' y)).card := by
    intro y
    rw [cof, ← prod_const, ← prod_div_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [dQ_sub h0p h0p']
    push_cast
    rfl
  have hcard : (I.filter (fun i => ¬ dQ p p' (xv p p' i) = z1)).card =
      (I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2)).card := by
    have a1 := card_filter_add_card_filter_not (s := I) (fun i => dQ p p' (xv p p' i) = z1)
    have a2 := card_filter_add_card_filter_not (s := I) (fun i => dQ p p' (xv p p' i) = z2)
    have b1 : (I.filter fun i => dQ p p' (xv p p' i) = z1).card = e1 := by rw [he1, cnt]
    have b2 : (I.filter fun i => dQ p p' (xv p p' i) = z2).card = e2 := by rw [he2, cnt]
    omega
  have h4 : (4 * (p : ℚ) * p') ≠ 0 := by positivity
  rw [hcof ((p' : ℤ) - 3 * p), hcof ((p' : ℤ) + 3 * p), ← hz1, ← hz2, hcard]
  have ex1 : (((p' : ℤ) - 3 * p : ℤ) : ℚ) = x1 := by rw [hx1]; push_cast; ring
  have ex2 : (((p' : ℤ) + 3 * p : ℤ) : ℚ) = x2 := by rw [hx2]; push_cast; ring
  rw [ex1, ex2]
  field_simp
  have key := congrArg (fun t => t * (Hw p p' R (2 - 2 * S) * Hw p p' R (-2 * S) *
    Hw p p' R (-2 * S - 2))) hv
  beta_reduce at key
  have hGn' := hGn
  apply mul_right_cancel₀ hGn'
  linear_combination key + (2 * x2) ^ e1 *
    (∏ i ∈ I.filter (fun i => ¬ dQ p p' (xv p p' i) = z2), (((xv p p' i : ℚ)) ^ 2 - x2 ^ 2)) * hvr

end Ratio

end TT

end Virasoro
