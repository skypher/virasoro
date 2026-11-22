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

end TT

end Virasoro
