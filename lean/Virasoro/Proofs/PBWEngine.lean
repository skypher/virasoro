import Virasoro.Proofs.VermaSpan

/-!
# A verified normal-ordering engine

`negIns f m w` writes `L_{-m} L_{-w}|h⟩` as a rational combination of words, moving `L_{-m}` to
the right past larger modes with `[L_{-m}, L_{-y}] = (y - m) L_{-m-y}`, so that the output words
are weakly decreasing (Poincaré–Birkhoff–Witt order) once the fuel `f` suffices.
`posActAff f k w` writes `L_k L_{-w}|h⟩` with coefficients affine in `(h, c)`: a triple
`(a, b, e)` stands for `a + b h + e c`.  Both are correct for every fuel (with too little fuel a
word may stay unordered); explicit computations check their output by evaluation.
-/

namespace Virasoro

open Verma

/-- Affine coefficients: `(a, b, e)` stands for `a + b h + e c`. -/
abbrev Aff := ℚ × ℚ × ℚ

/-- `q (a, b, e) = (q a, q b, q e)`. -/
def affScale (q : ℚ) (x : Aff) : Aff := (q * x.1, q * x.2.1, q * x.2.2)

/-- `L_{-m} L_{-w}|h⟩` as a rational combination of words. -/
def negIns : ℕ → ℕ → List ℕ → List (List ℕ × ℚ)
  | 0, m, w => [(m :: w, 1)]
  | _ + 1, m, [] => [([m], 1)]
  | f + 1, m, y :: w =>
      if y ≤ m then [(m :: y :: w, 1)]
      else ((negIns f m w).flatMap fun t => (negIns f y t.1).map fun u => (u.1, t.2 * u.2)) ++
        ((negIns f (m + y) w).map fun u => (u.1, ((y - m : ℕ) : ℚ) * u.2))

/-- `L_k L_{-w}|h⟩` with affine coefficients in `(h, c)`. -/
def posActAff (f : ℕ) : ℤ → List ℕ → List (List ℕ × Aff)
  | k, [] => if k < 0 then [([k.natAbs], (1, 0, 0))] else if k = 0 then [([], (0, 1, 0))] else []
  | k, y :: w =>
      if k < 0 then (negIns f k.natAbs (y :: w)).map fun u => (u.1, (u.2, 0, 0))
      else if k = 0 then [(y :: w, (((y + w.sum : ℕ) : ℚ), 1, 0))]
      else
        ((posActAff f k w).flatMap fun t =>
            (negIns f y t.1).map fun u => (u.1, affScale u.2 t.2)) ++
          ((posActAff f (k - y) w).map fun t => (t.1, affScale ((k + y : ℤ) : ℚ) t.2)) ++
          (if k = y then [(w, (0, 0, ((k ^ 3 - k : ℤ) : ℚ) / 12))] else [])

section Semantics

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The value `a + b h + e c` of an affine coefficient. -/
def evalAff (c h : R) (x : Aff) : R :=
  algebraMap ℚ R x.1 + algebraMap ℚ R x.2.1 * h + algebraMap ℚ R x.2.2 * c

/-- A rational combination of words, read in `R`. -/
def ofQ (s : List (List ℕ × ℚ)) : St R := s.map fun t => (t.1, algebraMap ℚ R t.2)

/-- An affine combination of words, read in `R` at `(c, h)`. -/
def ofAff (c h : R) (s : List (List ℕ × Aff)) : St R := s.map fun t => (t.1, evalAff c h t.2)

theorem evalAff_scale (c h : R) (q : ℚ) (x : Aff) :
    evalAff c h (affScale q x) = algebraMap ℚ R q * evalAff c h x := by
  simp only [evalAff, affScale, map_mul]
  ring

variable {c h : R}

theorem toVerma_flatMap {α : Type*} (s : List (List ℕ × α)) (val : α → R)
    (g : List ℕ → List (List ℕ × ℚ)) (y : ℕ)
    (hg : ∀ w, St.toVerma (c := c) (h := h) (ofQ (g w)) = L (-(y : ℤ)) (neg w)) :
    St.toVerma (c := c) (h := h)
        ((s.flatMap fun t => (g t.1).map fun u => (u.1, algebraMap ℚ R u.2 * val t.2)))
      = L (-(y : ℤ)) (St.toVerma (s.map fun t => (t.1, val t.2))) := by
  induction s with
  | nil => simp [St.toVerma_nil]
  | cons t s ih =>
    rw [List.flatMap_cons, St.toVerma_append, ih, List.map_cons, St.toVerma_cons, map_add,
      map_smul, ← hg t.1]
    congr 1
    have e : ((g t.1).map fun u => (u.1, algebraMap ℚ R u.2 * val t.2))
        = (ofQ (g t.1)).map fun u => (u.1, val t.2 * u.2) := by
      simp only [ofQ, List.map_map]
      refine List.map_congr_left fun u _ => ?_
      simp [mul_comm]
    rw [e, St.toVerma_map_smul]

theorem negIns_spec (f : ℕ) : ∀ (m : ℕ) (w : List ℕ),
    St.toVerma (c := c) (h := h) (ofQ (negIns f m w)) = L (-(m : ℤ)) (neg w) := by
  induction f with
  | zero =>
    intro m w
    simp [negIns, ofQ, St.toVerma_single, neg_cons]
  | succ f ih =>
    intro m w
    cases w with
    | nil => simp [negIns, ofQ, St.toVerma_single, neg_cons]
    | cons y w =>
      simp only [negIns]
      split_ifs with hym
      · simp [ofQ, St.toVerma_single, neg_cons]
      · push Not at hym
        rw [ofQ, List.map_append, St.toVerma_append]
        have h1 : St.toVerma (c := c) (h := h)
            (((negIns f m w).flatMap fun t => (negIns f y t.1).map fun u => (u.1, t.2 * u.2)).map
              fun t => (t.1, algebraMap ℚ R t.2))
            = L (-(y : ℤ)) (L (-(m : ℤ)) (neg w)) := by
          rw [← ih m w, ofQ,
            ← toVerma_flatMap (c := c) (h := h) (negIns f m w) (algebraMap ℚ R) (negIns f y) y (ih y),
            List.map_flatMap]
          congr 1
          refine List.flatMap_congr fun t _ => ?_
          simp only [List.map_map]
          refine List.map_congr_left fun u _ => ?_
          simp [map_mul, mul_comm]
        have h2 : St.toVerma (c := c) (h := h)
            (((negIns f (m + y) w).map fun u => (u.1, ((y - m : ℕ) : ℚ) * u.2)).map
              fun t => (t.1, algebraMap ℚ R t.2))
            = ((y - m : ℕ) : R) • L (-((m + y : ℕ) : ℤ)) (neg w) := by
          rw [← ih (m + y) w, ← St.toVerma_map_smul, ofQ, List.map_map, List.map_map]
          congr 1
          refine List.map_congr_left fun u _ => ?_
          simp [map_mul]
        rw [h1, h2, neg_cons, L_L (-(m : ℤ)) (-(y : ℤ)) (neg w), if_neg (by omega), add_zero]
        congr 1
        have e1 : -(m : ℤ) + -(y : ℤ) = -((m + y : ℕ) : ℤ) := by push_cast; ring
        have e2 : ((-(m : ℤ) - -(y : ℤ) : ℤ) : R) = ((y - m : ℕ) : R) := by
          rw [Nat.cast_sub hym.le]; push_cast; ring
        rw [e1, e2]

theorem posActAff_spec (f : ℕ) (w : List ℕ) : ∀ k : ℤ,
    St.toVerma (c := c) (h := h) (ofAff c h (posActAff f k w)) = L k (neg w) := by
  induction w with
  | nil =>
    intro k
    simp only [posActAff]
    split_ifs with hk hk0
    · have e : k = -((k.natAbs : ℕ) : ℤ) := by omega
      rw [e]
      simp [ofAff, evalAff, St.toVerma_single, neg_cons]
    · subst hk0
      simp [ofAff, evalAff, St.toVerma_single, neg_nil, L_hw_zero]
    · simp [ofAff, St.toVerma_nil, neg_nil, L_hw_pos (show 0 < k by omega)]
  | cons y w ih =>
    intro k
    rw [posActAff]
    by_cases hk : k < 0
    · rw [if_pos hk]
      have e : ofAff c h ((negIns f k.natAbs (y :: w)).map fun u => (u.1, ((u.2, 0, 0) : Aff)))
          = (ofQ (negIns f k.natAbs (y :: w)) : St R) := by
        simp [ofAff, ofQ, evalAff, List.map_map]
      rw [e, negIns_spec, show -((k.natAbs : ℕ) : ℤ) = k by omega]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0]
        subst hk0
        simp only [ofAff, List.map_cons, List.map_nil, St.toVerma_single]
        rw [L_zero_neg]
        congr 1
        simp only [evalAff, map_natCast, map_one, map_zero, one_mul, zero_mul, add_zero,
          List.sum_cons]
        push_cast
        ring
      · rw [if_neg hk0]
        have h1 : St.toVerma (c := c) (h := h)
            (((posActAff f k w).flatMap fun t =>
                (negIns f y t.1).map fun u => (u.1, affScale u.2 t.2)).map
              fun t => (t.1, evalAff c h t.2))
            = L (-(y : ℤ)) (L k (neg w)) := by
          rw [← ih k, ofAff,
            ← toVerma_flatMap (c := c) (h := h) (posActAff f k w) (evalAff c h) (negIns f y) y
              (negIns_spec f y),
            List.map_flatMap]
          congr 1
          refine List.flatMap_congr fun t _ => ?_
          simp only [List.map_map]
          refine List.map_congr_left fun u _ => ?_
          simp [evalAff_scale]
        have h2 : St.toVerma (c := c) (h := h)
            (((posActAff f (k - y) w).map fun t => (t.1, affScale ((k + y : ℤ) : ℚ) t.2)).map
              fun t => (t.1, evalAff c h t.2))
            = ((k + y : ℤ) : R) • L (k - y) (neg w) := by
          rw [← ih (k - y), ← St.toVerma_map_smul, ofAff, List.map_map, List.map_map]
          congr 1
          refine List.map_congr_left fun u _ => ?_
          simp [evalAff_scale]
        have h3 : St.toVerma (c := c) (h := h)
            ((if k = y then [(w, ((0, 0, ((k ^ 3 - k : ℤ) : ℚ) / 12) : Aff))] else []).map
              fun t => (t.1, evalAff c h t.2))
            = (if k + -(y : ℤ) = 0 then centralTerm c k • neg w else 0) := by
          by_cases hky : k = y
          · rw [if_pos hky, if_pos (by omega)]
            simp [evalAff, St.toVerma_single, centralTerm]
          · rw [if_neg hky, if_neg (by omega)]
            rfl
        rw [ofAff, List.map_append, List.map_append, St.toVerma_append, St.toVerma_append, h1, h2,
          h3, neg_cons, L_L k (-(y : ℤ)) (neg w)]
        have e1 : k + -(y : ℤ) = k - y := by ring
        have e2 : k - -(y : ℤ) = k + y := by ring
        rw [e1, e2]

end Semantics

end Virasoro
