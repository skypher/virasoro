import Virasoro.Algebra
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Normal ordering and the Shapovalov and torus matrices (paper Definition 2.2, Lemma 2.4)

The matrix elements `⟨h| L_Y L_{-Y'} |h⟩` and `⟨h| L_Y V_d(1) L_{-Y'} |h⟩` are evaluated by the
commutation procedure in the proof of Lemma 2.4: positive modes are moved to the right with the
Virasoro commutator, and modes are moved through the primary field with the Ward commutator.
The evaluation is carried out over an arbitrary commutative `ℚ`-algebra `R` containing the
parameters `c`, `h`, `d`.

A word `w = [w₁, …, w_r]` of positive integers stands for the vector `L_{-w₁} ⋯ L_{-w_r} |h⟩`,
and a list of pairs (word, coefficient) for the corresponding linear combination.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The vector `L_k L_{-w₁} ⋯ L_{-w_r} |h⟩`, expanded by moving `L_k` to the right:
`L_k L_{-y} = L_{-y} L_k + (k + y) L_{k-y} + c/12 (k^3 - k) δ_{k,y}` for `k > 0`,
`L_0` acts on a word of level `|w|` by `h + |w|`, and a negative mode is prepended. -/
def actWord (c h : R) : ℤ → List ℕ → St R
  | k, [] => if k < 0 then [([k.natAbs], 1)] else if k = 0 then [([], h)] else []
  | k, y :: w =>
      if k < 0 then [(k.natAbs :: y :: w, 1)]
      else if k = 0 then [(y :: w, h + ((y + w.sum : ℕ) : R))]
      else
        ((actWord c h k w).map fun t => (y :: t.1, t.2)) ++
        ((actWord c h (k - y) w).map fun t => (t.1, ((k + y : ℤ) : R) * t.2)) ++
        (if k = y then [(w, centralTerm c k)] else [])

/-- `L_k` applied to a linear combination of words. -/
def actSt (c h : R) (k : ℤ) (s : St R) : St R :=
  s.flatMap fun t => (actWord c h k t.1).map fun u => (u.1, t.2 * u.2)

/-- The coefficient of the highest-weight vector `|h⟩` (the empty word). -/
def vac (s : St R) : R := (s.map fun t => if t.1.isEmpty then t.2 else 0).sum

/-- `⟨h| L_{y_ℓ} ⋯ L_{y₁} L_{-Y'} |h⟩` for words `Y = [y₁, …, y_ℓ]` and `Y'`: the modes
`L_{y₁}, L_{y₂}, …` are applied in turn to `L_{-Y'}|h⟩` and the coefficient of `|h⟩` is taken.
For weakly decreasing `Y` this is the Shapovalov matrix element
`⟨h| L_Y L_{-Y'} |h⟩`, `L_Y = L_{y_ℓ} ⋯ L_{y₁}`. -/
def gramWord (c h : R) (Y Y' : List ℕ) : R :=
  vac (Y.foldl (fun (s : St R) (y : ℕ) => actSt c h (y : ℤ) s) [(Y', 1)])

/-- `⟨h| V_d(1) L_{-w₁} ⋯ L_{-w_r} |h⟩`: by the Ward identity with `L_{w₁}⟨h|^† = 0`,
`⟨h|V_d(1) L_{-m} w'⟩ = (|w'| + m d) ⟨h|V_d(1) w'⟩`. -/
def phi (d : R) : List ℕ → R
  | [] => 1
  | m :: w => (((w.sum : ℕ) : R) + (m : R) * d) * phi d w

/-- `⟨h| L_{y_ℓ} ⋯ L_{y₁} V_d(1) L_{-w} |h⟩` for words `Y = [y₁, …, y_ℓ]` and `w`:
the mode `L_{y₁}` next to the field is moved through it,
`⟨u'| L_y V_d(1) |w⟩ = ⟨u'| V_d(1) L_y |w⟩ + (|u'| - |w| + y d) ⟨u'| V_d(1) |w⟩`. -/
def torusWord (c h d : R) : List ℕ → List ℕ → R
  | [], w => phi d w
  | y :: Y, w =>
      ((actWord c h (y : ℤ) w).map fun t => t.2 * torusWord c h d Y t.1).sum
        + (((Y.sum : ℕ) : R) - ((w.sum : ℕ) : R) + (y : R) * d) * torusWord c h d Y w

/-- The Shapovalov (Gram) matrix `G_N(c,h)` of level `N` (paper Definition 2.2):
`G_N(c,h)_{Y,Y'} = ⟨h| L_Y L_{-Y'} |h⟩`. -/
def gram (c h : R) (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) R :=
  Matrix.of fun Y Y' => gramWord c h Y.word Y'.word

/-- The torus matrix `ρ_N(c,h,d)` of level `N` (paper Definition 2.2):
`ρ_N(c,h,d)_{Y,Y'} = ⟨h| L_Y V_d(1) L_{-Y'} |h⟩`. -/
def torus (c h d : R) (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) R :=
  Matrix.of fun Y Y' => torusWord c h d Y.word Y'.word

@[simp] theorem centralTerm_zero (c : R) : centralTerm c 0 = 0 := by simp [centralTerm]
@[simp] theorem centralTerm_one (c : R) : centralTerm c 1 = 0 := by simp [centralTerm]
@[simp] theorem centralTerm_neg_one (c : R) : centralTerm c (-1) = 0 := by simp [centralTerm]

end Virasoro
