import Virasoro.Statements.Sec5a

/-!
# Frozen statements: Section 5, Ising collisions (Proposition 5.11 – Theorem 5.15)

Explicit vectors are given as lists of (word, coefficient) pairs: the word `[y₁, …, y_ℓ]`
stands for `L_{-y₁} ⋯ L_{-y_ℓ}`.
-/

namespace Virasoro

open Polynomial

/-- The torus matrix element `⟨v| V_d(1) |v⟩` of a vector with level-`N` coordinates `v` in
`M(c,h)`, as a polynomial in `d`. -/
noncomputable def torusPolyForm (c h : ℂ) {N : ℕ} (v : Nat.Partition N → ℂ) : ℂ[X] :=
  torusForm (C c) (C h) (X : ℂ[X]) N (fun Y => C (v Y)) (fun Y => C (v Y))

/-- `ξ₂ = (L_{-1}² - 4/3 L_{-2}) |1/2⟩`. -/
noncomputable def xi2 : St ℂ := [([1, 1], 1), ([2], -4 / 3)]

/-- `ξ₃ = (L_{-1}³ - 3 L_{-2} L_{-1} + 3/4 L_{-3}) |1/2⟩`. -/
noncomputable def xi3 : St ℂ := [([1, 1, 1], 1), ([2, 1], -3), ([3], 3 / 4)]

/-- `L_{-1} ξ₂ = (-4/3 L_{-3} - 4/3 L_{-2} L_{-1} + L_{-1}³) |1/2⟩`. -/
noncomputable def L1xi2 : St ℂ := [([3], -4 / 3), ([2, 1], -4 / 3), ([1, 1, 1], 1)]

/-- `E₂(d) = d (d-1) (3d-14) (3d-5) / 9`. -/
noncomputable def E2 : ℂ[X] := C (1 / 9) * X * (X - 1) * (3 * X - 14) * (3 * X - 5)

/-- `E₃(d) = d (d-1) (2d-15) (2d-7) (2d-5) (2d-1) / 16`. -/
noncomputable def E3 : ℂ[X] :=
  C (1 / 16) * X * (X - 1) * (2 * X - 15) * (2 * X - 7) * (2 * X - 5) * (2 * X - 1)

/-- Proposition 5.11 (`prop:first-collision`).  The first repeated Ising Kac weight occurs at
level `3`: `Δ_{2,1} = Δ_{1,3} = 1/2`.  In `M(1/2,1/2)` the vectors `ξ₂`, `ξ₃` are singular; at
level `3`, `ker G₃(1/2,1/2) = span{L_{-1} ξ₂, ξ₃}` and the local Smith exponents are `(0,1,1)`;
the crossing scalars are `β_{ξ₂} = 28/9`, `β_{ξ₃} = -105/8`; the level-three crossing form in
the ordered basis `(L_{-1} ξ₂, ξ₃)` is `diag(140/9, -105/8) = diag(28/9 · G₁(1/2,5/2), -105/8)`;
and `⟨ξ₂|V_d(1)|ξ₂⟩ = E₂(d)`, `⟨ξ₃|V_d(1)|ξ₃⟩ = E₃(d)`. -/
def Stmt_prop_first_collision : Prop :=
  (isingDelta 2 1 = 1 / 2 ∧ isingDelta 1 3 = 1 / 2 ∧
    ∀ a ∈ labels 2, ∀ a' ∈ labels 2,
      isingDelta (a.1 : ℤ) (a.2 : ℤ) = isingDelta (a'.1 : ℤ) (a'.2 : ℤ) → a = a') ∧
  Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi2) 2 ∧
  Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi3) 3 ∧
  St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) L1xi2 = Verma.L (-1) (St.toVerma xi2) ∧
  LinearMap.ker (gram (1 / 2 : ℂ) (1 / 2) 3).mulVecLin =
    Submodule.span ℂ {St.coords 3 L1xi2, St.coords 3 xi3} ∧
  IsSmith (gramLocal (1 / 2 : ℂ) (1 / 2) 3) {0, 1, 1} ∧
  crossScalar (1 / 2 : ℂ) (1 / 2) (St.coords 2 xi2) = 28 / 9 ∧
  crossScalar (1 / 2 : ℂ) (1 / 2) (St.coords 3 xi3) = -105 / 8 ∧
  (cross1 (gramLocal (1 / 2 : ℂ) (1 / 2) 3) (St.coords 3 L1xi2) (St.coords 3 L1xi2) = 140 / 9 ∧
    cross1 (gramLocal (1 / 2 : ℂ) (1 / 2) 3) (St.coords 3 L1xi2) (St.coords 3 xi3) = 0 ∧
    cross1 (gramLocal (1 / 2 : ℂ) (1 / 2) 3) (St.coords 3 xi3) (St.coords 3 L1xi2) = 0 ∧
    cross1 (gramLocal (1 / 2 : ℂ) (1 / 2) 3) (St.coords 3 xi3) (St.coords 3 xi3) = -105 / 8) ∧
  (140 / 9 : ℂ) = 28 / 9 * gram (1 / 2 : ℂ) (5 / 2) 1 (onesPartition 1) (onesPartition 1) ∧
  torusPolyForm (1 / 2) (1 / 2) (St.coords 2 xi2) = E2 ∧
  torusPolyForm (1 / 2) (1 / 2) (St.coords 3 xi3) = E3

/-- Theorem 5.12 (`thm:first-recursive-residue`).  At `c = 1/2` the earliest collided
coefficient has the simple principal part
`Res_{Δ=1/2} H₃(1/2,Δ,d) = 9/28 E₂(d) H₁(1/2,5/2,d) - 8/105 E₃(d)`. -/
def Stmt_thm_first_recursive_residue : Prop :=
  poleOrder (HN (1 / 2) 3) (pt (1 / 2)) ≤ 1 ∧
  ppCoeff (HN (1 / 2) 3) (pt (1 / 2)) 1 =
    (9 / 28 : Kd) * algebraMap ℂ[X] Kd E2 *
        RatFunc.eval (RingHom.id Kd) (pt (5 / 2)) (HN (1 / 2) 1)
      - (8 / 105 : Kd) * algebraMap ℂ[X] Kd E3

/-- Proposition 5.13 (`prop:spin-collision`).  At level `4` the labels `(1,2)` and `(2,2)`
collide at `Δ = 1/16`; the Shapovalov determinant at `c = 1/2` is
`12 Δ³ (2Δ-7) (2Δ-1)³ (3Δ-5) (16Δ-21) (16Δ-1)³`; at `Δ = 1/16` the local Smith exponents are
`(0,0,1,1,1)`; consequently `G₄(1/2,Δ)⁻¹`, `F₄(1/2,Δ,d)` and `H₄(1/2,Δ,d)` have at most a simple
pole at `Δ = 1/16`. -/
def Stmt_prop_spin_collision : Prop :=
  (isingDelta 1 2 = 1 / 16 ∧ isingDelta 2 2 = 1 / 16) ∧
  (gramPoly (1 / 2 : ℂ) 4).det =
    12 * X ^ 3 * (2 * X - 7) * (2 * X - 1) ^ 3 * (3 * X - 5) * (16 * X - 21) * (16 * X - 1) ^ 3 ∧
  IsSmith (gramLocal (1 / 2 : ℂ) (1 / 16) 4) {0, 0, 1, 1, 1} ∧
  poleOrderInv (gramLocal (1 / 2 : ℂ) (1 / 16) 4) ≤ 1 ∧
  poleOrder (FN (1 / 2) 4) (pt (1 / 16)) ≤ 1 ∧
  poleOrder (HN (1 / 2) 4) (pt (1 / 16)) ≤ 1

/-- `χ₂ = (L_{-1}² - 3/4 L_{-2}) |1/16⟩`. -/
noncomputable def chi2 : St ℂ := [([1, 1], 1), ([2], -3 / 4)]

/-- `χ₄ = (L_{-1}⁴ - 25/6 L_{-2} L_{-1}² + 49/144 L_{-2}² + 11/6 L_{-3} L_{-1} - 1/4 L_{-4})
|1/16⟩`. -/
noncomputable def chi4 : St ℂ :=
  [([1, 1, 1, 1], 1), ([2, 1, 1], -25 / 6), ([2, 2], 49 / 144), ([3, 1], 11 / 6), ([4], -1 / 4)]

/-- `L_{-2} χ₂ = (-3/4 L_{-2}² + L_{-2} L_{-1}²) |1/16⟩`. -/
noncomputable def L2chi2 : St ℂ := [([2, 2], -3 / 4), ([2, 1, 1], 1)]

/-- `L_{-1}² χ₂ = (-3/2 L_{-4} - 3/2 L_{-3} L_{-1} - 3/4 L_{-2} L_{-1}² + L_{-1}⁴) |1/16⟩`. -/
noncomputable def L11chi2 : St ℂ :=
  [([4], -3 / 2), ([3, 1], -3 / 2), ([2, 1, 1], -3 / 4), ([1, 1, 1, 1], 1)]

/-- `P₂(d) = d (d-1) (2d-7) (2d-1) / 4`. -/
noncomputable def P2 : ℂ[X] := C (1 / 4) * X * (X - 1) * (2 * X - 7) * (2 * X - 1)

/-- `P₄(d) = d (d-1) (2d-7) (2d-1) (3d-14) (3d-5) (6d-55) (6d-1) / 1296`. -/
noncomputable def P4 : ℂ[X] :=
  C (1 / 1296) * X * (X - 1) * (2 * X - 7) * (2 * X - 1) * (3 * X - 14) * (3 * X - 5) *
    (6 * X - 55) * (6 * X - 1)

/-- Proposition 5.14 (`prop:spin-singular-data`).  With `h₀ = 1/16`, the vectors `χ₂`, `χ₄` of
`M(1/2,h₀)` are singular; `ker G₄(1/2,h₀) = span{L_{-2} χ₂, L_{-1}² χ₂, χ₄}`; in this ordered
basis the crossing form is
`β₄ = [[-119/8, -693/32, 0], [-693/32, -9471/128, 0], [0, 0, 13475/648]]
    = diag(-7/4 · G₂(1/2,33/16), 13475/648)`,
with `G₂(1/2,33/16) = [[17/2, 99/8], [99/8, 1353/32]]` in the basis `(L_{-2}, L_{-1}²)`;
and `⟨χ₂|V_d(1)|χ₂⟩ = P₂(d)`, `⟨χ₄|V_d(1)|χ₄⟩ = P₄(d)`. -/
def Stmt_prop_spin_singular_data : Prop :=
  Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2) 2 ∧
  Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) 4 ∧
  St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) L2chi2 = Verma.L (-2) (St.toVerma chi2) ∧
  St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) L11chi2 =
    Verma.L (-1) (Verma.L (-1) (St.toVerma chi2)) ∧
  LinearMap.ker (gram (1 / 2 : ℂ) (1 / 16) 4).mulVecLin =
    Submodule.span ℂ {St.coords 4 L2chi2, St.coords 4 L11chi2, St.coords 4 chi4} ∧
  (let β := cross1 (gramLocal (1 / 2 : ℂ) (1 / 16) 4)
   let u₁ := St.coords 4 L2chi2
   let u₂ := St.coords 4 L11chi2
   let u₃ := St.coords 4 chi4
   β u₁ u₁ = -119 / 8 ∧ β u₁ u₂ = -693 / 32 ∧ β u₁ u₃ = 0 ∧
   β u₂ u₁ = -693 / 32 ∧ β u₂ u₂ = -9471 / 128 ∧ β u₂ u₃ = 0 ∧
   β u₃ u₁ = 0 ∧ β u₃ u₂ = 0 ∧ β u₃ u₃ = 13475 / 648) ∧
  (let G := gram (1 / 2 : ℂ) (33 / 16) 2
   let y₂ := Nat.Partition.indiscrete 2
   let y₁₁ := onesPartition 2
   G y₂ y₂ = 17 / 2 ∧ G y₂ y₁₁ = 99 / 8 ∧ G y₁₁ y₂ = 99 / 8 ∧ G y₁₁ y₁₁ = 1353 / 32) ∧
  torusPolyForm (1 / 2) (1 / 16) (St.coords 2 chi2) = P2 ∧
  torusPolyForm (1 / 2) (1 / 16) (St.coords 4 chi4) = P4

/-- Theorem 5.15 (`thm:spin-recursive-residue`).  At `c = 1/2`,
`Res_{Δ=1/16} H₄(1/2,Δ,d) = -4/7 P₂(d) H₂(1/2,33/16,d) + 648/13475 P₄(d)`, and this residue is
`d (d-1) (2d-7) (2d-1) (248 d⁴ - 5752 d³ + 25274 d² - 33630 d + 5775) / 40425`. -/
def Stmt_thm_spin_recursive_residue : Prop :=
  ppCoeff (HN (1 / 2) 4) (pt (1 / 16)) 1 =
    -(4 / 7 : Kd) * algebraMap ℂ[X] Kd P2 *
        RatFunc.eval (RingHom.id Kd) (pt (33 / 16)) (HN (1 / 2) 2)
      + (648 / 13475 : Kd) * algebraMap ℂ[X] Kd P4 ∧
  ppCoeff (HN (1 / 2) 4) (pt (1 / 16)) 1 =
    algebraMap ℂ[X] Kd
      (C (1 / 40425) * X * (X - 1) * (2 * X - 7) * (2 * X - 1) *
        (248 * X ^ 4 - 5752 * X ^ 3 + 25274 * X ^ 2 - 33630 * X + 5775))

end Virasoro
