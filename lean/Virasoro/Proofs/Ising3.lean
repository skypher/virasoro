import Virasoro.Proofs.CoordTools
import Virasoro.Proofs.SmithSimple
import Virasoro.Statements.Sec5b
import Mathlib.Algebra.CharZero.Infinite

/-!
# The earliest Ising collision: explicit vectors at levels two and three

Singularity of `ξ₂` and `ξ₃` in `M(1/2,1/2)` by direct commutation, their Shapovalov forms as
polynomials in the weight, and their torus polynomials by the Ward recursion.
-/

namespace Virasoro

open Polynomial

variable (K : Type) [Field K] [CharZero K]

/-- `ξ₂ = (L_{-1}² - 4/3 L_{-2}) |1/2⟩` over a field of characteristic zero. -/
def xi2K : St K := [([1, 1], 1), ([2], -4 / 3)]

/-- `ξ₃ = (L_{-1}³ - 3 L_{-2} L_{-1} + 3/4 L_{-3}) |1/2⟩` over a field of characteristic
zero. -/
def xi3K : St K := [([1, 1, 1], 1), ([2, 1], -3), ([3], 3 / 4)]

/-- `L_{-1} ξ₂` over a field of characteristic zero. -/
def L1xi2K : St K := [([3], -4 / 3), ([2, 1], -4 / 3), ([1, 1, 1], 1)]

/-- `E₂(d)` over a field of characteristic zero. -/
noncomputable def E2K : K[X] := C (1 / 9) * X * (X - 1) * (3 * X - 14) * (3 * X - 5)

/-- `E₃(d)` over a field of characteristic zero. -/
noncomputable def E3K : K[X] :=
  C (1 / 16) * X * (X - 1) * (2 * X - 15) * (2 * X - 7) * (2 * X - 5) * (2 * X - 1)

theorem xi2_eq : xi2 = xi2K ℂ := rfl

theorem xi3_eq : xi3 = xi3K ℂ := rfl

theorem L1xi2_eq : L1xi2 = L1xi2K ℂ := rfl

theorem E2_eq : E2 = E2K ℂ := rfl

theorem E3_eq : E3 = E3K ℂ := rfl

omit [CharZero K] in
theorem isLevel_xi2 : IsLevelSt 2 (xi2K K) := by
  simp [IsLevelSt, xi2K, PosWord]

omit [CharZero K] in
theorem isLevel_xi3 : IsLevelSt 3 (xi3K K) := by
  simp [IsLevelSt, xi3K, PosWord]

omit [CharZero K] in
theorem isLevel_L1xi2 : IsLevelSt 3 (L1xi2K K) := by
  simp [IsLevelSt, L1xi2K, PosWord]

theorem coords_xi2_ne : St.coords 2 (xi2K K) ≠ 0 := by
  intro h0
  have hw : (partOf (N := 2) [1, 1] (by simp [PosWord]) rfl).word = [1, 1] :=
    partOf_word _ _ (by simp)
  have h1 := congrFun h0 (partOf [1, 1] (by simp [PosWord]) rfl)
  simp [St.coords, xi2K, hw] at h1

theorem coords_xi3_ne : St.coords 3 (xi3K K) ≠ 0 := by
  intro h0
  have hw : (partOf (N := 3) [1, 1, 1] (by simp [PosWord]) rfl).word = [1, 1, 1] :=
    partOf_word _ _ (by simp)
  have h1 := congrFun h0 (partOf [1, 1, 1] (by simp [PosWord]) rfl)
  simp [St.coords, xi3K, hw] at h1

/-- `ξ₂` is singular in `M(1/2,1/2)`: direct commutation with `L_1`, `L_2`. -/
theorem xi2_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : K)) (h := (1 / 2 : K)) (xi2K K)) 2 := by
  refine isSingular_of_actSt (xi2K K) (isLevel_xi2 K) (coords_xi2_ne K) fun n h1 h2 => ?_
  interval_cases n
  · simp [actSt, actWord, xi2K, St.toVerma, centralTerm]
    module
  · simp [actSt, actWord, xi2K, St.toVerma, centralTerm]
    module

/-- `ξ₃` is singular in `M(1/2,1/2)`: direct commutation with `L_1`, `L_2`, `L_3`. -/
theorem xi3_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : K)) (h := (1 / 2 : K)) (xi3K K)) 3 := by
  refine isSingular_of_actSt (xi3K K) (isLevel_xi3 K) (coords_xi3_ne K) fun n h1 h2 => ?_
  interval_cases n
  · simp [actSt, actWord, xi3K, St.toVerma, centralTerm]
    module
  · simp [actSt, actWord, xi3K, St.toVerma, centralTerm]
    module
  · simp [actSt, actWord, xi3K, St.toVerma, centralTerm]
    module

theorem L_neg_one_neg {c h : K} (w : List ℕ) :
    Verma.L (-1) (Verma.neg (c := c) (h := h) w) = Verma.neg (1 :: w) := by
  simpa using (Verma.neg_cons (c := c) (h := h) 1 w).symm

/-- `L_{-1} L_{-2} = L_{-2} L_{-1} + L_{-3}` on the highest-weight vector. -/
theorem neg_one_two {c h : K} :
    Verma.neg (c := c) (h := h) [1, 2] = Verma.neg [2, 1] + Verma.neg [3] := by
  have key := Verma.L_L (c := c) (h := h) (-1) (-2) (Verma.neg [])
  norm_num at key
  have e1 : Verma.neg (c := c) (h := h) [1, 2] = Verma.L (-1) (Verma.L (-2) (Verma.neg [])) := by
    rw [Verma.neg_cons, Verma.neg_cons]
    norm_num
  have e2 : Verma.neg (c := c) (h := h) [2, 1] = Verma.L (-2) (Verma.L (-1) (Verma.neg [])) := by
    rw [Verma.neg_cons, Verma.neg_cons]
    norm_num
  have e3 : Verma.neg (c := c) (h := h) [3] = Verma.L (-3) (Verma.neg []) := by
    rw [Verma.neg_cons]
    norm_num
  rw [e1, e2, e3, key]

/-- `L_{-1} ξ₂` in the Poincaré–Birkhoff–Witt basis. -/
theorem toVerma_L1xi2 :
    St.toVerma (c := (1 / 2 : K)) (h := (1 / 2 : K)) (L1xi2K K) = Verma.L (-1) (St.toVerma (xi2K K)) := by
  simp only [St.toVerma, L1xi2K, xi2K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, map_add, LinearMap.map_smul, L_neg_one_neg, neg_one_two]
  module

/-- `⟨ξ₂|ξ₂⟩` as a polynomial in the weight. -/
noncomputable def Qxi2 : K[X] := C 8 * X ^ 2 - C (44 / 9) * X + C (4 / 9)

/-- `⟨L_{-1}ξ₂|L_{-1}ξ₂⟩` as a polynomial in the weight. -/
noncomputable def Q11 : K[X] := C 48 * X ^ 3 - C (88 / 9) * X ^ 2 - C (32 / 3) * X + C (16 / 9)

/-- `⟨L_{-1}ξ₂|ξ₃⟩` as a polynomial in the weight. -/
noncomputable def Q12 : K[X] := C 48 * X ^ 3 - C 52 * X ^ 2 + C 16 * X - C 1

/-- `⟨ξ₃|ξ₃⟩` as a polynomial in the weight. -/
noncomputable def Q22 : K[X] := C 48 * X ^ 3 - C 72 * X ^ 2 + C (183 / 8) * X + C (9 / 16)

theorem gramForm_xi2 (x : K) :
    gramForm (1 / 2 : K) x 2 (St.coords 2 (xi2K K)) (St.coords 2 (xi2K K)) = (Qxi2 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_xi2 K) (isLevel_xi2 K)]
  simp [xi2K, Qxi2, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramForm_11 (x : K) :
    gramForm (1 / 2 : K) x 3 (St.coords 3 (L1xi2K K)) (St.coords 3 (L1xi2K K)) = (Q11 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L1xi2 K) (isLevel_L1xi2 K)]
  simp [L1xi2K, Q11, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramForm_12 (x : K) :
    gramForm (1 / 2 : K) x 3 (St.coords 3 (L1xi2K K)) (St.coords 3 (xi3K K)) = (Q12 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L1xi2 K) (isLevel_xi3 K)]
  simp [L1xi2K, xi3K, Q12, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramForm_21 (x : K) :
    gramForm (1 / 2 : K) x 3 (St.coords 3 (xi3K K)) (St.coords 3 (L1xi2K K)) = (Q12 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_xi3 K) (isLevel_L1xi2 K)]
  simp [L1xi2K, xi3K, Q12, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramForm_22 (x : K) :
    gramForm (1 / 2 : K) x 3 (St.coords 3 (xi3K K)) (St.coords 3 (xi3K K)) = (Q22 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_xi3 K) (isLevel_xi3 K)]
  simp [xi3K, Q22, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem crossScalar_xi2 : crossScalar (1 / 2 : K) (1 / 2) (St.coords 2 (xi2K K)) = 28 / 9 := by
  rw [crossScalar_eq (gramForm_xi2 K)]
  simp [Qxi2]
  norm_num

theorem crossScalar_xi3 : crossScalar (1 / 2 : K) (1 / 2) (St.coords 3 (xi3K K)) = -105 / 8 := by
  rw [crossScalar_eq (gramForm_22 K)]
  simp [Q22]
  norm_num

theorem cross1_11 : cross1 (gramLocal (1 / 2 : K) (1 / 2) 3) (St.coords 3 (L1xi2K K))
    (St.coords 3 (L1xi2K K)) = 140 / 9 := by
  rw [cross1_gramLocal_eq (gramForm_11 K)]
  simp [Q11]
  norm_num

theorem cross1_12 : cross1 (gramLocal (1 / 2 : K) (1 / 2) 3) (St.coords 3 (L1xi2K K))
    (St.coords 3 (xi3K K)) = 0 := by
  rw [cross1_gramLocal_eq (gramForm_12 K)]
  simp [Q12]
  norm_num

theorem cross1_21 : cross1 (gramLocal (1 / 2 : K) (1 / 2) 3) (St.coords 3 (xi3K K))
    (St.coords 3 (L1xi2K K)) = 0 := by
  rw [cross1_gramLocal_eq (gramForm_21 K)]
  simp [Q12]
  norm_num

theorem cross1_22 : cross1 (gramLocal (1 / 2 : K) (1 / 2) 3) (St.coords 3 (xi3K K))
    (St.coords 3 (xi3K K)) = -105 / 8 := by
  rw [cross1_gramLocal_eq (gramForm_22 K)]
  simp [Q22]
  norm_num

/-- `⟨ξ₂|V_d(1)|ξ₂⟩ = E₂(d)` by the Ward recursion. -/
theorem torus_xi2 (d : K) :
    torusForm (1 / 2 : K) (1 / 2) d 2 (St.coords 2 (xi2K K)) (St.coords 2 (xi2K K)) = (E2K K).eval d := by
  rw [torusForm_coords _ _ _ _ _ (isLevel_xi2 K) (isLevel_xi2 K)]
  simp [xi2K, E2K, torusWord, phi, actWord, centralTerm]
  ring

/-- `⟨ξ₃|V_d(1)|ξ₃⟩ = E₃(d)` by the Ward recursion. -/
theorem torus_xi3 (d : K) :
    torusForm (1 / 2 : K) (1 / 2) d 3 (St.coords 3 (xi3K K)) (St.coords 3 (xi3K K)) = (E3K K).eval d := by
  rw [torusForm_coords _ _ _ _ _ (isLevel_xi3 K) (isLevel_xi3 K)]
  simp [xi3K, E3K, torusWord, phi, actWord, centralTerm]
  ring

end Virasoro
