import Virasoro.Proofs.Ising2

/-!
# The first spin-module collision: explicit vectors at levels two and four

Singularity of `χ₂` and `χ₄` in `M(1/2,1/16)` by direct commutation, the Shapovalov forms of
`L_{-2}χ₂`, `L_{-1}²χ₂`, `χ₄` as polynomials in the weight, and the torus polynomials.
-/

namespace Virasoro

open Polynomial

set_option maxRecDepth 20000

variable (K : Type) [Field K] [CharZero K]

/-- `χ₂ = (L_{-1}² - 3/4 L_{-2}) |1/16⟩` over a field of characteristic zero. -/
def chi2K : St K := [([1, 1], 1), ([2], -3 / 4)]

/-- `χ₄` over a field of characteristic zero. -/
def chi4K : St K :=
  [([1, 1, 1, 1], 1), ([2, 1, 1], -25 / 6), ([2, 2], 49 / 144), ([3, 1], 11 / 6), ([4], -1 / 4)]

/-- `L_{-2} χ₂` over a field of characteristic zero. -/
def L2chi2K : St K := [([2, 2], -3 / 4), ([2, 1, 1], 1)]

/-- `L_{-1}² χ₂` over a field of characteristic zero. -/
def L11chi2K : St K :=
  [([4], -3 / 2), ([3, 1], -3 / 2), ([2, 1, 1], -3 / 4), ([1, 1, 1, 1], 1)]

/-- `P₂(d)` over a field of characteristic zero. -/
noncomputable def P2K : K[X] := C (1 / 4) * X * (X - 1) * (2 * X - 7) * (2 * X - 1)

/-- `P₄(d)` over a field of characteristic zero. -/
noncomputable def P4K : K[X] :=
  C (1 / 1296) * X * (X - 1) * (2 * X - 7) * (2 * X - 1) * (3 * X - 14) * (3 * X - 5) *
    (6 * X - 55) * (6 * X - 1)

theorem chi2_eq : chi2 = chi2K ℂ := rfl

theorem chi4_eq : chi4 = chi4K ℂ := rfl

theorem L2chi2_eq : L2chi2 = L2chi2K ℂ := rfl

theorem L11chi2_eq : L11chi2 = L11chi2K ℂ := rfl

theorem P2_eq : P2 = P2K ℂ := rfl

theorem P4_eq : P4 = P4K ℂ := rfl

omit [CharZero K] in
theorem isLevel_chi2 : IsLevelSt 2 (chi2K K) := by
  simp [IsLevelSt, chi2K, PosWord]

omit [CharZero K] in
theorem isLevel_chi4 : IsLevelSt 4 (chi4K K) := by
  simp [IsLevelSt, chi4K, PosWord]

omit [CharZero K] in
theorem isLevel_L2chi2 : IsLevelSt 4 (L2chi2K K) := by
  simp [IsLevelSt, L2chi2K, PosWord]

omit [CharZero K] in
theorem isLevel_L11chi2 : IsLevelSt 4 (L11chi2K K) := by
  simp [IsLevelSt, L11chi2K, PosWord]

theorem coords_chi2_ne : St.coords 2 (chi2K K) ≠ 0 := by
  intro h0
  have hw : (partOf (N := 2) [1, 1] (by simp [PosWord]) rfl).word = [1, 1] :=
    partOf_word _ _ (by simp)
  have h1 := congrFun h0 (partOf [1, 1] (by simp [PosWord]) rfl)
  simp [St.coords, chi2K, hw] at h1

theorem coords_chi4_ne : St.coords 4 (chi4K K) ≠ 0 := by
  intro h0
  have hw : (partOf (N := 4) [1, 1, 1, 1] (by simp [PosWord]) rfl).word = [1, 1, 1, 1] :=
    partOf_word _ _ (by simp)
  have h1 := congrFun h0 (partOf [1, 1, 1, 1] (by simp [PosWord]) rfl)
  simp [St.coords, chi4K, hw] at h1

/-- `χ₂` is singular in `M(1/2,1/16)`. -/
theorem chi2_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : K)) (h := (1 / 16 : K)) (chi2K K)) 2 := by
  refine isSingular_of_actSt (chi2K K) (isLevel_chi2 K) (coords_chi2_ne K) fun n h1 h2 => ?_
  interval_cases n
  · simp [actSt, actWord, chi2K, St.toVerma, centralTerm]
    module
  · simp [actSt, actWord, chi2K, St.toVerma, centralTerm]
    module

/-- `χ₄` is singular in `M(1/2,1/16)`. -/
theorem chi4_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : K)) (h := (1 / 16 : K)) (chi4K K)) 4 := by
  refine isSingular_of_actSt (chi4K K) (isLevel_chi4 K) (coords_chi4_ne K) fun n h1 h2 => ?_
  interval_cases n
  · simp [actSt, actWord, chi4K, St.toVerma, centralTerm, neg_one_two]
    module
  · simp [actSt, actWord, chi4K, St.toVerma, centralTerm]
    module
  · simp [actSt, actWord, chi4K, St.toVerma, centralTerm]
    module
  · simp [actSt, actWord, chi4K, St.toVerma, centralTerm]
    module

theorem L_neg_one_neg_two {c h : K} (v : Verma K c h) :
    Verma.L (-1) (Verma.L (-2) v) = Verma.L (-2) (Verma.L (-1) v) + Verma.L (-3) v := by
  have key := Verma.L_L (c := c) (h := h) (-1) (-2) v
  norm_num at key
  exact key

theorem L_neg_one_neg_three {c h : K} (v : Verma K c h) :
    Verma.L (-1) (Verma.L (-3) v)
      = Verma.L (-3) (Verma.L (-1) v) + (2 : K) • Verma.L (-4) v := by
  have key := Verma.L_L (c := c) (h := h) (-1) (-3) v
  norm_num at key
  exact key

/-- `L_{-2} χ₂` in the Poincaré–Birkhoff–Witt basis. -/
theorem toVerma_L2chi2 :
    St.toVerma (c := (1 / 2 : K)) (h := (1 / 16 : K)) (L2chi2K K)
      = Verma.L (-2) (St.toVerma (chi2K K)) := by
  simp only [St.toVerma, L2chi2K, chi2K, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, map_add, LinearMap.map_smul, Verma.neg_cons, Nat.cast_ofNat,
    Nat.cast_one]
  module

/-- `L_{-1}² χ₂` in the Poincaré–Birkhoff–Witt basis. -/
theorem toVerma_L11chi2 :
    St.toVerma (c := (1 / 2 : K)) (h := (1 / 16 : K)) (L11chi2K K)
      = Verma.L (-1) (Verma.L (-1) (St.toVerma (chi2K K))) := by
  simp only [St.toVerma, L11chi2K, chi2K, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, map_add, LinearMap.map_smul, Verma.neg_cons, Nat.cast_ofNat,
    Nat.cast_one, L_neg_one_neg_two, L_neg_one_neg_three]
  module

/-- `⟨χ₂|χ₂⟩` as a polynomial in the weight. -/
noncomputable def Qchi2 : K[X] := C 8 * X ^ 2 - C (11 / 4) * X + C (9 / 64)

/-- `⟨L_{-2}χ₂|L_{-2}χ₂⟩` as a polynomial in the weight. -/
noncomputable def R11 : K[X] :=
  C 32 * X ^ 3 + C 64 * X ^ 2 - C (93 / 4) * X + C (153 / 128)

/-- `⟨L_{-2}χ₂|L_{-1}²χ₂⟩` as a polynomial in the weight. -/
noncomputable def R12 : K[X] :=
  C 264 * X ^ 3 + C (105 / 2) * X ^ 2 - C (501 / 16) * X + C (27 / 16)

/-- `⟨L_{-2}χ₂|χ₄⟩` as a polynomial in the weight. -/
noncomputable def R13 : K[X] :=
  C (464 / 3) * X ^ 3 - C (517 / 6) * X ^ 2 + C (215 / 24) * X - C (401 / 1536)

/-- `⟨L_{-1}²χ₂|L_{-1}²χ₂⟩` as a polynomial in the weight. -/
noncomputable def R22 : K[X] :=
  C 384 * X ^ 4 + C 738 * X ^ 3 + C (1275 / 8) * X ^ 2 - C (1647 / 16) * X + C (45 / 8)

/-- `⟨L_{-1}²χ₂|χ₄⟩` as a polynomial in the weight. -/
noncomputable def R23 : K[X] :=
  C 384 * X ^ 4 - C 164 * X ^ 3 + C 60 * X ^ 2 - C (381 / 64) * X + C (11 / 64)

/-- `⟨χ₄|χ₄⟩` as a polynomial in the weight. -/
noncomputable def R33 : K[X] :=
  C 384 * X ^ 4 - C (6232 / 9) * X ^ 3 + C (293173 / 648) * X ^ 2 - C (16139 / 576) * X
    + C (24401 / 165888)

theorem gramForm_chi2 (x : K) :
    gramForm (1 / 2 : K) x 2 (St.coords 2 (chi2K K)) (St.coords 2 (chi2K K))
      = (Qchi2 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_chi2 K) (isLevel_chi2 K)]
  simp [chi2K, Qchi2, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR11 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (L2chi2K K)) (St.coords 4 (L2chi2K K))
      = (R11 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L2chi2 K) (isLevel_L2chi2 K)]
  simp [L2chi2K, R11, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR12 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (L2chi2K K)) (St.coords 4 (L11chi2K K))
      = (R12 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L2chi2 K) (isLevel_L11chi2 K)]
  simp [L2chi2K, L11chi2K, R12, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR21 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (L11chi2K K)) (St.coords 4 (L2chi2K K))
      = (R12 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L11chi2 K) (isLevel_L2chi2 K)]
  simp [L2chi2K, L11chi2K, R12, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR13 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (L2chi2K K)) (St.coords 4 (chi4K K))
      = (R13 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L2chi2 K) (isLevel_chi4 K)]
  simp [L2chi2K, chi4K, R13, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR31 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (chi4K K)) (St.coords 4 (L2chi2K K))
      = (R13 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_chi4 K) (isLevel_L2chi2 K)]
  simp [L2chi2K, chi4K, R13, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR22 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (L11chi2K K)) (St.coords 4 (L11chi2K K))
      = (R22 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L11chi2 K) (isLevel_L11chi2 K)]
  simp [L11chi2K, R22, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR23 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (L11chi2K K)) (St.coords 4 (chi4K K))
      = (R23 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_L11chi2 K) (isLevel_chi4 K)]
  simp [L11chi2K, chi4K, R23, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR32 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (chi4K K)) (St.coords 4 (L11chi2K K))
      = (R23 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_chi4 K) (isLevel_L11chi2 K)]
  simp [L11chi2K, chi4K, R23, gramWord, actSt, actWord, vac, centralTerm]
  ring

theorem gramFormR33 (x : K) :
    gramForm (1 / 2 : K) x 4 (St.coords 4 (chi4K K)) (St.coords 4 (chi4K K))
      = (R33 K).eval x := by
  rw [gramForm_coords _ _ _ _ (isLevel_chi4 K) (isLevel_chi4 K)]
  simp [chi4K, R33, gramWord, actSt, actWord, vac, centralTerm]
  ring

end Virasoro
