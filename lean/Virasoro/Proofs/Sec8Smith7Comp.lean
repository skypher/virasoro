import Virasoro.Proofs.PBWBridge
import Virasoro.Proofs.Sec5TwoStep
import Virasoro.Proofs.ResidueCore1
import Virasoro.Statements.Sec8

/-!
# Proposition 8.1: the explicit level-seven computations

The singular vectors `φ₅`, `φ₄`, `ξ₇`, the two expressions of `ξ₇`, and the second crossing
form `γ₇ = -700700`, by the normal-ordering engine over `ℚ` and over `ℚ[x]/(x³)`.
-/

namespace Virasoro

open Verma

set_option maxRecDepth 100000

/-- `ℚ → ℂ`. -/
noncomputable abbrev qC : ℚ →+* ℂ := algebraMap ℚ ℂ

def xi2Q : List (List ℕ × ℚ) := [([1, 1], 1), ([2], -4 / 3)]
def xi3Q : List (List ℕ × ℚ) := [([1, 1, 1], 1), ([2, 1], -3), ([3], 3 / 4)]
def phi5Q : List (List ℕ × ℚ) :=
  [([1, 1, 1, 1, 1], 1), ([2, 1, 1, 1], -15), ([2, 2, 1], 36), ([3, 1, 1], 99 / 4),
    ([3, 2], -45), ([4, 1], -54), ([5], 45)]
def phi4Q : List (List ℕ × ℚ) :=
  [([1, 1, 1, 1], 1), ([2, 1, 1], -40 / 3), ([2, 2], 16), ([3, 1], 88 / 3), ([4], -152 / 3)]

/-- The coordinates of `ξ₇`. -/
def x7Q : List (List ℕ × ℚ) :=
  [([1, 1, 1, 1, 1, 1, 1], 1), ([2, 1, 1, 1, 1, 1], -49 / 3), ([3, 1, 1, 1, 1], 217 / 12),
    ([4, 1, 1, 1], -242 / 3), ([5, 1, 1], 25), ([6, 1], 80), ([7], -10), ([2, 2, 1, 1, 1], 56),
    ([3, 2, 1, 1], -18), ([4, 2, 1], 192), ([5, 2], -36), ([2, 2, 2, 1], -48), ([3, 2, 2], 12),
    ([3, 3, 1], -66), ([4, 3], 6)]

/-- A solution of `G₀ v₁ = - G₁ ξ₇`. -/
def v1Q : List (List ℕ × ℚ) := [([7], -340), ([6, 1], -304), ([5, 2], -176 / 3), ([4, 3], 288)]

theorem xi2_eq_mapSt : xi2 = mapSt qC xi2Q := by
  simp [xi2, xi2Q, mapSt, map_div₀]

theorem xi3_eq_mapSt : xi3 = mapSt qC xi3Q := by
  simp [xi3, xi3Q, mapSt, map_div₀]

theorem phi5_eq_mapSt : phi5 = mapSt qC phi5Q := by
  simp [phi5, phi5Q, mapSt, map_div₀]

theorem phi4_eq_mapSt : phi4 = mapSt qC phi4Q := by
  simp [phi4, phi4Q, mapSt, map_div₀]

theorem isLevel_phi5Q : IsLevelSt 5 phi5Q := by unfold IsLevelSt PosWord; decide
theorem isLevel_phi4Q : IsLevelSt 4 phi4Q := by unfold IsLevelSt PosWord; decide
theorem isLevel_x7Q : IsLevelSt 7 x7Q := by unfold IsLevelSt PosWord; decide
theorem isLevel_v1Q : IsLevelSt 7 v1Q := by unfold IsLevelSt PosWord; decide

theorem coords_ne_of_ones {N : ℕ} (s : List (List ℕ × ℚ))
    (h : ((s.filter fun t => t.1 = List.replicate N 1).map Prod.snd).sum ≠ 0) :
    St.coords N s ≠ 0 := by
  intro h0
  apply h
  have := congrFun h0 (onesPartition N)
  rwa [coords_ones] at this

/-- `φ₅` is singular in `M(1/2,5/2)`. -/
theorem phi5_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (5 / 2 : ℂ)) phi5) 5 := by
  rw [phi5_eq_mapSt]
  refine isSingular_ofQ 40 (1 / 2) (5 / 2) (by simp [map_div₀]) (by simp [map_div₀]) phi5Q
    isLevel_phi5Q (coords_ne_of_ones _ (by decide +kernel)) fun n h1 h2 => ?_
  interval_cases n <;> decide +kernel

/-- `φ₄` is singular in `M(1/2,7/2)`. -/
theorem phi4_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (7 / 2 : ℂ)) phi4) 4 := by
  rw [phi4_eq_mapSt]
  refine isSingular_ofQ 40 (1 / 2) (7 / 2) (by simp [map_div₀]) (by simp [map_div₀]) phi4Q
    isLevel_phi4Q (coords_ne_of_ones _ (by decide +kernel)) fun n h1 h2 => ?_
  interval_cases n <;> decide +kernel

theorem toVerma_opN_of (f : ℕ) (cq hq : ℚ) {c h : ℂ} (hc : qC cq = c) (hh : qC hq = h)
    (s t : List (List ℕ × ℚ)) :
    St.toVerma (c := c) (h := h) (mapSt qC (opN f cq hq s t))
      = St.toOp c (mapSt qC s) • St.toVerma (mapSt qC t) := by
  subst hc hh
  exact toVerma_opN qC f cq hq s t

theorem toVerma_mapSt_perm {c h : ℂ} {s s' : List (List ℕ × ℚ)} (hp : s.Perm s') :
    St.toVerma (c := c) (h := h) (mapSt qC s) = St.toVerma (mapSt qC s') :=
  toVerma_perm (hp.map _)

theorem opN_phi5_xi2 : (opN 40 (1 / 2 : ℚ) (1 / 2) phi5Q xi2Q).Perm x7Q := by decide +kernel

theorem opN_phi4_xi3 : (opN 40 (1 / 2 : ℚ) (1 / 2) phi4Q xi3Q).Perm x7Q := by decide +kernel

/-- `ξ₇ = j_{ξ₂}(φ₅)`, in coordinates. -/
theorem xi7_eq_x7 :
    St.toOp (1 / 2 : ℂ) phi5 • St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi2
      = St.toVerma (mapSt qC x7Q) := by
  rw [phi5_eq_mapSt, xi2_eq_mapSt,
    ← toVerma_opN_of 40 (1 / 2) (1 / 2) (by simp [map_div₀]) (by simp [map_div₀]),
    toVerma_mapSt_perm opN_phi5_xi2]

/-- `ξ₇ = j_{ξ₃}(φ₄)`, in coordinates. -/
theorem xi7_eq_x7' :
    St.toOp (1 / 2 : ℂ) phi4 • St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi3
      = St.toVerma (mapSt qC x7Q) := by
  rw [phi4_eq_mapSt, xi3_eq_mapSt,
    ← toVerma_opN_of 40 (1 / 2) (1 / 2) (by simp [map_div₀]) (by simp [map_div₀]),
    toVerma_mapSt_perm opN_phi4_xi3]

/-- `ξ₇` is singular. -/
theorem x7_singular :
    Verma.IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) (mapSt qC x7Q)) 7 := by
  refine isSingular_ofQ 40 (1 / 2) (1 / 2) (by simp [map_div₀]) (by simp [map_div₀]) x7Q
    isLevel_x7Q (coords_ne_of_ones _ (by decide +kernel)) fun n h1 h2 => ?_
  interval_cases n <;> decide +kernel

end Virasoro
