import Virasoro.Proofs.PBWEngine
import Virasoro.Proofs.Naturality

/-!
# The normal-ordering engine on states

`actN f c h k s` applies `L_k` to a combination `s` of words with coefficients in a computable
ring `A`, collects equal words and drops zero coefficients.  Read in the Verma module over any
`ℚ`-algebra `R` through a ring homomorphism `φ : A →+* R`, it computes `L_k` exactly
(`toVerma_actN`).  `negN f w s` applies `L_{-w}`.
-/

namespace Virasoro

open Verma

section Collect

variable {α : Type*}

/-- Add `a` to the coefficient of the word `w`. -/
def addTo [Add α] (w : List ℕ) (a : α) : List (List ℕ × α) → List (List ℕ × α)
  | [] => [(w, a)]
  | t :: s => if t.1 = w then (t.1, t.2 + a) :: s else t :: addTo w a s

/-- Collect equal words. -/
def collect [Add α] (s : List (List ℕ × α)) : List (List ℕ × α) :=
  s.foldl (fun acc t => addTo t.1 t.2 acc) []

/-- Drop zero coefficients. -/
def prune [Zero α] [DecidableEq α] (s : List (List ℕ × α)) : List (List ℕ × α) :=
  s.filter fun t => t.2 ≠ 0

end Collect

section State

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- `L_k` on a combination of words, at `(c, h)`, before collecting. -/
def posActSt (f : ℕ) (c h : A) (k : ℤ) (s : List (List ℕ × A)) : List (List ℕ × A) :=
  s.flatMap fun t => (posActAff f k t.1).map fun u => (u.1, t.2 * evalAff c h u.2)

/-- `L_k` on a combination of words, collected and pruned. -/
def actN [DecidableEq A] (f : ℕ) (c h : A) (k : ℤ) (s : List (List ℕ × A)) :
    List (List ℕ × A) :=
  prune (collect (posActSt f c h k s))

/-- `L_{-w} = L_{-w₁} ⋯ L_{-w_r}` on a combination of words (the last mode acts first). -/
def negN [DecidableEq A] (f : ℕ) (c h : A) (w : List ℕ) (s : List (List ℕ × A)) :
    List (List ℕ × A) :=
  w.foldr (fun y acc => actN f c h (-(y : ℤ)) acc) s

/-- `L_{y_ℓ} ⋯ L_{y₁}` on a combination of words, the modes `y₁, y₂, …` applied in turn. -/
def posN [DecidableEq A] (f : ℕ) (c h : A) (Y : List ℕ) (s : List (List ℕ × A)) :
    List (List ℕ × A) :=
  Y.foldl (fun acc y => actN f c h (y : ℤ) acc) s

/-- `(∑ a L_{-w}) t` for combinations `s`, `t` of words. -/
def opN [DecidableEq A] (f : ℕ) (c h : A) (s t : List (List ℕ × A)) : List (List ℕ × A) :=
  prune (collect (s.flatMap fun u => (negN f c h u.1 t).map fun v => (v.1, u.2 * v.2)))

end State

section Semantics

variable {A R : Type*} [CommRing A] [Algebra ℚ A] [CommRing R] [Algebra ℚ R] (φ : A →+* R)
variable {c h : R}

theorem toVerma_addTo (w : List ℕ) (a : R) : ∀ s : St R,
    St.toVerma (c := c) (h := h) (addTo w a s) = St.toVerma s + a • neg w
  | [] => by simp [addTo, St.toVerma_single, St.toVerma_nil]
  | t :: s => by
    unfold addTo
    split_ifs with ht
    · rw [St.toVerma_cons, St.toVerma_cons, ← ht, add_smul]
      abel
    · rw [St.toVerma_cons, St.toVerma_cons, toVerma_addTo w a s]
      abel

theorem toVerma_foldl_addTo : ∀ (s acc : St R),
    St.toVerma (c := c) (h := h) (s.foldl (fun acc t => addTo t.1 t.2 acc) acc)
      = St.toVerma acc + St.toVerma s
  | [], acc => by simp [St.toVerma_nil]
  | t :: s, acc => by
    rw [List.foldl_cons, toVerma_foldl_addTo s, toVerma_addTo, St.toVerma_cons]
    abel

theorem toVerma_collect (s : St R) :
    St.toVerma (c := c) (h := h) (collect s) = St.toVerma s := by
  rw [collect, toVerma_foldl_addTo, St.toVerma_nil, zero_add]

theorem mapSt_addTo (w : List ℕ) (a : A) (s : List (List ℕ × A)) :
    mapSt φ (addTo w a s) = addTo w (φ a) (mapSt φ s) := by
  induction s with
  | nil => simp [addTo, mapSt]
  | cons t s ih =>
    by_cases ht : t.1 = w
    · simp [addTo, mapSt, ht, map_add]
    · simp only [mapSt] at ih ⊢
      simp [addTo, ht, ih]

theorem mapSt_collect (s : List (List ℕ × A)) : mapSt φ (collect s) = collect (mapSt φ s) := by
  unfold collect
  suffices ∀ acc : List (List ℕ × A), mapSt φ (s.foldl (fun acc t => addTo t.1 t.2 acc) acc)
      = (mapSt φ s).foldl (fun acc t => addTo t.1 t.2 acc) (mapSt φ acc) by
    simpa [mapSt] using this []
  induction s with
  | nil => intro acc; rfl
  | cons t s ih =>
    intro acc
    rw [List.foldl_cons, ih, mapSt_addTo]
    rfl

theorem toVerma_mapSt_prune [DecidableEq A] (s : List (List ℕ × A)) :
    St.toVerma (c := c) (h := h) (mapSt φ (prune s)) = St.toVerma (mapSt φ s) := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    unfold prune
    rw [List.filter_cons]
    split_ifs with ht
    · simp only [mapSt, List.map_cons, St.toVerma_cons] at ih ⊢
      rw [← ih]
      rfl
    · simp only [decide_eq_true_eq, not_not] at ht
      simp only [mapSt, List.map_cons, St.toVerma_cons, ht, map_zero, zero_smul, zero_add]
      exact ih

theorem evalAff_map (c h : A) (x : Aff) : φ (evalAff c h x) = evalAff (φ c) (φ h) x := by
  simp only [evalAff, map_add, map_mul, RingHom.map_rat_algebraMap]

theorem mapSt_posActSt (f : ℕ) (c h : A) (k : ℤ) (s : List (List ℕ × A)) :
    mapSt φ (posActSt f c h k s) = posActSt f (φ c) (φ h) k (mapSt φ s) := by
  simp only [posActSt, mapSt, List.map_flatMap, List.flatMap_map, List.map_map]
  refine List.flatMap_congr fun t _ => ?_
  refine List.map_congr_left fun u _ => ?_
  simp [map_mul, evalAff_map]

theorem toVerma_posActSt (f : ℕ) (k : ℤ) (s : St R) :
    St.toVerma (c := c) (h := h) (posActSt f c h k s) = L k (St.toVerma s) := by
  induction s with
  | nil => simp [posActSt, St.toVerma_nil]
  | cons t s ih =>
    have e : posActSt f c h k (t :: s)
        = ((posActAff f k t.1).map fun u => (u.1, t.2 * evalAff c h u.2)) ++ posActSt f c h k s := by
      simp [posActSt]
    rw [e, St.toVerma_append, ih, St.toVerma_cons, map_add, map_smul, ← posActAff_spec f t.1 k,
      ← St.toVerma_map_smul, ofAff, List.map_map]
    rfl

/-- The engine computes `L_k` exactly. -/
theorem toVerma_actN [DecidableEq A] (f : ℕ) (c h : A) (k : ℤ) (s : List (List ℕ × A)) :
    St.toVerma (c := φ c) (h := φ h) (mapSt φ (actN f c h k s))
      = L k (St.toVerma (mapSt φ s)) := by
  rw [actN, toVerma_mapSt_prune, mapSt_collect, toVerma_collect, mapSt_posActSt,
    toVerma_posActSt]

theorem toVerma_negN [DecidableEq A] (f : ℕ) (c h : A) (w : List ℕ) (s : List (List ℕ × A)) :
    St.toVerma (c := φ c) (h := φ h) (mapSt φ (negN f c h w s))
      = (VirEnv.negOp (φ c) w) • St.toVerma (mapSt φ s) := by
  induction w with
  | nil => simp [negN, VirEnv.negOp]
  | cons y w ih =>
    have e : negN f c h (y :: w) s = actN f c h (-(y : ℤ)) (negN f c h w s) := rfl
    rw [e, toVerma_actN, ih, show VirEnv.negOp (φ c) (y :: w)
        = VirEnv.L (φ c) (-(y : ℤ)) * VirEnv.negOp (φ c) w by simp [VirEnv.negOp], mul_smul]
    rfl

theorem toVerma_posN [DecidableEq A] (f : ℕ) (c h : A) (Y : List ℕ) :
    ∀ s : List (List ℕ × A), St.toVerma (c := φ c) (h := φ h) (mapSt φ (posN f c h Y s))
      = (Y.reverse.map fun y => (L (y : ℤ) : Verma R (φ c) (φ h) →ₗ[R] _)).prod
          (St.toVerma (mapSt φ s)) := by
  induction Y with
  | nil => intro s; simp [posN]
  | cons y Y ih =>
    intro s
    have e : posN f c h (y :: Y) s = posN f c h Y (actN f c h (y : ℤ) s) := rfl
    rw [e, ih, toVerma_actN]
    simp [List.reverse_cons, List.map_append, List.prod_append, Module.End.mul_apply]

theorem toVerma_opN [DecidableEq A] (f : ℕ) (c h : A) (s t : List (List ℕ × A)) :
    St.toVerma (c := φ c) (h := φ h) (mapSt φ (opN f c h s t))
      = St.toOp (φ c) (mapSt φ s) • St.toVerma (mapSt φ t) := by
  rw [opN, toVerma_mapSt_prune, mapSt_collect, toVerma_collect]
  induction s with
  | nil => simp [mapSt, St.toOp, St.toVerma_nil]
  | cons u s ih =>
    rw [List.flatMap_cons, mapSt_append, St.toVerma_append, ih]
    have e : mapSt φ ((negN f c h u.1 t).map fun v => (v.1, u.2 * v.2))
        = (mapSt φ (negN f c h u.1 t)).map fun v => (v.1, φ u.2 * v.2) := by
      simp [mapSt, List.map_map, map_mul]
    rw [e, St.toVerma_map_smul, toVerma_negN]
    simp only [mapSt, List.map_cons, St.toOp, List.sum_cons, add_smul, smul_assoc]

end Semantics

end Virasoro
