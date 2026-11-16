import Virasoro.Proofs.VermaFree
import Virasoro.Proofs.VermaSpan

/-!
# The vacuum functional and the Shapovalov matrix (paper Definition 2.2)

The Verma module has exactly one vacuum functional `⟨h|`, and the matrix elements
`⟨h| L_Y L_{-Y'} |h⟩` are computed by the normal-ordering procedure `gramWord`.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

/-- Existence of the vacuum functional. -/
theorem exists_vacuum : ∃ ε : Verma R c h →ₗ[R] R, IsVacuumFunctional ε := by
  obtain ⟨Φ, h1, h2⟩ := exists_negHom (c := c) (h := h) (W := R) (fun _ => 0)
    (by intro m n _ _; simp) (1 : R)
  refine ⟨Φ, h1, ?_⟩
  intro n hn v
  have := h2 (-n) (by omega) v
  rw [neg_neg] at this
  rw [this]
  rfl

theorem vacuum_neg {ε : Verma R c h →ₗ[R] R} (hε : IsVacuumFunctional ε) (w : List ℕ)
    (hw : PosWord w) : ε (neg w) = if w = [] then 1 else 0 := by
  cases w with
  | nil => rw [neg_nil, hε.1, if_pos rfl]
  | cons y w =>
    rw [neg_cons, if_neg (by simp)]
    have hy : 0 < y := hw y List.mem_cons_self
    exact hε.2 _ (by omega) _

/-- Uniqueness of the vacuum functional. -/
theorem vacuum_unique {ε ε' : Verma R c h →ₗ[R] R} (hε : IsVacuumFunctional ε)
    (hε' : IsVacuumFunctional ε') : ε = ε' :=
  linearMap_ext fun w hw => by rw [vacuum_neg hε w hw, vacuum_neg hε' w hw]

/-- The vacuum functional reads off the coefficient of the empty word. -/
theorem vacuum_toVerma {ε : Verma R c h →ₗ[R] R} (hε : IsVacuumFunctional ε) {s : St R}
    (hs : PosSt s) : ε (St.toVerma s) = vac s := by
  induction s with
  | nil => simp [St.toVerma_nil, vac]
  | cons t s ih =>
    have ht : PosWord t.1 := hs t List.mem_cons_self
    have hs' : PosSt s := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    have e : vac (t :: s) = (if t.1.isEmpty then t.2 else 0) + vac s := by simp [vac]
    rw [St.toVerma_cons, map_add, map_smul, ih hs', vacuum_neg hε _ ht, e]
    congr 1
    by_cases h0 : t.1 = []
    · rw [if_pos h0, if_pos (by rw [h0]; rfl), smul_eq_mul, mul_one]
    · rw [if_neg h0, if_neg (by simpa using h0), smul_zero]

/-- `L_Y v = L_{y_ℓ} ⋯ L_{y₁} v`. -/
theorem posOp_smul (w : List ℕ) : ∀ v : Verma R c h,
    VirEnv.posOp c w • v = w.foldl (fun v (y : ℕ) => L (y : ℤ) v) v := by
  induction w with
  | nil =>
    intro v
    simp [VirEnv.posOp]
  | cons y w ih =>
    intro v
    have e : VirEnv.posOp c (y :: w) = VirEnv.posOp c w * VirEnv.L c (y : ℤ) := by
      simp [VirEnv.posOp]
    rw [e, mul_smul, ih, List.foldl_cons]
    rfl

theorem toVerma_foldl_actSt (Y : List ℕ) : ∀ s : St R,
    St.toVerma (c := c) (h := h) (Y.foldl (fun (s : St R) (y : ℕ) => actSt c h (y : ℤ) s) s)
      = Y.foldl (fun v (y : ℕ) => L (y : ℤ) v) (St.toVerma s) := by
  induction Y with
  | nil => intro s; rfl
  | cons y Y ih =>
    intro s
    rw [List.foldl_cons, List.foldl_cons, ih, St.toVerma_actSt]

theorem posSt_foldl_actSt (Y : List ℕ) : ∀ s : St R, PosSt s →
    PosSt (Y.foldl (fun (s : St R) (y : ℕ) => actSt c h (y : ℤ) s) s) := by
  induction Y with
  | nil => intro s hs; exact hs
  | cons y Y ih =>
    intro s hs
    rw [List.foldl_cons]
    exact ih _ (posSt_actSt c h _ hs)

/-- The matrix elements `⟨h| L_Y L_{-Y'} |h⟩` are computed by normal ordering. -/
theorem vacuum_gramWord {ε : Verma R c h →ₗ[R] R} (hε : IsVacuumFunctional ε) (Y Y' : List ℕ)
    (hY' : PosWord Y') : ε (VirEnv.posOp c Y • neg Y') = gramWord c h Y Y' := by
  have hs : PosSt ([(Y', 1)] : St R) := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact hY'
  rw [posOp_smul, gramWord, ← vacuum_toVerma hε (posSt_foldl_actSt Y _ hs), toVerma_foldl_actSt,
    St.toVerma_single, one_smul]

end Verma

end Virasoro
