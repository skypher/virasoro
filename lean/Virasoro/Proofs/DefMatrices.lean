import Virasoro.Proofs.PairingConstr
import Virasoro.Proofs.GramDet
import Virasoro.Statements.Sec2

/-!
# Well-posedness of Definition 2.2

Uniqueness of the primary pairing, the identification of its matrix elements with the
normal-ordering procedure `torusWord`, and the proof of `Stmt_def_matrices`.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h d : R}

namespace Verma

variable {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R}

/-- `⟨h|V_d(1) L_{-m} w⟩ = (|w| + m d) ⟨h|V_d(1) w⟩`. -/
theorem primary_hw_neg (hT : IsPrimaryPairing d T) (w : List ℕ) (hw : PosWord w) :
    T Verma.hw (neg w) = phi d w := by
  induction w with
  | nil => rw [neg_nil, hT.1]; rfl
  | cons m w ih =>
    have hm : 0 < m := hw m List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have e := hT.2 (-(m : ℤ)) Verma.hw (neg w)
    rw [neg_neg, L_hw_pos (by omega), L_hw_zero, L_zero_neg, map_zero, LinearMap.zero_apply,
      map_smul, map_smul, LinearMap.smul_apply, ← neg_cons, ih hw'] at e
    rw [phi]
    simp only [smul_eq_mul, Int.cast_neg, Int.cast_natCast] at e
    linear_combination -e

theorem primary_toVerma (T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R) (u : Verma R c h)
    (s : St R) : T u (St.toVerma s) = (s.map fun t => t.2 * T u (neg t.1)).sum := by
  induction s with
  | nil => rw [St.toVerma_nil, map_zero]; rfl
  | cons t s ih =>
    rw [St.toVerma_cons, map_add, map_smul, ih, List.map_cons, List.sum_cons, smul_eq_mul]

/-- The matrix elements of a primary pairing are computed by the Ward identity. -/
theorem primary_torusWord (hT : IsPrimaryPairing d T) : ∀ Y : List ℕ, PosWord Y →
    ∀ w : List ℕ, PosWord w → T (neg Y) (neg w) = torusWord c h d Y w := by
  intro Y
  induction Y with
  | nil =>
    intro _ w hw
    rw [neg_nil, primary_hw_neg hT w hw, torusWord]
  | cons y Y ih =>
    intro hY w hw
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    have e := hT.2 (y : ℤ) (neg Y) (neg w)
    rw [← neg_cons, L_neg_actWord w (y : ℤ), L_zero_neg, L_zero_neg, map_smul, map_smul,
      LinearMap.smul_apply, primary_toVerma, ih hY' w hw] at e
    have e2 : ((actWord c h (y : ℤ) w).map fun t => t.2 * T (neg Y) (neg t.1))
        = (actWord c h (y : ℤ) w).map fun t => t.2 * torusWord c h d Y t.1 := by
      refine List.map_congr_left fun t ht => ?_
      rw [ih hY' t.1 (posSt_actWord c h hw (y : ℤ) t ht)]
    rw [e2] at e
    rw [torusWord]
    simp only [smul_eq_mul, Int.cast_natCast] at e
    linear_combination e

/-- Uniqueness of the primary pairing. -/
theorem primary_unique {T' : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R}
    (hT : IsPrimaryPairing d T) (hT' : IsPrimaryPairing d T') : T = T' :=
  linearMap_ext fun Y hY => linearMap_ext fun w hw => by
    rw [primary_torusWord hT Y hY w hw, primary_torusWord hT' Y hY w hw]

end Verma

/-- The Verma module has exactly one vacuum functional and, for every weight `d`, exactly one
primary pairing; `gram` and `torus` are their matrix elements on the vectors `L_{-Y}|h⟩`.

Paper label: def:matrices -/
theorem def_matrices : Stmt_def_matrices := by
  intro R _ _ c h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := Verma.exists_vacuum (c := c) (h := h)
    exact ⟨ε, hε, fun ε' hε' => Verma.vacuum_unique hε' hε⟩
  · intro ε hε N Y Y'
    rw [Verma.vacuum_gramWord hε _ _ (word_pos Y')]
    rfl
  · intro d
    exact ⟨Verma.pairing c h d, Verma.isPrimaryPairing_pairing d,
      fun T hT => Verma.primary_unique hT (Verma.isPrimaryPairing_pairing d)⟩
  · intro d T hT N Y Y'
    rw [Verma.primary_torusWord hT _ (word_pos Y) _ (word_pos Y')]
    rfl

example : Stmt_def_matrices := def_matrices

end Virasoro
