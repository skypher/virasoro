import Virasoro.Proofs.Vacuum
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The Shapovalov form

The Verma module carries exactly one contravariant bilinear form with `⟨h|h⟩ = 1`.  It is
symmetric, and its matrix elements on the vectors `L_{-Y}|h⟩` are the entries of the matrices
`gram`.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

variable (c h)

/-- The vacuum functional `⟨h|`. -/
noncomputable def vacuum : Verma R c h →ₗ[R] R := Classical.choose exists_vacuum

variable {c h}

theorem isVacuum_vacuum : IsVacuumFunctional (vacuum c h) := Classical.choose_spec exists_vacuum

theorem vacuum_L_zero {ε : Verma R c h →ₗ[R] R} (hε : IsVacuumFunctional ε) (v : Verma R c h) :
    ε (L 0 v) = h * ε v := by
  refine induction_neg (P := fun v => ε (L 0 v) = h * ε v) ?_ ?_ ?_ v
  · intro w hw
    rw [L_zero_neg, map_smul, vacuum_neg hε w hw, smul_eq_mul]
    by_cases h0 : w = []
    · rw [h0]; simp
    · rw [if_neg h0, mul_zero, mul_zero]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add, mul_add]
  · intro r v hv
    rw [map_smul, map_smul, hv, map_smul, smul_eq_mul, smul_eq_mul]
    ring

theorem dualL_comm (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    (LinearMap.lcomp R R (L (c := c) (h := h) m) : Module.End R (Verma R c h →ₗ[R] R))
        * LinearMap.lcomp R R (L n)
      = LinearMap.lcomp R R (L n) * LinearMap.lcomp R R (L m)
        + ((n - m : ℤ) : R) • LinearMap.lcomp R R (L (m + n)) := by
  refine LinearMap.ext fun ψ => LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply, LinearMap.lcomp_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  rw [L_L_ct m n v, ct, if_neg (by omega), zero_smul, add_zero, map_add, map_smul]

variable (c h)

/-- The Shapovalov form `⟨u, v⟩`. -/
noncomputable def shap : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R :=
  Classical.choose (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (L (c := c) (h := h) m) :
      Module.End R (Verma R c h →ₗ[R] R)))
    dualL_comm (vacuum c h))

variable {c h}

theorem shap_hw : shap c h hw = vacuum c h :=
  (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (L (c := c) (h := h) m) :
      Module.End R (Verma R c h →ₗ[R] R)))
    dualL_comm (vacuum c h))).1

theorem shap_neg {m : ℤ} (hm : 0 < m) (u v : Verma R c h) :
    shap c h (L (-m) u) v = shap c h u (L m v) := by
  have := (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (L (c := c) (h := h) m) :
      Module.End R (Verma R c h →ₗ[R] R)))
    dualL_comm (vacuum c h))).2 m hm u
  rw [shap, this]
  rfl

/-- Contravariance of the Shapovalov form for all modes. -/
theorem shap_L (u : Verma R c h) : ∀ (n : ℤ) (v : Verma R c h),
    shap c h (L n u) v = shap c h u (L (-n) v) := by
  refine induction_L (P := fun u => ∀ (n : ℤ) (v : Verma R c h),
    shap c h (L n u) v = shap c h u (L (-n) v)) ?_ ?_ ?_ ?_ u
  · intro n v
    by_cases hn : n < 0
    · have := shap_neg (c := c) (h := h) (show 0 < -n by omega) hw v
      rwa [neg_neg] at this
    · by_cases h0 : n = 0
      · subst h0
        rw [neg_zero, L_hw_zero, map_smul, LinearMap.smul_apply, shap_hw,
          vacuum_L_zero isVacuum_vacuum, smul_eq_mul]
      · rw [L_hw_pos (by omega), map_zero, LinearMap.zero_apply, shap_hw,
          isVacuum_vacuum.2 (-n) (by omega)]
  · intro u v hu hv n w
    simp only [map_add, LinearMap.add_apply, hu, hv]
  · intro r v hv n w
    simp only [map_smul, LinearMap.smul_apply, hv]
  · intro k hk u hu n v
    have e1 := L_L_ct (c := c) (h := h) (-k) n u
    have e2 := L_L_ct (c := c) (h := h) (-n) k v
    rw [neg_neg] at e1 e2
    rw [e1, map_add, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, shap_neg hk, hu n, hu (-k + n), shap_neg hk,
      e2, map_add, map_add, map_smul, map_smul, ct_symm c n k,
      show -(-k + n) = -n + k by ring]
    push_cast
    ring

/-- Existence of the Shapovalov form. -/
theorem isShapovalov_shap : IsShapovalov (shap c h) := by
  refine ⟨?_, fun n u v => shap_L u n v⟩
  rw [shap_hw]
  exact isVacuum_vacuum.1

/-- A Shapovalov form restricts to the vacuum functional on `|h⟩`. -/
theorem IsShapovalov.isVacuum {B : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hB : IsShapovalov B) :
    IsVacuumFunctional (B hw) := by
  refine ⟨hB.1, fun n hn v => ?_⟩
  have := hB.2 (-n) hw v
  rw [neg_neg, L_hw_pos (by omega), map_zero, LinearMap.zero_apply] at this
  exact this.symm

/-- Uniqueness of the Shapovalov form. -/
theorem shapovalov_unique {B B' : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hB : IsShapovalov B)
    (hB' : IsShapovalov B') : B = B' := by
  refine LinearMap.ext fun u => ?_
  refine induction_L (P := fun u => B u = B' u) ?_ ?_ ?_ ?_ u
  · exact vacuum_unique hB.isVacuum hB'.isVacuum
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
  · intro r v hv
    rw [map_smul, map_smul, hv]
  · intro m _ u hu
    refine LinearMap.ext fun v => ?_
    rw [hB.2, hB'.2, hu]

/-- The Shapovalov form is symmetric. -/
theorem IsShapovalov.symm {B : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hB : IsShapovalov B)
    (u v : Verma R c h) : B u v = B v u := by
  have hflip : IsShapovalov B.flip := by
    refine ⟨hB.1, fun n u v => ?_⟩
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    have := hB.2 (-n) v u
    rw [neg_neg] at this
    exact this.symm
  have := shapovalov_unique hflip hB
  exact LinearMap.congr_fun (LinearMap.congr_fun this v) u

/-- `⟨L_{-Y}|h⟩, v⟩ = ⟨h| L_Y v`. -/
theorem IsShapovalov.neg_left {B : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hB : IsShapovalov B)
    (Y : List ℕ) : ∀ v : Verma R c h, B (neg Y) v = B hw (VirEnv.posOp c Y • v) := by
  induction Y with
  | nil =>
    intro v
    rw [neg_nil, posOp_smul]
    rfl
  | cons y Y ih =>
    intro v
    rw [neg_cons, hB.2, neg_neg, ih, posOp_smul, posOp_smul, List.foldl_cons]

/-- The matrix elements of a Shapovalov form are computed by normal ordering. -/
theorem IsShapovalov.gramWord {B : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hB : IsShapovalov B)
    (Y Y' : List ℕ) (hY' : PosWord Y') : B (neg Y) (neg Y') = gramWord c h Y Y' := by
  rw [hB.neg_left, vacuum_gramWord hB.isVacuum Y Y' hY']

end Verma

/-- `gramWord` is symmetric on words of positive integers. -/
theorem gramWord_symm (c h : R) {Y Y' : List ℕ} (hY : PosWord Y) (hY' : PosWord Y') :
    gramWord c h Y Y' = gramWord c h Y' Y := by
  have hB := Verma.isShapovalov_shap (c := c) (h := h)
  rw [← hB.gramWord Y Y' hY', ← hB.gramWord Y' Y hY, hB.symm]

end Virasoro
