import Virasoro.Proofs.Vacuum
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The functional `v ↦ ⟨h| V_d(1) |v⟩`

For a primary field of weight `d` the Ward identity and `⟨h| L_{-m} = 0` (`m > 0`) give
`⟨h|V_d(1) L_{-m} v⟩ = ⟨h|V_d(1) (L_0 + m d - h) v⟩`.  The functional
`φ(v) = ⟨h|V_d(1)|v⟩` with `φ(|h⟩) = 1` is constructed from the freeness of the Verma module
over `U(Vir_-)`: the functionals `p ↦ φ(p(L_0) v)` on polynomials `p` form a representation of
`Vir_-`, with `L_{-m}` acting by the transpose of `p ↦ (X - h + m d) p(X + m)`.
-/

namespace Virasoro

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The operator `p ↦ (X - h + n d) p(X + n)` on polynomials. -/
noncomputable def aOp (h d : R) (n : ℤ) : R[X] →ₗ[R] R[X] :=
  (LinearMap.mulLeft R (X - C h + C ((n : R) * d))) ∘ₗ taylor (n : R)

omit [Algebra ℚ R] in
theorem aOp_apply (h d : R) (n : ℤ) (p : R[X]) :
    aOp h d n p = (X - C h + C ((n : R) * d)) * taylor (n : R) p := rfl

omit [Algebra ℚ R] in
theorem aOp_comm (h d : R) (a b : ℤ) (p : R[X]) :
    aOp h d b (aOp h d a p)
      = aOp h d a (aOp h d b p) + ((b - a : ℤ) : R) • aOp h d (a + b) p := by
  simp only [aOp_apply, taylor_mul, map_add, map_sub, taylor_X, taylor_C, taylor_taylor]
  rw [show (b : R) + a = ((a + b : ℤ) : R) by push_cast; ring,
    show (a : R) + b = ((a + b : ℤ) : R) by push_cast; ring, smul_eq_C_mul]
  generalize taylor ((a + b : ℤ) : R) p = q
  push_cast
  simp only [map_add, map_sub, map_mul]
  ring

omit [Algebra ℚ R] in
theorem aOp_X_mul (h d : R) (n : ℤ) (p : R[X]) :
    aOp h d n (X * p) = X * aOp h d n p + (n : R) • aOp h d n p := by
  simp only [aOp_apply, taylor_mul, taylor_X, smul_eq_C_mul]
  ring

variable {c h : R} (d : R)

namespace Verma

omit [Algebra ℚ R] in
theorem aDual_comm (m n : ℤ) :
    (LinearMap.lcomp R R (aOp h d m) : Module.End R (R[X] →ₗ[R] R)) * LinearMap.lcomp R R (aOp h d n)
      = LinearMap.lcomp R R (aOp h d n) * LinearMap.lcomp R R (aOp h d m)
        + ((n - m : ℤ) : R) • LinearMap.lcomp R R (aOp h d (m + n)) := by
  refine LinearMap.ext fun ψ => LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply, LinearMap.lcomp_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  rw [aOp_comm h d m n p, map_add, map_smul]

variable (c h)

/-- The map `v ↦ (p ↦ ⟨h|V_d(1) p(L_0) v⟩)`. -/
noncomputable def PhiMap : Verma R c h →ₗ[R] (R[X] →ₗ[R] R) :=
  Classical.choose (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (aOp h d m) : Module.End R (R[X] →ₗ[R] R)))
    (fun m n _ _ => aDual_comm d m n) (leval h))

variable {c h}

theorem PhiMap_hw (p : R[X]) : PhiMap c h d hw p = p.eval h := by
  have := (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (aOp h d m) : Module.End R (R[X] →ₗ[R] R)))
    (fun m n _ _ => aDual_comm d m n) (leval h))).1
  rw [PhiMap, this]
  rfl

theorem PhiMap_neg {m : ℤ} (hm : 0 < m) (v : Verma R c h) (p : R[X]) :
    PhiMap c h d (L (-m) v) p = PhiMap c h d v (aOp h d m p) := by
  have := (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (aOp h d m) : Module.End R (R[X] →ₗ[R] R)))
    (fun m n _ _ => aDual_comm d m n) (leval h))).2 m hm v
  rw [PhiMap, this]
  rfl

/-- `⟨h|V_d(1) p(L_0) L_0 v⟩ = ⟨h|V_d(1) (X p)(L_0) v⟩`. -/
theorem PhiMap_L_zero (v : Verma R c h) : ∀ p : R[X],
    PhiMap c h d (L 0 v) p = PhiMap c h d v (X * p) := by
  refine induction_L (P := fun v => ∀ p : R[X],
    PhiMap c h d (L 0 v) p = PhiMap c h d v (X * p)) ?_ ?_ ?_ ?_ v
  · intro p
    rw [L_hw_zero, map_smul, LinearMap.smul_apply, PhiMap_hw, PhiMap_hw, eval_mul, eval_X,
      smul_eq_mul]
  · intro u v hu hv p
    simp only [map_add, LinearMap.add_apply, hu, hv]
  · intro r v hv p
    simp only [map_smul, LinearMap.smul_apply, hv]
  · intro m hm v hv p
    have e : L 0 (L (-m) v) = L (-m) (L 0 v) + (m : R) • L (-m) v := by
      have := L_L_zero (c := c) (h := h) (-m) v
      rw [this]
      push_cast
      module
    rw [e, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, PhiMap_neg d hm,
      PhiMap_neg d hm, PhiMap_neg d hm, hv, aOp_X_mul, map_add, map_smul]

variable (c h)

/-- The functional `φ(v) = ⟨h|V_d(1)|v⟩`. -/
noncomputable def phiVac : Verma R c h →ₗ[R] R :=
  (LinearMap.applyₗ (1 : R[X])) ∘ₗ PhiMap c h d

variable {c h}

theorem phiVac_apply (v : Verma R c h) : phiVac c h d v = PhiMap c h d v 1 := rfl

theorem phiVac_hw : phiVac c h d (hw : Verma R c h) = 1 := by
  rw [phiVac_apply, PhiMap_hw, eval_one]

/-- `φ(L_{-m} v) = φ(L_0 v) + (m d - h) φ(v)` for `m > 0`. -/
theorem phiVac_neg {m : ℤ} (hm : 0 < m) (v : Verma R c h) :
    phiVac c h d (L (-m) v) = phiVac c h d (L 0 v) + ((m : R) * d - h) * phiVac c h d v := by
  rw [phiVac_apply, phiVac_apply, phiVac_apply, PhiMap_neg d hm, PhiMap_L_zero, aOp_apply,
    taylor_one, map_one, mul_one, mul_one]
  have e : (X - C h + C ((m : R) * d) : R[X]) = X + ((m : R) * d - h) • (1 : R[X]) := by
    rw [smul_eq_C_mul, mul_one, map_sub]
    ring
  rw [e, map_add, map_smul, smul_eq_mul]

end Verma

end Virasoro
