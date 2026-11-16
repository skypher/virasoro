import Virasoro.Proofs.Induced
import Virasoro.Proofs.VermaBasic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The Verma module is free over `U(Vir_-)`

The Virasoro action on `U(Vir_-)` gives a linear map `Verma R c h → U(Vir_-)` sending `|h⟩` to
`1` and intertwining all modes.  Consequently every representation of `Vir_-` receives, for each
of its vectors `w₀`, a linear map from the Verma module sending `|h⟩` to `w₀` and intertwining
the negative modes.
-/

namespace Virasoro

open NegEnv

variable {R : Type*} [CommRing R] [Algebra ℚ R] (c h : R)

/-- The representation of the Virasoro algebra on `U(Vir_-)`. -/
noncomputable def rhoNeg : VirEnv R c →ₐ[R] Module.End R (NegEnv R) :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R (Lop c h), by
    intro x y hxy
    induction hxy with
    | comm m n =>
      simp only [map_mul, map_add, map_smul, FreeAlgebra.lift_ι_apply]
      refine LinearMap.ext fun u => ?_
      rw [Module.End.mul_apply, Lop_comm c h m n u]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply]
      congr 1
      split_ifs
      · rw [AlgHom.commutes, Module.algebraMap_end_apply]
      · rw [map_zero, LinearMap.zero_apply]⟩

theorem rhoNeg_L (n : ℤ) : rhoNeg c h (VirEnv.L c n) = Lop c h n := by
  rw [rhoNeg, VirEnv.L, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

theorem rhoNeg_hwIdeal (x : VirEnv R c) (hx : x ∈ hwIdeal R c h) : rhoNeg c h x 1 = 0 := by
  refine Submodule.span_induction (p := fun x _ => rhoNeg c h x 1 = 0) ?_ ?_ ?_ ?_ hx
  · rintro x (⟨n, hn, rfl⟩ | rfl)
    · rw [rhoNeg_L, Lop_one_nonneg c h hn.le, if_neg hn.ne', zero_smul]
    · rw [map_sub, rhoNeg_L, AlgHom.commutes, LinearMap.sub_apply,
        Lop_one_nonneg c h le_rfl, if_pos rfl, Module.algebraMap_end_apply, sub_self]
  · rw [map_zero, LinearMap.zero_apply]
  · intro x y _ _ hx hy
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  · intro a x _ hx
    rw [smul_eq_mul, map_mul, Module.End.mul_apply, hx, map_zero]

theorem rhoNeg_ker : (hwIdeal R c h).restrictScalars R ≤
    LinearMap.ker ((LinearMap.applyₗ (1 : NegEnv R)) ∘ₗ (rhoNeg c h).toLinearMap) := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  rw [LinearMap.mem_ker]
  exact rhoNeg_hwIdeal c h x hx

/-- The map `Verma R c h → U(Vir_-)`, `x |h⟩ ↦ x • 1`. -/
noncomputable def toNeg : Verma R c h →ₗ[R] NegEnv R :=
  (Submodule.liftQ ((hwIdeal R c h).restrictScalars R)
      ((LinearMap.applyₗ (1 : NegEnv R)) ∘ₗ (rhoNeg c h).toLinearMap) (rhoNeg_ker c h)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (hwIdeal R c h)).symm.toLinearMap

theorem toNeg_mk (x : VirEnv R c) : toNeg c h (Verma.mk x) = rhoNeg c h x 1 := by
  rw [toNeg, LinearMap.comp_apply]
  show (Submodule.liftQ _ _ _) ((Submodule.Quotient.restrictScalarsEquiv R (hwIdeal R c h)).symm
    (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  rfl

theorem toNeg_hw : toNeg c h Verma.hw = 1 := by
  have h1 : rhoNeg c h 1 = 1 := map_one _
  rw [Verma.hw_eq, toNeg_mk, h1]
  rfl

theorem toNeg_L (n : ℤ) (v : Verma R c h) :
    toNeg c h (Verma.L n v) = Lop c h n (toNeg c h v) := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [Verma.L_mk, toNeg_mk, map_mul, Module.End.mul_apply, rhoNeg_L]
    rfl

variable {c h}

/-- Freeness of the Verma module over `U(Vir_-)`: operators `B m` (`m > 0`) with
`B m B n = B n B m + (n - m) B (m + n)` and a vector `w₀` determine a linear map `Φ` from the
Verma module with `Φ |h⟩ = w₀` and `Φ L_{-m} = B m Φ`. -/
theorem Verma.exists_negHom {W : Type*} [AddCommGroup W] [Module R W] (B : ℤ → Module.End R W)
    (hB : ∀ m n : ℤ, 0 < m → 0 < n → B m * B n = B n * B m + ((n - m : ℤ) : R) • B (m + n))
    (w₀ : W) :
    ∃ Φ : Verma R c h →ₗ[R] W, Φ Verma.hw = w₀ ∧
      ∀ m : ℤ, 0 < m → ∀ v, Φ (Verma.L (-m) v) = B m (Φ v) := by
  have hA : IsNegRep (fun m : ℤ => if 0 < m then B m else 0) := by
    constructor
    · intro m hm
      show (if 0 < m then B m else 0) = 0
      rw [if_neg (by omega)]
    · intro m n hm hn
      show (if 0 < m then B m else 0) * (if 0 < n then B n else 0)
        = (if 0 < n then B n else 0) * (if 0 < m then B m else 0)
          + ((n - m : ℤ) : R) • (if 0 < m + n then B (m + n) else 0)
      rw [if_pos hm, if_pos hn, if_pos (by omega)]
      exact hB m n hm hn
  refine ⟨orbit _ hA w₀ ∘ₗ toNeg c h, ?_, ?_⟩
  · rw [LinearMap.comp_apply, toNeg_hw, orbit_one]
  · intro m hm v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, toNeg_L, Lop_neg c h _ (-m) (by omega),
      neg_neg, orbit_g_mul]
    show (if 0 < m then B m else 0) _ = _
    rw [if_pos hm]

end Virasoro
