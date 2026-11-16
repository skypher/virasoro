import Virasoro.Proofs.Shapovalov
import Virasoro.Proofs.Naturality

/-!
# Change of the coefficient ring

A ring homomorphism `f : R → S` with `f c = c'`, `f h = h'` induces an `f`-semilinear map
`M_R(c,h) → M_S(c',h')` of Verma modules that sends `L_{-w}|h⟩` to `L_{-w}|h'⟩` and commutes
with all modes; the Shapovalov forms correspond under `f`.
-/

namespace Virasoro

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)

/-- The `R`-algebra structure on `VirEnv S c'` through `f`. -/
@[reducible] noncomputable def VirEnv.algThrough (c' : S) : Algebra R (VirEnv S c') :=
  ((algebraMap S (VirEnv S c')).comp f).toAlgebra' fun r x => Algebra.commutes (f r) x

omit [Algebra ℚ R] in
theorem VirEnv.algThrough_smul (c' : S) (r : R) (x : VirEnv S c') :
    letI := VirEnv.algThrough f c'
    r • x = f r • x := by
  let _ := VirEnv.algThrough f c'
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

section

variable {c : R} {c' : S} (hc : f c = c')

/-- The ring homomorphism `VirEnv R c → VirEnv S c'` over `f`, sending `L n` to `L n`. -/
noncomputable def VirEnv.baseChange : VirEnv R c →+* VirEnv S c' :=
  letI := VirEnv.algThrough f c'
  (RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R (fun n : ℤ => VirEnv.L c' n), by
    intro x y hxy
    induction hxy with
    | comm m n =>
      simp only [map_mul, map_add, map_smul, FreeAlgebra.lift_ι_apply]
      rw [VirEnv.L_mul_L, VirEnv.algThrough_smul, map_intCast]
      congr 1
      split_ifs
      · rw [AlgHom.commutes]
        show _ = algebraMap S (VirEnv S c') (f (centralTerm c m))
        rw [map_centralTerm, hc]
      · rw [map_zero]⟩ : VirEnv R c →ₐ[R] VirEnv S c').toRingHom

theorem VirEnv.baseChange_L (n : ℤ) :
    VirEnv.baseChange f hc (VirEnv.L c n) = VirEnv.L c' n := by
  letI := VirEnv.algThrough f c'
  show (RingQuot.liftAlgHom R _) (RingQuot.mkAlgHom R _ (FreeAlgebra.ι R n)) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

theorem VirEnv.baseChange_smul (r : R) (x : VirEnv R c) :
    VirEnv.baseChange f hc (r • x) = f r • VirEnv.baseChange f hc x := by
  letI := VirEnv.algThrough f c'
  have h1 : ∀ (φ : VirEnv R c →ₐ[R] VirEnv S c'), φ (r • x) = r • φ x := fun φ => map_smul φ r x
  rw [← VirEnv.algThrough_smul f c' r]
  exact h1 _

theorem VirEnv.baseChange_algebraMap (r : R) :
    VirEnv.baseChange f hc (algebraMap R (VirEnv R c) r) = algebraMap S (VirEnv S c') (f r) := by
  rw [Algebra.algebraMap_eq_smul_one, VirEnv.baseChange_smul, map_one,
    Algebra.algebraMap_eq_smul_one]

variable {h : R} {h' : S} (hh : f h = h')

/-- The map `x ↦ f(x)|h'⟩` from `VirEnv R c` to the Verma module over `S`. -/
noncomputable def Verma.bcPre (h' : S) : VirEnv R c →ₛₗ[f] Verma S c' h' where
  toFun x := Verma.mk (VirEnv.baseChange f hc x)
  map_add' x y := by rw [map_add]; rfl
  map_smul' r x := by rw [VirEnv.baseChange_smul]; rfl

include hh in
theorem Verma.bcPre_ker :
    (hwIdeal R c h).restrictScalars R ≤ LinearMap.ker (Verma.bcPre f hc h') := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  rw [LinearMap.mem_ker]
  show Verma.mk (VirEnv.baseChange f hc x) = 0
  rw [Verma.mk, Submodule.Quotient.mk_eq_zero]
  refine Submodule.span_induction
    (p := fun x _ => VirEnv.baseChange f hc x ∈ hwIdeal S c' h') ?_ ?_ ?_ ?_ hx
  · rintro x (⟨n, hn, rfl⟩ | rfl)
    · rw [VirEnv.baseChange_L]
      exact Submodule.subset_span (Or.inl ⟨n, hn, rfl⟩)
    · rw [map_sub, VirEnv.baseChange_L, VirEnv.baseChange_algebraMap, hh]
      exact Submodule.subset_span (Or.inr rfl)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [smul_eq_mul, map_mul]
    exact Submodule.smul_mem _ _ hx

/-- The change of coefficient ring `M_R(c,h) → M_S(c',h')` over `f`. -/
noncomputable def Verma.baseChange : Verma R c h →ₛₗ[f] Verma S c' h' :=
  (Submodule.liftQ ((hwIdeal R c h).restrictScalars R) (Verma.bcPre f hc h')
      (Verma.bcPre_ker f hc hh)).comp
    (Submodule.Quotient.restrictScalarsEquiv R (hwIdeal R c h)).symm.toLinearMap

theorem Verma.baseChange_mk (x : VirEnv R c) :
    Verma.baseChange f hc hh (Verma.mk x) = Verma.mk (VirEnv.baseChange f hc x) := by
  show (Submodule.liftQ ((hwIdeal R c h).restrictScalars R) (Verma.bcPre f hc h')
      (Verma.bcPre_ker f hc hh))
    ((Submodule.Quotient.restrictScalarsEquiv R (hwIdeal R c h)).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  rfl

theorem Verma.baseChange_hw : Verma.baseChange f hc hh Verma.hw = Verma.hw := by
  rw [Verma.hw_eq, Verma.baseChange_mk, map_one, Verma.hw_eq]

theorem Verma.baseChange_L (n : ℤ) (v : Verma R c h) :
    Verma.baseChange f hc hh (Verma.L n v) = Verma.L n (Verma.baseChange f hc hh v) := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [Verma.L_mk]
    show Verma.baseChange f hc hh (Verma.mk _) = Verma.L n (Verma.baseChange f hc hh (Verma.mk x))
    rw [Verma.baseChange_mk, Verma.baseChange_mk, map_mul, VirEnv.baseChange_L, Verma.L_mk]

theorem Verma.baseChange_neg (w : List ℕ) :
    Verma.baseChange f hc hh (Verma.neg w) = Verma.neg w := by
  induction w with
  | nil => rw [Verma.neg_nil, Verma.baseChange_hw, Verma.neg_nil]
  | cons y w ih => rw [Verma.neg_cons, Verma.baseChange_L, ih, Verma.neg_cons]

theorem Verma.baseChange_pbwCoord (N : ℕ) (v : Nat.Partition N → R) :
    Verma.baseChange f hc hh (Verma.pbwCoord N v) = Verma.pbwCoord N fun Y => f (v Y) := by
  simp only [Verma.pbwCoord, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, map_sum, LinearMap.map_smulₛₗ, Verma.baseChange_neg]

/-- The Shapovalov forms correspond under the change of coefficient ring. -/
theorem Verma.shap_baseChange (u v : Verma R c h) :
    Verma.shap c' h' (Verma.baseChange f hc hh u) (Verma.baseChange f hc hh v)
      = f (Verma.shap c h u v) := by
  refine Verma.induction_neg (P := fun u => ∀ v : Verma R c h,
    Verma.shap c' h' (Verma.baseChange f hc hh u) (Verma.baseChange f hc hh v)
      = f (Verma.shap c h u v)) ?_ ?_ ?_ u v
  · intro Y _ v
    refine Verma.induction_neg (P := fun v =>
      Verma.shap c' h' (Verma.baseChange f hc hh (Verma.neg Y)) (Verma.baseChange f hc hh v)
        = f (Verma.shap c h (Verma.neg Y) v)) ?_ ?_ ?_ v
    · intro w hw
      rw [Verma.baseChange_neg, Verma.baseChange_neg,
        Verma.isShapovalov_shap.gramWord Y w hw, Verma.isShapovalov_shap.gramWord Y w hw,
        ← hc, ← hh, gramWord_map]
    · intro a b ha hb
      simp only [map_add, ha, hb]
    · intro r a ha
      simp only [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, ha]
  · intro a b ha hb v
    simp only [map_add, LinearMap.add_apply, ha, hb]
  · intro r a ha v
    simp only [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, ha]

end

end Virasoro
