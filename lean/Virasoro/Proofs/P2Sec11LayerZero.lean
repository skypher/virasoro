import Virasoro.Proofs.P2Sec11LayerIdent
import Virasoro.Proofs.P2Sec9IrrTrace

/-!
# Proposition 11.2(ii): the layer `i = 0` (paper.tex l.2486)

"For `i = 0`, `J⁰/J¹ = L(c⋆,μ)` gives `T^irr_N(c⋆,μ,d)`": `J⁰_N` is the whole level, `J¹_N` is
`ker G_N(c⋆,μ)`, `B^{(0)}` is the Shapovalov form and `ρ^{(0)} = ρ_{c⋆,μ,d}`, so a layer trace of
the layer `0` is an irreducible trace.
-/

namespace Virasoro

open Polynomial Verma

variable {c μ d : ℂ}

theorem jantzenLayer_zero (N : ℕ) : jantzenLayer c μ N 0 = ⊤ := by
  rw [eq_top_iff]
  intro v _
  exact ⟨fun Y => C (v Y), fun Y => eval_C, fun Y => by rw [pow_zero]; exact one_dvd _⟩

theorem jantzenLayer_one (N : ℕ) :
    jantzenLayer c μ N 1 = LinearMap.ker (gram c μ N).mulVecLin := by
  ext v
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨w, hw0, hdvd⟩
    funext Y
    have h1 := hdvd Y
    rw [pow_one, X_dvd_iff, coeff_zero_eq_eval_zero, eval_mulVec_gramShift] at h1
    have e : (fun Z => (w Z).eval 0) = v := funext hw0
    rw [e] at h1
    exact h1
  · intro hv
    refine ⟨fun Y => C (v Y), fun Y => eval_C, fun Y => ?_⟩
    rw [pow_one, X_dvd_iff, coeff_zero_eq_eval_zero, eval_mulVec_gramShift]
    have e : (fun Z => (C (v Z) : ℂ[X]).eval 0) = v := funext fun Z => eval_C
    rw [e, hv]
    rfl

/-- `B^{(0)}` is the Shapovalov form. -/
theorem jform_zero (N : ℕ) (u v : Nat.Partition N → ℂ) :
    jform c μ N 0 u v = gramForm c μ N u v := by
  have hu : IsJFamily c μ N 0 u fun Y => C (u Y) :=
    ⟨fun Y => eval_C, fun Y => by rw [pow_zero]; exact one_dvd _⟩
  have hv : IsJFamily c μ N 0 v fun Y => C (v Y) :=
    ⟨fun Y => eval_C, fun Y => by rw [pow_zero]; exact one_dvd _⟩
  rw [← jformFam_eq_jform c μ hu hv, jformFam, coeff_zero_eq_eval_zero, gramForm,
    form_symm (gram_transpose c μ N)]
  have h1 := RingHom.map_dotProduct (evalRingHom (0 : ℂ)) (fun Y => C (v Y))
    ((gramShift c μ N).mulVec fun Y => C (u Y))
  simp only [coe_evalRingHom] at h1
  rw [h1]
  congr 1
  · exact funext fun Y => eval_C
  · funext Y
    show eval 0 ((gramShift c μ N).mulVec (fun Y => C (u Y)) Y) = _
    rw [eval_mulVec_gramShift]
    congr 1
    exact funext fun Z => eval_C

/-- `ρ^{(0)} = ρ_{c,μ,d}` (l.2412). -/
theorem vform_zero (HV : VertexPartI c μ d) (N : ℕ) (u v : Nat.Partition N → ℂ) :
    vform c μ d N 0 u v = torusForm c μ d N u v := by
  have hu : IsJFamily c μ N 0 u fun Y => C (u Y) :=
    ⟨fun Y => eval_C, fun Y => by rw [pow_zero]; exact one_dvd _⟩
  have hv : IsJFamily c μ N 0 v fun Y => C (v Y) :=
    ⟨fun Y => eval_C, fun Y => by rw [pow_zero]; exact one_dvd _⟩
  have hT := isPrimaryPairing_pairing (c := C c) (h := C μ + (X : ℂ[X])) (C d)
  have hT₀ := isPrimaryPairing_pairing (c := c) (h := μ) d
  have h1 := (vform_fam HV hu hv).2
  have h2 : pairing (C c) (C μ + X) (C d) (pbwCoord N fun Y => C (u Y))
      (pbwCoord N fun Y => C (v Y)) =
        (fun Y => C (u Y)) ⬝ᵥ (torusShift c μ d N).mulVec fun Y => C (v Y) :=
    primary_pbwCoord hT N _ _
  rw [← h1, ← h2, primary_coeff_zero hT hT₀ hu.1 hv.1, primary_pbwCoord hT₀]

/-- `ρ(c,μ,d)` descends to `L(c,μ)` when `J¹(c,μ) ⊂ rad ρ_{c,μ,d}`. -/
theorem torusDescends_of_radical
    (hrad : ∀ T : Verma ℂ c μ →ₗ[ℂ] Verma ℂ c μ →ₗ[ℂ] ℂ, IsPrimaryPairing d T →
      ∀ u ∈ jantzen c μ 1, ∀ v, T u v = 0 ∧ T v u = 0) : TorusDescends c μ d := by
  intro T hT B hB u hu v
  have hBs : B = shap c μ := shapovalov_unique hB isShapovalov_shap
  have hmem : u ∈ jantzen c μ 1 := by
    have h := jantzen_one_eq_radical c μ
    rw [← SetLike.mem_coe, h]
    intro x
    rw [← hBs]
    exact hu x
  exact hrad T hT u hmem v

/-- A layer trace of the layer `0` is an irreducible trace. -/
theorem isIrrTrace_of_layer_zero (HV : VertexPartI c μ d) {N : ℕ} {t : ℂ}
    (ht : IsLayerTrace c μ d N 0 t) : IsIrrTrace c μ d N t := by
  classical
  obtain ⟨κ, _, _, E, -, hLI, hdisj, hsup, hdet, rfl⟩ := ht
  rw [jantzenLayer_one] at hdisj hsup
  rw [jantzenLayer_zero] at hsup
  have hA : (Matrix.of fun a b => jform c μ N 0 (E a) (E b)) =
      Matrix.of fun a b => gramForm c μ N (E a) (E b) := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.of_apply, Matrix.of_apply, jform_zero]
  rw [hA] at hdet
  let eqv := Fintype.equivFin κ
  have hrange : Set.range (fun i => E (eqv.symm i)) = Set.range E :=
    eqv.symm.surjective.range_comp E
  have hsub : (Matrix.of fun i j => gramForm c μ N (E (eqv.symm i)) (E (eqv.symm j))) =
      (Matrix.of fun a b => gramForm c μ N (E a) (E b)).submatrix eqv.symm eqv.symm := rfl
  refine ⟨Fintype.card κ, fun i => E (eqv.symm i), hLI.comp _ eqv.symm.injective, ?_, ?_, ?_⟩
  · rw [hrange]
    exact ⟨hdisj, codisjoint_iff.2 hsup⟩
  · rw [hsub, Matrix.det_submatrix_equiv_self]
    exact hdet
  · rw [hsub, Matrix.inv_submatrix_equiv, hA]
    simp only [Matrix.submatrix_apply, vform_zero HV]
    rw [← Equiv.sum_comp eqv.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp eqv.symm]

/-- `Stmt_sub_vertex_layer_zero` (paper.tex l.2486). -/
theorem sub_vertex_layer_zero (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_layer_zero := by
  intro p p' r s b hset ε k₀ k m hk hm c μ d N t T₀ ht hT
  have HV : VertexPartI c μ d := fun i N₁ N₂ a a₂ wa wb ha hb =>
    vertex_part_i hJ hH hU hF hI p p' r s b hset ε k₀ k m hk hm _
      (Verma.isPrimaryPairing_pairing _) i N₁ N₂ a a₂ wa wb ha hb
  have hd : TorusDescends c μ d := torusDescends_of_radical fun T hT' =>
    sub_vertex_radical_zero hJ hH hU hF p p' r s b hset ε k₀ k m hk hm T hT'
  exact (irrTrace_existsUnique hd N).unique (isIrrTrace_of_layer_zero HV ht) hT

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_layer_zero := sub_vertex_layer_zero hJ hH hU hF hI

end Virasoro
