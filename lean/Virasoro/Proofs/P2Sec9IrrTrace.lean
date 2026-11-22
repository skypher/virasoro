import Virasoro.Proofs.P2Sec9Main
import Virasoro.Proofs.SingularPull
import Virasoro.Proofs.PBWSpan
import Virasoro.Proofs.Family
import Virasoro.Proofs.TorusAtZero
import Virasoro.Proofs.PairingConstr
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Theorem 9.1(i): the irreducible trace is well-defined (paper.tex l.1857–1858)

When `ρ(c⋆,λ,d)` descends to `L(c⋆,λ) × L(c⋆,λ)`, the operator induced by `V_d(1)` on
`L(c⋆,λ)_N = M(c⋆,λ)_N / ker G_N` has a trace `T^irr_N(c⋆,λ,d)`: for a family `E` whose classes
form a basis of the quotient the Gram matrix `A = (B(E_i,E_j))` is invertible, and
`tr(A⁻¹ (ρ(E_i,E_j)))` does not depend on `E` (two such families differ by an invertible matrix
`S` modulo `ker G_N`, on which `B` and `ρ` vanish, so `A' = S A Sᵀ`, `R' = S R Sᵀ`).
-/

namespace Virasoro

open Verma Module

section LinAlg

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem form_symm {Gm : Matrix P P ℂ} (hsym : Gm.transpose = Gm) (u v : P → ℂ) :
    u ⬝ᵥ Gm.mulVec v = v ⬝ᵥ Gm.mulVec u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]

/-- A basis of a complement of `ker G` has an invertible Gram matrix. -/
theorem gram_compl_det_ne_zero {Gm : Matrix P P ℂ} (hsym : Gm.transpose = Gm) {n : ℕ}
    {E : Fin n → P → ℂ} (hLI : LinearIndependent ℂ E)
    (hc : IsCompl (Submodule.span ℂ (Set.range E)) (LinearMap.ker Gm.mulVecLin)) :
    (Matrix.of fun i j => E i ⬝ᵥ Gm.mulVec (E j)).det ≠ 0 := by
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv : ∀ i, E i ⬝ᵥ Gm.mulVec (∑ j, a j • E j) = 0 := by
    intro i
    have := congrFun ha i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Matrix.mulVec_sum, dotProduct_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]
    rfl
  have hW : ∀ w ∈ Submodule.span ℂ (Set.range E), w ⬝ᵥ Gm.mulVec (∑ j, a j • E j) = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => w ⬝ᵥ Gm.mulVec (∑ j, a j • E j) = 0)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩
      exact hv i
    · exact zero_dotProduct _
    · intro x y _ _ hx hy
      rw [add_dotProduct, hx, hy, add_zero]
    · intro t x _ hx
      rw [smul_dotProduct, hx, smul_zero]
  have hker : Gm.mulVec (∑ j, a j • E j) = 0 := by
    refine dotProduct_eq _ _ fun u => ?_
    rw [zero_dotProduct, dotProduct_comm]
    have hu : u ∈ Submodule.span ℂ (Set.range E) ⊔ LinearMap.ker Gm.mulVecLin := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨w, hw, k, hk, rfl⟩ := Submodule.mem_sup.1 hu
    rw [add_dotProduct, hW w hw, zero_add, form_symm hsym]
    have hk' : Gm.mulVec k = 0 := hk
    rw [hk', dotProduct_zero]
  have hmem : (∑ j, a j • E j) ∈
      Submodule.span ℂ (Set.range E) ⊓ LinearMap.ker Gm.mulVecLin :=
    ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), hker⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at hmem
  exact ha0 (funext fun j => Fintype.linearIndependent_iff.1 hLI a hmem j)

/-- A family whose classes form a basis of `V / ker G` exists. -/
theorem exists_irr_basis (Gm : Matrix P P ℂ) (hsym : Gm.transpose = Gm) :
    ∃ (n : ℕ) (E : Fin n → P → ℂ), LinearIndependent ℂ E ∧
      IsCompl (Submodule.span ℂ (Set.range E)) (LinearMap.ker Gm.mulVecLin) ∧
      (Matrix.of fun i j => E i ⬝ᵥ Gm.mulVec (E j)).det ≠ 0 := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker Gm.mulVecLin)
  let bW := Module.finBasis ℂ W
  have hLI : LinearIndependent ℂ (fun i => (bW i : P → ℂ)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span ℂ (Set.range fun i => (bW i : P → ℂ)) = W := by
    have h1 : (Set.range fun i => (bW i : P → ℂ)) = W.subtype '' Set.range bW := by
      rw [← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, bW.span_eq, Submodule.map_subtype_top]
  have hc : IsCompl (Submodule.span ℂ (Set.range fun i => (bW i : P → ℂ)))
      (LinearMap.ker Gm.mulVecLin) := by
    rw [hspan]
    exact hW.symm
  exact ⟨_, _, hLI, hc, gram_compl_det_ne_zero hsym hLI hc⟩

/-- Change of the family: `F' = S F Sᵀ` for a bilinear form vanishing on `K` on both sides. -/
theorem form_change (Mm : Matrix P P ℂ) {n : ℕ} (E E' : Fin n → P → ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (kk : Fin n → P → ℂ) (hE' : ∀ i, E' i = ∑ j, S i j • E j + kk i)
    (hM : ∀ i (u : P → ℂ), kk i ⬝ᵥ Mm.mulVec u = 0 ∧ u ⬝ᵥ Mm.mulVec (kk i) = 0) :
    (Matrix.of fun i j => E' i ⬝ᵥ Mm.mulVec (E' j)) =
      S * (Matrix.of fun a b => E a ⬝ᵥ Mm.mulVec (E b)) * S.transpose := by
  ext i j
  rw [Matrix.of_apply, hE' i, hE' j, add_dotProduct, (hM i _).1, add_zero, Matrix.mulVec_add,
    dotProduct_add, (hM j _).2, add_zero, sum_dotProduct, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.mulVec_sum,
    dotProduct_sum, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The trace `tr(A⁻¹R)` does not depend on the family. -/
theorem irr_trace_indep {Gm Rm : Matrix P P ℂ} (hsym : Gm.transpose = Gm)
    (hρ : ∀ k : P → ℂ, Gm.mulVec k = 0 →
      ∀ u : P → ℂ, k ⬝ᵥ Rm.mulVec u = 0 ∧ u ⬝ᵥ Rm.mulVec k = 0)
    {n n' : ℕ} {E : Fin n → P → ℂ} {E' : Fin n' → P → ℂ}
    (hLI : LinearIndependent ℂ E) (hLI' : LinearIndependent ℂ E')
    (hc : IsCompl (Submodule.span ℂ (Set.range E)) (LinearMap.ker Gm.mulVecLin))
    (hc' : IsCompl (Submodule.span ℂ (Set.range E')) (LinearMap.ker Gm.mulVecLin))
    (hdet' : (Matrix.of fun i j => E' i ⬝ᵥ Gm.mulVec (E' j)).det ≠ 0) :
    ∑ i, ∑ j, (Matrix.of fun i j => E i ⬝ᵥ Gm.mulVec (E j))⁻¹ i j * (E j ⬝ᵥ Rm.mulVec (E i)) =
      ∑ i, ∑ j, (Matrix.of fun i j => E' i ⬝ᵥ Gm.mulVec (E' j))⁻¹ i j *
        (E' j ⬝ᵥ Rm.mulVec (E' i)) := by
  have hn : n = n' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 := Submodule.finrank_add_eq_of_isCompl hc'
    rw [finrank_span_eq_card hLI, Fintype.card_fin] at h1
    rw [finrank_span_eq_card hLI', Fintype.card_fin] at h2
    omega
  subst hn
  have hdec : ∀ i, ∃ (s : Fin n → ℂ) (k : P → ℂ), Gm.mulVec k = 0 ∧
      E' i = ∑ j, s j • E j + k := by
    intro i
    have hu : E' i ∈ Submodule.span ℂ (Set.range E) ⊔ LinearMap.ker Gm.mulVecLin := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨w, hw, k, hk, hwk⟩ := Submodule.mem_sup.1 hu
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    exact ⟨s, k, hk, by rw [hs, hwk]⟩
  choose S kk hkk hE' using hdec
  have hG : ∀ i (u : P → ℂ), kk i ⬝ᵥ Gm.mulVec u = 0 ∧ u ⬝ᵥ Gm.mulVec (kk i) = 0 := by
    intro i u
    have h2 : u ⬝ᵥ Gm.mulVec (kk i) = 0 := by rw [hkk i, dotProduct_zero]
    exact ⟨by rw [form_symm hsym, h2], h2⟩
  have hA := form_change Gm E E' (Matrix.of S) kk hE' hG
  have hR := form_change Rm E E' (Matrix.of S) kk hE' fun i u => hρ (kk i) (hkk i) u
  set A := Matrix.of fun i j => E i ⬝ᵥ Gm.mulVec (E j) with hAdef
  set R := Matrix.of fun i j => E i ⬝ᵥ Rm.mulVec (E j) with hRdef
  set A' := Matrix.of fun i j => E' i ⬝ᵥ Gm.mulVec (E' j) with hA'def
  set R' := Matrix.of fun i j => E' i ⬝ᵥ Rm.mulVec (E' j) with hR'def
  have hS : IsUnit (Matrix.of S).det := by
    rw [hA, Matrix.det_mul, Matrix.det_mul] at hdet'
    exact (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (left_ne_zero_of_mul hdet')))
  have hSt : IsUnit (Matrix.of S).transpose.det := by rwa [Matrix.det_transpose]
  have e1 : ∑ i, ∑ j, A⁻¹ i j * (E j ⬝ᵥ Rm.mulVec (E i)) = (A⁻¹ * R).trace := by
    simp [Matrix.trace, Matrix.mul_apply, hRdef]
  have e2 : ∑ i, ∑ j, A'⁻¹ i j * (E' j ⬝ᵥ Rm.mulVec (E' i)) = (A'⁻¹ * R').trace := by
    simp [Matrix.trace, Matrix.mul_apply, hR'def]
  rw [e1, e2, hA, hR, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc (A⁻¹ * R).trace
      = (A⁻¹ * R * ((Matrix.of S).transpose * (Matrix.of S).transpose⁻¹)).trace := by
        rw [Matrix.mul_nonsing_inv _ hSt, Matrix.mul_one]
    _ = ((Matrix.of S).transpose⁻¹ * (A⁻¹ * ((Matrix.of S)⁻¹ * Matrix.of S) * R *
          (Matrix.of S).transpose)).trace := by
        rw [Matrix.nonsing_inv_mul _ hS, Matrix.mul_one,
          Matrix.trace_mul_comm ((Matrix.of S).transpose⁻¹),
          Matrix.mul_assoc (A⁻¹ * R)]
    _ = _ := by simp only [Matrix.mul_assoc]

end LinAlg

variable {c h : ℂ}

/-- A vector with coordinates in `ker G_N` is in the radical of the Shapovalov form. -/
theorem shap_radical_of_ker {N : ℕ} {k : Nat.Partition N → ℂ}
    (hk : (gram c h N).mulVec k = 0) (v : Verma ℂ c h) : shap c h v (pbwCoord N k) = 0 := by
  have hv : v ∈ (⨆ M : ℕ, (level M : Submodule ℂ (Verma ℂ c h))) := by
    rw [iSup_level_eq_top]; trivial
  refine Submodule.iSup_induction (motive := fun v => shap c h v (pbwCoord N k) = 0) _ hv
    ?_ ?_ ?_
  · intro M u hu
    by_cases hMN : M = N
    · subst hMN
      exact shap_pbwCoord_radical hk hu
    · exact shap_level_ne hMN hu ⟨k, rfl⟩
  · simp
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- When `ρ` descends, it vanishes in coordinates on `ker G_N`. -/
theorem torusForm_ker_of_descends {d : ℂ} (hd : TorusDescends c h d) {N : ℕ}
    {k : Nat.Partition N → ℂ} (hk : (gram c h N).mulVec k = 0) (u : Nat.Partition N → ℂ) :
    torusForm c h d N k u = 0 ∧ torusForm c h d N u k = 0 := by
  have hT := isPrimaryPairing_pairing (c := c) (h := h) d
  have := hd _ hT _ isShapovalov_shap (pbwCoord N k) (shap_radical_of_ker hk) (pbwCoord N u)
  rw [primary_pbwCoord hT, primary_pbwCoord hT] at this
  exact this

/-- For a weight `h` and an external weight `d` at which `ρ(c,h,d)` descends to `L(c,h)`, each
coefficient `T^irr_N(c,h,d)` exists and is unique. -/
theorem irrTrace_existsUnique {d : ℂ} (hd : TorusDescends c h d) (N : ℕ) :
    ∃! T : ℂ, IsIrrTrace c h d N T := by
  classical
  obtain ⟨n, E, hLI, hc, hdet⟩ := exists_irr_basis (gram c h N) (gram_transpose c h N)
  refine ⟨_, ⟨n, E, hLI, hc, hdet, rfl⟩, ?_⟩
  rintro T ⟨n', E', hLI', hc', hdet', rfl⟩
  exact (irr_trace_indep (gram_transpose c h N)
    (fun k hk u => torusForm_ker_of_descends hd hk u) hLI hLI' hc hc' hdet').symm

/-- `Stmt_sub_irr_trace_unique` (paper.tex l.1857–1858). -/
theorem sub_irr_trace_unique : Stmt_sub_irr_trace_unique := by
  intro p p' r s b _ _ _ _ _ _ _ _ d hd N
  exact irrTrace_existsUnique hd N

example : Stmt_sub_irr_trace_unique := sub_irr_trace_unique

end Virasoro
