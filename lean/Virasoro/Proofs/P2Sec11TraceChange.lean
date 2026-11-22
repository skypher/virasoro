import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# The trace `Tr_{V/W}(B̄⁻¹ρ̄)` does not depend on the basis (proof of Proposition 11.2(ii))

For bilinear forms `β`, `ϱ` on `V` that vanish on a subspace `W` in both slots, and two families
`E`, `E'` whose classes are bases of `V/W`: `E' = S E` and `E = T E'` modulo `W` with
`T S = 1`, `S T = 1`, the Gram matrices satisfy `A' = S A Sᵀ`, `R' = S R Sᵀ`, and
`tr(A'⁻¹R') = tr(A⁻¹R)`.  This is the basis independence used in "computing the trace in this
basis" (paper.tex l.2472) and in the identification of the layers (l.2486–2495).
-/

namespace Virasoro

open Matrix

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- `E' = S E` modulo `W`. -/
def IsChange (W : Submodule ℂ M) (E : κ → M) (E' : κ' → M) (S : Matrix κ' κ ℂ) : Prop :=
  ∀ a', E' a' - ∑ a, S a' a • E a ∈ W

omit [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] in
theorem exists_change {W : Submodule ℂ M} {E : κ → M} (E' : κ' → M)
    (hs : ∀ x, x ∈ Submodule.span ℂ (Set.range E) ⊔ W) :
    ∃ S : Matrix κ' κ ℂ, IsChange W E E' S := by
  have h : ∀ a', ∃ s : κ → ℂ, E' a' - ∑ a, s a • E a ∈ W := by
    intro a'
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs (E' a'))
    obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
    exact ⟨s, by rw [← hyz, add_sub_cancel_left]; exact hz⟩
  choose S hS using h
  exact ⟨Matrix.of S, hS⟩

omit [DecidableEq κ'] in
theorem change_mul_eq_one {W : Submodule ℂ M} {E : κ → M} {E' : κ' → M} {S : Matrix κ' κ ℂ}
    {T : Matrix κ κ' ℂ} (hS : IsChange W E E' S) (hT : IsChange W E' E T)
    (hLI : LinearIndependent ℂ E) (hd : Disjoint (Submodule.span ℂ (Set.range E)) W) :
    T * S = 1 := by
  refine Matrix.ext fun a b => ?_
  have e1 : ∑ b, (1 : Matrix κ κ ℂ) a b • E b = E a := by
    simp [Matrix.one_apply]
  have e2 : ∑ b, (T * S) a b • E b = ∑ a', T a a' • ∑ b, S a' b • E b := by
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have e3 : ∑ b, ((1 : Matrix κ κ ℂ) a b - (T * S) a b) • E b =
      (E a - ∑ a', T a a' • E' a') + ∑ a', T a a' • (E' a' - ∑ b, S a' b • E b) := by
    simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, smul_sub]
    abel
  have hx : ∑ b, ((1 : Matrix κ κ ℂ) a b - (T * S) a b) • E b ∈ W := by
    rw [e3]
    exact W.add_mem (hT a) (W.sum_mem fun a' _ => W.smul_mem _ (hS a'))
  have hx2 : ∑ b, ((1 : Matrix κ κ ℂ) a b - (T * S) a b) • E b ∈
      Submodule.span ℂ (Set.range E) :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have h0 := Submodule.disjoint_def.1 hd _ hx2 hx
  have h1 := Fintype.linearIndependent_iff.1 hLI _ h0 b
  exact (sub_eq_zero.1 h1).symm

omit [DecidableEq κ] [DecidableEq κ'] in
/-- `A' = S A Sᵀ` for a form vanishing on `W` in both slots. -/
theorem gram_change (β : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) {W : Submodule ℂ M}
    (hβ : ∀ k ∈ W, ∀ u, β k u = 0 ∧ β u k = 0) {E : κ → M} {E' : κ' → M} {S : Matrix κ' κ ℂ}
    (hS : IsChange W E E' S) :
    (Matrix.of fun a' b' => β (E' a') (E' b')) =
      S * (Matrix.of fun a b => β (E a) (E b)) * Sᵀ := by
  refine Matrix.ext fun x y => ?_
  have e1 : β (E' x) (E' y) = β (∑ a, S x a • E a) (E' y) := by
    have h := (hβ _ (hS x) (E' y)).1
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  have e2 : β (∑ a, S x a • E a) (E' y) = β (∑ a, S x a • E a) (∑ b, S y b • E b) := by
    have h := (hβ _ (hS y) (∑ a, S x a • E a)).2
    rw [map_sub, sub_eq_zero] at h
    exact h
  rw [Matrix.of_apply, e1, e2]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- `tr(A⁻¹R)` does not depend on the family of representatives of a basis of `V/W`. -/
theorem trace_change (β ϱ : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) (W : Submodule ℂ M)
    (hβ : ∀ k ∈ W, ∀ u, β k u = 0 ∧ β u k = 0) (hϱ : ∀ k ∈ W, ∀ u, ϱ k u = 0 ∧ ϱ u k = 0)
    {E : κ → M} {E' : κ' → M} (hLI : LinearIndependent ℂ E) (hLI' : LinearIndependent ℂ E')
    (hd : Disjoint (Submodule.span ℂ (Set.range E)) W)
    (hd' : Disjoint (Submodule.span ℂ (Set.range E')) W)
    (hs : ∀ x, x ∈ Submodule.span ℂ (Set.range E) ⊔ W)
    (hs' : ∀ x, x ∈ Submodule.span ℂ (Set.range E') ⊔ W)
    (hdet : (Matrix.of fun a b => β (E a) (E b)).det ≠ 0) :
    ∑ a, ∑ b, (Matrix.of fun a b => β (E a) (E b))⁻¹ a b * ϱ (E b) (E a) =
      ∑ a, ∑ b, (Matrix.of fun a b => β (E' a) (E' b))⁻¹ a b * ϱ (E' b) (E' a) := by
  obtain ⟨S, hS⟩ := exists_change (W := W) (E := E) E' hs
  obtain ⟨T, hT⟩ := exists_change (W := W) (E := E') E hs'
  have hTS : T * S = 1 := change_mul_eq_one hS hT hLI hd
  have hST : S * T = 1 := change_mul_eq_one hT hS hLI' hd'
  set A : Matrix κ κ ℂ := Matrix.of fun a b => β (E a) (E b) with hA
  set R : Matrix κ κ ℂ := Matrix.of fun a b => ϱ (E a) (E b) with hR
  have hA' : (Matrix.of fun a b => β (E' a) (E' b)) = S * A * Sᵀ := gram_change β hβ hS
  have hR' : (Matrix.of fun a b => ϱ (E' a) (E' b)) = S * R * Sᵀ := gram_change ϱ hϱ hS
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hinv : (S * A * Sᵀ)⁻¹ = Tᵀ * A⁻¹ * T := by
    refine Matrix.inv_eq_right_inv ?_
    calc S * A * Sᵀ * (Tᵀ * A⁻¹ * T) = S * (A * (Sᵀ * Tᵀ) * A⁻¹) * T := by
          simp only [Matrix.mul_assoc]
      _ = S * (A * A⁻¹) * T := by
          rw [← Matrix.transpose_mul, hTS, Matrix.transpose_one, Matrix.mul_one]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one, hST]
  have tr1 : ∑ a, ∑ b, A⁻¹ a b * ϱ (E b) (E a) = Matrix.trace (A⁻¹ * R) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hR, Matrix.of_apply]
  have tr2 : ∑ a, ∑ b, (S * A * Sᵀ)⁻¹ a b * ϱ (E' b) (E' a) =
      Matrix.trace ((S * A * Sᵀ)⁻¹ * (S * R * Sᵀ)) := by
    rw [← hR']
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [hA', tr1, tr2, hinv]
  have e1 : Tᵀ * A⁻¹ * T * (S * R * Sᵀ) = Tᵀ * (A⁻¹ * R * Sᵀ) := by
    calc Tᵀ * A⁻¹ * T * (S * R * Sᵀ) = Tᵀ * (A⁻¹ * ((T * S) * R) * Sᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = Tᵀ * (A⁻¹ * R * Sᵀ) := by rw [hTS, Matrix.one_mul]
  have e2 : Matrix.trace (Tᵀ * (A⁻¹ * R * Sᵀ)) = Matrix.trace (A⁻¹ * R) := by
    rw [Matrix.trace_mul_comm Tᵀ (A⁻¹ * R * Sᵀ), Matrix.mul_assoc (A⁻¹ * R), ← Matrix.transpose_mul,
      hTS, Matrix.transpose_one, Matrix.mul_one]
  rw [e1, e2]

end Virasoro
