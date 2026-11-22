import Virasoro.Proofs.P2Sec13DiagForms
import Virasoro.Proofs.P2Sec11LayerZero

/-!
# Lemma 13.1, Step 4: tools for the limit (paper.tex l.2990–3028)

* `det_ne_zero_of_compl`: the Gram matrix of a complement of the radical is invertible (the
  generic fibres of `𝒱_N`);
* `locLam_injective`: the expansion `b ↦ b⋆ + X` of `ℂ[b,b⁻¹]` is injective;
* `irrTrace_of_diag`: the irreducible trace computed in a family that is orthogonal for the
  Shapovalov form and spans modulo the radical.
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial

open scoped PowerSeries

theorem gramForm_sum_right {c h : ℂ} {N : ℕ} {ι : Type*} [Fintype ι] (x : Nat.Partition N → ℂ)
    (f : ι → (Nat.Partition N → ℂ)) (a : ι → ℂ) :
    gramForm c h N x (∑ i, a i • f i) = ∑ i, a i * gramForm c h N x (f i) := by
  simp only [gramForm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
    smul_eq_mul]

theorem gramForm_sum_left {c h : ℂ} {N : ℕ} {ι : Type*} [Fintype ι] (x : Nat.Partition N → ℂ)
    (f : ι → (Nat.Partition N → ℂ)) (a : ι → ℂ) :
    gramForm c h N (∑ i, a i • f i) x = ∑ i, a i * gramForm c h N (f i) x := by
  simp only [gramForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem gramForm_symm' (c h : ℂ) (N : ℕ) (x y : Nat.Partition N → ℂ) :
    gramForm c h N x y = gramForm c h N y x := by
  unfold gramForm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, gram_transpose, dotProduct_comm]

/-- The Gram matrix of a family spanning a complement of the radical is invertible. -/
theorem det_ne_zero_of_compl {c h : ℂ} {N n : ℕ} {E : Fin n → (Nat.Partition N → ℂ)}
    (hLI : LinearIndependent ℂ E)
    (hc : IsCompl (Submodule.span ℂ (Set.range E)) (LinearMap.ker (gram c h N).mulVecLin)) :
    (Matrix.of fun i j => gramForm c h N (E i) (E j)).det ≠ 0 := by
  intro h0
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set v : Nat.Partition N → ℂ := ∑ j, a j • E j with hv
  have hpair : ∀ i, gramForm c h N (E i) v = 0 := by
    intro i
    have h1 := congrFun ha i
    rw [hv, gramForm_sum_right]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hker : v ∈ LinearMap.ker (gram c h N).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext Y
    obtain ⟨x, hx, k, hk, hxk⟩ := Submodule.mem_sup.1
      (show Pi.single Y 1 ∈ Submodule.span ℂ (Set.range E) ⊔
        LinearMap.ker (gram c h N).mulVecLin by rw [hc.sup_eq_top]; exact Submodule.mem_top)
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
    have e1 : (gram c h N).mulVec v Y = gramForm c h N (Pi.single Y 1) v := by
      rw [gramForm, single_dotProduct, one_mul]
    rw [e1, ← hxk]
    have e2 : gramForm c h N ((∑ i, α i • E i) + k) v =
        gramForm c h N (∑ i, α i • E i) v + gramForm c h N k v := by
      simp only [gramForm, add_dotProduct]
    rw [e2, gramForm_sum_left, gramForm_symm' c h N k v]
    have hk' : (gram c h N).mulVec k = 0 := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk; exact hk
    rw [gramForm, hk', dotProduct_zero, add_zero, Pi.zero_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [hpair i, mul_zero]
  have hv0 : v = 0 := by
    have hmem : v ∈ Submodule.span ℂ (Set.range E) ⊓ LinearMap.ker (gram c h N).mulVecLin :=
      ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩),
        hker⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  exact ha0 (funext fun j => (Fintype.linearIndependent_iff.1 hLI) a hv0 j)

/-- The expansion `b ↦ b⋆ + X` of `ℂ[b,b⁻¹]` is injective. -/
theorem locLam_injective {b : ℂ} (hb : b ≠ 0) : Function.Injective (locLam b hb) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨⟨q, ⟨_, n, rfl⟩⟩, hq⟩ := IsLocalization.surj (Submonoid.powers (X : ℂ[X])) a
  simp only at hq
  have h1 := congrArg (locLam b hb) hq
  rw [map_mul, ha, zero_mul, locLam_algebraMap] at h1
  have hq0 : q = 0 := by
    by_contra hne
    apply shiftPS_ne_zero b hne
    exact h1.symm
  rw [hq0, map_zero] at hq
  have hu : IsUnit (algebraMap ℂ[X] Lam ((X : ℂ[X]) ^ n)) :=
    IsLocalization.map_units Lam (⟨(X : ℂ[X]) ^ n, n, rfl⟩ : Submonoid.powers (X : ℂ[X]))
  exact (hu.mul_left_eq_zero).1 hq

/-- The irreducible trace computed in a family that is orthogonal for the Shapovalov form and
spans modulo the radical (l.2992–2996, 3018–3023). -/
theorem irrTrace_of_diag {c h d : ℂ} {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hd : TorusDescends c h d) (v : ι → (Nat.Partition N → ℂ))
    (horth : ∀ a b, a ≠ b → gramForm c h N (v a) (v b) = 0)
    (hdiag : ∀ a, gramForm c h N (v a) (v a) ≠ 0)
    (hspan : ∀ z, z ∈ Submodule.span ℂ (Set.range v) ⊔ LinearMap.ker (gram c h N).mulVecLin)
    {T : ℂ} (hT : IsIrrTrace c h d N T) :
    T = ∑ a, torusForm c h d N (v a) (v a) / gramForm c h N (v a) (v a) := by
  classical
  have hcoef : ∀ (α : ι → ℂ) (b : ι), gramForm c h N (v b) (∑ a, α a • v a) =
      α b * gramForm c h N (v b) (v b) := by
    intro α b
    rw [gramForm_sum_right, Finset.sum_eq_single b (fun a _ hab => by rw [horth b a hab.symm,
      mul_zero]) (fun hb => absurd (Finset.mem_univ b) hb)]
  have hLI : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro α hα b
    have := hcoef α b
    rw [hα, gramForm, Matrix.mulVec_zero, dotProduct_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_right (hdiag b)
  have hdisj : Disjoint (Submodule.span ℂ (Set.range v)) (LinearMap.ker (gram c h N).mulVecLin) := by
    rw [Submodule.disjoint_def]
    intro x hx hk
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
    have hα : ∀ b, α b = 0 := by
      intro b
      have := hcoef α b
      rw [gramForm, hk, dotProduct_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hdiag b)
    simp [hα]
  have hcompl : IsCompl (Submodule.span ℂ (Set.range v)) (LinearMap.ker (gram c h N).mulVecLin) :=
    ⟨hdisj, codisjoint_iff.2 (eq_top_iff.2 fun z _ => hspan z)⟩
  let eqv := Fintype.equivFin ι
  set E : Fin (Fintype.card ι) → (Nat.Partition N → ℂ) := fun i => v (eqv.symm i) with hE
  have hrange : Set.range E = Set.range v := eqv.symm.surjective.range_comp v
  have hM : (Matrix.of fun i j => gramForm c h N (E i) (E j)) =
      Matrix.diagonal fun i => gramForm c h N (E i) (E i) := by
    ext i j
    rw [Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · exact horth _ _ fun he => hij (eqv.symm.injective he)
  have hdet : (Matrix.of fun i j => gramForm c h N (E i) (E j)).det ≠ 0 := by
    rw [hM, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hdiag _
  have hval : IsIrrTrace c h d N
      (∑ i, ∑ j, (Matrix.of fun i j => gramForm c h N (E i) (E j))⁻¹ i j *
        torusForm c h d N (E j) (E i)) :=
    ⟨_, E, hLI.comp _ eqv.symm.injective, by rw [hrange]; exact hcompl, hdet, rfl⟩
  have hinv : (Matrix.diagonal fun i => gramForm c h N (E i) (E i))⁻¹ =
      Matrix.diagonal fun i => (gramForm c h N (E i) (E i))⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hdiag _)
  rw [(irrTrace_existsUnique hd N).unique hT hval, hM, hinv]
  have e1 : ∀ i, (∑ j, Matrix.diagonal (fun i => (gramForm c h N (E i) (E i))⁻¹) i j *
      torusForm c h d N (E j) (E i)) =
        torusForm c h d N (E i) (E i) / gramForm c h N (E i) (E i) := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [Matrix.diagonal_apply_ne _ hji.symm,
      zero_mul]) (fun hi => absurd (Finset.mem_univ i) hi), Matrix.diagonal_apply_eq,
      div_eq_mul_inv, mul_comm]
  simp only [e1]
  rw [hE]
  exact Equiv.sum_comp eqv.symm (fun a => torusForm c h d N (v a) (v a) / gramForm c h N (v a) (v a))

end Virasoro.P2
