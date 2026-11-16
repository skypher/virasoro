import Virasoro.Proofs.Levels
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Level components of the Verma module

The Poincaré–Birkhoff–Witt basis gives level components: every vector is the finite sum of its
components, an `L_0`-eigenvector of weight `h + ℓ` lies in level `ℓ`, and the negative modes
act injectively.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

variable (c h)

/-- The Poincaré–Birkhoff–Witt basis `(L_{-Y}|h⟩)_Y`, indexed by all partitions. -/
noncomputable def pbwBasis : Module.Basis (Σ N : ℕ, Nat.Partition N) R (Verma R c h) :=
  Module.Basis.mk neg_word_linearIndependent (by rw [span_neg_word_eq_top])

variable {c h}

theorem pbwBasis_apply (Y : Σ N : ℕ, Nat.Partition N) : pbwBasis c h Y = neg Y.2.word := by
  rw [pbwBasis, Module.Basis.mk_apply]

/-- The level-`N` coordinates of a vector. -/
noncomputable def comp (N : ℕ) : Verma R c h →ₗ[R] (Nat.Partition N → R) :=
  LinearMap.pi fun Y =>
    (Finsupp.lapply (⟨N, Y⟩ : Σ N : ℕ, Nat.Partition N)) ∘ₗ (pbwBasis c h).repr.toLinearMap

theorem comp_apply (N : ℕ) (v : Verma R c h) (Y : Nat.Partition N) :
    comp N v Y = (pbwBasis c h).repr v ⟨N, Y⟩ := rfl

theorem comp_neg_word {M : ℕ} (Z : Nat.Partition M) (N : ℕ) (Y : Nat.Partition N) :
    comp (c := c) (h := h) N (neg Z.word) Y
      = if (⟨M, Z⟩ : Σ N : ℕ, Nat.Partition N) = ⟨N, Y⟩ then 1 else 0 := by
  classical
  have e : neg (c := c) (h := h) Z.word = pbwBasis c h ⟨M, Z⟩ :=
    (pbwBasis_apply (c := c) (h := h) ⟨M, Z⟩).symm
  rw [comp_apply, e, Module.Basis.repr_self, Finsupp.single_apply]

theorem comp_pbwCoord_same (N : ℕ) (u : Nat.Partition N → R) :
    comp (c := c) (h := h) N (pbwCoord N u) = u := by
  classical
  funext Y
  rw [pbwCoord_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, comp_neg_word, smul_eq_mul]
  rw [Finset.sum_eq_single Y]
  · rw [if_pos rfl, mul_one]
  · intro Z _ hne
    rw [if_neg (fun h => hne (by simpa using h)), mul_zero]
  · intro hY
    exact absurd (Finset.mem_univ Y) hY

theorem comp_pbwCoord_ne {M N : ℕ} (hne : M ≠ N) (u : Nat.Partition M → R) :
    comp (c := c) (h := h) N (pbwCoord M u) = 0 := by
  classical
  funext Y
  rw [pbwCoord_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun Z _ => ?_
  simp only [map_smul, Pi.smul_apply, comp_neg_word, smul_eq_mul]
  rw [if_neg (fun h => hne (congrArg Sigma.fst h)), mul_zero]

theorem comp_of_mem_level_ne {M N : ℕ} (hne : M ≠ N) {v : Verma R c h} (hv : v ∈ level M) :
    comp N v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  exact comp_pbwCoord_ne hne u

theorem pbwCoord_comp_of_mem_level {N : ℕ} {v : Verma R c h} (hv : v ∈ level N) :
    pbwCoord N (comp N v) = v := by
  obtain ⟨u, rfl⟩ := hv
  rw [comp_pbwCoord_same]

/-- Every vector is the finite sum of its level components. -/
theorem exists_decomp (v : Verma R c h) :
    ∃ T : Finset ℕ, v = ∑ M ∈ T, pbwCoord M (comp M v) := by
  classical
  set a := (pbwBasis c h).repr v with ha
  refine ⟨a.support.image Sigma.fst, ?_⟩
  have h1 : ∑ M ∈ a.support.image Sigma.fst, pbwCoord (c := c) (h := h) M (comp M v)
      = ∑ i ∈ (a.support.image Sigma.fst).sigma fun _ => Finset.univ,
          a i • neg i.2.word := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun N _ => pbwCoord_apply N _
  have h2 : v = ∑ i ∈ a.support, a i • neg i.2.word := by
    conv_lhs => rw [← (pbwBasis c h).linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pbwBasis_apply]
  rw [h1]
  conv_lhs => rw [h2]
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ _⟩
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.1 hi, zero_smul]

theorem comp_L_zero (M : ℕ) (v : Verma R c h) :
    comp M (L 0 v) = (h + (M : R)) • comp M v := by
  classical
  have key : (comp (c := c) (h := h) M) ∘ₗ L 0 = (h + (M : R)) • comp M := by
    refine (pbwBasis c h).ext fun i => ?_
    obtain ⟨M', Z⟩ := i
    rw [pbwBasis_apply, LinearMap.comp_apply, L_zero_neg, word_sum', map_smul,
      LinearMap.smul_apply]
    funext Y
    simp only [Pi.smul_apply, comp_neg_word, smul_eq_mul]
    split_ifs with heq
    · have : M' = M := congrArg Sigma.fst heq
      rw [this]
    · rw [mul_zero, mul_zero]
  exact LinearMap.congr_fun key v

/-- An `L_0`-eigenvector of weight `h + ℓ` lies in level `ℓ`. -/
theorem mem_level_of_L_zero {ℓ : ℕ} {v : Verma R c h} (hv : L 0 v = (h + (ℓ : R)) • v) :
    v ∈ level ℓ := by
  have hz : ∀ M : ℕ, M ≠ ℓ → comp M v = 0 := by
    intro M hM
    have h1 := comp_L_zero M v
    rw [hv, map_smul] at h1
    funext Y
    have h2 := congrFun h1 Y
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (((ℓ : ℤ) - (M : ℤ) : ℤ) : R) * comp M v Y = 0 := by
      push_cast
      linear_combination h2
    exact intCast_mul_eq_zero (by omega) h3
  obtain ⟨T, hT⟩ := exists_decomp v
  rw [hT]
  refine Submodule.sum_mem _ fun M _ => ?_
  by_cases hM : M = ℓ
  · rw [hM]
    exact ⟨_, rfl⟩
  · rw [hz M hM, map_zero]
    exact Submodule.zero_mem _

/-- The polynomial realization is injective. -/
theorem polyMap_injective : Function.Injective (polyMap c h) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hmem : v ∈ Submodule.span R (Set.range fun Y : (Σ N : ℕ, Nat.Partition N) =>
      neg (c := c) (h := h) Y.2.word) := by
    rw [span_neg_word_eq_top]; trivial
  obtain ⟨a, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hmem
  rw [Finsupp.sum, map_sum] at hv
  simp only [map_smul] at hv
  have hli := polyMap_neg_word_linearIndependent (c := c) (h := h)
  rw [linearIndependent_iff'] at hli
  have h0 := hli a.support (fun i => a i) hv
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [h0 i hi, zero_smul]

/-- The negative modes act injectively on the Verma module. -/
theorem L_neg_injective {m : ℤ} (hm : 0 < m) :
    Function.Injective (L (c := c) (h := h) (-m)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 := congrArg (polyMap c h) hv
  rw [polyMap_L_neg hm, map_zero] at h1
  have h2 := (injective_iff_map_eq_zero _).1 (polyG_injective m.toNat) _ h1
  exact (injective_iff_map_eq_zero _).1 polyMap_injective _ h2

end Verma

end Virasoro
