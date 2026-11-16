import Virasoro.Proofs.PBWBasis
import Virasoro.Proofs.TorusDegree

/-!
# Levels of the Verma module

The mode `L_n` maps level `N` to level `N - n` (and to zero if `n > N`), `L_0` acts on level `N`
by `h + N`, the Shapovalov form on level `N` is given by the matrix `gram c h N` in
Poincaré–Birkhoff–Witt coordinates, and different levels are orthogonal.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

theorem word_sum' {N : ℕ} (Y : Nat.Partition N) : Y.word.sum = N := by
  have h1 : ((Y.word : List ℕ) : Multiset ℕ).sum = N := by rw [word_coe, Y.parts_sum]
  rwa [Multiset.sum_coe] at h1

theorem toVerma_mem_level {s : St R} {M : ℕ} (hs : PosSt s) (hsum : ∀ t ∈ s, t.1.sum = M) :
    St.toVerma (c := c) (h := h) s ∈ level M := by
  induction s with
  | nil => rw [St.toVerma_nil]; exact Submodule.zero_mem _
  | cons t s ih =>
    rw [St.toVerma_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))
        (fun u hu => hsum u (List.mem_cons_of_mem _ hu)))
    have := neg_mem_level (c := c) (h := h) t.1.length t.1 (hs t List.mem_cons_self) le_rfl
    rwa [hsum t List.mem_cons_self] at this

/-- `L_n` maps `L_{-w}|h⟩` of level `|w|` into the level `|w| - n`. -/
theorem L_neg_mem_level {w : List ℕ} (hw : PosWord w) {n : ℤ} {M : ℕ}
    (hM : (M : ℤ) = (w.sum : ℕ) - n) : L n (neg (c := c) (h := h) w) ∈ level M := by
  rw [L_neg_actWord]
  refine toVerma_mem_level (posSt_actWord c h hw n) fun t ht => ?_
  have := actWord_sum c h w n t ht
  omega

theorem L_neg_eq_zero {w : List ℕ} {n : ℤ} (hn : ((w.sum : ℕ) : ℤ) < n) :
    L n (neg (c := c) (h := h) w) = 0 := by
  rw [L_neg_actWord]
  have hnil : actWord c h n w = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro t ht
    have := actWord_sum c h w n t ht
    omega
  rw [hnil, St.toVerma_nil]

/-- `L_n` maps level `N` into level `N - n`. -/
theorem L_mem_level {N M : ℕ} {n : ℤ} (hM : (M : ℤ) = (N : ℤ) - n) {v : Verma R c h}
    (hv : v ∈ level N) : L n v ∈ level M := by
  obtain ⟨u, rfl⟩ := hv
  rw [pbwCoord_apply, map_sum]
  refine Submodule.sum_mem _ fun Y _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (L_neg_mem_level (posWord_word Y) ?_)
  rw [word_sum']
  exact hM

theorem L_eq_zero_of_level {N : ℕ} {n : ℤ} (hn : (N : ℤ) < n) {v : Verma R c h}
    (hv : v ∈ level N) : L n v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  rw [pbwCoord_apply, map_sum]
  refine Finset.sum_eq_zero fun Y _ => ?_
  rw [map_smul, L_neg_eq_zero (by rw [word_sum']; exact hn), smul_zero]

/-- `L_0` acts on level `N` by `h + N`. -/
theorem L_zero_of_mem_level {N : ℕ} {v : Verma R c h} (hv : v ∈ level N) :
    L 0 v = (h + (N : R)) • v := by
  obtain ⟨u, rfl⟩ := hv
  rw [pbwCoord_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, L_zero_neg, word_sum', smul_comm]

/-- The Shapovalov form on level `N` in coordinates. -/
theorem shap_neg_pbwCoord {N : ℕ} (Y : Nat.Partition N) (v : Nat.Partition N → R) :
    shap c h (neg Y.word) (pbwCoord N v) = (gram c h N).mulVec v Y := by
  rw [pbwCoord_apply, map_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [map_smul, isShapovalov_shap.gramWord _ _ (posWord_word Z), smul_eq_mul, mul_comm]
  rfl

theorem intCast_mul_eq_zero {k : ℤ} (hk : k ≠ 0) {x : R} (hx : (k : R) * x = 0) : x = 0 := by
  have h1 : algebraMap ℚ R ((k : ℚ)⁻¹) * ((k : R) * x) = x := by
    rw [← mul_assoc, show ((k : ℤ) : R) = algebraMap ℚ R (k : ℚ) by simp, ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast hk), map_one, one_mul]
  rw [← h1, hx, mul_zero]

/-- Different levels are orthogonal for the Shapovalov form. -/
theorem shap_level_ne {N M : ℕ} (hNM : N ≠ M) {u v : Verma R c h} (hu : u ∈ level N)
    (hv : v ∈ level M) : shap c h u v = 0 := by
  have h1 := isShapovalov_shap.2 (0 : ℤ) u v
  rw [neg_zero, L_zero_of_mem_level hu, L_zero_of_mem_level hv, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  have h2 : (((N : ℤ) - (M : ℤ) : ℤ) : R) * shap c h u v = 0 := by
    push_cast
    linear_combination h1
  exact intCast_mul_eq_zero (by omega) h2

end Verma

end Virasoro
