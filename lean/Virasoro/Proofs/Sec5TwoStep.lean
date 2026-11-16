import Virasoro.Proofs.Sec5Cross
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Proofs: Proposition 5.3 (two-step inverse principal part)
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_ker2 {G : Matrix ι ι K⟦X⟧} {v : ι → K} :
    v ∈ ker2 G ↔ v ∈ ker0 G ∧ ∀ u ∈ ker0 G, cross1 G u v = 0 := Iff.rfl

theorem cross2_def (G : Matrix ι ι K⟦X⟧) (u v v₁ : ι → K) :
    cross2 G u v v₁ = u ⬝ᵥ ((coeffMat 2 G).mulVec v + (coeffMat 1 G).mulVec v₁) := rfl

/-- Nondegeneracy of the second crossing form on `K₂`. -/
def Cross2NondegK (G : Matrix ι ι K⟦X⟧) : Prop :=
  ∀ v ∈ ker2 G,
    (∀ u ∈ ker2 G, ∀ v₁ : ι → K,
      (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v → cross2 G u v v₁ = 0) → v = 0

/-- The first crossing form is symmetric. -/
theorem cross1_comm {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (u v : ι → K) :
    cross1 G u v = cross1 G v u := by
  rw [cross1_def, cross1_def, dot_mulVec_symm (coeffMat_isSymm hG 1), dotProduct_comm]

/-- For `v ∈ K₂` the equation `G₀ v₁ = - G₁ v` is solvable. -/
theorem exists_v1 {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {v : ι → K} (hv : v ∈ ker2 G) :
    ∃ v₁ : ι → K, (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v := by
  refine symm_range_of_orth (coeffMat_isSymm hG 0) _ fun u hu => ?_
  rw [dotProduct_neg, ← cross1_def, (mem_ker2.1 hv).2 u (mem_ker0.2 hu), neg_zero]

/-- `β₂` does not depend on the choice of `v₁`. -/
theorem cross2_indep {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {u v v₁ v₁' : ι → K}
    (hu : u ∈ ker2 G)
    (h1 : (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v)
    (h1' : (coeffMat 0 G).mulVec v₁' = -(coeffMat 1 G).mulVec v) :
    cross2 G u v v₁ = cross2 G u v v₁' := by
  have hk : v₁ - v₁' ∈ ker0 G := by
    rw [mem_ker0, Matrix.mulVec_sub, h1, h1', sub_self]
  have h0 : cross1 G (v₁ - v₁') u = 0 := (mem_ker2.1 hu).2 _ hk
  rw [cross1_comm hG, cross1_def, Matrix.mulVec_sub, dotProduct_sub] at h0
  rw [cross2_def, cross2_def, dotProduct_add, dotProduct_add]
  linear_combination h0

/-- `β₂` is symmetric. -/
theorem cross2_symm {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {u v u₁ v₁ : ι → K}
    (hu1 : (coeffMat 0 G).mulVec u₁ = -(coeffMat 1 G).mulVec u)
    (hv1 : (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v) :
    cross2 G u v v₁ = cross2 G v u u₁ := by
  rw [cross2_def, cross2_def, dotProduct_add, dotProduct_add]
  have e1 : u ⬝ᵥ (coeffMat 2 G).mulVec v = v ⬝ᵥ (coeffMat 2 G).mulVec u := by
    rw [dot_mulVec_symm (coeffMat_isSymm hG 2), dotProduct_comm]
  have e2 : u ⬝ᵥ (coeffMat 1 G).mulVec v₁ = v ⬝ᵥ (coeffMat 1 G).mulVec u₁ := by
    calc u ⬝ᵥ (coeffMat 1 G).mulVec v₁
        = (coeffMat 1 G).mulVec u ⬝ᵥ v₁ := dot_mulVec_symm (coeffMat_isSymm hG 1) _ _
      _ = -((coeffMat 0 G).mulVec u₁ ⬝ᵥ v₁) := by rw [hu1, neg_dotProduct, neg_neg]
      _ = -(u₁ ⬝ᵥ (coeffMat 0 G).mulVec v₁) := by
          rw [dot_mulVec_symm (coeffMat_isSymm hG 0)]
      _ = u₁ ⬝ᵥ (coeffMat 1 G).mulVec v := by rw [hv1, dotProduct_neg, neg_neg]
      _ = (coeffMat 1 G).mulVec u₁ ⬝ᵥ v := dot_mulVec_symm (coeffMat_isSymm hG 1) _ _
      _ = v ⬝ᵥ (coeffMat 1 G).mulVec u₁ := dotProduct_comm _ _
  rw [e1, e2]

/-- A vector of `ker G₀` whose image under `G₁` lies in the range of `G₀` belongs to `K₂`. -/
theorem mem_ker2_of {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {v y : ι → K}
    (h0 : (coeffMat 0 G).mulVec v = 0)
    (h1 : (coeffMat 0 G).mulVec y + (coeffMat 1 G).mulVec v = 0) : v ∈ ker2 G := by
  refine mem_ker2.2 ⟨mem_ker0.2 h0, fun u hu => ?_⟩
  have : (coeffMat 1 G).mulVec v = -(coeffMat 0 G).mulVec y := eq_neg_of_add_eq_zero_right h1
  rw [cross1_def, this, dotProduct_neg, dot_coeffMat_zero hG hu, neg_zero]

/-- `K₂ = {v(0) : G v ∈ x² K⟦X⟧^ι}`. -/
theorem ker2_eq_layer {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) : ker2 G = layer G 2 := by
  ext v
  constructor
  · intro hv
    obtain ⟨v₁, hv₁⟩ := exists_v1 hG hv
    refine ⟨lift3 v v₁ 0, fun j => lift3_constantCoeff _ _ _ j, fun j => ?_⟩
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · have := coeff_zero_mulVec G (lift3 v v₁ 0)
      rw [lift3_coeff_zero, mem_ker0.1 (mem_ker2.1 hv).1] at this
      exact congrFun this j
    · have := coeff_one_mulVec G (lift3 v v₁ 0)
      rw [lift3_coeff_zero, lift3_coeff_one, hv₁, neg_add_cancel] at this
      exact congrFun this j
  · rintro ⟨V, hV0, hdvd⟩
    have hc : ∀ m, m < 2 → ∀ j, PowerSeries.coeff m (G.mulVec V j) = 0 := fun m hm j =>
      (PowerSeries.X_pow_dvd_iff.1 (hdvd j)) m hm
    have hv0 : (fun j => PowerSeries.coeff 0 (V j)) = v := by
      funext j
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hV0]
    have h0 := coeff_zero_mulVec G V
    rw [hv0] at h0
    have h1 := coeff_one_mulVec G V
    rw [hv0] at h1
    refine mem_ker2_of hG (y := fun j => PowerSeries.coeff 1 (V j)) ?_ ?_
    · rw [← h0]; funext j; exact hc 0 (by norm_num) j
    · rw [← h1]; funext j; exact hc 1 (by norm_num) j

/-- A vector with a lift killed by `G` modulo `x³` belongs to `K₂`, and `β₂` pairs it trivially
with `K₂`. -/
theorem layer3_cross2 {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {v : ι → K} (hv : v ∈ layer G 3) :
    v ∈ ker2 G ∧ ∀ u ∈ ker2 G, ∀ v₁ : ι → K,
      (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v → cross2 G u v v₁ = 0 := by
  obtain ⟨V, hV0, hdvd⟩ := hv
  have hc : ∀ m, m < 3 → ∀ j, PowerSeries.coeff m (G.mulVec V j) = 0 := fun m hm j =>
    (PowerSeries.X_pow_dvd_iff.1 (hdvd j)) m hm
  have hv0 : (fun j => PowerSeries.coeff 0 (V j)) = v := by
    funext j
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hV0]
  have h0 := coeff_zero_mulVec G V
  have h1 := coeff_one_mulVec G V
  have h2 := coeff_two_mulVec G V
  rw [hv0] at h0 h1 h2
  set y₁ : ι → K := fun j => PowerSeries.coeff 1 (V j)
  set y₂ : ι → K := fun j => PowerSeries.coeff 2 (V j)
  have e0 : (coeffMat 0 G).mulVec v = 0 := by
    rw [← h0]; funext j; exact hc 0 (by norm_num) j
  have e1 : (coeffMat 0 G).mulVec y₁ + (coeffMat 1 G).mulVec v = 0 := by
    rw [← h1]; funext j; exact hc 1 (by norm_num) j
  have e2 : (coeffMat 0 G).mulVec y₂ + (coeffMat 1 G).mulVec y₁ + (coeffMat 2 G).mulVec v = 0 := by
    rw [← h2]; funext j; exact hc 2 (by norm_num) j
  refine ⟨mem_ker2_of hG e0 e1, fun u hu v₁ hv₁ => ?_⟩
  have hy₁ : (coeffMat 0 G).mulVec y₁ = -(coeffMat 1 G).mulVec v := eq_neg_of_add_eq_zero_left e1
  rw [cross2_indep hG hu hv₁ hy₁, cross2_def]
  have : (coeffMat 2 G).mulVec v + (coeffMat 1 G).mulVec y₁ = -(coeffMat 0 G).mulVec y₂ := by
    rw [eq_neg_iff_add_eq_zero, ← e2]; abel
  rw [this, dotProduct_neg, dot_coeffMat_zero hG (mem_ker2.1 hu).1, neg_zero]

/-- If `β₂` is nondegenerate, the third layer vanishes. -/
theorem layer3_eq_bot_of_nondeg {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hnd : Cross2NondegK G) :
    layer G 3 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := layer3_cross2 hG hv
  simp [hnd v h1 h2]

/-- A vector of `K₂` that `β₂` pairs trivially with `K₂` has a lift killed by `G` modulo `x³`. -/
theorem mem_layer3_of {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {v : ι → K} (hv : v ∈ ker2 G)
    (h : ∀ u ∈ ker2 G, ∀ v₁ : ι → K,
      (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v → cross2 G u v v₁ = 0) :
    v ∈ layer G 3 := by
  obtain ⟨v₁, hv₁⟩ := exists_v1 hG hv
  set c : ι → K := (coeffMat 2 G).mulVec v + (coeffMat 1 G).mulVec v₁ with hc
  -- solve `G₁ k + G₀ z = -c`, `G₀ k = 0` by the Fredholm alternative for a symmetric block matrix
  have hS : (Matrix.fromBlocks (coeffMat 1 G) (coeffMat 0 G) (coeffMat 0 G)
      (0 : Matrix ι ι K)).IsSymm :=
    Matrix.IsSymm.fromBlocks (coeffMat_isSymm hG 1) (coeffMat_isSymm hG 0).eq
      Matrix.isSymm_zero
  obtain ⟨Y, hY⟩ := symm_range_of_orth hS (Sum.elim (-c) 0) (by
    intro U hU
    rw [Matrix.fromBlocks_mulVec] at hU
    have hU1 : (coeffMat 1 G).mulVec (U ∘ Sum.inl) + (coeffMat 0 G).mulVec (U ∘ Sum.inr) = 0 := by
      funext j; exact congrFun hU (Sum.inl j)
    have hU2 : (coeffMat 0 G).mulVec (U ∘ Sum.inl) = 0 := by
      funext j
      have := congrFun hU (Sum.inr j)
      simpa using this
    have hk : U ∘ Sum.inl ∈ ker2 G :=
      mem_ker2_of hG (y := U ∘ Sum.inr) hU2 (by rw [add_comm]; exact hU1)
    have hUe : U = Sum.elim (U ∘ Sum.inl) (U ∘ Sum.inr) := (Sum.elim_comp_inl_inr U).symm
    rw [hUe, sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_zero, add_zero,
      hc, ← cross2_def, h _ hk v₁ hv₁, neg_zero])
  rw [Matrix.fromBlocks_mulVec] at hY
  set k : ι → K := Y ∘ Sum.inl
  set z : ι → K := Y ∘ Sum.inr
  have hY1 : (coeffMat 1 G).mulVec k + (coeffMat 0 G).mulVec z = -c := by
    funext j; exact congrFun hY (Sum.inl j)
  have hY2 : (coeffMat 0 G).mulVec k = 0 := by
    funext j
    have := congrFun hY (Sum.inr j)
    simpa using this
  refine ⟨lift3 v (v₁ + k) z, fun j => lift3_constantCoeff _ _ _ j, fun j => ?_⟩
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · have := coeff_zero_mulVec G (lift3 v (v₁ + k) z)
    rw [lift3_coeff_zero, mem_ker0.1 (mem_ker2.1 hv).1] at this
    exact congrFun this j
  · have := coeff_one_mulVec G (lift3 v (v₁ + k) z)
    rw [lift3_coeff_zero, lift3_coeff_one, Matrix.mulVec_add, hv₁, hY2, add_zero,
      neg_add_cancel] at this
    exact congrFun this j
  · have := coeff_two_mulVec G (lift3 v (v₁ + k) z)
    rw [lift3_coeff_zero, lift3_coeff_one, lift3_coeff_two, Matrix.mulVec_add] at this
    have hz : (coeffMat 0 G).mulVec z + ((coeffMat 1 G).mulVec v₁ + (coeffMat 1 G).mulVec k) +
        (coeffMat 2 G).mulVec v = 0 := by
      have : (coeffMat 0 G).mulVec z + ((coeffMat 1 G).mulVec v₁ + (coeffMat 1 G).mulVec k) +
          (coeffMat 2 G).mulVec v = ((coeffMat 1 G).mulVec k + (coeffMat 0 G).mulVec z) + c := by
        rw [hc]; abel
      rw [this, hY1, neg_add_cancel]
    rw [hz] at this
    exact congrFun this j

/-- If `β₂` is nondegenerate, `G(x)⁻¹` has a pole of order at most `2`. -/
theorem cross2_pole_le_two {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hdet : G.det ≠ 0)
    (hnd : Cross2NondegK G) : poleOrderInv G ≤ 2 := by
  by_contra hlt
  push Not at hlt
  set p := poleOrderInv G with hp
  have hGH := mul_scaledInv hdet (matOrdGE_inv G)
  rw [← hp] at hGH
  have h0 : coeffMat 0 G * coeffMat 0 (scaledInv G p) = 0 := by
    rw [← coeffMat_zero_mul, hGH, coeffMat_X_pow_smul_one, if_neg (by omega)]
  have h1 : coeffMat 0 G * coeffMat 1 (scaledInv G p) +
      coeffMat 1 G * coeffMat 0 (scaledInv G p) = 0 := by
    rw [← coeffMat_one_mul, hGH, coeffMat_X_pow_smul_one, if_neg (by omega)]
  have h2 : coeffMat 0 G * coeffMat 2 (scaledInv G p) +
      coeffMat 1 G * coeffMat 1 (scaledInv G p) + coeffMat 2 G * coeffMat 0 (scaledInv G p) = 0 := by
    rw [← coeffMat_two_mul, hGH, coeffMat_X_pow_smul_one, if_neg (by omega)]
  apply coeffMat_zero_scaledInv_ne_zero G (by omega)
  rw [← hp]
  refine matrix_eq_zero_of_mulVec fun w => ?_
  have e0 : (coeffMat 0 G).mulVec ((coeffMat 0 (scaledInv G p)).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  have e1 : (coeffMat 0 G).mulVec ((coeffMat 1 (scaledInv G p)).mulVec w) +
      (coeffMat 1 G).mulVec ((coeffMat 0 (scaledInv G p)).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h1, Matrix.zero_mulVec]
  have e2 : (coeffMat 0 G).mulVec ((coeffMat 2 (scaledInv G p)).mulVec w) +
      (coeffMat 1 G).mulVec ((coeffMat 1 (scaledInv G p)).mulVec w) +
      (coeffMat 2 G).mulVec ((coeffMat 0 (scaledInv G p)).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
      ← Matrix.add_mulVec, h2, Matrix.zero_mulVec]
  have hmem := mem_ker2_of hG e0 e1
  apply hnd _ hmem
  intro u hu v₁ hv₁
  have hy₁ := eq_neg_of_add_eq_zero_left e1
  rw [cross2_indep hG hu hv₁ hy₁, cross2_def]
  have : (coeffMat 2 G).mulVec ((coeffMat 0 (scaledInv G p)).mulVec w) +
      (coeffMat 1 G).mulVec ((coeffMat 1 (scaledInv G p)).mulVec w) =
      -(coeffMat 0 G).mulVec ((coeffMat 2 (scaledInv G p)).mulVec w) := by
    rw [eq_neg_iff_add_eq_zero, ← e2]; abel
  rw [this, dotProduct_neg, dot_coeffMat_zero hG (mem_ker2.1 hu).1, neg_zero]

/-- If `G(x)⁻¹` has a pole of order at most `2`, its coefficient `C₂ = [x⁻²] G(x)⁻¹` satisfies
`C₂ w ∈ K₂` and `β₂(u, C₂ w) = u · w` for `u ∈ K₂`. -/
theorem cross2_coeff {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hdet : G.det ≠ 0)
    (hp : poleOrderInv G ≤ 2) (w : ι → K) :
    (invCoeff G (-2)).mulVec w ∈ ker2 G ∧
      ∀ u ∈ ker2 G, ∀ v₁ : ι → K,
        (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec ((invCoeff G (-2)).mulVec w) →
        cross2 G u ((invCoeff G (-2)).mulVec w) v₁ = u ⬝ᵥ w := by
  have hord : MatOrdGE (invLaurent G) (-((2 : ℕ) : ℤ)) :=
    (matOrdGE_inv G).mono (by
      have : (poleOrderInv G : ℤ) ≤ 2 := by exact_mod_cast hp
      push_cast
      linarith)
  have hGH := mul_scaledInv hdet hord
  have h0 : coeffMat 0 G * coeffMat 0 (scaledInv G 2) = 0 := by
    rw [← coeffMat_zero_mul, hGH, coeffMat_X_pow_smul_one, if_neg (by omega)]
  have h1 : coeffMat 0 G * coeffMat 1 (scaledInv G 2) +
      coeffMat 1 G * coeffMat 0 (scaledInv G 2) = 0 := by
    rw [← coeffMat_one_mul, hGH, coeffMat_X_pow_smul_one, if_neg (by omega)]
  have h2 : coeffMat 0 G * coeffMat 2 (scaledInv G 2) +
      coeffMat 1 G * coeffMat 1 (scaledInv G 2) + coeffMat 2 G * coeffMat 0 (scaledInv G 2) = 1 := by
    rw [← coeffMat_two_mul, hGH, coeffMat_X_pow_smul_one, if_pos rfl]
  have hres : invCoeff G (-2) = coeffMat 0 (scaledInv G 2) := by
    rw [coeffMat_scaledInv]; norm_num
  rw [hres]
  have e0 : (coeffMat 0 G).mulVec ((coeffMat 0 (scaledInv G 2)).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  have e1 : (coeffMat 0 G).mulVec ((coeffMat 1 (scaledInv G 2)).mulVec w) +
      (coeffMat 1 G).mulVec ((coeffMat 0 (scaledInv G 2)).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h1, Matrix.zero_mulVec]
  have e2 : (coeffMat 0 G).mulVec ((coeffMat 2 (scaledInv G 2)).mulVec w) +
      (coeffMat 1 G).mulVec ((coeffMat 1 (scaledInv G 2)).mulVec w) +
      (coeffMat 2 G).mulVec ((coeffMat 0 (scaledInv G 2)).mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
      ← Matrix.add_mulVec, h2, Matrix.one_mulVec]
  refine ⟨mem_ker2_of hG e0 e1, fun u hu v₁ hv₁ => ?_⟩
  have hy₁ := eq_neg_of_add_eq_zero_left e1
  rw [cross2_indep hG hu hv₁ hy₁, cross2_def]
  have : (coeffMat 2 G).mulVec ((coeffMat 0 (scaledInv G 2)).mulVec w) +
      (coeffMat 1 G).mulVec ((coeffMat 1 (scaledInv G 2)).mulVec w) =
      w - (coeffMat 0 G).mulVec ((coeffMat 2 (scaledInv G 2)).mulVec w) :=
    eq_sub_of_add_eq ((by abel : _ = _).trans e2)
  rw [this, dotProduct_sub, dot_coeffMat_zero hG (mem_ker2.1 hu).1, sub_zero]

/-- Proposition 5.3 for an arbitrary coefficient field and index type: the Smith counts and the
characterization of nondegenerate `β₂`. -/
theorem cross2_counts {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {s : Multiset ℕ} (hs : IsSmith G s) :
    (s.filter fun e => 1 ≤ e).card = finrank K (ker0 G) ∧
    (s.filter fun e => 2 ≤ e).card = finrank K (ker2 G) ∧
    (Cross2NondegK G ↔ ∀ e ∈ s, e ≤ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(smith_main hs).2.1]
    congr 1
  · rw [ker2_eq_layer hG, finrank_layer hs 2]
  · have h3 := finrank_layer hs 3
    constructor
    · intro hnd e he
      by_contra hlt
      push Not at hlt
      rw [layer3_eq_bot_of_nondeg hG hnd, finrank_bot] at h3
      have : e ∈ s.filter fun x => 3 ≤ x := Multiset.mem_filter.2 ⟨he, by omega⟩
      rw [Multiset.card_eq_zero.1 h3.symm] at this
      simp at this
    · intro hle v hv h
      have hmem := mem_layer3_of hG hv h
      have h0 : finrank K (layer G 3) = 0 := by
        rw [h3, Multiset.card_eq_zero, Multiset.filter_eq_nil]
        intro e he
        have := hle e he
        omega
      rw [Submodule.finrank_eq_zero] at h0
      rw [h0] at hmem
      simpa using hmem

/-- Paper label: prop:two-step-residue -/
theorem prop_two_step_residue : Stmt_prop_two_step_residue := by
  intro m G hG hdet
  refine ⟨fun v hv => exists_v1 hG hv, fun v _ v₁ v₁' h1 h1' u hu => cross2_indep hG hu h1 h1',
    fun u _ v _ u₁ v₁ hu1 hv1 => cross2_symm hG hu1 hv1, fun s hs => cross2_counts hG hs, ?_⟩
  intro hnd w
  exact cross2_coeff hG hdet (cross2_pole_le_two hG hdet hnd) w

example : Stmt_prop_two_step_residue := prop_two_step_residue

end Virasoro
