import Virasoro.Proofs.P2Sec11LayerSum1
import Virasoro.Proofs.P2Sec11Congruence

/-!
# Proposition 11.2(ii), first step: the adapted basis (paper.tex l.2463–2472)

For the columns `v_a(x)` of `U(x)` with `B_x(v_a(x),v_b(x)) = δ_{ab} x^{e_a} u_a(x)`:
`v_a(x) ∈ 𝒥^{(e_a)}`, and for each `i` the layer of order `i` is spanned by the vectors
`v_a(0)` with `e_a ≥ i`.
-/

namespace Virasoro

set_option linter.unusedSectionVars false

open PowerSeries Matrix

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {G : Matrix ι ι K⟦X⟧} {w : ι → ι → K⟦X⟧} {e : ι → ℕ} {u : ι → K⟦X⟧}

/-- The rows `w a` form a unimodular matrix and `w_aᵀ G w_b = δ_{ab} x^{e_a} u_a` with units
`u_a`. -/
structure OrthBasis (G : Matrix ι ι K⟦X⟧) (w : ι → ι → K⟦X⟧) (e : ι → ℕ) (u : ι → K⟦X⟧) :
    Prop where
  unit : IsUnit (Matrix.of w).det
  hu : ∀ a, IsUnit (u a)
  diag : ∀ a, bf G (w a) (w a) = (X : K⟦X⟧) ^ e a * u a
  orth : ∀ a b, a ≠ b → bf G (w a) (w b) = 0

/-- The value `v_a(0)`. -/
noncomputable def val0 (w : ι → ι → K⟦X⟧) (a : ι) : ι → K := fun Y => constantCoeff (w a Y)

namespace OrthBasis

theorem gram (h : OrthBasis G w e u) :
    Matrix.of w * G * (Matrix.of w)ᵀ = Matrix.diagonal fun a => (X : K⟦X⟧) ^ e a * u a := by
  refine Matrix.ext fun a b => ?_
  rw [gram_entry, Matrix.diagonal_apply]
  split_ifs with hab
  · rw [← hab, h.diag]
  · exact h.orth a b hab

/-- `G v_a = x^{e_a} u_a · (column a of the inverse)`. -/
theorem mulVec_row (h : OrthBasis G w e u) (a Y : ι) :
    (G *ᵥ w a) Y = (Matrix.of w)⁻¹ Y a * ((X : K⟦X⟧) ^ e a * u a) := by
  have h1 : G * (Matrix.of w)ᵀ =
      (Matrix.of w)⁻¹ * Matrix.diagonal fun a => (X : K⟦X⟧) ^ e a * u a := by
    rw [← h.gram, Matrix.mul_assoc (Matrix.of w), ← Matrix.mul_assoc (Matrix.of w)⁻¹,
      Matrix.nonsing_inv_mul _ h.unit, Matrix.one_mul]
  have h2 : (G *ᵥ w a) Y = (G * (Matrix.of w)ᵀ) Y a := by
    simp only [Matrix.mul_apply, mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
  rw [h2, h1, Matrix.mul_diagonal]

theorem psFam (h : OrthBasis G w e u) (a : ι) {j : ℕ} (hj : j ≤ e a) :
    PSFam G j (val0 w a) (w a) := by
  refine ⟨fun _ => rfl, fun Y => ?_⟩
  rw [h.mulVec_row]
  exact Dvd.dvd.mul_left ((pow_dvd_pow _ hj).trans (dvd_mul_right _ _)) _

/-- `v_bᵀ G V = x^{e_b} u_b y_b` for `V = ∑_a y_a v_a`. -/
theorem bf_coord (h : OrthBasis G w e u) (y : ι → K⟦X⟧) (b : ι) :
    bf G (w b) ((Matrix.of w)ᵀ *ᵥ y) = (X : K⟦X⟧) ^ e b * u b * y b := by
  have h1 : bf G (w b) ((Matrix.of w)ᵀ *ᵥ y) =
      ((Matrix.of w * G * (Matrix.of w)ᵀ) *ᵥ y) b := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl
  rw [h1, h.gram, Matrix.mulVec_diagonal]

theorem linearIndependent_val0 (h : OrthBasis G w e u) : LinearIndependent K (val0 w) := by
  have hdet : ((Matrix.of w).map (constantCoeff (R := K))).det = constantCoeff (Matrix.of w).det :=
    (RingHom.map_det (constantCoeff (R := K)) (Matrix.of w)).symm
  have hunit : IsUnit ((Matrix.of w).map (constantCoeff (R := K))) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_iff_constantCoeff.1 h.unit
  exact Matrix.linearIndependent_rows_iff_isUnit.2 hunit

/-- The layer of order `j` is spanned by the `v_a(0)` with `e_a ≥ j`. -/
theorem layer_eq_span (h : OrthBasis G w e u) (j : ℕ) :
    layer G j = Submodule.span K (val0 w '' {a | j ≤ e a}) := by
  apply le_antisymm
  · rintro v ⟨V, hV0, hdvd⟩
    have hWT : IsUnit ((Matrix.of w)ᵀ).det := by rw [det_transpose]; exact h.unit
    set y : ι → K⟦X⟧ := ((Matrix.of w)ᵀ)⁻¹ *ᵥ V with hy
    have hVy : (Matrix.of w)ᵀ *ᵥ y = V := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hWT, Matrix.one_mulVec]
    have hy0 : ∀ b, e b < j → constantCoeff (y b) = 0 := by
      intro b hb
      have h1 : (X : K⟦X⟧) ^ j ∣ (X : K⟦X⟧) ^ e b * u b * y b := by
        rw [← h.bf_coord y b, hVy]
        exact dvd_dot_right hdvd
      have h2 : (X : K⟦X⟧) ^ e b * X ∣ (X : K⟦X⟧) ^ e b * (u b * y b) := by
        rw [← pow_succ, ← mul_assoc]
        exact (pow_dvd_pow _ hb).trans h1
      have h3 : (X : K⟦X⟧) ∣ u b * y b :=
        (mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).1 h2
      have h4 : (X : K⟦X⟧) ∣ y b := ((h.hu b).dvd_mul_left).1 h3
      rw [X_dvd_iff] at h4
      exact h4
    have hv : v = ∑ a, constantCoeff (y a) • val0 w a := by
      funext Y
      rw [← hV0 Y, ← hVy]
      simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, val0]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [hv]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : j ≤ e a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
    · rw [hy0 a (not_le.1 ha), zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨w a, (h.psFam a ha).1, (h.psFam a ha).2⟩

/-- `[x^i] v_bᵀ G v_a = δ_{ab} u_a(0)` for `e_a = i`. -/
theorem psForm_val (h : OrthBasis G w e u) (a b : ι) :
    psForm G (e a) (w a) (w b) = if a = b then constantCoeff (u a) else 0 := by
  rw [psForm]
  have e1 : w b ⬝ᵥ G *ᵥ w a = bf G (w b) (w a) := rfl
  rw [e1]
  split_ifs with hab
  · rw [← hab, h.diag]
    have := coeff_X_pow_mul (u a) (e a) 0
    rw [zero_add] at this
    rw [this, coeff_zero_eq_constantCoeff_apply]
  · rw [h.orth b a (Ne.symm hab), map_zero]

end OrthBasis

end Virasoro
