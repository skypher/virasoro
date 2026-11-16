import Virasoro.Proofs.Sec5Smith
import Virasoro.Proofs.SmithExist
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-!
# Fredholm alternative for symmetric matrices, and the layers `{v(0) : G v ∈ x^i}`
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fredholm alternative: for a symmetric matrix `A` over a field, a vector orthogonal to
`ker A` lies in the range of `A`. -/
theorem symm_range_of_orth {A : Matrix ι ι K} (hA : A.IsSymm) (w : ι → K)
    (h : ∀ u : ι → K, A.mulVec u = 0 → u ⬝ᵥ w = 0) : ∃ y : ι → K, A.mulVec y = w := by
  by_contra hne
  have hw : w ∉ LinearMap.range A.mulVecLin := by
    rintro ⟨y, hy⟩
    exact hne ⟨y, hy⟩
  obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  set u : ι → K := fun i => f (fun j => if i = j then 1 else 0) with hu
  have hfu : ∀ v : ι → K, f v = u ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp only [dotProduct, hu, smul_eq_mul, mul_comm]
  have hfA : ∀ v : ι → K, f (A.mulVec v) = 0 := by
    intro v
    have : f (A.mulVec v) ∈ (LinearMap.range A.mulVecLin).map f :=
      Submodule.mem_map_of_mem ⟨v, rfl⟩
    rw [hf] at this
    simpa using this
  have hAu : A.mulVec u = 0 := by
    funext i
    have := hfA (Pi.single i 1)
    rw [hfu, dot_mulVec_symm hA] at this
    simpa using this
  exact hfw (by rw [hfu]; exact h u hAu)

/-- The layer `{v(0) : v ∈ K⟦X⟧^ι, G v ∈ x^i K⟦X⟧^ι}`. -/
noncomputable def layer (G : Matrix ι ι K⟦X⟧) (i : ℕ) : Submodule K (ι → K) where
  carrier := {v | ∃ V : ι → K⟦X⟧, (∀ j, PowerSeries.constantCoeff (V j) = v j) ∧
      ∀ j, (PowerSeries.X : K⟦X⟧) ^ i ∣ (G.mulVec V) j}
  add_mem' := by
    rintro v v' ⟨V, hV, hd⟩ ⟨V', hV', hd'⟩
    refine ⟨V + V', fun j => by simp [hV, hV'], fun j => ?_⟩
    rw [Matrix.mulVec_add]
    exact dvd_add (hd j) (hd' j)
  zero_mem' := ⟨0, fun j => by simp, fun j => by simp⟩
  smul_mem' := by
    rintro a v ⟨V, hV, hd⟩
    refine ⟨PowerSeries.C a • V, fun j => by simp [hV], fun j => ?_⟩
    rw [Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hd j) _

theorem constantCoeff_mulVec (A : Matrix ι ι K⟦X⟧) (V : ι → K⟦X⟧) :
    (fun j => PowerSeries.constantCoeff (A.mulVec V j)) =
      (coeffMat 0 A).mulVec fun j => PowerSeries.constantCoeff (V j) := by
  funext j
  simp [Matrix.mulVec, dotProduct, coeffMat, map_sum]

theorem dvd_mulVec {A : Matrix ι ι K⟦X⟧} {V : ι → K⟦X⟧} {d : K⟦X⟧} (h : ∀ j, d ∣ V j) (j : ι) :
    d ∣ A.mulVec V j := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (h k) _

/-- The `0/1` diagonal matrix selecting the indices with `e_j ≥ i`. -/
noncomputable def selDiag (e : ι → ℕ) (i : ℕ) : Matrix ι ι K :=
  Matrix.diagonal fun j => if i ≤ e j then (1 : K) else 0

theorem layer_eq_range {G : Matrix ι ι K⟦X⟧} {e : ι → ℕ} {U V : Matrix ι ι K⟦X⟧}
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hD : U * G * V = Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) (i : ℕ) :
    layer G i = LinearMap.range (coeffMat 0 V * selDiag e i).mulVecLin := by
  have hVV : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv _ hV
  have hUU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul _ hU
  ext v
  constructor
  · rintro ⟨Vv, hV0, hdiv⟩
    -- `W = V⁻¹ Vv`
    set W : ι → K⟦X⟧ := V⁻¹.mulVec Vv with hW
    have hVW : V.mulVec W = Vv := by
      rw [hW, Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
    have hDW : ∀ j, (PowerSeries.X : K⟦X⟧) ^ i ∣ (PowerSeries.X : K⟦X⟧) ^ e j * W j := by
      intro j
      have h1 : (Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i).mulVec W =
          U.mulVec (G.mulVec Vv) := by
        calc (Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i).mulVec W
            = (U * G * V).mulVec W := by rw [hD]
          _ = U.mulVec (G.mulVec (V.mulVec W)) := by
              simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
          _ = U.mulVec (G.mulVec Vv) := by rw [hVW]
      have h2 := dvd_mulVec (A := U) hdiv j
      rw [← h1, Matrix.mulVec_diagonal] at h2
      exact h2
    have hW0 : ∀ j, e j < i → PowerSeries.constantCoeff (W j) = 0 := by
      intro j hj
      have := (PowerSeries.X_pow_dvd_iff.1 (hDW j)) (e j) hj
      have h3 := PowerSeries.coeff_X_pow_mul (W j) (e j) 0
      rw [zero_add] at h3
      rw [h3] at this
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact this
    refine ⟨fun j => PowerSeries.constantCoeff (W j), ?_⟩
    have hv : v = (coeffMat 0 V).mulVec fun j => PowerSeries.constantCoeff (W j) := by
      rw [← constantCoeff_mulVec, hVW]
      funext j
      exact (hV0 j).symm
    rw [hv, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
    congr 1
    funext j
    simp only [selDiag, Matrix.mulVec_diagonal]
    by_cases hj : i ≤ e j
    · simp [hj]
    · simp [hj, hW0 j (by omega)]
  · rintro ⟨w, rfl⟩
    set w' : ι → K := (selDiag e i).mulVec w with hw'
    have hw0 : ∀ j, e j < i → w' j = 0 := by
      intro j hj
      simp [hw', selDiag, Matrix.mulVec_diagonal, show ¬ i ≤ e j by omega]
    refine ⟨V.mulVec fun j => PowerSeries.C (w' j), ?_, ?_⟩
    · intro j
      have := congrFun (constantCoeff_mulVec V fun j => PowerSeries.C (w' j)) j
      simp only [PowerSeries.constantCoeff_C] at this
      rw [this, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
    · intro j
      -- `G V C(w') = U⁻¹ D C(w')`
      have h1 : G.mulVec (V.mulVec fun j => PowerSeries.C (w' j)) =
          U⁻¹.mulVec ((Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i).mulVec
            fun j => PowerSeries.C (w' j)) := by
        rw [← hD, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
      rw [h1]
      refine dvd_mulVec (fun k => ?_) j
      rw [Matrix.mulVec_diagonal]
      by_cases hk : i ≤ e k
      · exact Dvd.dvd.mul_right (pow_dvd_pow _ hk) _
      · rw [hw0 k (by omega)]
        simp

/-- `dim {v(0) : G v ∈ x^i} = #{j : e_j ≥ i}`. -/
theorem finrank_layer {G : Matrix ι ι K⟦X⟧} {s : Multiset ℕ} (hs : IsSmith G s) (i : ℕ) :
    finrank K (layer G i) = (s.filter fun x => i ≤ x).card := by
  classical
  obtain ⟨e, U, V, hU, hV, hD, rfl⟩ := hs
  rw [layer_eq_range hU hV hD i, multiset_filter_card]
  have hr : finrank K (LinearMap.range (coeffMat 0 V * selDiag e i).mulVecLin) =
      (coeffMat 0 V * selDiag e i).rank := rfl
  rw [hr, Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (det_coeffMat_zero_ne_zero hV), selDiag,
    Matrix.rank_diagonal, Fintype.card_subtype]
  congr 1
  ext j
  by_cases hj : i ≤ e j <;> simp [hj]

end Virasoro
