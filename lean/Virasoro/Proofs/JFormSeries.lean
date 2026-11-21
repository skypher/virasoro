import Virasoro.Proofs.SmithLayers

/-!
# The top coefficient of `v(x)ᵀ G(x) u(x)` for families in a layer (proof of Lemma 5.4)

For a symmetric matrix `G` over `K⟦x⟧` and families `u(x), v(x)` with `G u(x), G v(x) ∈ x^i`,
the coefficient of `x^i` in `v(x)ᵀ G(x) u(x)` is `v(0)ᵀ [x^i](G u(x)) = u(0)ᵀ [x^i](G v(x))`,
so it depends only on `u(0)` and `v(0)` (paper.tex l.628–632).  If `x^k G⁻¹` is regular, the
family `x^k G⁻¹ w` has value `[x^{-k}]G⁻¹ w` at `x = 0` and `G` maps it to `x^k w`
(paper.tex l.641–649).

Consumer: `lem_top_coefficient` in `Virasoro/Proofs/Sec5TopCoeff.lean`.
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `V` is a power-series family for `v` in the `i`-th layer of `G`: `V(0) = v` and
`G V ∈ x^i K⟦x⟧`. -/
def PSFam (G : Matrix ι ι K⟦X⟧) (i : ℕ) (v : ι → K) (V : ι → K⟦X⟧) : Prop :=
  (∀ j, PowerSeries.constantCoeff (V j) = v j) ∧
    ∀ j, (PowerSeries.X : K⟦X⟧) ^ i ∣ (G.mulVec V) j

/-- `[x^i] v(x)ᵀ G(x) u(x)`. -/
noncomputable def psForm (G : Matrix ι ι K⟦X⟧) (i : ℕ) (Vu Vv : ι → K⟦X⟧) : K :=
  PowerSeries.coeff i (Vv ⬝ᵥ G.mulVec Vu)

/-- `[x^i] G(x) v(x)`. -/
noncomputable def topVec (G : Matrix ι ι K⟦X⟧) (i : ℕ) (V : ι → K⟦X⟧) : ι → K :=
  fun j => PowerSeries.coeff i (G.mulVec V j)

omit [DecidableEq ι] in
theorem coeff_dot_of_dvd (i : ℕ) (V P : ι → K⟦X⟧)
    (hP : ∀ j, (PowerSeries.X : K⟦X⟧) ^ i ∣ P j) :
    PowerSeries.coeff i (V ⬝ᵥ P) =
      (fun j => PowerSeries.constantCoeff (V j)) ⬝ᵥ fun j => PowerSeries.coeff i (P j) := by
  choose Q hQ using hP
  simp only [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hQ j, ← mul_assoc, mul_comm (V j), mul_assoc]
  simp [PowerSeries.coeff_X_pow_mul']

omit [DecidableEq ι] in
theorem dot_mulVec_comm {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (U V : ι → K⟦X⟧) :
    V ⬝ᵥ G.mulVec U = U ⬝ᵥ G.mulVec V := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG.eq, dotProduct_comm]

theorem psForm_right {G : Matrix ι ι K⟦X⟧} {i : ℕ} {Vu : ι → K⟦X⟧}
    (hu : ∀ j, (PowerSeries.X : K⟦X⟧) ^ i ∣ (G.mulVec Vu) j) (Vv : ι → K⟦X⟧) :
    psForm G i Vu Vv = (fun j => PowerSeries.constantCoeff (Vv j)) ⬝ᵥ topVec G i Vu :=
  coeff_dot_of_dvd i Vv _ hu

theorem psForm_symm {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (i : ℕ) (Vu Vv : ι → K⟦X⟧) :
    psForm G i Vu Vv = psForm G i Vv Vu := by
  rw [psForm, psForm, dot_mulVec_comm hG]

theorem psForm_left {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {i : ℕ} {Vv : ι → K⟦X⟧}
    (hv : ∀ j, (PowerSeries.X : K⟦X⟧) ^ i ∣ (G.mulVec Vv) j) (Vu : ι → K⟦X⟧) :
    psForm G i Vu Vv = (fun j => PowerSeries.constantCoeff (Vu j)) ⬝ᵥ topVec G i Vv := by
  rw [psForm_symm hG]
  exact psForm_right hv Vu

/-- The top coefficient does not depend on the families. -/
theorem psForm_congr {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {i : ℕ} {u v : ι → K}
    {Vu Vu' Vv Vv' : ι → K⟦X⟧} (hu : PSFam G i u Vu) (hu' : PSFam G i u Vu')
    (hv : PSFam G i v Vv) (hv' : PSFam G i v Vv') :
    psForm G i Vu Vv = psForm G i Vu' Vv' := by
  have e1 : (fun j => PowerSeries.constantCoeff (Vu j)) =
      fun j => PowerSeries.constantCoeff (Vu' j) := by
    funext j
    rw [hu.1, hu'.1]
  have e2 : (fun j => PowerSeries.constantCoeff (Vv j)) =
      fun j => PowerSeries.constantCoeff (Vv' j) := by
    funext j
    rw [hv.1, hv'.1]
  rw [psForm_left hG hv.2 Vu, e1, ← psForm_left hG hv.2 Vu', psForm_right hu'.2 Vv, e2,
    ← psForm_right hu'.2 Vv']

omit [DecidableEq ι] in
theorem coeff_mulVec_C (G : Matrix ι ι K⟦X⟧) (n : ℕ) (u : ι → K) (j : ι) :
    PowerSeries.coeff n (G.mulVec (fun k => PowerSeries.C (u k)) j) =
      (coeffMat n G).mulVec u j := by
  simp [Matrix.mulVec, dotProduct, coeffMat, PowerSeries.coeff_mul_C]

omit [DecidableEq ι] in
theorem mulVec_lin (G : Matrix ι ι K⟦X⟧) (u u₁ : ι → K) (j : ι) :
    G.mulVec (fun k => PowerSeries.C (u k) + PowerSeries.X * PowerSeries.C (u₁ k)) j =
      G.mulVec (fun k => PowerSeries.C (u k)) j +
        PowerSeries.X * G.mulVec (fun k => PowerSeries.C (u₁ k)) j := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem coeff_zero_mulVec_lin (G : Matrix ι ι K⟦X⟧) (u u₁ : ι → K) (j : ι) :
    PowerSeries.coeff 0
        (G.mulVec (fun k => PowerSeries.C (u k) + PowerSeries.X * PowerSeries.C (u₁ k)) j) =
      (coeffMat 0 G).mulVec u j := by
  rw [mulVec_lin, map_add, PowerSeries.coeff_zero_X_mul, add_zero, coeff_mulVec_C]

theorem coeff_succ_mulVec_lin (G : Matrix ι ι K⟦X⟧) (n : ℕ) (u u₁ : ι → K) (j : ι) :
    PowerSeries.coeff (n + 1)
        (G.mulVec (fun k => PowerSeries.C (u k) + PowerSeries.X * PowerSeries.C (u₁ k)) j) =
      (coeffMat (n + 1) G).mulVec u j + (coeffMat n G).mulVec u₁ j := by
  rw [mulVec_lin, map_add, PowerSeries.coeff_succ_X_mul, coeff_mulVec_C, coeff_mulVec_C]

/-- A vector of a layer `i ≥ 1` lies in `ker G(0)`. -/
theorem coeffMat_zero_mulVec_of_psFam {G : Matrix ι ι K⟦X⟧} {i : ℕ} (hi : 1 ≤ i) {v : ι → K}
    {V : ι → K⟦X⟧} (h : PSFam G i v V) : (coeffMat 0 G).mulVec v = 0 := by
  have e : (fun j => PowerSeries.constantCoeff (V j)) = v := funext h.1
  have hc := constantCoeff_mulVec G V
  rw [e] at hc
  rw [← hc]
  funext j
  obtain ⟨Q, hQ⟩ := h.2 j
  show PowerSeries.constantCoeff (G.mulVec V j) = 0
  rw [hQ, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), zero_mul]

/-- The family `x^k G⁻¹ w`: its value at `x = 0` is `[x^{-k}] G⁻¹ w`, and `G` maps it to
`x^k w`. -/
theorem scaled_psFam {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) {k : ℕ}
    (hp : MatOrdGE (invLaurent G) (-(k : ℤ))) (w : ι → K) :
    PSFam G k ((invCoeff G (-(k : ℤ))).mulVec w)
        ((scaledInv G k).mulVec fun j => PowerSeries.C (w j)) ∧
      topVec G k ((scaledInv G k).mulVec fun j => PowerSeries.C (w j)) = w := by
  have hmul : G.mulVec ((scaledInv G k).mulVec fun j => PowerSeries.C (w j)) =
      fun j => (PowerSeries.X : K⟦X⟧) ^ k * PowerSeries.C (w j) := by
    rw [Matrix.mulVec_mulVec, mul_scaledInv hdet hp]
    funext j
    simp [Matrix.smul_mulVec]
  refine ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩
  · have h1 := congrFun (constantCoeff_mulVec (scaledInv G k) fun j => PowerSeries.C (w j)) j
    have h2 : (fun j => PowerSeries.constantCoeff (PowerSeries.C (w j) : K⟦X⟧)) = w := by
      funext j
      simp
    rw [h2, coeffMat_scaledInv] at h1
    rw [h1]
    simp
  · rw [hmul]
    exact Dvd.intro _ rfl
  · funext j
    rw [topVec, hmul]
    simp

end Virasoro
