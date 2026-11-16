import Virasoro.Proofs.CrossBasic

/-!
# Proofs: Proposition 5.2 (transverse inverse residue)
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nondegeneracy of the first crossing form on `ker G(0)`. -/
def Cross1NondegK (G : Matrix ι ι K⟦X⟧) : Prop :=
  ∀ v ∈ ker0 G, (∀ u ∈ ker0 G, cross1 G u v = 0) → v = 0

theorem cross1_def (G : Matrix ι ι K⟦X⟧) (u v : ι → K) :
    cross1 G u v = u ⬝ᵥ (coeffMat 1 G).mulVec v := rfl

/-- For `u ∈ ker G₀` and symmetric `G₀`, `u · G₀ y = 0`. -/
theorem dot_coeffMat_zero {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) {u : ι → K} (hu : u ∈ ker0 G)
    (y : ι → K) : u ⬝ᵥ (coeffMat 0 G).mulVec y = 0 := by
  rw [dot_mulVec_symm (coeffMat_isSymm hG 0), mem_ker0.1 hu, zero_dotProduct]

/-- If the first crossing form is nondegenerate, `G(x)⁻¹` has at most a simple pole. -/
theorem cross1_pole_le_one {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hdet : G.det ≠ 0)
    (hnd : Cross1NondegK G) : poleOrderInv G ≤ 1 := by
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
  apply coeffMat_zero_scaledInv_ne_zero G (by omega)
  rw [← hp]
  refine matrix_eq_zero_of_mulVec fun w => ?_
  apply hnd
  · rw [mem_ker0, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  · intro u hu
    have h1' : coeffMat 1 G * coeffMat 0 (scaledInv G p) =
        -(coeffMat 0 G * coeffMat 1 (scaledInv G p)) := eq_neg_of_add_eq_zero_right h1
    rw [cross1_def, Matrix.mulVec_mulVec, h1', Matrix.neg_mulVec, dotProduct_neg,
      ← Matrix.mulVec_mulVec, dot_coeffMat_zero hG hu, neg_zero]

/-- If `G(x)⁻¹` has at most a simple pole, its residue `R` satisfies `R w ∈ ker G₀` and
`β(u, R w) = u · w` for `u ∈ ker G₀`. -/
theorem cross1_residue {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hdet : G.det ≠ 0)
    (hp : poleOrderInv G ≤ 1) (w : ι → K) :
    (invCoeff G (-1)).mulVec w ∈ ker0 G ∧
      ∀ u ∈ ker0 G, cross1 G u ((invCoeff G (-1)).mulVec w) = u ⬝ᵥ w := by
  have hord : MatOrdGE (invLaurent G) (-((1 : ℕ) : ℤ)) :=
    (matOrdGE_inv G).mono (by
      have : (poleOrderInv G : ℤ) ≤ 1 := by exact_mod_cast hp
      push_cast
      linarith)
  have hGH := mul_scaledInv hdet hord
  have h0 : coeffMat 0 G * coeffMat 0 (scaledInv G 1) = 0 := by
    rw [← coeffMat_zero_mul, hGH, coeffMat_X_pow_smul_one, if_neg (by omega)]
  have h1 : coeffMat 0 G * coeffMat 1 (scaledInv G 1) +
      coeffMat 1 G * coeffMat 0 (scaledInv G 1) = 1 := by
    rw [← coeffMat_one_mul, hGH, coeffMat_X_pow_smul_one, if_pos rfl]
  have hres : invCoeff G (-1) = coeffMat 0 (scaledInv G 1) := by
    rw [coeffMat_scaledInv]; norm_num
  rw [hres]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [mem_ker0, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  · have h1' : coeffMat 1 G * coeffMat 0 (scaledInv G 1) =
        1 - coeffMat 0 G * coeffMat 1 (scaledInv G 1) := eq_sub_of_add_eq' h1
    rw [cross1_def, Matrix.mulVec_mulVec, h1', Matrix.sub_mulVec, Matrix.one_mulVec,
      dotProduct_sub, ← Matrix.mulVec_mulVec, dot_coeffMat_zero hG hu, sub_zero]

/-- A multiset of natural numbers bounded by `1` has sum equal to the number of its positive
members. -/
theorem multiset_sum_of_le_one (s : Multiset ℕ) (h : ∀ e ∈ s, e ≤ 1) :
    s.sum = (s.filter fun e => 0 < e).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha := h a (Multiset.mem_cons_self a t)
    have iht := ih fun e he => h e (Multiset.mem_cons_of_mem he)
    by_cases h0 : 0 < a
    · rw [Multiset.filter_cons_of_pos (p := fun e : ℕ => 0 < e) t h0, Multiset.sum_cons,
        Multiset.card_cons, iht]
      omega
    · rw [Multiset.filter_cons_of_neg (p := fun e : ℕ => 0 < e) t h0, Multiset.sum_cons, iht]
      omega

/-- If the determinant valuation equals the nullity, `G(x)⁻¹` has at most a simple pole. -/
theorem pole_le_one_of_order_eq {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0)
    (h : G.det.order = ((finrank K (ker0 G) : ℕ) : ℕ∞)) : poleOrderInv G ≤ 1 := by
  obtain ⟨s, hs⟩ := exists_isSmith hdet
  obtain ⟨h1, h2, h3⟩ := smith_main hs
  have hfilt : (s.filter fun e => 0 < e) = s.filter fun e => e ≠ 0 :=
    Multiset.filter_congr fun e _ => Nat.pos_iff_ne_zero
  have hsum : s.sum = s.countP fun e => e ≠ 0 := by
    rw [h1] at h
    have : s.sum = finrank K (ker0 G) := by exact_mod_cast h
    rw [this, Multiset.countP_eq_card_filter, ← hfilt, ← h2]
  have hone := multiset_pos_eq_one s hsum
  rw [h3]
  refine Multiset.sup_le.2 fun e he => ?_
  by_cases hpos : e ≠ 0
  · exact (hone e he hpos).le
  · have : e = 0 := by omega
    simp [this]

/-- If `G(x)⁻¹` has at most a simple pole, the first crossing form is nondegenerate. -/
theorem cross1_nondeg_of_pole {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hdet : G.det ≠ 0)
    (hp : poleOrderInv G ≤ 1) : Cross1NondegK G := by
  intro v hv hcross
  -- `G₁ v ∈ range G₀`
  obtain ⟨y, hy⟩ := symm_range_of_orth (coeffMat_isSymm hG 0) ((coeffMat 1 G).mulVec v)
    (fun u hu => hcross u (mem_ker0.2 hu))
  -- the lift `v - x y`
  set V := lift3 v (-y) 0 with hV
  have hc0 : ∀ j, PowerSeries.coeff 0 (G.mulVec V j) = 0 := by
    have := coeff_zero_mulVec G V
    rw [hV, lift3_coeff_zero, mem_ker0.1 hv] at this
    exact fun j => congrFun this j
  have hc1 : ∀ j, PowerSeries.coeff 1 (G.mulVec V j) = 0 := by
    have := coeff_one_mulVec G V
    rw [hV, lift3_coeff_zero, lift3_coeff_one, Matrix.mulVec_neg, hy, neg_add_cancel] at this
    exact fun j => congrFun this j
  have hdvd : ∀ j, (PowerSeries.X : K⟦X⟧) ^ 2 ∣ G.mulVec V j := by
    intro j
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · exact hc0 j
    · exact hc1 j
  choose W hW using hdvd
  have hord : MatOrdGE (invLaurent G) (-((1 : ℕ) : ℤ)) :=
    (matOrdGE_inv G).mono (by
      have : (poleOrderInv G : ℤ) ≤ 1 := by exact_mod_cast hp
      push_cast
      linarith)
  have hHG := scaledInv_mul hdet hord
  have key : ∀ j, (PowerSeries.X : K⟦X⟧) * V j =
      (PowerSeries.X : K⟦X⟧) ^ 2 * (scaledInv G 1).mulVec W j := by
    intro j
    have h1 : (scaledInv G 1).mulVec (G.mulVec V) j = (PowerSeries.X : K⟦X⟧) * V j := by
      rw [Matrix.mulVec_mulVec, hHG]
      simp [Matrix.smul_mulVec]
    have h2 : (scaledInv G 1).mulVec (G.mulVec V) j =
        (PowerSeries.X : K⟦X⟧) ^ 2 * (scaledInv G 1).mulVec W j := by
      have : G.mulVec V = (PowerSeries.X : K⟦X⟧) ^ 2 • W := funext fun k => hW k
      rw [this, Matrix.mulVec_smul]
      rfl
    rw [← h1, h2]
  funext j
  have hXne : (PowerSeries.X : K⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  have hVj : V j = (PowerSeries.X : K⟦X⟧) * (scaledInv G 1).mulVec W j := by
    have := key j
    rw [pow_two, mul_assoc] at this
    exact mul_left_cancel₀ hXne this
  have hcc : PowerSeries.constantCoeff (V j) = 0 := by
    rw [hVj]; simp
  rw [hV, lift3_constantCoeff] at hcc
  simpa using hcc

/-- Proposition 5.2 for an arbitrary coefficient field and index type. -/
theorem cross1_main {G : Matrix ι ι K⟦X⟧} (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    (Cross1NondegK G →
      poleOrderInv G ≤ 1 ∧
      ∀ w : ι → K, (invCoeff G (-1)).mulVec w ∈ ker0 G ∧
        ∀ u ∈ ker0 G, cross1 G u ((invCoeff G (-1)).mulVec w) = u ⬝ᵥ w) ∧
    (Cross1NondegK G ↔ G.det.order = ((finrank K (ker0 G) : ℕ) : ℕ∞)) := by
  refine ⟨fun hnd => ⟨cross1_pole_le_one hG hdet hnd,
    cross1_residue hG hdet (cross1_pole_le_one hG hdet hnd)⟩, ?_, ?_⟩
  · intro hnd
    have hp := cross1_pole_le_one hG hdet hnd
    obtain ⟨s, hs⟩ := exists_isSmith hdet
    obtain ⟨h1, h2, h3⟩ := smith_main hs
    rw [h1, h2]
    congr 1
    refine multiset_sum_of_le_one s fun e he => ?_
    rw [h3] at hp
    exact le_trans (Multiset.le_sup he) hp
  · intro h
    exact cross1_nondeg_of_pole hG hdet (pole_le_one_of_order_eq hdet h)

/-- Paper label: prop:transverse-residue -/
theorem prop_transverse_residue : Stmt_prop_transverse_residue := by
  intro m G hG hdet
  exact cross1_main hG hdet

example : Stmt_prop_transverse_residue := prop_transverse_residue

end Virasoro
