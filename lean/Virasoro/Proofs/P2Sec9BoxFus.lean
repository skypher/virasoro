import Virasoro.Proofs.P2Sec10FusRoots
import Virasoro.Proofs.P2Sec9BoxQuad

/-!
# Theorem 9.2: the fusion polynomial as a product of linear factors in the momenta
(paper.tex l.2133–2138, 2686–2690)

`P_{R,S}(b;Δ₁,Δ₂) = ∏_{p',q'} (λ₁+λ₂+p'b+q'b⁻¹)/2 · (λ₁-λ₂+p'b+q'b⁻¹)/2` with
`Δ_i = (Q²-λ_i²)/4`, as a polynomial in the momentum `λ₁`.
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- `p'b + q'b⁻¹` for `(p',q') = (2i+1-R, 2i'+1-S)`. -/
noncomputable def bet (b : ℂ) (R S : ℕ) (y : ℕ × ℕ) : ℂ :=
  ((2 * (y.1 : ℤ) + 1 - R : ℤ) : ℂ) * b + ((2 * (y.2 : ℤ) + 1 - S : ℤ) : ℂ) * b⁻¹

/-- The paired form of `fusP` is the product (10.9) over all `(p',q')`. -/
theorem fusP_eq_prod (r s : ℕ) (b L M Δa Δb : ℂ) (hL : L ^ 2 = (b + b⁻¹) ^ 2 - 4 * Δa)
    (hM : M ^ 2 = (b + b⁻¹) ^ 2 - 4 * Δb) :
    fusP r s b Δa Δb =
      ∏ y ∈ idxBox r s, ((L + M + bet b r s y) / 2) * ((L - M + bet b r s y) / 2) := by
  set F : ℤ × ℤ → ℂ := fun x =>
    ((L + M + ((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹)) / 2) *
      ((L - M + ((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹)) / 2) with hF
  have h1 : ∏ y ∈ idxBox r s, ((L + M + bet b r s y) / 2) * ((L - M + bet b r s y) / 2) =
      ∏ x ∈ stepRange r ×ˢ stepRange s, F x := by
    unfold idxBox stepRange
    rw [Finset.prod_product, Finset.prod_product, Finset.prod_image (by
      intro i _ j _ h
      have h' : 2 * (i : ℤ) + 1 - r = 2 * (j : ℤ) + 1 - r := h
      omega)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_image (by
      intro i _ j _ h
      have h' : 2 * (i : ℤ) + 1 - s = 2 * (j : ℤ) + 1 - s := h
      omega)]
    refine Finset.prod_congr rfl fun i' _ => ?_
    simp only [hF, bet]
  rw [h1]
  set U := stepRange r ×ˢ stepRange s with hU
  set pos : ℤ × ℤ → Prop := fun x => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2) with hpos
  have hneg : ∏ x ∈ (U.filter fun x => ¬x = (0, 0)).filter (fun x => ¬pos x), F x =
      ∏ x ∈ U.filter pos, F (-x) := by
    refine Finset.prod_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [hU, hpos, Finset.mem_filter, Finset.mem_product, Prod.ext_iff] at hx ⊢
      refine ⟨⟨neg_mem_stepRange hx.1.1.1, neg_mem_stepRange hx.1.1.2⟩, ?_⟩
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
    · intro x hx
      simp only [hU, hpos, Finset.mem_filter, Finset.mem_product, Prod.ext_iff] at hx ⊢
      refine ⟨⟨⟨neg_mem_stepRange hx.1.1, neg_mem_stepRange hx.1.2⟩, ?_⟩, ?_⟩ <;>
        simp only [Prod.fst_neg, Prod.snd_neg] <;> omega
    · intro x _; exact neg_neg x
    · intro x _; exact neg_neg x
    · intro x _; rw [neg_neg]
  have hposf : (U.filter fun x => ¬x = (0, 0)).filter pos = U.filter pos := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun x _ => ?_
    simp only [hpos, Prod.ext_iff]
    omega
  rw [← Finset.prod_filter_mul_prod_filter_not U (fun x => x = (0, 0)),
    ← Finset.prod_filter_mul_prod_filter_not (U.filter fun x => ¬x = (0, 0)) pos, hposf, hneg,
    ← Finset.prod_mul_distrib]
  unfold fusP
  simp only
  rw [← hL, ← hM]
  congr 1
  · rw [Finset.filter_eq']
    have hmem : ((0 : ℤ), (0 : ℤ)) ∈ U ↔ (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s := by
      rw [hU, Finset.mem_product]
    by_cases h0 : (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s
    · rw [if_pos h0, if_pos (hmem.2 h0), Finset.prod_singleton]
      simp only [hF, Int.cast_zero, zero_mul, add_zero]
      ring
    · rw [if_neg h0, if_neg (fun h => h0 (hmem.1 h)), Finset.prod_empty]
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp only [hF, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    ring

/-- `P_{R,S}(b;·,d)` as a polynomial in the momentum `λ₁`, for the momentum `M` of `d`. -/
noncomputable def fusL (R S : ℕ) (b M : ℂ) : ℂ[X] :=
  ∏ y ∈ idxBox R S,
    (C (1 / 2) * (X + C (M + bet b R S y))) * (C (1 / 2) * (X - C (M - bet b R S y)))

theorem fusL_eval (R S : ℕ) (b M L : ℂ) :
    (fusL R S b M).eval L =
      ∏ y ∈ idxBox R S, ((L + M + bet b R S y) / 2) * ((L - M + bet b R S y) / 2) := by
  unfold fusL
  rw [eval_prod]
  refine Finset.prod_congr rfl fun y _ => ?_
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X]
  ring

/-- `P_{R,S}(b;(Q²-L²)/4,d) = fusL(L)` when `d = (Q²-M²)/4`. -/
theorem fusP_eq_fusL (R S : ℕ) (b L M d : ℂ) (hM : M ^ 2 = (b + b⁻¹) ^ 2 - 4 * d) :
    fusP R S b (((b + b⁻¹) ^ 2 - L ^ 2) / 4) d = (fusL R S b M).eval L := by
  rw [fusL_eval]
  exact fusP_eq_prod R S b L M _ d (by ring) hM

end Virasoro.P2
