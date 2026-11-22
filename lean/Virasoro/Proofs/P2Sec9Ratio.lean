import Virasoro.Proofs.P2Sec12TwoStep

/-!
# Theorem 9.2 (generic first-layer Jantzen vertex ratio): the Gamma factorization
(paper.tex l.2716–2749), and the reduction of the theorem to the box formula (9.4)
-/

namespace Virasoro

open Polynomial

/-- The box formula (9.4) of Theorem 9.2, paper.tex l.2630–2715: for generic `b`, `R, S ≥ 1`,
`k < R`, `m < S`, `d = h_{2k+1,2m+1}(b)` and a singular vector `χ` of level `RS` in
`M(c(b),h_{R,S}(b))`, `∂_Δ B_Δ(χ,χ) ≠ 0` and
`∂_Δ ρ_{Δ,d}(χ,χ) · ∏_{(a,b') ≠ (0,0)} (at+b') = ∂_Δ B_Δ(χ,χ) · ∏_{(a,b') ≠ (-k,-m)}
((a+k)t+(b'+m))`, both derivatives at `Δ = h_{R,S}(b)`.

Demand sheet (the knobs are those of `Stmt_thm_first_layer_ratio`, whose first three clauses
after `boxDen ≠ 0` this is).
- generic `b`: `b ≠ 0`, `b² ∉ ℚ` (l.2631, 2693–2696);
- `R, S ≥ 1`, `k < R`, `m < S` (l.2632);
- every singular vector of level `RS`, in coordinates `x` (l.2633–2634);
- the two derivatives are `torusCrossScalar` and `crossScalar`; cross-multiplied with the two
  box products (l.2676–2715). -/
def Stmt_sub_first_layer_box : Prop :=
  ∀ b : ℂ, b ≠ 0 → (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
    ∀ R S k m : ℕ, 0 < R → 0 < S → k < R → m < S →
      ∀ x : Nat.Partition (R * S) → ℂ,
        Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x) (R * S) →
          crossScalar (kacC b) (kacH R S b) x ≠ 0 ∧
          torusCrossScalar (kacC b) (kacH R S b)
              (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) x * boxDen R S (b ^ 2) =
            crossScalar (kacC b) (kacH R S b) x * boxNum R S k m (b ^ 2)

section Generic

variable {b : ℂ} (hirr : ∀ q : ℚ, b ^ 2 ≠ (q : ℂ))

include hirr

/-- At irrational `t = b²` a linear factor `at + c` with `(a,c) ≠ (0,0)` does not vanish
(l.2693–2696). -/
theorem lin_ne_generic (a c : ℤ) (h : a ≠ 0 ∨ c ≠ 0) : (a : ℂ) * b ^ 2 + (c : ℂ) ≠ 0 := by
  intro h0
  by_cases ha : a = 0
  · subst ha
    rcases h with h | h
    · exact h rfl
    · apply h
      have : (c : ℂ) = 0 := by simpa using h0
      exact_mod_cast this
  · have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    apply hirr (-(c : ℚ) / a)
    push_cast
    rw [eq_div_iff hac]
    linear_combination h0

theorem linV_ne_generic (y : ℤ × ℤ) (h : y.1 ≠ 0 ∨ y.2 ≠ 0) : linV (b ^ 2) y ≠ 0 :=
  lin_ne_generic hirr y.1 y.2 h

theorem recGamma_ne_generic_div (hb : b ≠ 0) {x : ℤ} (hx : x ≠ 0) (z : ℂ) (N : ℤ)
    (hz : z = (x : ℂ) / b ^ 2 + N) : (Complex.Gamma z)⁻¹ ≠ 0 := by
  refine inv_ne_zero (Complex.Gamma_ne_zero fun M h => ?_)
  rw [hz] at h
  have h' : (x : ℂ) / b ^ 2 = -(M : ℂ) - N := by linear_combination h
  have hx' : (x : ℂ) = (x : ℂ) / b ^ 2 * b ^ 2 := by field_simp
  rw [h'] at hx'
  refine lin_ne_generic hirr (-(M : ℤ) - N) (-x) (Or.inr (neg_ne_zero.2 hx)) ?_
  push_cast
  linear_combination -hx'

theorem recGamma_ne_generic_mul {a : ℤ} (ha : a ≠ 0) (z : ℂ) (N : ℤ)
    (hz : z = (a : ℂ) * b ^ 2 + N) : (Complex.Gamma z)⁻¹ ≠ 0 := by
  refine inv_ne_zero (Complex.Gamma_ne_zero fun M h => ?_)
  rw [hz] at h
  refine lin_ne_generic hirr a (N + M) (Or.inl ha) ?_
  push_cast
  linear_combination h

end Generic

/-- The numerator of (9.4) after the shift `(a,b') ↦ (a+k,b'+m)`. -/
theorem boxNum_shift (R S : ℤ) (k m : ℕ) (t : ℂ) :
    boxNum R S k m t = ∏ y ∈ (boxShift R S k m).erase (0, 0), linV t y := by
  unfold boxNum
  refine Finset.prod_nbij' (fun x => (x.1 + k, x.2 + m)) (fun y => (y.1 - k, y.2 - m))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_erase, boxSet, boxShift, Finset.mem_product, Finset.mem_Icc, ne_eq,
      Prod.ext_iff] at hx ⊢
    omega
  · intro y hy
    simp only [Finset.mem_erase, boxSet, boxShift, Finset.mem_product, Finset.mem_Icc, ne_eq,
      Prod.ext_iff] at hy ⊢
    omega
  · intro x _
    simp
  · intro y _
    simp
  · intro x _
    rfl

/-- The Gamma factorization of Theorem 9.2 (l.2716–2749) and the nonvanishing of the two
denominators `∏ (at+b')` and `Ψ(ϖ_{R,S};b)` at generic `b`. -/
theorem box_gamma_generic {b : ℂ} (hb : b ≠ 0) (hirr : ∀ q : ℚ, b ^ 2 ≠ (q : ℂ))
    {R S k m : ℕ} (hkR : k < R) (hmS : m < S) :
    boxDen R S (b ^ 2) ≠ 0 ∧
      PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b ≠ 0 ∧
      boxNum R S k m (b ^ 2) * PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b =
        boxDen R S (b ^ 2) * PsiPot k m (((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2) b := by
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun y hy => ?_
    refine linV_ne_generic hirr y ?_
    by_contra hc
    push_neg at hc
    exact Finset.ne_of_mem_erase hy (Prod.ext hc.1 hc.2)
  · have h := PsiPot_strip hb R k m (S : ℤ) (-(S : ℤ)) rfl
    have e1 : ((R : ℂ) * b + (((S : ℤ) : ℤ) : ℂ) * b⁻¹) / 2 =
        ((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2 := by
      push_cast; ring
    rw [e1] at h
    rw [h]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ ?_) <;>
      refine Finset.prod_ne_zero_iff.2 fun x hx => ?_ <;> rw [Finset.mem_Icc] at hx
    · exact recGamma_ne_generic_div hirr hb (x := x) (by omega) _ ((R : ℤ) + 1) (by push_cast; ring)
    · exact recGamma_ne_generic_div hirr hb (x := x) (by omega) _ (1 - (R : ℤ)) (by push_cast; ring)
    · exact recGamma_ne_generic_mul hirr (a := x) (by omega) _ ((S : ℤ) + m + 1) (by push_cast; ring)
    · exact recGamma_ne_generic_mul hirr (a := x) (by omega) _ (1 + -(S : ℤ) + m) (by push_cast; ring)
  · have h2 := two_step_box hkR hmS (linV (b ^ 2))
    rw [← boxNum_shift] at h2
    change _ = boxDen R S (b ^ 2) * _ at h2
    have hpsi := psi_box_core hb R S k m
    have hN : ((∏ y ∈ stripN1 R S m, linV (b ^ 2) y) *
        ∏ y ∈ stripN2 R S k m, linV (b ^ 2) y) ≠ 0 := by
      refine mul_ne_zero ?_ ?_ <;> refine Finset.prod_ne_zero_iff.2 fun y hy => ?_
      · simp only [stripN1, Finset.mem_product, Finset.mem_Icc] at hy
        exact linV_ne_generic hirr y (Or.inr (by omega))
      · simp only [stripN2, Finset.mem_product, Finset.mem_Icc] at hy
        exact linV_ne_generic hirr y (Or.inl (by omega))
    refine mul_left_cancel₀ hN ?_
    linear_combination boxNum R S k m (b ^ 2) * hpsi +
      PsiPot k m (((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2) b * h2

/-- Theorem 9.2 from the box formula (9.4). -/
theorem thm_first_layer_ratio_of_box (h : Stmt_sub_first_layer_box) :
    Stmt_thm_first_layer_ratio := by
  intro b hb hirr R S k m hR hS hk hm x hx
  obtain ⟨h1, h2⟩ := h b hb hirr R S k m hR hS hk hm x hx
  obtain ⟨g1, g2, g3⟩ := box_gamma_generic hb hirr hk hm
  exact ⟨g1, h1, h2, g2, g3⟩

end Virasoro
