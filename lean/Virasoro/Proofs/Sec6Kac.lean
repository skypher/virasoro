import Virasoro.Statements.Sec6
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Proofs: Lemma 6.4 (distinct weights and no shifted self-poles away from rational `b²`)

The working statements are over an arbitrary field of characteristic zero and an element `b`
whose square is not rational; they apply to complex `b⋆`, to the rational function `b`, and to
the germ `b⋆ + t`.
-/

namespace Virasoro

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `b²` is not a rational number. -/
def SqIrrational (b : 𝔽) : Prop := ∀ q : ℚ, b ^ 2 ≠ (q : 𝔽)

/-- If `b²` is irrational, then `m b² + n ≠ 0` for integers `(m, n) ≠ (0, 0)`. -/
theorem lin_sq_ne_zero {b : 𝔽} (hirr : SqIrrational b) (m n : ℤ) (h : m ≠ 0 ∨ n ≠ 0) :
    (m : 𝔽) * b ^ 2 + (n : 𝔽) ≠ 0 := by
  intro h0
  by_cases hm : m = 0
  · subst hm
    have hn : n ≠ 0 := by tauto
    simp only [Int.cast_zero, zero_mul, zero_add] at h0
    exact hn (by exact_mod_cast h0)
  · have hm' : (m : 𝔽) ≠ 0 := Int.cast_ne_zero.mpr hm
    apply hirr (-(n : ℚ) / (m : ℚ))
    push_cast
    field_simp
    linear_combination h0

theorem kacH_shift_sub {b : 𝔽} (hb : b ≠ 0) (r s u v : ℤ) :
    kacH r s b + ((r * s : ℤ) : 𝔽) - kacH u v b =
      (((u - r : ℤ) : 𝔽) * b ^ 2 + ((v + s : ℤ) : 𝔽)) *
        (((u + r : ℤ) : 𝔽) * b ^ 2 + ((v - s : ℤ) : 𝔽)) / (4 * b ^ 2) := by
  unfold kacH
  push_cast
  field_simp
  ring

theorem kacH_sub {b : 𝔽} (hb : b ≠ 0) (r s u v : ℤ) :
    kacH r s b - kacH u v b =
      (((u - r : ℤ) : 𝔽) * b ^ 2 + ((v - s : ℤ) : 𝔽)) *
        (((u + r : ℤ) : 𝔽) * b ^ 2 + ((v + s : ℤ) : 𝔽)) / (4 * b ^ 2) := by
  unfold kacH
  push_cast
  field_simp
  ring

/-- No shifted weight `h_{r,s}(b) + rs` is a Kac weight `h_{u,v}(b)` when `b²` is irrational. -/
theorem kacH_shift_ne {b : 𝔽} (hb : b ≠ 0) (hirr : SqIrrational b) (r s u v : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) :
    kacH r s b + ((r * s : ℤ) : 𝔽) - kacH u v b ≠ 0 := by
  rw [kacH_shift_sub hb]
  have h4 : (4 * b ^ 2 : 𝔽) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  refine div_ne_zero (mul_ne_zero ?_ ?_) h4
  · exact lin_sq_ne_zero hirr _ _ (Or.inr (by omega))
  · exact lin_sq_ne_zero hirr _ _ (Or.inl (by omega))

/-- Distinct positive labels have distinct Kac weights when `b²` is irrational. -/
theorem kacH_ne {b : 𝔽} (hb : b ≠ 0) (hirr : SqIrrational b) (r s u v : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hne : (r, s) ≠ (u, v)) :
    kacH r s b - kacH u v b ≠ 0 := by
  rw [kacH_sub hb]
  have h4 : (4 * b ^ 2 : 𝔽) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  refine div_ne_zero (mul_ne_zero ?_ ?_) h4
  · refine lin_sq_ne_zero hirr _ _ ?_
    by_contra hcon
    push Not at hcon
    apply hne
    rw [Prod.mk.injEq]
    constructor <;> omega
  · exact lin_sq_ne_zero hirr _ _ (Or.inl (by omega))

/-- The factors `p b + q b⁻¹` of `𝒜_{r,s}` do not vanish when `b²` is irrational. -/
theorem genA_factor_ne {b : 𝔽} (hb : b ≠ 0) (hirr : SqIrrational b) (p q : ℤ)
    (h : p ≠ 0 ∨ q ≠ 0) : (p : 𝔽) * b + (q : 𝔽) * b⁻¹ ≠ 0 := by
  have e : (p : 𝔽) * b + (q : 𝔽) * b⁻¹ = ((p : 𝔽) * b ^ 2 + (q : 𝔽)) / b := by
    field_simp
  rw [e]
  exact div_ne_zero (lin_sq_ne_zero hirr p q h) hb

theorem mem_genAIndex {r s : ℕ} {pq : ℤ × ℤ} (h : pq ∈ genAIndex r s) :
    pq.1 ≠ 0 ∨ pq.2 ≠ 0 := by
  simp only [genAIndex, Finset.mem_filter] at h
  by_contra hcon
  push Not at hcon
  exact h.2.1 (Prod.ext hcon.1 hcon.2)

theorem genA_ne_zero {b : 𝔽} (hb : b ≠ 0) (hirr : SqIrrational b) (r s : ℕ) :
    genA r s b ≠ 0 := by
  unfold genA
  refine mul_ne_zero (inv_ne_zero (by norm_num)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro pq hpq
  exact inv_ne_zero (genA_factor_ne hb hirr _ _ (mem_genAIndex hpq))

/-- The square of the variable of `ℂ(b)` is not a rational number. -/
theorem sqIrrational_ratFuncX : SqIrrational (RatFunc.X : RatFunc ℂ) := by
  intro q h
  have h1 : RatFunc.intDegree ((RatFunc.X : RatFunc ℂ) ^ 2) = 2 := by
    rw [pow_two, RatFunc.intDegree_mul RatFunc.X_ne_zero RatFunc.X_ne_zero, RatFunc.intDegree_X]
    norm_num
  have h2 : ((q : ℚ) : RatFunc ℂ) = RatFunc.C (q : ℂ) := (map_ratCast (RatFunc.C : ℂ →+* RatFunc ℂ) q).symm
  rw [h, h2, RatFunc.intDegree_C] at h1
  norm_num at h1

/-- Paper label: lem:no-generic-shifted-pole -/
theorem lem_no_generic_shifted_pole : Stmt_lem_no_generic_shifted_pole := by
  refine ⟨?_, ?_⟩
  · intro r s u v hr hs hu hv
    have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    refine ⟨?_, ?_⟩
    · have := kacH_shift_ne hX sqIrrational_ratFuncX r s u v (by exact_mod_cast hr)
        (by exact_mod_cast hs) (by exact_mod_cast hu) (by exact_mod_cast hv)
      simpa using this
    · intro hne
      refine kacH_ne hX sqIrrational_ratFuncX r s u v (by exact_mod_cast hr)
        (by exact_mod_cast hs) (by exact_mod_cast hu) (by exact_mod_cast hv) ?_
      intro h
      apply hne
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · intro b hb hq r s u v hr hs hu hv
    have hirr : SqIrrational b := hq
    refine ⟨?_, ?_, ?_, genA_ne_zero hb hirr r s⟩
    · have := kacH_shift_ne hb hirr r s u v (by exact_mod_cast hr)
        (by exact_mod_cast hs) (by exact_mod_cast hu) (by exact_mod_cast hv)
      simpa using this
    · intro hne
      refine kacH_ne hb hirr r s u v (by exact_mod_cast hr)
        (by exact_mod_cast hs) (by exact_mod_cast hu) (by exact_mod_cast hv) ?_
      intro h
      apply hne
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · intro pq hpq
      exact genA_factor_ne hb hirr _ _ (mem_genAIndex hpq)

example : Stmt_lem_no_generic_shifted_pole := lem_no_generic_shifted_pole

end Virasoro
