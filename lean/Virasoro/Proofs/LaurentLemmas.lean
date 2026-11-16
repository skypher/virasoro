import Virasoro.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Valuation bookkeeping for Laurent series

`OrdGE x n` says that all coefficients of `x` below degree `n` vanish, i.e. `ord_t x ≥ n`
(with `ord_t 0 = ∞`).
-/

namespace Virasoro

open scoped LaurentSeries

variable {K : Type*} [Field K]

/-- `ord_t x ≥ n`. -/
def OrdGE (x : K⸨X⸩) (n : ℤ) : Prop := (n : WithTop ℤ) ≤ x.orderTop

theorem ordGE_iff {x : K⸨X⸩} {n : ℤ} : OrdGE x n ↔ ∀ m : ℤ, m < n → x.coeff m = 0 := by
  unfold OrdGE
  rw [HahnSeries.le_orderTop_iff_forall]
  constructor
  · intro h m hm
    exact h m (by exact_mod_cast hm)
  · intro h m hm
    exact h m (by exact_mod_cast hm)

theorem OrdGE.coeff_eq_zero {x : K⸨X⸩} {n m : ℤ} (h : OrdGE x n) (hm : m < n) : x.coeff m = 0 :=
  ordGE_iff.1 h m hm

theorem OrdGE.mono {x : K⸨X⸩} {n m : ℤ} (h : OrdGE x n) (hmn : m ≤ n) : OrdGE x m :=
  ordGE_iff.2 fun k hk => h.coeff_eq_zero (lt_of_lt_of_le hk hmn)

theorem OrdGE.zero (n : ℤ) : OrdGE (0 : K⸨X⸩) n := ordGE_iff.2 fun _ _ => by simp

theorem OrdGE.add {x y : K⸨X⸩} {n : ℤ} (hx : OrdGE x n) (hy : OrdGE y n) : OrdGE (x + y) n :=
  ordGE_iff.2 fun m hm => by
    rw [HahnSeries.coeff_add, hx.coeff_eq_zero hm, hy.coeff_eq_zero hm, add_zero]

theorem OrdGE.neg {x : K⸨X⸩} {n : ℤ} (hx : OrdGE x n) : OrdGE (-x) n :=
  ordGE_iff.2 fun m hm => by rw [HahnSeries.coeff_neg, hx.coeff_eq_zero hm, neg_zero]

theorem OrdGE.sub {x y : K⸨X⸩} {n : ℤ} (hx : OrdGE x n) (hy : OrdGE y n) : OrdGE (x - y) n :=
  ordGE_iff.2 fun m hm => by
    rw [HahnSeries.coeff_sub, hx.coeff_eq_zero hm, hy.coeff_eq_zero hm, sub_zero]

theorem OrdGE.sum {α : Type*} {s : Finset α} {f : α → K⸨X⸩} {n : ℤ}
    (h : ∀ i ∈ s, OrdGE (f i) n) : OrdGE (∑ i ∈ s, f i) n :=
  ordGE_iff.2 fun m hm => by
    rw [HahnSeries.coeff_sum]
    exact Finset.sum_eq_zero fun i hi => (h i hi).coeff_eq_zero hm

theorem OrdGE.mul {x y : K⸨X⸩} {a b : ℤ} (hx : OrdGE x a) (hy : OrdGE y b) :
    OrdGE (x * y) (a + b) := by
  unfold OrdGE at *
  calc ((a + b : ℤ) : WithTop ℤ) = (a : WithTop ℤ) + (b : WithTop ℤ) := by push_cast; rfl
    _ ≤ x.orderTop + y.orderTop := add_le_add hx hy
    _ ≤ (x * y).orderTop := HahnSeries.orderTop_add_le_mul

theorem ordGE_order (x : K⸨X⸩) : OrdGE x x.order := by
  by_cases hx : x = 0
  · subst hx; exact OrdGE.zero _
  · unfold OrdGE
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hx]

theorem ordGE_one : OrdGE (1 : K⸨X⸩) 0 := by
  have := ordGE_order (1 : K⸨X⸩)
  rwa [HahnSeries.order_one] at this

theorem ordGE_C (c : K) : OrdGE (HahnSeries.C c : K⸨X⸩) 0 := by
  have := ordGE_order (HahnSeries.C c : K⸨X⸩)
  rwa [HahnSeries.order_C] at this

theorem OrdGE.pow {x : K⸨X⸩} {a : ℤ} (hx : OrdGE x a) (n : ℕ) : OrdGE (x ^ n) (n * a) := by
  induction n with
  | zero => simpa using ordGE_one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hx
    refine this.mono (le_of_eq ?_)
    push_cast
    ring

theorem order_inv {x : K⸨X⸩} (hx : x ≠ 0) : (x⁻¹).order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  linarith

theorem ordGE_inv (x : K⸨X⸩) : OrdGE x⁻¹ (-x.order) := by
  by_cases hx : x = 0
  · subst hx; simpa using OrdGE.zero (K := K) _
  · rw [← order_inv hx]
    exact ordGE_order _

theorem OrdGE.div {x : K⸨X⸩} {a : ℤ} (hx : OrdGE x a) (y : K⸨X⸩) :
    OrdGE (x / y) (a - y.order) := by
  rw [div_eq_mul_inv, sub_eq_add_neg]
  exact hx.mul (ordGE_inv y)

/-- If the coefficients of `x` and `y` agree up to degree `U`, then `ord_t (x - y) ≥ U + 1`. -/
theorem ordGE_sub_of_coeff_eq {x y : K⸨X⸩} {U : ℤ} (h : ∀ n : ℤ, n ≤ U → x.coeff n = y.coeff n) :
    OrdGE (x - y) (U + 1) :=
  ordGE_iff.2 fun m hm => by
    rw [HahnSeries.coeff_sub, h m (by linarith), sub_self]

/-- The precision rule for a product: if `A, A'` have valuation at least `a`, `S, S'` have
valuation at least `s`, `A' ≡ A` through `t^{U-s}` and `S' ≡ S` through `t^{U-a}`, then
`A' S' ≡ A S` through `t^U`. -/
theorem coeff_mul_congr {A A' S S' : K⸨X⸩} {a s U : ℤ}
    (hA : OrdGE A a) (hS' : OrdGE S' s)
    (hAA : ∀ n : ℤ, n ≤ U - s → A'.coeff n = A.coeff n)
    (hSS : ∀ n : ℤ, n ≤ U - a → S'.coeff n = S.coeff n) :
    ∀ n : ℤ, n ≤ U → (A' * S').coeff n = (A * S).coeff n := by
  intro n hn
  have e : A' * S' - A * S = (A' - A) * S' + A * (S' - S) := by ring
  have h1 : OrdGE ((A' - A) * S') (U + 1) :=
    ((ordGE_sub_of_coeff_eq hAA).mul hS').mono (by linarith)
  have h2 : OrdGE (A * (S' - S)) (U + 1) :=
    (hA.mul (ordGE_sub_of_coeff_eq hSS)).mono (by linarith)
  have h3 : OrdGE (A' * S' - A * S) (U + 1) := by rw [e]; exact h1.add h2
  have := h3.coeff_eq_zero (show n < U + 1 by linarith)
  rw [HahnSeries.coeff_sub] at this
  exact sub_eq_zero.mp this

/-- An element with valuation at least `0` and nonzero constant coefficient has order `0`. -/
theorem order_eq_zero_of {x : K⸨X⸩} (h : OrdGE x 0) (h0 : x.coeff 0 ≠ 0) : x.order = 0 := by
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h0)
  by_contra hlt
  push Not at hlt
  have hx : x ≠ 0 := by
    intro hx; rw [hx] at h0; simp at h0
  have : x.coeff x.order ≠ 0 := fun h0 => hx (HahnSeries.coeff_order_eq_zero.mp h0)
  exact this (h.coeff_eq_zero hlt)

end Virasoro
