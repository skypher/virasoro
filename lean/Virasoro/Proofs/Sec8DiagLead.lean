import Virasoro.Proofs.Sec8DiagPoles

/-!
# Section 8.1: leading coefficients of germs

`LV x m c`: `x = c t^m + O(t^{m+1})`.  Closed under products, inverses (nonzero `c`), quotients
and powers; the coefficient of `t^{m+n}` in a product of germs of orders `≥ m`, `≥ n` is the
product of the coefficients of `t^m` and `t^n`.
-/

namespace Virasoro

open scoped LaurentSeries

section LV

variable {K : Type*} [Field K] [CharZero K]

/-- `x = c t^m + O(t^{m+1})`. -/
def LV (x : K⸨X⸩) (m : ℤ) (c : K) : Prop := OrdGE x m ∧ x.coeff m = c

theorem ordGE_single_mul {x : K⸨X⸩} {m : ℤ} (hx : OrdGE x m) :
    OrdGE (HahnSeries.single (-m) (1 : K) * x) 0 := by
  have hs : OrdGE (HahnSeries.single (-m) (1 : K) : K⸨X⸩) (-m) := by
    unfold OrdGE; exact HahnSeries.orderTop_single_le
  have := hs.mul hx
  simpa using this

theorem coeff_shift (x : K⸨X⸩) (m i : ℤ) :
    (HahnSeries.single (-m) (1 : K) * x).coeff i = x.coeff (i + m) := by
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]

theorem coeff_mul_of_ordGE {x y : K⸨X⸩} {m n : ℤ} (hx : OrdGE x m) (hy : OrdGE y n) :
    (x * y).coeff (m + n) = x.coeff m * y.coeff n := by
  have h0 := coeff_zero_mul_of_ordGE (ordGE_single_mul hx) (ordGE_single_mul hy)
  rw [coeff_shift, coeff_shift, zero_add, zero_add] at h0
  rw [← h0]
  have e : (HahnSeries.single (-m) (1 : K) * x) * (HahnSeries.single (-n) (1 : K) * y) =
      HahnSeries.single (-(m + n)) (1 : K) * (x * y) := by
    rw [mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul, neg_add]
  rw [e, coeff_shift, zero_add]

theorem LV.mul {x y : K⸨X⸩} {m n : ℤ} {c d : K} (hx : LV x m c) (hy : LV y n d) :
    LV (x * y) (m + n) (c * d) :=
  ⟨hx.1.mul hy.1, by rw [coeff_mul_of_ordGE hx.1 hy.1, hx.2, hy.2]⟩

theorem LV.orderTop_eq {x : K⸨X⸩} {m : ℤ} {c : K} (hx : LV x m c) (hc : c ≠ 0) :
    x.orderTop = m := by
  apply le_antisymm
  · exact HahnSeries.orderTop_le_of_coeff_ne_zero (by rw [hx.2]; exact hc)
  · exact hx.1

theorem LV.inv {x : K⸨X⸩} {m : ℤ} {c : K} (hx : LV x m c) (hc : c ≠ 0) :
    LV x⁻¹ (-m) c⁻¹ := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hc (by rw [← hx.2]; simp)
  have hord : OrdGE x⁻¹ (-m) := by
    unfold OrdGE
    rw [dgOrderTop_inv hx0, hx.orderTop_eq hc]
    rfl
  refine ⟨hord, ?_⟩
  have h1 := coeff_mul_of_ordGE hx.1 hord
  rw [mul_inv_cancel₀ hx0, add_neg_cancel, hx.2] at h1
  have h1' : c * x⁻¹.coeff (-m) = 1 := by
    rw [← h1]; simp
  exact eq_inv_of_mul_eq_one_right h1'

theorem LV.div {x y : K⸨X⸩} {m n : ℤ} {c d : K} (hx : LV x m c) (hy : LV y n d) (hd : d ≠ 0) :
    LV (x / y) (m - n) (c / d) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, sub_eq_add_neg]
  exact hx.mul (hy.inv hd)

theorem LV.pow {x : K⸨X⸩} {m : ℤ} {c : K} (hx : LV x m c) (k : ℕ) :
    LV (x ^ k) (k * m) (c ^ k) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [pow_zero, Nat.cast_zero, zero_mul]
      unfold OrdGE
      rw [HahnSeries.orderTop_one]
      simp
    · simp
  | succ k ih =>
    have := ih.mul hx
    rw [pow_succ, pow_succ]
    convert this using 2
    push_cast; ring

theorem LV.sub {x y : K⸨X⸩} {m : ℤ} {c d : K} (hx : LV x m c) (hy : LV y m d) :
    LV (x - y) m (c - d) :=
  ⟨hx.1.sub hy.1, by rw [HahnSeries.coeff_sub, hx.2, hy.2]⟩

theorem lv_natCast (n : ℕ) : LV ((n : K⸨X⸩)) 0 (n : K) :=
  ⟨(regVal_natCast n).1, (regVal_natCast n).2⟩

theorem LV.congr {x : K⸨X⸩} {m m' : ℤ} {c c' : K} (hx : LV x m c) (hm : m = m') (hc : c = c') :
    LV x m' c' := by subst hm; subst hc; exact hx

end LV

end Virasoro
