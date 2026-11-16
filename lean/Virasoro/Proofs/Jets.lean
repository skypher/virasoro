import Virasoro.Proofs.Sec4Core2
import Virasoro.Proofs.Germs
import Virasoro.Proofs.Sec7Val

/-!
# Jets of Laurent germs regular at `t = 0`

`J1 x a b` records that `x` is regular at `t = 0` with `x = a + b t + O(t²)`, and `J2 x a b c`
that `x = a + b t + c t² + O(t³)`.  Sums, products, inverses and finite products of jets follow
the usual rules; finite products are recorded through logarithmic derivatives.
-/

namespace Virasoro

open scoped LaurentSeries

variable {K : Type*} [Field K] [CharZero K]

/-- `x = a + b t + O(t²)`. -/
def J1 (x : K⸨X⸩) (a b : K) : Prop := OrdGE x 0 ∧ x.coeff 0 = a ∧ x.coeff 1 = b

/-- `x = a + b t + c t² + O(t³)`. -/
def J2 (x : K⸨X⸩) (a b c : K) : Prop := OrdGE x 0 ∧ x.coeff 0 = a ∧ x.coeff 1 = b ∧ x.coeff 2 = c

theorem J2.toJ1 {x : K⸨X⸩} {a b c : K} (h : J2 x a b c) : J1 x a b := ⟨h.1, h.2.1, h.2.2.1⟩

/-- The three lowest coefficients of a germ regular at `0` are those of its power series. -/
theorem coeff_ofPowerSeries_nat (p : PowerSeries K) (n : ℕ) :
    (HahnSeries.ofPowerSeries ℤ K p).coeff (n : ℤ) = PowerSeries.coeff n p :=
  HahnSeries.ofPowerSeries_apply_coeff p n

theorem J2.mul {x y : K⸨X⸩} {a b c a' b' c' : K} (hx : J2 x a b c) (hy : J2 y a' b' c') :
    J2 (x * y) (a * a') (a * b' + b * a') (a * c' + b * b' + c * a') := by
  have hord : OrdGE (x * y) 0 := by simpa using hx.1.mul hy.1
  obtain ⟨p, rfl, -⟩ := exists_ofPowerSeries hx.1
  obtain ⟨q, rfl, -⟩ := exists_ofPowerSeries hy.1
  obtain ⟨-, hx0, hx1, hx2⟩ := hx
  obtain ⟨-, hy0, hy1, hy2⟩ := hy
  have e0 := coeff_ofPowerSeries_nat p 0
  have e1 := coeff_ofPowerSeries_nat p 1
  have e2 := coeff_ofPowerSeries_nat p 2
  have f0 := coeff_ofPowerSeries_nat q 0
  have f1 := coeff_ofPowerSeries_nat q 1
  have f2 := coeff_ofPowerSeries_nat q 2
  push_cast at e0 e1 e2 f0 f1 f2
  rw [e0] at hx0; rw [e1] at hx1; rw [e2] at hx2
  rw [f0] at hy0; rw [f1] at hy1; rw [f2] at hy2
  rw [← map_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact hord
  · rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, coeff_ofPowerSeries_nat, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    rw [← hx0, ← hy0]
  · rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, coeff_ofPowerSeries_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton]
    simp only [zero_add]
    rw [← hx0, ← hy0, ← hx1, ← hy1]
  · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, coeff_ofPowerSeries_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp only [zero_add]
    rw [← hx0, ← hy0, ← hx1, ← hy1, ← hx2, ← hy2]
    ring


theorem J2.add {x y : K⸨X⸩} {a b c a' b' c' : K} (hx : J2 x a b c) (hy : J2 y a' b' c') :
    J2 (x + y) (a + a') (b + b') (c + c') :=
  ⟨hx.1.add hy.1, by rw [HahnSeries.coeff_add, hx.2.1, hy.2.1],
    by rw [HahnSeries.coeff_add, hx.2.2.1, hy.2.2.1], by rw [HahnSeries.coeff_add, hx.2.2.2, hy.2.2.2]⟩

theorem J2.sub {x y : K⸨X⸩} {a b c a' b' c' : K} (hx : J2 x a b c) (hy : J2 y a' b' c') :
    J2 (x - y) (a - a') (b - b') (c - c') :=
  ⟨hx.1.sub hy.1, by rw [HahnSeries.coeff_sub, hx.2.1, hy.2.1],
    by rw [HahnSeries.coeff_sub, hx.2.2.1, hy.2.2.1], by rw [HahnSeries.coeff_sub, hx.2.2.2, hy.2.2.2]⟩

theorem J2.congr {x : K⸨X⸩} {a b c a' b' c' : K} (hx : J2 x a b c) (ha : a = a') (hb : b = b')
    (hc : c = c') : J2 x a' b' c' := by
  subst ha hb hc; exact hx

theorem j2_C (c : K) : J2 (HahnSeries.C c : K⸨X⸩) c 0 0 := by
  refine ⟨ordGE_C c, by simp [HahnSeries.C], ?_, ?_⟩
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num)]
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num)]

theorem j2_intCast (n : ℤ) : J2 ((n : K⸨X⸩)) (n : K) 0 0 := by
  have : ((n : K⸨X⸩)) = HahnSeries.C (n : K) := (map_intCast (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]; exact j2_C _

theorem j2_natCast (n : ℕ) : J2 ((n : K⸨X⸩)) (n : K) 0 0 := by
  have : ((n : K⸨X⸩)) = HahnSeries.C (n : K) := (map_natCast (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]; exact j2_C _

theorem j2_ofNat (n : ℕ) [n.AtLeastTwo] :
    J2 ((OfNat.ofNat n : K⸨X⸩)) (OfNat.ofNat n : K) 0 0 := by
  have : ((OfNat.ofNat n : K⸨X⸩)) = HahnSeries.C (OfNat.ofNat n : K) :=
    (map_ofNat (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]; exact j2_C _

theorem J2.inv {x : K⸨X⸩} {a b c : K} (hx : J2 x a b c) (ha : a ≠ 0) :
    J2 x⁻¹ a⁻¹ (-b / a ^ 2) ((b ^ 2 - a * c) / a ^ 3) := by
  have hrv : RegVal x⁻¹ a⁻¹ := RegVal.inv ⟨hx.1, hx.2.1⟩ ha
  set w1 := x⁻¹.coeff 1
  set w2 := x⁻¹.coeff 2
  have hw : J2 x⁻¹ a⁻¹ w1 w2 := ⟨hrv.1, hrv.2, rfl, rfl⟩
  have hne : x ≠ 0 := by
    intro h; have := hx.2.1; rw [h] at this; exact ha (by simpa using this.symm)
  have hm := hw.mul hx
  rw [inv_mul_cancel₀ hne] at hm
  have h1 : J2 (1 : K⸨X⸩) 1 0 0 := by simpa using j2_C (1 : K)
  have e1 : a⁻¹ * b + w1 * a = 0 := by rw [← h1.2.2.1, hm.2.2.1]
  have e2 : a⁻¹ * c + w1 * b + w2 * a = 0 := by rw [← h1.2.2.2, hm.2.2.2]
  have hw1 : w1 = -b / a ^ 2 := by field_simp; field_simp at e1; linear_combination e1
  have hw2 : w2 = (b ^ 2 - a * c) / a ^ 3 := by
    rw [hw1] at e2; field_simp; field_simp at e2; linear_combination e2
  exact hw.congr rfl hw1 hw2

theorem J2.div {x y : K⸨X⸩} {a b c a' b' c' : K} (hx : J2 x a b c) (hy : J2 y a' b' c')
    (ha' : a' ≠ 0) :
    J2 (x / y) (a * a'⁻¹) (a * (-b' / a' ^ 2) + b * a'⁻¹)
      (a * ((b' ^ 2 - a' * c') / a' ^ 3) + b * (-b' / a' ^ 2) + c * a'⁻¹) := by
  rw [div_eq_mul_inv]
  exact hx.mul (hy.inv ha')

theorem j2_bGerm (bs : K) : J2 (bGerm bs) bs 1 0 := by
  refine ⟨ordGE_bGerm bs, bGerm_coeff_zero bs, ?_, ?_⟩
  · unfold bGerm
    rw [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num),
      HahnSeries.coeff_single_same, zero_add]
  · unfold bGerm
    rw [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num),
      HahnSeries.coeff_single_of_ne (by norm_num), add_zero]

theorem j2_bGerm_inv {bs : K} (hbs : bs ≠ 0) :
    J2 (bGerm bs)⁻¹ bs⁻¹ (-1 / bs ^ 2) (1 / bs ^ 3) :=
  ((j2_bGerm bs).inv hbs).congr rfl rfl (by ring)

theorem J1.mul {x y : K⸨X⸩} {a b a' b' : K} (hx : J1 x a b) (hy : J1 y a' b') :
    J1 (x * y) (a * a') (a * b' + b * a') := by
  have := (J2.mul (⟨hx.1, hx.2.1, hx.2.2, rfl⟩ : J2 x a b (x.coeff 2))
    (⟨hy.1, hy.2.1, hy.2.2, rfl⟩ : J2 y a' b' (y.coeff 2)))
  exact this.toJ1

theorem J1.inv {x : K⸨X⸩} {a b : K} (hx : J1 x a b) (ha : a ≠ 0) :
    J1 x⁻¹ a⁻¹ (-b / a ^ 2) :=
  (J2.inv (⟨hx.1, hx.2.1, hx.2.2, rfl⟩ : J2 x a b (x.coeff 2)) ha).toJ1

theorem J1.congr {x : K⸨X⸩} {a b a' b' : K} (hx : J1 x a b) (ha : a = a') (hb : b = b') :
    J1 x a' b' := by
  subst ha hb; exact hx

/-- Finite products of 1-jets, through logarithmic derivatives. -/
theorem J1.prod {α : Type*} {s : Finset α} {f : α → K⸨X⸩} {a b : α → K}
    (h : ∀ i ∈ s, J1 (f i) (a i) (b i)) (ha : ∀ i ∈ s, a i ≠ 0) :
    J1 (∏ i ∈ s, f i) (∏ i ∈ s, a i) ((∏ i ∈ s, a i) * ∑ i ∈ s, b i / a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (j2_C (1 : K)).toJ1
  | insert j s hj ih =>
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hm := (h j (Finset.mem_insert_self j s)).mul ih'
    have haj := ha j (Finset.mem_insert_self j s)
    refine hm.congr rfl ?_
    field_simp
    ring

end Virasoro
