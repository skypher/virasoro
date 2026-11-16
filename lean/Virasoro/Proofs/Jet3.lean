import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# Second-order jets `K[x]/(x³)`

`T3 K` is the ring of `a + b x + c x²` with `x³ = 0`, with computable operations, and
`trunc3 : K⟦X⟧ →+* T3 K` truncates a power series.  It is used to read off the coefficients
`G₀, G₁, G₂` of `G(h + x)` by exact computation.
-/

namespace Virasoro

/-- `a + b x + c x²` modulo `x³`. -/
@[ext] structure T3 (K : Type*) where
  a : K
  b : K
  c : K
deriving DecidableEq

namespace T3

variable {K : Type*} [CommRing K]

instance : Zero (T3 K) := ⟨⟨0, 0, 0⟩⟩
instance : One (T3 K) := ⟨⟨1, 0, 0⟩⟩
instance : Add (T3 K) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg (T3 K) := ⟨fun x => ⟨-x.a, -x.b, -x.c⟩⟩
instance : Sub (T3 K) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c⟩⟩
instance : Mul (T3 K) :=
  ⟨fun x y => ⟨x.a * y.a, x.a * y.b + x.b * y.a, x.a * y.c + x.b * y.b + x.c * y.a⟩⟩

@[simp] theorem zero_a : (0 : T3 K).a = 0 := rfl
@[simp] theorem zero_b : (0 : T3 K).b = 0 := rfl
@[simp] theorem zero_c : (0 : T3 K).c = 0 := rfl
@[simp] theorem one_a : (1 : T3 K).a = 1 := rfl
@[simp] theorem one_b : (1 : T3 K).b = 0 := rfl
@[simp] theorem one_c : (1 : T3 K).c = 0 := rfl
@[simp] theorem add_a (x y : T3 K) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : T3 K) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : T3 K) : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_a (x : T3 K) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : T3 K) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : T3 K) : (-x).c = -x.c := rfl
@[simp] theorem sub_a (x y : T3 K) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : T3 K) : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c (x y : T3 K) : (x - y).c = x.c - y.c := rfl
@[simp] theorem mul_a (x y : T3 K) : (x * y).a = x.a * y.a := rfl
@[simp] theorem mul_b (x y : T3 K) : (x * y).b = x.a * y.b + x.b * y.a := rfl
@[simp] theorem mul_c (x y : T3 K) : (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a := rfl

instance : CommRing (T3 K) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  mul_comm x y := by ext <;> simp <;> ring
  sub_eq_add_neg x y := by ext <;> simp [sub_eq_add_neg]

/-- `k ↦ k + 0 x + 0 x²`. -/
def inl : K →+* T3 K where
  toFun k := ⟨k, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp
  map_zero' := rfl
  map_add' x y := by ext <;> simp

@[simp] theorem inl_a (k : K) : (inl k).a = k := rfl
@[simp] theorem inl_b (k : K) : (inl k).b = 0 := rfl
@[simp] theorem inl_c (k : K) : (inl k).c = 0 := rfl

instance [Algebra ℚ K] : Algebra ℚ (T3 K) := (inl.comp (algebraMap ℚ K)).toAlgebra

theorem algebraMap_eq [Algebra ℚ K] (q : ℚ) :
    algebraMap ℚ (T3 K) q = ⟨algebraMap ℚ K q, 0, 0⟩ := rfl

/-- Applying a ring homomorphism to the three coefficients. -/
def map {L : Type*} [CommRing L] (f : K →+* L) : T3 K →+* T3 L where
  toFun x := ⟨f x.a, f x.b, f x.c⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem map_a {L : Type*} [CommRing L] (f : K →+* L) (x : T3 K) : (map f x).a = f x.a :=
  rfl
@[simp] theorem map_b {L : Type*} [CommRing L] (f : K →+* L) (x : T3 K) : (map f x).b = f x.b :=
  rfl
@[simp] theorem map_c {L : Type*} [CommRing L] (f : K →+* L) (x : T3 K) : (map f x).c = f x.c :=
  rfl

theorem coeff_mul_one (p q : PowerSeries K) :
    PowerSeries.coeff 1 (p * q) =
      PowerSeries.coeff 0 p * PowerSeries.coeff 1 q + PowerSeries.coeff 1 p * PowerSeries.coeff 0 q := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton]

theorem coeff_mul_two (p q : PowerSeries K) :
    PowerSeries.coeff 2 (p * q) =
      PowerSeries.coeff 0 p * PowerSeries.coeff 2 q + PowerSeries.coeff 1 p * PowerSeries.coeff 1 q
        + PowerSeries.coeff 2 p * PowerSeries.coeff 0 q := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp only [zero_add]
  ring

/-- Truncation of a power series to second order. -/
noncomputable def trunc3 : PowerSeries K →+* T3 K where
  toFun p := ⟨PowerSeries.coeff 0 p, PowerSeries.coeff 1 p, PowerSeries.coeff 2 p⟩
  map_one' := by
    ext <;> simp [PowerSeries.coeff_one]
  map_mul' p q := by
    ext
    · simp [PowerSeries.coeff_mul]
    · simp only [mul_b]; exact coeff_mul_one p q
    · simp only [mul_c]; exact coeff_mul_two p q
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp

@[simp] theorem trunc3_a (p : PowerSeries K) : (trunc3 p).a = PowerSeries.coeff 0 p := rfl
@[simp] theorem trunc3_b (p : PowerSeries K) : (trunc3 p).b = PowerSeries.coeff 1 p := rfl
@[simp] theorem trunc3_c (p : PowerSeries K) : (trunc3 p).c = PowerSeries.coeff 2 p := rfl

theorem trunc3_C (k : K) : trunc3 (PowerSeries.C k) = inl k := by
  ext <;> simp [PowerSeries.coeff_C]

theorem trunc3_X : trunc3 (PowerSeries.X : PowerSeries K) = ⟨0, 1, 0⟩ := by
  ext <;> simp [PowerSeries.coeff_X]

end T3

end Virasoro
