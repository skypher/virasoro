import Virasoro.Kac
import Virasoro.Residue
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Rational functions over a field `K` regular at a point of a `K`-algebra field

For a field `𝔽` of characteristic zero and `b : 𝔽`, the rational functions `x ∈ ℚ(b)` whose
denominator does not vanish at `b` form a subalgebra, and evaluation at `b` is a ring
homomorphism from it to `𝔽`.  Identities of rational functions of `b` over `ℚ` specialize along
this homomorphism.
-/

namespace Virasoro

open Polynomial

variable {K 𝔽 : Type} [Field K] [Field 𝔽] [Algebra K 𝔽] [CharZero K] [CharZero 𝔽] (b : 𝔽)

/-- `x ∈ ℚ(b)` is regular at `b` and takes the value `v` there. -/
def EvToK (x : RatFunc K) (v : 𝔽) : Prop :=
  Polynomial.eval₂ (algebraMap K 𝔽) b (RatFunc.denom x) ≠ 0 ∧
    RatFunc.eval (algebraMap K 𝔽) b x = v

variable {b}

theorem EvToK.add {x y : RatFunc K} {v w : 𝔽} (hx : EvToK b x v) (hy : EvToK b y w) :
    EvToK b (x + y) (v + w) := by
  refine ⟨fun h0 => ?_, by rw [RatFunc.eval_add (f := algebraMap K 𝔽) (a := b) hx.1 hy.1, hx.2, hy.2]⟩
  obtain ⟨q, hq⟩ := RatFunc.denom_add_dvd x y
  have := congrArg (Polynomial.eval₂ (algebraMap K 𝔽) b) hq
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, h0, zero_mul] at this
  rcases mul_eq_zero.1 this with h | h
  · exact hx.1 h
  · exact hy.1 h

theorem EvToK.mul {x y : RatFunc K} {v w : 𝔽} (hx : EvToK b x v) (hy : EvToK b y w) :
    EvToK b (x * y) (v * w) := by
  refine ⟨fun h0 => ?_, by rw [RatFunc.eval_mul (f := algebraMap K 𝔽) (a := b) hx.1 hy.1, hx.2, hy.2]⟩
  obtain ⟨q, hq⟩ := RatFunc.denom_mul_dvd x y
  have := congrArg (Polynomial.eval₂ (algebraMap K 𝔽) b) hq
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, h0, zero_mul] at this
  rcases mul_eq_zero.1 this with h | h
  · exact hx.1 h
  · exact hy.1 h

theorem evToK_C (q : K) : EvToK b (RatFunc.C q) (algebraMap K 𝔽 q) := by
  refine ⟨?_, RatFunc.eval_C (f := algebraMap K 𝔽) (a := b)⟩
  rw [RatFunc.denom_C, Polynomial.eval₂_one]
  exact one_ne_zero

theorem evToK_X : EvToK b (RatFunc.X : RatFunc K) b := by
  refine ⟨?_, RatFunc.eval_X (f := algebraMap K 𝔽) (a := b)⟩
  rw [RatFunc.denom_X, Polynomial.eval₂_one]
  exact one_ne_zero

theorem evToK_one : EvToK b (1 : RatFunc K) 1 := by
  have := evToK_C (K := K) (b := b) 1
  rwa [map_one, map_one] at this

theorem evToK_zero : EvToK b (0 : RatFunc K) 0 := by
  have := evToK_C (K := K) (b := b) 0
  rwa [map_zero, map_zero] at this

theorem evToK_intCast (n : ℤ) : EvToK b ((n : RatFunc K)) (n : 𝔽) := by
  have := evToK_C (K := K) (b := b) (n : K)
  rwa [map_intCast, map_intCast] at this

theorem evToK_natCast (n : ℕ) : EvToK b ((n : RatFunc K)) (n : 𝔽) := by
  have := evToK_C (K := K) (b := b) (n : K)
  rwa [map_natCast, map_natCast] at this

theorem evToK_ofNat (n : ℕ) [n.AtLeastTwo] :
    EvToK b (OfNat.ofNat n : RatFunc K) (OfNat.ofNat n : 𝔽) := by
  have := evToK_natCast (K := K) (b := b) (OfNat.ofNat n)
  simpa only [Nat.cast_ofNat] using this

theorem EvToK.neg {x : RatFunc K} {v : 𝔽} (hx : EvToK b x v) : EvToK b (-x) (-v) := by
  have := (evToK_intCast (b := b) (-1)).mul hx
  simpa using this

theorem EvToK.sub {x y : RatFunc K} {v w : 𝔽} (hx : EvToK b x v) (hy : EvToK b y w) :
    EvToK b (x - y) (v - w) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hx.add hy.neg

theorem EvToK.pow {x : RatFunc K} {v : 𝔽} (hx : EvToK b x v) (n : ℕ) : EvToK b (x ^ n) (v ^ n) := by
  induction n with
  | zero => simpa using evToK_one (K := K) (b := b)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx

theorem EvToK.inv {x : RatFunc K} {v : 𝔽} (hx : EvToK b x v) (hv : v ≠ 0) : EvToK b x⁻¹ v⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hv (by rw [← hx.2]; exact RatFunc.eval_zero (f := algebraMap K 𝔽) (a := b))
  have hnum : Polynomial.eval₂ (algebraMap K 𝔽) b (RatFunc.num x) ≠ 0 := by
    intro h0
    apply hv
    rw [← hx.2, RatFunc.eval, h0, zero_div]
  have hreg : Polynomial.eval₂ (algebraMap K 𝔽) b (RatFunc.denom x⁻¹) ≠ 0 := by
    intro h0
    have e : x⁻¹ = algebraMap K[X] (RatFunc K) (RatFunc.denom x)
        / algebraMap K[X] (RatFunc K) (RatFunc.num x) := by
      conv_lhs => rw [← RatFunc.num_div_denom x, inv_div]
    obtain ⟨q, hq⟩ := RatFunc.denom_div_dvd (RatFunc.denom x) (RatFunc.num x)
    rw [← e] at hq
    have := congrArg (Polynomial.eval₂ (algebraMap K 𝔽) b) hq
    rw [Polynomial.eval₂_mul, h0, zero_mul] at this
    exact hnum this
  refine ⟨hreg, ?_⟩
  have h1 := RatFunc.eval_mul (f := algebraMap K 𝔽) (a := b) hreg hx.1
  rw [inv_mul_cancel₀ hx0, RatFunc.eval_one (f := algebraMap K 𝔽) (a := b), hx.2] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem EvToK.div {x y : RatFunc K} {v w : 𝔽} (hx : EvToK b x v) (hy : EvToK b y w)
    (hw : w ≠ 0) : EvToK b (x / y) (v / w) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hx.mul (hy.inv hw)

theorem EvToK.prod {ι : Type*} (s : Finset ι) {x : ι → RatFunc K} {v : ι → 𝔽}
    (h : ∀ i ∈ s, EvToK b (x i) (v i)) : EvToK b (∏ i ∈ s, x i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evToK_one (K := K) (b := b)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem evToK_kacC (hb : b ≠ 0) : EvToK b (kacC (RatFunc.X : RatFunc K)) (kacC b) := by
  unfold kacC
  exact evToK_one.add ((evToK_ofNat 6).mul ((evToK_X.add (evToK_X.inv hb)).pow 2))

theorem evToK_kacH (hb : b ≠ 0) (r s : ℤ) :
    EvToK b (kacH r s (RatFunc.X : RatFunc K)) (kacH r s b) := by
  unfold kacH
  refine EvToK.div (((evToK_X.add (evToK_X.inv hb)).pow 2).sub
    ((((evToK_intCast r).mul evToK_X).add ((evToK_intCast s).mul (evToK_X.inv hb))).pow 2))
    (evToK_ofNat 4) ?_
  norm_num

variable (b)

variable (K)

/-- The subalgebra of `ℚ(b)` of functions regular at `b`. -/
def regSubK : Subalgebra K (RatFunc K) where
  carrier := {x | Polynomial.eval₂ (algebraMap K 𝔽) b (RatFunc.denom x) ≠ 0}
  mul_mem' := fun {x y} hx hy => (EvToK.mul (b := b) ⟨hx, rfl⟩ ⟨hy, rfl⟩).1
  add_mem' := fun {x y} hx hy => (EvToK.add (b := b) ⟨hx, rfl⟩ ⟨hy, rfl⟩).1
  algebraMap_mem' := fun q => by
    have e : algebraMap K (RatFunc K) q = RatFunc.C q := rfl
    rw [e]
    exact (evToK_C (b := b) q).1

/-- Evaluation at `b`, as a ring homomorphism on the functions regular at `b`. -/
noncomputable def evRegK : regSubK K b →+* 𝔽 where
  toFun x := RatFunc.eval (algebraMap K 𝔽) b x.1
  map_one' := RatFunc.eval_one (f := algebraMap K 𝔽) (a := b)
  map_mul' x y := RatFunc.eval_mul (f := algebraMap K 𝔽) (a := b) x.2 y.2
  map_zero' := RatFunc.eval_zero (f := algebraMap K 𝔽) (a := b)
  map_add' x y := RatFunc.eval_add (f := algebraMap K 𝔽) (a := b) x.2 y.2

variable {b}

theorem evRegK_mk {x : RatFunc K} {v : 𝔽} (hx : EvToK b x v) :
    evRegK K b ⟨x, hx.1⟩ = v := hx.2

end Virasoro
