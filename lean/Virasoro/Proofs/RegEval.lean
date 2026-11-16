import Virasoro.Kac
import Virasoro.Residue
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Rational functions of `b` over `ℚ` regular at a point of a field

For a field `𝔽` of characteristic zero and `b : 𝔽`, the rational functions `x ∈ ℚ(b)` whose
denominator does not vanish at `b` form a subalgebra, and evaluation at `b` is a ring
homomorphism from it to `𝔽`.  Identities of rational functions of `b` over `ℚ` specialize along
this homomorphism.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] (b : 𝔽)

/-- `x ∈ ℚ(b)` is regular at `b` and takes the value `v` there. -/
def EvTo (x : RatFunc ℚ) (v : 𝔽) : Prop :=
  Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom x) ≠ 0 ∧
    RatFunc.eval (algebraMap ℚ 𝔽) b x = v

variable {b}

theorem EvTo.add {x y : RatFunc ℚ} {v w : 𝔽} (hx : EvTo b x v) (hy : EvTo b y w) :
    EvTo b (x + y) (v + w) := by
  refine ⟨fun h0 => ?_, by rw [RatFunc.eval_add (f := algebraMap ℚ 𝔽) (a := b) hx.1 hy.1, hx.2, hy.2]⟩
  obtain ⟨q, hq⟩ := RatFunc.denom_add_dvd x y
  have := congrArg (Polynomial.eval₂ (algebraMap ℚ 𝔽) b) hq
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, h0, zero_mul] at this
  rcases mul_eq_zero.1 this with h | h
  · exact hx.1 h
  · exact hy.1 h

theorem EvTo.mul {x y : RatFunc ℚ} {v w : 𝔽} (hx : EvTo b x v) (hy : EvTo b y w) :
    EvTo b (x * y) (v * w) := by
  refine ⟨fun h0 => ?_, by rw [RatFunc.eval_mul (f := algebraMap ℚ 𝔽) (a := b) hx.1 hy.1, hx.2, hy.2]⟩
  obtain ⟨q, hq⟩ := RatFunc.denom_mul_dvd x y
  have := congrArg (Polynomial.eval₂ (algebraMap ℚ 𝔽) b) hq
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, h0, zero_mul] at this
  rcases mul_eq_zero.1 this with h | h
  · exact hx.1 h
  · exact hy.1 h

theorem evTo_C (q : ℚ) : EvTo b (RatFunc.C q) (algebraMap ℚ 𝔽 q) := by
  refine ⟨?_, RatFunc.eval_C (f := algebraMap ℚ 𝔽) (a := b)⟩
  rw [RatFunc.denom_C, Polynomial.eval₂_one]
  exact one_ne_zero

theorem evTo_X : EvTo b (RatFunc.X : RatFunc ℚ) b := by
  refine ⟨?_, RatFunc.eval_X (f := algebraMap ℚ 𝔽) (a := b)⟩
  rw [RatFunc.denom_X, Polynomial.eval₂_one]
  exact one_ne_zero

theorem evTo_one : EvTo b (1 : RatFunc ℚ) 1 := by
  have := evTo_C (b := b) 1
  rwa [map_one, map_one] at this

theorem evTo_zero : EvTo b (0 : RatFunc ℚ) 0 := by
  have := evTo_C (b := b) 0
  rwa [map_zero, map_zero] at this

theorem evTo_intCast (n : ℤ) : EvTo b ((n : RatFunc ℚ)) (n : 𝔽) := by
  have := evTo_C (b := b) (n : ℚ)
  rwa [map_intCast, map_intCast] at this

theorem evTo_natCast (n : ℕ) : EvTo b ((n : RatFunc ℚ)) (n : 𝔽) := by
  have := evTo_C (b := b) (n : ℚ)
  rwa [map_natCast, map_natCast] at this

theorem evTo_ofNat (n : ℕ) [n.AtLeastTwo] :
    EvTo b (OfNat.ofNat n : RatFunc ℚ) (OfNat.ofNat n : 𝔽) := by
  have := evTo_natCast (b := b) (OfNat.ofNat n)
  simpa only [Nat.cast_ofNat] using this

theorem EvTo.neg {x : RatFunc ℚ} {v : 𝔽} (hx : EvTo b x v) : EvTo b (-x) (-v) := by
  have := (evTo_intCast (b := b) (-1)).mul hx
  simpa using this

theorem EvTo.sub {x y : RatFunc ℚ} {v w : 𝔽} (hx : EvTo b x v) (hy : EvTo b y w) :
    EvTo b (x - y) (v - w) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hx.add hy.neg

theorem EvTo.pow {x : RatFunc ℚ} {v : 𝔽} (hx : EvTo b x v) (n : ℕ) : EvTo b (x ^ n) (v ^ n) := by
  induction n with
  | zero => simpa using evTo_one (b := b)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx

theorem EvTo.inv {x : RatFunc ℚ} {v : 𝔽} (hx : EvTo b x v) (hv : v ≠ 0) : EvTo b x⁻¹ v⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hv (by rw [← hx.2]; exact RatFunc.eval_zero (f := algebraMap ℚ 𝔽) (a := b))
  have hnum : Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.num x) ≠ 0 := by
    intro h0
    apply hv
    rw [← hx.2, RatFunc.eval, h0, zero_div]
  have hreg : Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom x⁻¹) ≠ 0 := by
    intro h0
    have e : x⁻¹ = algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom x)
        / algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num x) := by
      conv_lhs => rw [← RatFunc.num_div_denom x, inv_div]
    obtain ⟨q, hq⟩ := RatFunc.denom_div_dvd (RatFunc.denom x) (RatFunc.num x)
    rw [← e] at hq
    have := congrArg (Polynomial.eval₂ (algebraMap ℚ 𝔽) b) hq
    rw [Polynomial.eval₂_mul, h0, zero_mul] at this
    exact hnum this
  refine ⟨hreg, ?_⟩
  have h1 := RatFunc.eval_mul (f := algebraMap ℚ 𝔽) (a := b) hreg hx.1
  rw [inv_mul_cancel₀ hx0, RatFunc.eval_one (f := algebraMap ℚ 𝔽) (a := b), hx.2] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem EvTo.div {x y : RatFunc ℚ} {v w : 𝔽} (hx : EvTo b x v) (hy : EvTo b y w)
    (hw : w ≠ 0) : EvTo b (x / y) (v / w) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hx.mul (hy.inv hw)

theorem EvTo.prod {ι : Type*} (s : Finset ι) {x : ι → RatFunc ℚ} {v : ι → 𝔽}
    (h : ∀ i ∈ s, EvTo b (x i) (v i)) : EvTo b (∏ i ∈ s, x i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evTo_one (b := b)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem evTo_kacC (hb : b ≠ 0) : EvTo b (kacC (RatFunc.X : RatFunc ℚ)) (kacC b) := by
  unfold kacC
  exact evTo_one.add ((evTo_ofNat 6).mul ((evTo_X.add (evTo_X.inv hb)).pow 2))

theorem evTo_kacH (hb : b ≠ 0) (r s : ℤ) :
    EvTo b (kacH r s (RatFunc.X : RatFunc ℚ)) (kacH r s b) := by
  unfold kacH
  refine EvTo.div (((evTo_X.add (evTo_X.inv hb)).pow 2).sub
    ((((evTo_intCast r).mul evTo_X).add ((evTo_intCast s).mul (evTo_X.inv hb))).pow 2))
    (evTo_ofNat 4) ?_
  norm_num

variable (b)

/-- The subalgebra of `ℚ(b)` of functions regular at `b`. -/
def regSub : Subalgebra ℚ (RatFunc ℚ) where
  carrier := {x | Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom x) ≠ 0}
  mul_mem' := fun {x y} hx hy => (EvTo.mul (b := b) ⟨hx, rfl⟩ ⟨hy, rfl⟩).1
  add_mem' := fun {x y} hx hy => (EvTo.add (b := b) ⟨hx, rfl⟩ ⟨hy, rfl⟩).1
  algebraMap_mem' := fun q => by
    have e : algebraMap ℚ (RatFunc ℚ) q = RatFunc.C q :=
      RingHom.congr_fun (Subsingleton.elim _ _) q
    rw [e]
    exact (evTo_C (b := b) q).1

/-- Evaluation at `b`, as a ring homomorphism on the functions regular at `b`. -/
noncomputable def evReg : regSub b →+* 𝔽 where
  toFun x := RatFunc.eval (algebraMap ℚ 𝔽) b x.1
  map_one' := RatFunc.eval_one (f := algebraMap ℚ 𝔽) (a := b)
  map_mul' x y := RatFunc.eval_mul (f := algebraMap ℚ 𝔽) (a := b) x.2 y.2
  map_zero' := RatFunc.eval_zero (f := algebraMap ℚ 𝔽) (a := b)
  map_add' x y := RatFunc.eval_add (f := algebraMap ℚ 𝔽) (a := b) x.2 y.2

variable {b}

theorem evReg_mk {x : RatFunc ℚ} {v : 𝔽} (hx : EvTo b x v) :
    evReg b ⟨x, hx.1⟩ = v := hx.2

end Virasoro
