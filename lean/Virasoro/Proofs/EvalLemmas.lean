import Virasoro.Proofs.GramDet
import Virasoro.Statements.Prelude
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic.FieldSimp

/-!
# Evaluation of rational functions at regular points, and of the block coefficients
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K]

/-- The rational function `x` is regular at `z`: its reduced denominator does not vanish. -/
def RegAt (z : K) (x : RatFunc K) : Prop := (RatFunc.denom x).eval z ≠ 0

/-- Evaluation at `z`. -/
noncomputable abbrev evalAt (z : K) (x : RatFunc K) : K := RatFunc.eval (RingHom.id K) z x

theorem RegAt.add {z : K} {x y : RatFunc K} (hx : RegAt z x) (hy : RegAt z y) : RegAt z (x + y) := by
  intro h
  obtain ⟨r, hr⟩ := RatFunc.denom_add_dvd x y
  have := congrArg (Polynomial.eval z) hr
  rw [eval_mul, eval_mul, h, zero_mul] at this
  exact mul_ne_zero hx hy this

theorem RegAt.mul {z : K} {x y : RatFunc K} (hx : RegAt z x) (hy : RegAt z y) : RegAt z (x * y) := by
  intro h
  obtain ⟨r, hr⟩ := RatFunc.denom_mul_dvd x y
  have := congrArg (Polynomial.eval z) hr
  rw [eval_mul, eval_mul, h, zero_mul] at this
  exact mul_ne_zero hx hy this

theorem regAt_algebraMap (z : K) (p : K[X]) : RegAt z (algebraMap K[X] (RatFunc K) p) := by
  simp [RegAt, RatFunc.denom_algebraMap]

theorem regAt_div (z : K) (p : K[X]) {q : K[X]} (hq : q.eval z ≠ 0) :
    RegAt z (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) := by
  intro h
  obtain ⟨r, hr⟩ := RatFunc.denom_div_dvd p q
  have := congrArg (Polynomial.eval z) hr
  rw [eval_mul, h, zero_mul] at this
  exact hq this

theorem regAt_zero (z : K) : RegAt z (0 : RatFunc K) := by
  simp [RegAt]

theorem RegAt.sum {α : Type*} {z : K} {s : Finset α} {f : α → RatFunc K}
    (h : ∀ i ∈ s, RegAt z (f i)) : RegAt z (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regAt_zero z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem evalAt_add {z : K} {x y : RatFunc K} (hx : RegAt z x) (hy : RegAt z y) :
    evalAt z (x + y) = evalAt z x + evalAt z y :=
  RatFunc.eval_add (f := RingHom.id K) (a := z) (by simpa [RegAt, Polynomial.eval₂_id] using hx)
    (by simpa [RegAt, Polynomial.eval₂_id] using hy)

theorem evalAt_mul {z : K} {x y : RatFunc K} (hx : RegAt z x) (hy : RegAt z y) :
    evalAt z (x * y) = evalAt z x * evalAt z y :=
  RatFunc.eval_mul (f := RingHom.id K) (a := z) (by simpa [RegAt, Polynomial.eval₂_id] using hx)
    (by simpa [RegAt, Polynomial.eval₂_id] using hy)

theorem evalAt_sum {α : Type*} {z : K} {s : Finset α} {f : α → RatFunc K}
    (h : ∀ i ∈ s, RegAt z (f i)) : evalAt z (∑ i ∈ s, f i) = ∑ i ∈ s, evalAt z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalAt]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add (h a (Finset.mem_insert_self a s))
        (RegAt.sum fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem evalAt_algebraMap (z : K) (p : K[X]) :
    evalAt z (algebraMap K[X] (RatFunc K) p) = p.eval z := by
  simp [evalAt, RatFunc.eval, Polynomial.eval₂_id]

/-- Evaluation of a quotient of polynomials at a point where the denominator does not vanish. -/
theorem evalAt_div (z : K) (p : K[X]) {q : K[X]} (hq : q.eval z ≠ 0) :
    evalAt z (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      p.eval z / q.eval z := by
  set x := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q with hx
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq; simp at hq
  have hreg : RegAt z x := regAt_div z p hq
  have hmul : x * algebraMap K[X] (RatFunc K) q = algebraMap K[X] (RatFunc K) p := by
    rw [hx, div_mul_cancel₀]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 hq0
  have h1 := congrArg (evalAt z) hmul
  rw [evalAt_mul hreg (regAt_algebraMap z q), evalAt_algebraMap, evalAt_algebraMap] at h1
  rw [eq_div_iff hq]
  exact h1

/-! ### The block coefficients at a point -/

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `F_N(c,z,d)` computed by Cramer's rule at the point `z`. -/
noncomputable def Fval (c d z : 𝔽) (M : ℕ) : 𝔽 :=
  (∑ Y, ∑ Y', (gram c z M).adjugate Y Y' * torus c z d M Y Y') / (gram c z M).det

/-- `H_N(c,z,d) = ∑ η_j F_{N-j}(c,z,d)` at the point `z`. -/
noncomputable def Hval (c d z : 𝔽) (N : ℕ) : 𝔽 :=
  ∑ j ∈ Finset.range (N + 1), (eta j : 𝔽) * Fval c d z (N - j)

theorem gramPoly_eval (c z : 𝔽) (M : ℕ) :
    (gramPoly c M).map (Polynomial.eval z) = gram c z M := by
  have := gram_map (Polynomial.evalRingHom z) (C c) (X : 𝔽[X]) M
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  exact this.symm

theorem torusPoly_eval (c d z : 𝔽) (M : ℕ) :
    (torusPoly c d M).map (Polynomial.eval z) = torus c z d M := by
  have := torus_map (Polynomial.evalRingHom z) (C c) (X : 𝔽[X]) (C d) M
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  exact this.symm

theorem gramPoly_det_eval (c z : 𝔽) (M : ℕ) :
    (gramPoly c M).det.eval z = (gram c z M).det := by
  rw [← gramPoly_eval]
  exact RingHom.map_det (Polynomial.evalRingHom z) (gramPoly c M)

theorem Fnum_eval (c d z : 𝔽) (M : ℕ) :
    (Fnum c d M).eval z = ∑ Y, ∑ Y', (gram c z M).adjugate Y Y' * torus c z d M Y Y' := by
  unfold Fnum
  rw [← gramPoly_eval, ← torusPoly_eval, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [Polynomial.eval_mul]
  have h := RingHom.map_adjugate (Polynomial.evalRingHom z) (gramPoly c M)
  have h2 := congrFun (congrFun h Y) Y'
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom] at h2
  rw [h2]
  rfl

theorem regAt_Frat {c d z : 𝔽} {M : ℕ} (h : (gram c z M).det ≠ 0) : RegAt z (Frat c d M) :=
  regAt_div z _ (by rwa [gramPoly_det_eval])

theorem evalAt_Frat {c d z : 𝔽} {M : ℕ} (h : (gram c z M).det ≠ 0) :
    evalAt z (Frat c d M) = Fval c d z M := by
  unfold Frat Fval
  rw [evalAt_div z _ (by rwa [gramPoly_det_eval]), Fnum_eval, gramPoly_det_eval]

theorem regAt_intCast (z : 𝔽) (n : ℤ) : RegAt z ((n : RatFunc 𝔽)) := by
  have : ((n : RatFunc 𝔽)) = algebraMap 𝔽[X] (RatFunc 𝔽) (n : 𝔽[X]) := by simp
  rw [this]
  exact regAt_algebraMap z _

theorem evalAt_intCast (z : 𝔽) (n : ℤ) : evalAt z ((n : RatFunc 𝔽)) = (n : 𝔽) := by
  have : ((n : RatFunc 𝔽)) = algebraMap 𝔽[X] (RatFunc 𝔽) (n : 𝔽[X]) := by simp
  rw [this, evalAt_algebraMap]
  simp

theorem regAt_Hrat {c d z : 𝔽} {N : ℕ} (h : ∀ M ≤ N, (gram c z M).det ≠ 0) :
    RegAt z (Hrat c d N) := by
  unfold Hrat
  refine RegAt.sum fun j hj => (regAt_intCast z _).mul (regAt_Frat (h _ (Nat.sub_le N j)))

/-- At a point `z` where no Shapovalov determinant of level at most `N` vanishes, the value of
`H_N` is given by Cramer's rule. -/
theorem evalAt_Hrat {c d z : 𝔽} {N : ℕ} (h : ∀ M ≤ N, (gram c z M).det ≠ 0) :
    evalAt z (Hrat c d N) = Hval c d z N := by
  unfold Hrat Hval
  rw [evalAt_sum fun j hj => (regAt_intCast z _).mul (regAt_Frat (h _ (Nat.sub_le N j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evalAt_mul (regAt_intCast z _) (regAt_Frat (h _ (Nat.sub_le N j))), evalAt_intCast,
    evalAt_Frat (h _ (Nat.sub_le N j))]

end Virasoro
