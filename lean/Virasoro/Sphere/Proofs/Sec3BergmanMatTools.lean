import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Matrix tools for sphere paper Lemma 3.5 (`sphere/paper.tex` l.835–866, l.941–945)

* a matrix whose rows outside the image of an embedding vanish has the same powers, on that
  image, as its submatrix (truncation of `M(z)` modulo a power of `z`);
* `x ∣ M i j` for all entries gives `x^k ∣ (M^k) i j`;
* a derivation applied to `Tr(M^{j+1})` gives `(j+1) Tr(δM · M^j)`.

Consumer: `Sec3BergmanTrace.lean`.
-/

namespace Virasoro.Sphere

open Matrix Finset

section Trunc

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

theorem sum_eq_sum_emb (e : κ ↪ ι) (f : ι → R) (hf : ∀ i, i ∉ Set.range e → f i = 0) :
    ∑ i, f i = ∑ a, f (e a) := by
  rw [← Finset.sum_map Finset.univ e f]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  simpa using hi

theorem pow_succ_zero_row (e : κ ↪ ι) (M : Matrix ι ι R)
    (hM : ∀ i, i ∉ Set.range e → ∀ j, M i j = 0) (k : ℕ) :
    ∀ i, i ∉ Set.range e → ∀ j, (M ^ (k + 1)) i j = 0 := by
  intro i hi j
  rw [pow_succ', Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hM i hi l, zero_mul]

theorem pow_submatrix_emb (e : κ ↪ ι) (M : Matrix ι ι R)
    (hM : ∀ i, i ∉ Set.range e → ∀ j, M i j = 0) (k : ℕ) (a b : κ) :
    (M ^ (k + 1)) (e a) (e b) = ((M.submatrix e e) ^ (k + 1)) a b := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' M, pow_succ' (M.submatrix e e), Matrix.mul_apply, Matrix.mul_apply,
      sum_eq_sum_emb e _ (fun i hi => by rw [pow_succ_zero_row e M hM k i hi, mul_zero])]
    exact Finset.sum_congr rfl fun c _ => by rw [ih]; rfl

theorem trace_diag_mul_pow_emb (e : κ ↪ ι) (M : Matrix ι ι R)
    (hM : ∀ i, i ∉ Set.range e → ∀ j, M i j = 0) (d : ι → R) (k : ℕ) :
    trace (diagonal d * M ^ (k + 1)) =
      trace (diagonal (fun a => d (e a)) * (M.submatrix e e) ^ (k + 1)) := by
  simp only [trace, diag_apply, diagonal_mul]
  rw [sum_eq_sum_emb e _ (fun i hi => by rw [pow_succ_zero_row e M hM k i hi, mul_zero])]
  exact Finset.sum_congr rfl fun a _ => by rw [pow_submatrix_emb e M hM]

theorem dvd_pow_entry (x : R) (M : Matrix ι ι R) (hM : ∀ i j, x ∣ M i j) (k : ℕ) :
    ∀ i j, x ^ k ∣ (M ^ k) i j := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    rw [pow_succ x, pow_succ M, Matrix.mul_apply]
    exact Finset.dvd_sum fun l _ => mul_dvd_mul (ih i l) (hM l j)

theorem dvd_trace_diag_mul_pow (x : R) (M : Matrix ι ι R) (hM : ∀ i j, x ∣ M i j) (d : ι → R)
    (k : ℕ) : x ^ k ∣ trace (diagonal d * M ^ k) := by
  simp only [trace, diag_apply, diagonal_mul]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_pow_entry x M hM k i i) _

end Trunc

section Deriv

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] (δ : Derivation S R R)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_mul_deriv (A B : Matrix ι ι R) :
    (A * B).map δ = A.map δ * B + A * B.map δ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem trace_mul_map_pow (M : Matrix ι ι R) (j : ℕ) :
    ∀ A : Matrix ι ι R, Commute A M →
      trace (A * (M ^ (j + 1)).map δ) = ((j : R) + 1) * trace (A * M.map δ * M ^ j) := by
  induction j with
  | zero => intro A _; simp
  | succ j ih =>
    intro A hA
    have h1 : trace (A * M * M.map δ * M ^ j) = trace (A * M.map δ * M ^ (j + 1)) := by
      rw [hA.eq, Matrix.mul_assoc M A, Matrix.mul_assoc M, trace_mul_comm,
        Matrix.mul_assoc (A * M.map δ), ← pow_succ]
    rw [pow_succ' M (j + 1), map_mul_deriv, mul_add, trace_add, ← Matrix.mul_assoc A M,
      ih (A * M) (hA.mul_left (Commute.refl M)), h1, ← Matrix.mul_assoc A (M.map δ)]
    push_cast
    ring

theorem trace_map_deriv (M : Matrix ι ι R) : trace (M.map δ) = δ (trace M) := by
  simp [trace, map_sum]

/-- `δ Tr(M^{j+1}) = (j+1) Tr(δM · M^j)`. -/
theorem deriv_trace_pow (M : Matrix ι ι R) (j : ℕ) :
    δ (trace (M ^ (j + 1))) = ((j : R) + 1) * trace (M.map δ * M ^ j) := by
  have h := trace_mul_map_pow δ M j 1 (Commute.one_left M)
  rwa [Matrix.one_mul, Matrix.one_mul, trace_map_deriv] at h

end Deriv

end Virasoro.Sphere
