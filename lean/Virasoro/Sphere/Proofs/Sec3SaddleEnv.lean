import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Sphere paper Lemma 3.4(iii): stationarity (`sphere/paper.tex` l.800–804)

The derivative of the saddle value along the saddle point is the explicit derivative: with
`Φ = ∑_m (-2m x_m r_m² + 4h_m x_m r_m) - 2∑_{m,n} b_{m,n} x_m x_n r_m r_n` and `A_m = m r_m`,
`θΦ = 2∑_m x_m A_m² - 4∑_m x_m (A_m + θr_m)(A_m - h_m + ∑_n b_{m,n} x_n r_n)`,
where the last factor is the saddle-point equation.  This is the algebraic identity behind
`z d𝓘₀/dz = 2∑_m m² z^{-m} σ_m σ̄_m`; `dA m` stands for `θA_m`, `u m` for `1/m`, `nn m` for `m`.

Consumer: `Sec3SaddleI0c.lean`.
-/

namespace Virasoro.Sphere

open Finset

theorem envelope_identity {R : Type*} [CommRing R] (I : Finset ℕ) (x A dA u h nn : ℕ → R)
    (b : ℕ → ℕ → R) (hb : ∀ m n, b m n = b n m) (hu : ∀ m ∈ I, nn m * u m = 1)
    (hx : ∀ m n, x (m + n) = x m * x n) :
    -2 * ∑ n ∈ I, u n * (nn n * x n * (A n * A n) + x n * (dA n * A n + A n * dA n)) +
        2 * (∑ n ∈ I, (2 * h n * u n) * (nn n * x n * A n + x n * dA n) +
          ∑ m ∈ I, ∑ n ∈ I, (-(b m n * u m * u n)) *
            ((nn m + nn n) * x (m + n) * (A m * A n) +
              x (m + n) * (dA m * A n + A m * dA n))) =
      2 * ∑ m ∈ I, x m * (A m * A m) -
        4 * ∑ m ∈ I, x m * (A m + u m * dA m) *
          (A m - h m + ∑ n ∈ I, (b m n * u n) * (x n * A n)) := by
  -- the single sums
  have e1 : -2 * ∑ n ∈ I, u n * (nn n * x n * (A n * A n) + x n * (dA n * A n + A n * dA n)) +
        2 * (∑ n ∈ I, (2 * h n * u n) * (nn n * x n * A n + x n * dA n) +
          ∑ m ∈ I, ∑ n ∈ I, (-(b m n * u m * u n)) *
            ((nn m + nn n) * x (m + n) * (A m * A n) +
              x (m + n) * (dA m * A n + A m * dA n))) =
      ∑ n ∈ I, (-2 * (u n * (nn n * x n * (A n * A n) + x n * (dA n * A n + A n * dA n))) +
          2 * ((2 * h n * u n) * (nn n * x n * A n + x n * dA n))) +
        ∑ m ∈ I, ∑ n ∈ I, 2 * ((-(b m n * u m * u n)) *
            ((nn m + nn n) * x (m + n) * (A m * A n) +
              x (m + n) * (dA m * A n + A m * dA n))) := by
    simp only [sum_add_distrib, ← mul_sum]
    ring
  have hm : ∀ m, x m * (A m + u m * dA m) *
      (A m - h m + ∑ n ∈ I, (b m n * u n) * (x n * A n)) =
      x m * (A m + u m * dA m) * (A m - h m) +
        ∑ n ∈ I, x m * (A m + u m * dA m) * ((b m n * u n) * (x n * A n)) := fun m => by
    rw [mul_add, mul_sum]
  have e2 : 2 * ∑ m ∈ I, x m * (A m * A m) -
        4 * ∑ m ∈ I, x m * (A m + u m * dA m) *
          (A m - h m + ∑ n ∈ I, (b m n * u n) * (x n * A n)) =
      ∑ m ∈ I, (2 * (x m * (A m * A m)) - 4 * (x m * (A m + u m * dA m) * (A m - h m))) +
        ∑ m ∈ I, ∑ n ∈ I, -4 * (x m * (A m + u m * dA m) * ((b m n * u n) * (x n * A n))) := by
    simp only [hm, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    ring
  rw [e1, e2]
  congr 1
  · refine sum_congr rfl fun n hn => ?_
    linear_combination (-2 * x n * (A n * A n) + 4 * h n * x n * A n) * hu n hn
  · -- the double sums: symmetrize
    have hsplit : ∀ m n, 2 * ((-(b m n * u m * u n)) *
          ((nn m + nn n) * x (m + n) * (A m * A n) +
            x (m + n) * (dA m * A n + A m * dA n))) =
        (-2 * (b m n * u m * u n * x m * x n * (nn m * A m * A n + dA m * A n))) +
          (-2 * (b n m * u n * u m * x n * x m * (nn n * A n * A m + dA n * A m))) := by
      intro m n
      rw [hx, hb n m]
      ring
    simp only [hsplit, sum_add_distrib]
    rw [sum_comm (f := fun m n =>
      -2 * (b n m * u n * u m * x n * x m * (nn n * A n * A m + dA n * A m))),
      ← sum_add_distrib]
    refine sum_congr rfl fun m hm' => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    linear_combination (-4 * b m n * u n * x m * x n * A m * A n) * hu m hm'

end Virasoro.Sphere
