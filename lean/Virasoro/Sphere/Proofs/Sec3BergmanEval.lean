import Virasoro.Sphere.Proofs.Sec3BergmanRows
import Virasoro.Sphere.Proofs.Sec3BergmanLiouTools
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Sphere paper Lemma 3.5, Step 1 on the unit disc (`sphere/paper.tex` l.880–889)

For `|x| < 1`: `∑_k h_k x^k = (1-x)^{-1/2}` (binomial series, here from `h(x)²(1-x) = 1`, continuity
and `h(0) = 1`), and the series identity of Step 1 evaluated at `x`,
`(1-x)^{-1/2} R_n(x) = 2n - 2 x^n ∑_m B_{m,n} x^m`, i.e. `f_n(1/x) = -½ x^{1-n}(1-x)^{-1/2}R_n(x)`
with `R_n(x) = -2 x^n P_n(1/x)`.

Consumer: the outer patch.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology Metric

theorem norm_ratCast_le {q c : ℚ} (h : |q| ≤ c) : ‖(q : ℂ)‖ ≤ (c : ℝ) := by
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast h

/-- The value at `x` of a power series with rational coefficients. -/
noncomputable def evq (f : PowerSeries ℚ) (x : ℂ) : ℂ := ∑' k : ℕ, ((coeff k f : ℚ) : ℂ) * x ^ k

/-- Absolute convergence at `x`. -/
def AbsC (f : PowerSeries ℚ) (x : ℂ) : Prop := Summable fun k : ℕ => ‖((coeff k f : ℚ) : ℂ) * x ^ k‖

theorem cauchy_term (f g : PowerSeries ℚ) (x : ℂ) (N : ℕ) :
    ∑ kl ∈ antidiagonal N, (((coeff kl.1 f : ℚ) : ℂ) * x ^ kl.1) * (((coeff kl.2 g : ℚ) : ℂ) * x ^ kl.2) =
      ((coeff N (f * g) : ℚ) : ℂ) * x ^ N := by
  rw [coeff_mul, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hkl' : kl.1 + kl.2 = N := by simpa using hkl
  rw [← hkl', pow_add, Rat.cast_mul]
  ring

theorem evq_mul {f g : PowerSeries ℚ} {x : ℂ} (hf : AbsC f x) (hg : AbsC g x) :
    evq f x * evq g x = evq (f * g) x := by
  rw [evq, evq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg, evq]
  exact tsum_congr fun N => cauchy_term f g x N

theorem summable_mul_of_absC {f g : PowerSeries ℚ} {x : ℂ} (hf : AbsC f x) (hg : AbsC g x) :
    Summable fun N : ℕ => ((coeff N (f * g) : ℚ) : ℂ) * x ^ N := by
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm
  simpa only [cauchy_term] using h

theorem absC_of_bound {f : PowerSeries ℚ} {x : ℂ} (hx : ‖x‖ < 1) {c : ℚ}
    (h : ∀ k, |coeff k f| ≤ c) : AbsC f x := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left (c : ℝ))
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (norm_ratCast_le (h k)) (pow_nonneg (norm_nonneg x) k)

theorem absC_hser {x : ℂ} (hx : ‖x‖ < 1) : AbsC hser x :=
  absC_of_bound hx (c := 1) fun k => by
    rw [hser, coeff_mk, abs_le]
    exact ⟨by linarith [halfBinom_nonneg k], halfBinom_le_one k⟩

theorem absC_Rrev {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) : AbsC (Rrev n) x :=
  absC_of_bound hx (c := 4 * (n : ℚ)) fun k => abs_coeff_Rrev_le n k

theorem absC_colB {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) : AbsC (colB n) x :=
  absC_of_bound hx (c := 2 * (n : ℚ) * ((n : ℚ) + 1)) fun k => by
    rw [colB, coeff_mk]
    exact Bcoef_abs_le k n

/-- `h(x) = ∑_k h_k x^k`, the binomial series of `(1-x)^{-1/2}`. -/
noncomputable def hfun (x : ℂ) : ℂ := evq hser x

theorem hser_sq_eq : hser ^ 2 = PowerSeries.mk (1 : ℕ → ℚ) := by
  have hU : PowerSeries.mk (1 : ℕ → ℚ) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℚ
  linear_combination PowerSeries.mk (1 : ℕ → ℚ) * hser_sq - hser ^ 2 * hU

theorem hfun_sq {x : ℂ} (hx : ‖x‖ < 1) : hfun x ^ 2 * (1 - x) = 1 := by
  have h1 : hfun x ^ 2 = (1 - x)⁻¹ := by
    rw [pow_two, hfun, evq_mul (absC_hser hx) (absC_hser hx), ← pow_two, hser_sq_eq, evq,
      ← tsum_geometric_of_norm_lt_one hx]
    exact tsum_congr fun k => by rw [coeff_mk, Pi.one_apply, Rat.cast_one, one_mul]
  rw [h1, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm (ne_one_of_norm_lt hx)))]

theorem continuousOn_hfun : ContinuousOn hfun (ball (0 : ℂ) 1) := by
  intro x hx
  have hx1 : ‖x‖ < 1 := by simpa using hx
  have hr : (‖x‖ + 1) / 2 < 1 := by linarith
  have hr0 : 0 ≤ (‖x‖ + 1) / 2 := by linarith [norm_nonneg x]
  have hc : ContinuousOn (fun y : ℂ => ∑' k : ℕ, ((coeff k hser : ℚ) : ℂ) * y ^ k)
      (ball (0 : ℂ) ((‖x‖ + 1) / 2)) :=
    continuousOn_tsum (fun k => by fun_prop) (summable_geometric_of_lt_one hr0 hr)
      fun k y hy => by
        have hy' : ‖y‖ < (‖x‖ + 1) / 2 := by simpa using hy
        rw [norm_mul, norm_pow]
        have h1 : ‖((coeff k hser : ℚ) : ℂ)‖ ≤ ((1 : ℚ) : ℝ) := norm_ratCast_le (by
          rw [hser, coeff_mk, abs_le]
          exact ⟨by linarith [halfBinom_nonneg k], halfBinom_le_one k⟩)
        rw [Rat.cast_one] at h1
        calc ‖((coeff k hser : ℚ) : ℂ)‖ * ‖y‖ ^ k ≤ 1 * ((‖x‖ + 1) / 2) ^ k :=
              mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg y) hy'.le k)
                (pow_nonneg (norm_nonneg y) k) zero_le_one
          _ = ((‖x‖ + 1) / 2) ^ k := one_mul _
  exact (hc.continuousAt (isOpen_ball.mem_nhds (by
    rw [mem_ball_zero_iff]; linarith))).continuousWithinAt

theorem hfun_zero : hfun 0 = 1 := by
  rw [hfun, evq, tsum_eq_single 0 fun k hk => by rw [zero_pow hk, mul_zero]]
  simp [hser, halfBinom, gbinom]

/-- The binomial series on the unit disc: `√(1-x) · ∑_k h_k x^k = 1`. -/
theorem sqrt_mul_hfun {x : ℂ} (hx : ‖x‖ < 1) : (1 - x) ^ (1 / 2 : ℂ) * hfun x = 1 := by
  have hf : ContinuousOn (fun y : ℂ => (1 - y) ^ (1 / 2 : ℂ) * hfun y) (ball (0 : ℂ) 1) :=
    ContinuousOn.mul (fun y hy => (differentiableAt_sqrt_one_sub
      (by simpa using hy)).continuousAt.continuousWithinAt) continuousOn_hfun
  have hsq : Set.EqOn ((fun y : ℂ => (1 - y) ^ (1 / 2 : ℂ) * hfun y) ^ 2)
      ((fun _ : ℂ => (1 : ℂ)) ^ 2) (ball (0 : ℂ) 1) := fun y hy => by
    have hy1 : ‖y‖ < 1 := by simpa using hy
    simp only [Pi.pow_apply]
    rw [mul_pow, cpow_half_sq, one_pow]
    linear_combination hfun_sq hy1
  have h0 : (fun y : ℂ => (1 - y) ^ (1 / 2 : ℂ) * hfun y) 0 = (fun _ : ℂ => (1 : ℂ)) 0 := by
    simp [hfun_zero]
  exact (convex_ball (0 : ℂ) 1).isPreconnected.eq_of_sq_eq hf continuousOn_const hsq
    (fun _ => one_ne_zero) (mem_ball_self one_pos) h0 (by simpa using hx)

/-- `∑_m B_{m,n} x^m`. -/
noncomputable def colBf (n : ℕ) (x : ℂ) : ℂ := evq (colB n) x

/-- `R_n(x) = ∑_{k ≤ n} ρ_{n,k} x^k`, the polynomial `-2 x^n P_n(1/x)` of Step 1. -/
noncomputable def Rf (n : ℕ) (x : ℂ) : ℂ := ∑ k ∈ range (n + 1), ((coeff k (Rrev n) : ℚ) : ℂ) * x ^ k

theorem evq_Rrev (n : ℕ) (x : ℂ) : evq (Rrev n) x = Rf n x := by
  rw [evq, Rf]
  refine tsum_eq_sum fun k hk => ?_
  rw [coeff_Rrev_of_lt (by simpa using hk), Rat.cast_zero, zero_mul]

/-- Step 1 evaluated on the unit disc (l.884–887): `(1-x)^{-1/2} R_n(x) = 2n - 2x^n ∑_m B_{m,n}x^m`
for `n ≥ 1`. -/
theorem colBf_closed {x : ℂ} (hx : ‖x‖ < 1) {n : ℕ} (hn : 1 ≤ n) :
    hfun x * Rf n x = 2 * (n : ℂ) - 2 * (x ^ n * colBf n x) := by
  have h2 : (C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
  have hn' : (C (n : ℚ) : PowerSeries ℚ) = n := map_natCast _ n
  have e2 : hser * Rrev n = C (2 : ℚ) * C (n : ℚ) - C 2 * (X ^ n * colB n) := by
    rw [h2, hn']
    linear_combination colB_eq n
  have hc : ∀ N, coeff N (hser * Rrev n) =
      2 * (if N = 0 then (n : ℚ) else 0) - 2 * (if n ≤ N then Bcoef (N - n) n else 0) := fun N => by
    rw [e2, map_sub, coeff_C_mul, coeff_C_mul, coeff_C, coeff_X_pow_mul', colB]
    simp only [coeff_mk]
  have hsum := summable_mul_of_absC (absC_hser hx) (absC_Rrev hx n)
  rw [← evq_Rrev, hfun, evq_mul (absC_hser hx) (absC_Rrev hx n), evq,
    ← hsum.sum_add_tsum_nat_add n]
  have p1 : ∑ N ∈ range n, ((coeff N (hser * Rrev n) : ℚ) : ℂ) * x ^ N = 2 * (n : ℂ) := by
    rw [Finset.sum_eq_single 0]
    · rw [hc 0, if_pos rfl, if_neg (by omega)]
      push_cast
      ring
    · intro N hN hN0
      rw [hc N, if_neg hN0, if_neg (by have := Finset.mem_range.1 hN; omega)]
      simp
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have p2 : ∀ N, ((coeff (N + n) (hser * Rrev n) : ℚ) : ℂ) * x ^ (N + n) =
      (-2 * x ^ n) * (((coeff N (colB n) : ℚ) : ℂ) * x ^ N) := fun N => by
    rw [hc (N + n), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel, colB, coeff_mk,
      pow_add]
    push_cast
    ring
  simp only [p2]
  rw [p1, tsum_mul_left, colBf, evq]
  ring

/-- `∑_{m ≥ 1} B_{m,n} x^m = x ∑_m B_{m+1,n} x^m`. -/
theorem colBf_shift {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    colBf n x = x * ∑' m : ℕ, (Bcoef (m + 1) n : ℂ) * x ^ m := by
  have hs : Summable fun k : ℕ => ((coeff k (colB n) : ℚ) : ℂ) * x ^ k := (absC_colB hx n).of_norm
  rw [colBf, evq, hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [colB, coeff_mk, Bcoef_zero_left, Rat.cast_zero, zero_mul, zero_add]
  exact tsum_congr fun m => by rw [pow_succ]; ring

end Virasoro.Sphere
