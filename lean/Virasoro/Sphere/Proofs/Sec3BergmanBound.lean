import Virasoro.Sphere.Proofs.Sec3BergmanStep1
import Virasoro.Sphere.Proofs.Sec3SaddlePsi
import Virasoro.Sphere.Proofs.Sec3SaddleOmega

/-!
# Sphere paper Lemma 3.5: the bound on `B_{m,n}` (`sphere/paper.tex` l.845–847, l.888–889)

The paper bounds `|B_{m,n}| ≤ C_ρ ρ^{-m-n}` for every `0 < ρ < 1` by Cauchy's inequality.  Here
the bound comes from the explicit coefficients of Step 1:
`p^n ∑_m B_{m,n} p^m = n - ½ (1-p)^{-1/2} ((2-p) U_n(p) - p U_{n-1}(p))`, the coefficients of
`(1-p)^{-1/2}` lie in `[0,1]` and those of `U_n` in `[0,n]`, so `|B_{m,n}| ≤ 2n(n+1)` for all
`m`, which gives the Cauchy bound for every `ρ < 1`.  The same estimate is the polynomial bound
`|[X^{n-k}] P_n(X)| = O(poly(n))` of l.888.

Consumer: the convergence of `[z^j] W_no(x₁,x₂)` in `Stmt_sub_bergman_liouville`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

theorem halfBinom_nonneg (k : ℕ) : 0 ≤ halfBinom k := by
  rw [halfBinom_eq]
  positivity

theorem halfBinom_le_one (k : ℕ) : halfBinom k ≤ 1 := by
  rw [halfBinom_eq, div_le_one (by positivity)]
  have h : Nat.centralBinom k ≤ 4 ^ k := by
    rw [Nat.centralBinom, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    exact Nat.choose_le_two_pow _ _
  exact_mod_cast h

theorem coeff_Useries (n k : ℕ) :
    coeff k (Useries n) = if k < n then ((n : ℚ) - k) * halfBinom k else 0 := by
  rw [Useries, coeff_mk]

theorem coeff_Useries_nonneg (n k : ℕ) : 0 ≤ coeff k (Useries n) := by
  rw [coeff_Useries]
  split_ifs with h
  · have : (k : ℚ) ≤ n := by exact_mod_cast h.le
    exact mul_nonneg (by linarith) (halfBinom_nonneg k)
  · exact le_rfl

theorem coeff_Useries_le (n k : ℕ) : coeff k (Useries n) ≤ n := by
  rw [coeff_Useries]
  split_ifs with h
  · have h1 : (k : ℚ) ≤ n := by exact_mod_cast h.le
    have h2 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    calc ((n : ℚ) - k) * halfBinom k ≤ ((n : ℚ) - k) * 1 :=
          mul_le_mul_of_nonneg_left (halfBinom_le_one k) (by linarith)
      _ ≤ n := by linarith
  · exact Nat.cast_nonneg n

/-- `-2 p^n P_n(1/p) = (2-p) U_n(p) - p U_{n-1}(p)`. -/
noncomputable def Rrev (n : ℕ) : PowerSeries ℚ :=
  (2 - X) * Useries n - X * Useries (n - 1)

theorem abs_coeff_Rrev_le (n k : ℕ) : |coeff k (Rrev n)| ≤ 4 * (n : ℚ) := by
  have e : Rrev n = Useries n + Useries n - X * Useries n - X * Useries (n - 1) := by
    rw [Rrev]; ring
  have a0 := coeff_Useries_nonneg n k
  have a1 := coeff_Useries_le n k
  have hn1 : (((n - 1 : ℕ) : ℚ)) ≤ n := by exact_mod_cast Nat.sub_le n 1
  rw [e, map_sub, map_sub, map_add]
  cases k with
  | zero =>
    rw [coeff_zero_X_mul, coeff_zero_X_mul, abs_le]
    constructor <;> linarith
  | succ k =>
    have b0 := coeff_Useries_nonneg n k
    have b1 := coeff_Useries_le n k
    have c0 := coeff_Useries_nonneg (n - 1) k
    have c1 := coeff_Useries_le (n - 1) k
    rw [coeff_succ_X_mul, coeff_succ_X_mul, abs_le]
    constructor <;> linarith

theorem coeff_Rrev_of_lt {n k : ℕ} (h : n < k) : coeff k (Rrev n) = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Rrev, sub_mul, map_sub, map_sub, coeff_succ_X_mul, coeff_succ_X_mul,
    show (2 : PowerSeries ℚ) * Useries n = Useries n + Useries n by ring, map_add,
    coeff_Useries_of_le (by omega), coeff_Useries_of_le (by omega : n ≤ k'),
    coeff_Useries_of_le (by omega : n - 1 ≤ k')]
  ring

/-- `p^n ∑_m B_{m,n} p^m = n - ½ (1-p)^{-1/2} ((2-p) U_n(p) - p U_{n-1}(p))`, doubled. -/
theorem colB_eq (n : ℕ) :
    2 * (X ^ n * colB n - (n : PowerSeries ℚ)) = -(hser * Rrev n) := by
  have h := step1_poly n
  rw [Rrev]
  linear_combination hser * h - 2 * (X ^ n * colB n - (n : PowerSeries ℚ)) * hser_mul_sOne

/-- The bound replacing Cauchy's inequality (sphere/paper.tex l.845–847):
`|B_{m,n}| ≤ 2n(n+1)` for all `m`. -/
theorem Bcoef_abs_le (m n : ℕ) : |Bcoef m n| ≤ 2 * (n : ℚ) * ((n : ℚ) + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Bcoef_zero_left, abs_zero]
    positivity
  have h := congrArg (coeff (m + n)) (colB_eq n)
  have hC : coeff (m + n) ((n : PowerSeries ℚ)) = 0 := by
    rw [show (n : PowerSeries ℚ) = C (n : ℚ) from (map_natCast _ n).symm, coeff_C,
      if_neg (by omega)]
  rw [show (2 : PowerSeries ℚ) * (X ^ n * colB n - (n : PowerSeries ℚ)) =
      (X ^ n * colB n - (n : PowerSeries ℚ)) + (X ^ n * colB n - (n : PowerSeries ℚ)) by ring,
    map_add, map_sub, hC, coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel, colB, coeff_mk,
    map_neg, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a hser * coeff b (Rrev n)), ← Finset.sum_range_reflect] at h
  rw [sub_zero] at h
  have hsum : |∑ j ∈ range (m + n).succ, coeff (m + n + 1 - 1 - j) hser *
      coeff (m + n - (m + n + 1 - 1 - j)) (Rrev n)| ≤ ((n : ℚ) + 1) * (4 * n) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsub : range (n + 1) ⊆ range (m + n).succ := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine (Finset.sum_le_card_nsmul _ _ (4 * (n : ℚ)) fun j _ => ?_).trans ?_
      · rw [abs_mul]
        have h1 : |coeff (m + n + 1 - 1 - j) hser| ≤ 1 := by
          rw [hser, coeff_mk, abs_of_nonneg (halfBinom_nonneg _)]
          exact halfBinom_le_one _
        calc |coeff (m + n + 1 - 1 - j) hser| * |coeff (m + n - (m + n + 1 - 1 - j)) (Rrev n)|
            ≤ 1 * (4 * (n : ℚ)) :=
              mul_le_mul h1 (abs_coeff_Rrev_le n _) (abs_nonneg _) zero_le_one
          _ = 4 * (n : ℚ) := one_mul _
      · rw [Finset.card_range, nsmul_eq_mul]
        push_cast
        exact le_rfl
    · intro j hj hj'
      have h1 := Finset.mem_range.1 hj
      have h2 : ¬ j < n + 1 := fun hc => hj' (Finset.mem_range.2 hc)
      rw [coeff_Rrev_of_lt (by omega), mul_zero, abs_zero]
  have h2 : |Bcoef m n + Bcoef m n| ≤ ((n : ℚ) + 1) * (4 * n) := by
    rw [h, abs_neg]
    exact hsum
  have h3 : |Bcoef m n + Bcoef m n| = 2 * |Bcoef m n| := by
    rw [← two_mul, abs_mul, abs_two]
  rw [h3] at h2
  linarith

end Virasoro.Sphere
