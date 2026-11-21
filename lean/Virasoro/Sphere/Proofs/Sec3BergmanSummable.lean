import Virasoro.Sphere.Proofs.Sec3BergmanPolyBdd
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Norm

/-!
# Sphere paper Lemma 3.5: convergence of `[z^j] W_no(x₁,x₂)` (`sphere/paper.tex` l.878–880)

For every `j` and all `x₁, x₂` in the open unit disc the double series of the coefficient of
`z^j` of `W_no(x₁,x₂)` converges absolutely: the coefficients of the four blocks are polynomially
bounded in `(m,n)`, the blocks `A₊₊`, `A₋₊`, `A₊₋` have finite support in the indices that carry
negative powers, and `∑ (m+2)^d |x|^m < ∞` for `|x| < 1`.

Consumer: the first clause of `IsWFormula` (`Stmt_sub_bergman_liouville`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset

theorem summable_shift_pow_mul_geom (d : ℕ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * r ^ n := by
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
      have : n ≠ 0 := by simpa using hn
      simp [this]
  have h := summable_pow_mul_geometric_of_norm_lt_one d (r := r)
    (by rwa [Real.norm_of_nonneg h0])
  have h2 := ((summable_nat_add_iff 2).2 h).mul_left (r⁻¹ ^ 2)
  refine h2.congr fun n => ?_
  push_cast
  field_simp
  ring

theorem summable_cut (j d : ℕ) (f : ℕ → ℂ) :
    Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * ‖if n + 2 ≤ j then f n else 0‖ :=
  summable_of_ne_finset_zero (s := range j) fun n hn => by
    have : ¬ n + 2 ≤ j := by
      have := Finset.mem_range.not.1 hn
      omega
    rw [if_neg this, norm_zero, mul_zero]

theorem summable_geom_norm (d : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * ‖x ^ n‖ :=
  (summable_shift_pow_mul_geom d (norm_nonneg x) hx).congr fun n => by rw [norm_pow]

/-- A double series `∑ a_{m+1,n+1} u_m v_n` with polynomially bounded `a` converges absolutely
when `∑ (m+2)^d |u_m|` and `∑ (n+2)^d |v_n|` converge for every `d`. -/
theorem summable_norm_block {A : IMat} (hA : PolyBdd A) (j : ℕ) (u v : ℕ → ℂ)
    (hu : ∀ d : ℕ, Summable fun m : ℕ => ((m : ℝ) + 2) ^ d * ‖u m‖)
    (hv : ∀ d : ℕ, Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * ‖v n‖) :
    Summable fun mn : ℕ × ℕ =>
      ‖((coeff j (A (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * u mn.1 * v mn.2‖ := by
  obtain ⟨C, d, hC, hb⟩ := hA j
  have hs := ((hu d).mul_of_nonneg (hv d)
    (fun m => mul_nonneg (by positivity) (norm_nonneg _))
    (fun n => mul_nonneg (by positivity) (norm_nonneg _))).mul_left (C : ℝ)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun mn => ?_) hs
  obtain ⟨m, n⟩ := mn
  have hq : ‖((coeff j (A (m + 1) (n + 1)) : ℚ) : ℂ)‖ ≤
      (C : ℝ) * ((((m : ℝ) + 2) * ((n : ℝ) + 2)) ^ d) := by
    have := (Rat.cast_le (K := ℝ)).2 (hb (m + 1) (n + 1))
    rw [Complex.norm_ratCast]
    simp only [wt, Rat.cast_abs, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, Nat.cast_add, Nat.cast_one] at this
    calc |((coeff j (A (m + 1) (n + 1)) : ℚ) : ℝ)|
        ≤ (C : ℝ) * (((m : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 1)) ^ d := this
      _ = (C : ℝ) * ((((m : ℝ) + 2) * ((n : ℝ) + 2)) ^ d) := by ring
  have hC' : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hCw : 0 ≤ (C : ℝ) * ((((m : ℝ) + 2) * ((n : ℝ) + 2)) ^ d) :=
    mul_nonneg hC' (by positivity)
  calc ‖((coeff j (A (m + 1) (n + 1)) : ℚ) : ℂ) * u m * v n‖
      = ‖((coeff j (A (m + 1) (n + 1)) : ℚ) : ℂ)‖ * ‖u m‖ * ‖v n‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (C : ℝ) * ((((m : ℝ) + 2) * ((n : ℝ) + 2)) ^ d) * ‖u m‖ * ‖v n‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
          (norm_nonneg _)
    _ = (C : ℝ) * ((((m : ℝ) + 2) ^ d * ‖u m‖) * (((n : ℝ) + 2) ^ d * ‖v n‖)) := by
        rw [mul_pow]; ring

theorem summable_block {A : IMat} (hA : PolyBdd A) (j : ℕ) (u v : ℕ → ℂ)
    (hu : ∀ d : ℕ, Summable fun m : ℕ => ((m : ℝ) + 2) ^ d * ‖u m‖)
    (hv : ∀ d : ℕ, Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * ‖v n‖) :
    Summable fun mn : ℕ × ℕ =>
      ((coeff j (A (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * u mn.1 * v mn.2 :=
  (summable_norm_block hA j u v hu hv).of_norm

/-- The negative power `x^{-m-2}`, kept only for `m + 2 ≤ j`. -/
noncomputable def cutz (j : ℕ) (x : ℂ) (m : ℕ) : ℂ :=
  if m + 2 ≤ j then x ^ (-((m : ℤ) + 2)) else 0

/-- At order `z^j` the negative powers only occur for `m + 2 ≤ j` (finite support of `A₊₊`,
`A₋₊`, `A₊₋`). -/
theorem WnoTerm_cut (j : ℕ) (x1 x2 : ℂ) (m n : ℕ) :
    WnoTerm j x1 x2 m n =
      ((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * cutz j x1 m * cutz j x2 n +
        ((coeff j (Amm (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ m * x2 ^ n +
        ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ m * cutz j x2 n +
        ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * cutz j x1 m * x2 ^ n := by
  have t1 : ((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ (-((m : ℤ) + 2)) *
      x2 ^ (-((n : ℤ) + 2)) =
      ((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * cutz j x1 m * cutz j x2 n := by
    by_cases h : m + 2 ≤ j ∧ n + 2 ≤ j
    · rw [cutz, cutz, if_pos h.1, if_pos h.2]
    · rw [X_pow_dvd_iff.1 (dvd_App (m + 1) (n + 1)) j (by omega)]
      simp
  have t3 : ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ m * x2 ^ (-((n : ℤ) + 2)) =
      ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ m * cutz j x2 n := by
    by_cases h : n + 2 ≤ j
    · rw [cutz, if_pos h]
    · rw [X_pow_dvd_iff.1 (dvd_Amp (m + 1) (n + 1)) j (by omega)]
      simp
  have t4 : ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ (-((m : ℤ) + 2)) * x2 ^ n =
      ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * cutz j x1 m * x2 ^ n := by
    by_cases h : m + 2 ≤ j
    · rw [cutz, if_pos h]
    · rw [X_pow_dvd_iff.1 (dvd_Apm (m + 1) (n + 1)) j (by omega)]
      simp
  rw [WnoTerm, t1, t3, t4]

theorem summable_cutz (j d : ℕ) (x : ℂ) :
    Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * ‖cutz j x n‖ :=
  summable_cut j d _

/-- The four series of norms of `[z^j] W_no(x₁,x₂)` converge on the open unit bidisc. -/
theorem summable_norm_Wno (j : ℕ) {x1 x2 : ℂ} (h1 : ‖x1‖ < 1) (h2 : ‖x2‖ < 1) :
    Summable fun mn : ℕ × ℕ =>
      ‖((coeff j (App (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * cutz j x1 mn.1 * cutz j x2 mn.2‖ +
        ‖((coeff j (Amm (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * x1 ^ mn.1 * x2 ^ mn.2‖ +
        ‖((coeff j (Amp (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * x1 ^ mn.1 * cutz j x2 mn.2‖ +
        ‖((coeff j (Apm (mn.1 + 1) (mn.2 + 1)) : ℚ) : ℂ) * cutz j x1 mn.1 * x2 ^ mn.2‖ :=
  (((summable_norm_block PolyBdd.App j (cutz j x1) (cutz j x2)
      (fun d => summable_cutz j d x1) (fun d => summable_cutz j d x2)).add
    (summable_norm_block PolyBdd.Amm j (fun m => x1 ^ m) (fun n => x2 ^ n)
      (fun d => summable_geom_norm d h1) (fun d => summable_geom_norm d h2))).add
    (summable_norm_block PolyBdd.Amp j (fun m => x1 ^ m) (cutz j x2)
      (fun d => summable_geom_norm d h1) (fun d => summable_cutz j d x2))).add
    (summable_norm_block PolyBdd.Apm j (cutz j x1) (fun n => x2 ^ n)
      (fun d => summable_cutz j d x1) (fun d => summable_geom_norm d h2))

/-- Each coefficient `[z^j] W_no(x₁,x₂)` converges absolutely on the open unit bidisc
(sphere/paper.tex l.878–880). -/
theorem summable_WnoTerm (j : ℕ) {x1 x2 : ℂ} (h1 : ‖x1‖ < 1) (h2 : ‖x2‖ < 1) :
    Summable fun mn : ℕ × ℕ => WnoTerm j x1 x2 mn.1 mn.2 := by
  refine Summable.of_norm_bounded (summable_norm_Wno j h1 h2) fun mn => ?_
  rw [WnoTerm_cut]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

end Virasoro.Sphere
