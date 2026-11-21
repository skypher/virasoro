import Virasoro.Sphere.Proofs.Sec3BergmanSymm
import Virasoro.Sphere.Proofs.Sec3BergmanG

/-!
# Sphere paper Lemma 3.5, Step 2: the Laurent coefficients of `[z^i] W_no(x₁,x₂)` in `x₁`
(`sphere/paper.tex` l.890–913)

For fixed `x₂`, `[z^i] W_no(x₁,x₂) = ∑_m (a_m x₁^{-m-2} + b_m x₁^m)` with
`a_m = (A₊₊ x₂^{-•-1} + A₊₋ x₂^{•-1})_{m+1}` and `b_m = (A₋₋ x₂^{•-1} + A₋₊ x₂^{-•-1})_{m+1}`
at order `z^i`.  The outer patch uses `b = -B w`, `a = D w` (l.906–910), here in the form
`b + B x₂^{•-1} = -(B D⁻¹) a`.

Consumers: the inner and outer patches.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `[z^i] A_{m+1,n+1}` as a complex number. -/
noncomputable def cf (A : IMat) (i m n : ℕ) : ℂ := ((coeff i (A (m + 1) (n + 1)) : ℚ) : ℂ)

/-- `B_{m+1,l+1}/(l+1)`. -/
noncomputable def bet (m l : ℕ) : ℂ :=
  ((Bcoef (m + 1) (l + 1) / (((l + 1 : ℕ)) : ℚ) : ℚ) : ℂ)

theorem summable_single (d m0 : ℕ) :
    Summable fun m : ℕ => ((m : ℝ) + 2) ^ d * ‖(if m = m0 then (1 : ℂ) else 0)‖ :=
  summable_of_ne_finset_zero (s := {m0}) fun m hm => by
    rw [if_neg (by simpa using hm)]
    simp

theorem summable_row {A : IMat} (hA : PolyBdd A) (i m0 : ℕ) (v : ℕ → ℂ)
    (hv : ∀ d : ℕ, Summable fun n : ℕ => ((n : ℝ) + 2) ^ d * ‖v n‖) :
    Summable fun n : ℕ => cf A i m0 n * v n := by
  have h := (summable_block hA i (fun m => if m = m0 then (1 : ℂ) else 0) v
    (fun d => summable_single d m0) hv).prod_factor m0
  simpa [cf] using h

theorem cf_App_zero {i m n : ℕ} (h : i < m + n + 2) : cf App i m n = 0 := by
  rw [cf, coeff_zero_of_dvd (dvd_App (m + 1) (n + 1)) (by omega), Rat.cast_zero]

theorem cf_Apm_zero {i m : ℕ} (n : ℕ) (h : i < m + 2) : cf Apm i m n = 0 := by
  rw [cf, coeff_zero_of_dvd (dvd_Apm (m + 1) (n + 1)) (by omega), Rat.cast_zero]

theorem cf_Amp_zero {i n : ℕ} (m : ℕ) (h : i < n + 2) : cf Amp i m n = 0 := by
  rw [cf, coeff_zero_of_dvd (dvd_Amp (m + 1) (n + 1)) (by omega), Rat.cast_zero]

/-- The coefficient of `x₁^{-m-2}` of `[z^i] W_no(x₁,x₂)`. -/
noncomputable def aR (x2 : ℂ) (i m : ℕ) : ℂ :=
  ∑' n : ℕ, (cf App i m n * cutz i x2 n + cf Apm i m n * x2 ^ n)

/-- The coefficient of `x₁^m` of `[z^i] W_no(x₁,x₂)`. -/
noncomputable def bR (x2 : ℂ) (i m : ℕ) : ℂ :=
  ∑' n : ℕ, (cf Amm i m n * x2 ^ n + cf Amp i m n * cutz i x2 n)

theorem summable_aR_term {x2 : ℂ} (h2 : ‖x2‖ < 1) (i m : ℕ) :
    Summable fun n : ℕ => cf App i m n * cutz i x2 n + cf Apm i m n * x2 ^ n :=
  (summable_row PolyBdd.App i m _ (fun d => summable_cutz i d x2)).add
    (summable_row PolyBdd.Apm i m _ (fun d => summable_geom_norm d h2))

theorem summable_bR_term {x2 : ℂ} (h2 : ‖x2‖ < 1) (i m : ℕ) :
    Summable fun n : ℕ => cf Amm i m n * x2 ^ n + cf Amp i m n * cutz i x2 n :=
  (summable_row PolyBdd.Amm i m _ (fun d => summable_geom_norm d h2)).add
    (summable_row PolyBdd.Amp i m _ (fun d => summable_cutz i d x2))

theorem aR_eq_zero (x2 : ℂ) {i m : ℕ} (h : i < m + 2) : aR x2 i m = 0 := by
  rw [aR]
  have e : ∀ n : ℕ, cf App i m n * cutz i x2 n + cf Apm i m n * x2 ^ n = 0 := fun n => by
    rw [cf_App_zero (by omega), cf_Apm_zero n h, zero_mul, zero_mul, add_zero]
  simp only [e, tsum_zero]

/-- `[z^i] W_no(x₁,x₂)` as a Laurent series in `x₁`. -/
theorem Wnos_rows (i : ℕ) {x1 x2 : ℂ} (h1 : ‖x1‖ < 1) (h2 : ‖x2‖ < 1) :
    coeff i (Wnos x1 x2) = ∑' m : ℕ, (aR x2 i m * cutz i x1 m + bR x2 i m * x1 ^ m) := by
  rw [Wnos, coeff_mk, (summable_WnoTerm i h1 h2).tsum_prod]
  refine tsum_congr fun m => ?_
  have e : ∀ n, WnoTerm i x1 x2 m n =
      cutz i x1 m * (cf App i m n * cutz i x2 n + cf Apm i m n * x2 ^ n) +
        x1 ^ m * (cf Amm i m n * x2 ^ n + cf Amp i m n * cutz i x2 n) := fun n => by
    rw [WnoTerm_cut]
    simp only [cf]
    ring
  simp only [e]
  rw [Summable.tsum_add ((summable_aR_term h2 i m).mul_left _)
    ((summable_bR_term h2 i m).mul_left _), tsum_mul_left, tsum_mul_left, aR, bR]
  ring

/-- Outer patch, row form (l.906–910): `b + B x₂^{•-1} = -(B D⁻¹) a` at order `z^i`. -/
theorem bR_outer {x2 : ℂ} (h2 : ‖x2‖ < 1) (i m : ℕ) :
    bR x2 i m + ∑' n : ℕ, cf Binf i m n * x2 ^ n = -∑ l ∈ range i, bet m l * aR x2 i l := by
  have hB : ∀ n, coeff i (Binf (m + 1) (n + 1)) = if i = 0 then Bcoef (m + 1) (n + 1) else 0 :=
    fun n => by rw [Binf, coeff_C]
  have h1 : ∀ n, cf Amm i m n + cf Binf i m n = -∑ l ∈ range i, bet m l * cf Apm i l n :=
    fun n => by
      have h := Amm_eq_sum i m n
      rw [← hB n] at h
      have h' := congrArg (fun q : ℚ => (q : ℂ)) h
      simp only [Rat.cast_add, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul] at h'
      exact h'
  have h3 : ∀ n, cf Amp i m n = -∑ l ∈ range i, bet m l * cf App i l n := fun n => by
    have h' := congrArg (fun q : ℚ => (q : ℂ)) (Amp_eq_sum i m n)
    simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul] at h'
    exact h'
  have e : ∀ n, cf Amm i m n * x2 ^ n + cf Amp i m n * cutz i x2 n =
      -(cf Binf i m n * x2 ^ n + ∑ l ∈ range i,
        bet m l * (cf App i l n * cutz i x2 n + cf Apm i l n * x2 ^ n)) := fun n => by
    have hA : cf Amm i m n = -cf Binf i m n - ∑ l ∈ range i, bet m l * cf Apm i l n := by
      linear_combination h1 n
    rw [hA, h3 n, Finset.sum_congr rfl (fun l _ =>
      (by ring : bet m l * (cf App i l n * cutz i x2 n + cf Apm i l n * x2 ^ n) =
        (bet m l * cf App i l n) * cutz i x2 n + (bet m l * cf Apm i l n) * x2 ^ n)),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hT : Summable fun n : ℕ => cf Binf i m n * x2 ^ n :=
    summable_row PolyBdd.Binf i m _ (fun d => summable_geom_norm d h2)
  have hS : Summable fun n : ℕ => ∑ l ∈ range i,
      bet m l * (cf App i l n * cutz i x2 n + cf Apm i l n * x2 ^ n) :=
    summable_sum fun l _ => (summable_aR_term h2 i l).mul_left _
  rw [bR]
  simp only [e]
  rw [tsum_neg, Summable.tsum_add hT hS,
    Summable.tsum_finsetSum fun l _ => (summable_aR_term h2 i l).mul_left _]
  simp only [tsum_mul_left, aR]
  ring

end Virasoro.Sphere
