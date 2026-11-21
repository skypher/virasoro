import Virasoro.Sphere.Proofs.Sec3BergmanOuter

/-!
# Sphere paper Lemma 3.5, Step 2, inner patch: the vector `D v` (`sphere/paper.tex` l.892–899)

On `|x₁| < |x₂|` the coefficient of `x₁^{m}` of `[z^i] W(x₁,x₂)` is `(D v)_{m+1}` with
`v = K₂₁(x₂^{-•-1} - M₂ x₂^{•-1})` (`bt`: the vector `b` plus, for `i = 0`, the expansion of
`(x₁-x₂)⁻²`), and the principal coefficients are `a = -B^{(z)} v` (`aR_inner`).  The series
`∑_m |(Dv)_{m+1}| r^m` converges for `r < |x₂|` (`|[z^j] v_n(x₂)| = O(|x₂|^{-n})`, l.899–901).

Consumer: `sub_bergman_inner`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `(D v)_{m+1}` at order `z^i`: the coefficient of `x₁^m` of `[z^i] W(x₁,x₂)` on
`|x₁| < |x₂|`. -/
noncomputable def bt (x2 : ℂ) (i m : ℕ) : ℂ :=
  bR x2 i m + (if i = 0 then ((m + 1 : ℕ) : ℂ) * x2⁻¹ ^ (m + 2) else 0)

theorem cf_Amp_mul_cutz {i I : ℕ} (h : i ≤ I) (l n : ℕ) (x : ℂ) :
    cf Amp i l n * cutz I x n = cf Amp i l n * cutz i x n := by
  by_cases hn : n + 2 ≤ i
  · rw [cutz_eq_pow hn, cutz_eq_pow (le_trans hn h)]
  · rw [cf_Amp_zero l (by omega), zero_mul, zero_mul]

theorem coeff_ione (k a b : ℕ) :
    coeff k (ione a b) = if a = b then (if k = 0 then (1 : ℚ) else 0) else 0 := by
  rw [ione]
  split_ifs <;> simp_all [coeff_one]

/-- `[z^k](A₋₊ + D)_{l+1,n+1}` as a complex number. -/
noncomputable def dl (k l n : ℕ) : ℂ :=
  ((coeff k (Amp (l + 1) (n + 1) + C (((l + 1 : ℕ)) : ℚ) * ione (l + 1) (n + 1)) : ℚ) : ℂ)

theorem dl_eq (k l n : ℕ) :
    dl k l n = cf Amp k l n + (if n = l then (if k = 0 then ((l + 1 : ℕ) : ℂ) else 0) else 0) := by
  rw [dl, map_add, coeff_C_mul, coeff_ione, cf]
  by_cases h : n = l
  · subst h
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]
  · have h' : ¬ (l = n) := fun hc => h hc.symm
    simp [h, h']

/-- Inner patch, row form (l.892–894): `a = -B^{(z)} v` at order `z^i`. -/
theorem aR_inner {x2 : ℂ} (h2 : ‖x2‖ < 1) (i m : ℕ) :
    aR x2 i m =
      -∑ l ∈ range i, bet m l * (if m + l + 2 ≤ i then bt x2 (i - (m + l + 2)) l else 0) := by
  have hApp : ∀ n, cf App i m n = -∑ l ∈ range i,
      bet m l * (if m + l + 2 ≤ i then dl (i - (m + l + 2)) l n else 0) := fun n => by
    have h' := congrArg (fun q : ℚ => (q : ℂ)) (App_eq_sum i m n)
    simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, apply_ite (Rat.cast : ℚ → ℂ),
      Rat.cast_zero] at h'
    exact h'
  have hApm : ∀ n, cf Apm i m n = -∑ l ∈ range i,
      bet m l * (if m + l + 2 ≤ i then cf Amm (i - (m + l + 2)) l n else 0) := fun n => by
    have h' := congrArg (fun q : ℚ => (q : ℂ)) (Apm_eq_sum i m n)
    simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, apply_ite (Rat.cast : ℚ → ℂ),
      Rat.cast_zero] at h'
    exact h'
  have e : ∀ n, cf App i m n * cutz i x2 n + cf Apm i m n * x2 ^ n =
      -∑ l ∈ range i, bet m l * (if m + l + 2 ≤ i then
        (dl (i - (m + l + 2)) l n * cutz i x2 n + cf Amm (i - (m + l + 2)) l n * x2 ^ n)
        else 0) := fun n => by
    rw [hApp n, hApm n, neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul, ← neg_add,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  have hrow : ∀ l, m + l + 2 ≤ i →
      (Summable fun n : ℕ => dl (i - (m + l + 2)) l n * cutz i x2 n +
        cf Amm (i - (m + l + 2)) l n * x2 ^ n) ∧
      ∑' n : ℕ, (dl (i - (m + l + 2)) l n * cutz i x2 n +
        cf Amm (i - (m + l + 2)) l n * x2 ^ n) = bt x2 (i - (m + l + 2)) l := fun l hl => by
    have hterm : ∀ n, dl (i - (m + l + 2)) l n * cutz i x2 n +
        cf Amm (i - (m + l + 2)) l n * x2 ^ n =
        (cf Amm (i - (m + l + 2)) l n * x2 ^ n +
          cf Amp (i - (m + l + 2)) l n * cutz (i - (m + l + 2)) x2 n) +
        (if n = l then (if i - (m + l + 2) = 0 then ((l + 1 : ℕ) : ℂ) else 0) else 0) *
          cutz i x2 n := fun n => by
      rw [dl_eq, add_mul, cf_Amp_mul_cutz (Nat.sub_le _ _)]
      ring
    have hs1 := summable_bR_term h2 (i - (m + l + 2)) l
    have hz : ∀ n, n ∉ ({l} : Finset ℕ) →
        (if n = l then (if i - (m + l + 2) = 0 then ((l + 1 : ℕ) : ℂ) else 0) else 0) *
          cutz i x2 n = 0 := fun n hn => by
      rw [if_neg (by simpa using hn), zero_mul]
    have hs2 : Summable fun n : ℕ =>
        (if n = l then (if i - (m + l + 2) = 0 then ((l + 1 : ℕ) : ℂ) else 0) else 0) *
          cutz i x2 n := summable_of_ne_finset_zero hz
    simp only [hterm]
    refine ⟨hs1.add hs2, ?_⟩
    rw [Summable.tsum_add hs1 hs2, tsum_eq_sum hz, Finset.sum_singleton, if_pos rfl,
      cutz_eq_pow (by omega : l + 2 ≤ i), bt, bR]
    congr 1
    split_ifs <;> simp
  have hsl : ∀ l ∈ range i, Summable fun n : ℕ => bet m l * (if m + l + 2 ≤ i then
      (dl (i - (m + l + 2)) l n * cutz i x2 n + cf Amm (i - (m + l + 2)) l n * x2 ^ n)
      else 0) := fun l _ => by
    by_cases hl : m + l + 2 ≤ i
    · simp only [if_pos hl]
      exact (hrow l hl).1.mul_left _
    · simp only [if_neg hl, mul_zero]
      exact summable_zero
  rw [aR]
  simp only [e]
  rw [tsum_neg, Summable.tsum_finsetSum hsl]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_left]
  by_cases hl : m + l + 2 ≤ i
  · simp only [if_pos hl]
    rw [(hrow l hl).2]
  · simp only [if_neg hl, tsum_zero]

/-- `∑_m |b_m| |y|^m < ∞` for `|y| < 1`. -/
theorem summable_norm_bR {x2 y : ℂ} (h2 : ‖x2‖ < 1) (hy : ‖y‖ < 1) (i : ℕ) :
    Summable fun m : ℕ => ‖bR x2 i m * y ^ m‖ := by
  have hA := summable_norm_block PolyBdd.Amm i (fun m => y ^ m) (fun n => x2 ^ n)
    (fun d => summable_geom_norm d hy) (fun d => summable_geom_norm d h2)
  have hB := summable_norm_block PolyBdd.Amp i (fun m => y ^ m) (cutz i x2)
    (fun d => summable_geom_norm d hy) (fun d => summable_cutz i d x2)
  have hAB := hA.add hB
  have hp := (summable_prod_of_nonneg (fun mn => add_nonneg (norm_nonneg _) (norm_nonneg _))).1 hAB
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hp.2
  rw [bR, ← tsum_mul_right]
  refine tsum_of_norm_bounded (hp.1 m).hasSum fun n => ?_
  have e : (cf Amm i m n * x2 ^ n + cf Amp i m n * cutz i x2 n) * y ^ m =
      cf Amm i m n * y ^ m * x2 ^ n + cf Amp i m n * y ^ m * cutz i x2 n := by ring
  rw [e]
  exact norm_add_le _ _

/-- `∑_m |(Dv)_{m+1}| |y|^m < ∞` for `|y| < |x₂|` (l.899–901). -/
theorem summable_norm_bt {x2 y : ℂ} (h2 : ‖x2‖ < 1) (hy : ‖y‖ < ‖x2‖) (i : ℕ) :
    Summable fun m : ℕ => ‖bt x2 i m * y ^ m‖ := by
  have h1 := summable_norm_bR h2 (lt_trans hy h2) i
  have h3 := (pole_outer hy).1.norm
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (h1.add h3)
  rw [bt, add_mul]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  split_ifs
  · exact le_of_eq (by rw [mul_comm])
  · rw [zero_mul, norm_zero]
    exact norm_nonneg _

end Virasoro.Sphere
