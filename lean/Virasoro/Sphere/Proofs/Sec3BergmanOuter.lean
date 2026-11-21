import Virasoro.Sphere.Proofs.Sec3BergmanOuterTools
import Virasoro.Sphere.Proofs.Sec3BergmanLiouConst
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Sphere paper Lemma 3.5, Step 2, outer patch (`sphere/paper.tex` l.906–913)

On `|x₂| < |x₁| < 1`, with `w = K₁₂(x₂^{•-1} - M₁ x₂^{-•-1})`:
`W = -x₁⁻² ∑_n w_n f_n(1/x₁)` and `x₁√(x₁-1) W = i ∑_n w_n P_n(1/x₁)`.  At order `z^i` the vector
`D w` is the vector `a` of principal coefficients (`aR`) plus, for `i = 0`, `(n x₂^{n-1})_n`;
`[z^0] w_n = x₂^{n-1}` and `[z^i] w` has finite support for `i ≥ 1`.  The right-hand side
(`GoOut`) is a series of polynomials in `1/x₁`, holomorphic on `|x₁| > |x₂|` and bounded on
`|x₁| ≥ 1`.

Consumer: `sub_bergman_const_of_patches`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology

theorem summable_prod_outer {f : ℕ × ℕ → ℂ} (h : Summable f) :
    Summable fun m : ℕ => ∑' n : ℕ, f (m, n) := by
  have h' : Summable (fun p : Σ _ : ℕ, ℕ => f (p.1, p.2)) :=
    (Equiv.sigmaEquivProd ℕ ℕ).summable_iff.2 h
  exact h'.sigma

theorem tsum_WnoTerm_row (i m : ℕ) (x1 : ℂ) {x2 : ℂ} (h2 : ‖x2‖ < 1) :
    ∑' n : ℕ, WnoTerm i x1 x2 m n = aR x2 i m * cutz i x1 m + bR x2 i m * x1 ^ m := by
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

/-- `(B x₂^{•-1})_{m+1}` at order `z^i` (zero unless `i = 0`). -/
noncomputable def TB (x2 : ℂ) (i m : ℕ) : ℂ := ∑' n : ℕ, cf Binf i m n * x2 ^ n

theorem cf_Binf (i m n : ℕ) :
    cf Binf i m n = if i = 0 then ((Bcoef (m + 1) (n + 1) : ℚ) : ℂ) else 0 := by
  rw [cf, Binf, coeff_C]
  split_ifs <;> simp

theorem TB_eq_zero (x2 : ℂ) {i : ℕ} (hi : i ≠ 0) (m : ℕ) : TB x2 i m = 0 := by
  rw [TB]
  simp only [cf_Binf, if_neg hi, zero_mul, tsum_zero]

theorem summable_TB {x x2 : ℂ} (h1 : ‖x‖ < 1) (h2 : ‖x2‖ < 1) (i : ℕ) :
    Summable fun m : ℕ => TB x2 i m * x ^ m := by
  have hF := summable_block PolyBdd.Binf i (fun m => x ^ m) (fun n => x2 ^ n)
    (fun d => summable_geom_norm d h1) (fun d => summable_geom_norm d h2)
  refine (summable_prod_outer hF).congr fun m => ?_
  rw [TB, ← tsum_mul_right]
  exact tsum_congr fun n => by
    dsimp only
    simp only [cf]
    ring

/-- `[z^i] W_no` on `0 < |x| < 1`: finite principal part and a power series. -/
theorem Wnos_split (i : ℕ) {x x2 : ℂ} (h1 : ‖x‖ < 1) (h2 : ‖x2‖ < 1) :
    (Summable fun m : ℕ => bR x2 i m * x ^ m) ∧
      coeff i (Wnos x x2) =
        ∑ l ∈ range i, aR x2 i l * x⁻¹ ^ (l + 2) + ∑' m : ℕ, bR x2 i m * x ^ m := by
  have hz : ∀ m, m ∉ range i → aR x2 i m * cutz i x m = 0 := fun m hm => by
    rw [aR_eq_zero x2 (by have := Finset.mem_range.not.1 hm; omega), zero_mul]
  have hfst : Summable fun m : ℕ => aR x2 i m * cutz i x m := summable_of_ne_finset_zero hz
  have hsum : Summable fun m : ℕ => aR x2 i m * cutz i x m + bR x2 i m * x ^ m :=
    (summable_prod_outer (summable_WnoTerm i h1 h2)).congr fun m => tsum_WnoTerm_row i m x h2
  have hsnd : Summable fun m : ℕ => bR x2 i m * x ^ m :=
    (hsum.sub hfst).congr fun m => by ring
  refine ⟨hsnd, ?_⟩
  rw [Wnos_rows i h1 h2, Summable.tsum_add hfst hsnd, tsum_eq_sum hz]
  congr 1
  exact Finset.sum_congr rfl fun l _ => aR_mul_cutz x2 x i l

/-- The regular part through `b = -B w` (l.906–910). -/
theorem tsum_bR (i : ℕ) {x x2 : ℂ} (hx0 : x ≠ 0) (h1 : ‖x‖ < 1) (h2 : ‖x2‖ < 1) :
    ∑' m : ℕ, bR x2 i m * x ^ m =
      -∑' m : ℕ, TB x2 i m * x ^ m -
        ∑ l ∈ range i, aR x2 i l * (x⁻¹ * colBf (l + 1) x / ((l + 1 : ℕ) : ℂ)) := by
  have e : ∀ m, bR x2 i m * x ^ m =
      -(TB x2 i m * x ^ m) - ∑ l ∈ range i, aR x2 i l * (bet m l * x ^ m) := fun m => by
    have h := bR_outer h2 i m
    have hb : bR x2 i m = -TB x2 i m - ∑ l ∈ range i, bet m l * aR x2 i l := by
      rw [TB]
      linear_combination h
    rw [hb, sub_mul, neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hS : Summable fun m : ℕ => ∑ l ∈ range i, aR x2 i l * (bet m l * x ^ m) :=
    summable_sum fun l _ => (summable_bet h1 l).mul_left _
  simp only [e]
  rw [Summable.tsum_sub (summable_TB h1 h2 i).neg hS, tsum_neg,
    Summable.tsum_finsetSum fun l _ => (summable_bet h1 l).mul_left _]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [tsum_mul_left, tsum_bet hx0 h1 l]

/-- Order `z^0`: `∑_m (B x₂^{•-1})_{m+1} x^m = ∑_k x₂^k x^{-1} ∑_m B_{m,k+1} x^m`. -/
theorem tsum_TB_zero {x x2 : ℂ} (hx0 : x ≠ 0) (h1 : ‖x‖ < 1) (h2 : ‖x2‖ < 1) :
    (Summable fun k : ℕ => x2 ^ k * (x⁻¹ * colBf (k + 1) x)) ∧
      ∑' m : ℕ, TB x2 0 m * x ^ m = ∑' k : ℕ, x2 ^ k * (x⁻¹ * colBf (k + 1) x) := by
  set F : ℕ × ℕ → ℂ := fun mn => cf Binf 0 mn.1 mn.2 * x ^ mn.1 * x2 ^ mn.2 with hF
  have hFs : Summable F := summable_block PolyBdd.Binf 0 (fun m => x ^ m) (fun n => x2 ^ n)
    (fun d => summable_geom_norm d h1) (fun d => summable_geom_norm d h2)
  have hcol : ∀ k, ∑' m : ℕ, F (m, k) = x2 ^ k * (x⁻¹ * colBf (k + 1) x) := fun k => by
    rw [colBf_shift h1, ← mul_assoc x⁻¹, inv_mul_cancel₀ hx0, one_mul, ← tsum_mul_left]
    exact tsum_congr fun m => by
      simp only [hF, cf_Binf, ↓reduceIte]
      ring
  have hrow : ∀ m, ∑' k : ℕ, F (m, k) = TB x2 0 m * x ^ m := fun m => by
    rw [TB, ← tsum_mul_right]
    exact tsum_congr fun n => by
      simp only [hF]
      ring
  have hsw : Summable fun p : ℕ × ℕ => F p.swap := hFs.prod_symm
  refine ⟨(summable_prod_outer hsw).congr fun k => hcol k, ?_⟩
  calc ∑' m : ℕ, TB x2 0 m * x ^ m = ∑' m : ℕ, ∑' k : ℕ, F (m, k) :=
        tsum_congr fun m => (hrow m).symm
    _ = ∑' p : ℕ × ℕ, F p := hFs.tsum_prod.symm
    _ = ∑' p : ℕ × ℕ, F p.swap := ((Equiv.prodComm ℕ ℕ).tsum_eq F).symm
    _ = ∑' k : ℕ, ∑' m : ℕ, F (m, k) := hsw.tsum_prod
    _ = _ := tsum_congr hcol

/-- The `z^0` part of the outer function: `½ ∑_k x₂^k x^{-(k+1)} R_{k+1}(x)`. -/
noncomputable def G0 (x2 x : ℂ) : ℂ := ∑' k : ℕ, x2 ^ k * (1 / 2 * Rinv (k + 1) x)

/-- The outer function at order `z^i` (l.909–913): `i ∑_n [z^i] w_n(x₂) P_n(1/x₁)` up to the
branch constant. -/
noncomputable def GoOut (x2 : ℂ) (i : ℕ) (x : ℂ) : ℂ :=
  (if i = 0 then G0 x2 x else 0) +
    ∑ l ∈ range i, aR x2 i l / ((l + 1 : ℕ) : ℂ) * (1 / 2 * Rinv (l + 1) x)

theorem outer_eq (i : ℕ) {x x2 : ℂ} (hx : ‖x2‖ < ‖x‖) (h1 : ‖x‖ < 1) :
    x * (1 - x) ^ (1 / 2 : ℂ) * coeff i (Wser x x2) = GoOut x2 i x := by
  have h2 : ‖x2‖ < 1 := lt_trans hx h1
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg _) hx)
  obtain ⟨_, hW⟩ := Wnos_split i h1 h2
  have hb := tsum_bR i hx0 h1 h2
  have hfin : x * (1 - x) ^ (1 / 2 : ℂ) * (∑ l ∈ range i, aR x2 i l * x⁻¹ ^ (l + 2) -
      ∑ l ∈ range i, aR x2 i l * (x⁻¹ * colBf (l + 1) x / ((l + 1 : ℕ) : ℂ))) =
      ∑ l ∈ range i, aR x2 i l / ((l + 1 : ℕ) : ℂ) * (1 / 2 * Rinv (l + 1) x) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl : ((l + 1 : ℕ) : ℂ) * ((l + 1 : ℕ) : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero l))
    rw [← half_Rinv hx0 h1 l, div_eq_mul_inv (aR x2 i l),
      div_eq_mul_inv (x⁻¹ * colBf (l + 1) x)]
    linear_combination (-(x * (1 - x) ^ (1 / 2 : ℂ) * aR x2 i l * x⁻¹ ^ (l + 2))) * hl
  by_cases hi : i = 0
  · subst hi
    obtain ⟨hs1, hT⟩ := tsum_TB_zero hx0 h1 h2
    obtain ⟨hs2, hP⟩ := pole_outer hx
    rw [GoOut, if_pos rfl, Finset.range_zero, Finset.sum_empty, add_zero, Wser_eq, map_add,
      coeff_C, if_pos rfl, hW, hb, hT, ← hP, Finset.range_zero, Finset.sum_empty,
      Finset.sum_empty, zero_add, sub_zero, ← sub_eq_add_neg, ← Summable.tsum_sub hs2 hs1,
      ← tsum_mul_left, G0]
    exact tsum_congr fun k => by
      rw [← half_Rinv hx0 h1 k]
      ring
  · have hT0 : ∑' m : ℕ, TB x2 i m * x ^ m = 0 := by
      simp only [TB_eq_zero x2 hi, zero_mul, tsum_zero]
    rw [GoOut, if_neg hi, zero_add, Wser_eq, map_add, coeff_C, if_neg hi, zero_add, hW, hb, hT0,
      neg_zero, zero_sub, ← hfin]
    ring

theorem term_bound (x2 : ℂ) {y : ℂ} {t : ℝ} (ht : 1 ≤ t) (hy : ‖y⁻¹‖ ≤ t) (k : ℕ) :
    ‖x2 ^ k * (1 / 2 * Rinv (k + 1) y)‖ ≤ 2 * t * (((k : ℝ) + 2) ^ 2 * (‖x2‖ * t) ^ k) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have hR := norm_Rinv_le (k + 1) ht hy
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hR
  rw [norm_mul, norm_pow, norm_mul, h12]
  calc ‖x2‖ ^ k * (1 / 2 * ‖Rinv (k + 1) y‖)
      ≤ ‖x2‖ ^ k * (1 / 2 * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1) * t ^ (k + 1))) := by
        gcongr
    _ ≤ 2 * t * (((k : ℝ) + 2) ^ 2 * (‖x2‖ * t) ^ k) := by
        rw [mul_pow, pow_succ]
        nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x2) k) (pow_nonneg ht0 k))
          (mul_nonneg ht0 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2))]

theorem summable_major {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (t : ℝ) :
    Summable fun k : ℕ => 2 * t * (((k : ℝ) + 2) ^ 2 * q ^ k) :=
  (summable_shift_pow_mul_geom 2 h0 h1).mul_left (2 * t)

theorem differentiableAt_G0 {x2 x : ℂ} (h20 : 0 < ‖x2‖) (h21 : ‖x2‖ < 1) (hx : ‖x2‖ < ‖x‖) :
    DifferentiableAt ℂ (G0 x2) x := by
  set r : ℝ := min ((‖x2‖ + ‖x‖) / 2) 1 with hr
  have hr2 : ‖x2‖ < r := lt_min (by linarith) h21
  have hrx : r < ‖x‖ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r ≤ 1 := min_le_right _ _
  have hr0 : 0 < r := lt_trans h20 hr2
  have ht : 1 ≤ r⁻¹ := (one_le_inv₀ hr0).2 hr1
  have hq : ‖x2‖ * r⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hr0]
    exact hr2
  have hU : IsOpen {y : ℂ | r < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hne : ∀ y ∈ {y : ℂ | r < ‖y‖}, y ≠ 0 := fun y hy =>
    norm_pos_iff.1 (lt_trans hr0 hy)
  refine (Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (k : ℕ) (y : ℂ) => x2 ^ k * (1 / 2 * Rinv (k + 1) y))
    (summable_major (mul_nonneg (norm_nonneg _) (le_trans zero_le_one ht)) hq r⁻¹)
    (fun k y hy => ((differentiableAt_const _).mul ((differentiableAt_const _).mul
      (differentiableAt_Rinv _ (hne y hy)))).differentiableWithinAt) hU
    (fun k y hy => term_bound x2 ht ?_ k)).differentiableAt (hU.mem_nhds hrx)
  rw [norm_inv]
  exact inv_anti₀ hr0 (le_of_lt hy)

theorem differentiableOn_GoOut {x2 : ℂ} (h20 : 0 < ‖x2‖) (h21 : ‖x2‖ < 1) (i : ℕ) :
    DifferentiableOn ℂ (GoOut x2 i) {x | ‖x2‖ < ‖x‖} := by
  intro x hx
  have hx' : ‖x2‖ < ‖x‖ := hx
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_trans h20 hx')
  have hA : DifferentiableAt ℂ (fun y => if i = 0 then G0 x2 y else 0) x := by
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact differentiableAt_G0 h20 h21 hx'
    · simp only [hi, if_false]
      exact differentiableAt_const _
  unfold GoOut
  exact (hA.add (DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul
    ((differentiableAt_const _).mul (differentiableAt_Rinv _ hx0)))).differentiableWithinAt

theorem bdd_GoOut {x2 : ℂ} (h21 : ‖x2‖ < 1) (i : ℕ) :
    ∃ M : ℝ, ∀ x : ℂ, 1 ≤ ‖x‖ → ‖GoOut x2 i x‖ ≤ M := by
  have hs := summable_major (q := ‖x2‖ * 1) (by positivity) (by rwa [mul_one]) 1
  refine ⟨∑' k : ℕ, 2 * 1 * (((k : ℝ) + 2) ^ 2 * (‖x2‖ * 1) ^ k) +
    ∑ l ∈ range i, ‖aR x2 i l / ((l + 1 : ℕ) : ℂ)‖ *
      (1 / 2 * (4 * ((l + 1 : ℕ) : ℝ) * (((l + 1 : ℕ) : ℝ) + 1) * 1 ^ (l + 1))), fun x hx => ?_⟩
  have hinv : ‖x⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [GoOut]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => ?_)))
  · by_cases hi : i = 0
    · rw [if_pos hi, G0]
      exact tsum_of_norm_bounded hs.hasSum fun k => term_bound x2 le_rfl hinv k
    · rw [if_neg hi, norm_zero]
      exact tsum_nonneg fun k => by positivity
  · rw [norm_mul, norm_mul, h12]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (norm_Rinv_le (l + 1) le_rfl hinv) (by norm_num)) (norm_nonneg _)

/-- Lemma 3.5, Step 2, outer patch (sphere/paper.tex l.906–913). -/
theorem sub_bergman_outer : Stmt_sub_bergman_outer :=
  fun x2 h20 h21 j => ⟨GoOut x2 j, differentiableOn_GoOut h20 h21 j, bdd_GoOut h21 j,
    fun _ hx h1 => outer_eq j hx h1⟩

end Virasoro.Sphere
