import Virasoro.Sphere.Proofs.Sec3BergmanLiouTools
import Virasoro.Sphere.Proofs.Sec3BergmanLiouGlue

/-!
# Sphere paper Lemma 3.5, Step 2: extension to `ℙ¹` and Liouville's theorem
(`sphere/paper.tex` l.890–929)

For fixed `x₂` and every order `z^j`, the function
`x₁ ↦ [z^j](Y(x₁) W(x₁,x₂) + S(x₁,x₂)/(Y(x₂)(x₁-x₂)²))` (with `1/Y = g` up to the branch
constant) is holomorphic on the punctured unit disc off `x₂`, bounded near `0` (inner patch) and
near `x₂` (the double pole cancels), and continues to `|x₁| > |x₂|` including `∞` (outer patch).
By Liouville's theorem it is constant.

The three analytic inputs are stated as sub-statements:
* `Stmt_sub_bergman_holo` (l.878–880): each `[z^j] W_no` is holomorphic in `x₁`;
* `Stmt_sub_bergman_inner` (l.892–905): `[z^j](√(x₁(x₁-z)) W)` is bounded near `x₁ = 0`;
* `Stmt_sub_bergman_outer` (l.906–913): `[z^j](x₁√(x₁-1) W)` continues to `|x₁| > |x₂|`, bounded
  at `∞`.

Consumer: `Stmt_sub_bergman_liouville`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Filter Topology Metric

/-- Sub-statement of Lemma 3.5 (sphere/paper.tex l.878–880): each coefficient `[z^j] W_no(x₁,x₂)`
is holomorphic in `x₁` on `0 < |x₁| < 1` (local normal convergence). -/
def Stmt_sub_bergman_holo : Prop :=
  ∀ x2 : ℂ, ‖x2‖ < 1 → ∀ x1 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → CoeffDiff (fun y => Wnos y x2) x1

/-- Sub-statement of Lemma 3.5, Step 2, inner patch (sphere/paper.tex l.892–905): at every order
in `z`, `√(x₁(x₁-z)) W(x₁,x₂) = x₁ √(1-z/x₁) W(x₁,x₂)` is bounded near `x₁ = 0`. -/
def Stmt_sub_bergman_inner : Prop :=
  ∀ x2 : ℂ, 0 < ‖x2‖ → ‖x2‖ < 1 → ∀ j : ℕ,
    BddNear (fun x1 => coeff j (C x1 * sqrtZ x1 * Wser x1 x2)) 0

/-- Sub-statement of Lemma 3.5, Step 2, outer patch (sphere/paper.tex l.906–913): at every order
in `z`, `x₁ √(1-x₁) W(x₁,x₂)` on `|x₂| < |x₁| < 1` is the restriction of a function holomorphic
on `|x₁| > |x₂|` and bounded on `|x₁| ≥ 1` (holomorphic at `∞`). -/
def Stmt_sub_bergman_outer : Prop :=
  ∀ x2 : ℂ, 0 < ‖x2‖ → ‖x2‖ < 1 → ∀ j : ℕ, ∃ Go : ℂ → ℂ,
    DifferentiableOn ℂ Go {x | ‖x2‖ < ‖x‖} ∧ (∃ M : ℝ, ∀ x, 1 ≤ ‖x‖ → ‖Go x‖ ≤ M) ∧
    ∀ x1 : ℂ, ‖x2‖ < ‖x1‖ → ‖x1‖ < 1 →
      x1 * (1 - x1) ^ (1 / 2 : ℂ) * coeff j (Wser x1 x2) = Go x1

/-- Sub-statement of Lemma 3.5, Step 2 (sphere/paper.tex l.914–924): for fixed `x₂`, at every
order in `z`, `Y(x₁) W(x₁,x₂) + g(x₂) S(x₁,x₂)/(x₁-x₂)²` does not depend on `x₁`. -/
def Stmt_sub_bergman_const : Prop :=
  ∀ x2 : ℂ, 0 < ‖x2‖ → ‖x2‖ < 1 → ∃ c : PowerSeries ℂ,
    ∀ x1 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → x1 ≠ x2 →
      Yser x1 * Wser x1 x2 + gser x2 * Sser x1 x2 * C (((x1 - x2) ^ 2)⁻¹) = c

/-- The pole term is bounded on `|x| ≥ 1`: in `u = 1/x` it is continuous on `|u| ≤ 1`. -/
theorem pole_bdd_outside {x2 : ℂ} (h21 : ‖x2‖ < 1) (γ γ' : ℂ) :
    ∃ M : ℝ, ∀ x : ℂ, 1 ≤ ‖x‖ →
      ‖(γ * (x * x2 * (x + x2) / 2 - x * x2) + γ' * ((x + x2) / 2 - x * x2)) *
        ((x - x2) ^ 2)⁻¹‖ ≤ M := by
  set Q : ℂ → ℂ := fun u => (γ * (x2 * (1 + x2 * u) / 2 - x2 * u) +
    γ' * ((u + x2 * u ^ 2) / 2 - x2 * u)) * ((1 - x2 * u) ^ 2)⁻¹ with hQ
  have hne : ∀ u ∈ closedBall (0 : ℂ) 1, (1 - x2 * u) ^ 2 ≠ 0 := fun u hu => by
    refine pow_ne_zero 2 (sub_ne_zero.2 fun h => ?_)
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    have e := congrArg norm h
    rw [norm_one, norm_mul] at e
    nlinarith [norm_nonneg x2, norm_nonneg u]
  have hQc : ContinuousOn Q (closedBall (0 : ℂ) 1) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop) hne)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hQc
  refine ⟨M, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le one_pos hx)
  have hxx2 : x - x2 ≠ 0 := sub_ne_zero.2 fun h => by rw [h] at hx; linarith
  have hu : x⁻¹ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have e : (γ * (x * x2 * (x + x2) / 2 - x * x2) + γ' * ((x + x2) / 2 - x * x2)) *
      ((x - x2) ^ 2)⁻¹ = Q x⁻¹ := by
    have h1 : (1 - x2 * x⁻¹) = (x - x2) / x := by field_simp
    simp only [hQ]
    rw [h1]
    field_simp
  rw [e]
  exact hM _ hu

/-- Step 2 of Lemma 3.5 from the inner and outer patches (l.914–924): removable singularities at
`x₁ = 0`, `x₁ = x₂`, continuation to `∞`, and Liouville's theorem at each order in `z`. -/
theorem sub_bergman_const_of_patches (hH : Stmt_sub_bergman_holo) (hI : Stmt_sub_bergman_inner)
    (hO : Stmt_sub_bergman_outer) : Stmt_sub_bergman_const := by
  intro x2 h20 h21
  have h20' : x2 ≠ 0 := norm_pos_iff.1 h20
  set LF : ℂ → PowerSeries ℂ := fun x1 =>
    Yser x1 * Wser x1 x2 + gser x2 * Sser x1 x2 * C (((x1 - x2) ^ 2)⁻¹) with hLF
  have hinv : ∀ x : ℂ, x ≠ x2 → DifferentiableAt ℂ (fun y : ℂ => ((y - x2) ^ 2)⁻¹) x :=
    fun x hx => ((differentiableAt_id.sub (differentiableAt_const _)).pow 2).inv
      (pow_ne_zero 2 (sub_ne_zero.2 hx))
  have key : ∀ (j : ℕ) (x y : ℂ), 0 < ‖x‖ → ‖x‖ < 1 → x ≠ x2 → 0 < ‖y‖ → ‖y‖ < 1 → y ≠ x2 →
      coeff j (LF x) = coeff j (LF y) := by
    intro j
    have hpd : ∀ x : ℂ, x ≠ x2 →
        DifferentiableAt ℂ (fun y => coeff j (gser x2 * Sser y x2) * ((y - x2) ^ 2)⁻¹) x :=
      fun x hx => (((CoeffDiff.const (gser x2) x).mul (coeffDiff_Sser x x2)) j).mul (hinv x hx)
    have hO' : ∀ i : ℕ, ∃ Go : ℂ → ℂ,
        DifferentiableOn ℂ Go {x | ‖x2‖ < ‖x‖} ∧ (∃ M : ℝ, ∀ x, 1 ≤ ‖x‖ → ‖Go x‖ ≤ M) ∧
        ∀ x1 : ℂ, ‖x2‖ < ‖x1‖ → ‖x1‖ < 1 →
          x1 * (1 - x1) ^ (1 / 2 : ℂ) * coeff i (Wser x1 x2) = Go x1 :=
      fun i => hO x2 h20 h21 i
    choose GoW hGoD hGoB hGoE using hO'
    choose MW hMW using hGoB
    refine liouville_glue (b := x2) (ρ := ‖x2‖) (G := fun x => coeff j (LF x))
      (Go := fun x => ∑ p ∈ antidiagonal j, (x⁻¹ ^ p.1 * coeff p.1 sOneC) * GoW p.2 x +
        coeff j (gser x2 * Sser x x2) * ((x - x2) ^ 2)⁻¹) h20' le_rfl h21 ?_ ?_ ?_ ?_ ?_ ?_
    · -- holomorphic off `0` and `x₂`
      intro x hx
      have hx1 : ‖x‖ < 1 := by simpa using hx.1.1
      have hxx2 : x ≠ x2 := hx.1.2
      have hx0 : x ≠ 0 := hx.2
      have hW : CoeffDiff (fun y => Wser y x2) x := by
        have e : (fun y => Wser y x2) = fun y => C (((y - x2) ^ 2)⁻¹) + Wnos y x2 :=
          funext fun y => Wser_eq y x2
        rw [e]
        exact (CoeffDiff.C (hinv x hxx2)).add (hH x2 h21 x (norm_pos_iff.2 hx0) hx1)
      exact ((((coeffDiff_Yser hx0 hx1).mul hW).add
        (((CoeffDiff.const (gser x2) x).mul (coeffDiff_Sser x x2)).mul
          (CoeffDiff.C (hinv x hxx2)))) j).differentiableWithinAt
    · -- bounded near `0`: the inner patch
      have hGeq : (fun x => coeff j (LF x)) = fun x =>
          (1 - x) ^ (1 / 2 : ℂ) * coeff j (C x * sqrtZ x * Wser x x2) +
            coeff j (gser x2 * Sser x x2) * ((x - x2) ^ 2)⁻¹ := funext fun x => by
        have e : LF x = C ((1 - x) ^ (1 / 2 : ℂ)) * (C x * sqrtZ x * Wser x x2) +
            gser x2 * Sser x x2 * C (((x - x2) ^ 2)⁻¹) := by
          simp only [hLF, Yser, map_mul]
          ring
        rw [e, map_add, coeff_C_mul, PowerSeries.coeff_mul_C]
      show BddNear (fun x => coeff j (LF x)) 0
      rw [hGeq]
      exact ((BddNear.of_continuousAt
        (differentiableAt_sqrt_one_sub (by simp)).continuousAt).mul (hI x2 h20 h21 j)).add
        (BddNear.of_continuousAt (hpd 0 h20'.symm).continuousAt)
    · -- bounded near `x₂`: the double pole cancels
      have hGeq : (fun x => coeff j (LF x)) = fun x =>
          coeff j (Yser x * Wnos x x2) +
            coeff j ((Yser x + gser x2 * Sser x x2) * C (((x - x2) ^ 2)⁻¹)) := funext fun x => by
        have e : LF x = Yser x * Wnos x x2 +
            (Yser x + gser x2 * Sser x x2) * C (((x - x2) ^ 2)⁻¹) := by
          simp only [hLF, Wser_eq]
          ring
        rw [e, map_add]
      show BddNear (fun x => coeff j (LF x)) x2
      rw [hGeq]
      have hYc : CoeffCont Yser x2 := (coeffDiff_Yser h20' h21).coeffCont
      have hF : CoeffCont (fun x => C 4 * (Yser x * Yser x2 - Sser x x2)) x2 :=
        (CoeffCont.const (C 4) x2).mul
          ((hYc.mul (CoeffCont.const (Yser x2) x2)).sub (coeffCont_Sser x2))
      have hR : CoeffCont (fun x => -(gser x2 * (C x * C x2 - X) ^ 2)) x2 :=
        ((CoeffCont.const (gser x2) x2).mul
          ((((CoeffCont.C continuousAt_id).mul (CoeffCont.const (C x2) x2)).sub
            (CoeffCont.const X x2)).pow 2)).neg
      have hP0 : coeff 0 (Pser x2) = x2 ^ 2 * (x2 - 1) := by
        simp [Pser]
      have h0' : coeff 0 (C 4 * (Yser x2 * Yser x2 - Sser x2 x2)) ≠ 0 := by
        rw [← pow_two, Yser_sq h20' h21, Sser_diag, coeff_C_mul, map_sub, map_neg, hP0]
        intro h
        apply mul_ne_zero (pow_ne_zero 2 h20') (sub_ne_zero.2 (ne_one_of_norm_lt h21))
        linear_combination (-1 / 8 : ℂ) * h
      have hopen : IsOpen {y : ℂ | 0 < ‖y‖ ∧ ‖y‖ < 1} :=
        (isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)
      have hmul : ∀ᶠ x in 𝓝[≠] x2,
          (Yser x + gser x2 * Sser x x2) * C (((x - x2) ^ 2)⁻¹) *
            (C 4 * (Yser x * Yser x2 - Sser x x2)) = -(gser x2 * (C x * C x2 - X) ^ 2) := by
        filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds ⟨h20, h21⟩), self_mem_nhdsWithin]
          with x hx hxne
        exact pole_identity (norm_pos_iff.1 hx.1) hx.2 h20' h21 hxne
      obtain ⟨L, hL⟩ := tendsto_coeff_of_mul hF hR h0' hmul j
      exact (BddNear.of_continuousAt ((hYc.mul (coeffCont_Wnos h20 h21 h21)) j)).add
        (BddNear.of_tendsto hL)
    · -- the outer function is holomorphic on `|x| > |x₂|`
      intro x hx
      have hx' : ‖x2‖ < ‖x‖ := hx
      have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_trans h20 hx')
      have hxx2 : x ≠ x2 := fun h => by rw [h] at hx'; exact lt_irrefl _ hx'
      have hmem : {y : ℂ | ‖x2‖ < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hx'
      exact (DifferentiableAt.add (DifferentiableAt.fun_sum fun p _ =>
        (((differentiableAt_inv hx0).pow p.1).mul (differentiableAt_const _)).mul
          ((hGoD p.2).differentiableAt hmem)) (hpd x hxx2)).differentiableWithinAt
    · -- bounded on `|x| ≥ 1`
      obtain ⟨MQ, hMQ⟩ := pole_bdd_outside h21 (coeff j (gser x2)) (coeff j (gser x2 * X))
      refine ⟨∑ p ∈ antidiagonal j, ‖coeff p.1 sOneC‖ * MW p.2 + MQ, fun x hx => ?_⟩
      refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun p _ => ?_)) ?_)
      · rw [norm_mul, norm_mul, norm_pow, norm_inv]
        have h1 : ‖x‖⁻¹ ^ p.1 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hx)
        have h2 := hMW p.2 x hx
        calc ‖x‖⁻¹ ^ p.1 * ‖coeff p.1 sOneC‖ * ‖GoW p.2 x‖
            ≤ 1 * ‖coeff p.1 sOneC‖ * MW p.2 := by
              have := norm_nonneg (coeff p.1 sOneC)
              have := norm_nonneg (GoW p.2 x)
              gcongr
          _ = ‖coeff p.1 sOneC‖ * MW p.2 := by rw [one_mul]
      · rw [coeff_mul_Sser]
        exact hMQ x hx
    · -- agreement on the annulus `|x₂| < |x| < 1`
      intro x hx hx1
      show coeff j (LF x) = _
      simp only [hLF]
      rw [map_add, PowerSeries.coeff_mul_C, coeff_mul]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← hGoE p.2 x hx hx1, Yser, coeff_C_mul, coeff_sqrtZ]
      ring
  have hn : ‖x2 / 2‖ = ‖x2‖ / 2 := by simp
  refine ⟨LF (x2 / 2), fun x1 h10 h11 hne => ?_⟩
  ext j
  exact key j x1 (x2 / 2) h10 h11 hne (by rw [hn]; linarith) (by rw [hn]; linarith)
    (fun h => by
      have := congrArg norm h
      rw [hn] at this
      linarith)

end Virasoro.Sphere
