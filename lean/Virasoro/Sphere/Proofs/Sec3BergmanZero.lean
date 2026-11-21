import Virasoro.Sphere.Proofs.Sec3BergmanZeroInt
import Mathlib.Algebra.Polynomial.Roots

/-!
# Sphere paper Lemma 3.5, Step 3, zero-mode condition (`sphere/paper.tex` l.931–941)

`∮_{|x₁|=r} W dx₁ = 0` at every order in `z` (l.931–933).  Dividing the formula for `W` by
`1/Y(x₂)` gives `∮ (S(x₁,x₂)/(x₁-x₂)² + 2C)/Y(x₁) dx₁ = 0` for `r < |x₂| < 1`; at each order in
`z` this integral is a polynomial in `w = 1/x₂` (`2πi` times a Laurent coefficient), so it
vanishes identically, and its value at `w = 0` (`x₂ → ∞`) is
`∮ (x₁/2 + 2C)/Y(x₁) dx₁ = 0` (l.933–935).  With `F₀ = [x⁰]`, `F₁ = [x⁻¹]` of
`(1-z/x)^{-1/2}(1-x)^{-1/2}` this is `F₁/2 + 2C F₀ = 0`.

Consumer: `Stmt_lem_bergman_det`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Real

/-- `[z^q]((S(x,x₂)/(x-x₂)² + 2C) g(x))`, the integrand after dividing by `g(x₂)`. -/
noncomputable def HqF (Cz : PowerSeries ℂ) (x2 x : ℂ) (q : ℕ) : ℂ :=
  coeff q (gser x * (C (((x - x2) ^ 2)⁻¹) * Sser x x2 + 2 * Cz))

/-- `h_{q-1}` (zero for `q = 0`). -/
noncomputable def hmq (q : ℕ) : ℂ := if q = 0 then 0 else ((halfBinom (q - 1) : ℚ) : ℂ)

/-- `λ_{q-1}(w)` (zero for `q = 0`). -/
noncomputable def lam1 (w : ℂ) (q : ℕ) : ℂ := if q = 0 then 0 else lam w (q - 1)

/-- `λ_{q-2}(w)` (zero for `q < 2`). -/
noncomputable def lam2 (w : ℂ) (q : ℕ) : ℂ := if q < 2 then 0 else lam w (q - 2)

/-- `2 [z^q](F₀ C)`. -/
noncomputable def SzC (Cz : PowerSeries ℂ) (q : ℕ) : ℂ :=
  ∑ p ∈ antidiagonal q, 2 * ((halfBinom p.1 : ℚ) : ℂ) ^ 2 * coeff p.2 Cz

theorem half_pos' : (0 : ℝ) < 1 / 2 := by norm_num

theorem half_lt_one' : (1 / 2 : ℝ) < 1 := by norm_num

/-- `∮ (S/(x₁-x₂)² + 2C)/Y(x₁) dx₁ = 0` at every order in `z`, for `1/2 < |x₂| < 1`. -/
theorem int_HqF_zero {Cz : PowerSeries ℂ} (hC : IsWFormula Cz) {w : ℂ} (hw1 : 1 < ‖w‖)
    (hw2 : ‖w‖ < 2) (q : ℕ) : (∮ x in C(0, 1 / 2), HqF Cz w⁻¹ x q) = 0 := by
  have hwpos : 0 < ‖w‖ := lt_trans one_pos hw1
  have h2a : (1 / 2 : ℝ) < ‖w⁻¹‖ := by
    rw [norm_inv, show (1 / 2 : ℝ) = 2⁻¹ by norm_num]
    exact (inv_lt_inv₀ two_pos hwpos).2 hw2
  have h2b : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hw1
  generalize w⁻¹ = x2 at h2a h2b ⊢
  have hr0 := half_pos'
  have hr1 := half_lt_one'
  have h20 : 0 < ‖x2‖ := lt_trans hr0 h2a
  have hsph : ∀ x ∈ Metric.sphere (0 : ℂ) (1 / 2), x ≠ 0 ∧ ‖x‖ < 1 ∧ x ≠ x2 := fun x hx => by
    obtain ⟨h0, hr, h1⟩ := sphere_facts hr0 hr1 hx
    exact ⟨h0, h1, fun h => by rw [h] at hr; linarith⟩
  have hcont : ∀ k, ContinuousOn (fun x => HqF Cz x2 x k) (Metric.sphere (0 : ℂ) (1 / 2)) :=
    fun k x hx => by
      obtain ⟨hx0, hx1, hxx2⟩ := hsph x hx
      have hinv : ContinuousAt (fun y : ℂ => ((y - x2) ^ 2)⁻¹) x :=
        ((continuousAt_id.sub continuousAt_const).pow 2).inv₀
          (pow_ne_zero 2 (sub_ne_zero.2 hxx2))
      exact (((coeffCont_gser hx0 hx1).mul (((CoeffCont.C hinv).mul
        (coeffDiff_Sser x x2).coeffCont).add (CoeffCont.const (2 * Cz) x))) k).continuousWithinAt
  have hII : ∀ j, ∑ p ∈ antidiagonal j,
      coeff p.1 (gser x2) * ∮ x in C(0, 1 / 2), HqF Cz x2 x p.2 = 0 := fun j => by
    have h0 := circleIntegral_W_eq_zero j hr0 hr1 h2b (ne_of_gt h2a)
    have hcongr : (∮ x in C(0, 1 / 2), coeff j (Wser x x2)) =
        ∮ x in C(0, 1 / 2), ∑ p ∈ antidiagonal j,
          -(coeff p.1 (gser x2)) * HqF Cz x2 x p.2 := by
      refine circleIntegral.integral_congr hr0.le fun x hx => ?_
      obtain ⟨hx0, hx1, hxx2⟩ := hsph x hx
      have hW := (hC x x2 (norm_pos_iff.2 hx0) hx1 h20 h2b hxx2).2
      show coeff j (Wser x x2) =
        ∑ p ∈ antidiagonal j, -(coeff p.1 (gser x2)) * HqF Cz x2 x p.2
      rw [hW, YYinv_eq, show -(gser x * gser x2) * (C (((x - x2) ^ 2)⁻¹) * Sser x x2 + 2 * Cz) =
        -(gser x2 * (gser x * (C (((x - x2) ^ 2)⁻¹) * Sser x x2 + 2 * Cz))) by ring, map_neg,
        coeff_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => by rw [HqF]; ring
    rw [hcongr, circleIntegral.integral_fun_sum (fun p _ =>
      (continuousOn_const.mul (hcont p.2)).circleIntegrable hr0.le)] at h0
    simp only [circleIntegral.integral_const_mul] at h0
    have e : ∑ p ∈ antidiagonal j, coeff p.1 (gser x2) * ∮ x in C(0, 1 / 2), HqF Cz x2 x p.2 =
        -∑ p ∈ antidiagonal j,
          -(coeff p.1 (gser x2)) * ∮ x in C(0, 1 / 2), HqF Cz x2 x p.2 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [e, h0, neg_zero]
  have hg0 : coeff 0 (gser x2) ≠ 0 := by
    have hx20 : x2 ≠ 0 := norm_pos_iff.1 h20
    rw [coeff_gser hx20 h2b]
    have hs := sqrt_mul_hfun h2b
    have hhf : hfun x2 ≠ 0 := fun h => by
      rw [h, mul_zero] at hs
      exact zero_ne_one hs
    have hh0 : ((halfBinom 0 : ℚ) : ℂ) ≠ 0 := by simp [halfBinom, gbinom]
    exact mul_ne_zero (mul_ne_zero hh0 (zpow_ne_zero _ hx20)) hhf
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    have h := hII q
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_eq_single 0] at h
    · exact (mul_eq_zero.1 h).resolve_left hg0
    · intro k hk hk0
      have hk' := Finset.mem_range.1 hk
      exact mul_eq_zero_of_right _ (ih (q - k) (by omega))
    · intro h'
      exact absurd (Finset.mem_range.2 (Nat.succ_pos q)) h'

/-- The contour integral of a combination of the Laurent monomials times `(1-xw)⁻²(1-x)^{-1/2}`
and `(1-x)^{-1/2}`. -/
theorem int_combo (w : ℂ) (hwr : ‖w‖ * (1 / 2) < 1) (A1 A2 : ℂ) (q : ℕ) (c : ℕ × ℕ → ℂ) :
    (∮ x in C(0, 1 / 2), (A1 * (x ^ (-(q : ℤ)) * (Efun w x * hfun x)) +
        A2 * (x ^ (-(q : ℤ) + 1) * (Efun w x * hfun x)) +
        ∑ p ∈ antidiagonal q, c p * (x ^ (-(p.1 : ℤ) - 1) * hfun x))) =
      (2 * π * Complex.I) * (A1 * lam1 w q + A2 * lam2 w q +
        ∑ p ∈ antidiagonal q, c p * ((halfBinom p.1 : ℚ) : ℂ)) := by
  have hr0 := half_pos'
  have hr1 := half_lt_one'
  have hI1 : CircleIntegrable (fun x : ℂ => A1 * (x ^ (-(q : ℤ)) * (Efun w x * hfun x))) 0
      (1 / 2) := (ci_E w _ hr0 hr1 hwr).const_smul
  have hI2 : CircleIntegrable (fun x : ℂ => A2 * (x ^ (-(q : ℤ) + 1) * (Efun w x * hfun x))) 0
      (1 / 2) := (ci_E w _ hr0 hr1 hwr).const_smul
  have hI12 : CircleIntegrable (fun x : ℂ => A1 * (x ^ (-(q : ℤ)) * (Efun w x * hfun x)) +
      A2 * (x ^ (-(q : ℤ) + 1) * (Efun w x * hfun x))) 0 (1 / 2) := hI1.add hI2
  have hI3t : ∀ p ∈ antidiagonal q,
      CircleIntegrable (fun x : ℂ => c p * (x ^ (-(p.1 : ℤ) - 1) * hfun x)) 0 (1 / 2) :=
    fun p _ => (ci_h _ hr0 hr1).const_smul
  have hI3 : CircleIntegrable (fun x : ℂ => ∑ p ∈ antidiagonal q,
      c p * (x ^ (-(p.1 : ℤ) - 1) * hfun x)) 0 (1 / 2) := by
    have e : (fun x : ℂ => ∑ p ∈ antidiagonal q, c p * (x ^ (-(p.1 : ℤ) - 1) * hfun x)) =
        ∑ p ∈ antidiagonal q, fun x : ℂ => c p * (x ^ (-(p.1 : ℤ) - 1) * hfun x) := by
      ext x
      rw [Finset.sum_apply]
    rw [e]
    exact CircleIntegrable.sum _ hI3t
  have hv1 : (∑' i : ℕ, if -(q : ℤ) + (i : ℤ) = -1 then lam w i * (2 * π * Complex.I) else 0) =
      lam1 w q * (2 * π * Complex.I) := by
    rw [lam1]
    by_cases h : q = 0
    · rw [if_pos h, zero_mul]
      exact tsum_pick_none _ _ (by omega)
    · rw [if_neg h]
      exact tsum_pick (fun i => lam w i * (2 * π * Complex.I)) _ (q - 1) (by omega)
  have hv2 : (∑' i : ℕ, if -(q : ℤ) + 1 + (i : ℤ) = -1 then lam w i * (2 * π * Complex.I)
      else 0) = lam2 w q * (2 * π * Complex.I) := by
    rw [lam2]
    by_cases h : q < 2
    · rw [if_pos h, zero_mul]
      exact tsum_pick_none _ _ (by omega)
    · rw [if_neg h]
      exact tsum_pick (fun i => lam w i * (2 * π * Complex.I)) _ (q - 2) (by omega)
  have hv3 : ∀ p : ℕ × ℕ, (∑' i : ℕ, if -(p.1 : ℤ) - 1 + (i : ℤ) = -1 then
      ((halfBinom i : ℚ) : ℂ) * (2 * π * Complex.I) else 0) =
      ((halfBinom p.1 : ℚ) : ℂ) * (2 * π * Complex.I) := fun p =>
    tsum_pick (fun i => ((halfBinom i : ℚ) : ℂ) * (2 * π * Complex.I)) _ p.1 (by omega)
  rw [circleIntegral.integral_add hI12 hI3, circleIntegral.integral_add hI1 hI2,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_fun_sum hI3t, int_E w _ hr0 hr1 hwr, int_E w _ hr0 hr1 hwr, hv1, hv2]
  simp only [circleIntegral.integral_const_mul, int_h _ hr0 hr1, hv3]
  have e : ∑ p ∈ antidiagonal q, c p * (((halfBinom p.1 : ℚ) : ℂ) * (2 * π * Complex.I)) =
      (2 * π * Complex.I) * ∑ p ∈ antidiagonal q, c p * ((halfBinom p.1 : ℚ) : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e]
  ring

/-- The zero-mode integral at order `z^q` as a polynomial in `w = 1/x₂` (l.933–935). -/
theorem int_HqF_eval (Cz : PowerSeries ℂ) {w : ℂ} (hw1 : 1 < ‖w‖) (hw2 : ‖w‖ < 2) (q : ℕ) :
    (∮ x in C(0, 1 / 2), HqF Cz w⁻¹ x q) =
      (2 * π * Complex.I) *
        ((((halfBinom q : ℚ) : ℂ) * (1 / 2 - w) + hmq q * (w / 2)) * lam1 w q +
          (((halfBinom q : ℚ) : ℂ) * (w / 2) + hmq q * (w ^ 2 / 2 - w)) * lam2 w q +
          SzC Cz q) := by
  have hr0 := half_pos'
  have hr1 := half_lt_one'
  have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_trans one_pos hw1)
  have hwr : ‖w‖ * (1 / 2) < 1 := by linarith
  have hcongr : (∮ x in C(0, 1 / 2), HqF Cz w⁻¹ x q) =
      ∮ x in C(0, 1 / 2),
        ((((halfBinom q : ℚ) : ℂ) * (1 / 2 - w) + hmq q * (w / 2)) *
            (x ^ (-(q : ℤ)) * (Efun w x * hfun x)) +
          (((halfBinom q : ℚ) : ℂ) * (w / 2) + hmq q * (w ^ 2 / 2 - w)) *
            (x ^ (-(q : ℤ) + 1) * (Efun w x * hfun x)) +
          ∑ p ∈ antidiagonal q, (2 * ((halfBinom p.1 : ℚ) : ℂ) * coeff p.2 Cz) *
            (x ^ (-(p.1 : ℤ) - 1) * hfun x)) := by
    refine circleIntegral.integral_congr hr0.le fun x hx => ?_
    obtain ⟨hx0, hxr, hx1⟩ := sphere_facts hr0 hr1 hx
    have hne : x ≠ w⁻¹ := fun h => by
      have e := congrArg norm h
      rw [hxr, norm_inv] at e
      have h2 : ‖w‖ = 2 := by
        rw [← inv_inv ‖w‖, ← e]
        norm_num
      linarith
    show HqF Cz w⁻¹ x q = _
    rw [HqF, hmq]
    exact zm_integrand Cz hx0 hx1 hw0 hne q
  rw [hcongr, int_combo w hwr]
  have e : ∑ p ∈ antidiagonal q, 2 * ((halfBinom p.1 : ℚ) : ℂ) * coeff p.2 Cz *
      ((halfBinom p.1 : ℚ) : ℂ) = SzC Cz q := by
    rw [SzC]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e]

/-- `λ_i` as a polynomial in `w`. -/
noncomputable def Lp (i : ℕ) : Polynomial ℂ :=
  ∑ kl ∈ antidiagonal i,
    Polynomial.C (((kl.1 : ℂ) + 1) * ((halfBinom kl.2 : ℚ) : ℂ)) * Polynomial.X ^ kl.1

theorem eval_Lp (w : ℂ) (i : ℕ) : (Lp i).eval w = lam w i := by
  rw [Lp, lam, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun kl _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem lam_zero (i : ℕ) : lam 0 i = ((halfBinom i : ℚ) : ℂ) := by
  rw [lam, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp

/-- The zero-mode integral at order `z^q`, divided by `2πi`, as a polynomial in `w = 1/x₂`. -/
noncomputable def Pq (Cz : PowerSeries ℂ) (q : ℕ) : Polynomial ℂ :=
  (Polynomial.C ((halfBinom q : ℚ) : ℂ) * (Polynomial.C (1 / 2) - Polynomial.X) +
      Polynomial.C (hmq q) * (Polynomial.C (1 / 2) * Polynomial.X)) *
      (if q = 0 then 0 else Lp (q - 1)) +
    (Polynomial.C ((halfBinom q : ℚ) : ℂ) * (Polynomial.C (1 / 2) * Polynomial.X) +
      Polynomial.C (hmq q) * (Polynomial.C (1 / 2) * Polynomial.X ^ 2 - Polynomial.X)) *
      (if q < 2 then 0 else Lp (q - 2)) +
    Polynomial.C (SzC Cz q)

theorem eval_Pq (Cz : PowerSeries ℂ) (q : ℕ) (w : ℂ) :
    (Pq Cz q).eval w =
      (((halfBinom q : ℚ) : ℂ) * (1 / 2 - w) + hmq q * (w / 2)) * lam1 w q +
        (((halfBinom q : ℚ) : ℂ) * (w / 2) + hmq q * (w ^ 2 / 2 - w)) * lam2 w q + SzC Cz q := by
  have e1 : (if q = 0 then (0 : Polynomial ℂ) else Lp (q - 1)).eval w = lam1 w q := by
    rw [lam1]
    split_ifs <;> simp [eval_Lp]
  have e2 : (if q < 2 then (0 : Polynomial ℂ) else Lp (q - 2)).eval w = lam2 w q := by
    rw [lam2]
    split_ifs <;> simp [eval_Lp]
  rw [Pq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, e1, e2]
  ring

/-- The leading term as `x₂ → ∞` (l.933–935): `[z^q](F₁/2 + 2 F₀ C) = 0`. -/
theorem zero_mode_coeff {Cz : PowerSeries ℂ} (hC : IsWFormula Cz) (q : ℕ) :
    ((halfBinom q : ℚ) : ℂ) * hmq q / 2 + SzC Cz q = 0 := by
  have hroot : ∀ t : ℝ, 1 < t → t < 2 → (Pq Cz q).IsRoot (t : ℂ) := fun t h1 h2 => by
    have hn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hA := int_HqF_zero hC (w := (t : ℂ)) (by rw [hn]; exact h1) (by rw [hn]; exact h2) q
    rw [int_HqF_eval Cz (by rw [hn]; exact h1) (by rw [hn]; exact h2) q] at hA
    have hK : (2 * (π : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
        Complex.I_ne_zero
    rw [Polynomial.IsRoot, eval_Pq]
    exact (mul_eq_zero.1 hA).resolve_left hK
  have hinf : Set.Infinite {x : ℂ | (Pq Cz q).IsRoot x} :=
    ((Set.Ioo_infinite (by norm_num : (1 : ℝ) < 2)).image
      Complex.ofReal_injective.injOn).mono (by
        rintro _ ⟨t, ht, rfl⟩
        exact hroot t ht.1 ht.2)
  have hP := Polynomial.eq_zero_of_infinite_isRoot _ hinf
  have h0 := congrArg (Polynomial.eval 0) hP
  rw [eval_Pq, Polynomial.eval_zero] at h0
  have hl1 : lam1 0 q = hmq q := by
    rw [lam1, hmq]
    split_ifs
    · rfl
    · exact lam_zero _
  rw [hl1] at h0
  linear_combination h0

/-- Lemma 3.5, Step 3, zero-mode condition (sphere/paper.tex l.931–941). -/
theorem sub_bergman_zero_mode : Stmt_sub_bergman_zero_mode := by
  intro Cz hC
  have hF0 : hyp2F1.map (algebraMap ℚ ℂ) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    rw [coeff_map, hyp2F1_eq, coeff_mk] at h'
    simp [halfBinom, gbinom] at h'
  have key : F1ser.map (algebraMap ℚ ℂ) + 4 * (hyp2F1.map (algebraMap ℚ ℂ) * Cz) = 0 := by
    ext q
    have h := zero_mode_coeff hC q
    have h4 : (4 : PowerSeries ℂ) = C 4 := (map_ofNat C 4).symm
    have hs : ∑ p ∈ antidiagonal q, coeff p.1 (hyp2F1.map (algebraMap ℚ ℂ)) * coeff p.2 Cz =
        SzC Cz q / 2 := by
      rw [SzC, Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => by
        rw [coeff_map, hyp2F1_eq, coeff_mk, eq_ratCast]
        push_cast
        ring
    have hf : (algebraMap ℚ ℂ) (if q = 0 then 0 else halfBinom q * halfBinom (q - 1)) =
        ((halfBinom q : ℚ) : ℂ) * hmq q := by
      rw [hmq, eq_ratCast]
      split_ifs <;> simp
    rw [map_add, h4, coeff_C_mul, coeff_mul, hs, coeff_map, F1ser, coeff_mk, hf, map_zero]
    linear_combination 2 * h
  have hR := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) F1ser_ratio
  rw [map_neg, map_mul] at hR
  refine mul_right_cancel₀ hF0 ?_
  rw [← hR]
  linear_combination key

/-- Lemma 3.5 (Bergman-kernel evaluation of the Gaussian determinant), sphere/paper.tex
l.825–970, from the Jacobi identity (2.3) cited there (l.969).

Paper label: lem:bergman-det -/
theorem lem_bergman_det_of_cited (hJ2 : Cited_JacobiIdentities2) : Stmt_lem_bergman_det :=
  lem_bergman_det_of_zero_mode hJ2 sub_bergman_zero_mode

example (hJ2 : Cited_JacobiIdentities2) : Stmt_lem_bergman_det := lem_bergman_det_of_cited hJ2

end Virasoro.Sphere
