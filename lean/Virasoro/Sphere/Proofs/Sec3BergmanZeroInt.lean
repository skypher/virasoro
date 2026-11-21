import Virasoro.Sphere.Proofs.Sec3BergmanStep2

/-!
# Sphere paper Lemma 3.5, Step 3, zero-mode condition: the contour integrals
(`sphere/paper.tex` l.931–937)

On `|x| = r < 1`: `[z^q] (1/Y(x)) ∝ h_q x^{-q-1}(1-x)^{-1/2}`, and for `|w| r < 1` the function
`(1-xw)⁻²(1-x)^{-1/2} = ∑_i λ_i(w) x^i` with `λ_i(w) = ∑_{k+l=i} (k+1) w^k h_l` a polynomial in
`w = 1/x₂`.  Each contour integral is `2πi` times a coefficient of these series
(`[x^0]` and `[x^{-1}]` of `(1-z/x)^{-1/2}(1-x)^{-1/2}` for `w = 0`, l.935–937).

Consumer: `sub_bergman_zero_mode`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Real

theorem coeff_gser {x : ℂ} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) (q : ℕ) :
    coeff q (gser x) = ((halfBinom q : ℚ) : ℂ) * x ^ (-(q : ℤ) - 1) * hfun x := by
  have hs := sqrt_mul_hfun hx1
  have hh : hfun x = ((1 - x) ^ (1 / 2 : ℂ))⁻¹ := eq_inv_of_mul_eq_one_right hs
  rw [gser, coeff_C_mul, invSqrtZ, coeff_mk, zpow_sub_one₀ hx0, hh, mul_inv]
  ring

/-- `(1 - x w)⁻²`. -/
noncomputable def Efun (w x : ℂ) : ℂ := ((1 - x * w) ^ 2)⁻¹

/-- `λ_i(w) = ∑_{k+l=i} (k+1) w^k h_l`. -/
noncomputable def lam (w : ℂ) (i : ℕ) : ℂ :=
  ∑ kl ∈ antidiagonal i, (((kl.1 : ℂ) + 1) * w ^ kl.1) * ((halfBinom kl.2 : ℚ) : ℂ)

theorem summable_lam {w : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hw : ‖w‖ * r < 1) :
    Summable fun i : ℕ => ‖lam w i‖ * r ^ i := by
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0]
  have hf : Summable fun k : ℕ => ‖((k : ℂ) + 1) * (w * (r : ℂ)) ^ k‖ := by
    have h := summable_succ_mul_geom (r := ‖w‖ * r) (by positivity) hw 1
    refine h.congr fun k => ?_
    simp only [one_mul, norm_mul, norm_pow, hnr]
  have hg : Summable fun l : ℕ => ‖((coeff l hser : ℚ) : ℂ) * (r : ℂ) ^ l‖ :=
    absC_hser (by rw [hnr]; exact hr1)
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  refine h.congr fun i => ?_
  have e : ‖lam w i‖ * r ^ i = ‖lam w i * (r : ℂ) ^ i‖ := by rw [norm_mul, norm_pow, hnr]
  rw [e, lam, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hkl' : kl.1 + kl.2 = i := by simpa using hkl
  rw [← hkl', pow_add, mul_pow, hser, coeff_mk]
  ring

theorem E_mul_hfun {w x : ℂ} (hx : ‖x‖ < 1) (hxw : ‖x * w‖ < 1) :
    Efun w x * hfun x = ∑' i : ℕ, lam w i * x ^ i := by
  have hf : Summable fun k : ℕ => ‖((k : ℂ) + 1) * (x * w) ^ k‖ := by
    have h := summable_succ_mul_geom (r := ‖x * w‖) (norm_nonneg _) hxw 1
    refine h.congr fun k => ?_
    simp only [one_mul, norm_mul, norm_pow]
  have hg : Summable fun l : ℕ => ‖((coeff l hser : ℚ) : ℂ) * x ^ l‖ := absC_hser hx
  rw [Efun, ← tsum_succ_mul_geom hxw, hfun, evq,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun i => ?_
  rw [lam, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hkl' : kl.1 + kl.2 = i := by simpa using hkl
  rw [← hkl', pow_add, mul_pow, hser, coeff_mk]
  ring

variable {r : ℝ}

theorem int_E (w : ℂ) (a : ℤ) (hr0 : 0 < r) (hr1 : r < 1) (hw : ‖w‖ * r < 1) :
    (∮ x in C(0, r), x ^ a * (Efun w x * hfun x)) =
      ∑' i : ℕ, if a + (i : ℤ) = -1 then lam w i * (2 * π * Complex.I) else 0 := by
  rw [← circleIntegral_zpow_mul_tsum (lam w) a hr0 (summable_lam hr0.le hr1 hw)]
  refine circleIntegral.integral_congr hr0.le fun x hx => ?_
  have hxr : ‖x‖ = r := by simpa using hx
  show x ^ a * (Efun w x * hfun x) = x ^ a * ∑' i : ℕ, lam w i * x ^ i
  rw [E_mul_hfun (by rw [hxr]; exact hr1) (by rw [norm_mul, hxr, mul_comm]; exact hw)]

theorem int_h (a : ℤ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ x in C(0, r), x ^ a * hfun x) =
      ∑' i : ℕ, if a + (i : ℤ) = -1 then ((halfBinom i : ℚ) : ℂ) * (2 * π * Complex.I) else 0 := by
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hs : Summable fun i : ℕ => ‖((halfBinom i : ℚ) : ℂ)‖ * r ^ i := by
    have h : Summable fun k : ℕ => ‖((coeff k hser : ℚ) : ℂ) * (r : ℂ) ^ k‖ :=
      absC_hser (by rw [hnr]; exact hr1)
    refine h.congr fun i => ?_
    rw [norm_mul, norm_pow, hnr, hser, coeff_mk]
  rw [← circleIntegral_zpow_mul_tsum (fun i => ((halfBinom i : ℚ) : ℂ)) a hr0 hs]
  refine circleIntegral.integral_congr hr0.le fun x _ => ?_
  show x ^ a * hfun x = x ^ a * ∑' i : ℕ, ((halfBinom i : ℚ) : ℂ) * x ^ i
  rw [hfun, evq]
  simp only [hser, coeff_mk]

theorem tsum_pick (c : ℕ → ℂ) (a : ℤ) (n : ℕ) (h : a + (n : ℤ) = -1) :
    (∑' i : ℕ, if a + (i : ℤ) = -1 then c i else 0) = c n := by
  rw [tsum_eq_single n fun i hi => if_neg (fun hc => hi (by omega)), if_pos h]

theorem tsum_pick_none (c : ℕ → ℂ) (a : ℤ) (h : 0 ≤ a) :
    (∑' i : ℕ, if a + (i : ℤ) = -1 then c i else 0) = 0 := by
  have e : ∀ i : ℕ, (if a + (i : ℤ) = -1 then c i else 0) = 0 := fun i => if_neg (by omega)
  simp only [e, tsum_zero]

theorem sphere_facts (hr0 : 0 < r) (hr1 : r < 1) {x : ℂ} (hx : x ∈ Metric.sphere (0 : ℂ) r) :
    x ≠ 0 ∧ ‖x‖ = r ∧ ‖x‖ < 1 := by
  have hxr : ‖x‖ = r := by simpa using hx
  exact ⟨norm_pos_iff.1 (by rw [hxr]; exact hr0), hxr, by rw [hxr]; exact hr1⟩

theorem ci_h (a : ℤ) (hr0 : 0 < r) (hr1 : r < 1) :
    CircleIntegrable (fun x : ℂ => x ^ a * hfun x) 0 r := by
  refine ContinuousOn.circleIntegrable hr0.le (ContinuousOn.mul (fun x hx => ?_)
    (continuousOn_hfun.mono fun x hx => ?_))
  · exact (continuousAt_zpow₀ x a (Or.inl (sphere_facts hr0 hr1 hx).1)).continuousWithinAt
  · rw [mem_ball_zero_iff]
    exact (sphere_facts hr0 hr1 hx).2.2

theorem ci_E (w : ℂ) (a : ℤ) (hr0 : 0 < r) (hr1 : r < 1) (hw : ‖w‖ * r < 1) :
    CircleIntegrable (fun x : ℂ => x ^ a * (Efun w x * hfun x)) 0 r := by
  refine ContinuousOn.circleIntegrable hr0.le (ContinuousOn.mul (fun x hx => ?_)
    (ContinuousOn.mul (fun x hx => ?_) (continuousOn_hfun.mono fun x hx => ?_)))
  · exact (continuousAt_zpow₀ x a (Or.inl (sphere_facts hr0 hr1 hx).1)).continuousWithinAt
  · have hne : (1 - x * w) ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (sub_ne_zero.2 fun h => ?_)
      have e := congrArg norm h
      rw [norm_one, norm_mul, (sphere_facts hr0 hr1 hx).2.1, mul_comm] at e
      linarith
    unfold Efun
    exact (((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).pow 2).inv₀
      hne).continuousWithinAt
  · rw [mem_ball_zero_iff]
    exact (sphere_facts hr0 hr1 hx).2.2

theorem coeff_mul_X' (f : PowerSeries ℂ) (q : ℕ) :
    coeff q (f * X) = if q = 0 then 0 else coeff (q - 1) f := by
  cases q with
  | zero => simp
  | succ n => rw [coeff_succ_mul_X]; simp

theorem zm_alg (x w Z E hf hq hm : ℂ) (hx : x ≠ 0) (hw : w ≠ 0) :
    w ^ 2 * E * (hq * (Z * x⁻¹) * hf * (x * w⁻¹ * (x + w⁻¹) / 2 - x * w⁻¹) +
        hm * Z * hf * ((x + w⁻¹) / 2 - x * w⁻¹)) =
      (hq * (1 / 2 - w) + hm * (w / 2)) * (Z * (E * hf)) +
        (hq * (w / 2) + hm * (w ^ 2 / 2 - w)) * (Z * x * (E * hf)) := by
  field_simp
  ring

/-- The integrand of the zero-mode condition after dividing by `1/Y(x₂)`, with `x₂ = 1/w`
(l.933–935). -/
theorem zm_integrand (Cz : PowerSeries ℂ) {x w : ℂ} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) (hw : w ≠ 0)
    (hne : x ≠ w⁻¹) (q : ℕ) :
    coeff q (gser x * (C (((x - w⁻¹) ^ 2)⁻¹) * Sser x w⁻¹ + 2 * Cz)) =
      (((halfBinom q : ℚ) : ℂ) * (1 / 2 - w) +
          (if q = 0 then 0 else ((halfBinom (q - 1) : ℚ) : ℂ)) * (w / 2)) *
          (x ^ (-(q : ℤ)) * (Efun w x * hfun x)) +
        (((halfBinom q : ℚ) : ℂ) * (w / 2) +
          (if q = 0 then 0 else ((halfBinom (q - 1) : ℚ) : ℂ)) * (w ^ 2 / 2 - w)) *
          (x ^ (-(q : ℤ) + 1) * (Efun w x * hfun x)) +
        ∑ p ∈ antidiagonal q, (2 * ((halfBinom p.1 : ℚ) : ℂ) * coeff p.2 Cz) *
          (x ^ (-(p.1 : ℤ) - 1) * hfun x) := by
  have h2 : (2 : PowerSeries ℂ) = C 2 := (map_ofNat C 2).symm
  have e : gser x * (C (((x - w⁻¹) ^ 2)⁻¹) * Sser x w⁻¹ + 2 * Cz) =
      C (((x - w⁻¹) ^ 2)⁻¹) * (gser x * Sser x w⁻¹) + C 2 * (gser x * Cz) := by
    rw [h2]
    ring
  rw [e, map_add, coeff_C_mul, coeff_mul_Sser, coeff_mul_X', coeff_C_mul, coeff_mul,
    Finset.mul_sum]
  congr 1
  · have hne' : x - w⁻¹ ≠ 0 := sub_ne_zero.2 hne
    have ha : ((x - w⁻¹) ^ 2)⁻¹ = w ^ 2 * Efun w x := by
      have h1 : (1 - x * w) = -(w * (x - w⁻¹)) := by field_simp; ring
      rw [Efun, h1]
      field_simp
    have hgq : coeff q (gser x) =
        ((halfBinom q : ℚ) : ℂ) * (x ^ (-(q : ℤ)) * x⁻¹) * hfun x := by
      rw [coeff_gser hx0 hx1, zpow_sub_one₀ hx0]
    have hgm : (if q = 0 then 0 else coeff (q - 1) (gser x)) =
        (if q = 0 then 0 else ((halfBinom (q - 1) : ℚ) : ℂ)) * x ^ (-(q : ℤ)) * hfun x := by
      by_cases h : q = 0
      · rw [if_pos h, if_pos h, zero_mul, zero_mul]
      · rw [if_neg h, if_neg h, coeff_gser hx0 hx1,
          show -(((q - 1 : ℕ)) : ℤ) - 1 = -(q : ℤ) by omega]
    rw [ha, hgq, hgm, zpow_add_one₀ hx0]
    exact zm_alg x w _ _ _ _ _ hx0 hw
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [coeff_gser hx0 hx1]
    ring

end Virasoro.Sphere
