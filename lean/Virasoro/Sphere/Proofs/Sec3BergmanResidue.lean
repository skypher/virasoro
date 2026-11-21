import Virasoro.Sphere.Proofs.Sec3BergmanRes1

/-!
# Sphere paper Lemma 3.5, Step 3: trace and residues (`sphere/paper.tex` l.943–966)

`Stmt_sub_bergman_residue`: from the formula of Step 2 for `W`,
`Tr(D M(z)² (I - M(z)²)⁻¹) = z/(8(z-1)) + 2C(z)/(2(z-1))`.
The contour integral of `x W_no(x,x)` over `|x| = ½` is `2πi · 2 Tr` (`circleIntegral_Wno_diag`);
by the coincidence limit (`diag_formula`) the integrand is
`(x²-z)² g(x)⁴/8 - 2C g(x)²` coefficientwise in `z`, whose integral is the sum of the residues
at `x = 0, z` at each order (`int_g2`, `int_g4`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset Real

variable {r : ℝ}

theorem continuousOn_gser_coeff (hr0 : 0 < r) (hr1 : r < 1) (n e k : ℕ) :
    ContinuousOn (fun x : ℂ => x * (x ^ e * coeff k (gser x ^ n))) (Metric.sphere (0 : ℂ) r) := by
  intro x hx
  have hx0 := sphere_ne_zero hr0 hx
  have hx1 : ‖x‖ < 1 := by rw [sphere_norm hx]; exact hr1
  exact (continuousAt_id.mul ((continuousAt_id.pow e).mul
    ((coeffCont_gser hx0 hx1).pow n k))).continuousWithinAt

theorem continuousOn_gser_coeff' (hr0 : 0 < r) (hr1 : r < 1) (n k : ℕ) :
    ContinuousOn (fun x : ℂ => x * coeff k (gser x ^ n)) (Metric.sphere (0 : ℂ) r) := by
  intro x hx
  have hx0 := sphere_ne_zero hr0 hx
  have hx1 : ‖x‖ < 1 := by rw [sphere_norm hx]; exact hr1
  exact (continuousAt_id.mul ((coeffCont_gser hx0 hx1).pow n k)).continuousWithinAt

theorem int_split (f1 f2 f3 f4 : ℂ → ℂ) (c1 c2 c3 : ℂ) (h1 : CircleIntegrable f1 0 r)
    (h2 : CircleIntegrable f2 0 r) (h3 : CircleIntegrable f3 0 r) (h4 : CircleIntegrable f4 0 r) :
    (∮ x in C(0, r), (c1 * f1 x - c2 * f2 x + c3 * f3 x - f4 x)) =
      c1 * (∮ x in C(0, r), f1 x) - c2 * (∮ x in C(0, r), f2 x) + c3 * (∮ x in C(0, r), f3 x) -
        ∮ x in C(0, r), f4 x := by
  have i1 : CircleIntegrable (fun x => c1 * f1 x) 0 r := h1.const_smul (a := c1)
  have i2 : CircleIntegrable (fun x => c2 * f2 x) 0 r := h2.const_smul (a := c2)
  have i3 : CircleIntegrable (fun x => c3 * f3 x) 0 r := h3.const_smul (a := c3)
  have i12 : CircleIntegrable (fun x => c1 * f1 x - c2 * f2 x) 0 r := i1.sub i2
  have i123 : CircleIntegrable (fun x => c1 * f1 x - c2 * f2 x + c3 * f3 x) 0 r := i12.add i3
  rw [circleIntegral.integral_sub i123 h4, circleIntegral.integral_add i12 i3,
    circleIntegral.integral_sub i1 i2, circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]

/-- `x [z^j] W_no(x,x)` from the coincidence limit, for `0 < |x| < 1`. -/
theorem mul_coeff_Wnos {Cz : PowerSeries ℂ} (hC : IsWFormula Cz) {x : ℂ} (h0 : 0 < ‖x‖)
    (h1 : ‖x‖ < 1) (j : ℕ) :
    x * coeff j (Wnos x x) =
      (1 / 8 : ℂ) * (x * (x ^ 4 * coeff j (gser x ^ 4))) -
        (if 1 ≤ j then (1 / 4 : ℂ) else 0) * (x * (x ^ 2 * coeff (j - 1) (gser x ^ 4))) +
        (if 2 ≤ j then (1 / 8 : ℂ) else 0) * (x * (x ^ 0 * coeff (j - 2) (gser x ^ 4))) -
        ∑ p ∈ antidiagonal j, (2 * coeff p.1 Cz) * (x * coeff p.2 (gser x ^ 2)) := by
  have h := diag_formula hC h0 h1
  have hq : (PowerSeries.C x * PowerSeries.C x - X) ^ 2 * gser x ^ 4 =
      PowerSeries.C (x ^ 4) * gser x ^ 4 - PowerSeries.C (2 * x ^ 2) * (X ^ 1 * gser x ^ 4) +
        X ^ 2 * gser x ^ 4 := by
    simp only [map_pow, map_mul, map_ofNat]
    ring
  have h8 : (8 : PowerSeries ℂ) = PowerSeries.C 8 := (map_ofNat _ 8).symm
  have h16 : (16 : PowerSeries ℂ) = PowerSeries.C 16 := (map_ofNat _ 16).symm
  rw [hq, h8, h16, mul_assoc] at h
  have hj := congrArg (coeff j) h
  rw [map_add, map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow_mul', coeff_mul] at hj
  have hsum : ∑ p ∈ antidiagonal j, (2 * coeff p.1 Cz) * (x * coeff p.2 (gser x ^ 2)) =
      2 * x * ∑ p ∈ antidiagonal j, coeff p.1 Cz * coeff p.2 (gser x ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  split_ifs at hj ⊢ <;> linear_combination (x / 8) * hj

/-- The coefficient of `z^j` of the trace, from the residues at `x = 0, z`. -/
theorem coeff_trace_formula {Cz : PowerSeries ℂ} (hC : IsWFormula Cz) (j : ℕ) :
    2 * ((coeff j traceDM : ℚ) : ℂ) =
      -(if 1 ≤ j then (1 / 4 : ℂ) else 0) - 2 * ∑ p ∈ antidiagonal j, coeff p.1 Cz := by
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hD := circleIntegral_Wno_diag j hr0 hr1
  have hcongr : (∮ x in C(0, (1 / 2 : ℝ)), x * ∑' mn : ℕ × ℕ, WnoTerm j x x mn.1 mn.2) =
      ∮ x in C(0, (1 / 2 : ℝ)),
        ((1 / 8 : ℂ) * (x * (x ^ 4 * coeff j (gser x ^ 4))) -
        (if 1 ≤ j then (1 / 4 : ℂ) else 0) * (x * (x ^ 2 * coeff (j - 1) (gser x ^ 4))) +
        (if 2 ≤ j then (1 / 8 : ℂ) else 0) * (x * (x ^ 0 * coeff (j - 2) (gser x ^ 4))) -
        ∑ p ∈ antidiagonal j, (2 * coeff p.1 Cz) * (x * coeff p.2 (gser x ^ 2))) := by
    refine circleIntegral.integral_congr hr0.le fun x hx => ?_
    have hx0 : 0 < ‖x‖ := by rw [sphere_norm hx]; exact hr0
    have hx1 : ‖x‖ < 1 := by rw [sphere_norm hx]; exact hr1
    have := mul_coeff_Wnos hC hx0 hx1 j
    rw [Wnos, coeff_mk] at this
    exact this
  have hi := fun (e k : ℕ) =>
    (continuousOn_gser_coeff hr0 hr1 4 e k).circleIntegrable hr0.le
  have h4 : CircleIntegrable (fun x : ℂ =>
      ∑ p ∈ antidiagonal j, (2 * coeff p.1 Cz) * (x * coeff p.2 (gser x ^ 2))) 0 (1 / 2 : ℝ) :=
    (continuousOn_finsetSum _ fun p _ =>
      continuousOn_const.mul (continuousOn_gser_coeff' hr0 hr1 2 p.2)).circleIntegrable hr0.le
  have hsumint : (∮ x in C(0, (1 / 2 : ℝ)),
      ∑ p ∈ antidiagonal j, (2 * coeff p.1 Cz) * (x * coeff p.2 (gser x ^ 2))) =
      ∑ p ∈ antidiagonal j, (2 * coeff p.1 Cz) * (2 * π * Complex.I) := by
    rw [circleIntegral.integral_fun_sum fun p _ =>
      (continuousOn_const.mul (continuousOn_gser_coeff' hr0 hr1 2 p.2)).circleIntegrable hr0.le]
    exact Finset.sum_congr rfl fun p _ => by
      rw [circleIntegral.integral_const_mul, int_g2 hr0 hr1]
  rw [hcongr, int_split _ _ _ _ _ _ _ (hi 4 j) (hi 2 (j - 1)) (hi 0 (j - 2)) h4,
    int_g4_four hr0 hr1, int_g4_two hr0 hr1, int_g4_zero hr0 hr1, hsumint, ← Finset.sum_mul,
    ← Finset.mul_sum] at hD
  have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine mul_left_cancel₀ hpi ?_
  rcases j with _ | _ | n
  · simp only [show ¬ (1 ≤ 0) by omega, show ¬ (2 ≤ 0) by omega, if_false, zero_mul, neg_zero,
      zero_add, zero_sub, sub_zero, Nat.zero_sub, Nat.cast_zero, mul_zero] at hD ⊢
    linear_combination (-1) * hD
  · simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_add, le_refl, if_true,
      show ¬ (2 ≤ 0 + 1) by omega, if_false, zero_mul, add_zero, Nat.cast_one] at hD ⊢
    linear_combination (-1) * hD
  · simp only [show 1 ≤ n + 1 + 1 by omega, show 2 ≤ n + 1 + 1 by omega, if_true,
      show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega] at hD ⊢
    push_cast at hD ⊢
    linear_combination (-1) * hD

/-- Lemma 3.5, Step 3, trace and residues (sphere/paper.tex l.943–966). -/
theorem sub_bergman_residue : Stmt_sub_bergman_residue := by
  intro Cz hC
  have hU : (PowerSeries.mk (1 : ℕ → ℂ)) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℂ
  have key : 8 * traceDM.map (algebraMap ℚ ℂ) = -((X + 8 * Cz) * PowerSeries.mk (1 : ℕ → ℂ)) := by
    ext j
    have h := coeff_trace_formula hC j
    have h8 : (8 : PowerSeries ℂ) = PowerSeries.C 8 := (map_ofNat _ 8).symm
    have hX : ∑ p ∈ antidiagonal j, coeff p.1 (X : PowerSeries ℂ) = if 1 ≤ j then 1 else 0 := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => coeff a (X : PowerSeries ℂ)) j]
      simp only [coeff_X]
      rw [Finset.sum_ite_eq' (range j.succ) 1 (fun _ => (1 : ℂ))]
      simp only [Finset.mem_range]
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [h8, coeff_C_mul, coeff_map, eq_ratCast, map_neg, coeff_mul]
    simp only [coeff_mk, Pi.one_apply, mul_one, map_add, coeff_C_mul]
    rw [Finset.sum_add_distrib, hX, ← Finset.mul_sum]
    split_ifs at h ⊢ <;> linear_combination 4 * h
  linear_combination (X - 1) * key + (X + 8 * Cz) * hU

/-- Lemma 3.5 from the cited Jacobi identity and the two remaining sub-statements of its proof
(Steps 1–2 and the zero-mode condition). -/
theorem lem_bergman_det_of_liouville_zero_mode (hJ2 : Cited_JacobiIdentities2)
    (hL : Stmt_sub_bergman_liouville) (hZ : Stmt_sub_bergman_zero_mode) :
    Stmt_lem_bergman_det :=
  lem_bergman_det_of_steps hJ2 hL hZ sub_bergman_residue

end Virasoro.Sphere
