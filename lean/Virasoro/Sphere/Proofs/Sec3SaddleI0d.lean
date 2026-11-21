import Virasoro.Sphere.Proofs.Sec3SaddleI0c

/-!
# Sphere paper Lemma 3.4(iii): `1 + 2∑_m a_m² z^m = [x⁰]Ω² = 1/((1-z)₂F₁²)`
(`sphere/paper.tex` l.802–803)

`₂F₁² (1 + 2∑_{m≥1} z^m a_m²) = N_0² + 2∑_{m≥1} z^m N_m²` with `N_m = ∑_l h_{m+l} h_l z^l`, and
its coefficient of `z^j` is `∑_{i,i'} h_i h_{j-i} h_{i'} h_{j-i'} = 1`: the coefficient of
`x⁰ z^j` in `((1-x)(1-z/x))⁻¹`, sorted by `m = |i - i'|`.

Consumer: `Sec3SaddleI0e.lean` (the value `𝓘₀ = log(16q/z)` in part (iii) of
`Stmt_lem_saddle`).
-/

namespace Virasoro.Sphere

open Finset PowerSeries

theorem sum_sq_triangular (n : ℕ) (f : ℕ → ℕ → ℚ) (hf : ∀ i j, f i j = f j i) :
    ∑ i ∈ range n, ∑ i' ∈ range n, f i i' =
      ∑ i ∈ range n, f i i + 2 * ∑ i ∈ range n, ∑ i' ∈ range i, f i i' := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ i ∈ range n, ∑ i' ∈ range (n + 1), f i i' =
        ∑ i ∈ range n, ∑ i' ∈ range n, f i i' + ∑ i ∈ range n, f i n := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => sum_range_succ _ _
    have h2 : ∑ i ∈ range n, f i n = ∑ i' ∈ range n, f n i' := sum_congr rfl fun i _ => hf i n
    rw [sum_range_succ, h1, sum_range_succ (fun i' => f n i'), ih, h2,
      sum_range_succ (fun i => f i i), sum_range_succ (fun i => ∑ i' ∈ range i, f i i')]
    ring

theorem sum_tri_reindex (j : ℕ) (g : ℕ → ℕ → ℚ) :
    ∑ i ∈ range (j + 1), ∑ i' ∈ range i, g i i' =
      ∑ m ∈ Icc 1 j, ∑ l ∈ range (j - m + 1), g (m + l) l := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.1 - x.2, x.2⟩) (fun y => ⟨y.1 + y.2, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_range, mem_Icc] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_range, mem_Icc] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_range, mem_Icc] at h
    show (⟨a - b + b, b⟩ : (_ : ℕ) × ℕ) = ⟨a, b⟩
    rw [Nat.sub_add_cancel (by omega)]
  · rintro ⟨a, b⟩ h
    show (⟨a + b - b, b⟩ : (_ : ℕ) × ℕ) = ⟨a, b⟩
    rw [Nat.add_sub_cancel]
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_range, mem_Icc] at h
    show g a b = g (a - b + b) b
    rw [Nat.sub_add_cancel (by omega)]

/-- `[z^j](N_0² + 2∑_{m≥1} z^m N_m²) = 1`. -/
theorem sum_Nser_sq (j : ℕ) :
    coeff j (hyp2F1 * hyp2F1) + 2 * ∑ m ∈ Icc 1 j, coeff (j - m) (Nser m * Nser m) = 1 := by
  set f : ℕ → ℕ → ℚ := fun i i' =>
    halfBinom i * halfBinom (j - i) * (halfBinom i' * halfBinom (j - i')) with hf
  have hsym : ∀ a b, f a b = f b a := fun a b => by
    simp only [hf]
    ring
  have h1 : ∑ i ∈ range (j + 1), ∑ i' ∈ range (j + 1), f i i' = 1 := by
    have h := sum_halfBinom_mul j
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => halfBinom a * halfBinom b) j]
      at h
    calc ∑ i ∈ range (j + 1), ∑ i' ∈ range (j + 1), f i i'
        = (∑ i ∈ range (j + 1), halfBinom i * halfBinom (j - i)) *
            ∑ i' ∈ range (j + 1), halfBinom i' * halfBinom (j - i') := by
          rw [sum_mul_sum]
      _ = 1 := by rw [h, mul_one]
  rw [sum_sq_triangular _ f hsym, sum_tri_reindex] at h1
  have hF : coeff j (hyp2F1 * hyp2F1) = ∑ i ∈ range (j + 1), f i i := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a hyp2F1 * coeff b hyp2F1) j]
    refine sum_congr rfl fun i _ => ?_
    rw [hyp2F1_eq, coeff_mk, coeff_mk]
    simp only [hf]
    ring
  have hN : ∀ m ∈ Icc 1 j, coeff (j - m) (Nser m * Nser m) =
      ∑ l ∈ range (j - m + 1), f (m + l) l := by
    intro m hm
    have hm1 := mem_Icc.1 hm
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a (Nser m) * coeff b (Nser m)) (j - m)]
    refine sum_congr rfl fun l hl => ?_
    have hl' := mem_range.1 hl
    simp only [Nser, coeff_mk, hf]
    rw [show j - (m + l) = j - m - l by omega, show m + (j - m - l) = j - l by omega]
    ring
  rw [hF, sum_congr rfl hN]
  exact h1

theorem F_sq_unit : PowerSeries.constantCoeff ((1 - X) * hyp2F1 ^ 2 : PowerSeries ℚ) ≠ 0 := by
  rw [map_mul, map_sub, map_one, constantCoeff_X, map_pow, constantCoeff_hyp2F1]
  norm_num

/-- `2∑_{m≤K} [z^K](z^m a_m²) = [z^K](1/((1-z)₂F₁²) - 1)`. -/
theorem coeff_inv_F (K : ℕ) :
    2 * ∑ m ∈ Icc 1 K, coeff K (X ^ m * (aSer m * aSer m)) =
      coeff K (((1 - X) * hyp2F1 ^ 2)⁻¹ - 1) := by
  set G : PowerSeries ℚ := 1 + C 2 * ∑ m ∈ Icc 1 K, X ^ m * (aSer m * aSer m) with hG
  have hM : ∀ j ≤ K, coeff j (G * hyp2F1 ^ 2) = 1 := by
    intro j hj
    have e : G * hyp2F1 ^ 2 = hyp2F1 * hyp2F1 +
        C 2 * ∑ m ∈ Icc 1 K, X ^ m * (Nser m * Nser m) := by
      rw [hG, add_mul, one_mul, mul_assoc, sum_mul, sq]
      congr 2
      refine sum_congr rfl fun m _ => ?_
      rw [← aSer_mul m]
      ring
    rw [e, map_add, coeff_C_mul, map_sum]
    have h1 : ∀ m ∈ Icc 1 K, coeff j (X ^ m * (Nser m * Nser m)) =
        if m ≤ j then coeff (j - m) (Nser m * Nser m) else 0 := fun m _ => by
      rw [coeff_X_pow_mul']
    rw [sum_congr rfl h1, ← sum_filter,
      show (Icc 1 K).filter (fun m => m ≤ j) = Icc 1 j from by
        ext x; simp only [mem_filter, mem_Icc]; omega]
    exact sum_Nser_sq j
  have hdvd : X ^ (K + 1) ∣ (G - ((1 - X) * hyp2F1 ^ 2)⁻¹) * ((1 - X) * hyp2F1 ^ 2) := by
    rw [sub_mul, PowerSeries.inv_mul_cancel _ F_sq_unit, PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [show G * ((1 - X) * hyp2F1 ^ 2) = G * hyp2F1 ^ 2 - X * (G * hyp2F1 ^ 2) by ring,
      map_sub, map_sub, PowerSeries.coeff_one]
    cases j with
    | zero =>
      rw [hM 0 (by omega), coeff_zero_X_mul]
      simp
    | succ i =>
      rw [hM (i + 1) (by omega), coeff_succ_X_mul, hM i (by omega), if_neg (by omega)]
      ring
  obtain ⟨V, hV⟩ := hdvd
  have h0 := coeff_eq_zero_of_mul_unit F_sq_unit hV le_rfl
  rw [map_sub, hG, map_add, coeff_C_mul, map_sum, PowerSeries.coeff_one] at h0
  rw [map_sub, PowerSeries.coeff_one]
  linarith

/-- The saddle value over `ℚ`: the coefficient of `z^k` is that of `PhiK k`. -/
noncomputable def I0Q : PowerSeries ℚ := PowerSeries.mk fun k => coeff k (PhiK k)

/-- `z dI₀/dz = 1/((1-z)₂F₁²) - 1`. -/
theorem X_mul_deriv_I0Q : X * derivative ℚ I0Q = ((1 - X) * hyp2F1 ^ 2)⁻¹ - 1 := by
  ext k
  rw [← theta_apply, coeff_theta, I0Q, coeff_mk, coeff_theta_PhiK, coeff_inv_F]

theorem constantCoeff_I0Q : PowerSeries.constantCoeff I0Q = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, I0Q, coeff_mk, PhiK]
  simp

end Virasoro.Sphere
