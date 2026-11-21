import Virasoro.Sphere.Proofs.Sec3SaddleSt

/-!
# Sphere paper Lemma 3.4(iii): the recursion for `a_m(z)` (`sphere/paper.tex` l.725–728)

`a_m = ₂F₁⁻¹ ∑_l h_{m+l} h_l z^l` satisfies `a_m = h_m - ∑_{n≥1} (B_{m,n}/n) z^n a_n`,
coefficient by coefficient in `z`.

Consumer: the saddle-point claim in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset PowerSeries

/-- `∑_l h_{m+l} h_l z^l`, the numerator of `a_m(z)`. -/
noncomputable def Nser (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun l => halfBinom (m + l) * halfBinom l

theorem hyp2F1_eq : hyp2F1 = PowerSeries.mk fun n => halfBinom n ^ 2 := by
  ext n
  rw [hyp2F1, coeff_mk, coeff_mk, halfBinom_eq]

theorem hyp2F1_unit : PowerSeries.constantCoeff hyp2F1 ≠ 0 := by
  rw [constantCoeff_hyp2F1]
  exact one_ne_zero

theorem aSer_mul (m : ℕ) : aSer m * hyp2F1 = Nser m := by
  rw [aSer, OmegaCoef, mul_assoc, PowerSeries.inv_mul_cancel _ hyp2F1_unit, mul_one]
  ext l
  have h1 : (0 : ℤ) ≤ (m : ℤ) + (l : ℤ) := by positivity
  have h2 : ((m : ℤ) + (l : ℤ)).toNat = m + l := by omega
  rw [coeff_mk, Nser, coeff_mk, if_pos h1, h2]

/-- `[z^K]a_m = h_m δ_{K,0} - ∑_{n=1}^K (B_{m,n}/n) [z^{K-n}]a_n`. -/
theorem coeff_aSer (m K : ℕ) :
    coeff K (aSer m) = (if K = 0 then halfBinom m else 0) -
      ∑ n ∈ Icc 1 K, Bcoef m n / (n : ℚ) * coeff (K - n) (aSer n) := by
  set E : PowerSeries ℚ := aSer m - C (halfBinom m) +
    ∑ n ∈ Icc 1 K, C (Bcoef m n / (n : ℚ)) * (X ^ n * aSer n) with hE
  have hG : ∀ j ≤ K, coeff j (E * hyp2F1) = 0 := by
    intro j hj
    have e : E * hyp2F1 = Nser m - C (halfBinom m) * hyp2F1 +
        ∑ n ∈ Icc 1 K, C (Bcoef m n / (n : ℚ)) * (X ^ n * Nser n) := by
      rw [hE, add_mul, sub_mul, aSer_mul, sum_mul]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [mul_assoc, mul_assoc, aSer_mul]
    rw [e, map_add, map_sub, coeff_C_mul, map_sum]
    have h1 : ∀ n ∈ Icc 1 K, coeff j (C (Bcoef m n / (n : ℚ)) * (X ^ n * Nser n)) =
        if n ≤ j then Bcoef m n / (n : ℚ) * (halfBinom j * halfBinom (j - n)) else 0 := by
      intro n _
      rw [coeff_C_mul, coeff_X_pow_mul']
      split_ifs with h
      · rw [Nser, coeff_mk, show n + (j - n) = j by omega]
      · rw [mul_zero]
    rw [sum_congr rfl h1, ← sum_filter,
      show (Icc 1 K).filter (fun n => n ≤ j) = Icc 1 j from by
        ext x; simp only [mem_filter, mem_Icc]; omega]
    rw [Nser, coeff_mk, hyp2F1_eq, coeff_mk, halfBinom_add m j]
    have : ∑ n ∈ Icc 1 j, Bcoef m n / (n : ℚ) * (halfBinom j * halfBinom (j - n)) =
        halfBinom j * ∑ n ∈ Icc 1 j, Bcoef m n / (n : ℚ) * halfBinom (j - n) := by
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [this]
    ring
  obtain ⟨V, hV⟩ : X ^ (K + 1) ∣ E * hyp2F1 := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    exact hG j (by omega)
  have h0 := coeff_eq_zero_of_mul_unit (N := K) (m := K) hyp2F1_unit hV le_rfl
  rw [hE, map_add, map_sub, coeff_C, map_sum] at h0
  have h2 : ∀ n ∈ Icc 1 K, coeff K (C (Bcoef m n / (n : ℚ)) * (X ^ n * aSer n)) =
      Bcoef m n / (n : ℚ) * coeff (K - n) (aSer n) := by
    intro n hn
    rw [coeff_C_mul, coeff_X_pow_mul', if_pos (mem_Icc.1 hn).2]
  rw [sum_congr rfl h2] at h0
  linarith

end Virasoro.Sphere
