import Virasoro.Sphere.Proofs.Sec3SaddleVal

/-!
# Sphere paper Lemma 3.4(iii): `1 - g_*(±1)` by evaluating (3.6) at `w = ±1`

At each order `z^K`, (3.6) makes `s(w)Ω_+(p(w)) = 1 - g_*(w)` a polynomial in `w` (`Wpoly`), and
`H(w) = s(w)Ω(p(w)) = 1 - g_*(w) + i∑ n t_{*,n}(w^n - w^{-n})` is a Laurent polynomial.  The
paper evaluates the continued identity at `w = 1` (`p(1) = 1`) and `w = -1` (`p(-1) = ∞`), where
the sum vanishes: `1 - g_*(1) = H(1) = (₂F₁ √(1-z))⁻¹` and `1 - g_*(-1) = H(-1) = ₂F₁⁻¹`.  Here
`H_two_ways`, multiplied by `4^K w^K`, is an identity of polynomials (`Hpoly_eq`), evaluated at
`w = ±1`: `s(w)p(w)^{-m}` vanishes there, `p(1)^{-l} = 1` and `p(-1)^{-l} = δ_{l0}`.

Consumer: `gStar_one`, `gStar_neg_one` (`Sec3SaddleValC.lean`).
-/

namespace Virasoro.Sphere

open Finset

/-- `[w^n](1 - g_*(w))` at order `z^K`: `δ_{K0}` for `n = 0`, `2nτ_n` for `n ≥ 1`. -/
noncomputable def wcWH (K n : ℕ) : ℚ :=
  if n = 0 then (if K = 0 then 1 else 0) else 2 * n * tauWH K n

/-- `1 - g_*(w) = s(w)Ω_+(p(w))` at order `z^K`, a polynomial of degree `≤ K`. -/
noncomputable def Wpoly (K : ℕ) : Polynomial ℚ :=
  ∑ n ∈ range (K + 1), Polynomial.C (wcWH K n) * Polynomial.X ^ n

/-- `4^K w^K H(w) = ∑_l c_l 4^{K-l} w^{K-l}(1+w)^{2l}`. -/
noncomputable def Hpoly (K : ℕ) : Polynomial ℚ :=
  ∑ l ∈ range (K + 1), Polynomial.C (cWH K l * 4 ^ (K - l)) * Polynomial.X ^ (K - l) *
    (1 + Polynomial.X) ^ (2 * l)

/-- `4^m w^m s(w) p(w)^{-m} = (1-w)(1+w)^{2m-1}`. -/
noncomputable def Spoly (m : ℕ) : Polynomial ℚ :=
  (1 - Polynomial.X) * (1 + Polynomial.X) ^ (2 * m - 1)

theorem coe_ringHom (p : Polynomial ℚ) :
    (p : PowerSeries ℚ) = Polynomial.coeToPowerSeries.ringHom p := rfl

theorem coe_Wpoly (K : ℕ) : ((Wpoly K : Polynomial ℚ) : PowerSeries ℚ) = sW * (OmP K).subst pW := by
  ext n
  rw [Polynomial.coeff_coe, Wpoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (K + 1)) n]
  by_cases hn : n ≤ K
  · rw [if_pos (mem_range.2 (by omega)), wcWH]
    rcases n with _ | n
    · rw [if_pos rfl, WH_identity_zero]
    · rw [if_neg (Nat.succ_ne_zero n), WH_identity K (n + 1) (by omega)]
  · rw [if_neg (fun h => hn (by have := mem_range.1 h; omega)),
      WH_identity K n (by omega), tauWH_eq_zero (by omega), mul_zero]

theorem coe_Hpoly (K : ℕ) : ((Hpoly K : Polynomial ℚ) : PowerSeries ℚ) =
    ∑ l ∈ range (K + 1), PowerSeries.C (cWH K l * 4 ^ (K - l)) * PowerSeries.X ^ (K - l) * Pm l := by
  rw [coe_ringHom, Hpoly, map_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [map_mul, map_pow, map_add, map_one, ← coe_ringHom, Polynomial.coe_C,
    Polynomial.coe_X, Pm]

theorem coe_Spoly {m : ℕ} (hm : 1 ≤ m) :
    ((Spoly m : Polynomial ℚ) : PowerSeries ℚ) = sW * Pm m := by
  rw [coe_ringHom, Spoly]
  simp only [map_mul, map_pow, map_add, map_sub, map_one, ← coe_ringHom, Polynomial.coe_X]
  obtain ⟨j, hj⟩ : ∃ j, 2 * m = j + 1 := ⟨2 * m - 1, by omega⟩
  rw [Pm, hj, Nat.add_sub_cancel, pow_succ]
  linear_combination ((1 + PowerSeries.X) ^ j) * sW_mul_one_add.symm

/-- `H_two_ways` as an identity of polynomials. -/
theorem Hpoly_eq (K : ℕ) :
    Hpoly K = Polynomial.C ((4 : ℚ) ^ K) * Polynomial.X ^ K * Wpoly K +
      ∑ m ∈ Icc 1 K, Polynomial.C (PowerSeries.coeff (K - m) (aSer m) * 4 ^ (K - m)) *
        Polynomial.X ^ (K - m) * Spoly m := by
  apply Polynomial.coe_injective
  rw [coe_Hpoly, H_two_ways, coe_ringHom, map_add, map_sum, ← coe_ringHom]
  congr 1
  · rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
      Polynomial.coe_X, coe_Wpoly]
  · refine sum_congr rfl fun m hm => ?_
    rw [← coe_ringHom, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C, Polynomial.coe_X, coe_Spoly (mem_Icc.1 hm).1]

theorem eval_Wpoly (K : ℕ) (s : ℚ) :
    (Wpoly K).eval s = ∑ n ∈ range (K + 1), wcWH K n * s ^ n := by
  simp [Wpoly, Polynomial.eval_finset_sum]

/-- `H(1)`: `[z^K](1 - g_*(1)) = ∑_l c_l`. -/
theorem eval_one_Wpoly (K : ℕ) : (Wpoly K).eval 1 = ∑ l ∈ range (K + 1), cWH K l := by
  have h := congrArg (Polynomial.eval (1 : ℚ)) (Hpoly_eq K)
  simp only [Hpoly, Spoly, Polynomial.eval_add, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_sub, sub_self, zero_mul, mul_zero, sum_const_zero, add_zero, one_pow,
    mul_one] at h
  have h4 : (4 : ℚ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ h4
  rw [← h, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ K := by have := mem_range.1 hl; omega
  rw [show (1 + 1 : ℚ) ^ (2 * l) = 4 ^ l by rw [pow_mul]; norm_num,
    show (4 : ℚ) ^ K = 4 ^ (K - l) * 4 ^ l by rw [← pow_add, Nat.sub_add_cancel hl']]
  ring

/-- `H(-1)`: `[z^K](1 - g_*(-1)) = c_0`. -/
theorem eval_neg_one_Wpoly (K : ℕ) : (Wpoly K).eval (-1) = cWH K 0 := by
  have h := congrArg (Polynomial.eval (-1 : ℚ)) (Hpoly_eq K)
  simp only [Hpoly, Spoly, Polynomial.eval_add, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_sub] at h
  have hz : ∀ m ∈ Icc 1 K, PowerSeries.coeff (K - m) (aSer m) * 4 ^ (K - m) * (-1) ^ (K - m) *
      ((1 - -1) * (1 + -1) ^ (2 * m - 1)) = (0 : ℚ) := by
    intro m hm
    have := (mem_Icc.1 hm).1
    rw [show (1 + -1 : ℚ) = 0 by norm_num, zero_pow (by omega)]
    ring
  rw [sum_eq_zero hz, add_zero, sum_eq_single 0] at h
  · have hK : (4 : ℚ) ^ K * (-1) ^ K ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
    apply mul_left_cancel₀ hK
    rw [show (1 + -1 : ℚ) ^ (2 * 0) = 1 by norm_num, Nat.sub_zero, mul_one] at h
    linear_combination -h
  · intro l _ hl
    rw [show (1 + -1 : ℚ) = 0 by norm_num, zero_pow (by omega), mul_zero]
  · intro h0
    exact absurd (mem_range.2 (Nat.succ_pos K)) h0

/-- `[z^K](1 - g_*(s)) = δ_{K0} + 2∑ n τ_n s^n`, the value of `Wpoly K` at `s`. -/
theorem coeff_one_sub_gAt (s : ℚ) (K : ℕ) :
    PowerSeries.coeff K (1 - MvPowerSeries.subst sigmaStar (gAt (s : ℂ))) =
      (((Wpoly K).eval s : ℚ) : ℂ) := by
  have hord : ∀ m : ℕ+, (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ sigmaStar m :=
    fun m => by simpa using smul_sigmaStar_dvd 1 m
  rw [map_sub, gAt, coeff_subst_linSeries _ hord, eval_Wpoly, sum_range_succ', PowerSeries.coeff_one]
  have hterm : ∀ m ∈ Icc 1 K,
      (2 * Complex.I * ∑ n ∈ Icc 1 m, (n : ℂ) * (s : ℂ) ^ n * tcoef n m) *
        PowerSeries.coeff K (sigmaStar m.toPNat') =
      ∑ n ∈ Icc 1 K, -2 * (n : ℂ) * (s : ℂ) ^ n *
        (((PowerSeries.coeff (K - m) (aSer m) : ℚ) : ℂ) / (m : ℂ) *
          ((PowerSeries.coeff m (psi n) : ℚ) : ℂ)) := by
    intro m hm
    have hm' := mem_Icc.1 hm
    have hcoe : ((m.toPNat' : ℕ+) : ℕ) = m := by rw [Nat.toPNat'_coe, if_pos (by omega)]
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [coeff_sigmaStar, hcoe, if_pos hm'.2]
    have hext : ∑ n ∈ Icc 1 m, (n : ℂ) * (s : ℂ) ^ n * tcoef n m =
        ∑ n ∈ Icc 1 K, (n : ℂ) * (s : ℂ) ^ n * tcoef n m := by
      refine sum_subset (fun n hn => by
        have := mem_Icc.1 hn; exact mem_Icc.2 ⟨this.1, by omega⟩) fun n _ hn => ?_
      have : ¬ n ≤ m := fun h => hn (mem_Icc.2 ⟨by have := mem_Icc.1 ‹n ∈ Icc 1 K›; omega, h⟩)
      rw [tcoef, if_neg this, mul_zero]
    rw [hext, mul_sum, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [tcoef_eq]
    linear_combination (2 * (n : ℂ) * (s : ℂ) ^ n * ((PowerSeries.coeff m (psi n) : ℚ) : ℂ) *
      ((PowerSeries.coeff (K - m) (aSer m) : ℚ) : ℂ) * (1 / (m : ℂ))) * Complex.I_mul_I
  have hW : ∑ x ∈ range K, wcWH K (x + 1) * s ^ (x + 1) =
      ∑ n ∈ Icc 1 K, 2 * (n : ℚ) * tauWH K n * s ^ n := by
    rw [← sum_Icc_one_eq_range (fun n => wcWH K n * s ^ n) K]
    refine sum_congr rfl fun n hn => ?_
    rw [wcWH, if_neg (by have := mem_Icc.1 hn; omega)]
  have hW0 : wcWH K 0 * s ^ 0 = if K = 0 then 1 else 0 := by simp [wcWH]
  rw [sum_congr rfl hterm, sum_comm, hW, hW0]
  push_cast [tauWH]
  rw [sub_eq_add_neg, ← sum_neg_distrib, add_comm]
  congr 1
  · refine sum_congr rfl fun n _ => ?_
    rw [← sum_neg_distrib, mul_sum, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    ring
  · split_ifs <;> simp

theorem ratCast_eq_algebraMap (x : ℚ) : (x : ℂ) = algebraMap ℚ ℂ x := (eq_ratCast _ x).symm

/-- `1 - g_*(1) = H(1) = (₂F₁ √(1-z))⁻¹`. -/
theorem one_sub_gAt_one_WH :
    1 - MvPowerSeries.subst sigmaStar (gAt 1) = (hyp2F1⁻¹ * hser).map (algebraMap ℚ ℂ) := by
  ext K
  have h := coeff_one_sub_gAt 1 K
  rw [Rat.cast_one] at h
  rw [h, eval_one_Wpoly, PowerSeries.coeff_map, mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i hser * PowerSeries.coeff j hyp2F1⁻¹) K,
    ratCast_eq_algebraMap]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [cWH, hser, PowerSeries.coeff_mk, mul_comm]

/-- `1 - g_*(-1) = H(-1) = ₂F₁⁻¹`. -/
theorem one_sub_gAt_neg_one_WH :
    1 - MvPowerSeries.subst sigmaStar (gAt (-1)) = (hyp2F1⁻¹).map (algebraMap ℚ ℂ) := by
  ext K
  have h := coeff_one_sub_gAt (-1) K
  rw [Rat.cast_neg, Rat.cast_one] at h
  rw [h, eval_neg_one_Wpoly, PowerSeries.coeff_map, cWH, Nat.sub_zero, ratCast_eq_algebraMap]
  congr 1
  simp [halfBinom, gbinom]

end Virasoro.Sphere
