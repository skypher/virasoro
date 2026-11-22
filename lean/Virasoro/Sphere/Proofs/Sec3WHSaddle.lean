import Virasoro.Sphere.Proofs.Sec3SaddleII
import Virasoro.Sphere.Proofs.Sec3WHIdentity

/-!
# Sphere paper Lemma 3.4(iii): the saddle-point equations from (3.6) (proof of Lemma 3.4(iii))

By part (ii), `∂_{σ_m}S^{(0)}(σ_*) = ∑_n [w^{-n}]p^{-m} (-4i(-1)^{n-1} - 4n t_{*,n})
= [w^0] p^{-m}(-4iw/(1+w) + 2i g_*(w))`.  Substituting (3.6), `g_*(w) = 1 - s(w)Ω_+(p(w))`, the
parenthesis becomes `2i s(w)(1 - Ω_+(p(w)))`, and the change of variables `p = p(w)` gives
`2i[p^m](1 - Ω_+(p)) = -2i a_m(z)`.  At order `z^K`, divided by `-2i`, with `t_{*,n} = iτ_n`:
`h_m δ_{K0} - ∑_l (B_{m,l}/l)[z^{K-l}]a_l = ∑_n [w^{-n}]p^{-m} d_n = [z^K]a_m`, where
`∑ d_n w^n = s(w)(Ω_+(p(w)) - δ_{K0})` (`Dd_eq`).  This is `coeff_aSer_WH`.

Consumer: `coeff_aSer` (`Sec3SaddleA.lean`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `(1+w)⁻¹ = ∑ (-1)^n w^n`. -/
noncomputable def altSer : PowerSeries ℚ := mk fun n => (-1 : ℚ) ^ n

theorem one_add_X_mul_altSer : (1 + X) * altSer = 1 := by
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp [altSer]
  · rw [coeff_succ_X_mul, altSer, coeff_mk, coeff_mk, pow_succ]
    simp

theorem sW_eq : sW = (1 - X) * altSer := by
  have h1 : (sW - (1 - X) * altSer) * (1 + X) = 0 := by
    linear_combination sW_mul_one_add - (1 - X) * one_add_X_mul_altSer
  have hne : (1 + X : PowerSeries ℚ) ≠ 0 := fun h => by
    have := congrArg constantCoeff h
    simp at this
  exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hne)

/-- `[w^n] s(w) = 1` for `n = 0` and `2(-1)^n` for `n ≥ 1`. -/
theorem coeff_sW (n : ℕ) : coeff n sW = if n = 0 then 1 else 2 * (-1) ^ n := by
  rw [sW_eq, sub_mul, one_mul, map_sub]
  rcases n with _ | n
  · simp [altSer]
  · rw [coeff_succ_X_mul, altSer, coeff_mk, coeff_mk, pow_succ, if_neg (Nat.succ_ne_zero n)]
    ring

/-- `d_n`, with `∑ d_n w^n = -4iw/(1+w) + 2i g_*(w)` divided by `-2i` at order `z^K`. -/
noncomputable def Dd (K : ℕ) : PowerSeries ℚ :=
  mk fun n => if n = 0 then 0 else
    2 * (-1) ^ (n - 1) * (if K = 0 then 1 else 0) + 2 * n * tauWH K n

/-- `∑ d_n w^n = s(w)(Ω_+(p(w)) - δ_{K0})`, from (3.6). -/
theorem Dd_eq (K : ℕ) :
    Dd K = sW * (OmP K - C (if K = 0 then 1 else 0)).subst pW := by
  rw [subst_sub hasSubst_pW, subst_C]
  ext n
  rw [mul_sub, map_sub, Dd, coeff_mk]
  rcases n with _ | n
  · rw [if_pos rfl, WH_identity_zero, show (MvPowerSeries.C (if K = 0 then (1 : ℚ) else 0) :
      PowerSeries ℚ) = C (if K = 0 then 1 else 0) from rfl, mul_comm, coeff_C_mul, coeff_sW,
      if_pos rfl]
    ring
  · rw [if_neg (Nat.succ_ne_zero n), WH_identity K (n + 1) (by omega),
      show (MvPowerSeries.C (if K = 0 then (1 : ℚ) else 0) : PowerSeries ℚ) =
        C (if K = 0 then 1 else 0) from rfl, mul_comm sW, coeff_C_mul, coeff_sW,
      if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
    ring

/-- `[w^0](p^{-m} D(w)) = ∑_n [w^{-n}]p^{-m} [w^n]D` for `D(0) = 0`, multiplied by `4^m w^m`. -/
theorem coeff_Pm_mul (m : ℕ) (D : PowerSeries ℚ) (hD : coeff 0 D = 0) :
    coeff m (Pm m * D) = 4 ^ m * ∑ n ∈ Icc 1 m, coeff m (psi n) * coeff n D := by
  rw [mul_comm (Pm m), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i D * coeff j (Pm m)),
    sum_range_succ', hD, zero_mul, add_zero, sum_Icc_one_eq_range, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ m := by have := mem_range.1 hk; omega
  rw [coeff_Pm, coeff_psi,
    Nat.choose_symm_of_eq_add (show 2 * m = (m - (k + 1)) + (m + (k + 1)) by omega)]
  field_simp

/-- `∑_n [w^{-n}]p^{-m} d_n = [z^K] a_m` for `m ≥ 1`: the change of variables `p = p(w)`. -/
theorem sum_psi_Dd (K m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 m, coeff m (psi n) * coeff n (Dd K) = coeff K (aSer m) := by
  have hcv := coeff_change_var (OmP K - C (if K = 0 then 1 else 0)) m
  rw [mul_assoc, ← Dd_eq, map_sub, coeff_C, if_neg (by omega), sub_zero, OmP, coeff_mk,
    coeff_Pm_mul m (Dd K) (by simp [Dd])] at hcv
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hcv

/-- The saddle-point equations at `σ_*`, coefficient by coefficient in `z`, as the paper derives
them from part (ii), (3.6) and the change of variables `p = p(w)`:
`[z^K]a_m = h_m δ_{K0} - ∑_{l=1}^K (B_{m,l}/l)[z^{K-l}]a_l`. -/
theorem coeff_aSer_WH (m K : ℕ) :
    coeff K (aSer m) = (if K = 0 then halfBinom m else 0) -
      ∑ n ∈ Icc 1 K, Bcoef m n / (n : ℚ) * coeff (K - n) (aSer n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [aSer, Nat.cast_zero, OmegaCoef_zero, PowerSeries.coeff_one,
      sum_eq_zero (fun n _ => by rw [Bcoef_zero_left, zero_div, zero_mul]), sub_zero]
    simp [halfBinom, gbinom]
  have hB : ∀ l, Bcoef m l =
      -2 * ∑ n ∈ Icc 1 m, (n : ℚ) * (coeff m (psi n) * coeff l (psi n)) := by
    intro l
    rw [Bcoef_eq_sum_psi m l m le_rfl, sum_range_succ', sum_Icc_one_eq_range]
    simp
  have halt := alt_sum_psi m hm
  rw [← sum_psi_Dd K m hm]
  have e1 : ∑ n ∈ Icc 1 m, coeff m (psi n) * coeff n (Dd K) =
      (if K = 0 then 1 else 0) * (-2 * ∑ n ∈ Icc 1 m, (-1 : ℚ) ^ n * coeff m (psi n)) +
        ∑ n ∈ Icc 1 m, 2 * n * coeff m (psi n) * tauWH K n := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn' := (mem_Icc.1 hn).1
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Dd, coeff_mk, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, pow_succ]
    push_cast
    ring
  have e2 : ∑ n ∈ Icc 1 m, 2 * n * coeff m (psi n) * tauWH K n =
      -∑ l ∈ Icc 1 K, Bcoef m l / (l : ℚ) * coeff (K - l) (aSer l) := by
    simp only [tauWH, mul_sum]
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [hB l, mul_sum, sum_div, sum_mul, ← sum_neg_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  rw [e1, e2, halt]
  split_ifs <;> ring

end Virasoro.Sphere
