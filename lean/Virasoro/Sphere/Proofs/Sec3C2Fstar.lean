import Virasoro.Sphere.Proofs.Sec3C2Lev
import Virasoro.Sphere.Proofs.Sec3BergmanLiouTools
import Virasoro.Sphere.Proofs.Sec3SaddlePsi

/-!
# Lemma 3.7, Step 3: `X = f(x;W_*)` and the change of variables (sphere paper)

sphere/paper.tex l.1128–1143.  With `t = x^{-1}` and `g = f(x;W_*)/x = exp(-∑_m W_{*,m} t^m)`:
`g = ((1+√(1-t))/2)²`, so that `X = f(x;W_*)` has the inverse `x = X + 1/2 + 1/(16X)` and
`√(x(x-1)) = X - 1/(16X)`; in the variable `t` these read
`g + t/2 + t²/(16g) = 1` and `g - t²/(16g) = √(1-t)`.  The formal residue of `f^p f'` is
`δ_{p,-1}` (`res_hS`).  The Laurent polynomials `x(X)^{k-1}(X - 1/(16X))` are combinations of
the `X^m - 16^{-m}X^{-m}`, `1 ≤ m ≤ k`, with coefficients `cst k m`, `cst k k = 1`
(`sOneC_expand`).
-/

namespace Virasoro.Sphere

open Finset PowerSeries

/-- `(1-t)^{-1/2}` with complex coefficients. -/
noncomputable def hserC : PowerSeries ℂ := hser.map (algebraMap ℚ ℂ)

theorem sOneC_sq : sOneC ^ 2 = 1 - X := by
  rw [sOneC, ← map_pow, sOne_sq]
  simp

theorem hserC_mul : hserC * sOneC = 1 := by
  rw [hserC, sOneC, ← map_mul, hser_mul_sOne, map_one]

theorem constantCoeff_sOneC : constantCoeff sOneC = 1 := by
  rw [sOneC, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_sOne, map_one]

/-- `∑_m m W_{*,m} t^m = (1-t)^{-1/2} - 1` (sphere/paper.tex l.1128). -/
theorem Hst_eq : Hst = hserC - 1 := by
  ext m
  rw [Hst, coeff_mk, map_sub, hserC, coeff_map, hser, coeff_mk, PowerSeries.coeff_one, wN]
  by_cases hm : m = 0
  · subst hm
    simp [halfBinom_zero']
  · have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    rw [if_neg hm, sub_zero, mul_div_cancel₀ _ hm']
    simp

/-- `1/4` as a constant series. -/
noncomputable def qq : PowerSeries ℂ := C (1 / 4 : ℂ)

theorem four_qq : 4 * qq = 1 := by
  rw [qq, ← map_ofNat (C (R := ℂ)) 4, ← map_mul]
  norm_num

theorem C_half : (C (1 / 2 : ℂ) : PowerSeries ℂ) = 2 * qq := by
  rw [qq, ← map_ofNat (C (R := ℂ)) 2, ← map_mul]
  norm_num

theorem C_sixteenth : (C (1 / 16 : ℂ) : PowerSeries ℂ) = qq ^ 2 := by
  rw [qq, ← map_pow]
  norm_num

theorem Est_mul_neg (c : ℂ) : Est c * Est (-c) = 1 := by
  rw [← Est_add, add_neg_cancel, Est_zero]

theorem Est_neg_one_deriv : X * derivative ℂ (Est (-1)) = -(Hst * Est (-1)) := by
  rw [Est_deriv]
  simp

/-- `exp(-∑_m W_{*,m} t^m) = ((1+√(1-t))/2)²`: the integration of l.1128–1129. -/
theorem Est_neg_one : Est (-1) = qq * (1 + sOneC) ^ 2 := by
  have e1 := sOneC_sq
  have e2 : 2 * sOneC * derivative ℂ sOneC = -1 := by
    have h := congrArg (derivative ℂ) e1
    rw [pow_two, Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have e3 : (Hst + 1) * sOneC = 1 := by
    rw [Hst_eq, sub_add_cancel, hserC_mul]
  have e4 := Est_neg_one_deriv
  have hf' : derivative ℂ (qq * (1 + sOneC) ^ 2) =
      qq * (2 * (1 + sOneC) * derivative ℂ sOneC) := by
    rw [qq, Derivation.leibniz, derivative_C, pow_two, Derivation.leibniz, map_add,
      Derivation.map_one_eq_zero]
    simp only [smul_eq_mul]
    ring
  refine eq_of_deriv_mul_eq (constantCoeff_Est _) ?_ ?_
  · rw [map_mul, map_pow, map_add, map_one, constantCoeff_sOneC, qq, constantCoeff_C]
    norm_num
  · rw [hf']
    have hsX : sOneC * X ≠ 0 := by
      refine mul_ne_zero ?_ X_ne_zero
      intro h
      have h1 := constantCoeff_sOneC
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    refine mul_left_cancel₀ hsX ?_
    linear_combination (sOneC * qq * (1 + sOneC) ^ 2) * e4 +
      (-(X * qq * (1 + sOneC) * Est (-1))) * e2 + (-(qq * (1 + sOneC) ^ 2 * Est (-1))) * e3 +
      (qq * (1 + sOneC) * Est (-1)) * e1

/-- `x = X + 1/2 + 1/(16X)` for `X = f(x;W_*)` (sphere/paper.tex l.1130), times `t`. -/
theorem xi_one : Est (-1) + 2 * qq * X + qq ^ 2 * X ^ 2 * Est 1 = 1 := by
  have hq := four_qq
  have e5 : Est (-1) * Est 1 = 1 := by
    have h := Est_mul_neg (-1)
    rwa [neg_neg] at h
  have hX : (X : PowerSeries ℂ) = 1 - sOneC ^ 2 := by
    rw [sOneC_sq]
    ring
  have h1 : Est (-1) ^ 2 + 2 * qq * X * Est (-1) + qq ^ 2 * X ^ 2 - Est (-1) = 0 := by
    rw [Est_neg_one, hX]
    linear_combination (qq * (1 + sOneC) ^ 2) * hq
  linear_combination Est 1 * h1 - (Est (-1) + 2 * qq * X - 1) * e5

/-- `√(x(x-1)) = X - 1/(16X)` for `X = f(x;W_*)` (sphere/paper.tex l.1131), times `t`. -/
theorem sOneC_eq : sOneC = Est (-1) - qq ^ 2 * X ^ 2 * Est 1 := by
  have hq := four_qq
  have e5 : Est (-1) * Est 1 = 1 := by
    have h := Est_mul_neg (-1)
    rwa [neg_neg] at h
  have hX : (X : PowerSeries ℂ) = 1 - sOneC ^ 2 := by
    rw [sOneC_sq]
    ring
  have h1 : Est (-1) * sOneC - Est (-1) ^ 2 + qq ^ 2 * X ^ 2 = 0 := by
    rw [Est_neg_one, hX]
    linear_combination (-(qq * (1 + sOneC) ^ 2 * sOneC)) * hq
  linear_combination Est 1 * h1 - (sOneC - Est (-1)) * e5

/-! ### The residue of `f^p f'` -/

/-- `f' f^{-M-1}` for `f = f(x;W_*)`, as `x^{-M-1}` times a series in `t = x^{-1}`:
`f = x g`, `f' = g - t g'` with `g' = ∂_t g`. -/
noncomputable def hS (M : ℤ) : PowerSeries ℂ :=
  Est ((M : ℂ) + 1) * (Est (-1) - X * derivative ℂ (Est (-1)))

/-- `f' f^{-M-1} = -(1/M) ∂_x f^{-M}`. -/
theorem hS_mul (M : ℤ) : C (M : ℂ) * hS M = C (M : ℂ) * Est M + X * derivative ℂ (Est M) := by
  have h1 : Est ((M : ℂ) + 1) * Est (-1) = Est M := by
    rw [← Est_add]
    congr 1
    ring
  rw [hS, Est_neg_one_deriv, Est_deriv]
  linear_combination (C (M : ℂ) * (1 + Hst)) * h1

theorem coeff_hS_mul (M : ℤ) (d : ℕ) :
    (M : ℂ) * coeff d (hS M) = ((M : ℂ) + d) * coeff d (Est M) := by
  have h := congrArg (coeff d) (hS_mul M)
  rw [coeff_C_mul, map_add, coeff_C_mul, coeff_X_mul_derivative] at h
  rw [h]
  ring

/-- The formal residue of `f^p f'` is `δ_{p,-1}` (sphere/paper.tex l.1134–1139, the change of
variables `X = f(x;W_*)`): the coefficient of `x^{-1}` in `f' f^{-M-1}` with `M = -d`. -/
theorem res_hS (d : ℕ) : coeff d (hS (-(d : ℤ))) = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, hS, coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_mul,
      constantCoeff_Est, constantCoeff_Est, constantCoeff_X]
    simp
  · rw [if_neg hd]
    have h := coeff_hS_mul (-(d : ℤ)) d
    have hd' : ((-(d : ℤ) : ℤ) : ℂ) ≠ 0 := by
      push_cast
      exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hd)
    have h0 : ((-(d : ℤ) : ℤ) : ℂ) + d = 0 := by
      push_cast
      ring
    rw [h0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hd'

theorem Est_mul_hS (c : ℤ) (M : ℤ) : Est (c : ℂ) * hS M = hS (M + c) := by
  rw [hS, hS, ← mul_assoc, ← Est_add]
  congr 2
  push_cast
  ring

/-! ### The span of `x(X)^{k-1}(X - 1/(16X))` -/

/-- `x(X)^{k-1}(X - 1/(16X)) = ∑_{m=1}^k cst k m (X^m - 16^{-m}X^{-m})`, from
`x(X)(X^m - 16^{-m}X^{-m}) = (X^{m+1} - 16^{-m-1}X^{-m-1}) + (1/2)(X^m - 16^{-m}X^{-m}) +
(1/16)(X^{m-1} - 16^{-m+1}X^{-m+1})` (sphere/paper.tex l.1140–1142). -/
noncomputable def cst : ℕ → ℕ → ℂ
  | 0, _ => 0
  | 1, m => if m = 1 then 1 else 0
  | (k + 2), m =>
    if m = 0 then 0 else cst (k + 1) (m - 1) + 1 / 2 * cst (k + 1) m + 1 / 16 * cst (k + 1) (m + 1)

theorem cst_zero_right : ∀ k : ℕ, cst k 0 = 0
  | 0 => rfl
  | 1 => by simp [cst]
  | (k + 2) => by simp [cst]

theorem cst_of_lt : ∀ k m : ℕ, k < m → cst k m = 0
  | 0, _, _ => rfl
  | 1, m, h => by
    rw [cst, if_neg (by omega)]
  | (k + 2), m, h => by
    rw [cst, if_neg (by omega), cst_of_lt (k + 1) (m - 1) (by omega), cst_of_lt (k + 1) m (by omega),
      cst_of_lt (k + 1) (m + 1) (by omega)]
    ring

theorem cst_self : ∀ k : ℕ, 1 ≤ k → cst k k = 1
  | 0, h => absurd h (by omega)
  | 1, _ => by simp [cst]
  | (k + 2), _ => by
    rw [cst, if_neg (by omega), show k + 2 - 1 = k + 1 from rfl, cst_self (k + 1) (by omega),
      cst_of_lt (k + 1) (k + 2) (by omega), cst_of_lt (k + 1) (k + 2 + 1) (by omega)]
    ring

/-- `t^K (X^m - 16^{-m} X^{-m})` at `X = f(x;W_*) = g/t`. -/
noncomputable def Dst (K m : ℕ) : PowerSeries ℂ :=
  X ^ (K - m) * Est (-(m : ℂ)) - qq ^ (2 * m) * X ^ (K + m) * Est (m : ℂ)

theorem Dst_zero (K : ℕ) : Dst K 0 = 0 := by
  simp [Dst]

theorem xi_mul_Dst (n j : ℕ) :
    Dst (n + 1 + j) (n + 1) =
      Dst (n + j + 2) (n + 2) + 2 * qq * Dst (n + j + 2) (n + 1) +
        qq ^ 2 * Dst (n + j + 2) n := by
  have r1 : Est (-1) * Est (-((n + 1 : ℕ) : ℂ)) = Est (-((n + 2 : ℕ) : ℂ)) := by
    rw [← Est_add]
    congr 1
    push_cast
    ring
  have r2 : Est 1 * Est (-((n + 1 : ℕ) : ℂ)) = Est (-(n : ℂ)) := by
    rw [← Est_add]
    congr 1
    push_cast
    ring
  have r3 : Est (-1) * Est ((n + 1 : ℕ) : ℂ) = Est (n : ℂ) := by
    rw [← Est_add]
    congr 1
    push_cast
    ring
  have r4 : Est 1 * Est ((n + 1 : ℕ) : ℂ) = Est ((n + 2 : ℕ) : ℂ) := by
    rw [← Est_add]
    congr 1
    push_cast
    ring
  have s1 : n + 1 + j - (n + 1) = j := by omega
  have s2 : n + j + 2 - (n + 2) = j := by omega
  have s3 : n + j + 2 - (n + 1) = j + 1 := by omega
  have s4 : n + j + 2 - n = j + 2 := by omega
  have hxi := xi_one
  unfold Dst
  rw [s1, s2, s3, s4]
  linear_combination (-(X ^ j * Est (-((n + 1 : ℕ) : ℂ)) -
      qq ^ (2 * (n + 1)) * X ^ (n + 1 + j + (n + 1)) * Est ((n + 1 : ℕ) : ℂ))) * hxi +
    (X ^ j) * r1 - (qq ^ (2 * n + 2) * X ^ (2 * n + 2 + j)) * r3 + (qq ^ 2 * X ^ (j + 2)) * r2 -
    (qq ^ (2 * n + 4) * X ^ (2 * n + 4 + j)) * r4

/-- `x^{k-1}√(x(x-1)) = ∑_m cst k m (X^m - 16^{-m}X^{-m})` at `X = f(x;W_*)`, times `t^k`. -/
theorem sOneC_expand : ∀ k : ℕ, 1 ≤ k →
    sOneC = ∑ m ∈ range (k + 1), C (cst k m) * Dst k m
  | 0, h => absurd h (by omega)
  | 1, _ => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      cst_zero_right, map_zero, zero_mul, zero_add, cst_self 1 le_rfl, map_one, one_mul, Dst,
      sOneC_eq]
    simp
  | (k + 2), _ => by
    have ih := sOneC_expand (k + 1) (by omega)
    have hterm : ∀ m ∈ range (k + 2), C (cst (k + 1) m) * Dst (k + 1) m =
        C (cst (k + 1) m) * Dst (k + 2) (m + 1) + 2 * qq * (C (cst (k + 1) m) * Dst (k + 2) m) +
          qq ^ 2 * (C (cst (k + 1) m) * Dst (k + 2) (m - 1)) := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [cst_zero_right]
        simp
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        obtain ⟨j, hj⟩ : ∃ j, k + 1 = n + 1 + j := ⟨k - n, by
          have := Finset.mem_range.mp hm
          omega⟩
        have h := xi_mul_Dst n j
        rw [← hj, show n + j + 2 = k + 2 by omega] at h
        rw [h, show n + 1 + 1 = n + 2 from rfl, show n + 1 - 1 = n from rfl]
        ring
    have T1 : ∑ m ∈ range (k + 2), C (cst (k + 1) m) * Dst (k + 2) (m + 1) =
        ∑ m ∈ range (k + 3), C (if m = 0 then 0 else cst (k + 1) (m - 1)) * Dst (k + 2) m := by
      rw [Finset.sum_range_succ' _ (k + 2), if_pos rfl, map_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [if_neg (by omega), Nat.add_sub_cancel]
    have T2 : ∑ m ∈ range (k + 2), C (cst (k + 1) m) * Dst (k + 2) m =
        ∑ m ∈ range (k + 3), C (cst (k + 1) m) * Dst (k + 2) m := by
      rw [Finset.sum_range_succ _ (k + 2), cst_of_lt (k + 1) (k + 2) (by omega), map_zero, zero_mul,
        add_zero]
    have T3 : ∑ m ∈ range (k + 2), C (cst (k + 1) m) * Dst (k + 2) (m - 1) =
        ∑ m ∈ range (k + 3), C (cst (k + 1) (m + 1)) * Dst (k + 2) m := by
      rw [Finset.sum_range_succ' _ (k + 1), cst_zero_right, map_zero, zero_mul, add_zero,
        Finset.sum_range_succ _ (k + 2), Finset.sum_range_succ _ (k + 1),
        cst_of_lt (k + 1) (k + 2 + 1) (by omega), cst_of_lt (k + 1) (k + 1 + 1) (by omega),
        map_zero, zero_mul, zero_mul, add_zero, add_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.add_sub_cancel]
    rw [ih, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, T1, T2, T3, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [Dst_zero]
      ring
    · rw [cst, if_neg (by omega), if_neg (by omega), map_add, map_add, map_mul, map_mul, C_half,
        C_sixteenth]
      ring

/-- The residue of `x^{k-1}√(x(x-1)) f' f^{-M-1}` (sphere/paper.tex l.1134–1143): the
coefficient of `X^M` in `x(X)^{k-1}(X - 1/(16X))`. -/
theorem rho_eq (k : ℕ) (hk : 1 ≤ k) (M : ℤ) (hM : M ≤ k) :
    coeff ((k : ℤ) - M).toNat (sOneC * hS M) = ∑ m ∈ range (k + 1), cst k m *
      ((if M = (m : ℤ) then 1 else 0) - (1 / 16 : ℂ) ^ m * (if M = -(m : ℤ) then 1 else 0)) := by
  have hq : ∀ m : ℕ, qq ^ (2 * m) = C ((1 / 16 : ℂ) ^ m) := fun m => by
    rw [qq, ← map_pow, pow_mul]
    norm_num
  rw [sOneC_expand k hk, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := by
    have := Finset.mem_range.mp hm
    omega
  have e1 : X ^ (k - m) * Est (-(m : ℂ)) * hS M = X ^ (k - m) * hS (M + (-(m : ℤ))) := by
    rw [mul_assoc, ← Est_mul_hS (-(m : ℤ)) M]
    push_cast
    rfl
  have e2 : qq ^ (2 * m) * X ^ (k + m) * Est (m : ℂ) * hS M =
      C ((1 / 16 : ℂ) ^ m) * (X ^ (k + m) * hS (M + (m : ℤ))) := by
    rw [hq, mul_assoc, mul_assoc, ← Est_mul_hS (m : ℤ) M]
    push_cast
    rfl
  rw [mul_assoc, coeff_C_mul, Dst, sub_mul, map_sub, e1, e2, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_pow_mul']
  congr 1
  have c1 : (if k - m ≤ ((k : ℤ) - M).toNat then
      coeff (((k : ℤ) - M).toNat - (k - m)) (hS (M + (-(m : ℤ)))) else 0) =
      if M = (m : ℤ) then 1 else 0 := by
    by_cases h : k - m ≤ ((k : ℤ) - M).toNat
    · rw [if_pos h]
      obtain ⟨d, hd⟩ : ∃ d : ℕ, ((k : ℤ) - M).toNat - (k - m) = d := ⟨_, rfl⟩
      have hd' : M + (-(m : ℤ)) = -(d : ℤ) := by omega
      rw [hd, hd', res_hS]
      by_cases h0 : d = 0
      · rw [if_pos h0, if_pos (by omega)]
      · rw [if_neg h0, if_neg (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have c2 : (if k + m ≤ ((k : ℤ) - M).toNat then
      coeff (((k : ℤ) - M).toNat - (k + m)) (hS (M + (m : ℤ))) else 0) =
      if M = -(m : ℤ) then 1 else 0 := by
    by_cases h : k + m ≤ ((k : ℤ) - M).toNat
    · rw [if_pos h]
      obtain ⟨d, hd⟩ : ∃ d : ℕ, ((k : ℤ) - M).toNat - (k + m) = d := ⟨_, rfl⟩
      have hd' : M + (m : ℤ) = -(d : ℤ) := by omega
      rw [hd, hd', res_hS]
      by_cases h0 : d = 0
      · rw [if_pos h0, if_pos (by omega)]
      · rw [if_neg h0, if_neg (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [c1, c2]

end Virasoro.Sphere
