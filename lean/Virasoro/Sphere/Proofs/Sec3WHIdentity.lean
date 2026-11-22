import Virasoro.Sphere.Proofs.Sec3WHSeries
import Virasoro.Sphere.Proofs.Sec3SaddleOmega

/-!
# Sphere paper Lemma 3.4(iii): the Wiener–Hopf identity (3.6) (proof of Lemma 3.4(iii))

At each order `z^K` (all statements below are the coefficients of `z^K`):
- `Ω_+(x) = ∑_{m≥0} a_m x^m` is `OmP K`, `Ω_-(x) - 1 = ∑_{m≥1} a_m (z/x)^m` has the coefficients
  `[z^{K-m}]a_m`, and `Ω = ₂F₁⁻¹ (1-x)^{-1/2} (1-z/x)^{-1/2}` reads
  `x^K Ω(x) = (∑_l c_l x^{K-l}) (1-x)^{-1/2}`, `c_l = [z^{K-l}]₂F₁⁻¹ h_l` (`laurent_OmP`);
- `H(w) = s(w) Ω(p(w)) = (₂F₁ √(1-z/p(w)))⁻¹ = ∑_l c_l p(w)^{-l}` (`H_two_ways`, multiplied by
  `4^K w^K`), even under `w ↔ w⁻¹`;
- `t_{*,n} = i τ_n` with `τ_n = ∑_m [z^{K-m}]a_m/m · [w^{-n}]p^{-m}`, and
  `s(w)(Ω_-(p(w)) - 1) = i∑ n t_{*,n}(w^n - w^{-n})` from `w∂_w p^{-m} = -m s p^{-m}`;
- comparing `[w^{-n}]H = [w^n]H` gives (3.6): `s(w) Ω_+(p(w)) = 1 - g_*(w)`, i.e.
  `[w^n](s Ω_+(p)) = 2nτ_n` for `n ≥ 1` and `δ_{K0}` for `n = 0` (`WH_identity`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `Ω_+` at order `z^K`: `∑_{m≥0} [z^K]a_m(z) x^m`. -/
noncomputable def OmP (K : ℕ) : PowerSeries ℚ := mk fun m => coeff K (aSer m)

/-- `c_l = [z^{K-l}]₂F₁⁻¹ · h_l`. -/
noncomputable def cWH (K l : ℕ) : ℚ := coeff (K - l) hyp2F1⁻¹ * halfBinom l

/-- `τ_n = [z^K] t_{*,n}/i = ∑_m [z^{K-m}]a_m/m · [w^{-n}]p(w)^{-m}`. -/
noncomputable def tauWH (K n : ℕ) : ℚ :=
  ∑ m ∈ Icc 1 K, coeff (K - m) (aSer m) / m * coeff m (psi n)

theorem coeff_OmegaCoef (e : ℤ) (K : ℕ) :
    coeff K (OmegaCoef e) = ∑ l ∈ range (K + 1),
      (if 0 ≤ e + l then halfBinom (e + l).toNat * halfBinom l else 0) *
        coeff (K - l) hyp2F1⁻¹ := by
  rw [OmegaCoef, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]

/-- `x^K Ω(x) = (∑_l c_l x^{K-l}) (1-x)^{-1/2}` at order `z^K`. -/
theorem laurent_OmP (K : ℕ) :
    X ^ K * OmP K + ∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m)) * X ^ (K - m) =
      (∑ l ∈ range (K + 1), C (cWH K l) * X ^ (K - l)) * hser := by
  ext j
  -- both sides have the coefficient `[z^K] OmegaCoef (j - K)`
  have hL : coeff j (X ^ K * OmP K + ∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m)) * X ^ (K - m)) =
      coeff K (OmegaCoef ((j : ℤ) - K)) := by
    rw [map_add, map_sum, coeff_X_pow_mul']
    simp only [coeff_C_mul, coeff_X_pow, OmP, coeff_mk, mul_ite, mul_one, mul_zero]
    by_cases hj : K ≤ j
    · rw [if_pos hj, sum_eq_zero (fun m hm => by
        have := mem_Icc.1 hm; rw [if_neg (by omega)]), add_zero, aSer,
        show (((j - K : ℕ) : ℤ)) = (j : ℤ) - K by omega]
    · rw [if_neg hj, zero_add, sum_eq_single (K - j)]
      · rw [if_pos (by omega), show (j : ℤ) - K = -((K - j : ℕ) : ℤ) by omega, OmegaCoef_neg,
          coeff_mul_X_pow', if_pos (by omega)]
      · intro m hm hmj
        have hm' := mem_Icc.1 hm
        rw [if_neg (by omega)]
      · intro h
        exact absurd (mem_Icc.2 ⟨by omega, by omega⟩) h
  rw [hL, coeff_OmegaCoef, sum_mul, map_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ K := by have := mem_range.1 hl; omega
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', cWH, hser, coeff_mk]
  by_cases hc : K - l ≤ j
  · rw [if_pos (by omega), if_pos hc, show ((j : ℤ) - K + l).toNat = j - (K - l) by omega]
    ring
  · rw [if_neg (by omega), if_neg hc]
    ring

theorem subst_sum_pW (s : Finset ℕ) (f : ℕ → PowerSeries ℚ) :
    (∑ i ∈ s, f i).subst pW = ∑ i ∈ s, (f i).subst pW := by
  rw [← coe_substAlgHom hasSubst_pW, map_sum]

theorem subst_C_mul_X_pow (a : ℚ) (k : ℕ) : (C a * X ^ k).subst pW = C a * pW ^ k := by
  rw [subst_mul hasSubst_pW, subst_pow hasSubst_pW, subst_X hasSubst_pW, subst_C]
  rfl

/-- `H(w) = s(w) Ω(p(w))` in two forms, multiplied by `4^K w^K`: from
`(₂F₁ √(1-z/p))⁻¹ = ∑_l c_l p^{-l}` and from `Ω = Ω_+ + (Ω_- - 1)`. -/
theorem H_two_ways (K : ℕ) :
    ∑ l ∈ range (K + 1), C (cWH K l * 4 ^ (K - l)) * X ^ (K - l) * Pm l =
      C ((4 : ℚ) ^ K) * X ^ K * (sW * (OmP K).subst pW) +
        ∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m) * 4 ^ (K - m)) * X ^ (K - m) * (sW * Pm m) := by
  have h := congrArg (fun f => sW * Pm K * f.subst pW) (laurent_OmP K)
  try simp only at h
  rw [subst_add hasSubst_pW, subst_mul hasSubst_pW, subst_pow hasSubst_pW, subst_X hasSubst_pW,
    subst_sum_pW, subst_mul hasSubst_pW, subst_sum_pW] at h
  simp only [subst_C_mul_X_pow] at h
  have hu := hser_subst_mul_sW
  have hL : ∑ l ∈ range (K + 1), C (cWH K l * 4 ^ (K - l)) * X ^ (K - l) * Pm l =
      sW * Pm K * ((∑ l ∈ range (K + 1), C (cWH K l) * pW ^ (K - l)) * hser.subst pW) := by
    rw [sum_mul, mul_sum]
    refine sum_congr rfl fun l hl => ?_
    have hl' : l ≤ K := by have := mem_range.1 hl; omega
    have hp := pW_pow_mul_Pm (k := K - l) (m := K) (by omega)
    rw [Nat.sub_sub_self hl'] at hp
    rw [map_mul]
    linear_combination (-C (cWH K l)) * hp - (C (cWH K l) * pW ^ (K - l) * Pm K) * hu

  have hR : sW * Pm K * (pW ^ K * (OmP K).subst pW +
      ∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m)) * pW ^ (K - m)) =
      C ((4 : ℚ) ^ K) * X ^ K * (sW * (OmP K).subst pW) +
        ∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m) * 4 ^ (K - m)) * X ^ (K - m) *
          (sW * Pm m) := by
    rw [mul_add, mul_sum]
    have h0 := pW_pow_mul_Pm (k := K) (m := K) le_rfl
    rw [Nat.sub_self, Pm_zero, mul_one] at h0
    congr 1
    · linear_combination (sW * (OmP K).subst pW) * h0
    · refine sum_congr rfl fun m hm => ?_
      have hm' := mem_Icc.1 hm
      have hp := pW_pow_mul_Pm (k := K - m) (m := K) (by omega)
      rw [Nat.sub_sub_self hm'.2] at hp
      rw [map_mul]
      linear_combination (C (coeff (K - m) (aSer m)) * sW) * hp
  rw [hL, ← h, hR]

theorem coeff_C_mul_X_pow_mul (c : ℚ) (a j : ℕ) (f : PowerSeries ℚ) :
    coeff j (C c * X ^ a * f) = if a ≤ j then c * coeff (j - a) f else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

theorem choose_add_eq_ite (l n : ℕ) :
    ((2 * l).choose (l + n) : ℚ) = if n ≤ l then ((2 * l).choose (l - n) : ℚ) else 0 := by
  split_ifs with h
  · rw [Nat.choose_symm_of_eq_add (show 2 * l = (l + n) + (l - n) by omega)]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem coeff_psi (n m : ℕ) : coeff m (psi n) = ((2 * m).choose (m + n) : ℚ) / 4 ^ m := by
  rw [psi, coeff_mk]

/-- The left side of `H_two_ways` at `w^{K+n}`. -/
theorem coeff_H_add (K n : ℕ) :
    coeff (K + n) (∑ l ∈ range (K + 1), C (cWH K l * 4 ^ (K - l)) * X ^ (K - l) * Pm l) =
      ∑ l ∈ range (K + 1), cWH K l * 4 ^ (K - l) * ((2 * l).choose (l + n) : ℚ) := by
  rw [map_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ K := by have := mem_range.1 hl; omega
  rw [coeff_C_mul_X_pow_mul, if_pos (by omega), coeff_Pm, show K + n - (K - l) = l + n by omega]

/-- The left side of `H_two_ways` at `w^{K-n}`, `n ≤ K`: the same value (evenness of `H`). -/
theorem coeff_H_sub (K n : ℕ) (hn : n ≤ K) :
    coeff (K - n) (∑ l ∈ range (K + 1), C (cWH K l * 4 ^ (K - l)) * X ^ (K - l) * Pm l) =
      ∑ l ∈ range (K + 1), cWH K l * 4 ^ (K - l) * ((2 * l).choose (l + n) : ℚ) := by
  rw [map_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ K := by have := mem_range.1 hl; omega
  rw [coeff_C_mul_X_pow_mul, coeff_Pm, choose_add_eq_ite]
  by_cases h : n ≤ l
  · rw [if_pos (by omega), if_pos h, show K - n - (K - l) = l - n by omega]
  · rw [if_neg (by omega), if_neg h, mul_zero]

/-- The `Ω_-` part of `H_two_ways` at `w^{K+n}` and `w^{K-n}`: `∓ 4^K n τ_n`
(`s p^{-m}` has the coefficients `-(j/m)[w^j]p^{-m}`, from `w∂_w p^{-m} = -m s p^{-m}`). -/
theorem coeff_Hminus_add (K n : ℕ) :
    coeff (K + n) (∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m) * 4 ^ (K - m)) * X ^ (K - m) *
      (sW * Pm m)) = -(4 ^ K * n * tauWH K n) := by
  rw [map_sum, tauWH, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_Icc.1 hm
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [coeff_C_mul_X_pow_mul, if_pos (by omega), show K + n - (K - m) = m + n by omega,
    coeff_sW_Pm hm'.1, coeff_psi]
  have h4 : (4 : ℚ) ^ K = 4 ^ (K - m) * 4 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hm'.2]
  rw [h4]
  push_cast
  field_simp
  ring

theorem coeff_Hminus_sub (K n : ℕ) (hn : n ≤ K) :
    coeff (K - n) (∑ m ∈ Icc 1 K, C (coeff (K - m) (aSer m) * 4 ^ (K - m)) * X ^ (K - m) *
      (sW * Pm m)) = 4 ^ K * n * tauWH K n := by
  rw [map_sum, tauWH, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_Icc.1 hm
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h4 : (4 : ℚ) ^ K = 4 ^ (K - m) * 4 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hm'.2]
  rw [coeff_C_mul_X_pow_mul, coeff_psi, choose_add_eq_ite]
  by_cases h : n ≤ m
  · rw [if_pos (by omega), if_pos h, show K - n - (K - m) = m - n by omega, coeff_sW_Pm hm'.1,
      h4, Nat.cast_sub h]
    field_simp
    ring
  · rw [if_neg (by omega), if_neg h]
    simp

/-- The `Ω_+` part of `H_two_ways` at `w^{K+n}` and `w^{K-n}`. -/
theorem coeff_Hplus_add (K n : ℕ) :
    coeff (K + n) (C ((4 : ℚ) ^ K) * X ^ K * (sW * (OmP K).subst pW)) =
      4 ^ K * coeff n (sW * (OmP K).subst pW) := by
  rw [coeff_C_mul_X_pow_mul, if_pos (by omega), Nat.add_sub_cancel_left]

theorem coeff_Hplus_sub (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) :
    coeff (K - n) (C ((4 : ℚ) ^ K) * X ^ K * (sW * (OmP K).subst pW)) = 0 := by
  rw [coeff_C_mul_X_pow_mul, if_neg (by omega)]

theorem tauWH_eq_zero {K n : ℕ} (hn : K < n) : tauWH K n = 0 := by
  rw [tauWH]
  refine sum_eq_zero fun m hm => ?_
  have hm' := mem_Icc.1 hm
  rw [coeff_psi, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The Wiener–Hopf identity (3.6) at order `z^K`, `n ≥ 1`: `[w^n](s Ω_+(p(w))) = 2nτ_n`, i.e.
`s(w)Ω_+(p(w)) = 1 - g_*(w)` with `g_*(w) = 2i∑ n t_{*,n} w^n`, `t_{*,n} = iτ_n`. -/
theorem WH_identity (K n : ℕ) (hn : 1 ≤ n) :
    coeff n (sW * (OmP K).subst pW) = 2 * n * tauWH K n := by
  have hadd := congrArg (coeff (K + n)) (H_two_ways K)
  rw [coeff_H_add, map_add, coeff_Hplus_add, coeff_Hminus_add] at hadd
  have h4 : (4 : ℚ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hnK : n ≤ K
  · have hsub := congrArg (coeff (K - n)) (H_two_ways K)
    rw [coeff_H_sub K n hnK, map_add, coeff_Hplus_sub K n hn hnK, coeff_Hminus_sub K n hnK,
      zero_add] at hsub
    apply mul_left_cancel₀ h4
    linear_combination hadd.symm.trans hsub
  · have hz : ∑ l ∈ range (K + 1), cWH K l * 4 ^ (K - l) * ((2 * l).choose (l + n) : ℚ) = 0 := by
      refine sum_eq_zero fun l hl => ?_
      have hl' : l ≤ K := by have := mem_range.1 hl; omega
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [hz, tauWH_eq_zero (by omega)] at hadd
    simp only [mul_zero, neg_zero, add_zero] at hadd
    rw [tauWH_eq_zero (by omega), mul_zero]
    exact (mul_eq_zero.1 hadd.symm).resolve_left h4

/-- At `n = 0`: `[w^0](s Ω_+(p(w))) = [z^K] a_0 = δ_{K0}`. -/
theorem WH_identity_zero (K : ℕ) :
    coeff 0 (sW * (OmP K).subst pW) = if K = 0 then 1 else 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_sW, one_mul,
    ← coeff_zero_eq_constantCoeff_apply, coeff_subst' hasSubst_pW, finsum_eq_single _ 0]
  · simp only [pow_zero, PowerSeries.coeff_one, if_true, smul_eq_mul, mul_one]
    rw [OmP, coeff_mk, aSer, Nat.cast_zero, OmegaCoef_zero, PowerSeries.coeff_one]
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_pW, zero_pow hd, smul_zero]

end Virasoro.Sphere
