import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Proposition 6.8(iii) of `paper.tex` at 70bac53: the `ℓ`-adic estimates behind (6.4)
(l.1392–1416)

A polynomial `c(M)` of degree `D ≤ 2n` with `ℓ`-integral values at all `M ≥ 0` is
`∑_{u ≤ D} β_u binom(M,u)` with `ℓ`-integral `β_u`; `(M₁-M₂) ∣ u!(binom(M₁,u) - binom(M₂,u))`
and Legendre's formula `v_ℓ(u!) ≤ (u-1)/(ℓ-1)` give
`v_ℓ(c(M₁) - c(M₂)) ≥ v_ℓ(M₁-M₂) - (n-1)` for `ℓ ≥ 3` (l.1393–1401).  Summing the terms
`(c_{i,j}(M₁) - c_{i,j}(M₂)) t₀^i Y₁^j` with `i + j ≥ 1` and adding the variation in `Y` gives
the Lipschitz bound for the normalized values (l.1401–1413).
-/

namespace Virasoro

open Polynomial Finset

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem pnorm_sum_le {α : Type*} (s : Finset α) (F : α → ℚ_[ℓ]) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ s, ‖F i‖ ≤ c) : ‖∑ i ∈ s, F i‖ ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (Padic.nonarchimedean _ _).trans
      (max_le (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))

theorem pnorm_nat_eq_one {w : ℕ} (hw : ¬ ℓ ∣ w) : ‖(w : ℚ_[ℓ])‖ = 1 := by
  have h1 : (w : ℚ_[ℓ]) = ((w : ℚ) : ℚ_[ℓ]) := by norm_cast
  rw [h1, Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff (p := ℓ) w).2 hw, Rat.cast_one]

theorem pnorm_rat_le_one {q : ℚ} (hq : padicNorm ℓ q ≤ 1) : ‖(q : ℚ_[ℓ])‖ ≤ 1 := by
  rw [Padic.eq_padicNorm]
  exact_mod_cast hq

theorem rinv_nonneg : (0 : ℝ) ≤ (ℓ : ℝ)⁻¹ := by positivity

theorem rinv_le_one : (ℓ : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_le)

theorem rinv_lt_one : (ℓ : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt)

theorem zpow_neg_eq (k : ℕ) : (ℓ : ℝ) ^ (-(k : ℤ)) = ((ℓ : ℝ)⁻¹) ^ k := by
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- `(M₁-M₂) ∣ u!(binom(M₁,u) - binom(M₂,u))` and `v_ℓ(u!) ≤ n - 1` for `u ≤ 2n`, `ℓ ≥ 3`
(paper.tex l.1397–1401). -/
theorem choose_diff_bound (hℓ2 : ℓ ≠ 2) {n u : ℕ} (hu : u ≤ 2 * n) (hn : 1 ≤ n) (M₁ M₂ : ℕ) :
    ‖((M₁.choose u : ℚ_[ℓ]) - (M₂.choose u : ℚ_[ℓ]))‖ * ((ℓ : ℝ)⁻¹) ^ (n - 1) ≤
      ‖(((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ])‖ := by
  have hprime := (Fact.out : ℓ.Prime)
  obtain ⟨v, w, hw, huw⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero u) ℓ hprime.ne_one
  have hv : v ≤ n - 1 := by
    have h1 : ℓ ^ v ∣ u.factorial := ⟨w, huw⟩
    have h2 := (padicValNat_dvd_iff_le (p := ℓ) (Nat.factorial_ne_zero u)).1 h1
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · have h3 : padicValNat ℓ (Nat.factorial 0) = 0 := by simp
      omega
    · have h3 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := ℓ) hupos.ne'
      have h4 : 2 ≤ ℓ - 1 := by
        have := hprime.two_le
        omega
      have h5 : 2 * padicValNat ℓ u.factorial ≤ (ℓ - 1) * padicValNat ℓ u.factorial :=
        Nat.mul_le_mul_right _ h4
      omega
  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (M₁ : ℤ) (M₂ : ℤ) (descPochhammer ℤ u)
  rw [descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose, huw]
    at hq
  have hK : (ℓ : ℚ_[ℓ]) ^ v * (w : ℚ_[ℓ]) *
      ((M₁.choose u : ℚ_[ℓ]) - (M₂.choose u : ℚ_[ℓ])) =
      (((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ]) * (q : ℚ_[ℓ]) := by
    have := congrArg (fun z : ℤ => (z : ℚ_[ℓ])) hq
    push_cast at this ⊢
    linear_combination this
  have hnorm := congrArg norm hK
  rw [norm_mul, norm_mul, norm_mul, Padic.norm_p_pow, pnorm_nat_eq_one ℓ hw, mul_one,
    zpow_neg_eq] at hnorm
  calc ‖((M₁.choose u : ℚ_[ℓ]) - (M₂.choose u : ℚ_[ℓ]))‖ * ((ℓ : ℝ)⁻¹) ^ (n - 1)
      ≤ ‖((M₁.choose u : ℚ_[ℓ]) - (M₂.choose u : ℚ_[ℓ]))‖ * ((ℓ : ℝ)⁻¹) ^ v :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (rinv_nonneg ℓ) (rinv_le_one ℓ) hv) (norm_nonneg _)
    _ = ‖(((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ])‖ * ‖(q : ℚ_[ℓ])‖ := by rw [mul_comm]; exact hnorm
    _ ≤ ‖(((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ])‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (Padic.norm_int_le_one q)

/-- A polynomial of degree at most `2n` with `ℓ`-integral values on `ℕ` satisfies
`v_ℓ(c(M₁) - c(M₂)) ≥ v_ℓ(M₁-M₂) - (n-1)` (paper.tex l.1393–1401). -/
theorem poly_diff_bound (hℓ2 : ℓ ≠ 2) (f : ℚ[X]) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : f.natDegree ≤ 2 * n) (hint : ∀ M : ℕ, ‖((f.eval (M : ℚ) : ℚ) : ℚ_[ℓ])‖ ≤ 1)
    (M₁ M₂ : ℕ) :
    ‖((f.eval (M₁ : ℚ) : ℚ) : ℚ_[ℓ]) - ((f.eval (M₂ : ℚ) : ℚ) : ℚ_[ℓ])‖ *
        ((ℓ : ℝ)⁻¹) ^ (n - 1) ≤ ‖(((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ])‖ := by
  obtain ⟨F, hF⟩ : ∃ F : ℚ_[ℓ][X], F = f.map (algebraMap ℚ ℚ_[ℓ]) := ⟨_, rfl⟩
  have hG : ∀ M : ℕ, F.eval (M : ℚ_[ℓ]) = ((f.eval (M : ℚ) : ℚ) : ℚ_[ℓ]) := by
    intro M
    have h1 : (M : ℚ_[ℓ]) = algebraMap ℚ ℚ_[ℓ] (M : ℚ) := by simp
    rw [hF, eval_map, h1, eval₂_at_apply]
    rfl
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ_[ℓ], β = fun u => (fwdDiff (1 : ℚ_[ℓ]))^[u] F.eval 0 := ⟨_, rfl⟩
  have hβ0 : ∀ u, 2 * n < u → β u = 0 := by
    intro u hu
    have hdF : F.natDegree < u := by
      rw [hF]
      exact lt_of_le_of_lt (natDegree_map_le.trans hdeg) hu
    rw [hβ]
    exact congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdF) 0
  have hβ1 : ∀ u, ‖β u‖ ≤ 1 := by
    intro u
    rw [hβ]
    show ‖(fwdDiff (1 : ℚ_[ℓ]))^[u] F.eval 0‖ ≤ 1
    rw [fwdDiff_iter_eq_sum_shift]
    refine pnorm_sum_le ℓ _ _ zero_le_one fun k _ => ?_
    rw [zsmul_eq_mul, norm_mul]
    have h1 := Padic.norm_int_le_one (p := ℓ) ((-1) ^ (u - k) * (u.choose k : ℤ))
    have h2 : ‖F.eval ((0 : ℚ_[ℓ]) + k • (1 : ℚ_[ℓ]))‖ ≤ 1 := by
      have h3 : (0 : ℚ_[ℓ]) + k • (1 : ℚ_[ℓ]) = (k : ℚ_[ℓ]) := by simp
      rw [h3, hG]
      exact hint k
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  have hexp : ∀ M : ℕ, F.eval (M : ℚ_[ℓ]) =
      ∑ u ∈ range (2 * n + 1), (M.choose u : ℚ_[ℓ]) * β u := by
    intro M
    have h1 := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ_[ℓ])) F.eval M 0
    have h2 : (0 : ℚ_[ℓ]) + M • (1 : ℚ_[ℓ]) = (M : ℚ_[ℓ]) := by simp
    rw [h2] at h1
    have hA : ∑ k ∈ range (M + 1), M.choose k • (fwdDiff (1 : ℚ_[ℓ]))^[k] F.eval 0 =
        ∑ k ∈ range (M + 1), (M.choose k : ℚ_[ℓ]) * β k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [nsmul_eq_mul, hβ]
    have hB : ∑ k ∈ range (M + 1), (M.choose k : ℚ_[ℓ]) * β k =
        ∑ k ∈ range (max (M + 1) (2 * n + 1)), (M.choose k : ℚ_[ℓ]) * β k := by
      refine Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun k _ hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    have hC : ∑ k ∈ range (2 * n + 1), (M.choose k : ℚ_[ℓ]) * β k =
        ∑ k ∈ range (max (M + 1) (2 * n + 1)), (M.choose k : ℚ_[ℓ]) * β k := by
      refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun k _ hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      rw [hβ0 k (by omega), mul_zero]
    rw [h1, hA, hB, ← hC]
  rw [← hG, ← hG, hexp, hexp, ← Finset.sum_sub_distrib]
  have hr : 0 < ((ℓ : ℝ)⁻¹) ^ (n - 1) := by
    have : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    positivity
  rw [← le_div_iff₀ hr]
  refine pnorm_sum_le ℓ _ _ (div_nonneg (norm_nonneg _) hr.le) fun u hu => ?_
  rw [le_div_iff₀ hr, ← sub_mul, norm_mul]
  have h1 := choose_diff_bound ℓ hℓ2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)) hn M₁ M₂
  have h2 : ‖((M₁.choose u : ℚ_[ℓ]) - (M₂.choose u : ℚ_[ℓ]))‖ * ‖β u‖ ≤
      ‖((M₁.choose u : ℚ_[ℓ]) - (M₂.choose u : ℚ_[ℓ]))‖ :=
    mul_le_of_le_one_right (norm_nonneg _) (hβ1 u)
  exact (mul_le_mul_of_nonneg_right h2 hr.le).trans h1

/-! ### The normalized values -/

variable {ℓ}

/-- `∑_{d ∈ S} c_d t₀^{d₀} Y^{d₁}`. -/
noncomputable def nS (S : Finset (Fin 2 →₀ ℕ)) (c : (Fin 2 →₀ ℕ) → ℚ) (t₀ Y : ℚ_[ℓ]) : ℚ_[ℓ] :=
  ∑ d ∈ S, (c d : ℚ_[ℓ]) * (t₀ ^ d 0 * Y ^ d 1)

theorem deg_pos_of_ne {d : Fin 2 →₀ ℕ} (hd : d ≠ 0) : 1 ≤ d 0 + d 1 := by
  by_contra h
  apply hd
  ext i
  fin_cases i
  · show d 0 = 0
    omega
  · show d 1 = 0
    omega

/-- The normalized value is an `ℓ`-adic unit (paper.tex l.1413–1414). -/
theorem nS_unit (S : Finset (Fin 2 →₀ ℕ)) (c : (Fin 2 →₀ ℕ) → ℚ) (h0 : (0 : Fin 2 →₀ ℕ) ∈ S)
    (hc0 : c 0 = 1) (hc1 : ∀ d, ‖(c d : ℚ_[ℓ])‖ ≤ 1) {t₀ Y : ℚ_[ℓ]} (ht : ‖t₀‖ ≤ (ℓ : ℝ)⁻¹)
    (hY : ‖Y‖ ≤ (ℓ : ℝ)⁻¹) : ‖nS S c t₀ Y‖ = 1 := by
  have hrest : ‖∑ d ∈ S.erase 0, (c d : ℚ_[ℓ]) * (t₀ ^ d 0 * Y ^ d 1)‖ ≤ (ℓ : ℝ)⁻¹ := by
    refine pnorm_sum_le ℓ _ _ (rinv_nonneg ℓ) fun d hd => ?_
    have hne : d ≠ 0 := (Finset.mem_erase.1 hd).1
    have hdeg := deg_pos_of_ne hne
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖t₀‖ ^ d 0 * ‖Y‖ ^ d 1 ≤ ((ℓ : ℝ)⁻¹) ^ d 0 * ((ℓ : ℝ)⁻¹) ^ d 1 :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht _) (pow_le_pow_left₀ (norm_nonneg _) hY _)
        (pow_nonneg (norm_nonneg _) _) (pow_nonneg (rinv_nonneg ℓ) _)
    have h2 : ((ℓ : ℝ)⁻¹) ^ d 0 * ((ℓ : ℝ)⁻¹) ^ d 1 ≤ (ℓ : ℝ)⁻¹ := by
      rw [← pow_add]
      calc ((ℓ : ℝ)⁻¹) ^ (d 0 + d 1) ≤ ((ℓ : ℝ)⁻¹) ^ 1 :=
            pow_le_pow_of_le_one (rinv_nonneg ℓ) (rinv_le_one ℓ) hdeg
        _ = (ℓ : ℝ)⁻¹ := pow_one _
    calc ‖(c d : ℚ_[ℓ])‖ * (‖t₀‖ ^ d 0 * ‖Y‖ ^ d 1) ≤ 1 * (‖t₀‖ ^ d 0 * ‖Y‖ ^ d 1) :=
          mul_le_mul_of_nonneg_right (hc1 d)
            (mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))
      _ = ‖t₀‖ ^ d 0 * ‖Y‖ ^ d 1 := one_mul _
      _ ≤ (ℓ : ℝ)⁻¹ := h1.trans h2
  have hfirst : (c 0 : ℚ_[ℓ]) * (t₀ ^ (0 : Fin 2 →₀ ℕ) 0 * Y ^ (0 : Fin 2 →₀ ℕ) 1) = 1 := by
    simp [hc0]
  rw [nS, ← Finset.add_sum_erase _ _ h0, hfirst]
  have hlt : ‖∑ d ∈ S.erase 0, (c d : ℚ_[ℓ]) * (t₀ ^ d 0 * Y ^ d 1)‖ < 1 :=
    lt_of_le_of_lt hrest (rinv_lt_one ℓ)
  rw [Padic.add_eq_max_of_ne (by rw [norm_one]; exact hlt.ne'), norm_one]
  exact max_eq_left hlt.le

theorem pow_sub_pow_norm_le {Y₁ Y₂ : ℚ_[ℓ]} (h1 : ‖Y₁‖ ≤ 1) (h2 : ‖Y₂‖ ≤ 1) (k : ℕ) :
    ‖Y₁ ^ k - Y₂ ^ k‖ ≤ ‖Y₁ - Y₂‖ := by
  rw [← (Commute.all Y₁ Y₂).geom_sum₂_mul k, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) (pnorm_sum_le ℓ _ _ zero_le_one fun i _ => ?_)
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) h1) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) h2)

/-- The Lipschitz bound for the normalized values (paper.tex l.1393–1413). -/
theorem nS_lip (hℓ2 : ℓ ≠ 2) (S : Finset (Fin 2 →₀ ℕ)) (c : (Fin 2 →₀ ℕ) → ℕ → ℚ)
    (hc0 : ∀ M, c 0 M = 1) (hc1 : ∀ d M, ‖(c d M : ℚ_[ℓ])‖ ≤ 1)
    (hcf : ∀ d : Fin 2 →₀ ℕ, ∃ f : ℚ[X], f.natDegree ≤ 2 * (d 0 + d 1) ∧
      ∀ M : ℕ, c d M = f.eval (M : ℚ))
    {a e : ℕ} (ha : 1 ≤ a) {t₀ Y₁ Y₂ : ℚ_[ℓ]} (ht : ‖t₀‖ ≤ ((ℓ : ℝ)⁻¹) ^ a)
    (hY₁ : ‖Y₁‖ ≤ ((ℓ : ℝ)⁻¹) ^ (a + 1)) (hY₂ : ‖Y₂‖ ≤ ((ℓ : ℝ)⁻¹) ^ (a + 1)) (M₁ M₂ : ℕ)
    (hM : ‖(((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ])‖ ≤ ((ℓ : ℝ)⁻¹) ^ e)
    (hYY : ‖Y₁ - Y₂‖ ≤ ((ℓ : ℝ)⁻¹) ^ (e + a)) :
    ‖nS S (fun d => c d M₁) t₀ Y₁ - nS S (fun d => c d M₂) t₀ Y₂‖ ≤ ((ℓ : ℝ)⁻¹) ^ (e + a) := by
  have hr0 := rinv_nonneg ℓ
  have hr1 := rinv_le_one ℓ
  have hpow : ∀ k : ℕ, ((ℓ : ℝ)⁻¹) ^ k ≤ 1 := fun k => pow_le_one₀ hr0 hr1
  have ht1 : ‖t₀‖ ≤ 1 := ht.trans (hpow a)
  have hY₁1 : ‖Y₁‖ ≤ 1 := hY₁.trans (hpow _)
  have hY₂1 : ‖Y₂‖ ≤ 1 := hY₂.trans (hpow _)
  have hsplit : nS S (fun d => c d M₁) t₀ Y₁ - nS S (fun d => c d M₂) t₀ Y₂ =
      (nS S (fun d => c d M₁) t₀ Y₁ - nS S (fun d => c d M₂) t₀ Y₁) +
        (nS S (fun d => c d M₂) t₀ Y₁ - nS S (fun d => c d M₂) t₀ Y₂) := by ring
  rw [hsplit]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · -- variation in `M`
    rw [nS, nS, ← Finset.sum_sub_distrib]
    refine pnorm_sum_le ℓ _ _ (pow_nonneg hr0 _) fun d _ => ?_
    rw [← sub_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    by_cases hd : d = 0
    · rw [hd, hc0, hc0, sub_self, norm_zero, zero_mul]
      exact pow_nonneg hr0 _
    · have hn := deg_pos_of_ne hd
      obtain ⟨f, hdeg, hf⟩ := hcf d
      have hint : ∀ M : ℕ, ‖((f.eval (M : ℚ) : ℚ) : ℚ_[ℓ])‖ ≤ 1 := fun M => by
        rw [← hf]
        exact hc1 d M
      have hΔ := poly_diff_bound ℓ hℓ2 f hn hdeg hint M₁ M₂
      rw [← hf, ← hf] at hΔ
      have hexp : (d 0 + d 1 - 1) + a ≤ a * d 0 + (a + 1) * d 1 := by
        rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
        · rw [h1] at hn ⊢
          have : a * d 0 ≥ d 0 + a - 1 := by
            have h2 : (a - 1) * (d 0 - 1) + (d 0 + a - 1) = a * d 0 := by
              obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
              obtain ⟨k, hk⟩ : ∃ k, d 0 = k + 1 := ⟨d 0 - 1, by omega⟩
              rw [hk]
              simp only [Nat.add_sub_cancel]
              ring_nf
              omega
            omega
          omega
        · have h2 : d 0 ≤ a * d 0 := Nat.le_mul_of_pos_left _ (by omega)
          have h3 : a ≤ a * d 1 := Nat.le_mul_of_pos_right _ h1
          have h4 : (a + 1) * d 1 = a * d 1 + d 1 := by ring
          omega
      have hty : ‖t₀‖ ^ d 0 * ‖Y₁‖ ^ d 1 ≤ ((ℓ : ℝ)⁻¹) ^ (d 0 + d 1 - 1) * ((ℓ : ℝ)⁻¹) ^ a := by
        calc ‖t₀‖ ^ d 0 * ‖Y₁‖ ^ d 1
            ≤ (((ℓ : ℝ)⁻¹) ^ a) ^ d 0 * (((ℓ : ℝ)⁻¹) ^ (a + 1)) ^ d 1 :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht _)
                (pow_le_pow_left₀ (norm_nonneg _) hY₁ _) (pow_nonneg (norm_nonneg _) _)
                (pow_nonneg (pow_nonneg hr0 _) _)
          _ = ((ℓ : ℝ)⁻¹) ^ (a * d 0 + (a + 1) * d 1) := by
              rw [← pow_mul, ← pow_mul, ← pow_add]
          _ ≤ ((ℓ : ℝ)⁻¹) ^ ((d 0 + d 1 - 1) + a) := pow_le_pow_of_le_one hr0 hr1 hexp
          _ = ((ℓ : ℝ)⁻¹) ^ (d 0 + d 1 - 1) * ((ℓ : ℝ)⁻¹) ^ a := pow_add _ _ _
      calc ‖((c d M₁ : ℚ) : ℚ_[ℓ]) - ((c d M₂ : ℚ) : ℚ_[ℓ])‖ * (‖t₀‖ ^ d 0 * ‖Y₁‖ ^ d 1)
          ≤ ‖((c d M₁ : ℚ) : ℚ_[ℓ]) - ((c d M₂ : ℚ) : ℚ_[ℓ])‖ *
              (((ℓ : ℝ)⁻¹) ^ (d 0 + d 1 - 1) * ((ℓ : ℝ)⁻¹) ^ a) :=
            mul_le_mul_of_nonneg_left hty (norm_nonneg _)
        _ = ‖((c d M₁ : ℚ) : ℚ_[ℓ]) - ((c d M₂ : ℚ) : ℚ_[ℓ])‖ *
              ((ℓ : ℝ)⁻¹) ^ (d 0 + d 1 - 1) * ((ℓ : ℝ)⁻¹) ^ a := by ring
        _ ≤ ((ℓ : ℝ)⁻¹) ^ e * ((ℓ : ℝ)⁻¹) ^ a :=
            mul_le_mul_of_nonneg_right (hΔ.trans hM) (pow_nonneg hr0 _)
        _ = ((ℓ : ℝ)⁻¹) ^ (e + a) := (pow_add _ _ _).symm
  · -- variation in `Y`
    rw [nS, nS, ← Finset.sum_sub_distrib]
    refine pnorm_sum_le ℓ _ _ (pow_nonneg hr0 _) fun d _ => ?_
    have e1 : ((c d M₂ : ℚ) : ℚ_[ℓ]) * (t₀ ^ d 0 * Y₁ ^ d 1) -
        ((c d M₂ : ℚ) : ℚ_[ℓ]) * (t₀ ^ d 0 * Y₂ ^ d 1) =
        ((c d M₂ : ℚ) : ℚ_[ℓ]) * t₀ ^ d 0 * (Y₁ ^ d 1 - Y₂ ^ d 1) := by ring
    rw [e1, norm_mul, norm_mul, norm_pow]
    have h1 : ‖((c d M₂ : ℚ) : ℚ_[ℓ])‖ * ‖t₀‖ ^ d 0 ≤ 1 :=
      mul_le_one₀ (hc1 d M₂) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) ht1)
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans
      ((pow_sub_pow_norm_le hY₁1 hY₂1 _).trans hYY)

end Virasoro
