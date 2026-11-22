import Virasoro.Proofs.Sec6H13Val
import Virasoro.Proofs.Sec6H13LipCore

/-!
# Proposition 6.8(iii) of `paper.tex` at 70bac53: the Lipschitz bound (6.4) (l.1392–1416)

By (i) and (ii) each `c_{i,j}^{(ν)}(M)` is a polynomial in `M` of degree at most `2i+2j` with
values in `ℤ[1/2]` for all `M ≥ 0`.  The estimates of `Sec6H13LipCore` give
`v_ℓ(P_{M₁}^{(ν)}(t₀,Y₁)/4^{M₁} - P_{M₂}^{(ν)}(t₀,Y₂)/4^{M₂}) ≥ e + a` (`ν = 1, 2`), and since
all four values are `ℓ`-adic units, (6.4) follows.
-/

namespace Virasoro

open Polynomial Finset

section

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem aeval_eq_nS (P : MvPolynomial (Fin 2) ℚ) (M : ℕ) (S : Finset (Fin 2 →₀ ℕ))
    (hS : P.support ⊆ S) (t₀ Y : ℚ_[ℓ]) :
    MvPolynomial.aeval (![t₀, Y] : Fin 2 → ℚ_[ℓ]) P =
      (4 : ℚ_[ℓ]) ^ M * nS S (fun d => P.coeff d / 4 ^ M) t₀ Y := by
  have h1 : MvPolynomial.aeval (![t₀, Y] : Fin 2 → ℚ_[ℓ]) P =
      ∑ d ∈ P.support, ((P.coeff d : ℚ) : ℚ_[ℓ]) * (t₀ ^ d 0 * Y ^ d 1) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fin.prod_univ_two, eq_ratCast]
    rfl
  have h2 : ∑ d ∈ P.support, ((P.coeff d : ℚ) : ℚ_[ℓ]) * (t₀ ^ d 0 * Y ^ d 1) =
      ∑ d ∈ S, ((P.coeff d : ℚ) : ℚ_[ℓ]) * (t₀ ^ d 0 * Y ^ d 1) := by
    refine Finset.sum_subset hS fun d _ hd => ?_
    rw [MvPolynomial.notMem_support_iff.1 hd, Rat.cast_zero, zero_mul]
  rw [h1, h2, nS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h4 : (4 : ℚ_[ℓ]) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  field_simp

theorem single_add_single (d : Fin 2 →₀ ℕ) :
    Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
  ext i
  fin_cases i <;> simp

end

/-- `P_0^{(ν)} = 1`. -/
theorem h13_P_zero (P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ)
    (hP : ∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) (ν : Fin 2) : P ν 0 = 1 := by
  have h1 : clearedH ν 0 = psi 1 := by
    rw [map_one]
    simp [clearedH, Hrat_zero]
  have h2 := eq_thetaMv_of_aeval ((hP ν 0).trans h1)
  rw [h2, map_one]

/-- The Lipschitz bound (6.4) (paper.tex l.1392–1416). -/
theorem sub_h13_lipschitz : Stmt_sub_h13_lipschitz := by
  intro P hP hi hii p' ℓ inst hp' hℓ2 hℓp t₀ Y₁ Y₂ M₁ M₂ e hM₁ hM₂ ht hY₁ hY₂ hdiv hYY
  have hprime := (Fact.out : ℓ.Prime)
  have hℓ2' : ¬ ℓ ∣ 2 := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 h)
  have hℓ4 : ∀ M : ℕ, ¬ ℓ ∣ 4 ^ M := by
    intro M h
    have h4 : ℓ ∣ 2 * 2 := by simpa using hprime.dvd_of_dvd_pow h
    rcases (Nat.Prime.dvd_mul hprime).1 h4 with h | h <;> exact hℓ2' h
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = padicValNat ℓ p' := ⟨_, rfl⟩
  have ha : 1 ≤ a := by
    rw [ha_def]
    exact one_le_padicValNat_of_dvd (by omega) hℓp
  rw [← ha_def] at ht hY₁ hY₂ hYY ⊢
  -- the hypotheses with `r = ℓ⁻¹`
  have ht' : ‖t₀‖ ≤ ((ℓ : ℝ)⁻¹) ^ a := by
    rw [← zpow_neg_eq]
    exact ht
  have hY₁' : ‖Y₁‖ ≤ ((ℓ : ℝ)⁻¹) ^ (a + 1) := by
    rw [← zpow_neg_eq]
    push_cast
    exact hY₁
  have hY₂' : ‖Y₂‖ ≤ ((ℓ : ℝ)⁻¹) ^ (a + 1) := by
    rw [← zpow_neg_eq]
    push_cast
    exact hY₂
  have hM' : ‖(((M₁ : ℤ) - M₂ : ℤ) : ℚ_[ℓ])‖ ≤ ((ℓ : ℝ)⁻¹) ^ e := by
    rw [← zpow_neg_eq]
    exact (Padic.norm_int_le_pow_iff_dvd _ _).2 hdiv
  have hYY' : ‖Y₁ - Y₂‖ ≤ ((ℓ : ℝ)⁻¹) ^ (e + a) := by
    rw [← zpow_neg_eq]
    push_cast
    exact hYY
  have hr0 := rinv_nonneg ℓ
  have hr1 := rinv_le_one ℓ
  have hra : ((ℓ : ℝ)⁻¹) ^ a ≤ (ℓ : ℝ)⁻¹ := by
    calc ((ℓ : ℝ)⁻¹) ^ a ≤ ((ℓ : ℝ)⁻¹) ^ 1 := pow_le_pow_of_le_one hr0 hr1 ha
      _ = (ℓ : ℝ)⁻¹ := pow_one _
  have hra1 : ((ℓ : ℝ)⁻¹) ^ (a + 1) ≤ (ℓ : ℝ)⁻¹ := by
    calc ((ℓ : ℝ)⁻¹) ^ (a + 1) ≤ ((ℓ : ℝ)⁻¹) ^ 1 := pow_le_pow_of_le_one hr0 hr1 (by omega)
      _ = (ℓ : ℝ)⁻¹ := pow_one _
  -- the coefficient family
  have hP0 := h13_P_zero P hP
  have hcoef0 : ∀ ν M, 1 ≤ M → (P ν M).coeff 0 = 4 ^ M := by
    intro ν M hM
    have h00 := (hi ν M hM).2.2
    have hz : (![0, 0] : Fin 2 → ℚ) = 0 := by
      ext i
      fin_cases i <;> rfl
    rw [hz, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] at h00
    exact h00
  have hc0 : ∀ (ν : Fin 2) (M : ℕ), (P ν M).coeff 0 / 4 ^ M = 1 := by
    intro ν M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · rw [hP0]
      simp
    · rw [hcoef0 ν M hM, div_self (pow_ne_zero _ (by norm_num))]
  have hn4 : ∀ M : ℕ, padicNorm ℓ ((4 : ℚ) ^ M) = 1 := by
    intro M
    have : ((4 : ℚ) ^ M) = ((4 ^ M : ℕ) : ℚ) := by push_cast; rfl
    rw [this, padicNorm.nat_eq_one_iff]
    exact hℓ4 M
  have hc1 : ∀ (ν : Fin 2) (d : Fin 2 →₀ ℕ) (M : ℕ),
      ‖(((P ν M).coeff d / 4 ^ M : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    intro ν d M
    apply pnorm_rat_le_one
    rw [padicNorm.div, hn4, div_one]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · rw [hP0, MvPolynomial.coeff_one]
      split_ifs
      · rw [padicNorm.one]
      · rw [padicNorm.zero]
        exact zero_le_one
    · obtain ⟨z, n, hz⟩ := (hi ν M hM).1 d
      have h2n : padicNorm ℓ ((2 : ℚ) ^ n) = 1 := by
        have : ((2 : ℚ) ^ n) = ((2 ^ n : ℕ) : ℚ) := by push_cast; rfl
        rw [this, padicNorm.nat_eq_one_iff]
        exact fun h => hℓ2' (hprime.dvd_of_dvd_pow h)
      rw [hz, padicNorm.div, h2n, div_one]
      exact padicNorm.of_int z
  have hcf : ∀ (ν : Fin 2) (d : Fin 2 →₀ ℕ), ∃ f : ℚ[X], f.natDegree ≤ 2 * (d 0 + d 1) ∧
      ∀ M : ℕ, (P ν M).coeff d / 4 ^ M = f.eval (M : ℚ) := by
    intro ν d
    obtain ⟨f, hdeg, hf⟩ := hii ν (d 0) (d 1)
    refine ⟨f, by omega, fun M => ?_⟩
    rw [← hf M, single_add_single]
  -- the four values
  obtain ⟨S, hS⟩ : ∃ S : Fin 2 → Finset (Fin 2 →₀ ℕ),
      S = fun ν => (P ν M₁).support ∪ (P ν M₂).support ∪ {0} := ⟨_, rfl⟩
  have hS1 : ∀ ν, (P ν M₁).support ⊆ S ν := by
    intro ν
    rw [hS]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hS2 : ∀ ν, (P ν M₂).support ⊆ S ν := by
    intro ν
    rw [hS]
    exact Finset.subset_union_right.trans Finset.subset_union_left
  have hS0 : ∀ ν, (0 : Fin 2 →₀ ℕ) ∈ S ν := by
    intro ν
    rw [hS]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self 0)
  have h4K : ∀ M : ℕ, ‖(4 : ℚ_[ℓ]) ^ M‖ = 1 := by
    intro M
    have : ((4 : ℚ_[ℓ]) ^ M) = ((4 ^ M : ℕ) : ℚ_[ℓ]) := by push_cast; rfl
    rw [this]
    exact pnorm_nat_eq_one ℓ (hℓ4 M)
  have hu1 : ∀ ν, ‖nS (S ν) (fun d => (P ν M₁).coeff d / 4 ^ M₁) t₀ Y₁‖ = 1 := fun ν =>
    nS_unit (S ν) _ (hS0 ν) (hc0 ν M₁) (fun d => hc1 ν d M₁) (ht'.trans hra) (hY₁'.trans hra1)
  have hu2 : ∀ ν, ‖nS (S ν) (fun d => (P ν M₂).coeff d / 4 ^ M₂) t₀ Y₂‖ = 1 := fun ν =>
    nS_unit (S ν) _ (hS0 ν) (hc0 ν M₂) (fun d => hc1 ν d M₂) (ht'.trans hra) (hY₂'.trans hra1)
  have hlip : ∀ ν, ‖nS (S ν) (fun d => (P ν M₁).coeff d / 4 ^ M₁) t₀ Y₁ -
      nS (S ν) (fun d => (P ν M₂).coeff d / 4 ^ M₂) t₀ Y₂‖ ≤ ((ℓ : ℝ)⁻¹) ^ (e + a) := fun ν =>
    nS_lip hℓ2 (S ν) (fun d M => (P ν M).coeff d / 4 ^ M) (hc0 ν) (hc1 ν) (hcf ν) ha ht' hY₁'
      hY₂' M₁ M₂ hM' hYY'
  have hE1 : ∀ ν, MvPolynomial.aeval (![t₀, Y₁] : Fin 2 → ℚ_[ℓ]) (P ν M₁) =
      (4 : ℚ_[ℓ]) ^ M₁ * nS (S ν) (fun d => (P ν M₁).coeff d / 4 ^ M₁) t₀ Y₁ := fun ν =>
    aeval_eq_nS (P ν M₁) M₁ (S ν) (hS1 ν) t₀ Y₁
  have hE2 : ∀ ν, MvPolynomial.aeval (![t₀, Y₂] : Fin 2 → ℚ_[ℓ]) (P ν M₂) =
      (4 : ℚ_[ℓ]) ^ M₂ * nS (S ν) (fun d => (P ν M₂).coeff d / 4 ^ M₂) t₀ Y₂ := fun ν =>
    aeval_eq_nS (P ν M₂) M₂ (S ν) (hS2 ν) t₀ Y₂
  show ‖MvPolynomial.aeval (![t₀, Y₁] : Fin 2 → ℚ_[ℓ]) (P 0 M₁)‖ = 1 ∧
    ‖MvPolynomial.aeval (![t₀, Y₁] : Fin 2 → ℚ_[ℓ]) (P 1 M₁)‖ = 1 ∧
    ‖MvPolynomial.aeval (![t₀, Y₂] : Fin 2 → ℚ_[ℓ]) (P 0 M₂)‖ = 1 ∧
    ‖MvPolynomial.aeval (![t₀, Y₂] : Fin 2 → ℚ_[ℓ]) (P 1 M₂)‖ = 1 ∧
    ‖MvPolynomial.aeval (![t₀, Y₁] : Fin 2 → ℚ_[ℓ]) (P 0 M₁) *
        MvPolynomial.aeval (![t₀, Y₂] : Fin 2 → ℚ_[ℓ]) (P 1 M₂) -
      MvPolynomial.aeval (![t₀, Y₁] : Fin 2 → ℚ_[ℓ]) (P 1 M₁) *
        MvPolynomial.aeval (![t₀, Y₂] : Fin 2 → ℚ_[ℓ]) (P 0 M₂)‖ ≤
      (ℓ : ℝ) ^ (-((e : ℤ) + (a : ℤ)))
  rw [hE1 0, hE1 1, hE2 0, hE2 1]
  refine ⟨by rw [norm_mul, h4K, hu1, mul_one], by rw [norm_mul, h4K, hu1, mul_one],
    by rw [norm_mul, h4K, hu2, mul_one], by rw [norm_mul, h4K, hu2, mul_one], ?_⟩
  obtain ⟨n01, hn01⟩ : ∃ x, x = nS (S 0) (fun d => (P 0 M₁).coeff d / 4 ^ M₁) t₀ Y₁ := ⟨_, rfl⟩
  obtain ⟨n11, hn11⟩ : ∃ x, x = nS (S 1) (fun d => (P 1 M₁).coeff d / 4 ^ M₁) t₀ Y₁ := ⟨_, rfl⟩
  obtain ⟨n02, hn02⟩ : ∃ x, x = nS (S 0) (fun d => (P 0 M₂).coeff d / 4 ^ M₂) t₀ Y₂ := ⟨_, rfl⟩
  obtain ⟨n12, hn12⟩ : ∃ x, x = nS (S 1) (fun d => (P 1 M₂).coeff d / 4 ^ M₂) t₀ Y₂ := ⟨_, rfl⟩
  have hl0 := hlip 0
  have hl1 := hlip 1
  have hu02 := hu2 0
  have hu12 := hu2 1
  rw [← hn01, ← hn02] at hl0
  rw [← hn11, ← hn12] at hl1
  rw [← hn02] at hu02
  rw [← hn12] at hu12
  rw [← hn01, ← hn11, ← hn02, ← hn12]
  have hcross : (4 : ℚ_[ℓ]) ^ M₁ * n01 * ((4 : ℚ_[ℓ]) ^ M₂ * n12) -
      (4 : ℚ_[ℓ]) ^ M₁ * n11 * ((4 : ℚ_[ℓ]) ^ M₂ * n02) =
      (4 : ℚ_[ℓ]) ^ M₁ * (4 : ℚ_[ℓ]) ^ M₂ * ((n01 - n02) * n12 + -((n11 - n12) * n02)) := by
    ring
  have hrhs : (ℓ : ℝ) ^ (-((e : ℤ) + (a : ℤ))) = ((ℓ : ℝ)⁻¹) ^ (e + a) := by
    rw [← zpow_neg_eq]
    push_cast
    rfl
  rw [hcross, hrhs, norm_mul, norm_mul, h4K, h4K, one_mul, one_mul]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, hu12, mul_one]
    exact hl0
  · rw [norm_neg, norm_mul, hu02, mul_one]
    exact hl1

example : Stmt_sub_h13_lipschitz := sub_h13_lipschitz

/-- Proposition 6.8 from its two open sub-statements: the integrality of clause (i) and
clause (ii). -/
theorem prop_h13_nonvanishing_of_two (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (h1 : Stmt_sub_h13_integral) (h2 : Stmt_sub_h13_degree) : Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_three hK hH h1 h2 sub_h13_lipschitz

end Virasoro
