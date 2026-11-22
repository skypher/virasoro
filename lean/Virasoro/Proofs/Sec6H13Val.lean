import Virasoro.Proofs.Sec6H13Spec
import Virasoro.Proofs.Generic
import Virasoro.Proofs.Sec4PFKac
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Proposition 6.8(iii) of `paper.tex` at 70bac53: the valuation (6.3) (l.1380–1392)

By the Kac determinant, `det G_M(c⋆,μ) ≠ 0` gives `det G_{M'}(c⋆,μ) ≠ 0` (`M' ≤ M`) and
`μ ≠ h_{u,1}(b⋆)` (`1 ≤ u ≤ M`).  Both `t⋆ = -p'/p` and `Y⋆ = μ t⋆²` lie in `ℓ ℤ_ℓ`, so (i) gives
`P_M^{(ν)}(t⋆,Y⋆) ≡ 4^M` modulo `ℓ`, whence `v_ℓ(P_M^{(ν)}(t⋆,Y⋆)) = 0` and `H_M(c⋆,μ,d_ν) ≠ 0`;
since `2μ - 2h_{u,1}(b⋆) = (m² - (p'u-p)²)/(2pp')`, taking `v_ℓ` gives (6.3).  Every coprime
pair `p, p' ≥ 2` has an odd prime factor, so `b ↦ b⁻¹` gives `H_M(c⋆,μ,d) ≢ 0` in general.
-/

namespace Virasoro

open Polynomial

/-- The Kac determinant at `t₀ = b²`: a nonvanishing `det G_M(c,μ)` gives nonvanishing
`det G_n(c,μ)` for `n ≤ M` and `μ ≠ h_{u,1}` for `1 ≤ u ≤ M` (paper.tex l.1380–1383). -/
theorem det_ne_of_kac (hK : Cited_KacDeterminant) {t₀ : ℚ} (ht : t₀ ≠ 0) {μ : ℚ} {M : ℕ}
    (h : (gram (cT t₀) μ M).det ≠ 0) :
    (∀ n ≤ M, (gram (cT t₀) μ n).det ≠ 0) ∧ ∀ u ∈ Finset.Icc 1 M, μ ≠ hT (u : ℤ) 1 t₀ := by
  obtain ⟨b, hb2⟩ := IsAlgClosed.exists_pow_nat_eq ((t₀ : ℚ) : ℂ) (n := 2) (by norm_num)
  have htC : ((t₀ : ℚ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hb2
    exact htC hb2.symm
  have hc : kacC b = ((cT t₀ : ℚ) : ℂ) := by
    simp only [kacC, cT]
    push_cast
    rw [← hb2]
    field_simp
    ring
  have hh : ∀ u v : ℤ, kacH u v b = ((hT u v t₀ : ℚ) : ℂ) := by
    intro u v
    simp only [kacH, hT]
    push_cast
    rw [← hb2]
    field_simp
  have hdetC : ∀ n, (gram (kacC b) ((μ : ℚ) : ℂ) n).det = (((gram (cT t₀) μ n).det : ℚ) : ℂ) := by
    intro n
    have hg := gram_map (Rat.castHom ℂ) (cT t₀) μ n
    have hd := RingHom.map_det (Rat.castHom ℂ) (gram (cT t₀) μ n)
    rw [hc]
    change (gram (Rat.castHom ℂ _) (Rat.castHom ℂ _) n).det = Rat.castHom ℂ _
    rw [hg, hd]
    rfl
  have hprod : ∀ n, ∃ C₀ : ℂ, C₀ ≠ 0 ∧ (((gram (cT t₀) μ n).det : ℚ) : ℂ) =
      C₀ * ∏ a ∈ labels n, (((μ : ℚ) : ℂ) - kacHL a b) ^
        Fintype.card (Nat.Partition (n - a.lvl)) := by
    intro n
    obtain ⟨C₀, hC₀, h1⟩ := hK b hb n
    refine ⟨C₀, hC₀, ?_⟩
    rw [← hdetC, ← gramPoly_det_eval, h1, eval_mul, eval_C, eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [eval_pow, eval_sub, eval_X, eval_C]
  have hroot : ∀ a ∈ labels M, ((μ : ℚ) : ℂ) - kacHL a b ≠ 0 := by
    intro a ha h0
    obtain ⟨C₀, -, h1⟩ := hprod M
    have hpos : Fintype.card (Nat.Partition (M - a.lvl)) ≠ 0 :=
      (Fintype.card_pos_iff.2 ⟨onesPartition _⟩).ne'
    have h2 : (((gram (cT t₀) μ M).det : ℚ) : ℂ) = 0 := by
      rw [h1, Finset.prod_eq_zero ha (by rw [h0, zero_pow hpos]), mul_zero]
    exact h (by exact_mod_cast h2)
  refine ⟨fun n hn h0 => ?_, fun u hu h0 => ?_⟩
  · obtain ⟨C₀, hC₀, h1⟩ := hprod n
    rw [h0, Rat.cast_zero] at h1
    rcases mul_eq_zero.1 h1.symm with h2 | h2
    · exact hC₀ h2
    · obtain ⟨a, ha, h3⟩ := Finset.prod_eq_zero_iff.1 h2
      exact pow_ne_zero _ (hroot a (labels_mono hn ha)) h3
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hu
    have hmem : ((u, 1) : Label) ∈ labels M := mem_labels.2 ⟨h1, le_refl 1, by simpa using h2⟩
    apply hroot _ hmem
    have : kacHL ((u, 1) : Label) b = ((hT (u : ℤ) 1 t₀ : ℚ) : ℂ) := by
      rw [kacHL, ← hh]
      rfl
    rw [this, h0, sub_self]

section Padic

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem padicNorm_sum_lt_one {α : Type*} (s : Finset α) (F : α → ℚ)
    (h : ∀ i ∈ s, padicNorm ℓ (F i) < 1) : padicNorm ℓ (∑ i ∈ s, F i) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt padicNorm.nonarchimedean
      (max_lt (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem padicValRat_prod {α : Type*} (s : Finset α) (F : α → ℚ) (h : ∀ i ∈ s, F i ≠ 0) :
    padicValRat ℓ (∏ i ∈ s, F i) = ∑ i ∈ s, padicValRat ℓ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem padicValRat_eq_zero_of_norm {x : ℚ} (h : padicNorm ℓ x = 1) : padicValRat ℓ x = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [padicNorm.zero] at h
    exact zero_ne_one h
  rw [padicNorm.eq_zpow_of_nonzero hx] at h
  have hℓ : (1 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have := (zpow_eq_one_iff_right₀ (by linarith) hℓ.ne').1 h
  omega

/-- A polynomial with `ℓ`-integral coefficients and constant term a unit takes a unit value at
arguments of norm less than one: `P(t⋆,Y⋆) ≡ P(0,0)` modulo `ℓ` (paper.tex l.1385–1387). -/
theorem eval_unit (P : MvPolynomial (Fin 2) ℚ) (hc : ∀ e, padicNorm ℓ (P.coeff e) ≤ 1)
    (h0 : padicNorm ℓ (P.coeff 0) = 1) {t₀ y₀ : ℚ} (ht : padicNorm ℓ t₀ < 1)
    (hy : padicNorm ℓ y₀ < 1) :
    padicNorm ℓ (MvPolynomial.eval (![t₀, y₀] : Fin 2 → ℚ) P) = 1 := by
  have h0mem : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h
    rw [h, padicNorm.zero] at h0
    exact zero_ne_one h0
  have hsplit : MvPolynomial.eval (![t₀, y₀] : Fin 2 → ℚ) P =
      P.coeff 0 + ∑ e ∈ P.support.erase 0, P.coeff e * (t₀ ^ e 0 * y₀ ^ e 1) := by
    rw [MvPolynomial.eval_eq', ← Finset.add_sum_erase _ _ h0mem]
    simp [Fin.prod_univ_two]
  have hrest : padicNorm ℓ (∑ e ∈ P.support.erase 0, P.coeff e * (t₀ ^ e 0 * y₀ ^ e 1)) < 1 := by
    refine padicNorm_sum_lt_one ℓ _ _ fun e he => ?_
    have hne : e ≠ 0 := (Finset.mem_erase.1 he).1
    rw [padicNorm.mul, padicNorm.mul, IsAbsoluteValue.abv_pow (padicNorm ℓ),
      IsAbsoluteValue.abv_pow (padicNorm ℓ)]
    have h1 : padicNorm ℓ t₀ ^ e 0 ≤ 1 := pow_le_one₀ (padicNorm.nonneg _) ht.le
    have h2 : padicNorm ℓ y₀ ^ e 1 ≤ 1 := pow_le_one₀ (padicNorm.nonneg _) hy.le
    have h3 : padicNorm ℓ t₀ ^ e 0 * padicNorm ℓ y₀ ^ e 1 < 1 := by
      by_cases he0 : e 0 = 0
      · have he1 : e 1 ≠ 0 := by
          intro he1
          apply hne
          ext i
          fin_cases i
          · exact he0
          · exact he1
        exact mul_lt_one_of_nonneg_of_lt_one_right h1 (pow_nonneg (padicNorm.nonneg _) _)
          (pow_lt_one₀ (padicNorm.nonneg _) hy he1)
      · exact mul_lt_one_of_nonneg_of_lt_one_left (pow_nonneg (padicNorm.nonneg _) _)
          (pow_lt_one₀ (padicNorm.nonneg _) ht he0) h2
    exact mul_lt_one_of_nonneg_of_lt_one_right (hc e)
      (mul_nonneg (pow_nonneg (padicNorm.nonneg _) _) (pow_nonneg (padicNorm.nonneg _) _)) h3
  rw [hsplit, padicNorm.add_eq_max_of_ne (by rw [h0]; exact hrest.ne'), h0]
  exact max_eq_left hrest.le

end Padic

/-- Clause (i) of Proposition 6.8 for a family `P`. -/
def H13ClauseI (P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ) : Prop :=
  ∀ ν M, 1 ≤ M →
    (∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n) ∧
    MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
      MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
    MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M

/-- The valuation of `H_M(c⋆,μ,d_ν)` at an odd prime `ℓ ∣ p'` (paper.tex l.1380–1390). -/
theorem h13_val_core (hK : Cited_KacDeterminant) (P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ)
    (hP : ∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M)
    (hi : H13ClauseI P) {p p' : ℕ} (hp : 2 ≤ p) (hp' : 2 ≤ p') (hcop : Nat.Coprime p p')
    (M : ℕ) (m : ℤ) (hM : 1 ≤ M)
    (hdet : (gram (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M).det ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p') (ν : Fin 2) :
    (∀ n ≤ M, (gram (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) n).det ≠ 0) ∧
    Hval (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (if ν = 0 then -1 + 2 * (p : ℚ) / p' else 2 + 2 * (p : ℚ) / p')
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M ≠ 0 ∧
    padicValRat ℓ (Hval (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (if ν = 0 then -1 + 2 * (p : ℚ) / p' else 2 + 2 * (p : ℚ) / p')
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M) =
        -(padicValNat ℓ M.factorial : ℤ) - (M : ℤ) * (padicValNat ℓ p' : ℤ)
          - ∑ u ∈ Finset.Icc 1 M,
              (padicValInt ℓ (m ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpq' : (p' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨μ, hμ⟩ : ∃ μ : ℚ, μ = ((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p') := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℚ, t₀ = -(p' : ℚ) / p := ⟨_, rfl⟩
  rw [← hμ] at hdet ⊢
  have ht : t₀ ≠ 0 := by
    rw [ht₀]
    exact div_ne_zero (neg_ne_zero.2 hpq') hpq
  have hcs : cT t₀ = 1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p') := by
    simp only [cT, ht₀]
    field_simp
    ring
  have hd : dval ν t₀ = if ν = 0 then -1 + 2 * (p : ℚ) / p' else 2 + 2 * (p : ℚ) / p' := by
    simp only [dval, ht₀]
    split_ifs <;> field_simp <;> ring
  rw [← hcs, ← hd]
  rw [← hcs] at hdet
  obtain ⟨hdets, hne⟩ := det_ne_of_kac hK ht hdet
  -- arithmetic of `ℓ`
  have hℓp_not : ¬ ℓ ∣ p := fun h =>
    hℓ.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h hℓp)
  have hℓ2' : ¬ ℓ ∣ 2 := fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
  have hnp : padicNorm ℓ (p : ℚ) = 1 := (padicNorm.nat_eq_one_iff (p := ℓ) p).2 hℓp_not
  have hnp' : padicNorm ℓ (p' : ℚ) < 1 := (padicNorm.nat_lt_one_iff (p := ℓ) p').2 hℓp
  have hnt : padicNorm ℓ t₀ < 1 := by
    rw [ht₀, padicNorm.div, padicNorm.neg, hnp, div_one]
    exact hnp'
  have hny : padicNorm ℓ (t₀ ^ 2 * μ) < 1 := by
    have e : t₀ ^ 2 * μ = t₀ * (((m ^ 2 - ((p' : ℤ) - p) ^ 2 : ℤ) : ℚ) / ((4 * p ^ 2 : ℕ) : ℚ)) *
        (-1) := by
      rw [hμ, ht₀]
      push_cast
      field_simp
    have h4 : padicNorm ℓ ((4 * p ^ 2 : ℕ) : ℚ) = 1 := by
      rw [padicNorm.nat_eq_one_iff]
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
      · exact hℓ2' (by
          have : ℓ ∣ 2 * 2 := by simpa using h
          rcases (Nat.Prime.dvd_mul hℓ).1 this with h | h <;> exact h)
      · exact hℓp_not (hℓ.dvd_of_dvd_pow h)
    have h5 : padicNorm ℓ (((m ^ 2 - ((p' : ℤ) - p) ^ 2 : ℤ) : ℚ) / ((4 * p ^ 2 : ℕ) : ℚ)) ≤ 1 := by
      rw [padicNorm.div, h4, div_one]
      exact padicNorm.of_int _
    rw [e, padicNorm.mul, padicNorm.mul, padicNorm.neg, padicNorm.one, mul_one]
    exact mul_lt_one_of_nonneg_of_lt_one_left (padicNorm.nonneg _) hnt h5
  -- the value of `P` is a unit
  obtain ⟨hint, -, h00⟩ := hi ν M hM
  have hcoef : ∀ e, padicNorm ℓ ((P ν M).coeff e) ≤ 1 := by
    intro e
    obtain ⟨z, n, hz⟩ := hint e
    have h2n : padicNorm ℓ ((2 : ℚ) ^ n) = 1 := by
      have : ((2 : ℚ) ^ n) = ((2 ^ n : ℕ) : ℚ) := by push_cast; rfl
      rw [this, padicNorm.nat_eq_one_iff]
      exact fun h => hℓ2' (hℓ.dvd_of_dvd_pow h)
    rw [hz, padicNorm.div, h2n, div_one]
    exact padicNorm.of_int z
  have hc0 : (P ν M).coeff 0 = 4 ^ M := by
    have hz : (![0, 0] : Fin 2 → ℚ) = 0 := by
      ext i
      fin_cases i <;> rfl
    rw [hz, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] at h00
    exact h00
  have hn0 : padicNorm ℓ ((P ν M).coeff 0) = 1 := by
    have : ((4 : ℚ) ^ M) = ((4 ^ M : ℕ) : ℚ) := by push_cast; rfl
    rw [hc0, this, padicNorm.nat_eq_one_iff]
    intro h
    have h4 : ℓ ∣ 2 * 2 := by simpa using hℓ.dvd_of_dvd_pow h
    rcases (Nat.Prime.dvd_mul hℓ).1 h4 with h | h <;> exact hℓ2' h
  have hunit := eval_unit ℓ (P ν M) hcoef hn0 hnt hny
  -- the specialization
  have hQ : clearedH ν M = psi (thetaInv (P ν M)) := by
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  have hspec := spec_formula hQ ht hdets
  rw [sig_thetaInv] at hspec
  have hval0 := padicValRat_eq_zero_of_norm ℓ hunit
  have hEne : ∀ u ∈ Finset.Icc 1 M, t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀) ≠ 0 := by
    intro u hu
    refine mul_ne_zero (pow_ne_zero _ ht) ?_
    have := hne u hu
    intro h0
    apply this
    linarith
  have hprodne : (∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 hEne
  have hfact : ((M.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
  have hHne : Hval (cT t₀) (dval ν t₀) μ M ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hspec
    rw [hspec, padicNorm.zero] at hunit
    exact zero_ne_one hunit
  refine ⟨hdets, hHne, ?_⟩
  rw [hspec, padicValRat.mul (mul_ne_zero hfact hprodne) hHne, padicValRat.mul hfact hprodne,
    padicValRat.of_nat, padicValRat_prod ℓ _ _ hEne] at hval0
  have hE : ∀ u ∈ Finset.Icc 1 M, padicValRat ℓ (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀)) =
      (padicValNat ℓ p' : ℤ) + (padicValInt ℓ (m ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ) := by
    intro u hu
    have e : t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀) =
        ((p' : ℚ) * ((m ^ 2 - ((p' : ℤ) * u - p) ^ 2 : ℤ) : ℚ)) / ((2 * p ^ 3 : ℕ) : ℚ) := by
      rw [hμ, ht₀, hT]
      push_cast
      field_simp
      ring
    have hz : ((m ^ 2 - ((p' : ℤ) * u - p) ^ 2 : ℤ) : ℚ) ≠ 0 := by
      intro h0
      apply hEne u hu
      rw [e, h0, mul_zero, zero_div]
    have hden : ((2 * p ^ 3 : ℕ) : ℚ) ≠ 0 := by
      have : 2 * p ^ 3 ≠ 0 := by positivity
      exact_mod_cast this
    have hden0 : padicValNat ℓ (2 * p ^ 3) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
      · exact hℓ2' h
      · exact hℓp_not (hℓ.dvd_of_dvd_pow h)
    rw [e, padicValRat.div (mul_ne_zero hpq' hz) hden, padicValRat.mul hpq' hz, padicValRat.of_nat,
      padicValRat.of_nat, padicValRat.of_int, hden0]
    simp
  rw [Finset.sum_congr rfl hE, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc] at hval0
  simp only [Nat.add_sub_cancel, nsmul_eq_mul] at hval0
  linarith

/-- The valuation identity (6.3) with its consequence `H_M(c⋆,μ,d) ≢ 0` (paper.tex
l.1380–1392). -/
theorem sub_h13_valuation (hK : Cited_KacDeterminant) : Stmt_sub_h13_valuation := by
  intro P hP hi p p' hp hp' hcop M m hM cs μ hdet
  have key : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ∣ p' → ∀ ν : Fin 2,
      (∀ n ≤ M, (gram cs μ n).det ≠ 0) ∧
      Hval cs (if ν = 0 then -1 + 2 * (p : ℚ) / p' else 2 + 2 * (p : ℚ) / p') μ M ≠ 0 ∧
      padicValRat ℓ (Hval cs (if ν = 0 then -1 + 2 * (p : ℚ) / p' else 2 + 2 * (p : ℚ) / p') μ M)
        = -(padicValNat ℓ M.factorial : ℤ) - (M : ℤ) * (padicValNat ℓ p' : ℤ)
          - ∑ u ∈ Finset.Icc 1 M, (padicValInt ℓ (m ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ) :=
    fun ℓ hℓ hℓ2 hℓp ν => h13_val_core hK P hP hi hp hp' hcop M m hM hdet ℓ hℓ hℓ2 hℓp ν
  refine ⟨?_, fun ℓ hℓ hℓ2 hℓp ν => ?_⟩
  · intro h0
    by_cases h2 : 2 ∣ p'
    · -- `p` is odd: exchange `p` and `p'`
      have hp2 : ¬ 2 ∣ p := fun h =>
        absurd (Nat.eq_one_of_dvd_coprimes hcop h h2) (by norm_num)
      have hℓ := Nat.minFac_prime (show p ≠ 1 by omega)
      have hℓ2 : p.minFac ≠ 2 := fun h => hp2 (h ▸ Nat.minFac_dvd p)
      have e1 : (1 - 6 * ((p : ℚ) - p') ^ 2 / (p' * p)) = cs := by
        show _ = 1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p')
        ring
      have e2 : (((m : ℚ) ^ 2 - ((p : ℚ) - p') ^ 2) / (4 * p' * p)) = μ := by
        show _ = ((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')
        ring
      have hsw := h13_val_core hK P hP hi hp' hp hcop.symm M m hM (by rw [e1, e2]; exact hdet)
        p.minFac hℓ hℓ2 (Nat.minFac_dvd p) 0
      rw [e1, e2] at hsw
      apply hsw.2.1
      rw [← eval_HpolyD, h0, eval_zero]
    · have hℓ := Nat.minFac_prime (show p' ≠ 1 by omega)
      have hℓ2 : p'.minFac ≠ 2 := fun h => h2 (h ▸ Nat.minFac_dvd p')
      apply (key p'.minFac hℓ hℓ2 (Nat.minFac_dvd p') 0).2.1
      rw [← eval_HpolyD, h0, eval_zero]
  · obtain ⟨hdets, hne, hval⟩ := key ℓ hℓ hℓ2 hℓp ν
    intro dν
    have hev := evalAt_Hrat (c := cs) (d := dν) (z := μ) (N := M) hdets
    refine ⟨regAt_Hrat hdets, ?_, ?_⟩
    · show evalAt μ (Hrat cs dν M) ≠ 0
      rw [hev]
      exact hne
    · show padicValRat ℓ (evalAt μ (Hrat cs dν M)) = _
      rw [hev]
      exact hval

example (hK : Cited_KacDeterminant) : Stmt_sub_h13_valuation := sub_h13_valuation hK

/-- Proposition 6.8 from its three open sub-statements: the integrality of clause (i), clause
(ii) and the Lipschitz bound (6.4). -/
theorem prop_h13_nonvanishing_of_three (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (h1 : Stmt_sub_h13_integral) (h2 : Stmt_sub_h13_degree)
    (h4 : Stmt_sub_h13_lipschitz) : Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_subs hK hH h1 h2 (sub_h13_valuation hK) h4

end Virasoro
