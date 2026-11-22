import Virasoro.Proofs.Sec6TTCase3b
import Virasoro.Proofs.Sec6H13Val

/-!
# Proposition 6.9, Case 3: `H_rat` from (6.4) (paper.tex l.1553–1562)

Put `t₀ = −p'/p`, `Y^± = t₀² μ^±_k`.  Then `v_ℓ(t₀) = a`, `v_ℓ(Y^±) ≥ a+1`,
`ℓ^{v_ℓ(k)} ∣ M⁺ − M⁻` and `v_ℓ(Y⁺ − Y⁻) ≥ v_ℓ(k) + 2a`; by (6.4) the four values
`P^{(ν)}_{M^±}(t₀, Y^±)` are units and `H_rat = (P⁽¹⁾_{M⁺}P⁽²⁾_{M⁻})/(P⁽²⁾_{M⁺}P⁽¹⁾_{M⁻})`, which equals
`(H_{M⁺}(d₁)/H_{M⁺}(d₂))/(H_{M⁻}(d₁)/H_{M⁻}(d₂))`, has `v_ℓ(H_rat) = 0` and
`v_ℓ(H_rat − 1) ≥ v_ℓ(k) + a`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

section Padic

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem norm_le_of_val (q : ℚ) (n : ℤ) (h : q ≠ 0 → n ≤ padicValRat ℓ q) :
    ‖(q : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-n) := by
  rw [Padic.eq_padicNorm]
  by_cases hq : q = 0
  · rw [hq, padicNorm.zero, Rat.cast_zero]
    positivity
  · rw [padicNorm.eq_zpow_of_nonzero hq]
    push_cast
    exact zpow_le_zpow_right₀ (by exact_mod_cast hℓ.out.one_lt.le) (by linarith [h hq])

theorem val_ge_of_norm_le {q : ℚ} (hq : q ≠ 0) {n : ℤ} (h : ‖(q : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-n)) :
    n ≤ padicValRat ℓ q := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq] at h
  push_cast at h
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  have := (zpow_le_zpow_iff_right₀ h1).1 h
  linarith

theorem padicNorm_one_of_norm {q : ℚ} (h : ‖(q : ℚ_[ℓ])‖ = 1) : padicNorm ℓ q = 1 := by
  rw [Padic.eq_padicNorm] at h
  exact_mod_cast h

/-- Four `ℓ`-adic units `A, B, C, D` with `‖AD − BC‖ ≤ ℓ^{−n}`: `v(AD/(BC)) = 0` and
`v(AD/(BC) − 1) ≥ n`. -/
theorem padic_ratio {A B C D : ℚ} (hA : ‖(A : ℚ_[ℓ])‖ = 1) (hB : ‖(B : ℚ_[ℓ])‖ = 1)
    (hC : ‖(C : ℚ_[ℓ])‖ = 1) (hD : ‖(D : ℚ_[ℓ])‖ = 1) {n : ℤ}
    (h : ‖((A * D - B * C : ℚ) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-n)) :
    padicValRat ℓ (A * D / (B * C)) = 0 ∧
      (A * D / (B * C) ≠ 1 → n ≤ padicValRat ℓ (A * D / (B * C) - 1)) := by
  have nz : ∀ {x : ℚ}, ‖(x : ℚ_[ℓ])‖ = 1 → x ≠ 0 := fun hx h0 => by
    rw [h0, Rat.cast_zero, norm_zero] at hx
    exact zero_ne_one hx
  have v0 : ∀ {x : ℚ}, ‖(x : ℚ_[ℓ])‖ = 1 → padicValRat ℓ x = 0 := fun hx =>
    padicValRat_eq_zero_of_norm ℓ (padicNorm_one_of_norm hx)
  have hA0 := nz hA
  have hB0 := nz hB
  have hC0 := nz hC
  have hD0 := nz hD
  refine ⟨?_, fun hne => ?_⟩
  · rw [padicValRat.div (mul_ne_zero hA0 hD0) (mul_ne_zero hB0 hC0), padicValRat.mul hA0 hD0,
      padicValRat.mul hB0 hC0, v0 hA, v0 hB, v0 hC, v0 hD]
    simp
  · have e : A * D / (B * C) - 1 = (A * D - B * C) / (B * C) := by
      field_simp
    have hn : A * D - B * C ≠ 0 := by
      intro h0
      apply hne
      rw [div_eq_one_iff_eq (mul_ne_zero hB0 hC0)]
      linarith
    rw [e, padicValRat.div hn (mul_ne_zero hB0 hC0), padicValRat.mul hB0 hC0, v0 hB, v0 hC,
      add_zero, sub_zero]
    exact val_ge_of_norm_le hn h

end Padic

section Hrat

variable {p p' r s : ℕ}

/-- `P^{(ν)}_M(t₀, t₀²μ) = M! ∏_u t₀²(2μ − 2h_{u,1}) · H_M(c⋆, μ, d_ν)`, `t₀ = −p'/p`
(Proposition 6.8's polynomial specialized, `spec_formula`). -/
theorem E_eq {P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ}
    (hP : ∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) (hp : 0 < p) (hp' : 0 < p') {μ : ℚ} {M : ℕ}
    (hdet : ∀ n ≤ M, (gram (cs p p') μ n).det ≠ 0) (ν : Fin 2) :
    MvPolynomial.eval (![-(p' : ℚ) / p, (-(p' : ℚ) / p) ^ 2 * μ] : Fin 2 → ℚ) (P ν M) =
      (M.factorial : ℚ) *
        (∏ u ∈ Finset.Icc 1 M, ((-(p' : ℚ) / p) ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 (-(p' : ℚ) / p)))) *
        (HpolyD (cs p p') μ M).eval
          (if ν = 0 then dQ p p' ((p' : ℤ) - 3 * p) else dQ p p' ((p' : ℤ) + 3 * p)) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpq' : (p' : ℚ) ≠ 0 := by exact_mod_cast hp'.ne'
  set t₀ : ℚ := -(p' : ℚ) / p with ht₀
  have ht : t₀ ≠ 0 := div_ne_zero (neg_ne_zero.2 hpq') hpq
  have hcs : cT t₀ = cs p p' := by
    simp only [cT, cs, ht₀]
    field_simp
    ring
  have hd : dval ν t₀ =
      if ν = 0 then dQ p p' ((p' : ℤ) - 3 * p) else dQ p p' ((p' : ℤ) + 3 * p) := by
    rw [d1_eq hp hp', d2_eq hp hp']
    simp only [dval, ht₀]
    split_ifs <;> field_simp <;> ring
  have hQ : clearedH ν M = psi (thetaInv (P ν M)) := by
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  have hdets : ∀ n ≤ M, (gram (cT t₀) μ n).det ≠ 0 := by rw [hcs]; exact hdet
  have hspec := spec_formula hQ ht hdets
  rw [sig_thetaInv, hcs, hd, ← eval_HpolyD] at hspec
  exact hspec

theorem val_frac {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hp : 0 < p) (hp' : 0 < p')
    (hℓp : ¬ ℓ ∣ p) (z : ℤ) (hz : z ≠ 0) :
    padicValRat ℓ ((p' : ℚ) * z / (4 * (p : ℚ) ^ 3)) = (padicValNat ℓ p' : ℤ) + padicValInt ℓ z := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpq' : (p' : ℚ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  have h4 : padicValRat ℓ (4 * (p : ℚ) ^ 3) = 0 := by
    have : (4 * (p : ℚ) ^ 3) = ((4 * p ^ 3 : ℕ) : ℚ) := by push_cast; ring
    rw [this, padicValRat.of_nat]
    norm_cast
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    rcases (Nat.Prime.dvd_mul hℓ.out).1 h with h | h
    · have : ℓ ∣ 2 * 2 := by norm_num; exact h
      rcases (Nat.Prime.dvd_mul hℓ.out).1 this with h | h <;>
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 h)
    · exact hℓp (hℓ.out.dvd_of_dvd_pow h)
  rw [padicValRat.div (mul_ne_zero hpq' hzq) (by positivity), padicValRat.mul hpq' hzq, h4,
    padicValRat.of_nat, padicValRat.of_int, sub_zero]

/-- `t₀² d_m = p'(m² − (p'−p)²)/(4p³)`. -/
theorem Y_eq (hp : 0 < p) (hp' : 0 < p') (m : ℤ) :
    (-(p' : ℚ) / p) ^ 2 * dQ p p' m = (p' : ℚ) * ((m ^ 2 - ((p' : ℤ) - p) ^ 2 : ℤ) : ℚ) /
      (4 * (p : ℚ) ^ 3) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpq' : (p' : ℚ) ≠ 0 := by exact_mod_cast hp'.ne'
  rw [dQ]
  push_cast
  field_simp

end Hrat

end TT

end Virasoro
