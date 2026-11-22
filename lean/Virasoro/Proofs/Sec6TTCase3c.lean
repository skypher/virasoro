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

section HratBound

variable {p p' r s : ℕ}

theorem val_2kpp {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ¬ ℓ ∣ p) {k : ℕ} (hk : 1 ≤ k)
    (hp : 0 < p) (hp' : 0 < p') :
    padicValInt ℓ (2 * (k : ℤ) * p * p') = padicValNat ℓ k + padicValNat ℓ p' := by
  have e : (2 * (k : ℤ) * p * p') = ((2 * k * p * p' : ℕ) : ℤ) := by push_cast; ring
  rw [e, padicValInt.of_nat, padicValNat.mul (by positivity) (by omega),
    padicValNat.mul (by positivity) (by omega), padicValNat.mul (by norm_num) (by omega),
    padicValNat.eq_zero_of_not_dvd (fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out
      Nat.prime_two).1 h)), padicValNat.eq_zero_of_not_dvd hℓp]
  ring

/-- `ℓ⁻_k − ℓ⁺_k = k(kpp' − m⁺_k)`. -/
theorem ell_diff {hr : r < p} {hs : s < p'} (hp : 0 < p) (hp' : 0 < p') {k : ℕ} (hk : 1 ≤ k) :
    (ellOrb p p' r s false k : ℤ) - ellOrb p p' r s true k =
      k * (k * p * p' - nOrb p p' r s true k) := by
  have h1 := nOrb_sq hr hs true hk
  have h2 := nOrb_sq hr hs false hk
  have hsum := nOrb_sum p p' r s k
  have hpp : (4 * (p : ℤ) * p') ≠ 0 := by positivity
  apply mul_left_cancel₀ hpp
  linear_combination h1 - h2 +
    (nOrb p p' r s false k - nOrb p p' r s true k + 2 * k * p * p') * hsum

/-- `v_ℓ(H_rat) = 0` and `v_ℓ(H_rat − 1) ≥ v_ℓ(k) + a` (paper.tex l.1553–1562). -/
theorem Hr_bound (h68 : Stmt_prop_h13_nonvanishing) {k N : ℕ} (hyp : CoreHyp p p' r s k N)
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p')
    (hsl : (ℓ : ℤ) ∣ (s : ℤ) - 1 ∨ (ℓ : ℤ) ∣ (s : ℤ) + 1) :
    let H : Bool → Fin 2 → ℚ := fun ε ν =>
      (HpolyD (cs p p') (muQ p p' r s ε k) (N - ellOrb p p' r s ε k)).eval
        (if ν = 0 then dQ p p' ((p' : ℤ) - 3 * p) else dQ p p' ((p' : ℤ) + 3 * p))
    padicValRat ℓ (H true 0 * H false 1 / (H true 1 * H false 0)) = 0 ∧
      (H true 0 * H false 1 / (H true 1 * H false 0) ≠ 1 →
        (padicValNat ℓ k : ℤ) + padicValNat ℓ p' ≤
          padicValRat ℓ (H true 0 * H false 1 / (H true 1 * H false 0) - 1)) := by
  intro H
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, -, hk, hN1, hN2, hdet, -, -⟩ := hyp
  obtain ⟨P, hP, -, -, -, hlip⟩ := h68
  have h0p : 0 < p := by omega
  have h0p' : 0 < p' := by omega
  have hℓpn : ¬ ℓ ∣ p := by
    intro h
    have := Nat.dvd_gcd h hℓp
    rw [hcop] at this
    exact hℓ.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hℓp'z : (ℓ : ℤ) ∣ p' := Int.natCast_dvd_natCast.2 hℓp
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast h0p.ne'
  have hpq' : (p' : ℚ) ≠ 0 := by exact_mod_cast h0p'.ne'
  set a : ℕ := padicValNat ℓ p' with ha
  set t₀ : ℚ := -(p' : ℚ) / p with ht₀
  set M : Bool → ℕ := fun ε => N - ellOrb p p' r s ε k with hMd
  set Y : Bool → ℚ := fun ε => t₀ ^ 2 * muQ p p' r s ε k with hYd
  set E : Fin 2 → Bool → ℚ := fun ν ε =>
    MvPolynomial.eval (![t₀, Y ε] : Fin 2 → ℚ) (P ν (M ε)) with hEd
  -- `E = K · H`
  have hE : ∀ ν ε, ∃ K : ℚ, E ν ε = K * H ε ν ∧
      ∀ ν', E ν' ε = K * H ε ν' := by
    intro ν ε
    refine ⟨((M ε).factorial : ℚ) * (∏ u ∈ Finset.Icc 1 (M ε),
      (t₀ ^ 2 * (2 * muQ p p' r s ε k - 2 * hT (u : ℤ) 1 t₀))), ?_, fun ν' => ?_⟩
    · exact E_eq hP h0p h0p' (hdet ε) ν
    · exact E_eq hP h0p h0p' (hdet ε) ν'
  -- the values in `ℚ_ℓ`
  have haev : ∀ ν ε, MvPolynomial.aeval (![(t₀ : ℚ_[ℓ]), (Y ε : ℚ_[ℓ])] : Fin 2 → ℚ_[ℓ])
      (P ν (M ε)) = ((E ν ε : ℚ) : ℚ_[ℓ]) := by
    intro ν ε
    have : (![(t₀ : ℚ_[ℓ]), (Y ε : ℚ_[ℓ])] : Fin 2 → ℚ_[ℓ]) =
        (algebraMap ℚ ℚ_[ℓ]) ∘ (![t₀, Y ε] : Fin 2 → ℚ) := by
      funext i
      fin_cases i <;> simp
    rw [this, MvPolynomial.aeval_algebraMap_apply, eq_ratCast]
    rfl
  -- the hypotheses of (6.4)
  have ht0 : ‖(t₀ : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(a : ℤ)) := by
    refine norm_le_of_val t₀ a fun _ => le_of_eq ?_
    rw [ht₀, padicValRat.div (neg_ne_zero.2 hpq') hpq, padicValRat.neg, padicValRat.of_nat,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hℓpn]
    simp [ha]
  have hzdiv : ∀ ε, (ℓ : ℤ) ∣ nOrb p p' r s ε k ^ 2 - ((p' : ℤ) - p) ^ 2 := by
    intro ε
    obtain ⟨t, σ', hσ', he⟩ := nOrb_mod p p' r s ε k
    have hσσ : σ' * σ' = 1 := by rcases hσ' with rfl | rfl <;> norm_num
    have e : nOrb p p' r s ε k ^ 2 - ((p' : ℤ) - p) ^ 2 =
        p' * (p' * t ^ 2 + 2 * t * σ' * p * s - p' + 2 * p) +
          (σ' * σ') * ((s - 1) * (s + 1)) * p * p + ((σ' * σ') - 1) * p * p := by rw [he]; ring
    rw [e, hσσ, sub_self, zero_mul, zero_mul, add_zero, one_mul]
    refine dvd_add (dvd_mul_of_dvd_left hℓp'z _) ?_
    rcases hsl with h | h
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _) _
  have hY : ∀ ε, ‖(Y ε : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-((a : ℤ) + 1)) := by
    intro ε
    refine norm_le_of_val (Y ε) ((a : ℤ) + 1) fun hY0 => ?_
    have hYe : Y ε = (p' : ℚ) * ((nOrb p p' r s ε k ^ 2 - ((p' : ℤ) - p) ^ 2 : ℤ) : ℚ) /
        (4 * (p : ℚ) ^ 3) := Y_eq h0p h0p' _
    have hz : nOrb p p' r s ε k ^ 2 - ((p' : ℤ) - p) ^ 2 ≠ 0 := by
      intro h0
      apply hY0
      rw [hYe, h0, Int.cast_zero, mul_zero, zero_div]
    rw [hYe, val_frac hℓ2 h0p h0p' hℓpn _ hz]
    have : 1 ≤ padicValInt ℓ (nOrb p p' r s ε k ^ 2 - ((p' : ℤ) - p) ^ 2) :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.2 hz) (Int.natCast_dvd.1 (hzdiv ε))
    rw [← ha]
    push_cast
    omega
  have hMle : ∀ ε, ellOrb p p' r s ε k ≤ N := by
    intro ε
    cases ε
    · rw [ellOrb_false hk]
      exact (le_max_right _ _).trans hN1.le
    · rw [ellOrb_true hk]
      exact (le_max_left _ _).trans hN1.le
  have hM1 : ∀ ε, 1 ≤ M ε := by
    intro ε
    cases ε
    · simp only [hMd]
      rw [ellOrb_false hk]
      have := le_max_right (ellPlus p p' r s k) (ellMinus p p' r s k)
      omega
    · simp only [hMd]
      rw [ellOrb_true hk]
      have := le_max_left (ellPlus p p' r s k) (ellMinus p p' r s k)
      omega
  have hdiv : (ℓ : ℤ) ^ (padicValNat ℓ k) ∣ (M true : ℤ) - M false := by
    have e : (M true : ℤ) - M false = k * (k * p * p' - nOrb p p' r s true k) := by
      show ((N - ellOrb p p' r s true k : ℕ) : ℤ) - ((N - ellOrb p p' r s false k : ℕ) : ℤ) = _
      rw [Nat.cast_sub (hMle true), Nat.cast_sub (hMle false)]
      have := ell_diff (hr := hrp) (hs := hsp) h0p h0p' hk
      linarith
    rw [e]
    exact dvd_mul_of_dvd_left (by exact_mod_cast pow_padicValNat_dvd) _
  have hY12 : ‖(Y true : ℚ_[ℓ]) - (Y false : ℚ_[ℓ])‖ ≤
      (ℓ : ℝ) ^ (-((padicValNat ℓ k : ℤ) + a)) := by
    rw [show (Y true : ℚ_[ℓ]) - (Y false : ℚ_[ℓ]) = ((Y true - Y false : ℚ) : ℚ_[ℓ]) by push_cast; rfl]
    refine norm_le_of_val _ _ fun hne => ?_
    have hsum := nOrb_sum p p' r s k
    set z : ℤ := (nOrb p p' r s true k - nOrb p p' r s false k) * (2 * k * p * p') with hz
    have hYe : Y true - Y false = (p' : ℚ) * (z : ℚ) / (4 * (p : ℚ) ^ 3) := by
      have h1 : Y true = _ := Y_eq h0p h0p' (nOrb p p' r s true k)
      have h2 : Y false = _ := Y_eq h0p h0p' (nOrb p p' r s false k)
      rw [h1, h2, hz]
      have hs' : ((nOrb p p' r s true k : ℤ) : ℚ) + nOrb p p' r s false k = 2 * k * p * p' := by
        exact_mod_cast hsum
      push_cast
      rw [div_sub_div_same]
      congr 1
      rw [← hs']
      ring
    have hz0 : z ≠ 0 := by
      intro h0
      apply hne
      rw [hYe, h0, Int.cast_zero, mul_zero, zero_div]
    rw [hYe, val_frac hℓ2 h0p h0p' hℓpn z hz0, hz]
    have hm : nOrb p p' r s true k - nOrb p p' r s false k ≠ 0 := by
      intro h0; apply hz0; rw [hz, h0, zero_mul]
    have h2k : (2 * (k : ℤ) * p * p') ≠ 0 := by
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk
      positivity
    rw [padicValInt.mul hm h2k, val_2kpp hℓ2 hℓpn hk h0p h0p', ← ha]
    push_cast
    omega
  -- apply (6.4)
  have hl := hlip p' ℓ hp' hℓ2 hℓp (t₀ : ℚ_[ℓ]) (Y true : ℚ_[ℓ]) (Y false : ℚ_[ℓ]) (M true)
    (M false) (padicValNat ℓ k) (hM1 true) (hM1 false) ht0 (hY true) (hY false) hdiv hY12
  simp only at hl
  rw [haev 0 true, haev 1 true, haev 0 false, haev 1 false] at hl
  obtain ⟨n1, n2, n3, n4, n5⟩ := hl
  rw [show ((E 0 true : ℚ) : ℚ_[ℓ]) * ((E 1 false : ℚ) : ℚ_[ℓ]) -
      ((E 1 true : ℚ) : ℚ_[ℓ]) * ((E 0 false : ℚ) : ℚ_[ℓ]) =
      ((E 0 true * E 1 false - E 1 true * E 0 false : ℚ) : ℚ_[ℓ]) by push_cast; rfl] at n5
  have hr := padic_ratio n1 n2 n3 n4 n5
  -- the prefactors cancel
  obtain ⟨Kt, hKt, hKt'⟩ := hE 0 true
  obtain ⟨Kf, hKf, hKf'⟩ := hE 0 false
  have hEne : ∀ ν ε, E ν ε ≠ 0 := by
    intro ν ε h0
    have hn : ‖((E ν ε : ℚ) : ℚ_[ℓ])‖ = 1 := by
      cases ν using Fin.cases with
      | zero => cases ε <;> assumption
      | succ i =>
        have : i = 0 := Subsingleton.elim _ _
        subst this
        cases ε <;> assumption
    rw [h0, Rat.cast_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hKt0 : Kt ≠ 0 := fun h0 => hEne 0 true (by rw [hKt, h0, zero_mul])
  have hKf0 : Kf ≠ 0 := fun h0 => hEne 0 false (by rw [hKf, h0, zero_mul])
  have hq : E 0 true * E 1 false / (E 1 true * E 0 false) =
      H true 0 * H false 1 / (H true 1 * H false 0) := by
    rw [hKt' 0, hKt' 1, hKf' 0, hKf' 1]
    rw [show Kt * H true 0 * (Kf * H false 1) = (Kt * Kf) * (H true 0 * H false 1) by ring,
      show Kt * H true 1 * (Kf * H false 0) = (Kt * Kf) * (H true 1 * H false 0) by ring,
      mul_div_mul_left _ _ (mul_ne_zero hKt0 hKf0)]
  rw [hq] at hr
  exact hr

end HratBound

end TT

end Virasoro
