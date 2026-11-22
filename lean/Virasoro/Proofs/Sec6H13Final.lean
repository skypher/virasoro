import Virasoro.Proofs.Sec6H13Values

/-!
# Proposition 6.8 of `paper.tex` at 70bac53: reduction to frozen sub-statements

Clause (i) is split into `P_M^{(ν)} ∈ ℚ[t,Y]` (`sub_h13_polynomial`, l.1224–1261), the values at
`t = 0` (`sub_h13_values`, l.1248–1256) and the integrality `P_M^{(ν)} ∈ ℤ[1/2][t,Y]`
(`Stmt_sub_h13_integral`, l.1261–1291).  Clause (ii) is `Stmt_sub_h13_degree` (l.1293–1378).
Clause (iii) is split into the valuation identity with its consequence
(`Stmt_sub_h13_valuation`, l.1380–1392) and the Lipschitz bound (6.4)
(`Stmt_sub_h13_lipschitz`, l.1392–1416).
-/

namespace Virasoro

open Polynomial

/-- Frozen sub-statement of Proposition 6.8(i) (paper.tex l.1185, proof l.1261–1291): the
coefficients of `P_M^{(ν)}` lie in `ℤ[1/2]`.
Demand sheet: for every family `P` tied to the definition by `P(t, t²Δ) = clearedH ν M`, the
first conjunct of clause (i) of `Stmt_prop_h13_nonvanishing`, word for word, for `M ≥ 1`. -/
def Stmt_sub_h13_integral : Prop :=
  ∀ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    (∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) →
    ∀ (ν : Fin 2) (M : ℕ), 1 ≤ M →
      ∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n

/-- Frozen sub-statement of Proposition 6.8(ii) (paper.tex l.1188–1190, proof l.1293–1378):
`c_{i,j}^{(ν)}(M)` is a polynomial in `M` of degree at most `2i+2j`, valid for all `M ≥ 0`.
Demand sheet: for every family `P` tied to the definition, clause (ii) of
`Stmt_prop_h13_nonvanishing`, word for word. -/
def Stmt_sub_h13_degree : Prop :=
  ∀ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    (∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) →
    (∀ (ν : Fin 2) (i j : ℕ), ∃ f : ℚ[X], f.natDegree ≤ 2 * i + 2 * j ∧
      ∀ M : ℕ, (P ν M).coeff (Finsupp.single 0 i + Finsupp.single 1 j) / 4 ^ M =
        f.eval (M : ℚ))

/-- Frozen sub-statement of Proposition 6.8(iii) (paper.tex l.1191–1201, proof l.1380–1392):
regularity, nonvanishing and the valuation (6.3) of `H_M(c⋆,μ,d_ν)`, and `H_M(c⋆,μ,d) ≢ 0`.
Demand sheet: for every family `P` tied to the definition and satisfying clause (i) (used at
l.1385–1387), the fourth clause of `Stmt_prop_h13_nonvanishing`, word for word. -/
def Stmt_sub_h13_valuation : Prop :=
  ∀ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    (∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) →
    (∀ ν M, 1 ≤ M →
      (∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n) ∧
      MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
        MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
      MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M) →
    (∀ p p' : ℕ, 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → ∀ (M : ℕ) (m : ℤ), 1 ≤ M →
      let cs : ℚ := 1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p')
      let μ : ℚ := ((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')
      (gram cs μ M).det ≠ 0 →
        HpolyD cs μ M ≠ 0 ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ p' → ∀ ν : Fin 2,
          let dν : ℚ := if ν = 0 then -1 + 2 * p / p' else 2 + 2 * p / p'
          (Hrat cs dν M).denom.eval μ ≠ 0 ∧
          RatFunc.eval (RingHom.id ℚ) μ (Hrat cs dν M) ≠ 0 ∧
          padicValRat ℓ (RatFunc.eval (RingHom.id ℚ) μ (Hrat cs dν M)) =
            -(padicValNat ℓ M.factorial : ℤ) - (M : ℤ) * (padicValNat ℓ p' : ℤ)
              - ∑ u ∈ Finset.Icc 1 M,
                  (padicValInt ℓ (m ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ))

/-- Frozen sub-statement of Proposition 6.8(iii) (paper.tex l.1201–1210, proof l.1392–1416):
the `ℓ`-adic Lipschitz bound (6.4).
Demand sheet: for every family `P` tied to the definition and satisfying clauses (i) and (ii)
(used at l.1393–1396), the fifth clause of `Stmt_prop_h13_nonvanishing`, word for word. -/
def Stmt_sub_h13_lipschitz : Prop :=
  ∀ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    (∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) →
    (∀ ν M, 1 ≤ M →
      (∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n) ∧
      MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
        MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
      MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M) →
    (∀ (ν : Fin 2) (i j : ℕ), ∃ f : ℚ[X], f.natDegree ≤ 2 * i + 2 * j ∧
      ∀ M : ℕ, (P ν M).coeff (Finsupp.single 0 i + Finsupp.single 1 j) / 4 ^ M =
        f.eval (M : ℚ)) →
    (∀ (p' ℓ : ℕ) [Fact ℓ.Prime], 2 ≤ p' → ℓ ≠ 2 → ℓ ∣ p' →
      ∀ (t₀ Y₁ Y₂ : Padic ℓ) (M₁ M₂ e : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
        ‖t₀‖ ≤ (ℓ : ℝ) ^ (-(padicValNat ℓ p' : ℤ)) →
        ‖Y₁‖ ≤ (ℓ : ℝ) ^ (-((padicValNat ℓ p' : ℤ) + 1)) →
        ‖Y₂‖ ≤ (ℓ : ℝ) ^ (-((padicValNat ℓ p' : ℤ) + 1)) →
        ((ℓ : ℤ) ^ e ∣ (M₁ : ℤ) - M₂) →
        ‖Y₁ - Y₂‖ ≤ (ℓ : ℝ) ^ (-((e : ℤ) + (padicValNat ℓ p' : ℤ))) →
          let ev : Fin 2 → ℕ → Padic ℓ → Padic ℓ := fun ν M Y =>
            MvPolynomial.aeval (![t₀, Y] : Fin 2 → Padic ℓ) (P ν M)
          ‖ev 0 M₁ Y₁‖ = 1 ∧ ‖ev 1 M₁ Y₁‖ = 1 ∧ ‖ev 0 M₂ Y₂‖ = 1 ∧ ‖ev 1 M₂ Y₂‖ = 1 ∧
          ‖ev 0 M₁ Y₁ * ev 1 M₂ Y₂ - ev 1 M₁ Y₁ * ev 0 M₂ Y₂‖ ≤
            (ℓ : ℝ) ^ (-((e : ℤ) + (padicValNat ℓ p' : ℤ))))

/-- Proposition 6.8 from its four open sub-statements; the polynomial clause and the values at
`t = 0` are proved. -/
theorem prop_h13_nonvanishing_of_subs (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (h1 : Stmt_sub_h13_integral) (h2 : Stmt_sub_h13_degree) (h3 : Stmt_sub_h13_valuation)
    (h4 : Stmt_sub_h13_lipschitz) : Stmt_prop_h13_nonvanishing := by
  obtain ⟨P, hP⟩ := sub_h13_polynomial hK hH
  have hi :
      (∀ ν M, 1 ≤ M →
        (∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n) ∧
        MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
          MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
        MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M) :=
    fun ν M hM => ⟨h1 P hP ν M hM, sub_h13_values P hP ν M hM⟩
  exact ⟨P, hP, hi, h2 P hP, h3 P hP hi, h4 P hP hi (h2 P hP)⟩

end Virasoro
