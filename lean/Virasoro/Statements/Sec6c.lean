import Virasoro.Statements.Sec5c
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Frozen statements: Section 6 of `paper.tex` at 70bac53, Propositions 6.8 and 6.9
-/

namespace Virasoro

open Polynomial

/-- `M! t^{2M} ∏_{u=1}^M (2Δ - 2h_{u,1}(b)) H_M(c(b),Δ,d_ν)` as a rational function of `Δ` over
`ℚ(t)`, `t = b²` (paper Proposition 6.8), with `d₁ = h_{1,3}(b) = -1 - 2/t` for `ν = 0` and
`d₂ = h_{1,-3}(b) = 2 - 2/t` for `ν = 1`. -/
noncomputable def clearedH (ν : Fin 2) (M : ℕ) : RatFunc (RatFunc ℚ) :=
  (M.factorial : RatFunc (RatFunc ℚ)) * RatFunc.C (RatFunc.X : RatFunc ℚ) ^ (2 * M) *
    (∏ u ∈ Finset.Icc 1 M,
      (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ)))) *
    Hrat (cT (RatFunc.X : RatFunc ℚ))
      (if ν = 0 then -1 - 2 / (RatFunc.X : RatFunc ℚ) else 2 - 2 / (RatFunc.X : RatFunc ℚ)) M

/-- Proposition 6.8 (`prop:h13-nonvanishing`), paper.tex l.1178–1212.  Put `t = b²`,
`d₁ = h_{1,3}(b)`, `d₂ = h_{1,-3}(b)`, `P_0^{(ν)} = 1`, and
`P_M^{(ν)}(t,Y) = M! t^{2M} ∏_{u=1}^M (2Δ - 2h_{u,1}(b)) H_M(c(b),Δ,d_ν)|_{Δ=Y/t²}`.
(i) `P_M^{(ν)} ∈ ℤ[1/2][t,Y]`, `P_M^{(2)}(0,Y) = P_M^{(1)}(0,Y)`, `P_M^{(ν)}(0,0) = 4^M`.
(ii) `c_{i,j}^{(ν)}(M) = [t^i Y^j](P_M^{(ν)}/4^M)` is a polynomial in `M` of degree at most
`2i+2j`, valid for all `M ≥ 0`.
(iii) For coprime `p, p' ≥ 2`, `b⋆² = -p'/p`, an odd prime `ℓ ∣ p'` with `a = v_ℓ(p')`, `M ≥ 1`
and `μ = (m² - (p'-p)²)/(4pp')` with `det G_M(c⋆,μ) ≠ 0`: `H_M(c⋆,μ,d_ν)` is regular and nonzero
with `v_ℓ(H_M(c⋆,μ,d_ν)) = -v_ℓ(M!) - Ma - ∑_{u=1}^M v_ℓ(m² - (p'u-p)²)`; in particular
`H_M(c⋆,μ,d) ≢ 0` in `ℚ[d]` for every coprime pair; and the `ℓ`-adic Lipschitz bound (6.4).

Demand sheet.
- `P ν M` is a polynomial in `(t, Y)` over `ℚ` (variables `0 ↦ t`, `1 ↦ Y`), tied to the
  definition by `P(t, t²Δ) = clearedH ν M` in `ℚ(t)(Δ)`; `t` and `t²Δ` are algebraically
  independent, so this determines `P ν M` (l.1182–1183); `ν = 0, 1` stand for `ν = 1, 2`;
- (i) for `M ≥ 1`: coefficients in `ℤ[1/2]` (each is an integer over a power of `2`);
  equality of the two polynomials at `t = 0` as polynomials in `Y`; value `4^M` at `(0,0)`
  (l.1185–1187);
- (ii) for all `i, j ≥ 0`, both `ν`: a single polynomial `f` in `M` over `ℚ`, degree at most
  `2i+2j`, valid for all `M ≥ 0` (l.1188–1190);
- (iii) all quantities are rational: `c⋆ = 1 - 6(p'-p)²/(pp')`, `μ`, and
  `d_ν(b⋆) = -1 + 2p/p'`, `2 + 2p/p'` (from `t⋆ = -p'/p`); `m ∈ ℤ`, `M ≥ 1`, hypothesis
  `det G_M(c⋆,μ) ≠ 0`; regular: the reduced denominator of `H_M` does not vanish at `μ`;
  the valuation identity uses `padicValRat`, `padicValNat`, `padicValInt` (l.1191–1199);
- "in particular": `H_M(c⋆,μ,·) ≠ 0` as a polynomial in `d` (`HpolyD`), for every coprime pair
  `p, p' ≥ 2`, without the prime (l.1200–1201);
- (6.4): `t₀, Y₁, Y₂ ∈ ℚ_ℓ` with `v_ℓ(t₀) ≥ a`, `v_ℓ(Y_i) ≥ a+1`, `M₁, M₂ ≥ 1`, `e ≥ 0`,
  `v_ℓ(M₁-M₂) ≥ e` (as `ℓ^e ∣ M₁ - M₂`), `v_ℓ(Y₁-Y₂) ≥ e+a`; `v_ℓ(x) ≥ n` is written
  `‖x‖ ≤ ℓ^{-n}`.  The quotient is not formed: the four values are `ℓ`-adic units (stated),
  and the bound is on `P^{(1)}_{M₁}(t₀,Y₁) P^{(2)}_{M₂}(t₀,Y₂) -
  P^{(2)}_{M₁}(t₀,Y₁) P^{(1)}_{M₂}(t₀,Y₂)` (l.1201–1210). -/
def Stmt_prop_h13_nonvanishing : Prop :=
  ∃ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    (∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) ∧
    (∀ ν M, 1 ≤ M →
      (∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n) ∧
      MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
        MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
      MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M) ∧
    (∀ (ν : Fin 2) (i j : ℕ), ∃ f : ℚ[X], f.natDegree ≤ 2 * i + 2 * j ∧
      ∀ M : ℕ, (P ν M).coeff (Finsupp.single 0 i + Finsupp.single 1 j) / 4 ^ M =
        f.eval (M : ℚ)) ∧
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
                  (padicValInt ℓ (m ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ)) ∧
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

/-- Proposition 6.9 (`prop:two-term-criteria`), paper.tex l.1419–1426.  In the setting of
Theorem 5.9, let `max(ℓ⁺_k, ℓ⁻_k) < N < ℓ_{k+1}` and let `P_N(d)` be the right side of (5.1).
Then `P_N(d) ≢ 0`, and `H_N(c⋆,Δ,d)` has a pole of order exactly `k` at `Δ = λ`.

Demand sheet.
- `MinimalSetting`, a family as in Theorem 5.8, coordinates `xp`, `xm` (l.1421);
- `k ≥ 1`, strict inequalities `max(ℓ⁺_k, ℓ⁻_k) < N < ℓ_{k+1}` (l.1422);
- `P_N` is the sum of both `topTerm`s, an element of `ℂ(d)`; nonvanishing there (l.1423);
- pole order: identity `= k`, `d` indeterminate (l.1424–1425). -/
def Stmt_prop_two_term_criteria : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → max (ellPlus p p' r s k) (ellMinus p p' r s k) < N →
        N < ellMin p p' r s (k + 1) →
        ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            topTerm (kacC b) (kacH r s b) N (ellPlus p p' r s k) k xp +
                topTerm (kacC b) (kacH r s b) N (ellMinus p p' r s k) k xm ≠ 0 ∧
            poleOrder (HN (kacC b) N) (pt (kacH r s b)) = k

end Virasoro
