import Virasoro.Sphere.Saddle
import Virasoro.Sphere.Statements.Sec3a
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Frozen statement: sphere paper Lemma 3.3 (`lem:lambda-expansion`)

Awaiting statement review.  The objects are in `Sphere/Saddle.lean`.
-/

namespace Virasoro.Sphere

/-- Lemma 3.3 (`lem:lambda-expansion`), sphere/paper.tex l.506–557.  Fix `μ > 0` and real
`Δ₁,…,Δ₄`; `S(σ;λ) = λ⁻² log F(λσ;λ)`.
(i) The coefficients of `S_m(σ;λ)` are rational functions of `λ`, regular at `λ = ∞`, giving
`S = ∑_r λ^{-r} S^{(r)}`.
(ii) `S^{(0)} = ∑ A_m σ_m + ∑ B_{m,n} σ_m σ_n` with (3.4), independent of `(μ,Δ₁,Δ₂)`;
`S^{(1)} = μ S̃^{(1)}`, independent of `(Δ₁,Δ₂)` and `ι`-odd;
`S^{(2)} = μ² S_c^{(2)} + (Δ₂ - 1/16) S_2^{(2)} + (Δ₁ - 1/16) S_1^{(2)}` is `ι`-even, with
`L_k^{(0)} S_2^{(2)} = k` and `L_k^{(0)} S_1^{(2)} = -1` for all `k ≥ 1`.
(iii) There are `𝓘₀, Φ_c^raw, Φ₁, Φ₂ ∈ zℚ[[z]]`, with `Φ_j = S_j^{(2)}(σ_*)` at the unique
saddle point `σ_* ∈ izℚ[[z]]^ℕ`, such that coefficient by coefficient in `z` the limit (3.5)
holds.

Demand sheet.
- `μ > 0`, `Δ_i` real (l.508); (i) and (ii) concern the `F` for `(Δ₁,Δ₂)`, (iii) all four;
- "rational functions of `λ`" (l.513–514): the Ward equations have exactly one solution `F`
  over `ℂ(λ)` (parameters `μ, Δ₁, Δ₂` constant, `λ = X`); at every real `λ > 0` its
  coefficients have no pole and their values form a solution of the Ward equations over `ℂ`,
  which is the `F` of Lemma 3.2(ii) by the uniqueness stated there;
- "regular at `λ = ∞`" (l.514): every coefficient of `S` has no negative power of `t` in the
  expansion of `r(1/t)` at `t = 0`; `S^{(r)}` is the coefficient of `t^r`, so that
  `S = ∑_r λ^{-r} S^{(r)}` is the expansion at `∞` of each coefficient (l.515);
- (ii) the universal series `S̃^{(1)}, S_c^{(2)}, S_1^{(2)}, S_2^{(2)}` do not depend on
  `(μ,Δ₁,Δ₂)`: they are quantified outside `μ, Δ₁, Δ₂` (`IsExpansionData`);
  `ι`-oddness is stated for `S̃^{(1)}` and `ι`-evenness for `S^{(2)}` at each real
  `(μ,Δ₁,Δ₂)` (l.527–532); `L_k^{(0)}` equations for all `k ≥ 1` (l.533–534);
- (iii) `𝓘₀, Φ_c^raw, Φ₁, Φ₂` existential, as printed (l.541–542), outside `μ, Δ_i`;
- (iii) saddle point (l.543–545): `IsSaddle`, in the class of pairs of families that can be
  substituted (`MvPowerSeries.HasSubst`: zero constant terms, and for each `k` finitely many
  members with a nonzero coefficient of `z^k`), where the stationarity equations multiplied
  by `z^m` are defined coefficientwise; existence, uniqueness in that class, and
  `σ_{*,m} ∈ izℚ[[z]]`;
- (iii) the limit (l.546–553) for every coefficient of `z`, along real `λ → +∞`; `ℬ_j` is the
  value of the rational function at `Δ = λ² + μ²`; `e^{-λ²𝓘₀}` and the exponential on the
  right are substitutions into the exponential series; the determinant is `detInvSqrt` of
  Lemma 3.5.
Reading recorded for Lemmas 3.4(iii) and 3.7: the `𝓘₀`, `Φ_c^raw` of this lemma are those its
proof constructs (l.694, l.707), `I0def` and `PhiCraw` at the saddle point. -/
def Stmt_lem_lambda_expansion : Prop :=
  (∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ,
    (∃! F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F) ∧
    ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F →
      (∀ lam : ℝ, 0 < lam →
        (∀ (m : ℕ) (α : ℕ+ →₀ ℕ), ((F m).coeff α).denom.eval (lam : ℂ) ≠ 0) ∧
        IsWardSeries (μ : ℂ) (lam : ℂ) (Δ1 : ℂ) (Δ2 : ℂ) fun m => specialize (lam : ℂ) (F m)) ∧
      (∀ α : ℕ+ →₀ ℕ, RegularAtInfty (Slam F α)) ∧
      Sord F 0 = S0 ∧
      iota (Sord F 2) = Sord F 2) ∧
  ∃ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ,
    IsExpansionData S1t S2c S21 S22 ∧
    iota S1t = -S1t ∧
    (∀ k : ℕ, 1 ≤ k → L0 k S22 = MvPowerSeries.C (k : ℂ) ∧ L0 k S21 = -1) ∧
    ∃ I0 Φc Φ1 Φ2 : PowerSeries ℂ, InZQ I0 ∧ InZQ Φc ∧ InZQ Φ1 ∧ InZQ Φ2 ∧
      ∃ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb ∧
        (∀ σ' σb' : ℕ+ → PowerSeries ℂ, IsSaddle σ' σb' → σ' = σ ∧ σb' = σb) ∧
        (∀ m : ℕ+, InIZQ (σ m)) ∧
        Φ1 = MvPowerSeries.subst σ S21 ∧ Φ2 = MvPowerSeries.subst σ S22 ∧
        ∀ μ : ℝ, 0 < μ → ∀ (Δe : Fin 4 → ℝ) (n : ℕ),
          Filter.Tendsto
            (fun lam : ℝ => PowerSeries.coeff n
              ((PowerSeries.exp ℂ).subst (PowerSeries.C (-(lam : ℂ) ^ 2) * I0) *
                PowerSeries.mk fun j =>
                  RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
                    (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) j)))
            Filter.atTop
            (nhds (PowerSeries.coeff n
              (detInvSqrt.map (algebraMap ℚ ℂ) *
                (PowerSeries.exp ℂ).subst
                  ((μ : ℂ) ^ 2 • Φc + ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • Φ1 +
                    ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • Φ2))))

end Virasoro.Sphere
