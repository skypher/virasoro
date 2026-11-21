import Virasoro.Sphere.Saddle
import Virasoro.Sphere.Cited

/-!
# Frozen statements: sphere paper Lemmas 3.4, 3.6, 3.7
(`lem:saddle`, `lem:ext-exponents`, `lem:central-charge`)

Awaiting statement review.  The objects are in `Sphere/Saddle.lean`.  Reading recorded in
`Stmt_lem_lambda_expansion`: the `𝓘₀`, `Φ_c^raw` of Lemma 3.3 are those its proof constructs,
`I0def` and `PhiCraw` at the saddle point; `S̃^{(1)}`, `S_c^{(2)}`, `S_1^{(2)}`, `S_2^{(2)}` are
the series with the property `IsExpansionData`.
-/

namespace Virasoro.Sphere

open Finset

/-- Lemma 3.4 (`lem:saddle`), sphere/paper.tex l.713–734.
(i) The functions (3.4) solve the order-`λ⁰` PDE of (3.3), and
`-½∑_{n=1}^{k-1} B_{n,k-n} = (k-1)/16` for every `k ≥ 1`.
(ii) With `p(w) = 4w/(1+w)²`, `t_n(σ) = [w^{-n}]∑_m σ_m p(w)^{-m}`,
`g(w) = 2i∑_n n t_n w^n`: `S^{(0)}(σ) = -4i∑_n (-1)^{n-1} t_n - 2∑_n n t_n²`.
(iii) `Ω(x;z) = 1 + ∑_m a_m(z) x^m + ∑_m a_m(z)(z/x)^m`; the saddle point is
`σ_{*,m} = i a_m(z) z^m/m`; and `𝓘₀ = log(16q(z)/z)`, `1 - g_*(1) = θ₄(q(z))⁻²`,
`1 - g_*(-1) = θ₃(q(z))⁻²`.

Demand sheet.
- (i) every `k ≥ 1` (l.716–718): `pdeZero k S0 = 0`, the order-`λ⁰` part of (3.3) for
  `S = S^{(0)}`;
- (ii) the sums over `n ≥ 1` (l.723) are taken coefficient by coefficient: `t_n` only involves
  `σ_m` with `m ≥ n`, so the coefficient of `σ^α` only involves `n` up to the largest index of
  a variable of `σ^α`;
- (iii) `a_m(z)` is the coefficient of `x^m` of the Laurent expansion (`OmegaCoef`); the
  expansion claim (l.725–727) is: constant coefficient `1` and coefficient `a_m(z) z^m` of
  `x^{-m}`;
- (iii) "the exact saddle point" (l.727–728): `σ_*` with some `σ̄` is a saddle point, and
  every saddle point has `σ = σ_*` (class as in Lemma 3.3(iii));
- (iii) values (l.729–733) at any saddle point `(σ, σ̄)`: `𝓘₀` is `I0def`, `g_*(±1)` is the
  substitution of `σ` into the linear series `g(±1) = 2i∑_n n(±1)^n t_n`;
- `q(z)`: any series `Q` with zero constant term and `z(Q(z)) = z`, as in Lemma 3.5;
  `16q(z)/z` is the series `R` with `16 Q = z R`; `log` is the substitution into
  `log(1+x)`. -/
def Stmt_lem_saddle : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    pdeZero k S0 = 0 ∧
    -(1 / 2 : ℚ) * ∑ n ∈ Icc 1 (k - 1), Bcoef n (k - n) = ((k : ℚ) - 1) / 16) ∧
  (S0 = fun α : ℕ+ →₀ ℕ =>
    MvPowerSeries.coeff α
      (∑ n ∈ Icc 1 (α.support.sup fun m => (m : ℕ)),
        ((-4 * Complex.I * (-1) ^ (n - 1)) • tlin n - (2 * (n : ℂ)) • tlin n ^ 2))) ∧
  (OmegaCoef 0 = 1 ∧
    ∀ m : ℕ, 1 ≤ m → OmegaCoef (-(m : ℤ)) = aSer m * (PowerSeries.X : PowerSeries ℚ) ^ m) ∧
  (∃ σb : ℕ+ → PowerSeries ℂ, IsSaddle sigmaStar σb) ∧
  ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb →
    σ = sigmaStar ∧
    ∀ Q : PowerSeries ℂ, PowerSeries.constantCoeff Q = 0 → (zq ℂ).subst Q = PowerSeries.X →
      (∀ R : PowerSeries ℂ, (16 : ℂ) • Q = PowerSeries.X * R →
        I0def σ σb = (PowerSeries.log ℂ).subst (R - 1)) ∧
      1 - MvPowerSeries.subst σ (gAt 1) = (((th4 ℂ).subst Q) ^ 2)⁻¹ ∧
      1 - MvPowerSeries.subst σ (gAt (-1)) = (((th3 ℂ).subst Q) ^ 2)⁻¹

/-- Lemma 3.6 (`lem:ext-exponents`), sphere/paper.tex l.974–978.
`S_2^{(2)}(σ) = 2 log(1 - g(1))`, `S_1^{(2)}(σ) = 2 log(1 - g(-1))`, and hence
`Φ₂(z) = -4 log θ₄(q(z))`, `Φ₁(z) = -4 log θ₃(q(z))`.

Demand sheet.
- `S_1^{(2)}, S_2^{(2)}` are those of Lemma 3.3(ii): any series with `IsExpansionData`;
- `g(±1)`: the linear series `gAt (±1)`; `log(1 - g)` is the substitution of `-g` into
  `log(1+x)`;
- `Φ_j = S_j^{(2)}(σ_*)` (Lemma 3.3(iii)) at any saddle point; `q(z)` as in Lemma 3.5;
  `log θ_j(q(z))` is the substitution of `θ_j(q(z)) - 1` into `log(1+x)`. -/
def Stmt_lem_ext_exponents : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    S22 = (2 : ℂ) • (PowerSeries.log ℂ).subst (-gAt 1) ∧
    S21 = (2 : ℂ) • (PowerSeries.log ℂ).subst (-gAt (-1)) ∧
    ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb →
      ∀ Q : PowerSeries ℂ, PowerSeries.constantCoeff Q = 0 → (zq ℂ).subst Q = PowerSeries.X →
        MvPowerSeries.subst σ S22 = (-4 : ℂ) • (PowerSeries.log ℂ).subst ((th4 ℂ).subst Q - 1) ∧
        MvPowerSeries.subst σ S21 = (-4 : ℂ) • (PowerSeries.log ℂ).subst ((th3 ℂ).subst Q - 1)

/-- Lemma 3.7 (`lem:central-charge`), sphere/paper.tex l.1013–1020.
`exp(Φ_c^raw(z) - 𝓘₀(z)) = ∏_{m≥1}(1 - q(z)^{2m})^{12} = (z/(16q(z)))(1-z)θ₃(q(z))^{12}`.

Demand sheet.
- `Φ_c^raw`, `𝓘₀`: `PhiCraw`, `I0def` at any saddle point, for any `S̃^{(1)}, S_c^{(2)}` with
  `IsExpansionData` (reading recorded in `Stmt_lem_lambda_expansion`);
- `exp` is the substitution into the exponential series;
- the product is `etaSqPow 12` substituted at `q(z)`; `q(z)` as in Lemma 3.5; `z/(16q(z))` is
  the inverse of the series `R` with `16 Q = z R`. -/
def Stmt_lem_central_charge : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb →
      ∀ Q : PowerSeries ℂ, PowerSeries.constantCoeff Q = 0 → (zq ℂ).subst Q = PowerSeries.X →
        (PowerSeries.exp ℂ).subst (PhiCraw S1t S2c σ σb - I0def σ σb) =
          ((etaSqPow 12).map (algebraMap ℚ ℂ)).subst Q ∧
        ∀ R : PowerSeries ℂ, (16 : ℂ) • Q = PowerSeries.X * R →
          (PowerSeries.exp ℂ).subst (PhiCraw S1t S2c σ σb - I0def σ σb) =
            R⁻¹ * (1 - PowerSeries.X) * ((th3 ℂ).subst Q) ^ 12

end Virasoro.Sphere
