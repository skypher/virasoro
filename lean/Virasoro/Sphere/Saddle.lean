import Virasoro.Sphere.Fock
import Virasoro.Sphere.Statements.Sec3b
import Virasoro.Local
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Objects of sphere paper Lemmas 3.3, 3.4, 3.6, 3.7 (`sphere/paper.tex` l.506–1020)

* the series `S(σ;λ) = λ⁻² log F(λσ;λ)` over `ℂ(λ)` and its expansion coefficients `S^{(r)}`
  at `λ = ∞`;
* the quadratic `S^{(0)}` of (3.4), the involution `ι`, the derivation `L_k^{(0)}` and the
  order-`λ⁰` equation of (3.3);
* the saddle-point equations, the saddle value `𝓘₀`, the Gaussian term `Ψ₁` and
  `Φ_c^raw = 2 S_c^{(2)}(σ_*) + Ψ₁` (l.662–708);
* the linear forms `t_n(σ)`, `g(±1)` and the coefficients `a_m(z)` of `Ω(x;z)` (l.720–733).

Formal series in the variables `σ_m` (`m ≥ 1`) are `MvPowerSeries ℕ+ K`; series in `z` are
`PowerSeries ℂ`.  A family `σ : ℕ+ → PowerSeries ℂ` can be substituted into a series in the
`σ_m` when `MvPowerSeries.HasSubst σ` holds: every `σ_m` has zero constant term and, for every
`k`, only finitely many `σ_m` have a nonzero coefficient of `z^k`.
-/

namespace Virasoro.Sphere

open Finset

/-! ### The `λ⁻¹`-expansion -/

/-- The formal series `F = ∑_m F_m` in `K[[u₁,u₂,…]]` of a sequence of Fock vectors: the
coefficient of `u^α` is read off from `F_m` with `m` the level of `u^α`. -/
noncomputable def wardSeries {K : Type*} [Field K] (F : ℕ → MvPolynomial ℕ+ K) :
    MvPowerSeries ℕ+ K :=
  fun α => MvPolynomial.coeff α (F (Finsupp.weight fockWeight α))

/-- `S(σ;λ) = λ⁻² log F(λσ;λ)` over `ℂ(λ)` (sphere/paper.tex l.509–510): the coefficient of
`σ^α` is `λ^{|α|-2}` times that of `u^α` in `log F`, with `|α|` the polynomial degree. -/
noncomputable def Slam (F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ)) : MvPowerSeries ℕ+ (RatFunc ℂ) :=
  fun α => (RatFunc.X : RatFunc ℂ) ^ ((α.degree : ℤ) - 2) *
    MvPowerSeries.coeff α ((PowerSeries.log (RatFunc ℂ)).subst (wardSeries F - 1))

/-- `r(1/t)` for a rational function `r(λ)`. -/
noncomputable def atInfty (r : RatFunc ℂ) : RatFunc ℂ :=
  Polynomial.aeval (RatFunc.X⁻¹ : RatFunc ℂ) r.num /
    Polynomial.aeval (RatFunc.X⁻¹ : RatFunc ℂ) r.denom

/-- The coefficient of `λ^{-n}` in the Laurent expansion of `r(λ)` at `λ = ∞`: the coefficient
of `t^n` in the expansion of `r(1/t)` at `t = 0`. -/
noncomputable def inftyCoeff (r : RatFunc ℂ) (n : ℤ) : ℂ := lcoeff (atInfty r) 0 n

/-- `r(λ)` is regular at `λ = ∞`. -/
def RegularAtInfty (r : RatFunc ℂ) : Prop := ∀ n : ℤ, n < 0 → inftyCoeff r n = 0

/-- `S^{(r)}(σ)`, the coefficient of `λ^{-r}` of `S(σ;λ)`, monomial by monomial
(sphere/paper.tex l.515). -/
noncomputable def Sord (F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ)) (r : ℕ) : MvPowerSeries ℕ+ ℂ :=
  fun α => inftyCoeff (Slam F α) r

/-- The value at `λ = lam` of a Fock vector with coefficients in `ℂ(λ)`, coefficient by
coefficient. -/
noncomputable def specialize (lam : ℂ) (f : MvPolynomial ℕ+ (RatFunc ℂ)) : Fock :=
  ∑ α ∈ f.support, MvPolynomial.monomial α (RatFunc.eval (RingHom.id ℂ) lam (f.coeff α))

/-! ### `S^{(0)}`, `ι`, `L_k^{(0)}` -/

/-- `binom(-1/2,k)(-1)^k = [x^k](1-x)^{-1/2}`. -/
noncomputable def halfBinom (k : ℕ) : ℚ := gbinom (-1 / 2 : ℚ) k * (-1) ^ k

/-- `A_m = [p^m] A(p)`, `A(p) = -2i((1-p)^{-1/2} - 1)`, for `m ≥ 1` (equation (3.4)). -/
noncomputable def Acoef (m : ℕ) : ℂ := -2 * Complex.I * (halfBinom m : ℂ)

/-- The linear series `∑_m c_m σ_m`. -/
noncomputable def linSeries (c : ℕ → ℂ) : MvPowerSeries ℕ+ ℂ :=
  fun α => if α.degree = 1 then ∑ m ∈ α.support, c m else 0

/-- `S^{(0)}(σ) = ∑_m A_m σ_m + ∑_{m,n} B_{m,n} σ_m σ_n` (sphere/paper.tex l.519–525).  The
coefficient of `σ_m σ_n` is `B_{m,n} + B_{n,m}` for `m ≠ n` and `B_{m,m}` for `m = n`. -/
noncomputable def S0 : MvPowerSeries ℕ+ ℂ :=
  fun α =>
    if α.degree = 1 then ∑ m ∈ α.support, Acoef m
    else if α.degree = 2 then
      ∑ m ∈ α.support, ∑ n ∈ α.support,
        if α = Finsupp.single m 1 + Finsupp.single n 1 then (Bcoef m n : ℂ) else 0
    else 0

/-- Complex conjugation of the coefficients (`i ↦ -i` at real parameters). -/
noncomputable def conjSeries (T : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  MvPowerSeries.map (starRingEnd ℂ) T

/-- The involution `ι(i) = -i`, `ι(σ_m) = -σ_m` (sphere/paper.tex l.528–529). -/
noncomputable def iota (T : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  fun α => (-1) ^ α.degree * (starRingEnd ℂ) (T α)

/-- `∂/∂σ_n` for a natural number `n ≥ 1`. -/
noncomputable def pd (n : ℕ) (T : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  MvPowerSeries.pderiv ℂ n.toPNat' T

/-- `∑_{n≥1} n σ_n ∂_{σ_{n+k}} T`: the coefficient of `σ^α` is a sum over the variables of
`σ^α`. -/
noncomputable def shiftOp (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  fun α => ∑ n ∈ α.support,
    ((n : ℕ) : ℂ) * MvPowerSeries.coeff (α - Finsupp.single n 1) (pd ((n : ℕ) + k) T)

/-- `∑_{n≥1} n σ_n ∂_{σ_n} T`, which multiplies `σ^α` by its oscillator level. -/
noncomputable def levelOp (T : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  fun α => ((Finsupp.weight fockWeight α : ℕ) : ℂ) * T α

/-- The left side of the order-`λ⁰` part of (3.3) (sphere/paper.tex l.563–568 at `λ = ∞`):
`i∂_k S + ∑_n nσ_n(∂_{n+k}S - ∂_n S) - ¼∑_{n=1}^{k-1}(∂_n S)(∂_{k-n} S) - 1`. -/
noncomputable def pdeZero (k : ℕ) (S : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  Complex.I • pd k S + shiftOp k S - levelOp S
    - (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pd n S * pd (k - n) S - 1

/-- The derivation `L_k^{(0)} = i∂_{σ_k} + ∑_n nσ_n(∂_{σ_{n+k}} - ∂_{σ_n})
- ½∑_{n=1}^{k-1}(∂_{σ_n}S^{(0)})∂_{σ_{k-n}}` (sphere/paper.tex l.535–539). -/
noncomputable def L0 (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  Complex.I • pd k T + shiftOp k T - levelOp T
    - (1 / 2 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pd n S0 * pd (k - n) T

/-- The universal pieces of `S^{(1)}` and `S^{(2)}` (Lemma 3.3(ii)): for every `μ > 0` and
real `Δ₁, Δ₂`, the solution `F` over `ℂ(λ)` of the Ward equations has `S^{(1)} = μ S̃^{(1)}` and
`S^{(2)} = μ² S_c^{(2)} + (Δ₂ - 1/16) S_2^{(2)} + (Δ₁ - 1/16) S_1^{(2)}`.  The arguments are
`S̃^{(1)}`, `S_c^{(2)}`, `S_1^{(2)}`, `S_2^{(2)}`; they are determined by this property once a
solution `F` exists for three affinely independent parameter values. -/
def IsExpansionData (S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ) : Prop :=
  ∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ, ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
    IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F →
      Sord F 1 = (μ : ℂ) • S1t ∧
      Sord F 2 = (μ : ℂ) ^ 2 • S2c + ((Δ2 : ℂ) - 1 / 16) • S22 + ((Δ1 : ℂ) - 1 / 16) • S21

/-! ### The saddle point -/

/-- `f ∈ zℚ[[z]]`. -/
def InZQ (f : PowerSeries ℂ) : Prop :=
  ∃ g : PowerSeries ℚ, PowerSeries.constantCoeff g = 0 ∧ f = g.map (algebraMap ℚ ℂ)

/-- `f ∈ i·zℚ[[z]]`. -/
def InIZQ (f : PowerSeries ℂ) : Prop :=
  ∃ g : PowerSeries ℚ, PowerSeries.constantCoeff g = 0 ∧
    f = Complex.I • g.map (algebraMap ℚ ℂ)

/-- `(σ, σ̄)` is a saddle point of
`-2∑_m m z^{-m} σ_m σ̄_m + S^{(0)}(σ) + S̃^{(0)}(σ̄)` (sphere/paper.tex l.547–548, l.666–668):
both families can be substituted into series in the `σ_m`, and the stationarity equations
`-2m z^{-m} σ̄_m + A_m + 2∑_n B_{m,n} σ_n = 0`, `-2m z^{-m} σ_m - A_m + 2∑_n B_{m,n} σ̄_n = 0`
hold, multiplied by `z^m`.  (`S̃^{(0)}` has the coefficients `Ā_m = -A_m`, `B_{m,n}`.) -/
structure IsSaddle (σ σb : ℕ+ → PowerSeries ℂ) : Prop where
  hasSubst : MvPowerSeries.HasSubst σ
  hasSubst_bar : MvPowerSeries.HasSubst σb
  eq : ∀ m : ℕ+, (2 * ((m : ℕ) : ℂ)) • σb m =
    (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) *
      (PowerSeries.C (Acoef m) + 2 * MvPowerSeries.subst σ (linSeries fun n => (Bcoef m n : ℂ)))
  eq_bar : ∀ m : ℕ+, (2 * ((m : ℕ) : ℂ)) • σ m =
    (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) *
      (PowerSeries.C (-Acoef m) + 2 * MvPowerSeries.subst σb (linSeries fun n => (Bcoef m n : ℂ)))

/-- The saddle value `𝓘₀(z) = -2∑_m m z^{-m} σ_m σ̄_m + S^{(0)}(σ) + S̃^{(0)}(σ̄)`
(sphere/paper.tex l.694).  The coefficient of `z^k` in `z^{-m} σ_m σ̄_m` is that of `z^{k+m}`
in `σ_m σ̄_m`; at a saddle point `σ_m σ̄_m` is divisible by `z^{2m}`, so the sum over `m` is
finite. -/
noncomputable def I0def (σ σb : ℕ+ → PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k =>
      -2 * ∑ᶠ m : ℕ+, ((m : ℕ) : ℂ) * PowerSeries.coeff (k + (m : ℕ)) (σ m * σb m))
    + MvPowerSeries.subst σ S0 + MvPowerSeries.subst σb (conjSeries S0)

section Gaussian

variable (N : ℕ)

/-- `D⁻¹ = diag(1,…,1/N)` for `D = diag(1,…,N)`. -/
noncomputable def DinvMat : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  Matrix.diagonal fun i => PowerSeries.C (1 / (((i : ℕ) + 1 : ℕ) : ℂ))

/-- `M₁ = D⁻¹B^{(z)}`, `B^{(z)}_{m,n} = z^{m+n} B_{m,n}` (sphere/paper.tex l.644–646). -/
noncomputable def M1mat : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  Matrix.of fun i j =>
    PowerSeries.C ((Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) : ℂ) / (((i : ℕ) + 1 : ℕ) : ℂ)) *
      (PowerSeries.X : PowerSeries ℂ) ^ (((i : ℕ) + 1) + ((j : ℕ) + 1))

/-- `M₂ = D⁻¹B` (sphere/paper.tex l.646). -/
noncomputable def M2mat : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  Matrix.of fun i j =>
    PowerSeries.C ((Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) : ℂ) / (((i : ℕ) + 1 : ℕ) : ℂ))

/-- `Cov(U_m,U_n) = z^{m+n}·½(K₂₁M₂D⁻¹)_{m,n}`, `K₂₁ = (I - M₂M₁)⁻¹`, in the truncation to
modes `≤ N` (sphere/paper.tex l.656–661, with `U_m = z^m ξ_m`). -/
noncomputable def covUU : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  Matrix.of fun i j =>
    (PowerSeries.X : PowerSeries ℂ) ^ (((i : ℕ) + 1) + ((j : ℕ) + 1)) *
      (PowerSeries.C (1 / 2 : ℂ) *
        (((1 - M2mat N * M1mat N)⁻¹ * M2mat N * DinvMat N) i j))

/-- `Cov(U_m,V_n) = z^m·½(K₂₁D⁻¹)_{m,n}`. -/
noncomputable def covUV : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  Matrix.of fun i j =>
    (PowerSeries.X : PowerSeries ℂ) ^ ((i : ℕ) + 1) *
      (PowerSeries.C (1 / 2 : ℂ) * (((1 - M2mat N * M1mat N)⁻¹ * DinvMat N) i j))

/-- `Cov(V_m,V_n) = ½(K₁₂M₁D⁻¹)_{m,n}`, `K₁₂ = (I - M₁M₂)⁻¹`. -/
noncomputable def covVV : Matrix (Fin N) (Fin N) (PowerSeries ℂ) :=
  Matrix.of fun i j =>
    PowerSeries.C (1 / 2 : ℂ) * (((1 - M1mat N * M2mat N)⁻¹ * M1mat N * DinvMat N) i j)

end Gaussian

/-- `Ψ₁(z)`: half the covariance contraction of the gradient of `S̃^{(1)}` at the saddle point
(sphere/paper.tex l.698–706), that is half the variance of
`∑_m (∂_{σ_m}S̃^{(1)}(σ_*) U_m + ∂_{σ̄_m}S̃^{(1)}_conj(σ̄_*) V_m)` in the centered Gaussian for
`(U,V)`.  The coefficient of `z^N` is computed with the modes `m ≤ N`, as in the paper's
argument modulo `z^{N+1}`. -/
noncomputable def Psi1 (S1t : MvPowerSeries ℕ+ ℂ) (σ σb : ℕ+ → PowerSeries ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk fun N =>
    PowerSeries.coeff N
      (PowerSeries.C (1 / 2 : ℂ) * ∑ i : Fin N, ∑ j : Fin N,
        (MvPowerSeries.subst σ (pd ((i : ℕ) + 1) S1t) *
            MvPowerSeries.subst σ (pd ((j : ℕ) + 1) S1t) * covUU N i j
          + 2 * (MvPowerSeries.subst σ (pd ((i : ℕ) + 1) S1t) *
            MvPowerSeries.subst σb (pd ((j : ℕ) + 1) (conjSeries S1t)) * covUV N i j)
          + MvPowerSeries.subst σb (pd ((i : ℕ) + 1) (conjSeries S1t)) *
            MvPowerSeries.subst σb (pd ((j : ℕ) + 1) (conjSeries S1t)) * covVV N i j))

/-- `Φ_c^raw(z) = 2 S_c^{(2)}(σ_*(z)) + Ψ₁(z)` (sphere/paper.tex l.707). -/
noncomputable def PhiCraw (S1t S2c : MvPowerSeries ℕ+ ℂ) (σ σb : ℕ+ → PowerSeries ℂ) :
    PowerSeries ℂ :=
  2 * MvPowerSeries.subst σ S2c + Psi1 S1t σ σb

/-! ### The half-pillow variables -/

/-- `[w^{-n}] p(w)^{-m}` for `p(w) = 4w/(1+w)²`: `p(w)^{-m} = (1+w)^{2m}/(4w)^m`, whose
coefficient of `w^{-n}` is `binom(2m, m-n)/4^m` for `n ≤ m` and `0` for `n > m`. -/
noncomputable def tcoef (n m : ℕ) : ℂ :=
  if n ≤ m then (Nat.choose (2 * m) (m - n) : ℂ) / 4 ^ m else 0

/-- `t_n(σ) = [w^{-n}] ∑_m σ_m p(w)^{-m}` (sphere/paper.tex l.721). -/
noncomputable def tlin (n : ℕ) : MvPowerSeries ℕ+ ℂ := linSeries fun m => tcoef n m

/-- `g(s) = 2i ∑_{n≥1} n t_n(σ) s^n` at `s = ±1` (sphere/paper.tex l.722), a linear series in
`σ`: the coefficient of `σ_m` is the finite sum over `n ≤ m`. -/
noncomputable def gAt (s : ℂ) : MvPowerSeries ℕ+ ℂ :=
  linSeries fun m => 2 * Complex.I * ∑ n ∈ Icc 1 m, (n : ℂ) * s ^ n * tcoef n m

/-- The coefficient of `x^e` (`e ∈ ℤ`) in the Laurent expansion on `|z| < |x| < 1` of
`Ω(x;z) = (₂F₁(½,½;1;z) √(1-x) √(1-z/x))⁻¹` (sphere/paper.tex l.725–726): the product of the
binomial series of `(1-x)^{-1/2}` and `(1-z/x)^{-1/2}` has the coefficient
`[x^{e+l}](1-x)^{-1/2} · [y^l](1-y)^{-1/2}` of `x^e z^l`. -/
noncomputable def OmegaCoef (e : ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun l : ℕ =>
      if 0 ≤ e + l then halfBinom (e + l).toNat * halfBinom l else 0) * hyp2F1⁻¹

/-- `a_m(z)`, the coefficient of `x^m` in `Ω(x;z)`, `m ≥ 1`. -/
noncomputable def aSer (m : ℕ) : PowerSeries ℚ := OmegaCoef m

/-- `σ_{*,m}(z) = i a_m(z) z^m / m` (sphere/paper.tex l.728). -/
noncomputable def sigmaStar (m : ℕ+) : PowerSeries ℂ :=
  Complex.I • ((1 / ((m : ℕ) : ℂ)) •
    ((aSer m).map (algebraMap ℚ ℂ) * (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ)))

end Virasoro.Sphere
