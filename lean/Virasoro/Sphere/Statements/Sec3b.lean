import Virasoro.Sphere.Defs
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Frozen statement: sphere paper Lemma 3.5 (`lem:bergman-det`)

Awaiting statement review.  New objects: the coefficients `B_{m,n}` of the generating function
`B(p,q)` of equation (3.4), the matrix `M(z)_{m,n} = z^m B_{m,n}/m`, the formal series
`det(I - M(z)²)^{-1/2}` and `₂F₁(1/2,1/2;1;z)`.
-/

namespace Virasoro.Sphere

open PowerSeries

/-- `√(1 - x_i) = ∑_k binom(1/2,k) (-x_i)^k` as a power series in the two variables
`x₀ = p`, `x₁ = q`. -/
noncomputable def sqrtOneSub (i : Fin 2) : MvPowerSeries (Fin 2) ℚ :=
  fun α => if α = Finsupp.single i (α i) then gbinom (1 / 2 : ℚ) (α i) * (-1) ^ (α i) else 0

/-- `B(p,q) = -pq / (2 √(1-p) √(1-q) (√(1-p) + √(1-q))²)`, sphere/paper.tex equation (3.4),
l.524–525. -/
noncomputable def Bgf : MvPowerSeries (Fin 2) ℚ :=
  -(MvPowerSeries.X 0 * MvPowerSeries.X 1) *
    (2 * sqrtOneSub 0 * sqrtOneSub 1 * (sqrtOneSub 0 + sqrtOneSub 1) ^ 2)⁻¹

/-- `B_{m,n} = [p^m q^n] B(p,q)`. -/
noncomputable def Bcoef (m n : ℕ) : ℚ :=
  MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 n) Bgf

/-- The truncation to `1 ≤ m, n ≤ N` of `M(z)_{m,n} = z^m B_{m,n}/m` (sphere/paper.tex l.556);
the index `i : Fin N` stands for `m = i + 1`. -/
noncomputable def Mmat (N : ℕ) : Matrix (Fin N) (Fin N) (PowerSeries ℚ) :=
  Matrix.of fun i j =>
    PowerSeries.C (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) *
      (PowerSeries.X : PowerSeries ℚ) ^ ((i : ℕ) + 1)

/-- The formal series `det(I - M(z)²)^{-1/2} = exp(½ ∑_{k≥1} Tr(M(z)^{2k})/k)`
(sphere/paper.tex l.864–865).  Row `m` of `M(z)` has `z`-order `m`, so the coefficient of `z^n`
only involves the truncation to indices at most `n` and the powers `k ≤ n`. -/
noncomputable def detInvSqrt : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff n
      ((PowerSeries.exp ℚ).subst
        ((2 : ℚ)⁻¹ • ∑ k ∈ Finset.Icc 1 n, ((k : ℚ)⁻¹) • Matrix.trace (Mmat n ^ (2 * k))))

/-- `₂F₁(1/2,1/2;1;z) = ∑_n (binom(2n,n)/4^n)² z^n`. -/
noncomputable def hyp2F1 : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((Nat.centralBinom n : ℚ) / 4 ^ n) ^ 2

/-- Lemma 3.5 (`lem:bergman-det`), sphere/paper.tex l.825–833.  As formal power series in `z`,
`det(I - M(z)²)^{-1/2} = (1-z)^{-1/8} ₂F₁(1/2,1/2;1;z)^{-1/2} = (1-z)^{-1/8} θ₃(q(z))^{-1}`.

Demand sheet.
- identities in `ℚ[[z]]` (l.836);
- the determinant is the series `detInvSqrt`, the paper's definition by the trace formula
  (l.864–865);
- powers `(1-z)^{-1/8}`, `₂F₁^{-1/2}` by the binomial series `fpow` (both series have constant
  term `1`);
- `q(z)`: the compositional inverse of `z(q)`; the second identity is stated for every series
  `Q` with zero constant term and `z(Q(z)) = z` (there is exactly one, since `z(q) = 16q + …`),
  with `θ₃(q(z))` the substitution `θ₃ ∘ Q`.
Both sides of the first identity were compared exactly up to `z⁴`
(`scratch/chains/check_bergman.py`). -/
def Stmt_lem_bergman_det : Prop :=
  detInvSqrt = fpow (1 - PowerSeries.X) (-1 / 8 : ℚ) * fpow hyp2F1 (-1 / 2 : ℚ) ∧
  ∀ Q : PowerSeries ℚ, PowerSeries.constantCoeff Q = 0 → (zq ℚ).subst Q = PowerSeries.X →
    detInvSqrt = fpow (1 - PowerSeries.X) (-1 / 8 : ℚ) * ((th3 ℚ).subst Q)⁻¹

end Virasoro.Sphere
