import Virasoro.Sphere.Statements.Sec4
import Virasoro.Sphere.Fock

/-!
# Results cited from the literature by `sphere/paper.tex`

Each `Cited_*` proposition records a result that the sphere paper uses without proof.  Results
it takes from the torus paper are the torus statements `Virasoro.Stmt_*` themselves and are
not repeated here.
-/

namespace Virasoro.Sphere

open Polynomial

/-- Zamolodchikov's fusion polynomial for the sphere three-point scalar.
Source: A. B. Zamolodchikov (1987), Section 2; proved in Al. Zamolodchikov (2004), Section 5,
equations (5.9)–(5.12); see also S. Ribault (2019), equation (3.4) (proof of Proposition 4.3,
sphere/paper.tex l.1276–1281).  For the singular vector `χ_{r,s}(b)` over `ℚ(b)` with
`L_{-1}^{rs}`-coefficient `1`, `⟨χ_{r,s}(b)|Φ_b(1)|Δ_a⟩ = P_{r,s}(b,Δ_a,Δ_b)`, with sign `+1`. -/
def Cited_SphereFusionPolynomial : Prop :=
  ∀ r s : ℕ, 0 < r → 0 < s →
    ∀ p : Nat.Partition (r * s) → RatFunc ℚ, p (onesPartition (r * s)) = 1 →
      Verma.IsSingular
        (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
          (r * s) p) (r * s) →
      ∀ Δa Δb : RatFunc ℚ,
        ∑ Y, p Y * gammaY (kacH r s (RatFunc.X : RatFunc ℚ)) Δa Δb Y.word =
          fusP r s (RatFunc.X : RatFunc ℚ) Δa Δb

/-- `∏_{m=1}^∞ (1 - q^{2m})^e` as a power series: the coefficient of `q^n` is that of the
product over `m ≤ n`. -/
noncomputable def etaSqPow (e : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff n
      (∏ m ∈ Finset.Icc 1 n, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * m)) ^ e)

/-- Three of the classical Jacobi identities of sphere/paper.tex equations (2.3)–(2.5), as
identities of formal power series in `q`.
Source: E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis* (1927), §21.6 and §22.3
(sphere/paper.tex l.348).
`1 - z(q) = θ₄(q)⁴/θ₃(q)⁴`; `θ₂θ₃θ₄ = 2q^{1/4} ∏(1-q^{2m})³`, written with
`θ₂ = 2q^{1/4}ψ` as `ψ θ₃ θ₄ = ∏(1-q^{2m})³`; and
`16q ∏(1-q^{2m})^{12} = z(q)(1-z(q)) θ₃(q)^{12}`.
The two identities that involve `₂F₁(1/2,1/2;1;z(q))` and the inverse series `q(z)` are not
recorded here. -/
def Cited_JacobiIdentities : Prop :=
  (1 - zq ℚ = th4 ℚ ^ 4 * (th3 ℚ ^ 4)⁻¹) ∧
  (thPsi ℚ * th3 ℚ * th4 ℚ = etaSqPow 3) ∧
  (16 * PowerSeries.X * etaSqPow 12 = zq ℚ * (1 - zq ℚ) * th3 ℚ ^ 12)

/-- Cited input for the operators (3.2), sphere/paper.tex l.428, l.443–444.
Source: M. Beşken, S. Datta and P. Kraus (2019), §2.1: the Feigin–Fuchs differential operators
form a Virasoro representation of central charge `c = 1 + 24μ²`, and `l_k† = l_{-k}` under the
form (3.1) for real `μ, λ`. -/
def Cited_FeiginFuchsOperators : Prop :=
  (∀ (μ lam : ℂ) (m n : ℤ) (f : Fock),
    ffOp μ lam m (ffOp μ lam n f) - ffOp μ lam n (ffOp μ lam m f) =
      ((m : ℂ) - n) • ffOp μ lam (m + n) f +
        if m + n = 0 then ((1 + 24 * μ ^ 2) / 12 * ((m : ℂ) ^ 3 - m)) • f else 0) ∧
  (∀ (μ lam : ℝ) (k : ℤ) (f g : Fock),
    fockForm (ffOp (μ : ℂ) (lam : ℂ) k f) g = fockForm f (ffOp (μ : ℂ) (lam : ℂ) (-k) g))

end Virasoro.Sphere
