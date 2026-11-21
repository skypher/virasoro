import Virasoro.Sphere.Statements.Sec3b
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Cited input: the two Jacobi identities of (2.3)–(2.4) that involve `₂F₁` and `q(z)`

`Sphere.Cited_JacobiIdentities` (`Sphere/Cited.lean`) records the other three identities of
sphere/paper.tex equations (2.3)–(2.5).
-/

namespace Virasoro.Sphere

/-- The identities `₂F₁(1/2,1/2;1;z(q)) = θ₃(q)²` and
`z (d/dz) log(16q(z)/z) = 1/((1-z)θ₃(q(z))⁴) - 1` of sphere/paper.tex equations (2.3), (2.4)
(l.349–354), as identities of formal power series.
Source: E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis* (1927), §21.6 and §22.3
(sphere/paper.tex l.348).
`q(z)` is any series `Q` with zero constant term and `z(Q(z)) = z`; `16q(z)/z` is the series
`R` with `16 Q = z R`, and `log` is the substitution into `log(1+x)`.  The analytic
identification of `q(z)` with the elliptic nome is not used and not recorded. -/
def Cited_JacobiIdentities2 : Prop :=
  hyp2F1.subst (zq ℚ) = th3 ℚ ^ 2 ∧
  ∀ Q : PowerSeries ℚ, PowerSeries.constantCoeff Q = 0 → (zq ℚ).subst Q = PowerSeries.X →
    ∀ R : PowerSeries ℚ, (16 : ℚ) • Q = PowerSeries.X * R →
      PowerSeries.X * PowerSeries.derivative ℚ ((PowerSeries.log ℚ).subst (R - 1)) =
        ((1 - PowerSeries.X) * ((th3 ℚ).subst Q) ^ 4)⁻¹ - 1

end Virasoro.Sphere
