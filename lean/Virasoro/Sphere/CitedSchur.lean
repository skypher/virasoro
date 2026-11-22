import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand

/-!
# Schur's irreducibility theorem for the Hermite polynomials (cited input)

Schur 1929, restated as Hilfssatz D in Schur 1931 (§1, p. 54), as used at sphere/paper.tex
(proof of Theorem 5.5, case `M ≥ 4`): the polynomials `x⁻¹He₃, He₄, x⁻¹He₅, He₆, …` are
irreducible over `ℚ`.  Schur's `H_m` (1931, p. 52) is the monic Hermite polynomial
`He_m(x) = (-1)^m e^{x²/2} (d/dx)^m e^{-x²/2}`, given by the three-term recurrence
`He_0 = 1`, `He_1 = x`, `He_{n+2} = x He_{n+1} - (n+1) He_n` (DLMF 18.9.1 with Table 18.9.1).
The paper uses the statement for `He_{2m}` and `He_{2m+1}/x` with `m ≥ 2` only.
-/

namespace Virasoro.Sphere

open Polynomial

/-- The monic (probabilists') Hermite polynomial `He_n(x)` over `ℚ`. -/
noncomputable def hermHe : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * hermHe (n + 1) - C ((n : ℚ) + 1) * hermHe n

/-- **Cited** (Schur 1929; Schur 1931, §1, Hilfssatz D): for every `m ≥ 2`, `He_{2m}` and
`He_{2m+1}/x` are irreducible over `ℚ`. -/
def Cited_SchurHermite : Prop :=
  ∀ m : ℕ, 2 ≤ m → Irreducible (hermHe (2 * m)) ∧ Irreducible (hermHe (2 * m + 1) /ₘ X)

end Virasoro.Sphere
