import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand

/-!
# Schur's irreducibility theorems for the Hermite polynomials (cited input)

Schur 1929 and Schur 1931, as used at sphere/paper.tex l.1775–1778: the physicists' Hermite
polynomial `H_{2m}(x)` and the quotient `H_{2m+1}(x)/x` are irreducible over `ℚ` for every
`m ≥ 1`.  The physicists' Hermite polynomials are given by the three-term recurrence
`H_0 = 1`, `H_1 = 2x`, `H_{n+1} = 2x H_n - 2n H_{n-1}` (DLMF 18.9.1 with Table 18.9.1).
-/

namespace Virasoro.Sphere

open Polynomial

/-- The physicists' Hermite polynomial `H_n(x)` over `ℚ`. -/
noncomputable def hermH : ℕ → ℚ[X]
  | 0 => 1
  | 1 => C 2 * X
  | n + 2 => C 2 * X * hermH (n + 1) - C (2 * ((n : ℚ) + 1)) * hermH n

/-- **Cited** (Schur 1929, Schur 1931; sphere/paper.tex l.1775–1778): for every `m ≥ 1`,
`H_{2m}` and `H_{2m+1}/x` are irreducible over `ℚ`. -/
def Cited_SchurHermite : Prop :=
  ∀ m : ℕ, 1 ≤ m → Irreducible (hermH (2 * m)) ∧ Irreducible (hermH (2 * m + 1) /ₘ X)

end Virasoro.Sphere
