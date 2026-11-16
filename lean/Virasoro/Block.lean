import Virasoro.NormalOrder
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharZero.Defs

/-!
# The block coefficients `F_N` and `H_N` (paper Definitions 2.2 and 2.3)

For a field `𝔽` of characteristic zero and `c d : 𝔽`, the coefficient `F_N(c,Δ,d)` is a rational
function of the internal weight `Δ` over `𝔽`.  By Cramer's rule
`∑ (G_N⁻¹)_{Y,Y'} ρ_{Y,Y'} = (∑ adj(G_N)_{Y,Y'} ρ_{Y,Y'}) / det G_N`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- The Shapovalov matrix `G_N(c,Δ)` with polynomial entries in the internal weight `Δ`. -/
noncomputable def gramPoly (c : 𝔽) (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) 𝔽[X] :=
  gram (C c) X N

/-- The torus matrix `ρ_N(c,Δ,d)` with polynomial entries in the internal weight `Δ`. -/
noncomputable def torusPoly (c d : 𝔽) (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) 𝔽[X] :=
  torus (C c) X (C d) N

/-- The numerator `∑_{Y,Y'} adj(G_N)_{Y,Y'} ρ_N{}_{Y,Y'}` of `F_N`. -/
noncomputable def Fnum (c d : 𝔽) (N : ℕ) : 𝔽[X] :=
  ∑ Y, ∑ Y', (gramPoly c N).adjugate Y Y' * torusPoly c d N Y Y'

/-- The coefficient `F_N(c,Δ,d) = ∑_{|Y|=|Y'|=N} (G_N(c,Δ)⁻¹)_{Y,Y'} ρ_N(c,Δ,d)_{Y,Y'}`
(paper Definition 2.2), as a rational function of `Δ`. -/
noncomputable def Frat (c d : 𝔽) (N : ℕ) : RatFunc 𝔽 :=
  algebraMap 𝔽[X] (RatFunc 𝔽) (Fnum c d N) / algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det

/-- The Euler coefficients `η_j`: `∏_{m ≥ 1} (1 - q^m) = ∑_{j ≥ 0} η_j q^j`.  The coefficient of
`q^j` in the infinite product equals its coefficient in `∏_{m=1}^{j} (1 - q^m)`. -/
noncomputable def eta (j : ℕ) : ℤ := (∏ m ∈ Finset.Icc 1 j, (1 - (X : ℤ[X]) ^ m)).coeff j

/-- The eta-reduced coefficient `H_N = ∑_{j=0}^{N} η_j F_{N-j}` (paper Definition 2.3). -/
noncomputable def Hrat (c d : 𝔽) (N : ℕ) : RatFunc 𝔽 :=
  ∑ j ∈ Finset.range (N + 1), (eta j : RatFunc 𝔽) * Frat c d (N - j)

end Virasoro
