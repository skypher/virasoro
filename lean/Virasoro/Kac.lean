import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# Kac weights and fixed specializations (paper Definition 3.1)

`c(b) = 1 + 6 (b + b⁻¹)²` and `h_{r,s}(b) = ((b + b⁻¹)² - (r b + s b⁻¹)²)/4` are defined for an
element `b` of any field, so that the same formulas give the complex values at `b⋆`, the
rational functions of `b`, and the Laurent germs at `b = b⋆ + t`.
-/

namespace Virasoro

section Field

variable {𝔽 : Type*} [Field 𝔽]

/-- The central charge `c(b) = 1 + 6 (b + b⁻¹)²`. -/
def kacC (b : 𝔽) : 𝔽 := 1 + 6 * (b + b⁻¹) ^ 2

/-- The Kac weight `h_{r,s}(b) = ((b + b⁻¹)² - (r b + s b⁻¹)²) / 4`. -/
def kacH (r s : ℤ) (b : 𝔽) : 𝔽 := ((b + b⁻¹) ^ 2 - ((r : 𝔽) * b + (s : 𝔽) * b⁻¹) ^ 2) / 4

/-- A positive Kac label `a = (r, s)`. -/
abbrev Label := ℕ × ℕ

/-- The level `ℓ_a = r s` of the singular vector of the label `a = (r, s)`. -/
def Label.lvl (a : Label) : ℕ := a.1 * a.2

/-- The Kac weight `h_a(b)` of a label `a = (r, s)`. -/
def kacHL (a : Label) (b : 𝔽) : 𝔽 := kacH (a.1 : ℤ) (a.2 : ℤ) b

/-- The positive labels `(r, s)` with `r s ≤ N`. -/
def labels (N : ℕ) : Finset Label :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun a => a.1 * a.2 ≤ N

open Classical in
/-- The finite set `Λ_N(b⋆) = {h_{r,s}(b⋆) : r, s > 0, r s ≤ N}` of limiting Kac weights. -/
noncomputable def Lam (N : ℕ) (b : 𝔽) : Finset 𝔽 := (labels N).image fun a => kacHL a b

open Classical in
/-- The collision class `C⋆_{λ,N} = {(r,s) : r, s > 0, r s ≤ N, h_{r,s}(b⋆) = λ}`. -/
noncomputable def collClass (N : ℕ) (b lam : 𝔽) : Finset Label :=
  (labels N).filter fun a => kacHL a b = lam

end Field

/-- The Ising value `b₀ = 2 i / √3` of the Coulomb-gas parameter, with `c(b₀) = 1/2`. -/
noncomputable def b0 : ℂ := 2 * Complex.I / (Real.sqrt 3 : ℂ)

/-- The Ising Kac weights `Δ_{r,s} = ((4r - 3s)² - 1)/48`. -/
def isingDelta (r s : ℤ) : ℚ := ((4 * r - 3 * s) ^ 2 - 1) / 48

/-- The Ising weights `λ_n = (n² - 1)/48`, `n ≥ 0`. -/
def isingLam (n : ℕ) : ℚ := ((n : ℚ) ^ 2 - 1) / 48

end Virasoro
