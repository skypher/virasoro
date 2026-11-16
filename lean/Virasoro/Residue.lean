import Virasoro.Kac
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity

/-!
# Generic residue data (paper Definition 6.1)

The functions `𝒫_{r,s}(b,d)`, `𝒜_{r,s}(b)` and `ℛ_{r,s}(b,d) = 𝒜_{r,s}(b) 𝒫_{r,s}(b,d)` are
defined for elements `b`, `d` of any field.
-/

namespace Virasoro

variable {𝔽 : Type*} [Field 𝔽]

/-- The odd integers `k` with `1 ≤ k ≤ 2n - 1`. -/
def oddsBelow (n : ℕ) : Finset ℕ := (Finset.range (2 * n)).filter fun k => k % 2 = 1

/-- `Λ² = (b + b⁻¹)² - 4 d`. -/
def lamSq (b d : 𝔽) : 𝔽 := (b + b⁻¹) ^ 2 - 4 * d

/-- The fusion polynomial
`𝒫_{r,s}(b,d) = ∏_{k odd ≤ 2r-1} ∏_{l odd ≤ 2s-1}
  (Λ² - (k b + l b⁻¹)²)/4 · (Λ² - (k b - l b⁻¹)²)/4`. -/
def genP (r s : ℕ) (b d : 𝔽) : 𝔽 :=
  ∏ k ∈ oddsBelow r, ∏ l ∈ oddsBelow s,
    ((lamSq b d - ((k : 𝔽) * b + (l : 𝔽) * b⁻¹) ^ 2) / 4) *
      ((lamSq b d - ((k : 𝔽) * b - (l : 𝔽) * b⁻¹) ^ 2) / 4)

/-- The index set `{(p,q) : 1 - r ≤ p ≤ r, 1 - s ≤ q ≤ s, (p,q) ≠ (0,0), (r,s)}`. -/
noncomputable def genAIndex (r s : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (1 - (r : ℤ)) r ×ˢ Finset.Icc (1 - (s : ℤ)) s).filter
    fun pq => pq ≠ (0, 0) ∧ pq ≠ ((r : ℤ), (s : ℤ))

/-- `𝒜_{r,s}(b) = ½ ∏_{(p,q)} (p b + q b⁻¹)⁻¹`, the product over `genAIndex r s`. -/
noncomputable def genA (r s : ℕ) (b : 𝔽) : 𝔽 :=
  2⁻¹ * ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹)⁻¹

/-- The generic residue coefficient `ℛ_{r,s}(b,d) = 𝒜_{r,s}(b) 𝒫_{r,s}(b,d)`. -/
noncomputable def genR (r s : ℕ) (b d : 𝔽) : 𝔽 := genA r s b * genP r s b d

end Virasoro
