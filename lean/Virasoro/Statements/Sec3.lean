import Virasoro.Statements.Prelude

/-!
# Frozen statements: Section 3 (Algebraic specializations and Ising resonance classes)
-/

namespace Virasoro

/-- The Ising values recorded in Definition 3.1 (`def:fixed-specialization`):
`c(b₀) = 1/2` and `Δ_{r,s} = h_{r,s}(b₀)`. -/
def Stmt_def_fixed_specialization_ising : Prop :=
  kacC b0 = 1 / 2 ∧ ∀ r s : ℤ, kacH r s b0 = (isingDelta r s : ℂ)

/-- Proposition 3.2 (`prop:minimal-collisions`).  Let `p, p'` be coprime positive integers and
`b⋆² = -p'/p`.  Then `c⋆ = 1 - 6 (p'-p)²/(p p')`,
`h_{r,s}(b⋆) = ((p' r - p s)² - (p'-p)²)/(4 p p')`, and for positive pairs `(r,s)`, `(r',s')`
the specialized weights are equal iff for some `ℓ ∈ ℤ`,
`(r',s') = (r + pℓ, s + p'ℓ)` or `(r',s') = (pℓ - r, p'ℓ - s)`. -/
def Stmt_prop_minimal_collisions : Prop :=
  ∀ p p' : ℕ, 0 < p → 0 < p' → Nat.Coprime p p' → ∀ b : ℂ, b ^ 2 = -(p' : ℂ) / p →
    kacC b = 1 - 6 * ((p' : ℂ) - p) ^ 2 / (p * p') ∧
    (∀ r s : ℤ,
      kacH r s b = (((p' : ℂ) * r - p * s) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')) ∧
    ∀ r s r' s' : ℤ, 0 < r → 0 < s → 0 < r' → 0 < s' →
      (kacH r s b = kacH r' s' b ↔
        ∃ l : ℤ, (r' = r + p * l ∧ s' = s + p' * l) ∨ (r' = p * l - r ∧ s' = p' * l - s))

/-- Corollary 3.3 (`cor:ising-classes`).  For positive pairs, `Δ_{r,s} = Δ_{r',s'}` iff for
some `ℓ ∈ ℤ`, `(r',s') = (r+3ℓ, s+4ℓ)` or `(r',s') = (3ℓ-r, 4ℓ-s)`.  Moreover
`Δ_{r,s} = λ_{|4r-3s|}`, the set of distinct positive-label degenerate weights at `c = 1/2` is
`{λ_n : n ≥ 0}`, every collision class contains infinitely many positive pairs, and for each
fixed level `N` only finitely many classes contain a pair with `r s ≤ N`.
A collision class is identified with its weight, so the last clause says that the set of
weights of positive pairs with `r s ≤ N` is finite. -/
def Stmt_cor_ising_classes : Prop :=
  (∀ r s r' s' : ℤ, 0 < r → 0 < s → 0 < r' → 0 < s' →
    (isingDelta r s = isingDelta r' s' ↔
      ∃ l : ℤ, (r' = r + 3 * l ∧ s' = s + 4 * l) ∨ (r' = 3 * l - r ∧ s' = 4 * l - s))) ∧
  (∀ r s : ℤ, 0 < r → 0 < s → isingDelta r s = isingLam (4 * r - 3 * s).natAbs) ∧
  ({x : ℚ | ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ x = isingDelta r s} = Set.range isingLam) ∧
  (∀ r s : ℤ, 0 < r → 0 < s →
    {q : ℤ × ℤ | 0 < q.1 ∧ 0 < q.2 ∧ isingDelta q.1 q.2 = isingDelta r s}.Infinite) ∧
  (∀ N : ℕ, {x : ℚ | ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ r * s ≤ N ∧ x = isingDelta r s}.Finite)

end Virasoro
