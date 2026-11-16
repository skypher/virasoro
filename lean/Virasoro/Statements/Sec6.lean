import Virasoro.Statements.Prelude

/-!
# Frozen statements: Section 6 (Generic residue data)
-/

namespace Virasoro

open Polynomial

/-- The two generic normalization identities, as identities of rational functions of `b` over
`ℚ` (the variable `b` is `RatFunc.X`).  For positive `r, s` there is a unique singular vector
`χ_{r,s}(b)` of level `r s` in `M(c(b), h_{r,s}(b))` over `ℚ(b)` whose `L_{-1}^{rs}`-coefficient
is `1`; its coordinates `p` are the solution of a finite linear system over `ℚ(b)`.  Then
`β_{χ_{r,s}(b)} = 𝒜_{r,s}(b)⁻¹` (6.1) and `⟨χ_{r,s}(b)|V_d(1)|χ_{r,s}(b)⟩ = 𝒫_{r,s}(b,d)` (6.2);
the second identity is polynomial in `d` and is stated for every `d ∈ ℚ(b)`. -/
def NormalizationIdentities : Prop :=
  ∀ r s : ℕ, 0 < r → 0 < s →
    ∃ p : Nat.Partition (r * s) → RatFunc ℚ,
      (p (onesPartition (r * s)) = 1 ∧
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p) (r * s)) ∧
      (∀ p' : Nat.Partition (r * s) → RatFunc ℚ, p' (onesPartition (r * s)) = 1 →
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p') (r * s) → p' = p) ∧
      crossScalar (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) p =
        (genA r s (RatFunc.X : RatFunc ℚ))⁻¹ ∧
      (∀ d : RatFunc ℚ,
        torusForm (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) d (r * s) p p =
          genP r s RatFunc.X d)

/-- The generic normalization identities of Proposition 6.2 with their continuation.  The
identities (6.1) and (6.2) hold as identities of rational functions of `b` over `ℚ` for the
normalized singular vector `χ_{r,s}(b)` with coordinates `p` (see `NormalizationIdentities`),
and they continue to every specialization `b₁ ∈ ℂ^×` at which the coordinates of the normalized
singular vector are regular.  At such a `b₁` the rational function `𝒜_{r,s}⁻¹` takes the value
`2 ∏ (p b₁ + q b₁⁻¹)`. -/
def ImportedNormalizations : Prop :=
  ∀ r s : ℕ, 0 < r → 0 < s →
    ∃ p : Nat.Partition (r * s) → RatFunc ℚ,
      (p (onesPartition (r * s)) = 1 ∧
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p) (r * s)) ∧
      (∀ p' : Nat.Partition (r * s) → RatFunc ℚ, p' (onesPartition (r * s)) = 1 →
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p') (r * s) → p' = p) ∧
      crossScalar (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) p =
        (genA r s (RatFunc.X : RatFunc ℚ))⁻¹ ∧
      (∀ d : RatFunc ℚ,
        torusForm (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) d (r * s) p p =
          genP r s RatFunc.X d) ∧
      (∀ b₁ : ℂ, b₁ ≠ 0 →
        (∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (p Y)) ≠ 0) →
        let p₁ : Nat.Partition (r * s) → ℂ := fun Y => RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y)
        crossScalar (kacC b₁) (kacH r s b₁) p₁ =
            2 * ∏ pq ∈ genAIndex r s, ((pq.1 : ℂ) * b₁ + (pq.2 : ℂ) * b₁⁻¹) ∧
          ∀ d : ℂ, torusForm (kacC b₁) (kacH r s b₁) d (r * s) p₁ p₁ = genP r s b₁ d)

/-- Proposition 6.2 (`prop:imported-normalizations`): the generic normalization identities
(6.1) and (6.2) as identities of rational functions of `b`, and their continuation to every
specialization at which the normalized singular vector is regular; see
`ImportedNormalizations`. -/
def Stmt_prop_imported_normalizations : Prop := ImportedNormalizations

/-- Lemma 6.4 (`lem:no-generic-shifted-pole`).  For positive labels `(r,s)` and `(u,v)`,
`h_{r,s}(b) + r s - h_{u,v}(b)` is not the zero rational function of `b`; for distinct positive
labels, `h_{r,s}(b) - h_{u,v}(b)` is not the zero rational function.  If `b⋆ ∈ ℂ^×` and
`b⋆² ∉ ℚ`, then neither function vanishes at `b⋆`, and every `𝒜_{r,s}` is regular and nonzero at
`b⋆`.  Regularity of `𝒜_{r,s}` at `b⋆` means that no factor `p b⋆ + q b⋆⁻¹` vanishes. -/
def Stmt_lem_no_generic_shifted_pole : Prop :=
  (∀ r s u v : ℕ, 0 < r → 0 < s → 0 < u → 0 < v →
    kacH r s (RatFunc.X : RatFunc ℂ) + ((r * s : ℕ) : RatFunc ℂ) - kacH u v RatFunc.X ≠ 0 ∧
    ((r, s) ≠ (u, v) → kacH r s (RatFunc.X : RatFunc ℂ) - kacH u v RatFunc.X ≠ 0)) ∧
  (∀ b : ℂ, b ≠ 0 → (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
    ∀ r s u v : ℕ, 0 < r → 0 < s → 0 < u → 0 < v →
      kacH r s b + ((r * s : ℕ) : ℂ) - kacH u v b ≠ 0 ∧
      ((r, s) ≠ (u, v) → kacH r s b - kacH u v b ≠ 0) ∧
      (∀ pq ∈ genAIndex r s, (pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹ ≠ 0) ∧
      genA r s b ≠ 0)

/-- Proposition 6.5 (`prop:generic-recursion`).  Fix `N ≥ 1`.  For all `b` outside a finite set
of algebraic values,
`H_N(c(b),Δ,d) = ∑_{ℓ_a ≤ N} ℛ_{r,s}(b,d)/(Δ - h_{r,s}(b)) · H_{N-ℓ_a}(c(b), h_{r,s}(b)+rs, d)`
as an identity of rational functions of `Δ`, polynomial in `d` (here `d` is the indeterminate
of `ℂ(d)`). -/
def Stmt_prop_generic_recursion : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ E : Finset ℂ, (∀ x ∈ E, IsAlgebraic ℚ x) ∧
    ∀ b : ℂ, b ∉ E → GenericRecursionAt Kd (RatFunc.C b) dvar N

/-- The generic recursion of Proposition 6.5 in the form used by its consumers (the proofs of
Theorem 4.3 and Proposition 7.7), where it is applied to the formal germ `b = b⋆ + t` and read
as an identity of rational functions of `b`: for each `N ≥ 1` there are finitely many nonzero
polynomials over `ℚ` such that the identity holds over every field of characteristic zero at
every `b ≠ 0` that is a root of none of them, for every `d`.  The roots of these polynomials
form the finite set of algebraic exceptional values of Proposition 6.5. -/
def GenericRecursionUniform : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ S : Finset ℚ[X], (∀ P ∈ S, P ≠ 0) ∧
    ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (b d : 𝔽), b ≠ 0 →
      (∀ P ∈ S, aeval b P ≠ 0) → GenericRecursionAt 𝔽 b d N

end Virasoro
