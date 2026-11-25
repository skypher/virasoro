import Virasoro.Statements.Rev20261124

/-!
# Statements of `paper.tex` restated in the pass of 2026-11-25

The pass of 2026-11-25 split the two manuscripts into three: `sphere/paper.tex` (the
large-weight limit), `paper.tex` (Part I torus one-point blocks, Part II sphere four-point blocks)
and `irreducible/paper.tex` (the irreducible traces).  In `paper.tex` the confluence theorem,
now Theorem 7.3 (`thm:general-confluence`), no longer contains the a priori pole bound
`M̂⋆_{λ,N}`: it states `A⋆ = Ã⋆` for every `k ≥ 1`, that only finitely many collision moments
are nonzero, the expansion with `∑_{k ≥ 1}`, and, for `b⋆² ∉ ℚ`, that the classes are singletons
and the moments with `k ≥ 2` vanish.  The bound is now Corollary 7.6 (`cor:pole-bound`).

A sum `∑_{k ≥ 1}` with finitely many nonzero terms is encoded as a sum over `1 ≤ k ≤ K` for
some `K` beyond which every term vanishes.
-/

namespace Virasoro

/-- Theorem 7.3 (`thm:general-confluence`) in the form of 2026-11-25. -/
def Stmt_thm_general_confluence_rev25 : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
    (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k → Astar b N lam k = AtildeC b N lam k) ∧
    (∃ K : ℕ, (∀ lam ∈ Lam N b, ∀ k : ℕ, K < k → AtildeC b N lam k = 0) ∧
      HN (kacC b) N =
        ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 K, poleTerm (AtildeC b N lam k) lam k) ∧
    ((∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
      (∀ lam ∈ Lam N b, (collClass N b lam).card = 1 ∧
        ∀ k : ℕ, 2 ≤ k → AtildeC b N lam k = 0) ∧
      GenericRecursionAt Kd (RatFunc.C b) dvar N)

/-- Corollary 7.6 (`cor:pole-bound`): the collision moments vanish beyond `M̂⋆_{λ,N}`, and the
pole order is at most `M̂⋆_{λ,N}`. -/
def Stmt_cor_pole_bound : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Lam N b,
    (∀ k : ℕ, MhatC b N lam < k → AtildeC b N lam k = 0) ∧ mstar b N lam ≤ MhatC b N lam

end Virasoro
