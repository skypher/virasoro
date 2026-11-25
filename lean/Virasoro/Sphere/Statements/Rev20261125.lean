import Virasoro.Sphere.Statements.Rev20261124

/-!
# Sphere statements restated in the pass of 2026-11-25

The sphere confluence theorem moved from `sphere/paper.tex` (Theorem 4.7) to Part II of
`paper.tex` (`thm:confluence`).  It no longer contains the a priori pole bound
`M̂⋆_{λ,N}`: part (i) says that every collision moment lies in `ℚ(b⋆)[Δ₁,…,Δ₄]` and that only
finitely many are nonzero, and part (ii) is the expansion with `∑_{k ≥ 1}`.  Part (iii) is
unchanged.  As in `Statements/Rev20261125.lean`, a sum `∑_{k ≥ 1}` with finitely many nonzero
terms is encoded as a sum over `1 ≤ k ≤ K` for some `K` beyond which every term vanishes.
-/

namespace Virasoro.Sphere

open Polynomial

/-- The sphere confluence theorem (`thm:confluence`) in the form of 2026-11-25. -/
def Stmt_thm_confluence_rev25 : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
    (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k →
      ∃ P : MvPolynomial (Fin 4) ℂ, (∀ m, P.coeff m ∈ Subfield.closure ({b} : Set ℂ)) ∧
        algebraMap (MvPolynomial (Fin 4) ℂ) K4 P = Atildeg (cK b) (RgSph b) N (cK lam) k) ∧
    (∃ K : ℕ, (∀ lam ∈ Lam N b, ∀ k : ℕ, K < k → Atildeg (cK b) (RgSph b) N (cK lam) k = 0) ∧
      Hsph (kacC (cK b)) ΔK N =
        ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 K,
          RatFunc.C (Atildeg (cK b) (RgSph b) N (cK lam) k) /
            (RatFunc.X - RatFunc.C (cK lam)) ^ k) ∧
    ∃ Q : K4[X], Q.natDegree = N ∧
      Bsph (kacC (cK b)) ΔK N =
        algebraMap K4[X] (RatFunc K4) Q + ∑ lam ∈ Lam N b, PP (Bsph (kacC (cK b)) ΔK N) (cK lam)

end Virasoro.Sphere
