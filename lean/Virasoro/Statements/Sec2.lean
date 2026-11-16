import Virasoro.Statements.Prelude
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation

/-!
# Frozen statements: Section 2 (Blocks and the reduced series)
-/

namespace Virasoro

open Polynomial

/-- Well-posedness of Definition 2.2 (`def:matrices`), over an arbitrary commutative
`ℚ`-algebra `R`.  The Verma module `M(c,h)` carries exactly one vacuum functional `⟨h|` and,
for every `d`, exactly one family of matrix elements `⟨u|V_d(1)|v⟩` of a primary field of weight
`d` normalised by `⟨h|V_d(z)|h⟩ = z^{-d}`; the matrices `gram` and `torus` are the matrix
elements `⟨h| L_Y L_{-Y'} |h⟩` and `⟨h| L_Y V_d(1) L_{-Y'} |h⟩`.
Reading convention: `⟨h| L_Y V_d(1) L_{-Y'} |h⟩ = T(L_{-Y}|h⟩, L_{-Y'}|h⟩)` for the pairing
`T(u,v) = ⟨u|V_d(1)|v⟩`, since `⟨h| L_Y` is the adjoint of `L_{-Y}|h⟩`. -/
def Stmt_def_matrices : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (c h : R),
    (∃! ε : Verma R c h →ₗ[R] R, Verma.IsVacuumFunctional ε) ∧
    (∀ ε : Verma R c h →ₗ[R] R, Verma.IsVacuumFunctional ε →
      ∀ (N : ℕ) (Y Y' : Nat.Partition N),
        ε (VirEnv.posOp c Y.word • Verma.neg Y'.word) = gram c h N Y Y') ∧
    (∀ d : R, ∃! T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R, Verma.IsPrimaryPairing d T) ∧
    (∀ (d : R) (T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R), Verma.IsPrimaryPairing d T →
      ∀ (N : ℕ) (Y Y' : Nat.Partition N),
        T (Verma.neg Y.word) (Verma.neg Y'.word) = torus c h d N Y Y')

/-- Lemma 2.4 (`lem:polynomial-entries`): for fixed `N`, every entry of `G_N(c,Δ)` belongs to
`ℚ[c,Δ]`, and every entry of `ρ_N(c,Δ,d)` belongs to `ℚ[c,Δ,d]`.
The variables of `MvPolynomial (Fin 2) ℚ` are `(c, Δ)`, those of `MvPolynomial (Fin 3) ℚ` are
`(c, Δ, d)`. -/
def Stmt_lem_polynomial_entries : Prop :=
  ∀ N : ℕ,
    (∃ P : Matrix (Nat.Partition N) (Nat.Partition N) (MvPolynomial (Fin 2) ℚ),
      ∀ c Δ : ℂ, gram c Δ N = P.map (MvPolynomial.aeval ![c, Δ])) ∧
    (∃ Q : Matrix (Nat.Partition N) (Nat.Partition N) (MvPolynomial (Fin 3) ℚ),
      ∀ c Δ d : ℂ, torus c Δ d N = Q.map (MvPolynomial.aeval ![c, Δ, d]))

end Virasoro
