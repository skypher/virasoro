import Virasoro.Basic
import Virasoro.Block
import Virasoro.Kac
import Virasoro.Local
import Virasoro.Smith
import Virasoro.Jantzen
import Virasoro.Residue
import Virasoro.Shifted
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Notation shared by the frozen statements

The paper's coefficient field for an indeterminate external weight `d` is realised as
`Kd = ℂ(d)`; `H_N(c,Δ,d)` is then a rational function of `Δ` over `Kd`.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

/-- The field `ℂ(d)` of rational functions of the external weight `d`. -/
abbrev Kd : Type := RatFunc ℂ

/-- The indeterminate external weight `d`, as an element of `ℂ(d)`. -/
noncomputable abbrev dvar : Kd := RatFunc.X

/-- `F_N(c,Δ,d)` for complex `c` and indeterminate `d`: a rational function of `Δ` over `ℂ(d)`. -/
noncomputable def FN (c : ℂ) (N : ℕ) : RatFunc Kd := Frat (RatFunc.C c) dvar N

/-- `H_N(c,Δ,d)` for complex `c` and indeterminate `d`: a rational function of `Δ` over `ℂ(d)`. -/
noncomputable def HN (c : ℂ) (N : ℕ) : RatFunc Kd := Hrat (RatFunc.C c) dvar N

/-- The point `Δ = λ` of the `Δ`-line over `ℂ(d)` attached to a complex number `λ`. -/
noncomputable abbrev pt (lam : ℂ) : Kd := RatFunc.C lam

/-- The term `A / (Δ - λ)^k` with `A ∈ ℂ(d)` and `λ ∈ ℂ`. -/
noncomputable def poleTerm (A : Kd) (lam : ℂ) (k : ℕ) : RatFunc Kd :=
  RatFunc.C A / (RatFunc.X - RatFunc.C (pt lam)) ^ k

/-- The subfield `ℚ(b²)` of `ℂ`. -/
noncomputable def Qb2 (b : ℂ) : Subfield ℂ := Subfield.closure {b ^ 2}

/-- `A ∈ k[d]`: the element `A` of `ℂ(d)` is a polynomial in `d` with coefficients in the
subfield `k` of `ℂ`. -/
def IsPolyOver (k : Subfield ℂ) (A : Kd) : Prop :=
  ∃ p : ℂ[X], (∀ n, p.coeff n ∈ k) ∧ algebraMap ℂ[X] Kd p = A

/-- The partial-fraction coefficient `A⋆_{λ,k,N}(d)` of `H_N(c⋆,Δ,d)`: the coefficient of
`(Δ - λ)^{-k}` in its Laurent expansion at `λ` (paper Theorem 4.2). -/
noncomputable def Astar (b : ℂ) (N : ℕ) (lam : ℂ) (k : ℕ) : Kd :=
  ppCoeff (HN (kacC b) N) (pt lam) k

/-- The multiplicity `m⋆_{λ,N}` of the pole of `H_N(c⋆,Δ,d)` at `λ` (zero if removable). -/
noncomputable def mstar (b : ℂ) (N : ℕ) (lam : ℂ) : ℕ := poleOrder (HN (kacC b) N) (pt lam)

/-- The collision moment `Ã⋆_{λ,k,N}(d)` at the complex base point `b⋆` (paper (7.1)). -/
noncomputable def AtildeC (b : ℂ) (N : ℕ) (lam : ℂ) (k : ℕ) : Kd :=
  Atilde (RatFunc.C b) dvar N (pt lam) k

/-- The a priori pole bound `M̂⋆_{λ,N}` at the complex base point `b⋆` (paper Definition 7.3). -/
noncomputable def MhatC (b : ℂ) (N : ℕ) (lam : ℂ) : ℕ :=
  Mhat (RatFunc.C b) dvar N (pt lam)

section Forms

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The Shapovalov form `⟨u, v⟩ = uᵀ G_N(c,h) v` in level-`N` coordinates. -/
def gramForm (c h : R) (N : ℕ) (u v : Nat.Partition N → R) : R :=
  u ⬝ᵥ (gram c h N).mulVec v

/-- The torus form `⟨u| V_d(1) |v⟩ = uᵀ ρ_N(c,h,d) v` in level-`N` coordinates. -/
def torusForm (c h d : R) (N : ℕ) (u v : Nat.Partition N → R) : R :=
  u ⬝ᵥ (torus c h d N).mulVec v

end Forms

/-- The crossing scalar `β_χ = d/dh ⟨h| ω(P) P |h⟩ |_{h = h₀}` of a vector `χ = P|h₀⟩` with
fixed level-`ℓ` coordinates `p` (paper Lemma 5.10). -/
noncomputable def crossScalar {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽] (c h₀ : 𝔽) {ℓ : ℕ}
    (p : Nat.Partition ℓ → 𝔽) : 𝔽 :=
  (derivative (gramForm (C c) (X : 𝔽[X]) ℓ (fun Y => C (p Y)) (fun Y => C (p Y)))).eval h₀

/-- The operator `∑ a L_{-w}` of `U(Vir_-)` attached to a list of (word, coefficient) pairs. -/
noncomputable def St.toOp {R : Type*} [CommRing R] [Algebra ℚ R] (c : R) (s : St R) : VirEnv R c :=
  (s.map fun t => t.2 • VirEnv.negOp c t.1).sum

/-- The identity of the generic recursion (paper Proposition 6.5) over a field `𝔽`, at
`b, d ∈ 𝔽` and level `N`:
`H_N(c(b),Δ,d) = ∑_{ℓ_a ≤ N} ℛ_a(b,d)/(Δ - h_a(b)) · H_{N-ℓ_a}(c(b), h_a(b) + ℓ_a, d)`. -/
def GenericRecursionAt (𝔽 : Type*) [Field 𝔽] [CharZero 𝔽] (b d : 𝔽) (N : ℕ) : Prop :=
  Hrat (kacC b) d N =
    ∑ a ∈ labels N,
      RatFunc.C (genR a.1 a.2 b d) / (RatFunc.X - RatFunc.C (kacHL a b)) *
        RatFunc.C (RatFunc.eval (RingHom.id 𝔽) (kacHL a b + (a.lvl : 𝔽))
          (Hrat (kacC b) d (N - a.lvl)))

/-- The partition `(1^N)` of `N`, the index of the monomial `L_{-1}^N`. -/
def onesPartition (N : ℕ) : Nat.Partition N :=
  Nat.Partition.ofSums N (Multiset.replicate N 1) (by simp)

end Virasoro
