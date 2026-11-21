import Virasoro.Jantzen
import Virasoro.Statements.Prelude

/-!
# Jantzen forms and Jantzen vertex forms (paper Lemma 5.4, Proposition 11.2)

For `u, v ∈ J^i_N(c,h)` with polynomial families `u(x), v(x)` as in Definition 5.2
(`u(0) = u`, `G_N(c,h+x) u(x) ∈ x^i ℂ[x]^{p(N)}`), the `i`-th Jantzen form is
`B^i(u,v) = [x^i] v(x)ᵀ G_N(c,h+x) u(x)` and the `i`-th Jantzen vertex form is
`ρ^{(i)}(u,v) = [x^i] u(x)ᵀ ρ_N(c,h+x,d) v(x)`.
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- `w` is a polynomial family for `v` in the `i`-th Jantzen layer of level `N` (paper
Definition 5.2): `w(0) = v` and `G_N(c,h+x) w(x) ∈ x^i K[x]^{p(N)}`. -/
def IsJFamily (c h : K) (N i : ℕ) (v : Nat.Partition N → K) (w : Nat.Partition N → K[X]) : Prop :=
  (∀ Y, (w Y).eval 0 = v Y) ∧ ∀ Y, (X : K[X]) ^ i ∣ ((gramShift c h N).mulVec w) Y

/-- `[x^i] v(x)ᵀ G_N(c,h+x) u(x)` for two polynomial families `u(x) = wu`, `v(x) = wv`. -/
noncomputable def jformFam (c h : K) (N i : ℕ) (wu wv : Nat.Partition N → K[X]) : K :=
  (wv ⬝ᵥ (gramShift c h N).mulVec wu).coeff i

open Classical in
/-- The `i`-th Jantzen form `B^i(u,v)` on `J^i_N(c,h)` (paper Lemma 5.4), evaluated with chosen
families; it is `0` if `u` or `v` is not in `J^i_N(c,h)`.  Independence of the families is part
(i) of Lemma 5.4 (`Stmt_lem_top_coefficient`), which characterizes this value as `jformFam` of
every pair of families. -/
noncomputable def jform (c h : K) (N i : ℕ) (u v : Nat.Partition N → K) : K :=
  if hu : ∃ w, IsJFamily c h N i u w then
    if hv : ∃ w, IsJFamily c h N i v w then jformFam c h N i hu.choose hv.choose else 0
  else 0

/-- The torus matrix `ρ_N(c, h + x, d)` over `K[x]`. -/
noncomputable def torusShift (c h d : K) (N : ℕ) :
    Matrix (Nat.Partition N) (Nat.Partition N) K[X] :=
  torus (C c) (C h + X) (C d) N

/-- `[x^i] u(x)ᵀ ρ_N(c,h+x,d) v(x)` for two polynomial families. -/
noncomputable def vformFam (c h d : K) (N i : ℕ) (wu wv : Nat.Partition N → K[X]) : K :=
  (wu ⬝ᵥ (torusShift c h d N).mulVec wv).coeff i

open Classical in
/-- The `i`-th Jantzen vertex form `ρ^{(i)}(u,v)` on `J^i_N(c,h)` at equal levels (paper
Proposition 11.2), evaluated with chosen families; `0` outside `J^i_N(c,h)`.  Independence of the
families is part (i) of Proposition 11.2. -/
noncomputable def vform (c h d : K) (N i : ℕ) (u v : Nat.Partition N → K) : K :=
  if hu : ∃ w, IsJFamily c h N i u w then
    if hv : ∃ w, IsJFamily c h N i v w then vformFam c h d N i hu.choose hv.choose else 0
  else 0

/-- `∂_Δ ρ_{Δ,d}(χ,χ)` at `Δ = h₀` for a vector `χ` with fixed level-`ℓ` coordinates `p`
(paper Theorem 9.2, numerator of the first-layer vertex ratio). -/
noncomputable def torusCrossScalar (c h₀ d : K) {ℓ : ℕ} (p : Nat.Partition ℓ → K) : K :=
  (derivative (torusForm (C c) (X : K[X]) (C d) ℓ (fun Y => C (p Y)) (fun Y => C (p Y)))).eval h₀

/-- `F_N(c,Δ,d) = ∑ (G_N(c,Δ)⁻¹)_{Y,Y'} ρ_N(c,Δ,d)_{Y,Y'}` (paper Definition 2.2) for `c, Δ` in a
field `K` at which `G_N(c,Δ)` is invertible, as a polynomial in the external weight `d`. -/
noncomputable def FpolyD (c Δ : K) (N : ℕ) : K[X] :=
  ∑ Y : Nat.Partition N, ∑ Y' : Nat.Partition N,
    C ((gram c Δ N)⁻¹ Y Y') * torus (C c) (C Δ) (X : K[X]) N Y Y'

/-- `H_N(c,Δ,d) = ∑_{j ≤ N} η_j F_{N-j}(c,Δ,d)` (paper Definition 2.3) as a polynomial in `d`,
for `c, Δ` in a field at which `G_M(c,Δ)` is invertible for all `M ≤ N`. -/
noncomputable def HpolyD (c Δ : K) (N : ℕ) : K[X] :=
  ∑ j ∈ Finset.range (N + 1), (eta j : K[X]) * FpolyD c Δ (N - j)

end Virasoro
