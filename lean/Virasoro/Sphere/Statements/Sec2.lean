import Virasoro.Sphere.Germs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Frozen statements: `sphere/paper.tex`, Sections 2 and 3
(Definitions 2.1 and 2.2, Theorem 3.1)
-/

namespace Virasoro.Sphere

open Polynomial

/-- Well-posedness of Definition 2.1 (`def:sphere-block`), sphere/paper.tex l.298–313: there is
a unique linear functional `⟨ · |Φ_b(1)|Δ_a⟩` on `M(c,Δ)` with value `1` on `v_Δ` and
`⟨L_{-n}u|Φ_b(1)|Δ_a⟩ = (h(u) + nΔ_b - Δ_a)⟨u|Φ_b(1)|Δ_a⟩` for homogeneous `u`, `n ≥ 1`, and
`⟨L_{-Y}v_Δ|Φ_b(1)|Δ_a⟩ = γ_Y(Δ;Δ_a,Δ_b)`.

Demand sheet.
- "indeterminate weights": every commutative `ℚ`-algebra `R` and all `c, Δ, Δ_a, Δ_b ∈ R`
  (l.299);
- existence and uniqueness of the functional (`∃!`) (l.306–311);
- the value on every PBW vector, for all levels and partitions; identity (l.312–313). -/
def Stmt_def_sphere_block : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (c h Δa Δb : R),
    (∃! φ : Verma R c h →ₗ[R] R, IsThreePoint Δa Δb φ) ∧
    ∀ φ : Verma R c h →ₗ[R] R, IsThreePoint Δa Δb φ →
      ∀ (N : ℕ) (Y : Nat.Partition N), φ (Verma.neg Y.word) = gammaY h Δa Δb Y.word

/-- The claims made inside Definition 2.2 (`def:H-series`), sphere/paper.tex l.336–384:
`z(q) ∈ 16q(1 + qℤ[[q]])`; `Φ̃(c,Δ,Δ_i;q) ∈ 1 + qℚ[c,Δ,Δ_1,…,Δ_4][[q]]`; and `H_0 = 1`.

Demand sheet.
- `z(q)`: zero constant term, coefficient `16` of `q`, every higher coefficient `16` times an
  integer (l.343–344);
- `Φ̃`: constant term `1`, and for each `n` one polynomial `Q` over `ℚ` in the six variables
  `(c, Δ, Δ₁, Δ₂, Δ₃, Δ₄)` giving the coefficient of `q^n` for all complex `c, Δ_i` (l.383);
- `H_0 = 1` (l.369).
The identification of the compositional inverse `q(z)` with the elliptic nome
`exp(-πK(1-z)/K(z))` (l.345–347) is a classical analytic fact that the definition of `H_N` does
not use; it is not part of this statement. -/
def Stmt_def_H_series : Prop :=
  (PowerSeries.coeff 0 (zq ℚ) = 0 ∧ PowerSeries.coeff 1 (zq ℚ) = 16 ∧
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff (n + 2) (zq ℚ) = 16 * (z : ℚ)) ∧
  (∀ n : ℕ, ∃ Q : MvPolynomial (Fin 6) ℚ, (n = 0 → Q = 1) ∧
    ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
      PowerSeries.coeff n (PhiTilde c Δe) =
        MvPolynomial.aeval
          (![RatFunc.C c, RatFunc.X, RatFunc.C (Δe 0), RatFunc.C (Δe 1), RatFunc.C (Δe 2),
            RatFunc.C (Δe 3)] : Fin 6 → RatFunc ℂ) Q) ∧
  (∀ (c : ℂ) (Δe : Fin 4 → ℂ), Hsph c Δe 0 = 1)

/-- Theorem 3.1 (`thm:large-delta`), sphere/paper.tex l.406–415.  For every `N ≥ 0` and every
`(c,Δ₁,…,Δ₄) ∈ ℂ⁵`, `lim_{Δ→∞} H_N(c,Δ,Δ_i) = δ_{N,0}`.  Equivalently, with
`H_N = P_N/det G_N(c,Δ)` and `P_N ∈ ℚ[c,Δ,Δ_1,…,Δ_4]`, `deg_Δ P_N < deg_Δ det G_N(c,Δ)` for every
`N ≥ 1`.

Demand sheet.
- all `N ≥ 0`, all complex `c, Δ_i` (l.407);
- the limit along `|Δ| → ∞` in `ℂ` (`Bornology.cobounded`), of the values of the rational
  function `H_N` (it has finitely many poles) (l.409);
- the equivalent form: one polynomial `Q` over `ℚ` in `(c, Δ, Δ₁, …, Δ₄)` for each `N` with
  `H_N det G_N = Q`; the degree inequality in `Δ` is stated at every complex `(c, Δ_i)`, which
  is the inequality of `Δ`-degrees over `ℚ[c,Δ_i]` because `deg_Δ det G_N` does not depend on
  `c` (l.411–414). -/
def Stmt_thm_large_delta : Prop :=
  ∀ N : ℕ,
    (∀ (c : ℂ) (Δe : Fin 4 → ℂ),
      Filter.Tendsto (fun Δ : ℂ => RatFunc.eval (RingHom.id ℂ) Δ (Hsph c Δe N))
        (Bornology.cobounded ℂ) (nhds (if N = 0 then 1 else 0))) ∧
    ∃ Q : MvPolynomial (Fin 6) ℚ, ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
      ∃ P : ℂ[X],
        algebraMap ℂ[X] (RatFunc ℂ) P =
          MvPolynomial.aeval
            (![RatFunc.C c, RatFunc.X, RatFunc.C (Δe 0), RatFunc.C (Δe 1), RatFunc.C (Δe 2),
              RatFunc.C (Δe 3)] : Fin 6 → RatFunc ℂ) Q ∧
        Hsph c Δe N * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det =
          algebraMap ℂ[X] (RatFunc ℂ) P ∧
        (1 ≤ N → P.degree < (gramPoly c N).det.degree)

end Virasoro.Sphere
