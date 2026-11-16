import Virasoro.Statements.Prelude
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Frozen statements: Section 4 (Coefficientwise partial fractions)
-/

namespace Virasoro

open Polynomial

/-- Lemma 4.1 (`lem:large-weight`).  For fixed `c, d, N`,
`lim_{Δ→∞} F_N(c,Δ,d) = p(N)`, and consequently `lim_{Δ→∞} H_N(c,Δ,d) = δ_{N,0}`.
Here `c, d` are complex numbers and the limit is taken along `|Δ| → ∞` in `ℂ`. -/
def Stmt_lem_large_weight : Prop :=
  ∀ (c d : ℂ) (N : ℕ),
    Filter.Tendsto (fun Δ : ℂ => RatFunc.eval (RingHom.id ℂ) Δ (Frat c d N))
      (Bornology.cobounded ℂ) (nhds (Fintype.card (Nat.Partition N) : ℂ)) ∧
    Filter.Tendsto (fun Δ : ℂ => RatFunc.eval (RingHom.id ℂ) Δ (Hrat c d N))
      (Bornology.cobounded ℂ) (nhds (if N = 0 then 1 else 0))

/-- Theorem 4.2 (`thm:general-partial-fractions`).  Fix `b⋆ ∈ ℂ^×`.  Then `H_0 = 1`, and for
every `N ≥ 1` there are unique coefficients `A⋆_{λ,k,N}(d) ∈ ℚ(b⋆²)[d]`, `λ ∈ Λ_N(b⋆)`,
`k ≥ 1`, only finitely many nonzero, with
`H_N(c⋆,Δ,d) = ∑_λ ∑_{k≥1} A⋆_{λ,k,N}(d)/(Δ-λ)^k`; the largest `k` with `A⋆_{λ,k,N} ≠ 0` is the
multiplicity `m⋆_{λ,N}` of the pole of `H_N` at `λ` (and `m⋆_{λ,N} = 0` if all vanish); and
`H_Δ^{(c⋆)}(d|q) = 1 + ∑_λ ∑_{k≥1} A⋆_{λ,k}(d;q)/(Δ-λ)^k` coefficientwise in `q`.

Reading conventions: `A⋆_{λ,k,N}` is `Astar` (the Laurent coefficient of `H_N` at `λ`) and
`m⋆_{λ,N}` is `mstar` (the order of the pole); existence is the expansion with these
coefficients, and uniqueness is asserted among all families in `ℚ(b⋆²)[d]` supported on
`Λ_N(b⋆) × {k ≥ 1}` with finitely many nonzero members.  The `q`-series identity is the
identity of the coefficients of `q^N` for every `N`. -/
def Stmt_thm_general_partial_fractions : Prop :=
  ∀ b : ℂ, b ≠ 0 →
    HN (kacC b) 0 = 1 ∧
    (∀ N : ℕ, 1 ≤ N →
      (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k → IsPolyOver (Qb2 b) (Astar b N lam k)) ∧
      {q : ℂ × ℕ | q.1 ∈ Lam N b ∧ 1 ≤ q.2 ∧ Astar b N q.1 q.2 ≠ 0}.Finite ∧
      HN (kacC b) N = ∑ lam ∈ Lam N b, PP (HN (kacC b) N) (pt lam) ∧
      (∀ A' : ℂ → ℕ → Kd,
        (∀ lam k, IsPolyOver (Qb2 b) (A' lam k)) →
        (∀ lam k, (lam ∉ Lam N b ∨ k = 0) → A' lam k = 0) →
        {q : ℂ × ℕ | A' q.1 q.2 ≠ 0}.Finite →
        HN (kacC b) N = ∑ lam ∈ Lam N b, ∑ᶠ k : ℕ, poleTerm (A' lam k) lam k →
        ∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k → A' lam k = Astar b N lam k) ∧
      (∀ lam ∈ Lam N b,
        ((∃ k : ℕ, 1 ≤ k ∧ Astar b N lam k ≠ 0) →
          Astar b N lam (mstar b N lam) ≠ 0 ∧ 1 ≤ mstar b N lam ∧
            ∀ k : ℕ, mstar b N lam < k → Astar b N lam k = 0) ∧
        ((∀ k : ℕ, 1 ≤ k → Astar b N lam k = 0) → mstar b N lam = 0))) ∧
    PowerSeries.mk (fun N => HN (kacC b) N) =
      1 + PowerSeries.mk (fun N =>
        if N = 0 then 0 else ∑ lam ∈ Lam N b, PP (HN (kacC b) N) (pt lam))

/-- The backward precision rule of Lemma 7.4 (`lem:precision-budget`) for the base point `b⋆`;
see `Stmt_lem_precision_budget`.  Two Laurent germs agree through `t^U` if their coefficients of
`t^n` agree for all `n ≤ U`. -/
def PrecisionRule (b : ℂ) : Prop :=
  let bs : Kd := RatFunc.C b
  (∀ (a g : Label) (M : ℕ) (U : ℤ), g ∈ labels M →
    ∀ A' S' : LaurentSeries Kd,
      (-((piG bs dvar g + sigmaG bs a g : ℕ) : ℤ) : WithTop ℤ) ≤ A'.orderTop →
      (-((WG bs dvar (M - g.lvl) g : ℕ) : ℤ) : WithTop ℤ) ≤ S'.orderTop →
      (∀ n : ℤ, n ≤ U + (WG bs dvar (M - g.lvl) g : ℕ) →
        A'.coeff n = (RG bs dvar g / (zG bs a - hG bs g)).coeff n) →
      (∀ n : ℤ, n ≤ U + (piG bs dvar g + sigmaG bs a g : ℕ) →
        S'.coeff n = (SG bs dvar (M - g.lvl) g).coeff n) →
      ∀ n : ℤ, n ≤ U →
        (A' * S').coeff n =
          (RG bs dvar g / (zG bs a - hG bs g) * SG bs dvar (M - g.lvl) g).coeff n) ∧
  (∀ (N : ℕ) (lam : ℂ) (a : Label) (k : ℕ), 1 ≤ N → a ∈ collClass N b lam → 1 ≤ k →
    ∀ R' S' D' : LaurentSeries Kd,
      (-((piG bs dvar a : ℕ) : ℤ) : WithTop ℤ) ≤ R'.orderTop →
      (-((WG bs dvar (N - a.lvl) a : ℕ) : ℤ) : WithTop ℤ) ≤ S'.orderTop →
      (∀ n : ℤ, n ≤ (WG bs dvar (N - a.lvl) a : ℕ) → R'.coeff n = (RG bs dvar a).coeff n) →
      (∀ n : ℤ, n ≤ (piG bs dvar a : ℕ) →
        S'.coeff n = (SG bs dvar (N - a.lvl) a).coeff n) →
      (0 : WithTop ℤ) ≤ D'.orderTop →
      (∀ n : ℤ, n ≤ (vhat bs dvar N a : ℕ) →
        D'.coeff n = (deltaG bs (pt lam) a ^ (k - 1)).coeff n) →
      (R' * S' * D').coeff 0 = (BG bs dvar N a * deltaG bs (pt lam) a ^ (k - 1)).coeff 0)

/-- Theorem 4.3 (`thm:general-confluence`).  Fix `b⋆ ∈ ℂ^×`.  For every `N ≥ 1`,
`H_N(c⋆,Δ,d) = ∑_{λ ∈ Λ_N(b⋆)} ∑_{k=1}^{M̂⋆_{λ,N}} Ã⋆_{λ,k,N}(d)/(Δ-λ)^k`  (4.1);
the backward precision rule supplies a finite truncation order for every intermediate Laurent
germ; for every `k ≥ 1`, `Ã⋆_{λ,k,N} = A⋆_{λ,k,N} ∈ ℚ(b⋆²)[d]` and `m⋆_{λ,N} ≤ M̂⋆_{λ,N}`;
the resulting series agrees coefficientwise in `q` with the inverse-Shapovalov definition; and
if `b⋆² ∉ ℚ`, every collision class consists of a single label, every `M̂⋆_{λ,N}` equals `1`, and
(4.1) is the generic recursion of Proposition 6.5 evaluated at `b = b⋆`.

Reading conventions: the finiteness of the sums and the termination of the recursion are part
of the definitions (`SG`, `WG`, `Atilde` are finite sums and well-founded recursions); the
precision clause is `PrecisionRule`. -/
def Stmt_thm_general_confluence : Prop :=
  ∀ b : ℂ, b ≠ 0 →
    (∀ N : ℕ, 1 ≤ N →
      HN (kacC b) N =
        ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (MhatC b N lam), poleTerm (AtildeC b N lam k) lam k ∧
      (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k →
        AtildeC b N lam k = Astar b N lam k ∧ IsPolyOver (Qb2 b) (AtildeC b N lam k)) ∧
      (∀ lam ∈ Lam N b, mstar b N lam ≤ MhatC b N lam)) ∧
    PrecisionRule b ∧
    PowerSeries.mk (fun N => HN (kacC b) N) =
      1 + PowerSeries.mk (fun N =>
        if N = 0 then 0 else
          ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (MhatC b N lam),
            poleTerm (AtildeC b N lam k) lam k) ∧
    ((∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) → ∀ N : ℕ, 1 ≤ N →
      (∀ lam ∈ Lam N b, (collClass N b lam).card = 1 ∧ MhatC b N lam = 1) ∧
      GenericRecursionAt Kd (RatFunc.C b) dvar N)

/-- Corollary 4.4 (`cor:ising-confluence`).  Let `b⋆ = b₀`, so `c⋆ = 1/2`.  The class
`C_{n,N}` is the set of positive labels with `|4r-3s| = n` and `r s ≤ N`.  For every `N ≥ 1`,
`H_N(1/2,Δ,d) = ∑_{n ≥ 0, C_{n,N} ≠ ∅} ∑_{k=1}^{M̂_{n,N}} Ã_{n,k,N}(d)/(Δ-λ_n)^k` with
`Ã_{n,k,N} = A_{n,k,N} ∈ ℚ[d]`, `m_{n,N} ≤ M̂_{n,N}` is the exact multiplicity of the pole of
`H_N` at `λ_n`, and `H_Δ^{(1/2)}(d|q) = 1 + ∑_{n≥0} ∑_{k≥1} A_{n,k}(d;q)/(Δ-λ_n)^k`
coefficientwise in `q`.
The indices `n` with `C_{n,N} ≠ ∅` are the values `|4r-3s|` on the labels with `r s ≤ N`. -/
def Stmt_cor_ising_confluence : Prop :=
  kacC b0 = 1 / 2 ∧
  (∀ N : ℕ, 1 ≤ N →
    let idx : Finset ℕ := (labels N).image fun a => (4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)).natAbs
    (∀ n : ℕ, collClass N b0 ((isingLam n : ℚ) : ℂ) =
      (labels N).filter fun a => (4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)).natAbs = n) ∧
    HN (1 / 2) N =
      ∑ n ∈ idx, ∑ k ∈ Finset.Icc 1 (MhatC b0 N ((isingLam n : ℚ) : ℂ)),
        poleTerm (AtildeC b0 N ((isingLam n : ℚ) : ℂ) k) ((isingLam n : ℚ) : ℂ) k ∧
    (∀ n ∈ idx, ∀ k : ℕ, 1 ≤ k →
      AtildeC b0 N ((isingLam n : ℚ) : ℂ) k = Astar b0 N ((isingLam n : ℚ) : ℂ) k ∧
      ∃ p : ℚ[X], algebraMap ℂ[X] Kd (p.map (algebraMap ℚ ℂ)) =
        AtildeC b0 N ((isingLam n : ℚ) : ℂ) k) ∧
    (∀ n ∈ idx, mstar b0 N ((isingLam n : ℚ) : ℂ) ≤ MhatC b0 N ((isingLam n : ℚ) : ℂ))) ∧
  PowerSeries.mk (fun N => HN (1 / 2) N) =
    1 + PowerSeries.mk (fun N =>
      if N = 0 then 0 else
        ∑ n ∈ (labels N).image fun a => (4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)).natAbs,
          PP (HN (1 / 2) N) (pt ((isingLam n : ℚ) : ℂ)))

end Virasoro
