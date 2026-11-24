import Virasoro.Statements.Sec4
import Virasoro.Algebra
import Virasoro.Kac

/-!
# Statements of `paper.tex` added or restated after 70bac53 (state of 2026-11-24)

The presentation pass of 2026-11-24 (307908d) stated a new numbered lemma, Lemma 11.2
(`lem:ward-induction`), and restated Theorem 4.3 of 70bac53 as Theorem 7.6
(`thm:general-confluence`) without the precision rule and the power-series form.  This file gives
both in the paper's current form.  `Stmt_thm_general_confluence` (Statements/Sec4.lean) keeps the
70bac53 form, which contains the current one.  The readability pass of 2026-11-24 put the
theorem ahead of the precision lemma, so the theorem is now Theorem 7.4 and the precision lemma
(`lem:precision-budget`) is Lemma 7.6.
-/

namespace Virasoro

open Verma

/-- Lemma 11.2 (`lem:ward-induction`).  At a minimal-model charge `c⋆ = c(b⋆)`,
`b⋆² = -p'/p`, let `ψ` be a symmetric bilinear form on `M(c⋆,ν)` satisfying the `V_d(1)` Ward
identity (9.3) with `Δ₁ = Δ₂ = ν`, and let `w ∈ M(c⋆,ν)_ℓ` be a singular vector with
`ψ(w,v_ν) = 0`.  Then `U(Vir₋)w ⊂ rad ψ`.

Reading: the Ward identity (9.3) for homogeneous `u, v` is the identity below with `L_0` acting
by `ν + N₁` and `ν + N₂`, extended linearly (as in `Verma.IsPrimaryPairing`, without the
normalization); `rad ψ` is the set of `u` with `ψ(u,·) = 0 = ψ(·,u)`. -/
def Stmt_lem_ward_induction : Prop :=
  ∀ (p p' : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    ∀ (ν d : ℂ) (ψ : Verma ℂ (kacC b) ν →ₗ[ℂ] Verma ℂ (kacC b) ν →ₗ[ℂ] ℂ),
      (∀ u v, ψ u v = ψ v u) →
      (∀ (n : ℤ) (u v : Verma ℂ (kacC b) ν),
        ψ (L (-n) u) v - ψ u (L n v) = ψ (L 0 u) v - ψ u (L 0 v) + (n : ℂ) * d * ψ u v) →
      ∀ (w : Verma ℂ (kacC b) ν) (ℓ : ℕ), IsSingular w ℓ → ψ w hw = 0 →
        ∀ u ∈ negSpan w, ∀ v, ψ u v = 0 ∧ ψ v u = 0

/-- Theorem 7.4 (`thm:general-confluence`), in the paper's current form.  Fix `b⋆ ∈ ℂ^×` and
`N ≥ 1`.  For every `λ ∈ Kac_N(b⋆)` and `k ≥ 1`, the partial-fraction coefficients of
Theorem 4.2 are the collision moments (7.1): `A⋆_{λ,k,N} = Ã⋆_{λ,k,N}`.  Hence
`m⋆_{λ,N} ≤ M̂⋆_{λ,N}` for every `λ`, and
`H_N(c⋆,Δ,d) = ∑_{λ ∈ Kac_N(b⋆)} ∑_{k=1}^{M̂⋆_{λ,N}} Ã⋆_{λ,k,N}(d)/(Δ-λ)^k`.  If `b⋆² ∉ ℚ`, every
collision class is a singleton, every `M̂⋆_{λ,N}` equals `1`, and the formula is
Proposition 6.4 evaluated at `b = b⋆`.

Encoding as in `Stmt_thm_general_confluence`: `Lam N b` is `Kac_N(b⋆)`, the last clause is
`GenericRecursionAt` at `b⋆`. -/
def Stmt_thm_general_confluence_paper : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
    (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k → Astar b N lam k = AtildeC b N lam k) ∧
    (∀ lam ∈ Lam N b, mstar b N lam ≤ MhatC b N lam) ∧
    HN (kacC b) N =
      ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (MhatC b N lam), poleTerm (AtildeC b N lam k) lam k ∧
    ((∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
      (∀ lam ∈ Lam N b, (collClass N b lam).card = 1 ∧ MhatC b N lam = 1) ∧
      GenericRecursionAt Kd (RatFunc.C b) dvar N)

end Virasoro
