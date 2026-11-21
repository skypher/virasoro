import Virasoro.Statements.Sec5c

/-!
# Frozen statements: Section 8 of `paper.tex` at 70bac53 (The Ising model)
-/

namespace Virasoro

open Polynomial

/-- One row of the table of Proposition 8.1: at the Ising weight `λ` the first double pole of
`H_N(1/2,Δ,d)` occurs at level `N`, with
`lim_{Δ→λ} (Δ-λ)² H_N = 𝒫_{R₁,S₁}(b₀,d) 𝒫_{R₂,S₂}(b₀,d) / γ`; `τ = 𝒫_{R₁,S₁} 𝒫_{R₂,S₂}` is the
torus norm of the normalized singular vector of level `N` in `M(1/2,λ)` and `γ` is its second
Jantzen norm. -/
def IsingDoublePole (lam : ℂ) (N R₁ S₁ R₂ S₂ : ℕ) (γ : ℂ) : Prop :=
  (∀ M : ℕ, M < N → poleOrder (HN (1 / 2) M) (pt lam) ≤ 1) ∧
  poleOrder (HN (1 / 2) N) (pt lam) = 2 ∧
  ppCoeff (HN (1 / 2) N) (pt lam) 2 =
    genP R₁ S₁ (RatFunc.C b0 : Kd) dvar * genP R₂ S₂ (RatFunc.C b0 : Kd) dvar / RatFunc.C γ ∧
  ∃ x : Nat.Partition N → ℂ, x (onesPartition N) = 1 ∧
    Verma.IsSingular (Verma.pbwCoord (c := (1 / 2 : ℂ)) (h := lam) N x) N ∧
    (∀ d : ℂ, torusForm (1 / 2 : ℂ) lam d N x x = genP R₁ S₁ b0 d * genP R₂ S₂ b0 d) ∧
    jform (1 / 2 : ℂ) lam N 2 x x = γ

/-- Proposition 8.1 (`prop:ising-double-poles`), paper.tex l.1736–1754.  For `N < 7` every pole
of `H_N(1/2,Δ,d)` in `Δ` is simple.  Over `ℚ(d)`, at `λ = 1/2, 1/16, 0` the first double poles
occur at `N = 7, 10, 11`, where `lim_{Δ→λ} (Δ-λ)² H_N(1/2,Δ,d) = τ(d)/γ` with
`(τ, γ) = (𝒫_{2,1}𝒫_{1,5}, -700700)`, `(𝒫_{1,2}𝒫_{4,2}, -1121229484375/192)`,
`(𝒫_{1,1}𝒫_{2,5}, -2477917160468750/6561)`; `τ` is the torus norm of the singular vector that
starts the second Jantzen layer and `γ` is its second Jantzen norm.

Demand sheet.
- first clause: all `N < 7`, every point of the `Δ`-line over `ℂ(d)`, pole order at most `1`
  (l.1737);
- "first double pole at `N`": pole order at most `1` at `λ` below level `N`, and exactly `2`
  at level `N` (l.1738–1739);
- the limit: coefficient of `(Δ-λ)^{-2}` (l.1740); `𝒫_{R,S}(b₀,d)` is `genP` (the monic
  polynomial `∏ (d - d_x)` of the proof of Proposition 6.9, l.1749–1751), with `d` the
  indeterminate of `ℂ(d)`;
- the constants `γ` as printed (l.1744–1746);
- `τ` and `γ` are attached to a singular vector: a normalized singular vector of level `N` in
  `M(1/2,λ)` exists with torus norm `τ` and `B²`-norm `γ` (l.1751–1753). -/
def Stmt_prop_ising_double_poles : Prop :=
  (∀ N : ℕ, N < 7 → ∀ a : Kd, poleOrder (HN (1 / 2) N) a ≤ 1) ∧
  IsingDoublePole (1 / 2) 7 2 1 1 5 (-700700) ∧
  IsingDoublePole (1 / 16) 10 1 2 4 2 (-1121229484375 / 192) ∧
  IsingDoublePole 0 11 1 1 2 5 (-2477917160468750 / 6561)

end Virasoro
