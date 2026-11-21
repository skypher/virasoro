import Virasoro.Statements.Sec9b

/-!
# Frozen statements: Sections 12 and 13 of `paper.tex` at 70bac53
(The BGG cocycle; the two-term identity)
-/

namespace Virasoro

open Polynomial

/-- The numerator of the box formula (9.4) as a polynomial in `t` over `ℚ`. -/
noncomputable def boxNumPoly (R S : ℤ) (k m : ℕ) : ℚ[X] :=
  ∏ x ∈ (boxSet R S).erase (-(k : ℤ), -(m : ℤ)),
    (C ((x.1 + k : ℤ) : ℚ) * X + C ((x.2 + m : ℤ) : ℚ))

/-- The denominator of the box formula (9.4) as a polynomial in `t` over `ℚ`. -/
noncomputable def boxDenPoly (R S : ℤ) : ℚ[X] :=
  ∏ x ∈ (boxSet R S).erase (0, 0), (C (x.1 : ℚ) * X + C (x.2 : ℚ))

/-- The rational function `c_{R,S}(t;2k+1,2m+1)` of `t` given by the box formula (9.4). -/
noncomputable def boxRatio (R S : ℤ) (k m : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (boxNumPoly R S k m) / algebraMap ℚ[X] (RatFunc ℚ) (boxDenPoly R S)

/-- Proposition 12.1 (`prop:bgg-cocycle`), paper.tex l.2753–2782.  Let `b⋆² = -p'/p`, `λ`
interior, `d = h_{2k+1,2m+1}(b⋆) ∈ ℱ_{p,p'}(r,s)`.
(i) For every primitive arrow `μ → ν` with label `(R,S)`, with `B₀ = [1-R,R] × [1-S,S]` and
`B₁ = [1-R+k,R+k] × [1-S+m,S+m]`, every factor `p b' - p' a`, `(a,b') ∈ (B₁∖B₀) ∪ (B₀∖B₁)`, is
nonzero, and `c_{R,S}(-p'/p;2k+1,2m+1) = ∏_{B₁∖B₀}(pb'-p'a) / ∏_{B₀∖B₁}(pb'-p'a) ∈ ℚ^×`.
(ii) For every diamond `μ → ν₁ → ξ`, `μ → ν₂ → ξ`,
`c(μ→ν₁) c(ν₁→ξ) = c(μ→ν₂) c(ν₂→ξ)`; hence the product of `c` along any directed path from `μ`
to `ξ` depends only on `(μ,ξ)`.

Demand sheet.
- `MinimalSetting`; `(k,m)` in the fusion box (l.2754–2755);
- (i) every arrow `μ^ε_j → μ^{ε'}_{j+1}`, `j ≥ 0`, with its label `arrowLabel`; nonvanishing of
  each factor on the symmetric difference; the value at `t = -p'/p` of the rational function
  `boxRatio` (reduced fraction; its reduced denominator does not vanish there) equals `cMM`;
  `cMM ≠ 0` (l.2757–2768);
- (ii) the diamond between layers `j` and `j+2` with intermediate nodes `μ^±_{j+1}`;
  path independence: two directed paths (lists of signs) of the same positive length with the
  same end node have the same product (l.2769–2780). -/
def Stmt_prop_bgg_cocycle : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      (∀ (ε : Bool) (j : ℕ) (ε' : Bool),
        let L := arrowLabel p p' (nOrb p p' r s ε j) (nOrb p p' r s ε' (j + 1))
        (∀ x ∈ (boxShift L.1 L.2 k m \ boxSet L.1 L.2) ∪ (boxSet L.1 L.2 \ boxShift L.1 L.2 k m),
          (p : ℤ) * x.2 - (p' : ℤ) * x.1 ≠ 0) ∧
        (boxRatio L.1 L.2 k m).denom.eval (-(p' : ℚ) / p) ≠ 0 ∧
        RatFunc.eval (RingHom.id ℚ) (-(p' : ℚ) / p) (boxRatio L.1 L.2 k m) =
          cMM p p' L.1 L.2 k m ∧
        cMM p p' L.1 L.2 k m ≠ 0) ∧
      (∀ (ε : Bool) (j : ℕ) (ε'' : Bool),
        cArrow p p' r s k m ε j true * cArrow p p' r s k m true (j + 1) ε'' =
          cArrow p p' r s k m ε j false * cArrow p p' r s k m false (j + 1) ε'') ∧
      (∀ (ε : Bool) (j : ℕ) (l l' : List Bool), l ≠ [] → l.length = l'.length →
        l.getLast? = l'.getLast? →
          pathProd p p' r s k m ε j l = pathProd p p' r s k m ε j l')

/-- Lemma 13.1 (`lem:degenerate-quotient-t`), paper.tex l.2851–2868.  Let `b⋆² = -p'/p`, `λ`
interior, `d⋆ = h_{u,v}(b⋆) ∈ ℱ_{p,p'}(r,s)`, `(u,v) = (2k+1,2m+1)`, and let
`μ ∈ 𝒪_{p,p'}(r,s)` have primitive arrows `μ → ν₁`, `μ → ν₂`.  Then
`𝒯^irr_{c⋆,μ,d⋆}(q) + Ω_{u,v}(μ→ν₂) q^{ν₂-μ} 𝒯^irr_{c⋆,ν₂,d⋆}(q)
 = ℱ^Verma_{c⋆,μ,d⋆}(q) - Ω_{u,v}(μ→ν₁) q^{ν₁-μ} ℱ^Verma_{c⋆,ν₁,d⋆}(q)`.

Demand sheet.
- `MinimalSetting`; `(k,m)` in the fusion box; node `μ = μ^ε_{k₀}`; `ν₁ = μ^{ε₁}_{k₀+1}` and
  `ν₂` the other node of layer `k₀+1`, for both choices of `ε₁` (l.2855–2857);
- the identity at each coefficient `q^N`; `ν_i - μ` is the level difference
  `ℓ^{·}_{k₀+1} - ℓ^ε_{k₀}`; a shifted series contributes only when that level is at most `N`;
- for all traces `T₁` at `μ` and `T₂` at `ν₂` (`IsIrrTrace`); `Ω` of a single arrow is its
  box ratio `cArrow`; `ℱ^Verma` values are `FvalAt` (regular by Theorem 9.1). -/
def Stmt_lem_degenerate_quotient_t : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      ∀ (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) (N : ℕ),
        let c : ℂ := kacC b
        let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
        let μ : ℂ := muOrb p p' r s ε k₀
        let lev₁ : ℕ := ellOrb p p' r s ε₁ (k₀ + 1) - ellOrb p p' r s ε k₀
        let lev₂ : ℕ := ellOrb p p' r s (!ε₁) (k₀ + 1) - ellOrb p p' r s ε k₀
        ∀ T₁ T₂ : ℂ, IsIrrTrace c μ d N T₁ →
          (lev₂ ≤ N → IsIrrTrace c (muOrb p p' r s (!ε₁) (k₀ + 1)) d (N - lev₂) T₂) →
          (N < lev₂ → T₂ = 0) →
            T₁ + (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) * T₂ =
              FvalAt c d N μ -
                (if lev₁ ≤ N then
                  (cArrow p p' r s k m ε k₀ ε₁ : ℂ) *
                    FvalAt c d (N - lev₁) (muOrb p p' r s ε₁ (k₀ + 1)) else 0)

end Virasoro
