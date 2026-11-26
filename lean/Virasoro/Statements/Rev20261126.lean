import Virasoro.Statements.Rev20261125
import Virasoro.Statements.Sec12

/-!
# Statements of `irreducible/paper.tex` restated in the pass of 2026-11-26

The pass of 2026-11-26 (a13dc17, 4c60a91) defines the BGG weight directly from the Gamma
product.  For an orbit weight `μ` with momentum `n_μ` and `d = h_{2k+1,2m+1}(b⋆)`, the paper's
display `eq:psi-star` is the value `Ψ⋆_{2k+1,2m+1}(μ)` of the Gamma potential
`eq:gamma-potential` (`PsiPot`) at `b = b⋆` and `2ϖ/b⋆ = n_μ/p'`, and the BGG weight is
`Ω_{2k+1,2m+1}(μ → ξ) := Ψ⋆(ξ)/Ψ⋆(μ)` for all orbit weights `μ, ξ`.  Proposition 6.1(ii)
(`prop:bgg-cocycle`) now says: `Ψ⋆` is finite and nonzero on the orbit; for every primitive arrow
`α → β` the box ratio at `b⋆` is `Ψ⋆(β)/Ψ⋆(α) = Ω(α → β)`; the product of the box ratios along a
directed path from `μ` to `ξ` is `Ω(μ → ξ)`; and `Ω(μ → ξ) ∈ ℚ^×` for all orbit pairs.
Proposition 6.1(i) is unchanged.  Theorem 4.3 (`thm:gen-rocha-caridi`) is unchanged in wording;
its `Ω` is now the BGG weight of the definition above.

Reading conventions.
- The orbit node `μ^ε_j` has momentum `nOrb p p' r s ε j`.  The node `λ = μ₀` is `(true, 0)`
  (momentum `n₀`); `(false, 0)` has momentum `-n₀` and the same `Ψ⋆`, the potential being even
  in `ϖ`.
- `1/Γ` is `(Complex.Gamma ·)⁻¹`, as in `PsiPot`; on the orbit no Gamma argument is a pole.
- "Finite and nonzero" for `Ψ⋆` is `psiStar … ≠ 0`; "`Ω ∈ ℚ^×`" is: some nonzero rational
  equals `Ω` in `ℂ`.
- A directed path from `μ^ε_j` is a nonempty list of signs `l` (the nodes visited at the layers
  `j+1, j+2, …`), as in `pathProd`; it ends at `μ^e_{j+|l|}` with `e` the last sign.
-/

namespace Virasoro

/-- `Ψ⋆_{2k+1,2m+1}(μ^ε_j)`, display `eq:psi-star` of `irreducible/paper.tex`: the Gamma
potential at `b = b⋆` and `2ϖ/b⋆ = n_μ/p'`. -/
noncomputable def psiStar (p p' r s k m : ℕ) (b : ℂ) (ε : Bool) (j : ℕ) : ℂ :=
  PsiPot k m ((nOrb p p' r s ε j : ℂ) * b / (2 * p')) b

/-- The BGG weight `Ω_{2k+1,2m+1}(μ^ε_j → μ^{ε'}_{j'}) = Ψ⋆(μ^{ε'}_{j'})/Ψ⋆(μ^ε_j)`
(paragraph before Theorem 4.3 of `irreducible/paper.tex`). -/
noncomputable def OmegaPsi (p p' r s k m : ℕ) (b : ℂ) (ε : Bool) (j : ℕ) (ε' : Bool) (j' : ℕ) :
    ℂ :=
  psiStar p p' r s k m b ε' j' / psiStar p p' r s k m b ε j

/-- Proposition 6.1 (`prop:bgg-cocycle`) of `irreducible/paper.tex` in the form of 2026-11-26.

Demand sheet.
- `MinimalSetting`; `(k,m)` in the fusion box;
- (i) as in `Stmt_prop_bgg_cocycle`: for every arrow `μ^ε_j → μ^{ε'}_{j+1}` with its label, the
  factors on the symmetric difference are nonzero, the reduced denominator of `boxRatio` does not
  vanish at `-p'/p`, its value there is `cMM`, and `cMM ≠ 0`;
- (ii) `Ψ⋆(μ^ε_j) ≠ 0` at every node; the box ratio `cArrow` of every arrow equals
  `Ω(α → β)`; the product along every directed path equals `Ω` from its start to its end; every
  `Ω(μ → ξ)`, for all pairs of nodes, is a nonzero rational. -/
def Stmt_prop_bgg_cocycle_rev26 : Prop :=
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
      (∀ (ε : Bool) (j : ℕ), psiStar p p' r s k m b ε j ≠ 0) ∧
      (∀ (ε : Bool) (j : ℕ) (ε' : Bool),
        ((cArrow p p' r s k m ε j ε' : ℚ) : ℂ) = OmegaPsi p p' r s k m b ε j ε' (j + 1)) ∧
      (∀ (l : List Bool) (ε : Bool) (j : ℕ) (e : Bool), l.getLast? = some e →
        ((pathProd p p' r s k m ε j l : ℚ) : ℂ) = OmegaPsi p p' r s k m b ε j e (j + l.length)) ∧
      (∀ (ε : Bool) (j : ℕ) (ε' : Bool) (j' : ℕ),
        ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = OmegaPsi p p' r s k m b ε j ε' j')

/-- Theorem 4.3 (`thm:gen-rocha-caridi`) of `irreducible/paper.tex` in the form of 2026-11-26:
`Stmt_thm_gen_rocha_caridi` with `Ω(λ → μ^±_j)` the BGG weight `OmegaPsi … true 0 ± j`.  The
demand sheet is that of `Stmt_thm_gen_rocha_caridi`. -/
def Stmt_thm_gen_rocha_caridi_rev26 : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let lam : ℂ := kacH r s b
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      (∀ N : ℕ, (∃ T : ℂ, IsIrrTrace c lam d N T) ∧
        ∀ T : ℂ, IsIrrTrace c lam d N T →
          T = FvalAt c d N lam + ∑ j ∈ Finset.Icc 1 N, (-1 : ℂ) ^ j *
            ((if ellOrb p p' r s true j ≤ N then
                OmegaPsi p p' r s k m b true 0 true j *
                  FvalAt c d (N - ellOrb p p' r s true j) (muOrb p p' r s true j) else 0) +
              (if ellOrb p p' r s false j ≤ N then
                OmegaPsi p p' r s k m b true 0 false j *
                  FvalAt c d (N - ellOrb p p' r s false j) (muOrb p p' r s false j) else 0))) ∧
      (∀ (ε : Bool) (j M : ℕ), (Frat c d M).denom.eval (muOrb p p' r s ε j) ≠ 0) ∧
      (k = 0 → m = 0 → d = 0 ∧
        (∀ (ε : Bool) (j : ℕ), OmegaPsi p p' r s k m b true 0 ε j = 1) ∧
        ∀ (ε : Bool) (j N : ℕ),
          FvalAt c d N (muOrb p p' r s ε j) = (Fintype.card (Nat.Partition N) : ℂ)) ∧
      (∀ (N : ℕ) (T : ℂ), IsIrrTrace c lam d N T → ∃ q : ℚ, T = (q : ℂ)) ∧
      (∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
        ∀ j : ℕ, 1 ≤ j →
          (∀ xp : Nat.Partition (ellPlus p p' r s j) → ℂ,
            Verma.pbwCoord (ellPlus p p' r s j) xp = wp j →
              vform c lam d (ellPlus p p' r s j) j xp xp =
                OmegaPsi p p' r s k m b true 0 true j *
                  jform c lam (ellPlus p p' r s j) j xp xp) ∧
          (∀ xm : Nat.Partition (ellMinus p p' r s j) → ℂ,
            Verma.pbwCoord (ellMinus p p' r s j) xm = wm j →
              vform c lam d (ellMinus p p' r s j) j xm xm =
                OmegaPsi p p' r s k m b true 0 false j *
                  jform c lam (ellMinus p p' r s j) j xm xm))

/-- Lemma 7.1 (`lem:degenerate-quotient-t`) of `irreducible/paper.tex` in the form of
2026-11-26: `Stmt_lem_degenerate_quotient_t` with the arrow weights `Ω(μ → ν₂)`, `Ω(μ → ν₁)` the
BGG weights `OmegaPsi` (before: the box ratios `cArrow`, equal to them by Proposition 6.1(ii)).
The demand sheet is that of `Stmt_lem_degenerate_quotient_t`. -/
def Stmt_lem_degenerate_quotient_t_rev26 : Prop :=
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
            T₁ + OmegaPsi p p' r s k m b ε k₀ (!ε₁) (k₀ + 1) * T₂ =
              FvalAt c d N μ -
                (if lev₁ ≤ N then
                  OmegaPsi p p' r s k m b ε k₀ ε₁ (k₀ + 1) *
                    FvalAt c d (N - lev₁) (muOrb p p' r s ε₁ (k₀ + 1)) else 0)

end Virasoro
