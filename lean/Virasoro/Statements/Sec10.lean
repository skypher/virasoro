import Virasoro.Statements.Sec6
import Virasoro.Orbit
import Virasoro.Irreducible
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Frozen statements: Section 10 of `paper.tex` at 70bac53
(Two-weight Ward identities and braided orbits)
-/

namespace Virasoro

open Polynomial

/-- Lemma 10.1 (`lem:two-weight-ward`), paper.tex l.2045–2068.  For `c, Δ₁, Δ₂, d ∈ ℂ` there is a
unique bilinear form `ρ_{Δ₁,Δ₂;d} : M(c,Δ₁) × M(c,Δ₂) → ℂ` with `ρ(v_{Δ₁}, v_{Δ₂}) = 1` and the
Ward identity (10.1).  Its matrix entries in the PBW bases belong to `ℚ[c,Δ₁,Δ₂,d]`; it satisfies
`ρ_{Δ₁,Δ₂;d}(u,v) = ρ_{Δ₂,Δ₁;d}(v,u)`; and `ρ_{Δ,Δ;0} = B_{c,Δ}`.

Demand sheet.
- complex `c, Δ₁, Δ₂, d` (l.2046); existence and uniqueness (`∃!`) (l.2046–2048);
- the Ward identity for all `m ∈ ℤ`; the paper states it for homogeneous `u, v` with the factor
  `(Δ₁+N₁) - (Δ₂+N₂)`; `IsTwoWeightPairing` states it for all `u, v` with `L₀`, which is the
  same by bilinearity (l.2049–2055);
- polynomial entries: for each pair of partitions (of any two levels) one polynomial over `ℚ`
  in `(c, Δ₁, Δ₂, d)`, uniform in the parameters (l.2057–2058);
- symmetry (10.2) between the forms of `(Δ₁,Δ₂)` and `(Δ₂,Δ₁)` (l.2059–2060);
- `Δ₁ = Δ₂`, `d = 0`: equality with every Shapovalov form (l.2062–2066). -/
def Stmt_lem_two_weight_ward : Prop :=
  (∀ c Δ₁ Δ₂ d : ℂ, ∃! T : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c Δ₂ →ₗ[ℂ] ℂ,
    Verma.IsTwoWeightPairing d T) ∧
  (∀ (N₁ N₂ : ℕ) (Y : Nat.Partition N₁) (Y' : Nat.Partition N₂),
    ∃ Q : MvPolynomial (Fin 4) ℚ, ∀ (c Δ₁ Δ₂ d : ℂ)
      (T : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c Δ₂ →ₗ[ℂ] ℂ), Verma.IsTwoWeightPairing d T →
        T (Verma.neg Y.word) (Verma.neg Y'.word) = MvPolynomial.aeval ![c, Δ₁, Δ₂, d] Q) ∧
  (∀ (c Δ₁ Δ₂ d : ℂ) (T : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c Δ₂ →ₗ[ℂ] ℂ)
      (T' : Verma ℂ c Δ₂ →ₗ[ℂ] Verma ℂ c Δ₁ →ₗ[ℂ] ℂ),
    Verma.IsTwoWeightPairing d T → Verma.IsTwoWeightPairing d T' → ∀ u v, T u v = T' v u) ∧
  (∀ (c Δ : ℂ) (T B : Verma ℂ c Δ →ₗ[ℂ] Verma ℂ c Δ →ₗ[ℂ] ℂ),
    Verma.IsTwoWeightPairing 0 T → Verma.IsShapovalov B → ∀ u v, T u v = B u v)

/-- Proposition 10.2 (`prop:fusion-poly`), paper.tex l.2115–2146.  Fix `R, S ≥ 1`.
(i) There is a unique family of singular vectors `χ_{R,S}(b) ∈ M(c(b),h_{R,S}(b))_{RS}` with
`L_{-1}^{RS}`-coefficient `1`; its PBW coefficients belong to `ℚ[b²,b⁻²]`, so `χ_{R,S}(b⋆)` is
well-defined and nonzero at every `b⋆ ∈ ℂ^×`.
(ii) For every `b ∈ ℂ^×` and `Δ₁, Δ₂ ∈ ℂ`,
`ρ_{h_{R,S}(b),Δ₁;Δ₂}(χ_{R,S}(b), v_{Δ₁}) = C_{R,S}(b) P_{R,S}(b;Δ₁,Δ₂)` with `C_{R,S}(b) ∈ ℂ^×`
independent of `(Δ₁,Δ₂)`; the roots in `d` of `P_{R,S}(b;h_{R,S}(b),d)` are precisely
`d = h_{u,v}(b)`, `u ∈ {1,3,…,2R-1}`, `v ∈ {1,3,…,2S-1}`.

Demand sheet.
- `R, S ≥ 1` (l.2116);
- (i) the family is over `ℚ(b)` (`b = RatFunc.X`), coordinates `p`; existence and uniqueness
  among normalized singular vectors of level `RS`; each coordinate is `f(b²)/b^{2n}` with
  `f ∈ ℚ[X]` (l.2118–2121); regular at every `b₁ ≠ 0` (l.2121–2122);
- (ii) all `b₁ ≠ 0`; `χ_{R,S}(b₁)` is the value `p₁` of the family; the pairing is the
  two-weight pairing between `M(c, h_{R,S}(b₁))` and `M(c, Δ₁)` with external weight `Δ₂`, as
  printed (l.2127); `C` nonzero and independent of `Δ₁, Δ₂` (quantifier order `∃ C, ∀ Δ₁ Δ₂`)
  (l.2130–2131);
- `P_{R,S}` is `fusP`, a function of `(Δ₁,Δ₂)` (the paper's product in `λ_i` with
  `Δ_i = (Q²-λ_i²)/4`, l.2125, 2133–2138);
- roots: an equivalence for every complex `d` (l.2139–2143). -/
def Stmt_prop_fusion_poly : Prop :=
  ∀ R S : ℕ, 0 < R → 0 < S →
    ∃ p : Nat.Partition (R * S) → RatFunc ℚ,
      (p (onesPartition (R * S)) = 1 ∧
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH R S RatFunc.X)
            (R * S) p) (R * S)) ∧
      (∀ p' : Nat.Partition (R * S) → RatFunc ℚ, p' (onesPartition (R * S)) = 1 →
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH R S RatFunc.X)
            (R * S) p') (R * S) → p' = p) ∧
      (∀ Y, ∃ (f : ℚ[X]) (n : ℕ),
        p Y = Polynomial.aeval ((RatFunc.X : RatFunc ℚ) ^ 2) f / RatFunc.X ^ (2 * n)) ∧
      (∀ b₁ : ℂ, b₁ ≠ 0 →
        (∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (p Y)) ≠ 0) ∧
        (let p₁ : Nat.Partition (R * S) → ℂ := fun Y => RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y)
         ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ (Δ₁ Δ₂ : ℂ)
           (T : Verma ℂ (kacC b₁) (kacH R S b₁) →ₗ[ℂ] Verma ℂ (kacC b₁) Δ₁ →ₗ[ℂ] ℂ),
           Verma.IsTwoWeightPairing Δ₂ T →
             T (Verma.pbwCoord (R * S) p₁) Verma.hw = C₀ * fusP R S b₁ Δ₁ Δ₂) ∧
        (∀ d : ℂ, fusP R S b₁ (kacH R S b₁) d = 0 ↔
          ∃ u ∈ oddsBelow R, ∃ v ∈ oddsBelow S, d = kacH (u : ℤ) (v : ℤ) b₁))

/-- A choice of singular vectors at an orbit weight `μ = μ^ε_{k₀}` as in Lemma 10.3(i): `wp i`,
`wm i` are singular vectors of `M(c⋆,μ)` of weights `μ^±_{k₀+i}`, and
`J^i(c⋆,μ) = U(Vir_-) wp_i + U(Vir_-) wm_i` for `i ≥ 1`. -/
def OrbitLayerSetting (p p' r s : ℕ) (b : ℂ) (ε : Bool) (k₀ : ℕ)
    (wp wm : ℕ → Verma ℂ (kacC b) (muOrb p p' r s ε k₀)) : Prop :=
  (∀ i : ℕ, 1 ≤ i →
    Verma.IsSingular (wp i) (ellOrb p p' r s true (k₀ + i) - ellOrb p p' r s ε k₀) ∧
    Verma.IsSingular (wm i) (ellOrb p p' r s false (k₀ + i) - ellOrb p p' r s ε k₀)) ∧
  (∀ i : ℕ, 1 ≤ i →
    jantzen (kacC b) (muOrb p p' r s ε k₀) i = Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i))

/-- Lemma 10.3 (`lem:bgg-arrows`), paper.tex l.2185–2229.  Let `μ ∈ 𝒪_{p,p'}(r,s)` lie at layer
`k ≥ 0`.
(i) `J^i(c⋆,μ) = M(c⋆,μ⁺_{k+i}) + M(c⋆,μ⁻_{k+i})`, with intersection `J^{i+1}(c⋆,μ)` and
`J^i/J^{i+1} ≅ L(c⋆,μ⁺_{k+i}) ⊕ L(c⋆,μ⁻_{k+i})`.
(ii) Each primitive arrow `μ → ν` has a unique positive Kac label `(R,S)` with
`h_{R,S}(b⋆) = μ`, `h_{R,-S}(b⋆) = ν`, determined by `p'R + pS = n_ν`, `p'R - pS = ±n_μ`.
(iii) `R ≡ r` or `p-r (mod p)`, `S ≡ s` or `p'-s (mod p')`, `R ≥ min(r,p-r)`,
`S ≥ min(s,p'-s)`, `min(R/p, S/p') < 1`; no `(qp,qp')`, `q ≠ 0`, lies in `[1-R,R] × [1-S,S]`,
and `γ_{R,S}(b⋆) = ∂_Δ B_{c⋆,Δ}(χ_{R,S}(b⋆), χ_{R,S}(b⋆))|_{Δ=μ} ≠ 0`.
(iv) The two arrows out of `μ` have distinct levels; with `m_i = p'R_i - pS_i`,
`n_i = p'R_i + pS_i`, `d/dt (h_{R₁,S₁}(t) - h_{R₂,S₂}(t))|_{t⋆} = (m₂n₂ - m₁n₁)/(4p'²) ≠ 0`,
`t⋆ = -p'/p`; and `max(ℓ⁺₁,ℓ⁻₁) < min(ℓ⁺₂,ℓ⁻₂)`.

Demand sheet.
- `MinimalSetting` (the normalization `n₁ < pp'` of l.2164–2167); every node `μ^ε_k`, `k ≥ 0`
  (for `k = 0` both signs give `μ_0 = λ`);
- (i) the submodules `M(c⋆,μ^±_{k+i})` are `U(Vir_-) w` for singular vectors `w` of these
  weights: existence of a family with `OrbitLayerSetting`; intersection clause as an equality
  of submodules; the isomorphism clause is read as: each `U(Vir_-) w^±_i / J^{i+1}` is a simple
  highest-weight module (no Virasoro submodule lies strictly between `J^{i+1}` and
  `U(Vir_-) w^±_i`, and they differ), which with the intersection clause is the stated
  decomposition (l.2190–2197);
- (ii) the label is `arrowLabel`; positivity, the two weight equations, the two momentum
  equations, and uniqueness among positive integer pairs (l.2198–2203);
- (iii) congruences, lower bounds, `R < p ∨ S < p'`, the box clause for all `q ≠ 0`; `γ_{R,S}`
  is the crossing scalar of the value at `b⋆` of the normalized family over `ℚ(b)`
  (l.2204–2216);
- (iv) the arrows to `μ⁺_{k+1}` (label 1) and `μ⁻_{k+1}` (label 2); derivative in `t = b²` as
  `HasDerivAt` of `hT` at `t⋆ = -p'/p`; nonvanishing; the last inequality concerns the levels
  of `λ` (l.2217–2227). -/
def Stmt_lem_bgg_arrows : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    max (ellPlus p p' r s 1) (ellMinus p p' r s 1) <
      min (ellPlus p p' r s 2) (ellMinus p p' r s 2) ∧
    ∀ (ε : Bool) (k : ℕ),
      (∃ wp wm : ℕ → Verma ℂ (kacC b) (muOrb p p' r s ε k),
        OrbitLayerSetting p p' r s b ε k wp wm ∧
        ∀ i : ℕ, 1 ≤ i →
          Verma.negSpan (wp i) ⊓ Verma.negSpan (wm i) =
            jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∧
          Verma.negSpan (wp i) ≠ jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∧
          Verma.negSpan (wm i) ≠ jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∧
          ∀ W : Submodule ℂ (Verma ℂ (kacC b) (muOrb p p' r s ε k)), Verma.IsVirSubmodule W →
            jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ≤ W →
              (W ≤ Verma.negSpan (wp i) →
                W = jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∨ W = Verma.negSpan (wp i)) ∧
              (W ≤ Verma.negSpan (wm i) →
                W = jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∨ W = Verma.negSpan (wm i))) ∧
      (∀ ε' : Bool, ∃ R S : ℕ, 0 < R ∧ 0 < S ∧
        arrowLabel p p' (nOrb p p' r s ε k) (nOrb p p' r s ε' (k + 1)) = ((R : ℤ), (S : ℤ)) ∧
        kacH R S b = muOrb p p' r s ε k ∧
        kacH (R : ℤ) (-(S : ℤ)) b = muOrb p p' r s ε' (k + 1) ∧
        (p' : ℤ) * R + (p : ℤ) * S = nOrb p p' r s ε' (k + 1) ∧
        ((p' : ℤ) * R - (p : ℤ) * S = nOrb p p' r s ε k ∨
          (p' : ℤ) * R - (p : ℤ) * S = -nOrb p p' r s ε k) ∧
        (∀ R' S' : ℤ, 0 < R' → 0 < S' → kacH R' S' b = muOrb p p' r s ε k →
          kacH R' (-S') b = muOrb p p' r s ε' (k + 1) → R' = R ∧ S' = S) ∧
        (R % p = r % p ∨ R % p = (p - r) % p) ∧ (S % p' = s % p' ∨ S % p' = (p' - s) % p') ∧
        min r (p - r) ≤ R ∧ min s (p' - s) ≤ S ∧ (R < p ∨ S < p') ∧
        (∀ q : ℤ, q ≠ 0 → (q * p, q * p') ∉ boxSet R S) ∧
        (∀ pc : Nat.Partition (R * S) → RatFunc ℚ, pc (onesPartition (R * S)) = 1 →
          Verma.IsSingular
            (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH R S RatFunc.X)
              (R * S) pc) (R * S) →
          crossScalar (kacC b) (kacH R S b)
            (fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (pc Y)) ≠ 0)) ∧
      (∀ R₁ S₁ R₂ S₂ : ℤ,
        arrowLabel p p' (nOrb p p' r s ε k) (nOrb p p' r s true (k + 1)) = (R₁, S₁) →
        arrowLabel p p' (nOrb p p' r s ε k) (nOrb p p' r s false (k + 1)) = (R₂, S₂) →
          R₁ * S₁ ≠ R₂ * S₂ ∧
          (let m₁ : ℤ := p' * R₁ - p * S₁
           let n₁ : ℤ := p' * R₁ + p * S₁
           let m₂ : ℤ := p' * R₂ - p * S₂
           let n₂ : ℤ := p' * R₂ + p * S₂
           0 < n₁ ∧ 0 < n₂ ∧ m₂ * n₂ - m₁ * n₁ ≠ 0 ∧
           HasDerivAt (fun t : ℂ => hT R₁ S₁ t - hT R₂ S₂ t)
             (((m₂ * n₂ - m₁ * n₁ : ℤ) : ℂ) / (4 * (p' : ℂ) ^ 2)) (-(p' : ℂ) / p)))

end Virasoro
