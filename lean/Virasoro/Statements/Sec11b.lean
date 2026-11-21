import Virasoro.Statements.Sec9b

/-!
# Frozen statements: Sections 11–13 of `paper.tex` at 70bac53
(Fusion descent, Jantzen vertex filtration, regularity, the BGG cocycle, the two-term identity)
-/

namespace Virasoro

open Polynomial

/-- Lemma 11.1 (`lem:fusion-injective`), paper.tex l.2295–2309.  Let `p, p' ≥ 2` be coprime,
`0 < r < p`, `0 < s < p'`.  (i) The common roots `d` of `P_{r,s}(b⋆;h_{r,s}(b⋆),d)` and
`P_{p-r,p'-s}(b⋆;h_{r,s}(b⋆),d)` are precisely the elements of `ℱ_{p,p'}(r,s)`.
(ii) `(k,m) ↦ h_{2k+1,2m+1}(b⋆)` is injective on `0 ≤ k < min(r,p-r)`, `0 ≤ m < min(s,p'-s)`.
(iii) The common roots of `𝒫_{r,s}(b⋆,d)` and `𝒫_{p-r,p'-s}(b⋆,d)` are precisely the elements
of `ℱ^±_{p,p'}(r,s)`.

Demand sheet.
- `b⋆² = -p'/p`; no labelling condition (l.2296);
- (i), (iii): equivalences for every complex `d` (l.2298–2307); `P_{R,S}(b;Δ₁,d)` is `fusP`
  with first weight `Δ₁ = h_{r,s}(b⋆)` in both factors, `𝒫` is `genP`;
- (ii): injectivity on the box (l.2302–2303). -/
def Stmt_lem_fusion_injective : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    0 < r → r < p → 0 < s → s < p' →
    (∀ d : ℂ,
      (fusP r s b (kacH r s b) d = 0 ∧ fusP (p - r) (p' - s) b (kacH r s b) d = 0) ↔
        d ∈ fusionSet p p' r s b) ∧
    (∀ k m k' m' : ℕ, k < min r (p - r) → m < min s (p' - s) → k' < min r (p - r) →
      m' < min s (p' - s) →
      kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b = kacH (2 * (k' : ℤ) + 1) (2 * (m' : ℤ) + 1) b →
        k = k' ∧ m = m') ∧
    (∀ d : ℂ, (genP r s b d = 0 ∧ genP (p - r) (p' - s) b d = 0) ↔ d ∈ fusionSetPM p p' r s b)

/-- Proposition 11.2 (`prop:jantzen-vertex`), paper.tex l.2374–2398.  Let `μ ∈ 𝒪_{p,p'}(r,s)` at
layer `k₀ ≥ 0` and `d = h_{2k+1,2m+1}(b⋆) ∈ ℱ_{p,p'}(r,s)`.
(i) For every `i ≥ 0`, `ρ_x(𝒥^{(i)},𝒥^{(i)}) ⊂ x^i ℂ[[x]]`, and
`ρ^{(i)}(a(0),b(0)) := [x^i] ρ_x(a(x),b(x))` is well-defined on `J^i(c⋆,μ) × J^i(c⋆,μ)`,
satisfies the `V_d(1)` Ward identity (10.1) with `Δ₁ = Δ₂ = μ`, and `J^{i+1} ⊂ rad ρ^{(i)}`.
(ii) For every `N ≥ 0`, `F_N(c⋆,μ+x,d)` is holomorphic at `x = 0`, and
`F_N(c⋆,μ,d) = T^irr_N(c⋆,μ,d) + ∑_{i=1}^{j_N(μ)} ∑_± σ^±_i(μ)/γ^±_i(μ) ·
T^irr_{N-(μ^±_{k₀+i}-μ)}(c⋆,μ^±_{k₀+i},d)`, with `γ^±_i(μ) = B^{(i)}(w^±_{k₀+i},w^±_{k₀+i}) ≠ 0`
and `σ^±_i(μ) = ρ^{(i)}(w^±_{k₀+i},w^±_{k₀+i})`.

Demand sheet.
- `MinimalSetting`; node `μ = μ^ε_{k₀}`; `(k,m)` in the fusion box (l.2375–2376);
- (i) `ρ_x` is the primary pairing of `M(c⋆,μ+x)` over `ℂ[x]` (unique by Definition 2.2's
  well-posedness), on vectors of any two levels `N₁, N₂`; the lattice `𝒥^{(i)}` is used through
  polynomial families (`IsJFamily`), which define the same layers as power-series families
  (proof of Lemma 5.3); all `i ≥ 0`;
  divisibility by `x^i`; well-definedness: the coefficient of `x^i` depends only on the values
  `a(0)`, `b(0)`; the Ward identity for `ρ^{(i)}` with `L_{-n}a`, `L_nb` given by coordinates
  `a'`, `b'` with their own families, for all `n ∈ ℤ`; radical: `ρ^{(i)}(a,b) = 0` when `a` has
  a family of order `i+1` (and symmetrically) (l.2378–2384);
- (ii) regular at `μ`: pole order `0`; the vectors `w^±_{k₀+i}` are any family with
  `OrbitLayerSetting`, in coordinates `xp i`, `xm i`; `γ^±_i ≠ 0` for all `i ≥ 1`; the
  decomposition holds for all traces `T₀` at `μ` and `Tp i`, `Tm i` at `μ^±_{k₀+i}` (levels
  `N - (ℓ^±_{k₀+i} - ℓ_{k₀})`; a term is absent when that level is negative); the sum over
  `1 ≤ i ≤ N` equals the sum up to `j_N(μ)` because the terms beyond it are absent
  (l.2385–2396). -/
def Stmt_prop_jantzen_vertex : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let μ : ℂ := muOrb p p' r s ε k₀
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      let lev : Bool → ℕ → ℕ := fun ε' i => ellOrb p p' r s ε' (k₀ + i) - ellOrb p p' r s ε k₀
      (∀ T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X],
        Verma.IsPrimaryPairing (C d) T →
        ∀ (i N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
          (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
          IsJFamily c μ N₁ i a wa → IsJFamily c μ N₂ i a₂ wb →
            (X : ℂ[X]) ^ i ∣ T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb) ∧
            (∀ (wa' : Nat.Partition N₁ → ℂ[X]) (wb' : Nat.Partition N₂ → ℂ[X]),
              IsJFamily c μ N₁ i a wa' → IsJFamily c μ N₂ i a₂ wb' →
                (T (Verma.pbwCoord N₁ wa') (Verma.pbwCoord N₂ wb')).coeff i =
                  (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb)).coeff i) ∧
            (∀ (n : ℤ) (N₁' N₂' : ℕ) (a' : Nat.Partition N₁' → ℂ) (b' : Nat.Partition N₂' → ℂ)
                (wa' : Nat.Partition N₁' → ℂ[X]) (wb' : Nat.Partition N₂' → ℂ[X]),
              IsJFamily c μ N₁' i a' wa' → IsJFamily c μ N₂' i b' wb' →
              Verma.pbwCoord (c := c) (h := μ) N₁' a' =
                Verma.L (-n) (Verma.pbwCoord (c := c) (h := μ) N₁ a) →
              Verma.pbwCoord (c := c) (h := μ) N₂' b' =
                Verma.L n (Verma.pbwCoord (c := c) (h := μ) N₂ a₂) →
                (T (Verma.pbwCoord N₁' wa') (Verma.pbwCoord N₂ wb)).coeff i -
                    (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂' wb')).coeff i =
                  (((N₁ : ℂ) - (N₂ : ℂ)) + (n : ℂ) * d) *
                    (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb)).coeff i) ∧
            (((∃ w, IsJFamily c μ N₁ (i + 1) a w) ∨ (∃ w, IsJFamily c μ N₂ (i + 1) a₂ w)) →
              (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb)).coeff i = 0)) ∧
      (∀ wp wm : ℕ → Verma ℂ c μ, OrbitLayerSetting p p' r s b ε k₀ wp wm →
        ∀ (xp : (i : ℕ) → Nat.Partition (lev true i) → ℂ)
            (xm : (i : ℕ) → Nat.Partition (lev false i) → ℂ),
          (∀ i, 1 ≤ i → Verma.pbwCoord (lev true i) (xp i) = wp i ∧
            Verma.pbwCoord (lev false i) (xm i) = wm i) →
          (∀ i, 1 ≤ i → jform c μ (lev true i) i (xp i) (xp i) ≠ 0 ∧
            jform c μ (lev false i) i (xm i) (xm i) ≠ 0) ∧
          ∀ N : ℕ, poleOrder (Frat c d N) μ = 0 ∧
            ∀ (T₀ : ℂ) (Tp Tm : ℕ → ℂ), IsIrrTrace c μ d N T₀ →
              (∀ i, 1 ≤ i → lev true i ≤ N →
                IsIrrTrace c (muOrb p p' r s true (k₀ + i)) d (N - lev true i) (Tp i)) →
              (∀ i, 1 ≤ i → lev false i ≤ N →
                IsIrrTrace c (muOrb p p' r s false (k₀ + i)) d (N - lev false i) (Tm i)) →
                FvalAt c d N μ = T₀ + ∑ i ∈ Finset.Icc 1 N,
                  ((if lev true i ≤ N then
                      vform c μ d (lev true i) i (xp i) (xp i) /
                        jform c μ (lev true i) i (xp i) (xp i) * Tp i else 0) +
                    (if lev false i ≤ N then
                      vform c μ d (lev false i) i (xm i) (xm i) /
                        jform c μ (lev false i) i (xm i) (xm i) * Tm i else 0)))

/-- Lemma 11.3 (`lem:joint-holomorphicity`), paper.tex l.2499–2506.  Let `λ = h_{r,s}(b⋆)` be an
interior Kac weight, `d⋆ = h_{2k+1,ε(2m+1)}(b⋆) ∈ ℱ^±_{p,p'}(r,s)`, `d(b) = h_{2k+1,ε(2m+1)}(b)`.
Then for every `N ≥ 0` and every `μ ∈ 𝒪_{p,p'}(r,s)`, the rational function
`F_N(c(b),Δ,d(b))` is regular at `(b⋆,μ)`.

Demand sheet.
- `p, p' ≥ 2` coprime, `b⋆² = -p'/p`, `0 < r < p`, `0 < s < p'`; no labelling condition
  (l.2500);
- `(k,m)` in the fusion box, both signs `ε` (l.2501);
- all `N ≥ 0`, all orbit weights (l.2503);
- regular at the point `(b⋆,μ)`: `JointRegular`, for the rational function over `ℂ(b)`
  (the paper's `ℚ(b,Δ)` after extension of scalars) (l.2504–2505). -/
def Stmt_lem_joint_holomorphicity : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    0 < r → r < p → 0 < s → s < p' →
    ∀ (k m : ℕ) (ε : Bool), k < min r (p - r) → m < min s (p' - s) →
      ∀ N : ℕ, ∀ μ ∈ orbitSet p p' r s,
        JointRegular
          (Frat (kacC (RatFunc.X : RatFunc ℂ))
            (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) (RatFunc.X : RatFunc ℂ)) N)
          b μ

end Virasoro
