import Virasoro.Statements.Sec10
import Virasoro.JantzenForm

/-!
# Frozen statements: Section 9 of `paper.tex` at 70bac53 (Irreducible minimal-model traces)
-/

namespace Virasoro

open Polynomial

/-- The value `F_N(c,μ,d)` of the Verma coefficient at a weight `μ` where it is regular. -/
noncomputable def FvalAt (c d : ℂ) (N : ℕ) (μ : ℂ) : ℂ :=
  RatFunc.eval (RingHom.id ℂ) μ (Frat c d N)

/-- `±n` for the sign `ε` (`true` is `+`). -/
def sgnInt (ε : Bool) (n : ℤ) : ℤ := if ε then n else -n

/-- Theorem 9.1 (`thm:descent-regularity`), paper.tex l.1836–1869.  Let `p, p' ≥ 2` be coprime,
`b⋆² = -p'/p`, `λ = h_{r,s}(b⋆)` with `0 < r < p`, `0 < s < p'`.  The map
`(k,m) ↦ h_{2k+1,2m+1}(b⋆)` is injective on the index box of `ℱ_{p,p'}(r,s)`, and for every
`d ∈ ℂ`: (i) `ρ(c⋆,λ,d)` descends to `L(c⋆,λ) × L(c⋆,λ)` iff `d ∈ ℱ_{p,p'}(r,s)`;
(ii) `F_N(c⋆,Δ,d)` is regular at `Δ = λ` for every `N ≥ 0` iff `d ∈ ℱ^±_{p,p'}(r,s)`.
When `d = h_{2k+1,ε(2m+1)}(b⋆) ∈ ℱ^±`, `F_N(c⋆,Δ,d)` is regular at every `μ` of the orbit
`𝒪_{p,p'}(r,s)` and `F_N(c(b),Δ,h_{2k+1,ε(2m+1)}(b))` is jointly regular in `(b,Δ)` at `(b⋆,μ)`.

Demand sheet.
- no labelling condition on `(r,s)` (l.1837–1838); the orbit set `orbitSet` does not depend on
  the choice between `(r,s)` and `(p-r,p'-s)`;
- injectivity on `0 ≤ k < min(r,p-r)`, `0 ≤ m < min(s,p'-s)` (l.1850–1851);
- (i), (ii): equivalences, for every complex `d` (l.1851–1862); descent is `TorusDescends`;
  "so `𝒯^irr` is well-defined": under descent each `T^irr_N` is unique (l.1857–1858);
- regularity at `λ`: pole order `0` of `Frat c⋆ d N` over `ℂ`, for all `N` (l.1860–1862);
- last clause: all `(k,m)` in the box and both signs `ε`; all orbit weights; all `N`; joint
  regularity is `JointRegular` for the rational function over `ℂ(b)` (l.1864–1868). -/
def Stmt_thm_descent_regularity : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    0 < r → r < p → 0 < s → s < p' →
    (∀ k m k' m' : ℕ, k < min r (p - r) → m < min s (p' - s) → k' < min r (p - r) →
      m' < min s (p' - s) →
      kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b = kacH (2 * (k' : ℤ) + 1) (2 * (m' : ℤ) + 1) b →
        k = k' ∧ m = m') ∧
    (∀ d : ℂ,
      (TorusDescends (kacC b) (kacH r s b) d ↔ d ∈ fusionSet p p' r s b) ∧
      (TorusDescends (kacC b) (kacH r s b) d →
        ∀ N : ℕ, ∃! T : ℂ, IsIrrTrace (kacC b) (kacH r s b) d N T) ∧
      ((∀ N : ℕ, poleOrder (Frat (kacC b) d N) (kacH r s b) = 0) ↔
        d ∈ fusionSetPM p p' r s b)) ∧
    (∀ (k m : ℕ) (ε : Bool), k < min r (p - r) → m < min s (p' - s) →
      ∀ μ ∈ orbitSet p p' r s, ∀ N : ℕ,
        poleOrder
          (Frat (kacC b) (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) b) N) μ = 0 ∧
        JointRegular
          (Frat (kacC (RatFunc.X : RatFunc ℂ))
            (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) (RatFunc.X : RatFunc ℂ)) N)
          b μ)

/-- Theorem 9.2 (`thm:first-layer-ratio`), paper.tex l.1874–1905.  Let `b ∈ ℂ^×` be generic,
`t = b²`, `R, S ≥ 1`, `0 ≤ k ≤ R-1`, `0 ≤ m ≤ S-1`, `d = h_{2k+1,2m+1}(b)`, and let
`χ_{R,S}(b)` be the nonzero singular vector of level `RS` (constant PBW coefficients).  Then
`c_{R,S}(t;2k+1,2m+1) := ∂_Δ ρ_{Δ,d}(χ,χ) / ∂_Δ B_Δ(χ,χ)` at `Δ = h_{R,S}(b)` equals
`∏_{(a,b') ≠ (-k,-m)} ((a+k)t + (b'+m)) / ∏_{(a,b') ≠ (0,0)} (at + b')` over
`[1-R,R] × [1-S,S]`, and equals `Ψ_{2k+1,2m+1}(ϖ_{R,-S};b) / Ψ_{2k+1,2m+1}(ϖ_{R,S};b)`.

Demand sheet.
- "generic `b`" is read as `b ≠ 0` and `b² ∉ ℚ`; this is the genericity the proof uses (a
  unique vanishing linear factor at irrational `t`, l.2693–2696), and at such `b` no denominator
  below vanishes;
- `R, S ≥ 1`, `k < R`, `m < S` (l.1876);
- `χ`: every singular vector of level `RS` in `M(c(b),h_{R,S}(b))`, with coordinates `x`; the
  ratio does not depend on its scale (l.1877–1879);
- the two derivatives are `torusCrossScalar` and `crossScalar`; no quotient is formed: the
  denominators `∂_Δ B_Δ(χ,χ)`, `boxDen` and `Ψ(ϖ_{R,S})` are stated to be nonzero and the two
  identities are cross-multiplied (l.1882–1895);
- `Ψ` is `PsiPot` with `ϖ_{R,±S} = (Rb ± Sb⁻¹)/2` (l.1893–1903). -/
def Stmt_thm_first_layer_ratio : Prop :=
  ∀ b : ℂ, b ≠ 0 → (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
    ∀ R S k m : ℕ, 0 < R → 0 < S → k < R → m < S →
      ∀ x : Nat.Partition (R * S) → ℂ,
        Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x) (R * S) →
          boxDen R S (b ^ 2) ≠ 0 ∧
          crossScalar (kacC b) (kacH R S b) x ≠ 0 ∧
          torusCrossScalar (kacC b) (kacH R S b)
              (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) x * boxDen R S (b ^ 2) =
            crossScalar (kacC b) (kacH R S b) x * boxNum R S k m (b ^ 2) ∧
          PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b ≠ 0 ∧
          boxNum R S k m (b ^ 2) * PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b =
            boxDen R S (b ^ 2) * PsiPot k m (((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2) b

/-- Theorem 9.3 (`thm:gen-rocha-caridi`), paper.tex l.1926–1960.  Let `b⋆² = -p'/p`, `λ` an
interior Kac weight, `d = h_{u,v}(b⋆) ∈ ℱ_{p,p'}(r,s)`, `(u,v) = (2k+1,2m+1)`.  Then
`𝒯^irr_{c⋆,λ,d}(q) = ℱ^Verma_{c⋆,λ,d}(q) + ∑_{j≥1} (-1)^j (Ω_{u,v}(λ→μ⁺_j) q^{ℓ⁺_j}
ℱ^Verma_{c⋆,μ⁺_j,d}(q) + Ω_{u,v}(λ→μ⁻_j) q^{ℓ⁻_j} ℱ^Verma_{c⋆,μ⁻_j,d}(q))`.
(a) At `d = 0`, `Ω_{1,1} ≡ 1` and `ℱ^Verma_{c⋆,μ,0}(q) = φ(q)⁻¹`.
(b) `T^irr_N(c⋆,λ,d) ∈ ℚ` for every `N`.
(c) `σ^±_j(λ)/γ^±_j(λ) = Ω_{u,v}(λ→μ^±_j)` for every layer `j ≥ 1`.

Demand sheet.
- `MinimalSetting`: the orbit data `μ^±_j`, `ℓ^±_j` of Section 10 are defined after the
  labelling `n₁ < pp'` (l.2164–2167);
- `(k,m)` in the fusion box (l.1929–1930);
- the identity is read at each coefficient `q^N`; since `ℓ^±_j ≥ j`, the sum over `j` stops at
  `N` (l.1930–1931); `ℱ^Verma` at an orbit weight is the value of `F_M` there, regular by
  Theorem 9.1 (stated as the second clause);
- `T^irr_N`: existence, and the identity for every `T` with `IsIrrTrace`;
- `Ω` is `Omega` from the node `λ` (layer `0`);
- (a) `k = m = 0`: `d = 0`, `Ω = 1` for both signs and all `j`, `F_N(c⋆,μ,0) = p(N)` at every
  orbit weight (l.1945–1947);
- (b) rationality of the value; "by a finite algebraic procedure" is not a formal claim
  (l.1948–1952);
- (c) cross-multiplied with `γ^±_j`, for a family as in Theorem 5.8; `σ` is `vform`
  (l.1953–1958). -/
def Stmt_thm_gen_rocha_caridi : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let lam : ℂ := kacH r s b
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      (∀ N : ℕ, (∃ T : ℂ, IsIrrTrace c lam d N T) ∧
        ∀ T : ℂ, IsIrrTrace c lam d N T →
          T = FvalAt c d N lam + ∑ j ∈ Finset.Icc 1 N, (-1 : ℂ) ^ j *
            ((if ellOrb p p' r s true j ≤ N then
                (Omega p p' r s k m true 0 true j : ℂ) *
                  FvalAt c d (N - ellOrb p p' r s true j) (muOrb p p' r s true j) else 0) +
              (if ellOrb p p' r s false j ≤ N then
                (Omega p p' r s k m true 0 false j : ℂ) *
                  FvalAt c d (N - ellOrb p p' r s false j) (muOrb p p' r s false j) else 0))) ∧
      (∀ (ε : Bool) (j M : ℕ), (Frat c d M).denom.eval (muOrb p p' r s ε j) ≠ 0) ∧
      (k = 0 → m = 0 → d = 0 ∧
        (∀ (ε : Bool) (j : ℕ), Omega p p' r s k m true 0 ε j = 1) ∧
        ∀ (ε : Bool) (j N : ℕ),
          FvalAt c d N (muOrb p p' r s ε j) = (Fintype.card (Nat.Partition N) : ℂ)) ∧
      (∀ (N : ℕ) (T : ℂ), IsIrrTrace c lam d N T → ∃ q : ℚ, T = (q : ℂ)) ∧
      (∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
        ∀ j : ℕ, 1 ≤ j →
          (∀ xp : Nat.Partition (ellPlus p p' r s j) → ℂ,
            Verma.pbwCoord (ellPlus p p' r s j) xp = wp j →
              vform c lam d (ellPlus p p' r s j) j xp xp =
                (Omega p p' r s k m true 0 true j : ℂ) *
                  jform c lam (ellPlus p p' r s j) j xp xp) ∧
          (∀ xm : Nat.Partition (ellMinus p p' r s j) → ℂ,
            Verma.pbwCoord (ellMinus p p' r s j) xm = wm j →
              vform c lam d (ellMinus p p' r s j) j xm xm =
                (Omega p p' r s k m true 0 false j : ℂ) *
                  jform c lam (ellMinus p p' r s j) j xm xm))

open Classical in
/-- The claims of Corollary 9.4 for the insertion `d(b) = h_{u,v}(b)` and a set `act` of active
Kac labels, at `b = b⋆`: every multiplier `ℛ_{R,S}(b,d(b))` of an active label is regular at
`b⋆`; no two active poles collide; no shifted weight of an active label hits an active pole; and
`H_N(c⋆,Δ,d(b⋆))` is given by the recursion over the active labels evaluated at `b⋆`. -/
def CollisionFree (b : ℂ) (u v : ℤ) (act : Label → Prop) : Prop :=
  (∀ a : Label, 0 < a.1 → 0 < a.2 → act a →
    (genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ))).denom.eval b ≠ 0) ∧
  (∀ a a' : Label, 0 < a.1 → 0 < a.2 → act a → 0 < a'.1 → 0 < a'.2 → act a' → a ≠ a' →
    kacHL a b ≠ kacHL a' b) ∧
  (∀ a a' : Label, 0 < a.1 → 0 < a.2 → act a → 0 < a'.1 → 0 < a'.2 → act a' →
    kacH (a.1 : ℤ) (-(a.2 : ℤ)) b ≠ kacHL a' b) ∧
  (∀ N : ℕ, 1 ≤ N →
    Hrat (kacC b) (kacH u v b) N =
      ∑ a ∈ (labels N).filter act,
        RatFunc.C (RatFunc.eval (RingHom.id ℂ) b
            (genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ)))) /
          (RatFunc.X - RatFunc.C (kacHL a b)) *
        RatFunc.C (RatFunc.eval (RingHom.id ℂ) (kacHL a b + (a.lvl : ℂ))
          (Hrat (kacC b) (kacH u v b) (N - a.lvl))))

/-- Corollary 9.4 (`cor:collision-free`), paper.tex l.1967–1979.  In Theorem 9.3, suppose
`d = h_{1,2m+1}(b⋆)` with `0 ≤ m < min(s,p'-s)` (or dually `d = h_{2k+1,1}(b⋆)` with
`0 ≤ k < min(r,p-r)`).  Then in the truncated recursion for `H_N(c(b),Δ,d(b))` restricted to
Kac labels `(R,S)` with `S ≤ m` (resp. `R ≤ k`), every multiplier `ℛ_{R,S}(b,d(b))` is regular
at `b⋆`, no two active poles collide, and no shifted weight `h_{R₁,-S₁}(b⋆)` hits an active pole;
thus the Verma series are evaluated at `b = b⋆` by the unmodified truncated recursion.

Demand sheet.
- `MinimalSetting` (the setting of Theorem 9.3);
- first case: all `m < min(s,p'-s)`, active labels `S ≤ m`, `d(b) = h_{1,2m+1}(b)`; dual case:
  all `k < min(r,p-r)`, active labels `R ≤ k`, `d(b) = h_{2k+1,1}(b)` (l.1968–1972);
- regular: the reduced denominator of `ℛ_{R,S}(b,d(b)) ∈ ℂ(b)` does not vanish at `b⋆`;
  no collision: distinct active labels have distinct weights at `b⋆`; no shifted hit: for all
  pairs of active labels, including equal ones (l.1972–1975);
- "evaluated directly at `b = b⋆` by the unmodified truncated recursion" is read as the
  recursion identity for `H_N(c⋆,Δ,d(b⋆))`, `N ≥ 1`, over the active labels with all data
  evaluated at `b⋆`, as rational functions of `Δ` over `ℂ` (l.1975–1978). -/
def Stmt_cor_collision_free : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    (∀ m : ℕ, m < min s (p' - s) →
      CollisionFree b 1 (2 * (m : ℤ) + 1) (fun a => a.2 ≤ m)) ∧
    (∀ k : ℕ, k < min r (p - r) →
      CollisionFree b (2 * (k : ℤ) + 1) 1 (fun a => a.1 ≤ k))

end Virasoro
