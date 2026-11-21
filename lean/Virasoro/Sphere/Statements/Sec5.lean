import Virasoro.Sphere.Germs
import Virasoro.Statements.Sec5c

/-!
# Frozen statements: `sphere/paper.tex`, Sections 5 and 6
(Minimal-model pole orders, top Jantzen layer, sharpness; examples)

Pole orders are taken over `K4 = ℂ(Δ₁,…,Δ₄)` (indeterminate external weights).
-/

namespace Virasoro.Sphere

open Polynomial

/-- Theorem 5.1 (`thm:jantzen-bound`), sphere/paper.tex l.1480–1486.  For every coprime pair
`p, p' ≥ 2`, every interior Kac weight `λ = h_{r,s}(b⋆)` and every `N ≥ 0`, `ℬ_N(c⋆,Δ,Δ_i)` and
`H_N(c⋆,Δ,Δ_i)` have poles of order at most `j_N(λ)` at `Δ = λ`.

Demand sheet.
- `MinimalSetting` (the labelling `n₁ < pp'` of l.1455–1458, which defines `j_N(λ)`); the
  assumption `p' > p` of l.1448 is not used in the statement;
- all `N ≥ 0`; both coefficients; a bound (l.1482–1485);
- indeterminate external weights. -/
def Stmt_thm_jantzen_bound : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ N : ℕ,
    poleOrder (Bsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) ≤ jDepth p p' r s N ∧
    poleOrder (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) ≤ jDepth p p' r s N

/-- The three-point scalar `⟨w|Φ_b(1)|Δ_a⟩ = ∑_Y x_Y γ_Y(λ;Δ_a,Δ_b)` of a vector `w` of
`M(c,λ)` with level-`ℓ` coordinates `x`, for weights in a field `𝔽 ⊇ ℂ`. -/
noncomputable def piScalar {𝔽 : Type*} [Field 𝔽] [Algebra ℂ 𝔽] (lam : ℂ) {ℓ : ℕ}
    (x : Nat.Partition ℓ → ℂ) (Δa Δb : 𝔽) : 𝔽 :=
  ∑ Y, algebraMap ℂ 𝔽 (x Y) * gammaY (algebraMap ℂ 𝔽 lam) Δa Δb Y.word

/-- Lemma 5.2 (`lem:pi-factorization`), sphere/paper.tex l.1499–1523.  For `k ≥ 1` let `w^±_k`
be the unique singular vector of level `ℓ^±_k` in `M(c⋆,λ)` with `L_{-1}`-coefficient `1` and
`π^±_k(Δ_a,Δ_b) = ⟨w^±_k|Φ_b(1)|Δ_a⟩`.
(i) For odd `k = 2j+1`: `π^±_k = P_{R^±_k,S^±_k}(b⋆,Δ_a,Δ_b)` with
`(R⁺,S⁺) = (r+jp, s+jp')`, `(R⁻,S⁻) = ((j+1)p-r, (j+1)p'-s)`.
(ii) For even `k = 2j`: `π^±_k = P_{r,s} P_{R^±_k,S^±_k}` with `(R⁺,S⁺) = (r+jp, jp'-s)`,
`(R⁻,S⁻) = (jp-r, jp'+s)`.
(iii) With `Δ_a = (a_a² - (p'-p)²)/(4pp')`, `Δ_b` likewise: every zero of `π^±_k` lies on a
hyperplane `a_a ± a_b = c` with `|c| ≤ m^±_k - p' - p`, and both hyperplanes
`a_a - a_b = ±(m^±_k - p' - p)` lie in the zero locus.

Demand sheet.
- `MinimalSetting`; `k ≥ 1`; both signs (`ε = true` is `+`);
- `w^±_k`: every normalized singular vector of level `ℓ^±_k` (the lemma calls it unique), in
  coordinates `x` (l.1501–1502);
- (i), (ii): identities for all complex `Δ_a, Δ_b`; `P` is `fusP` (l.1505–1511);
- (iii): for all complex `a_a, a_b`; the constant `c` is an integer; `m^±_k` is `nOrb`
  (l.1512–1521). -/
def Stmt_lem_pi_factorization : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (k : ℕ) (ε : Bool), 1 ≤ k →
    ∀ x : Nat.Partition (ellOrb p p' r s ε k) → ℂ, x (onesPartition _) = 1 →
      Verma.IsSingular
        (Verma.pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
        (ellOrb p p' r s ε k) →
      (k % 2 = 1 → ∀ Δa Δb : ℂ,
        piScalar (kacH r s b) x Δa Δb =
          (if ε then fusP (r + k / 2 * p) (s + k / 2 * p') b Δa Δb
            else fusP ((k / 2 + 1) * p - r) ((k / 2 + 1) * p' - s) b Δa Δb)) ∧
      (k % 2 = 0 → ∀ Δa Δb : ℂ,
        piScalar (kacH r s b) x Δa Δb =
          fusP r s b Δa Δb *
            (if ε then fusP (r + k / 2 * p) (k / 2 * p' - s) b Δa Δb
              else fusP (k / 2 * p - r) (k / 2 * p' + s) b Δa Δb)) ∧
      (∀ aa ab : ℂ,
        let Δa : ℂ := (aa ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')
        let Δb : ℂ := (ab ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')
        let mm : ℤ := nOrb p p' r s ε k - p' - p
        (piScalar (kacH r s b) x Δa Δb = 0 →
          ∃ c₀ : ℤ, |c₀| ≤ mm ∧ (aa + ab = (c₀ : ℂ) ∨ aa - ab = (c₀ : ℂ))) ∧
        ((aa - ab = (mm : ℂ) ∨ aa - ab = -(mm : ℂ)) → piScalar (kacH r s b) x Δa Δb = 0))

/-- The summand `π(Δ₄,Δ₃) π(Δ₁,Δ₂)/γ · f_{N-ℓ}(c⋆, λ+ℓ, Δ_i)` of (5.1), (5.2) for a singular
vector of level `ℓ` with coordinates `x`, where `f` is `ℬ` or `H`; `0` when `ℓ > N`. -/
noncomputable def topTermSph (f : ℕ → RatFunc K4) (c lam : ℂ) (N ℓ k : ℕ)
    (x : Nat.Partition ℓ → ℂ) : K4 :=
  if ℓ ≤ N then
    piScalar lam x (ΔK 3) (ΔK 2) * piScalar lam x (ΔK 0) (ΔK 1) * cK (jform c lam ℓ k x x)⁻¹ *
      RatFunc.eval (RingHom.id K4) (cK (lam + (ℓ : ℂ))) (f (N - ℓ))
  else 0

/-- Theorem 5.3 (`thm:top-layer`), sphere/paper.tex l.1550–1570.  Let `k ≥ 1`,
`ℓ_k ≤ N < ℓ_{k+1}`, `γ^±_k = B^k(w^±_k,w^±_k)`.  Then `j_N(λ) = k`; for each sign with
`ℓ^±_k ≤ N`, `γ^±_k ≠ 0` and `det G_M(c⋆,μ^±_k) ≠ 0` for `0 ≤ M ≤ N - ℓ^±_k`; and
`lim_{Δ→λ} (Δ-λ)^k ℬ_N = ∑_{±: ℓ^±_k ≤ N} π^±_k(Δ₄,Δ₃) π^±_k(Δ₁,Δ₂)/γ^±_k ·
ℬ_{N-ℓ^±_k}(c⋆,μ^±_k,Δ_i)`, and the same with `H` in place of `ℬ`.

Demand sheet.
- `MinimalSetting`, a family `w^±_k` as in the torus Theorem 5.8 (`TopLayerSetting`), in
  coordinates `xp`, `xm`; the summands do not depend on the scale of `w^±_k`;
- `k ≥ 1`, `ℓ_k ≤ N < ℓ_{k+1}` (l.1552);
- `j_N(λ) = k`; per sign with `ℓ^±_k ≤ N`: `γ ≠ 0`, determinants nonzero for all
  `M ≤ N - ℓ^±_k` (l.1555–1557);
- the two limits: pole order at most `k` and coefficient of `(Δ-λ)^{-k}`, over
  `ℂ(Δ₁,…,Δ₄)` (l.1559–1568). -/
def Stmt_thm_top_layer : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → ellMin p p' r s k ≤ N → N < ellMin p p' r s (k + 1) →
        jDepth p p' r s N = k ∧
        (∀ xp : Nat.Partition (ellPlus p p' r s k) → ℂ,
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k → ellPlus p p' r s k ≤ N →
            jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp ≠ 0 ∧
            ∀ M : ℕ, M ≤ N - ellPlus p p' r s k →
              (gram (kacC b) (kacH r s b + (ellPlus p p' r s k : ℂ)) M).det ≠ 0) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s k) → ℂ,
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k → ellMinus p p' r s k ≤ N →
            jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm ≠ 0 ∧
            ∀ M : ℕ, M ≤ N - ellMinus p p' r s k →
              (gram (kacC b) (kacH r s b + (ellMinus p p' r s k : ℂ)) M).det ≠ 0) ∧
        (∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            (poleOrder (Bsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) ≤ k ∧
              ppCoeff (Bsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) k =
                topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N
                    (ellPlus p p' r s k) k xp +
                  topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N
                    (ellMinus p p' r s k) k xm) ∧
            (poleOrder (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) ≤ k ∧
              ppCoeff (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) k =
                topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N
                    (ellPlus p p' r s k) k xp +
                  topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N
                    (ellMinus p p' r s k) k xm))

/-- Theorem 5.4 (`thm:sharp-B`), sphere/paper.tex l.1607–1615.  For every coprime pair
`p, p' ≥ 2`, every interior Kac weight `λ` and every `N ≥ 1`, `ℬ_N(c⋆,Δ,Δ_1,…,Δ_4)`, as a
rational function of `Δ` over `ℚ(Δ_1,…,Δ_4)`, has a pole of order exactly `j_N(λ)` at `Δ = λ`.

Demand sheet.
- `MinimalSetting`; every `N ≥ 1` (l.1609–1610);
- indeterminate external weights: over `ℂ(Δ₁,…,Δ₄)`, where the pole order is the same as over
  `ℚ(Δ₁,…,Δ₄)` (l.1612–1613);
- identity `poleOrder = j_N(λ)` (l.1614). -/
def Stmt_thm_sharp_B : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ N : ℕ, 1 ≤ N →
    poleOrder (Bsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) = jDepth p p' r s N

/-- Theorem 5.5 (`thm:sharp-H`), sphere/paper.tex l.1693–1701.  The same for the elliptic
coefficient `H_N(c⋆,Δ,Δ_1,…,Δ_4)`: a pole of order exactly `j_N(λ)` at `Δ = λ` for every
`N ≥ 1`.  Demand sheet as for `Stmt_thm_sharp_B`. -/
def Stmt_thm_sharp_H : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ N : ℕ, 1 ≤ N →
    poleOrder (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) = jDepth p p' r s N

/-- The leading coefficient `P_{R₁,S₁}(Δ₄,Δ₃) P_{R₂,S₂}(Δ₄,Δ₃) P_{R₁,S₁}(Δ₁,Δ₂)
P_{R₂,S₂}(Δ₁,Δ₂)/γ` of the examples of Section 6, at `b⋆ = b`. -/
noncomputable def exampleCoeff (b : ℂ) (R₁ S₁ R₂ S₂ : ℕ) (γ : ℂ) : K4 :=
  fusP R₁ S₁ (cK b) (ΔK 3) (ΔK 2) * fusP R₂ S₂ (cK b) (ΔK 3) (ΔK 2) *
    fusP R₁ S₁ (cK b) (ΔK 0) (ΔK 1) * fusP R₂ S₂ (cK b) (ΔK 0) (ΔK 1) / cK γ

/-- "The first double pole of `ℬ_N` and `H_N` at `Δ = λ` occurs at level `N`, with leading
Laurent coefficient `coef`", at the charge `c`. -/
def FirstDoublePole (c lam : ℂ) (N : ℕ) (coef : K4) : Prop :=
  (∀ M : ℕ, M < N → poleOrder (Bsph (cK c) ΔK M) (cK lam) ≤ 1 ∧
    poleOrder (Hsph (cK c) ΔK M) (cK lam) ≤ 1) ∧
  poleOrder (Bsph (cK c) ΔK N) (cK lam) = 2 ∧ poleOrder (Hsph (cK c) ΔK N) (cK lam) = 2 ∧
  ppCoeff (Bsph (cK c) ΔK N) (cK lam) 2 = coef ∧ ppCoeff (Hsph (cK c) ΔK N) (cK lam) 2 = coef

/-- Proposition 6.1 (`prop:c0-example`), sphere/paper.tex l.1793–1811.  At `(p,p') = (2,3)`
(`c⋆ = 0`, `b⋆² = -3/2`) and `λ = h_{1,1}(b⋆) = 0`: `ℓ⁺₁ = 1`, `ℓ⁻₁ = 2`, `ℓ⁻₂ = 5`, `ℓ⁺₂ = 7`;
the first double pole of `H_N(0,Δ,Δ_i)` and `ℬ_N(0,Δ,Δ_i)` at `Δ = 0` occurs at `N = 5`, where
`lim Δ² H_5 = lim Δ² ℬ_5 = P_{1,1}(Δ₄,Δ₃) P_{1,4}(Δ₄,Δ₃) P_{1,1}(Δ₁,Δ₂) P_{1,4}(Δ₁,Δ₂)/γ_5`,
`γ_5 = -11200/3`.

Demand sheet.
- every `b⋆` with `b⋆² = -3/2`; the values `c⋆ = 0`, `λ = 0` and the four levels (l.1795–1797);
- first double pole at `N = 5` for both coefficients, with the stated leading coefficient
  (l.1798–1806); the comparison with Ribault's equation (3.24) (l.1806–1809) is a remark on
  conventions and is not part of the statement. -/
def Stmt_prop_c0_example : Prop :=
  ∀ b : ℂ, b ^ 2 = -3 / 2 →
    kacC b = 0 ∧ kacH 1 1 b = 0 ∧
    ellPlus 2 3 1 1 1 = 1 ∧ ellMinus 2 3 1 1 1 = 2 ∧ ellMinus 2 3 1 1 2 = 5 ∧
    ellPlus 2 3 1 1 2 = 7 ∧
    FirstDoublePole 0 0 5 (exampleCoeff b 1 1 1 4 (-11200 / 3))

/-- Proposition 6.2 (`prop:ising-example`), sphere/paper.tex l.1813–1832.  At `(p,p') = (3,4)`
(`c⋆ = 1/2`, `b⋆² = -4/3`), at `λ = 1/2, 1/16, 0` the first double poles of `ℬ_N` and `H_N`
occur at `N = 7, 10, 11`, with leading coefficient `π(Δ₄,Δ₃) π(Δ₁,Δ₂)/γ`,
`(π, γ) = (P_{2,1}P_{1,5}, -700700)`, `(P_{1,2}P_{4,2}, -1121229484375/192)`,
`(P_{1,1}P_{2,5}, -2477917160468750/6561)`.

Demand sheet.
- every `b⋆` with `b⋆² = -4/3` (l.1815);
- three rows; both coefficients; first double pole and leading coefficient (l.1816–1827);
- the constants `γ` as printed; they are those of the torus Proposition 8.1 (l.1829–1830). -/
def Stmt_prop_ising_example : Prop :=
  ∀ b : ℂ, b ^ 2 = -4 / 3 →
    kacC b = 1 / 2 ∧
    FirstDoublePole (1 / 2) (1 / 2) 7 (exampleCoeff b 2 1 1 5 (-700700)) ∧
    FirstDoublePole (1 / 2) (1 / 16) 10 (exampleCoeff b 1 2 4 2 (-1121229484375 / 192)) ∧
    FirstDoublePole (1 / 2) 0 11 (exampleCoeff b 1 1 2 5 (-2477917160468750 / 6561))

end Virasoro.Sphere
