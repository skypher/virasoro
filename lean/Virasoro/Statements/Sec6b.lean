import Virasoro.Statements.Sec5c
import Virasoro.Statements.Sec6

/-!
# Frozen statements: Section 6 of `paper.tex` at 70bac53, new results 6.5–6.7

Proposition 6.2, Lemma 6.3 and Proposition 6.4 are unchanged and stay in `Statements/Sec6`
(there numbered 6.2, 6.4, 6.5).
-/

namespace Virasoro

open Polynomial

/-- Lemma 6.5 (`lem:d-derivatives`), paper.tex l.1063–1071.  For `N ≥ 1`, `H_N(c(b),Δ,d)`
vanishes at `d = 0`, and, as rational functions of `(b,Δ)`,
`∂_d H_N|_{d=0} = -∑_{rs=N} (r b² + s) / (2 (b² + 1) (Δ - h_{r,s}(b)))`.

Demand sheet.
- `N ≥ 1` (l.1065);
- "as rational functions of `(b,Δ)`": the field is `ℚ(b)(Δ)`, `b = RatFunc.C RatFunc.X`,
  `Δ = RatFunc.X` (l.1066);
- `H_N` is the polynomial in `d` of Definition 2.2–2.3 over this field (`HpolyD`); the Gram
  matrices `G_M(c(b),Δ)`, `M ≤ N`, are invertible there, which is recorded as the first clause;
- value at `d = 0`: the constant coefficient; `∂_d|_{d=0}`: the coefficient of `d`;
- the sum runs over the positive labels with `r s = N` exactly (l.1069); identity. -/
def Stmt_lem_d_derivatives : Prop :=
  let bK : RatFunc (RatFunc ℚ) := RatFunc.C RatFunc.X
  let ΔK : RatFunc (RatFunc ℚ) := RatFunc.X
  ∀ N : ℕ, 1 ≤ N →
    (∀ M : ℕ, M ≤ N → (gram (kacC bK) ΔK M).det ≠ 0) ∧
    (HpolyD (kacC bK) ΔK N).coeff 0 = 0 ∧
    (HpolyD (kacC bK) ΔK N).coeff 1 =
      -∑ a ∈ (labels N).filter (fun a => a.1 * a.2 = N),
        (((a.1 : ℕ) : RatFunc (RatFunc ℚ)) * bK ^ 2 + ((a.2 : ℕ) : RatFunc (RatFunc ℚ))) /
          (2 * (bK ^ 2 + 1) * (ΔK - kacHL a bK))

/-- Lemma 6.6 (`lem:regular-everywhere`), paper.tex l.1090–1100.  For every positive label
`(r,s)` and every `b⋆ ∈ ℂ^×`, the normalized singular vector `χ_{r,s}(b)` of Proposition 6.2 is
regular at `b⋆`, and its value is a singular vector of level `rs` in `M(c⋆, h_{r,s}(b⋆))` with
`L_{-1}^{rs}`-coefficient `1`.  Hence (6.2) holds at `b⋆`, and so does (6.1) when `𝒜_{r,s}` is
regular there.

Demand sheet.
- all positive `(r,s)`, all `b⋆ ≠ 0` (l.1092);
- `χ_{r,s}(b)`: every normalized singular vector over `ℚ(b)` (the one of Proposition 6.2, which
  is unique), with coordinates `p`;
- regular at `b⋆`: no denominator of a coordinate vanishes at `b⋆` (l.1094);
- the value `p₁` is singular of level `rs` with `L_{-1}^{rs}`-coefficient `1` (l.1095–1096);
- (6.2) at `b⋆` for every complex `d` (l.1097);
- (6.1) at `b⋆` under the hypothesis that `𝒜_{r,s}` is regular at `b⋆`, read as: no factor
  `p b⋆ + q b⋆⁻¹` of its product vanishes (l.1098–1099). -/
def Stmt_lem_regular_everywhere : Prop :=
  ∀ r s : ℕ, 0 < r → 0 < s →
    ∀ p : Nat.Partition (r * s) → RatFunc ℚ, p (onesPartition (r * s)) = 1 →
      Verma.IsSingular
        (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
          (r * s) p) (r * s) →
      ∀ b₁ : ℂ, b₁ ≠ 0 →
        (∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (p Y)) ≠ 0) ∧
        (let p₁ : Nat.Partition (r * s) → ℂ := fun Y => RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y)
         p₁ (onesPartition (r * s)) = 1 ∧
         Verma.IsSingular (Verma.pbwCoord (c := kacC b₁) (h := kacH r s b₁) (r * s) p₁) (r * s) ∧
         (∀ d : ℂ, torusForm (kacC b₁) (kacH r s b₁) d (r * s) p₁ p₁ = genP r s b₁ d) ∧
         ((∀ pq ∈ genAIndex r s, (pq.1 : ℂ) * b₁ + (pq.2 : ℂ) * b₁⁻¹ ≠ 0) →
           crossScalar (kacC b₁) (kacH r s b₁) p₁ = (genA r s b₁)⁻¹))

/-- The constant `c_k = (-1)^{⌊k/2⌋} binom(k-1, ⌊(k-1)/2⌋)` of Proposition 6.7. -/
def layerConst (k : ℕ) : ℤ := (-1) ^ (k / 2) * (Nat.choose (k - 1) ((k - 1) / 2) : ℤ)

/-- Proposition 6.7 (`prop:layer-coefficients`), paper.tex l.1114–1122.  In the setting of
Theorem 5.9, with `ρ = -n₀/(2(p'-p))` and `c_k = (-1)^{⌊k/2⌋} binom(k-1, ⌊(k-1)/2⌋)`,
`τ^±_k/γ^±_k = c_k (±ρ)^k d^k + O(d^{k+1})`; in particular `τ^±_k` vanishes to order exactly `k`
at `d = 0`.

Demand sheet.
- `MinimalSetting`, a family `w^±_k` as in Theorem 5.8 (`TopLayerSetting`), coordinates
  `xp`, `xm`; every `k ≥ 1` and both signs (Theorem 5.9 gives `γ^±_k ≠ 0` for every `k`, with
  `N = ℓ^±_k`);
- `ρ = -n₀/(2(p'-p))`, `n₀ = p' r - p s` (l.1118); `p' ≠ p` since they are coprime and `≥ 2`;
- the expansion is stated without the division by `γ^±_k`: the coefficients of `d^n`, `n < k`,
  of `τ^±_k` vanish and the coefficient of `d^k` equals `γ^±_k c_k (±ρ)^k` (l.1120);
- order exactly `k`: the coefficient of `d^k` is nonzero (l.1121). -/
def Stmt_prop_layer_coefficients : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k : ℕ, 1 ≤ k →
        let ρ : ℂ := -((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p))
        (∀ xp : Nat.Partition (ellPlus p p' r s k) → ℂ,
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
            (∀ n : ℕ, n < k → (torusPolyForm (kacC b) (kacH r s b) xp).coeff n = 0) ∧
            (torusPolyForm (kacC b) (kacH r s b) xp).coeff k =
              jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp *
                (layerConst k : ℂ) * ρ ^ k ∧
            (torusPolyForm (kacC b) (kacH r s b) xp).coeff k ≠ 0) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s k) → ℂ,
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            (∀ n : ℕ, n < k → (torusPolyForm (kacC b) (kacH r s b) xm).coeff n = 0) ∧
            (torusPolyForm (kacC b) (kacH r s b) xm).coeff k =
              jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm *
                (layerConst k : ℂ) * (-ρ) ^ k ∧
            (torusPolyForm (kacC b) (kacH r s b) xm).coeff k ≠ 0)

end Virasoro
