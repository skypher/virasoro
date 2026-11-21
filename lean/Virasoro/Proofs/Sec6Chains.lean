import Virasoro.Proofs.Sec6LayerPP
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Proposition 6.7 of `paper.tex` at 70bac53: the colliding chains and `T_N(w,y)`

Paper.tex l.1127–1141.  With `ν = b²`, `ν⋆ = -p'/p`, dots for `d/dν` at `ν⋆`:
* `ρ_g = ∂_d ℛ_g|_{d=0} = -(p'u - pv)/(2(p'-p))` for `g = (u,v)` (l.1132–1133);
* `κ₀ = p(p'-p)/p'` (l.1130);
* the limit of `ℛ_g/τ` along `(ν,Δ,d) = (ν⋆+τ, λ+τw, τy)` is
  `ρ_g y ∏_j (1 - y/(jκ₀))`, the product over the `j ≠ 0` with `(jp, jp') ∈ B_g`,
  `B_g = [1-u,u] × [1-v,v]` (l.1127–1135; `B` as in the proof of Lemma 6.5, l.1074);
* a chain `g₁,…,g_n` from `λ` is colliding when `h_{g_i}(ν⋆) = z_{i-1}(ν⋆)`, `z₀ = λ`,
  `z_i = h_{g_i} + ℓ_{g_i}`; in momenta, `(p'u_i - pv_i)² = m_{i-1}²` with `m₀ = n₀` and
  `m_i = p'u_i + pv_i`;
* `T_N(w,y)` is the sum over the colliding chains of total level `N` of
  `∏_i ρ_{g_i} y ∏_j (1 - y/(jκ₀)) / (ζ_{i-1} - ḣ_{g_i})`, `ζ₀ = w`, `ζ_i = ḣ_{g_i}` (l.1139–1141).

The proof of Proposition 6.7 then has two parts, frozen here as sub-statements:
`Stmt_sub_layer_chain_limit` (l.1135–1148: the top pole coefficient of `H_{ℓ^±_k}(c⋆,Δ,d)` is
`O(d^k)` with `[d^k] = lim_w w^k [y^k] T_{ℓ^±_k}`) and `Stmt_sub_layer_chain_eval`
(l.1150–1173: the limit equals `c_k (±ρ)^k`).
-/

namespace Virasoro

open Polynomial

/-- `ρ_g = -(p'u - pv)/(2(p'-p))` for `g = (u,v)` (paper.tex l.1132–1133). -/
noncomputable def rhoG (p p' : ℕ) (g : Label) : ℂ :=
  -((p' : ℂ) * g.1 - (p : ℂ) * g.2) / (2 * ((p' : ℂ) - p))

/-- `ḣ_g = (d/dν) h_{u,v}` at `ν⋆ = -p'/p`: `4p'² ḣ_g = p'²(1-u²) - p²(1-v²)`. -/
noncomputable def hdotNu (p p' : ℕ) (g : Label) : ℂ :=
  ((1 - (g.1 : ℂ) ^ 2) - (1 - (g.2 : ℂ) ^ 2) * (p : ℂ) ^ 2 / (p' : ℂ) ^ 2) / 4

/-- `κ₀ = p(p'-p)/p'` (paper.tex l.1130). -/
noncomputable def kappa0 (p p' : ℕ) : ℂ := (p : ℂ) * ((p' : ℂ) - p) / p'

/-- The integers `j ≠ 0` with `(jp, jp') ∈ B_g = [1-u,u] × [1-v,v]` (paper.tex l.1129–1130). -/
noncomputable def boxMults (p p' : ℕ) (g : Label) : Finset ℤ :=
  (Finset.Icc (-((g.1 : ℤ) + g.2)) ((g.1 : ℤ) + g.2)).filter fun j =>
    j ≠ 0 ∧ 1 - (g.1 : ℤ) ≤ j * p ∧ j * p ≤ g.1 ∧ 1 - (g.2 : ℤ) ≤ j * p' ∧ j * p' ≤ g.2

/-- `ρ_g y ∏_j (1 - y/(jκ₀))`, the limit of `ℛ_g/τ` (paper.tex l.1134–1135), as a polynomial in
`y`. -/
noncomputable def resLimit (p p' : ℕ) (g : Label) : ℂ[X] :=
  C (rhoG p p' g) * X * ∏ j ∈ boxMults p p' g, (1 - C (((j : ℂ) * kappa0 p p')⁻¹) * X)

/-- The sum over the colliding chains of total level `N` that start from a weight of squared
momentum `m2` with slope `ζ`, organized by the first step `g` (which must satisfy
`(p'u - pv)² = m2`); `fuel` bounds the length of the chains. -/
noncomputable def chainT (p p' : ℕ) : ℕ → ℕ → ℤ → RatFunc ℂ → (RatFunc ℂ)[X]
  | 0, N, _, _ => if N = 0 then 1 else 0
  | fuel + 1, N, m2, ζ =>
      if N = 0 then 1
      else ∑ g ∈ labels N,
        if ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = m2 then
          C ((ζ - RatFunc.C (hdotNu p p' g))⁻¹) *
            (resLimit p p' g).map (algebraMap ℂ (RatFunc ℂ)) *
            chainT p p' fuel (N - g.lvl) (((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2)
              (RatFunc.C (hdotNu p p' g))
        else 0

/-- `T_N(w,y)` for the chains from `λ = h_{r,s}(b⋆)` (paper.tex l.1139–1141): a polynomial in
`y` over `ℂ(w)`.  Every step has level at least `1`, so chains of total level `N` have length at
most `N`. -/
noncomputable def chainTN (p p' r s N : ℕ) : (RatFunc ℂ)[X] :=
  chainT p p' N N (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) RatFunc.X

/-- A rational function of `w` that tends to `0` as `w → ∞`. -/
def VanishesAtInfinity (e : RatFunc ℂ) : Prop := e = 0 ∨ e.intDegree < 0

/-- Frozen sub-statement of Proposition 6.7 (paper.tex l.1135–1148): for `N = ℓ^±_k`, the
coefficient of `(Δ-λ)^{-k}` of `H_N(c⋆,Δ,d)` is a polynomial `A(d)` with `[d^n]A = 0` for
`n < k` and `[d^k]A = lim_{w→∞} w^k [y^k] T_N(w,y)`.

Demand sheet.
- `MinimalSetting`, every `k ≥ 1`, both signs, `N = ℓ^±_k` (l.1147–1148);
- `A ∈ ℂ[d]` with image the coefficient of `(Δ-λ)^{-k}` over `ℂ(d)`; `[d^n]A = 0`, `n < k`
  (from `H_N(c⋆,λ+ε,εy) → Φ(0,1,y)`, l.1145–1146);
- the limit: `w^k [y^k]T_N - [d^k]A` is a rational function of `w` vanishing at infinity
  (l.1144–1148);
- `T_N` is `chainTN`; its denominators `ζ_{i-1} - ḣ_{g_i}` are nonzero on colliding chains
  (l.1137, l.1155), so no inverse of zero occurs in the chains that contribute. -/
def Stmt_sub_layer_chain_limit : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ k : ℕ, 1 ≤ k →
    (∃ A : ℂ[X],
      ppCoeff (HN (kacC b) (ellPlus p p' r s k)) (pt (kacH r s b)) k = algebraMap ℂ[X] Kd A ∧
      (∀ n : ℕ, n < k → A.coeff n = 0) ∧
      ∃ e : RatFunc ℂ, VanishesAtInfinity e ∧
        (chainTN p p' r s (ellPlus p p' r s k)).coeff k * RatFunc.X ^ k =
          RatFunc.C (A.coeff k) + e) ∧
    (∃ A : ℂ[X],
      ppCoeff (HN (kacC b) (ellMinus p p' r s k)) (pt (kacH r s b)) k = algebraMap ℂ[X] Kd A ∧
      (∀ n : ℕ, n < k → A.coeff n = 0) ∧
      ∃ e : RatFunc ℂ, VanishesAtInfinity e ∧
        (chainTN p p' r s (ellMinus p p' r s k)).coeff k * RatFunc.X ^ k =
          RatFunc.C (A.coeff k) + e)

/-- Frozen sub-statement of Proposition 6.7 (paper.tex l.1150–1173): for `N = ℓ^±_k`, if
`w^k [y^k] T_N(w,y)` has a finite limit as `w → ∞`, the limit is `c_k (±ρ)^k`.

Demand sheet.
- `p, p' ≥ 2` coprime, `0 < r < p`, `0 < s < p'`, `n₁ < pp'` (the setting, without `b`);
  every `k ≥ 1`, both signs;
- hypothesis `[y^k]T_N = O(w^{-k})` with limit `a` of `w^k [y^k]T_N`: the paper takes it from
  the first paragraph of the proof (l.1145, used at l.1162–1163), and the consumer
  `sub_layer_pp_of_chain` supplies it from `Stmt_sub_layer_chain_limit`;
- `ρ = -n₀/(2(p'-p))`, `c_k` is `layerConst k`; conclusion `a = c_k (±ρ)^k` (l.1163–1173).
The existence of the limit with this value was checked exactly for the eight pairs `(p,p')` with
`p, p' ≤ 5` and `k ≤ 2` (`scratch/chains/check_TN.py`). -/
def Stmt_sub_layer_chain_eval : Prop :=
  ∀ p p' r s : ℕ, 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → 0 < r → r < p → 0 < s → s < p' →
    p' * r + p * s < p * p' → ∀ k : ℕ, 1 ≤ k →
    let ρ : ℂ := -((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p))
    (∀ (a : ℂ) (e : RatFunc ℂ), VanishesAtInfinity e →
      (chainTN p p' r s (ellPlus p p' r s k)).coeff k * RatFunc.X ^ k = RatFunc.C a + e →
        a = (layerConst k : ℂ) * ρ ^ k) ∧
    (∀ (a : ℂ) (e : RatFunc ℂ), VanishesAtInfinity e →
      (chainTN p p' r s (ellMinus p p' r s k)).coeff k * RatFunc.X ^ k = RatFunc.C a + e →
        a = (layerConst k : ℂ) * (-ρ) ^ k)

/-- The two parts of the proof of Proposition 6.7 give `Stmt_sub_layer_pp`. -/
theorem sub_layer_pp_of_chain (h1 : Stmt_sub_layer_chain_limit)
    (h2 : Stmt_sub_layer_chain_eval) : Stmt_sub_layer_pp := by
  intro p p' r s b hset k hk
  obtain ⟨⟨Ap, hAp, hAp0, ep, hep, hTp⟩, ⟨Am, hAm, hAm0, em, hem, hTm⟩⟩ := h1 p p' r s b hset k hk
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  obtain ⟨hEp, hEm⟩ := h2 p p' r s hp hp' hcop hr hrp hs hsp hlt k hk
  exact ⟨⟨Ap, hAp, hAp0, hEp _ ep hep hTp⟩, ⟨Am, hAm, hAm0, hEm _ em hem hTm⟩⟩

/-- Proposition 6.7 from its two frozen parts and the cited injectivity of the singular
embedding. -/
theorem prop_layer_coefficients_of_chain (hI : Cited_VermaHomInjective)
    (h1 : Stmt_sub_layer_chain_limit) (h2 : Stmt_sub_layer_chain_eval) :
    Stmt_prop_layer_coefficients :=
  prop_layer_coefficients_of_pp hI (sub_layer_pp_of_chain h1 h2)

end Virasoro
