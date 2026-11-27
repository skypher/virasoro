import Virasoro.Statements.Sec8Diagonal

/-!
# Frozen statements: Section 8.2 of `paper.tex` (boundary weights)

Paper: `paper.tex`, Section 8.2 (`sec:boundary`), Lemma 8.10 and Theorem 8.11, version of
2026-11-27 (at 8c6f845).

Reading conventions (besides those of `Virasoro.Statements.Sec8Diagonal`).
* The setting is `BoundarySetting p p' x₀ b`: coprime `p, p' ≥ 2`, `b⋆² = -p'/p`, and `x₀` a
  positive multiple of exactly one of `p, p'` with `x₀ < pp'`.  `λ = d_{x₀}` with
  `d_x = (x² - (p'-p)²)/(4pp')` (`momWt`).
* `ε = 1` if `p ∣ x₀` and `ε = -1` otherwise; `π_k = (-1)^k ⌈k/2⌉`; `T_k = x₀ + π_k N₀` with
  `N₀ = 2pp'`; `M_k = |T_k|`; the node `μ_k = d_{M_k}` of layer `k`.  The level of `μ_k` above
  `λ` is `π_k (x₀ + pp' π_k)` (`bLev`), so `μ_k - μ_i = bLev k - bLev i`.
* `c^{(k')}_{μ_i→μ_k,j}` is `chainFnC` at the weight `μ_i` with `D = bLev k - bLev i`, and
  `Top(μ_i→μ_k) = c^{(k-i)}_{μ_i→μ_k,0}(b⋆)`.
* The label `g` of weight `μ_i` leading to `μ_k` of Lemma 8.10 is written out as `bLabel i k`
  (`y_g = M_k`, `x_g = -ε sgn(T_k) T_i`, `u = (x_g + y_g)/(2p')`, `v = (y_g - x_g)/(2p)`); "exactly
  one positive label" is the equivalence with `g = bLabel i k`.  `x_g = p'u - pv`,
  `y_g = p'u + pv`.  `R_g` is the germ `RG` of Section 7 and `ρ_g` its coefficient of
  `t^{1-(k-i)}`; "nonzero in `K⋆`" is nonzero in `ℂ(d)`.
* `h_{aθ} = ς(K + ε T_a T_θ)` with `ς = b⋆/(2p'²)`, `K = p'² - p²` (`bH`).
* `H_{N-Δ_D}(c⋆, μ_{i+D}, d)` is the value at `Δ = μ_{i+D}` of the rational function
  `H_{N-Δ_D}(c⋆, ·, d)` over `ℂ(d)`.  "At a specialized `d`": `H_N(c⋆, Δ, d₀)` for `d₀ ∈ ℂ` is
  `Hrat (kacC b) d₀ N`, a rational function of `Δ` over `ℂ`; the top coefficient
  `Top(μ_i→μ_{i+D}) H_{N-Δ_D}(c⋆, μ_{i+D}, d)` is a polynomial in `d` (the image of `P`), and its
  value at `d₀` is `P(d₀)`.
-/

namespace Virasoro

open scoped LaurentSeries Polynomial

/-- The setting of Section 8.2: `x₀` a positive multiple of exactly one of `p, p'`, `x₀ < pp'`. -/
def BoundarySetting (p p' x₀ : ℕ) (b : ℂ) : Prop :=
  2 ≤ p ∧ 2 ≤ p' ∧ Nat.Coprime p p' ∧ 0 < x₀ ∧ x₀ < p * p' ∧ (p ∣ x₀ ↔ ¬ p' ∣ x₀) ∧
    b ^ 2 = -(p' : ℂ) / p

section Defs

variable (p p' x₀ : ℕ)

/-- `ε = 1` if `p ∣ x₀`, `ε = -1` if `p' ∣ x₀`. -/
def bEps : ℤ := if p ∣ x₀ then 1 else -1

/-- `π_k = (-1)^k ⌈k/2⌉`. -/
def bPi (k : ℕ) : ℤ := (-1) ^ k * (((k + 1) / 2 : ℕ) : ℤ)

/-- `T_k = x₀ + π_k N₀`, `N₀ = 2pp'`. -/
def bT (k : ℕ) : ℤ := x₀ + bPi k * (2 * p * p')

/-- `M_k = |T_k|`. -/
def bM (k : ℕ) : ℕ := (bT p p' x₀ k).natAbs

/-- The node `μ_k = d_{M_k}` (`μ_0 = λ`). -/
noncomputable def bWt (k : ℕ) : ℂ := momWt p p' (bM p p' x₀ k)

/-- The level `μ_k - λ = π_k (x₀ + pp' π_k)`. -/
def bLev (k : ℕ) : ℕ := (bPi k * ((x₀ : ℤ) + p * p' * bPi k)).toNat

/-- The label from `μ_i` to `μ_k` of Lemma 8.10: `y_g = M_k`, `x_g = -ε sgn(T_k) T_i`. -/
def bLabel (i k : ℕ) : Label :=
  let y : ℤ := bM p p' x₀ k
  let x : ℤ := -bEps p x₀ * (if 0 < bT p p' x₀ k then 1 else -1) * bT p p' x₀ i
  (((x + y) / (2 * p')).toNat, ((y - x) / (2 * p)).toNat)

end Defs

section Chains

variable (p p' x₀ : ℕ) (b : ℂ)

/-- `c^{(k')}_{μ_i→μ_k,j}`. -/
noncomputable def bChain (i k k' j : ℕ) : Kd⸨X⸩ :=
  chainFnC b (bWt p p' x₀ i) (bLev p p' x₀ k - bLev p p' x₀ i) k' j

/-- `Top(μ_i → μ_k) = c^{(k-i)}_{μ_i→μ_k,0}(b⋆)`. -/
noncomputable def bTop (i k : ℕ) : Kd := (bChain p p' x₀ b i k (k - i) 0).coeff 0

/-- The residue germ `R_g` of the label from `μ_i` to `μ_k`. -/
noncomputable def bR (i k : ℕ) : Kd⸨X⸩ := RG (bsC b) dvar (bLabel p p' x₀ i k)

/-- `ρ_g`, the coefficient of `t^{1-(k-i)}` in `R_g`. -/
noncomputable def bRho (i k : ℕ) : Kd := (bR p p' x₀ b i k).coeff (1 - ((k : ℤ) - i))

/-- `h_{aθ} = ς(K + ε T_a T_θ)` for `a = μ_i`, `θ = μ_m`. -/
noncomputable def bH (i m : ℕ) : Kd :=
  pt (varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) +
    (bEps p x₀ : ℂ) * (bT p p' x₀ i : ℂ) * (bT p p' x₀ m : ℂ)))

end Chains

/-- Lemma 8.10 (`lem:boundary-labels`).  For `0 ≤ i < k` there is exactly one positive label `g`
of weight `μ_i` leading to `μ_k`; it has `y_g = M_k`, `x_g = -ε sgn(T_k) T_i` and
`x_g y_g = -ε T_i T_k`, and `R_g = ρ_g t^{1-(k-i)} + O(t^{2-(k-i)})` with `ρ_g ≠ 0` in `K⋆`.  Every
positive label whose weight is a node `μ_i` leads to a node `μ_k` with `k > i`. -/
def Stmt_lem_boundary_labels : Prop :=
  ∀ (p p' x₀ : ℕ) (b : ℂ), BoundarySetting p p' x₀ b →
    (∀ i k : ℕ, i < k →
      (∀ g : Label, 0 < g.1 → 0 < g.2 →
        (kacHL g b = bWt p p' x₀ i ∧ kacHL g b + (g.lvl : ℂ) = bWt p p' x₀ k ↔
          g = bLabel p p' x₀ i k)) ∧
      0 < (bLabel p p' x₀ i k).1 ∧ 0 < (bLabel p p' x₀ i k).2 ∧
      (p' : ℤ) * (bLabel p p' x₀ i k).1 + p * (bLabel p p' x₀ i k).2 = bM p p' x₀ k ∧
      (p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 =
        -bEps p x₀ * (if 0 < bT p p' x₀ k then 1 else -1) * bT p p' x₀ i ∧
      ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2) *
          ((p' : ℤ) * (bLabel p p' x₀ i k).1 + p * (bLabel p p' x₀ i k).2) =
        -bEps p x₀ * bT p p' x₀ i * bT p p' x₀ k ∧
      (((1 - ((k : ℤ) - i) : ℤ) : WithTop ℤ) ≤ (bR p p' x₀ b i k).orderTop) ∧
      bRho p p' x₀ b i k ≠ 0) ∧
    ∀ (i : ℕ) (g : Label), 0 < g.1 → 0 < g.2 → kacHL g b = bWt p p' x₀ i →
      ∃ k : ℕ, i < k ∧ kacHL g b + (g.lvl : ℂ) = bWt p p' x₀ k

/-- Theorem 8.11 (`thm:boundary`).  Let `a = μ_i`, `μ = μ_k`, `D = k - i ≥ 1`, `g` the label from
`μ_i` to `μ_k`.
(i) `Top(a→μ) = ρ_g ∏_{i<m<k} (h_{aμ} - h_{aμ_m}) = ρ_g (ε ς N₀ T_i)^{D-1} ∏_{i<m<k} (π_k - π_m)`,
nonzero in `K⋆`.
(ii) For `0 ≤ j ≤ D-1`:
`c^{(D-j)}_{a→μ,j}(b⋆) = (1/j!) (T_k/T_i)^j ∏_{m=1}^j (π_i - π_{k-m})/(π_k - π_{k-m}) Top(a→μ)`.
(iii) With `Δ_m = μ_{i+m} - μ_i` and `Δ_D ≤ N < Δ_{D+1}`: `A⋆_{μ_i,k',N} = 0` for `k' > D`, and
`A⋆_{μ_i,D,N} = Top(μ_i→μ_{i+D}) H_{N-Δ_D}(c⋆, μ_{i+D}, d)`; this is nonzero in `K⋆`, so
`H_N(c⋆,Δ,d)` has a pole of order exactly `D` at `Δ = μ_i`.  At a specialized `d` the order is at
most `D`, and exactly `D` iff `Top(μ_i→μ_{i+D}) H_{N-Δ_D}(c⋆, μ_{i+D}, d) ≠ 0`. -/
def Stmt_thm_boundary : Prop :=
  ∀ (p p' x₀ : ℕ) (b : ℂ), BoundarySetting p p' x₀ b →
    (∀ i k : ℕ, i < k →
      bTop p p' x₀ b i k =
          bRho p p' x₀ b i k * ∏ m ∈ Finset.Ioo i k, (bH p p' x₀ b i k - bH p p' x₀ b i m) ∧
      bTop p p' x₀ b i k =
          bRho p p' x₀ b i k *
            pt (((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ)) ^ (k - i - 1) *
              ∏ m ∈ Finset.Ioo i k, ((bPi k : ℂ) - bPi m)) ∧
      bTop p p' x₀ b i k ≠ 0) ∧
    (∀ i k j : ℕ, i < k → j < k - i →
      (bChain p p' x₀ b i k (k - i - j) j).coeff 0 =
        ((1 / j.factorial * ((bT p p' x₀ k : ℚ) / bT p p' x₀ i) ^ j *
            ∏ m ∈ Finset.Icc 1 j, (((bPi i : ℚ) - bPi (k - m)) / ((bPi k : ℚ) - bPi (k - m))) : ℚ) :
          Kd) * bTop p p' x₀ b i k) ∧
    (∀ i D N : ℕ, 1 ≤ D → bLev p p' x₀ (i + D) - bLev p p' x₀ i ≤ N →
      N < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ i →
      (∀ k' : ℕ, D < k' → Astar b N (bWt p p' x₀ i) k' = 0) ∧
      Astar b N (bWt p p' x₀ i) D =
        bTop p p' x₀ b i (i + D) *
          RatFunc.eval (RingHom.id Kd) (pt (bWt p p' x₀ (i + D)))
            (HN (kacC b) (N - (bLev p p' x₀ (i + D) - bLev p p' x₀ i))) ∧
      Astar b N (bWt p p' x₀ i) D ≠ 0 ∧
      poleOrder (HN (kacC b) N) (pt (bWt p p' x₀ i)) = D ∧
      ∃ P : ℂ[X], algebraMap ℂ[X] Kd P = Astar b N (bWt p p' x₀ i) D ∧
        ∀ d₀ : ℂ, poleOrder (Hrat (kacC b) d₀ N) (bWt p p' x₀ i) ≤ D ∧
          (poleOrder (Hrat (kacC b) d₀ N) (bWt p p' x₀ i) = D ↔ P.eval d₀ ≠ 0))

end Virasoro
