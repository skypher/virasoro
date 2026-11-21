import Virasoro.Statements.Sec5a
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Minimal-model setting, the braided orbit and box ratios (paper Theorem 5.8, Sections 10, 12)

`p, p' ≥ 2` are coprime, `b⋆² = -p'/p`, and `λ = h_{r,s}(b⋆)` is an interior Kac weight labelled
so that `n₁ = p' r + p s < p p'`; `n₀ = p' r - p s`.  The sign `+` is `true`, the sign `-` is
`false`.
-/

namespace Virasoro

/-- The setting of Theorem 5.8: `p, p' ≥ 2` coprime, `0 < r < p`, `0 < s < p'`,
`n₁ = p' r + p s < p p'`, and `b⋆² = -p'/p`. -/
def MinimalSetting (p p' r s : ℕ) (b : ℂ) : Prop :=
  2 ≤ p ∧ 2 ≤ p' ∧ Nat.Coprime p p' ∧ 0 < r ∧ r < p ∧ 0 < s ∧ s < p' ∧
    p' * r + p * s < p * p' ∧ b ^ 2 = -(p' : ℂ) / p

/-- A choice of the singular vectors `w^±_k` of Theorem 5.8: `wp k`, `wm k` are singular of
levels `ℓ^±_k` in `M(c⋆,λ)` and `J^i(c⋆,λ) = U(Vir_-) w⁺_i + U(Vir_-) w⁻_i` for `i ≥ 1`. -/
def TopLayerSetting (p p' r s : ℕ) (b : ℂ)
    (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)) : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    Verma.IsSingular (wp k) (ellPlus p p' r s k) ∧ Verma.IsSingular (wm k) (ellMinus p p' r s k)) ∧
  (∀ i : ℕ, 1 ≤ i →
    jantzen (kacC b) (kacH r s b) i = Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i))

/-- `ℓ^ε_k`: `ℓ⁺_k` for `ε = true`, `ℓ⁻_k` for `ε = false`, and `0` for `k = 0`. -/
def ellOrb (p p' r s : ℕ) (ε : Bool) (k : ℕ) : ℕ :=
  if k = 0 then 0 else if ε then ellPlus p p' r s k else ellMinus p p' r s k

/-- `ℓ_k = min(ℓ⁺_k, ℓ⁻_k)` (paper Theorem 5.9). -/
def ellMin (p p' r s k : ℕ) : ℕ := min (ellPlus p p' r s k) (ellMinus p p' r s k)

/-- The momenta of the braided orbit, paper equation (10.5):
`n⁺_{2j} = 2jpp' + n₀`, `n⁻_{2j} = 2jpp' - n₀`, `n⁺_{2j+1} = 2jpp' + n₁`,
`n⁻_{2j+1} = 2(j+1)pp' - n₁`. -/
def nOrb (p p' r s : ℕ) (ε : Bool) (k : ℕ) : ℤ :=
  let n0 : ℤ := (p' : ℤ) * r - (p : ℤ) * s
  let n1 : ℤ := (p' : ℤ) * r + (p : ℤ) * s
  if k % 2 = 0 then (if ε then (k : ℤ) * p * p' + n0 else (k : ℤ) * p * p' - n0)
  else (if ε then ((k : ℤ) - 1) * p * p' + n1 else ((k : ℤ) + 1) * p * p' - n1)

/-- The weight `(n² - (p'-p)²)/(4pp')` of the momentum `n`, paper equation (10.6). -/
noncomputable def momWt (p p' : ℕ) (n : ℤ) : ℂ :=
  (((n : ℂ)) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')

/-- The orbit weight `μ^ε_k` (`μ_0 = λ` for `k = 0`, either sign). -/
noncomputable def muOrb (p p' r s : ℕ) (ε : Bool) (k : ℕ) : ℂ := momWt p p' (nOrb p p' r s ε k)

/-- The braided orbit `𝒪_{p,p'}(r,s) = {μ_0} ∪ {μ^±_k : k ≥ 1}`. -/
def orbitSet (p p' r s : ℕ) : Set ℂ := {μ | ∃ (ε : Bool) (k : ℕ), μ = muOrb p p' r s ε k}

/-- The minimal-model fusion set `ℱ_{p,p'}(r,s)`, paper equation (9.2). -/
def fusionSet (p p' r s : ℕ) (b : ℂ) : Set ℂ :=
  {d | ∃ k m : ℕ, k < min r (p - r) ∧ m < min s (p' - s) ∧
    d = kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b}

/-- The reflected enlargement `ℱ^±_{p,p'}(r,s)`, paper equation (9.3). -/
def fusionSetPM (p p' r s : ℕ) (b : ℂ) : Set ℂ :=
  {d | ∃ k m : ℕ, k < min r (p - r) ∧ m < min s (p' - s) ∧
    (d = kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b ∨
      d = kacH (2 * (k : ℤ) + 1) (-(2 * (m : ℤ) + 1)) b)}

/-- The Kac label `(R,S)` of the primitive arrow `μ → ν` with momenta `n_μ`, `n_ν` (paper
Lemma 10.3(ii)): `p' R + p S = n_ν` and `p' R - p S = σ n_μ` for the sign `σ` for which
`2p'` divides `n_ν + σ n_μ`. -/
def arrowLabel (p p' : ℕ) (nμ nν : ℤ) : ℤ × ℤ :=
  if (2 * (p' : ℤ)) ∣ nν + nμ then ((nν + nμ) / (2 * p'), (nν - nμ) / (2 * p))
  else ((nν - nμ) / (2 * p'), (nν + nμ) / (2 * p))

/-- The box `[1-R, R] × [1-S, S]`. -/
noncomputable def boxSet (R S : ℤ) : Finset (ℤ × ℤ) := Finset.Icc (1 - R) R ×ˢ Finset.Icc (1 - S) S

/-- The shifted box `[1-R+k, R+k] × [1-S+m, S+m]`. -/
noncomputable def boxShift (R S : ℤ) (k m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (1 - R + k) (R + k) ×ˢ Finset.Icc (1 - S + m) (S + m)

/-- The numerator `∏_{(a,b') ≠ (-k,-m)} ((a+k)t + (b'+m))` of the box formula (9.4). -/
noncomputable def boxNum (R S : ℤ) (k m : ℕ) (t : ℂ) : ℂ :=
  ∏ x ∈ (boxSet R S).erase (-(k : ℤ), -(m : ℤ)), (((x.1 + k : ℤ) : ℂ) * t + ((x.2 + m : ℤ) : ℂ))

/-- The denominator `∏_{(a,b') ≠ (0,0)} (a t + b')` of the box formula (9.4). -/
noncomputable def boxDen (R S : ℤ) (t : ℂ) : ℂ :=
  ∏ x ∈ (boxSet R S).erase (0, 0), ((x.1 : ℂ) * t + (x.2 : ℂ))

/-- The reduced box ratio (12.1) at `t = -p'/p`:
`∏_{B₁∖B₀} (p b' - p' a) / ∏_{B₀∖B₁} (p b' - p' a)`. -/
noncomputable def cMM (p p' : ℕ) (R S : ℤ) (k m : ℕ) : ℚ :=
  ((∏ x ∈ boxShift R S k m \ boxSet R S, ((p : ℤ) * x.2 - (p' : ℤ) * x.1) : ℤ) : ℚ) /
    ((∏ x ∈ boxSet R S \ boxShift R S k m, ((p : ℤ) * x.2 - (p' : ℤ) * x.1) : ℤ) : ℚ)

/-- The box ratio `c(μ^ε_j → μ^{ε'}_{j+1})` of a primitive arrow of the orbit. -/
noncomputable def cArrow (p p' r s k m : ℕ) (ε : Bool) (j : ℕ) (ε' : Bool) : ℚ :=
  cMM p p' (arrowLabel p p' (nOrb p p' r s ε j) (nOrb p p' r s ε' (j + 1))).1
    (arrowLabel p p' (nOrb p p' r s ε j) (nOrb p p' r s ε' (j + 1))).2 k m

/-- The product of the box ratios along the directed path that starts at `μ^ε_j` and visits the
nodes of signs `l` at the layers `j+1, j+2, …`. -/
noncomputable def pathProd (p p' r s k m : ℕ) : Bool → ℕ → List Bool → ℚ
  | _, _, [] => 1
  | ε, j, ε' :: l => cArrow p p' r s k m ε j ε' * pathProd p p' r s k m ε' (j + 1) l

/-- The cocycle `Ω_{2k+1,2m+1}(μ^ε_j → μ^{ε'}_{j+n})`, evaluated along the path through the
`+` nodes of the intermediate layers (paper Proposition 12.1(ii) states that every directed path
gives the same product). -/
noncomputable def Omega (p p' r s k m : ℕ) (ε : Bool) (j : ℕ) (ε' : Bool) (n : ℕ) : ℚ :=
  if n = 0 then 1 else pathProd p p' r s k m ε j (List.replicate (n - 1) true ++ [ε'])

/-- The Gamma potential `Ψ_{2k+1,2m+1}(ϖ;b)` of paper equation (9.5); `1/Γ` is the entire
reciprocal Gamma function (`Complex.Gamma` vanishes at its poles in Mathlib's convention, so the
inverse is `0` there, the value of `1/Γ`). -/
noncomputable def PsiPot (k m : ℕ) (ϖ b : ℂ) : ℂ :=
  (∏ j ∈ Finset.Icc 1 m,
      (Complex.Gamma (1 + 2 * ϖ / b + (j : ℂ) / b ^ 2) *
        Complex.Gamma (1 - 2 * ϖ / b + (j : ℂ) / b ^ 2))⁻¹) *
    ∏ i ∈ Finset.Icc 1 k,
      (Complex.Gamma (1 + 2 * ϖ * b + (i : ℂ) * b ^ 2 + m) *
        Complex.Gamma (1 - 2 * ϖ * b + (i : ℂ) * b ^ 2 + m))⁻¹

/-- `h_{R,S}` as a function of `t = b²`, paper equation (10.3):
`((t+1)² - (R t + S)²)/(4t)`. -/
def hT {𝔽 : Type*} [Field 𝔽] (R S : ℤ) (t : 𝔽) : 𝔽 :=
  ((t + 1) ^ 2 - ((R : 𝔽) * t + (S : 𝔽)) ^ 2) / (4 * t)

/-- `c` as a function of `t = b²`: `13 + 6t + 6/t`. -/
def cT {𝔽 : Type*} [Field 𝔽] (t : 𝔽) : 𝔽 := 13 + 6 * t + 6 / t

end Virasoro
