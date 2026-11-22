import Virasoro.Sphere.Defs
import Virasoro.Kac

/-!
# The BPZ equation for a block with the degenerate field `Φ_{2,1}` (cited input)

Belavin–Polyakov–Zamolodchikov 1984, eqs. (5.2), (5.17), (5.19), as used in the proof of
Theorem 5.4 (Paper label: thm:sharp-B), step (c), of sphere/paper.tex: for `Δ₂ = h_{2,1}(b)` and `Λ₁ = Λ_μ + b` (the level-2 null vector decouples,
`P_{2,1}(b,Δ₁,μ) = 0`), `𝓕(z) = z^{μ-Δ₁-Δ₂} ℬ(z)`, `ℬ(z) = ∑_n ℬ_n(c(b),μ,Δ_i) zⁿ`, solves
`(b^{-2}∂² - (1/z + 1/(z-1))∂ + Δ₁/z² + Δ₃/(z-1)² + (Δ₁+Δ₂+Δ₃-Δ₄)/(z(1-z))) 𝓕 = 0`.

Encoding.  External weights are parameterized by `Λ_j² = Q(b)² - 4Δ_j` (opening of
§4, sec:confluence); with `β = bΛ`
the weight is `((b²+1)² - β²)/(4b²)` (`wtB`), and `Λ₁ = Λ_μ + b` reads `β₁ = β_μ + b²`.  The
equation is stated through its coefficients: multiplying by `z²(z-1)²` and writing `θ = z∂_z`,
the coefficient of `z^{s+n}`, `s = μ - Δ₁ - Δ₂`, is
`P₀(s+n) ℬ_n + P₁(s+n-1) ℬ_{n-1} + P₂(s+n-2) ℬ_{n-2}` with
`P₀(x) = b^{-2}x(x-1) - x + Δ₁`, `P₁(x) = -2b^{-2}x(x-1) + 3x + D - 2Δ₁`,
`P₂(x) = b^{-2}x(x-1) - 2x + Δ₁ + Δ₃ - D`, `D = Δ₁+Δ₂+Δ₃-Δ₄` (`ℬ_{-1} = ℬ_{-2} = 0`).
"Generic" (step (c), first sentence) is read as: `b ≠ 0`, `b² ∉ ℚ`, and the block is defined at `Δ = μ`
(every `G_m(c(b),μ)` invertible).
-/

namespace Virasoro.Sphere

/-- The weight `((b²+1)² - β²)/(4b²)` of `Λ = β/b`, `Λ² = Q² - 4Δ`. -/
noncomputable def wtB (b β : ℂ) : ℂ := ((b ^ 2 + 1) ^ 2 - β ^ 2) / (4 * b ^ 2)

/-- `P₀(x) = b^{-2}x(x-1) - x + Δ₁`. -/
noncomputable def bpzP0 (b Δ₁ x : ℂ) : ℂ := (b ^ 2)⁻¹ * x * (x - 1) - x + Δ₁

/-- `P₁(x) = -2b^{-2}x(x-1) + 3x + D - 2Δ₁`. -/
noncomputable def bpzP1 (b Δ₁ D x : ℂ) : ℂ := -2 * (b ^ 2)⁻¹ * x * (x - 1) + 3 * x + D - 2 * Δ₁

/-- `P₂(x) = b^{-2}x(x-1) - 2x + Δ₁ + Δ₃ - D`. -/
noncomputable def bpzP2 (b Δ₁ Δ₃ D x : ℂ) : ℂ := (b ^ 2)⁻¹ * x * (x - 1) - 2 * x + Δ₁ + Δ₃ - D

/-- The block coefficient `ℬ_n(c,μ,Δ_i)` at the internal weight `Δ = μ`. -/
noncomputable def blockAt (c μ : ℂ) (Δe : Fin 4 → ℂ) (n : ℕ) : ℂ :=
  RatFunc.eval (RingHom.id ℂ) μ (Bsph c Δe n)

/-- The external weights of the BPZ setting: `Δ₁ = wt(β_μ + b²)`, `Δ₂ = h_{2,1}(b)`,
`Δ₃ = wt(β₃)`, `Δ₄ = wt(β₄)`. -/
noncomputable def bpzWeights (b βμ β₃ β₄ : ℂ) : Fin 4 → ℂ :=
  ![wtB b (βμ + b ^ 2), kacH 2 1 b, wtB b β₃, wtB b β₄]

/-- The coefficient of `z^{s+n}` in the BPZ equation (see the module docstring). -/
noncomputable def bpzCoeff (b βμ β₃ β₄ : ℂ) (n : ℕ) : ℂ :=
  let μ := wtB b βμ
  let Δe := bpzWeights b βμ β₃ β₄
  let s := μ - Δe 0 - Δe 1
  let D := Δe 0 + Δe 1 + Δe 2 - Δe 3
  bpzP0 b (Δe 0) (s + n) * blockAt (kacC b) μ Δe n +
    (if 1 ≤ n then bpzP1 b (Δe 0) D (s + n - 1) * blockAt (kacC b) μ Δe (n - 1) else 0) +
    (if 2 ≤ n then bpzP2 b (Δe 0) (Δe 2) D (s + n - 2) * blockAt (kacC b) μ Δe (n - 2) else 0)

/-- **Cited** (BPZ 1984, eqs. (5.2), (5.17), (5.19); proof of Theorem 5.4, step (c)): for generic
`(b,Λ_μ,Λ₃,Λ₄)` with `Δ₂ = h_{2,1}(b)` and `Λ₁ = Λ_μ + b`, the block `z^{μ-Δ₁-Δ₂}ℬ(z)` solves
the BPZ equation, coefficientwise. -/
def Cited_BPZEquation : Prop :=
  ∀ b βμ β₃ β₄ : ℂ, b ≠ 0 → (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
    (∀ m : ℕ, (gram (kacC b) (wtB b βμ) m).det ≠ 0) →
      ∀ n : ℕ, bpzCoeff b βμ β₃ β₄ n = 0

end Virasoro.Sphere
