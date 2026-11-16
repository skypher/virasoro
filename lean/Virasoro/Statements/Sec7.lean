import Virasoro.Statements.Sec4

/-!
# Frozen statements: Section 7 (All-order confluent recursion)

The germs are Laurent series in `t = b - b⋆` over `Kd = ℂ(d)`, with base point
`RatFunc.C b⋆` and external weight `dvar`.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

/-- Lemma 7.2 (`lem:shifted-valuation-bound`): `ord_t S_{a,M}(t) ≥ - W_{a,M}`, for positive
labels `a` and all `M ≥ 0`, where `W_{a,M}` is the recursively defined majorant `WG`. -/
def Stmt_lem_shifted_valuation_bound : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ (a : Label) (M : ℕ), 0 < a.1 → 0 < a.2 →
    (-((WG (RatFunc.C b : Kd) dvar M a : ℕ) : ℤ) : WithTop ℤ) ≤
      (SG (RatFunc.C b : Kd) dvar M a).orderTop

/-- Lemma 7.4 (`lem:precision-budget`).  If `S_{a,M}` is required through the coefficient of
`t^U`, then for its `g`-summand it suffices to know `R_g/(z_a - h_g)` through
`t^{U + W_{g,M-ℓ_g}}` and `S_{g,M-ℓ_g}` through `t^{U + π_g + σ_{a,g}}`; to compute every
collision moment at level `N` it suffices, for each `a`, to compute `R_a` through
`t^{W_{a,N-ℓ_a}}`, `S_{a,N-ℓ_a}` through `t^{π_a}` and `δ_a^{k-1}` through `t^{v̂_{a,N}}`.
"Sufficient to know through `t^n`" is read as: replacing the germ by any germ with the same
coefficients up to `t^n` and the same a priori valuation bound does not change the required
coefficients.  Since the rule applies at every node of the finite recursion tree, it gives a
finite precision at every node. -/
def Stmt_lem_precision_budget : Prop := ∀ b : ℂ, b ≠ 0 → PrecisionRule b

/-- Lemma 7.5 (`lem:collision-pole-support`).  Let `B(t) ∈ K⋆((t))` and `δ(t) ∈ t K⋆[[t]]`.
Every coefficient of `B(t)/(x - δ(t)) = ∑_{j≥0} B(t) δ(t)^j / x^{j+1}` as a Laurent series in
`t` is a finite `K⋆`-linear combination of `x⁻¹, x⁻², …`: for each `m` the coefficient of `t^m`
equals `∑_{j<n} [t^m](B δ^j) / x^{j+1}` for all large `n`.  Here `x` is the indeterminate of
`K⋆(x)`. -/
def Stmt_lem_collision_pole_support : Prop :=
  ∀ B δ : LaurentSeries Kd, (0 : WithTop ℤ) < δ.orderTop →
    ∀ m : ℤ, ∃ n : ℕ, ∀ n' : ℕ, n ≤ n' →
      (B.map (algebraMap Kd (RatFunc Kd)) /
          (HahnSeries.C (RatFunc.X : RatFunc Kd) - δ.map (algebraMap Kd (RatFunc Kd)))).coeff m =
        ∑ j ∈ Finset.range n', RatFunc.C ((B * δ ^ j).coeff m) / (RatFunc.X : RatFunc Kd) ^ (j + 1)

/-- The class sum `𝒢⋆_{λ,N} = ∑_{a ∈ C⋆_{λ,N}} B_{a,N}(t)/(Δ - h_a(t))` of (7.3), as a Laurent
series in `t` over `ℂ(d)(Δ)`. -/
noncomputable def Gclass (b : ℂ) (N : ℕ) (lam : ℂ) : LaurentSeries (RatFunc Kd) :=
  ∑ a ∈ collClass N b lam,
    (BG (RatFunc.C b : Kd) dvar N a).map (algebraMap Kd (RatFunc Kd)) /
      (HahnSeries.C (RatFunc.X : RatFunc Kd) -
        (hG (RatFunc.C b : Kd) a).map (algebraMap Kd (RatFunc Kd)))

/-- Corollary 7.6 (`cor:class-regular`): every `𝒢⋆_{λ,N}` lies in `K⋆(Δ)[[t]]`. -/
def Stmt_cor_class_regular : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Lam N b, ∀ m : ℤ, m < 0 →
    (Gclass b N lam).coeff m = 0

/-- The value at `t = 0` of a germ regular at `t = 0`. -/
noncomputable def germ0 (f : LaurentSeries Kd) : Kd := f.coeff 0

/-- The derivative `d/dt` at `t = 0` of a germ regular at `t = 0`. -/
noncomputable def germDot (f : LaurentSeries Kd) : Kd := f.coeff 1

/-- The second derivative `d²/dt²` at `t = 0` of a germ regular at `t = 0`. -/
noncomputable def germDDot (f : LaurentSeries Kd) : Kd := 2 * f.coeff 2

/-- `ζ(t) = z_κ(t) - h_τ(t)` for a branch `(κ, τ)` at the base point `b⋆`. -/
noncomputable def zetaG (b : ℂ) (κ τ : Label) : LaurentSeries Kd :=
  zG (RatFunc.C b : Kd) κ - hG (RatFunc.C b : Kd) τ

/-- The derivative term
`T = (Ṙ_κ R_τ + R_κ Ṙ_τ)/ζ̇ - R_κ R_τ ζ̈/(2 ζ̇²)` of Proposition 7.7, with every undotted factor
evaluated at `t = 0`. -/
noncomputable def Tterm (b : ℂ) (κ τ : Label) : Kd :=
  let Rκ := RG (RatFunc.C b : Kd) dvar κ
  let Rτ := RG (RatFunc.C b : Kd) dvar τ
  (germDot Rκ * germ0 Rτ + germ0 Rκ * germDot Rτ) / germDot (zetaG b κ τ)
    - germ0 Rκ * germ0 Rτ * germDDot (zetaG b κ τ) / (2 * germDot (zetaG b κ τ) ^ 2)

/-- The hypotheses (i)–(iii) of Proposition 7.7 on a branch `(κ, τ)` at level `N`: with
`M = N - ℓ_κ` and `z = z_κ(0)`, `ℓ_τ = M`, `τ` is the only label `g` with `ℓ_g ≤ M` and
`h_g(0) = z`; `R_κ` and `R_τ` are regular at `t = 0`; and `ζ(t) = z_κ(t) - h_τ(t)` has a simple
zero at `t = 0`. -/
def TwoBranchHyp (b : ℂ) (N : ℕ) (κ τ : Label) : Prop :=
  τ.lvl = N - κ.lvl ∧ τ ∈ labels (N - κ.lvl) ∧
  (∀ g ∈ labels (N - κ.lvl), kacHL g b = kacHL κ b + (κ.lvl : ℂ) ↔ g = τ) ∧
  (0 : WithTop ℤ) ≤ (RG (RatFunc.C b : Kd) dvar κ).orderTop ∧
  (0 : WithTop ℤ) ≤ (RG (RatFunc.C b : Kd) dvar τ).orderTop ∧
  (zetaG b κ τ).orderTop = (1 : ℤ)

/-- The finite part `Q(d) = ∂_z {(z - z₀) H_M(c⋆,z,d)} |_{z=z₀}`.  When `H_M(c⋆,·,d)` has at
most a simple pole at `z₀`, this derivative is the coefficient of `(z - z₀)⁰` in its Laurent
expansion at `z₀`, which is the definition used here. -/
noncomputable def finitePart (c : ℂ) (M : ℕ) (z₀ : ℂ) : Kd := lcoeff (HN c M) (pt z₀) 0

/-- Proposition 7.7 (`prop:two-branch`).  Fix `b⋆ ∈ ℂ^×`, `N ≥ 1` and `λ ∈ Λ_N(b⋆)` with
`C⋆_{λ,N} = {κ₁, κ₂}` (two labels).  For `i = 1, 2` put `M_i = N - ℓ_{κ_i}`, `z_i = z_{κ_i}(0)`
and suppose there is a label `τ_i` satisfying `TwoBranchHyp`.  With
`Q_i = ∂_z {(z - z_i) H_{M_i}(c⋆,z,d)} |_{z=z_i}` and `T_i` the derivative term `Tterm`,
`R_{κ₁} R_{τ₁}/ζ̇₁ + R_{κ₂} R_{τ₂}/ζ̇₂ = 0` at `t = 0`  (7.4), and
`PP_{Δ=λ} H_N(c⋆,Δ,d) = (ḣ_{κ₁} - ḣ_{κ₂}) R_{κ₁} R_{τ₁} / (ζ̇₁ (Δ-λ)²)
   + (R_{κ₁} Q₁ + R_{κ₂} Q₂ + T₁ + T₂)/(Δ-λ)`  (7.5). -/
def Stmt_prop_two_branch : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Lam N b, ∀ κ₁ κ₂ τ₁ τ₂ : Label,
    κ₁ ≠ κ₂ → collClass N b lam = {κ₁, κ₂} →
    TwoBranchHyp b N κ₁ τ₁ → TwoBranchHyp b N κ₂ τ₂ →
      let bs : Kd := RatFunc.C b
      let R : Label → Kd := fun a => germ0 (RG bs dvar a)
      let hdot : Label → Kd := fun a => germDot (hG bs a)
      let Q₁ := finitePart (kacC b) (N - κ₁.lvl) (kacHL κ₁ b + (κ₁.lvl : ℂ))
      let Q₂ := finitePart (kacC b) (N - κ₂.lvl) (kacHL κ₂ b + (κ₂.lvl : ℂ))
      R κ₁ * R τ₁ / germDot (zetaG b κ₁ τ₁) + R κ₂ * R τ₂ / germDot (zetaG b κ₂ τ₂) = 0 ∧
      PP (HN (kacC b) N) (pt lam) =
        poleTerm ((hdot κ₁ - hdot κ₂) * R κ₁ * R τ₁ / germDot (zetaG b κ₁ τ₁)) lam 2 +
        poleTerm (R κ₁ * Q₁ + R κ₂ * Q₂ + Tterm b κ₁ τ₁ + Tterm b κ₂ τ₂) lam 1

end Virasoro
