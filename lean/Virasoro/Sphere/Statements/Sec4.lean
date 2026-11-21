import Virasoro.Sphere.Germs
import Virasoro.Statements.Prelude
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Frozen statements: `sphere/paper.tex`, Section 4
(Generic recursion and all-order algebraic confluence)
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

/-- Lemma 4.2 (`lem:3pt-factor`), sphere/paper.tex l.1232–1239.  For a homogeneous vector
`w ∈ M(c,h)_ℓ` and a partition `Z` of `M`,
`⟨L_{-Z}w|Φ_b(1)|Δ_a⟩ = γ_Z(h+ℓ;Δ_a,Δ_b) ⟨w|Φ_b(1)|Δ_a⟩`.

Demand sheet.
- complex `c, h, Δ_a, Δ_b`; `φ` is the functional of Definition 2.1 (l.1233);
- homogeneous of level `ℓ`: `L₀w = (h+ℓ)w` (l.1233);
- every `M` and every partition `Z` of `M`; identity (l.1236–1237). -/
def Stmt_lem_3pt_factor : Prop :=
  ∀ (c h Δa Δb : ℂ) (φ : Verma ℂ c h →ₗ[ℂ] ℂ), IsThreePoint Δa Δb φ →
    ∀ (ℓ : ℕ) (w : Verma ℂ c h), Verma.L 0 w = (h + (ℓ : ℂ)) • w →
      ∀ (M : ℕ) (Z : Nat.Partition M),
        φ (VirEnv.negOp c Z.word • w) = gammaY (h + (ℓ : ℂ)) Δa Δb Z.word * φ w

/-- Proposition 4.3 (`prop:imported`), sphere/paper.tex l.1248–1265.  For positive `r, s` and
generic `b`, let `χ_{r,s}(b)` be the unique singular vector of level `rs` with
`L_{-1}^{rs}`-coefficient `1`.  Then `β_{χ_{r,s}(b)} = 𝒜_{r,s}(b)⁻¹` and
`⟨χ_{r,s}(b)|Φ_b(1)|Δ_a⟩ = P_{r,s}(b,Δ_a,Δ_b)`, as identities of rational functions of `b`;
`χ_{r,s}(b)` is regular at every `b⋆ ∈ ℂ^×` and the second identity specializes to every `b⋆`.

Demand sheet.
- positive `r, s`; the vector over `ℚ(b)` (`b = RatFunc.X`), existence and uniqueness among
  normalized singular vectors, as in the torus `NormalizationIdentities` (l.1249–1251);
- first identity over `ℚ(b)` only ("used only as an identity of rational functions of `b`",
  l.1263–1264);
- second identity over `ℚ(b)` for all `Δ_a, Δ_b ∈ ℚ(b)` (it is polynomial in them); the
  three-point scalar of a vector with coordinates `p` is `∑_Y p_Y γ_Y(h_{r,s};Δ_a,Δ_b)`
  (Definition 2.1) (l.1255–1256);
- regularity at every `b₁ ≠ 0` and the second identity there for all complex `Δ_a, Δ_b`
  (l.1258–1263). -/
def Stmt_prop_imported : Prop :=
  ∀ r s : ℕ, 0 < r → 0 < s →
    ∃ p : Nat.Partition (r * s) → RatFunc ℚ,
      (p (onesPartition (r * s)) = 1 ∧
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p) (r * s)) ∧
      (∀ p' : Nat.Partition (r * s) → RatFunc ℚ, p' (onesPartition (r * s)) = 1 →
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p') (r * s) → p' = p) ∧
      crossScalar (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) p =
        (genA r s (RatFunc.X : RatFunc ℚ))⁻¹ ∧
      (∀ Δa Δb : RatFunc ℚ,
        ∑ Y, p Y * gammaY (kacH r s (RatFunc.X : RatFunc ℚ)) Δa Δb Y.word =
          fusP r s (RatFunc.X : RatFunc ℚ) Δa Δb) ∧
      (∀ b₁ : ℂ, b₁ ≠ 0 →
        (∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (p Y)) ≠ 0) ∧
        ∀ Δa Δb : ℂ,
          ∑ Y, RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y) * gammaY (kacH r s b₁) Δa Δb Y.word =
            fusP r s b₁ Δa Δb)

/-- The identity (4.3) of the generic Zamolodchikov recursion at `b` and complex external
weights `Δ_i`, as rational functions of `Δ` over `ℂ`. -/
def SphRecursionAt (b : ℂ) (Δe : Fin 4 → ℂ) (N : ℕ) : Prop :=
  Hsph (kacC b) Δe N =
    ∑ a ∈ labels N,
      RatFunc.C (Rsph a.1 a.2 b Δe) / (RatFunc.X - RatFunc.C (kacHL a b)) *
        RatFunc.C (RatFunc.eval (RingHom.id ℂ) (kacHL a b + (a.lvl : ℂ))
          (Hsph (kacC b) Δe (N - a.lvl)))

/-- Proposition 4.4 (`prop:generic-recursion`), sphere/paper.tex l.1284–1295.  Fix `N ≥ 1`.
For every `b ∈ ℂ^×` outside a finite set of algebraic values,
`H_N(c(b),Δ,Δ_i) = ∑_{rs ≤ N} ℛ^sph_{r,s}(b,Δ_i)/(Δ - h_{r,s}(b)) ·
H_{N-rs}(c(b), h_{r,s}(b)+rs, Δ_i)` as rational functions of `Δ`, polynomial in the `Δ_i`.

Demand sheet.
- `N ≥ 1`; a finite exceptional set of algebraic numbers, chosen before `b` and the `Δ_i`
  (l.1285–1286);
- `b ≠ 0`, `b` outside the set;
- "polynomial in `(Δ₁,…,Δ₄)`": the identity is stated for all complex `Δ_i`, which is the
  polynomial identity (l.1293–1294);
- identity of rational functions of `Δ`; the shifted coefficient is the value of
  `H_{N-rs}` at `h_{r,s}(b)+rs` (l.1288–1291). -/
def Stmt_prop_generic_recursion : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ E : Finset ℂ, (∀ x ∈ E, IsAlgebraic ℚ x) ∧
    ∀ b : ℂ, b ≠ 0 → b ∉ E → ∀ Δe : Fin 4 → ℂ, SphRecursionAt b Δe N

/-- The backward precision rule of Lemma 4.6 at the base point `b⋆`, for the germs over
`K⋆ = ℂ(Δ₁,…,Δ₄)`; same reading as the torus `PrecisionRule`. -/
def PrecisionRuleSph (b : ℂ) : Prop :=
  (∀ (a g : Label) (M : ℕ) (U : ℤ), g ∈ labels M →
    ∀ A' S' : K4⸨X⸩,
      (-((piGg (RgSph b) g + sigmaG (cK b) a g : ℕ) : ℤ) : WithTop ℤ) ≤ A'.orderTop →
      (-((WGg (cK b) (RgSph b) (M - g.lvl) g : ℕ) : ℤ) : WithTop ℤ) ≤ S'.orderTop →
      (∀ n : ℤ, n ≤ U + (WGg (cK b) (RgSph b) (M - g.lvl) g : ℕ) →
        A'.coeff n = (RgSph b g / (zG (cK b) a - hG (cK b) g)).coeff n) →
      (∀ n : ℤ, n ≤ U + (piGg (RgSph b) g + sigmaG (cK b) a g : ℕ) →
        S'.coeff n = (SGg (cK b) (RgSph b) (M - g.lvl) g).coeff n) →
      ∀ n : ℤ, n ≤ U →
        (A' * S').coeff n =
          (RgSph b g / (zG (cK b) a - hG (cK b) g) *
            SGg (cK b) (RgSph b) (M - g.lvl) g).coeff n) ∧
  (∀ (N : ℕ) (lam : ℂ) (a : Label) (k : ℕ), 1 ≤ N → a ∈ collClass N b lam → 1 ≤ k →
    ∀ R' S' D' : K4⸨X⸩,
      (-((piGg (RgSph b) a : ℕ) : ℤ) : WithTop ℤ) ≤ R'.orderTop →
      (-((WGg (cK b) (RgSph b) (N - a.lvl) a : ℕ) : ℤ) : WithTop ℤ) ≤ S'.orderTop →
      (∀ n : ℤ, n ≤ (WGg (cK b) (RgSph b) (N - a.lvl) a : ℕ) →
        R'.coeff n = (RgSph b a).coeff n) →
      (∀ n : ℤ, n ≤ (piGg (RgSph b) a : ℕ) →
        S'.coeff n = (SGg (cK b) (RgSph b) (N - a.lvl) a).coeff n) →
      (0 : WithTop ℤ) ≤ D'.orderTop →
      (∀ n : ℤ, n ≤ (vhatg (cK b) (RgSph b) N a : ℕ) →
        D'.coeff n = (deltaG (cK b) (cK lam) a ^ (k - 1)).coeff n) →
      (R' * S' * D').coeff 0 =
        (BGg (cK b) (RgSph b) N a * deltaG (cK b) (cK lam) a ^ (k - 1)).coeff 0)

/-- Lemma 4.6 (`lem:precision-budget`), sphere/paper.tex l.1358–1367.  To compute `S_{a,M}(t)`
through `t^U` it suffices to compute, for each `g` with `ℓ_g ≤ M`, `R_g/(z_a - h_g)` through
`t^{U+W_{g,M-ℓ_g}}` and `S_{g,M-ℓ_g}` through `t^{U+π_g+σ_{a,g}}`; in particular `R_a` through
`t^{W_{a,N-ℓ_a}}`, `S_{a,N-ℓ_a}` through `t^{π_a}` and `δ_a^{k-1}` through `t^{v̂_{a,N}}` suffice
for all collision moments at level `N`.

Demand sheet.
- every `b⋆ ≠ 0` (l.1322);
- "suffices to compute through `t^n`": replacing a germ by any germ with the same coefficients
  up to `t^n` and the same a priori valuation bound does not change the required coefficients
  (the reading of the torus Lemma 7.4);
- both parts, for all labels, levels and `k ≥ 1` (l.1359–1366). -/
def Stmt_lem_precision_budget : Prop := ∀ b : ℂ, b ≠ 0 → PrecisionRuleSph b

/-- Theorem 4.7 (`thm:confluence`), sphere/paper.tex l.1369–1390.  Fix `b⋆ ∈ ℂ^×`, `N ≥ 1`.
(i) Every collision moment `Ã⋆_{λ,k,N}` lies in `ℚ(b⋆)[Δ₁,…,Δ₄]`.
(ii) `H_N(c⋆,Δ,Δ_i) = ∑_{λ ∈ Λ_N(b⋆)} ∑_{k=1}^{M̂⋆_{λ,N}} Ã⋆_{λ,k,N}/(Δ-λ)^k`.
(iii) `ℬ_N(c⋆,Δ,Δ_i)` is a polynomial of degree `N` in `Δ` plus a finite partial-fraction sum
over `Λ_N(b⋆)`.

Demand sheet.
- every `b⋆ ≠ 0`, every `N ≥ 1` (l.1371);
- (i) for `λ ∈ Λ_N(b⋆)` and `1 ≤ k ≤ M̂⋆_{λ,N}` (the range of Definition 4.5): a polynomial in
  the `Δ_i` over `ℂ` whose coefficients lie in the subfield `ℚ(b⋆)`; "computed in finitely many
  algebraic operations" is not a formal claim (l.1373–1376);
- (ii) identity in `ℂ(Δ₁,…,Δ₄)(Δ)` (l.1377–1383);
- (iii) `ℬ_N = Q + ∑_{λ ∈ Λ_N(b⋆)} PP_{Δ=λ} ℬ_N` with `deg Q = N` exactly; the explicit
  substitution into equation (2.8) is not restated (l.1385–1388). -/
def Stmt_thm_confluence : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
    (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k → k ≤ Mhatg (cK b) (RgSph b) N (cK lam) →
      ∃ P : MvPolynomial (Fin 4) ℂ, (∀ m, P.coeff m ∈ Subfield.closure ({b} : Set ℂ)) ∧
        algebraMap (MvPolynomial (Fin 4) ℂ) K4 P = Atildeg (cK b) (RgSph b) N (cK lam) k) ∧
    Hsph (kacC (cK b)) ΔK N =
      ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (Mhatg (cK b) (RgSph b) N (cK lam)),
        RatFunc.C (Atildeg (cK b) (RgSph b) N (cK lam) k) /
          (RatFunc.X - RatFunc.C (cK lam)) ^ k ∧
    ∃ Q : K4[X], Q.natDegree = N ∧
      Bsph (kacC (cK b)) ΔK N =
        algebraMap K4[X] (RatFunc K4) Q + ∑ lam ∈ Lam N b, PP (Bsph (kacC (cK b)) ΔK N) (cK lam)

end Virasoro.Sphere
