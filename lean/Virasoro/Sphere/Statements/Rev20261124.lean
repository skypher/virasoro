import Virasoro.Sphere.Statements.Sec3c
import Virasoro.Sphere.Statements.Sec5

/-!
# Statements of `sphere/paper.tex` added or restated after 70bac53 (state of 2026-11-24)

- The presentation pass of 2026-11-24 (307908d) split Lemma 3.3(iii) of 70bac53 off as
  Proposition 3.4 (`prop:gaussian-limit`).  Lemma 3.3 now consists of parts (i) and (ii).
  `Stmt_lem_lambda_expansion` (Statements/Sec3c.lean) keeps the 70bac53 form, which is the
  conjunction of the two current statements.
- Lemma 5.2(iii) now says that the zero locus of `φ^±_k` in the `(x_a,x_b)`-plane is a union of
  lines `x_a ± x_b = e` with `|e| ≤ m^±_k - p' - p` that contains both lines
  `x_a - x_b = ±(m^±_k - p' - p)`; that `φ^±_k ≠ 0` when `|x_a + x_b|` and `|x_a - x_b|` both
  exceed `m^±_k - p' - p`; and that these statements are unchanged under
  `(x_a,x_b) ↦ (-x_a,-x_b)`.  The 70bac53 form (`Stmt_lem_pi_factorization`) has the bound on
  the zeros and the two extremal lines; the current form adds that each zero lies on a whole
  line of the zero locus, the nonvanishing clause and the symmetry.

The variables `μ, λ` of the encoding are the paper's `η, ω` (`c = 1 + 24η²`, `Δ = ω² + η²`).
-/

namespace Virasoro.Sphere

open Polynomial

/-- Lemma 3.3 (`lem:lambda-expansion`), parts (i) and (ii), in the encoding of
`Stmt_lem_lambda_expansion`: the Ward series and its specializations, regularity at
`ω = ∞` (i); `S^{(0)}`, the `ι`-parities of `S^{(1)}` and `S^{(2)}`, and the equations
`L_k^{(0)} S^{(2)}_2 = k`, `L_k^{(0)} S^{(2)}_1 = -1` (ii). -/
def Stmt_lem_lambda_expansion_paper : Prop :=
  (∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ,
    (∃! F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F) ∧
    ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F →
      (∀ lam : ℝ, 0 < lam →
        (∀ (m : ℕ) (α : ℕ+ →₀ ℕ), ((F m).coeff α).denom.eval (lam : ℂ) ≠ 0) ∧
        IsWardSeries (μ : ℂ) (lam : ℂ) (Δ1 : ℂ) (Δ2 : ℂ) fun m => specialize (lam : ℂ) (F m)) ∧
      (∀ α : ℕ+ →₀ ℕ, RegularAtInfty (Slam F α)) ∧
      Sord F 0 = S0 ∧
      iota (Sord F 2) = Sord F 2) ∧
  ∃ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ,
    IsExpansionData S1t S2c S21 S22 ∧
    iota S1t = -S1t ∧
    (∀ k : ℕ, 1 ≤ k → L0 k S22 = MvPowerSeries.C (k : ℂ) ∧ L0 k S21 = -1)

/-- Proposition 3.4 (`prop:gaussian-limit`).  In the setting of Lemma 3.3, the function
`-2∑_m m z^{-m} σ_m σ̄_m + S^{(0)}(σ) + S̃^{(0)}(σ̄)` has a unique saddle point, with
`σ_*(z) ∈ izℚ[[z]]^ℕ`.  There exist universal series `𝓘₀, Φ_c^raw, Φ₁, Φ₂ ∈ zℚ[[z]]`, with
`Φ_j(z) = S^{(2)}_j(σ_*(z))`, such that, coefficient by coefficient in `z`,
`lim_{ω→∞} e^{-ω²𝓘₀(z)} ℬ(1+24η²,ω²+η²,Δ_i;z)
  = det(I-M(z)²)^{-1/2} exp(η²Φ_c^raw + (Δ₁+Δ₄-1/8)Φ₁ + (Δ₂+Δ₃-1/8)Φ₂)`  (3.6).

Encoding as in part (iii) of `Stmt_lem_lambda_expansion`; the series `S^{(2)}_j` are those of
Lemma 3.3, given by `IsExpansionData`. -/
def Stmt_prop_gaussian_limit : Prop :=
  ∃ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ,
    IsExpansionData S1t S2c S21 S22 ∧
    ∃ I0 Φc Φ1 Φ2 : PowerSeries ℂ, InZQ I0 ∧ InZQ Φc ∧ InZQ Φ1 ∧ InZQ Φ2 ∧
      ∃ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb ∧
        (∀ σ' σb' : ℕ+ → PowerSeries ℂ, IsSaddle σ' σb' → σ' = σ ∧ σb' = σb) ∧
        (∀ m : ℕ+, InIZQ (σ m)) ∧
        Φ1 = MvPowerSeries.subst σ S21 ∧ Φ2 = MvPowerSeries.subst σ S22 ∧
        ∀ μ : ℝ, 0 < μ → ∀ (Δe : Fin 4 → ℝ) (n : ℕ),
          Filter.Tendsto
            (fun lam : ℝ => PowerSeries.coeff n
              ((PowerSeries.exp ℂ).subst (PowerSeries.C (-(lam : ℂ) ^ 2) * I0) *
                PowerSeries.mk fun j =>
                  RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
                    (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) j)))
            Filter.atTop
            (nhds (PowerSeries.coeff n
              (detInvSqrt.map (algebraMap ℚ ℂ) *
                (PowerSeries.exp ℂ).subst
                  ((μ : ℂ) ^ 2 • Φc + ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • Φ1 +
                    ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • Φ2))))

/-- `f` vanishes on the whole line through `(x_a,x_b)` on which `x_a + x_b = e` or
`x_a - x_b = e`, and `(x_a,x_b)` lies on it. -/
def ZeroOnLine (f : ℂ → ℂ → ℂ) (e : ℤ) (xa xb : ℂ) : Prop :=
  (xa + xb = (e : ℂ) ∧ ∀ ya yb : ℂ, ya + yb = (e : ℂ) → f ya yb = 0) ∨
  (xa - xb = (e : ℂ) ∧ ∀ ya yb : ℂ, ya - yb = (e : ℂ) → f ya yb = 0)

/-- The weight `Δ = (x² - (p'-p)²)/(4pp')` of the momentum coordinate `x` of Lemma 5.2(iii). -/
noncomputable def wtX (p p' : ℕ) (x : ℂ) : ℂ := (x ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')

/-- Lemma 5.2 (`lem:pi-factorization`), in the paper's current form.  Parts (i) and (ii) as in
`Stmt_lem_pi_factorization`.  (iii) With `Δ_a = (x_a² - (p'-p)²)/(4pp')` and `Δ_b` likewise:
every zero of `φ^±_k` lies on a line `x_a ± x_b = e` with `|e| ≤ m^±_k - p' - p` contained in the
zero locus (so the zero locus is a union of such lines); both lines
`x_a - x_b = ±(m^±_k - p' - p)` lie in it; if `|x_a + x_b|` and `|x_a - x_b|` both exceed
`m^±_k - p' - p`, then `φ^±_k ≠ 0`; and `φ^±_k` takes the same value at `(x_a,x_b)` and
`(-x_a,-x_b)`, so these statements are unchanged under that map.  All `x_a, x_b ∈ ℂ`. -/
def Stmt_lem_pi_factorization_paper : Prop :=
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
      (∀ xa xb : ℂ,
        let φ : ℂ → ℂ → ℂ := fun ya yb => piScalar (kacH r s b) x (wtX p p' ya) (wtX p p' yb)
        let mm : ℤ := nOrb p p' r s ε k - p' - p
        (φ xa xb = 0 → ∃ e : ℤ, |e| ≤ mm ∧ ZeroOnLine φ e xa xb) ∧
        ((xa - xb = (mm : ℂ) ∨ xa - xb = -(mm : ℂ)) → φ xa xb = 0) ∧
        ((mm : ℝ) < ‖xa + xb‖ → (mm : ℝ) < ‖xa - xb‖ → φ xa xb ≠ 0) ∧
        φ (-xa) (-xb) = φ xa xb)

end Virasoro.Sphere
