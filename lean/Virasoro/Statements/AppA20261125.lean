import Virasoro.Statements.Sec6c
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Statements of Appendix A of `paper.tex` at 086b33a (Lemmas A.1–A.3)

The pass of 2026-11-25 (e50db7c, 086b33a) split the proof of Proposition 9.2(i)–(ii) into
Lemma A.1 (`lem:mode-count`, paper.tex l.2915–2927), Lemma A.2 (`lem:odd-primes`, l.2947–2959)
and Lemma A.3 (`lem:level-poly`, l.3001–3009).  Throughout, `t = b²`, `Δ = Y/t²`,
`c(b) = 6/t + 13 + 6t` (`cT`) and `d = −2/t + ζ`.

Reading conventions.
- A polynomial with coefficients in `ℤ[1/2]` is a rational polynomial each of whose coefficients
  is an integer over a power of `2` (as in `Stmt_prop_h13_nonvanishing`).
- Polynomials in `(t, Y)` and `(t, Y, ζ)` are `MvPolynomial (Fin 2) ℚ` and
  `MvPolynomial (Fin 3) ℚ` (variables `0 ↦ t`, `1 ↦ Y`, `2 ↦ ζ`); identities with the rational
  matrices `G_M`, `ρ_M` are read in the fraction field of `ℚ[t,Y,ζ]`.
- "`t` and `Y` are algebraically independent over `𝔽_ϖ` in the residue field" is read as: for
  every `f ∈ ℤ[X₀,X₁]` with a coefficient not divisible by `ϖ`, `f(t,Y)` is not in the maximal
  ideal.  (The residue field has characteristic `ϖ`, since `ϖ` is a uniformizer, and every
  polynomial over `𝔽_ϖ` lifts to such an `f`.)
- "`𝒮_𝔭` contains `ℤ_(ϖ)[b,b⁻¹]`": the rationals with denominator prime to `ϖ` lie in `𝒮_𝔭`,
  `b` is a unit of `𝒮_𝔭`, and `b` is transcendental over `ℚ`.
- A matrix inverse is taken only with the determinant stated nonzero.
- `R_M` lives in `ℚ[Y,Y⁻¹][[t]]`: it is the expansion in `t` of a rational function of `(t,Δ)`
  at `Δ = Y/t²`, read as `R_M · q = p` for polynomials `p, q` in `(t, Y)` with
  `R_M`'s rational function equal to `p/q` and `q` invertible in `ℚ[Y,Y⁻¹][[t]]`
  (`IsTExpansion`; the expansion is unique).  "A polynomial in `M` of degree at most `D`" for an
  integer `D` is a polynomial `f ∈ ℚ[X]` whose coefficients of degree `> D` vanish (so `f = 0`
  when `D < 0`).
-/

namespace Virasoro

open Polynomial

/-- `K_Z = ∏_n m_n! (2n)^{m_n}` for `Z = (1^{m_1} 2^{m_2} ⋯)` (paper.tex l.2910). -/
def appKZ {M : ℕ} (Z : Nat.Partition M) : ℕ :=
  ∏ n ∈ Z.parts.toFinset, (Z.parts.count n).factorial * (2 * n) ^ (Z.parts.count n)

/-- The coefficients lie in `ℤ[1/2]`. -/
def HalfIntCoeffs {σ : Type*} (p : MvPolynomial σ ℚ) : Prop :=
  ∀ e, ∃ (z : ℤ) (n : ℕ), p.coeff e = (z : ℚ) / 2 ^ n

/-- The fraction field of `ℚ[t,Y,ζ]`. -/
abbrev KtYz : Type := FractionRing (MvPolynomial (Fin 3) ℚ)

/-- `ℚ[t,Y,ζ] → ℚ(t,Y,ζ)`. -/
noncomputable def evtYz : MvPolynomial (Fin 3) ℚ →+* KtYz := algebraMap _ _

/-- Lemma A.1 (`lem:mode-count`), paper.tex l.2915–2927.  For `Z, Z' ⊢ M` put
`G̃_{Z,Z'} = t^{ℓ(Z)+ℓ(Z')} G_M(c(b),Y/t²)_{Z,Z'}` and
`ρ̃_{Z,Z'} = t^{ℓ(Z)+ℓ(Z')} ρ_M(c(b),Y/t²,−2/t+ζ)_{Z,Z'}`.  Then `G̃ = D₀(Y) + t G₁(t,Y)`,
`D₀ = diag(K_Z Y^{ℓ(Z)})`, with `G₁ ∈ Mat(ℤ[1/2][t,Y])`, and `ρ̃ ∈ Mat(ℤ[1/2][t,Y,ζ])` with
`ρ̃(0,Y;ζ)` independent of `ζ`.

Demand sheet.
- every level `M ≥ 0`; `Z, Z'` range over the partitions of `M`, `ℓ(Z)` the number of parts
  (l.2916–2918);
- `G₁`: a matrix of polynomials in `(t, Y)` with coefficients in `ℤ[1/2]`; identity
  `D₀ + t G₁ = G̃` in `ℚ(t,Y,ζ)`, entry by entry (l.2920–2925);
- `ρ̃`: a matrix of polynomials in `(t, Y, ζ)`, `ζ` indeterminate, coefficients in `ℤ[1/2]`;
  identity with `t^{ℓ(Z)+ℓ(Z')} ρ_M` entry by entry (l.2925–2926);
- `ρ̃(0,Y;ζ)` independent of `ζ`: setting `t = 0`, the value equals the value at `ζ = 0`
  (l.2926–2927). -/
def Stmt_lem_mode_count : Prop :=
  ∀ M : ℕ, ∃ (G1 : Matrix (Nat.Partition M) (Nat.Partition M) (MvPolynomial (Fin 2) ℚ))
      (ρt : Matrix (Nat.Partition M) (Nat.Partition M) (MvPolynomial (Fin 3) ℚ)),
    let t : KtYz := evtYz (MvPolynomial.X 0)
    let Y : KtYz := evtYz (MvPolynomial.X 1)
    let ζ : KtYz := evtYz (MvPolynomial.X 2)
    (∀ Z Z', HalfIntCoeffs (G1 Z Z')) ∧
    (∀ Z Z', HalfIntCoeffs (ρt Z Z')) ∧
    (∀ Z Z', evtYz (MvPolynomial.rename Fin.castSucc
        ((if Z = Z' then MvPolynomial.C (appKZ Z : ℚ) * MvPolynomial.X 1 ^ Z.parts.card
          else 0) + MvPolynomial.X 0 * G1 Z Z')) =
      t ^ (Z.parts.card + Z'.parts.card) * gram (cT t) (Y / t ^ 2) M Z Z') ∧
    (∀ Z Z', evtYz (ρt Z Z') =
      t ^ (Z.parts.card + Z'.parts.card) * torus (cT t) (Y / t ^ 2) (-2 / t + ζ) M Z Z') ∧
    (∀ Z Z', MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
          Fin 3 → MvPolynomial (Fin 3) ℚ) (ρt Z Z') =
        MvPolynomial.aeval (![0, MvPolynomial.X 1, 0] : Fin 3 → MvPolynomial (Fin 3) ℚ)
          (ρt Z Z'))

/-- Lemma A.2 (`lem:odd-primes`), paper.tex l.2947–2959.  Let `ϖ` be an odd prime.  There are a
discrete valuation ring `𝒮_𝔭` with uniformizer `ϖ` that contains `ℤ_(ϖ)[b,b⁻¹]`, and elements
`q₀, α ∈ 𝒮_𝔭` with `c(b) = 1 − 12q₀²` and `Δ = ½α(α − 2q₀)`, such that `t = b²` and
`Y = ½b⁴α(α − 2q₀)` are algebraically independent over `𝔽_ϖ` in the residue field and, for every
`M ≥ 0`, `M! G_{M−s}(c(b),Δ)⁻¹ ∈ Mat_{p(M−s)}(𝒮_𝔭)` (`0 ≤ s ≤ M`).

Demand sheet.
- every odd prime `ϖ` (l.2948);
- `𝒮_𝔭`: a subring of a field `K` of characteristic `0`, a discrete valuation ring, with `ϖ`
  irreducible in it (a uniformizer) (l.2948–2949);
- contains `ℤ_(ϖ)[b,b⁻¹]`: `z/n ∈ 𝒮_𝔭` for `ϖ ∤ n`; `b` a unit of `𝒮_𝔭`; `b` transcendental
  over `ℚ` (l.2949–2950);
- `q₀, α ∈ 𝒮_𝔭`, `c(b) = 1 − 12q₀²` as `cT (b²) = 1 − 12 q₀²` in `K`; `Δ = ½α(α − 2q₀)`
  substituted (l.2950–2951);
- `Y ∈ 𝒮_𝔭` with `Y = ½b⁴α(α − 2q₀)` in `K`; algebraic independence of `t = b²` and `Y` over
  `𝔽_ϖ` in the residue field, in the reading of the module docstring (l.2952–2953);
- for all `M ≥ 0` and `0 ≤ s ≤ M`: `G_{M−s}(c(b),Δ)` invertible over `K` (implicit in the
  inverse) and every entry of `M! G_{M−s}(c(b),Δ)⁻¹` in `𝒮_𝔭` (l.2953–2958). -/
def Stmt_lem_odd_primes : Prop :=
  ∀ ϖ : ℕ, ϖ.Prime → ϖ ≠ 2 →
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (S : Subring K)
      (_ : IsDiscreteValuationRing S) (b q₀ α Y : S),
      Irreducible ((ϖ : ℕ) : S) ∧
      (∀ (z : ℤ) (n : ℕ), ¬ ϖ ∣ n → (z : K) / (n : K) ∈ S) ∧
      IsUnit b ∧ Transcendental ℚ (b : K) ∧
      cT ((b : K) ^ 2) = 1 - 12 * (q₀ : K) ^ 2 ∧
      (Y : K) = (b : K) ^ 4 * (α : K) * ((α : K) - 2 * (q₀ : K)) / 2 ∧
      (∀ f : MvPolynomial (Fin 2) ℤ, (∃ e, ¬ (ϖ : ℤ) ∣ f.coeff e) →
        MvPolynomial.aeval (![b ^ 2, Y] : Fin 2 → S) f ∉ IsLocalRing.maximalIdeal S) ∧
      ∀ M s : ℕ, s ≤ M →
        (gram (cT ((b : K) ^ 2)) ((α : K) * ((α : K) - 2 * (q₀ : K)) / 2) (M - s)).det ≠ 0 ∧
        ∀ Z Z' : Nat.Partition (M - s),
          (M.factorial : K) *
              (gram (cT ((b : K) ^ 2)) ((α : K) * ((α : K) - 2 * (q₀ : K)) / 2) (M - s))⁻¹ Z Z'
            ∈ S

/-- `ℚ[Y,Y⁻¹][[t]]`. -/
abbrev SerTY : Type := PowerSeries (LaurentPolynomial ℚ)

/-- `[t^i Y^j]` on `ℚ[Y,Y⁻¹][[t]]`. -/
noncomputable def coeffTY (F : SerTY) (i : ℕ) (j : ℤ) : ℚ :=
  (PowerSeries.coeff i F).coeff j

/-- `ℚ[t,Y] → ℚ(t)(Δ)`, `t ↦ t`, `Y ↦ t²Δ` (variables as in `Stmt_prop_h13_nonvanishing`). -/
noncomputable def tyToRat : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] RatFunc (RatFunc ℚ) :=
  MvPolynomial.aeval
    (![RatFunc.C (RatFunc.X : RatFunc ℚ), RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] :
      Fin 2 → RatFunc (RatFunc ℚ))

/-- `ℚ[t,Y] → ℚ[Y,Y⁻¹][[t]]`, `t ↦ t`, `Y ↦ Y`. -/
noncomputable def tyToSer : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] SerTY :=
  MvPolynomial.aeval
    (![PowerSeries.X, PowerSeries.C (LaurentPolynomial.T 1 : LaurentPolynomial ℚ)] :
      Fin 2 → SerTY)

/-- `r ∈ ℚ[Y,Y⁻¹][[t]]` is the expansion in `t` of `x ∈ ℚ(t)(Δ)` at `Δ = Y/t²`. -/
def IsTExpansion (x : RatFunc (RatFunc ℚ)) (r : SerTY) : Prop :=
  ∃ p q : MvPolynomial (Fin 2) ℚ, tyToRat q ≠ 0 ∧ tyToRat p = x * tyToRat q ∧
    IsUnit (tyToSer q) ∧ r * tyToSer q = tyToSer p

/-- `(M!/2^M) Y^M F_M(c(b),Y/t²,−2/t+ζ)` as a rational function of `(t,Δ)`, `Y = t²Δ`,
for `ζ = −1` (`ν = 0`) and `ζ = 2` (`ν = 1`). -/
noncomputable def appRrat (ν : Fin 2) (M : ℕ) : RatFunc (RatFunc ℚ) :=
  ((M.factorial : ℚ) / 2 ^ M : RatFunc (RatFunc ℚ)) *
    (RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X) ^ M *
    Frat (cT (RatFunc.X : RatFunc ℚ))
      (if ν = 0 then -1 - 2 / (RatFunc.X : RatFunc ℚ) else 2 - 2 / (RatFunc.X : RatFunc ℚ)) M

/-- Lemma A.3 (`lem:level-poly`), paper.tex l.3001–3009.  For `ζ ∈ {−1, 2}` put
`R_M(t,Y) = (M!/2^M) Y^M F_M(c(b),Y/t²,−2/t+ζ)`.  For every `i ≥ 0` and `j ∈ ℤ`, the coefficient
`[t^i Y^j] R_M` is a polynomial in `M` of degree at most `2i + 2j`, valid for all `M ≥ 0`.

Demand sheet.
- both values `ζ = −1, 2` (`ν = 0, 1`) (l.3002);
- `R_M ∈ ℚ[Y,Y⁻¹][[t]]` is the expansion of the rational function (`IsTExpansion`), for every
  `M ≥ 0` (l.3003–3005);
- every `i ≥ 0`, every `j ∈ ℤ`: one polynomial `f ∈ ℚ[X]` with no coefficient beyond degree
  `2i + 2j`, and `[t^i Y^j] R_M = f(M)` for every `M ≥ 0` (l.3006–3008). -/
def Stmt_lem_level_poly : Prop :=
  ∀ ν : Fin 2, ∃ R : ℕ → SerTY,
    (∀ M, IsTExpansion (appRrat ν M) (R M)) ∧
    ∀ (i : ℕ) (j : ℤ), ∃ f : ℚ[X],
      (∀ n : ℕ, 2 * (i : ℤ) + 2 * j < n → f.coeff n = 0) ∧
      ∀ M : ℕ, coeffTY (R M) i j = f.eval (M : ℚ)

end Virasoro
