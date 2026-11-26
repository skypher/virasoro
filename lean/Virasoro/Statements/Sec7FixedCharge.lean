import Virasoro.Statements.Prelude
import Virasoro.FixedCharge

/-!
# Frozen statements: Section 7.2 of `paper.tex` (a recursion at the fixed charge)

Paper: `paper.tex`, Section 7.2 (`sec:fixed-charge`), Lemma 7.8 to Corollary 7.15, version of
2026-11-26.

Reading conventions.
* As in the statements of Section 7, the paper's field `K⋆ = ℚ(b⋆, d)` is realised inside
  `Kd = ℂ(d)`, germs in `t = b - b⋆` are Laurent series over `Kd`, and the base point is
  `bs = RatFunc.C b`.  A rational function of `b` is identified with its germ; "regular at
  `b⋆`" is `OrdGE x 0` (no negative powers of `t`), and its value at `b⋆` is `x.coeff 0`.
* A chain function `c^{(k)}_{λ→μ,j}` is nonzero only when `μ - λ` is a positive integer `D`;
  it is `chainFnC b λ D k j` (Definition 7.9, encoded by recursion on the level, see
  `Virasoro.FixedCharge`).  A sum over `μ` with `0 < μ - λ < N` is the sum over `n = μ - λ` in
  `Finset.Ioo 0 N`.
* `∂_Δ^j (H_M(c⋆,·) - PP_{Δ=μ} H_M(c⋆,·))` at `Δ = μ` is `j!` times the coefficient of
  `(Δ - μ)^j` in the Laurent expansion of `H_M(c⋆,·)` at `μ` (`lcoeff`), since the principal
  part has no nonnegative powers.
* `H_M(c(b), Δ, d)` with `b = b⋆ + t` is `Hrat (kacC (bGerm bs)) (C d) M`, a rational function of
  `Δ` over the field of germs; its colliding group at `μ` and the remainder `Reg^{(M)}_μ` are
  rational functions of `Δ` over the same field.  `Reg` "has no pole on `b = b⋆` near `Δ = μ`"
  means that `Reg = P/E` with `P, E` polynomials in `Δ` whose coefficients are power series in
  `t` and `E(0, μ) ≠ 0`; its restriction to `b = b⋆` is `P(0,·)/E(0,·)`, which (7.6) identifies.
  The derivatives `φ^{(M)}_{μ,j} = ∂_Δ^j Reg(b⋆ + t, μ) = j! [(Δ-μ)^j] Reg` (`phiRemC`) are
  then regular at `t = 0`.
* A series over `j` that converges `t`-adically is stated through valuations: for every `m`,
  every finite tail `∑_{J₁ ≤ j < J₂}` with `J₁` large has `t`-order at least `m`; an identity
  with such a series means that the difference with the partial sums over `j < J` has `t`-order
  at least `m` for `J` large.
-/

namespace Virasoro

open scoped LaurentSeries

/-- The base point `b⋆` as an element of `ℂ(d)`. -/
noncomputable abbrev bsC (b : ℂ) : Kd := RatFunc.C b

/-- `c^{(k)}_{λ→λ+D,j}` at the complex base point `b⋆` (Definition 7.9). -/
noncomputable def chainFnC (b lam : ℂ) (D k j : ℕ) : Kd⸨X⸩ :=
  chainFn (bsC b) dvar (pt lam) D k j

/-- The full moment `C_{λ,k,N}(t)` at the complex base point (Lemma 7.8). -/
noncomputable def fullMomentC (b : ℂ) (N : ℕ) (lam : ℂ) (k : ℕ) : Kd⸨X⸩ :=
  fullMoment (bsC b) dvar N (pt lam) k

/-- `φ^{(M)}_{μ,j}(t) = ∂_Δ^j Reg^{(M)}_μ(b⋆+t, μ)` at the complex base point (Lemma 7.12). -/
noncomputable def phiRemC (b : ℂ) (M : ℕ) (mu : ℂ) (j : ℕ) : Kd⸨X⸩ :=
  phiRem (bsC b) dvar M (pt mu) j

/-- `H_M(c(b⋆+t), Δ, d)`, a rational function of `Δ` over the field of germs. -/
noncomputable def HgermC (b : ℂ) (M : ℕ) : RatFunc Kd⸨X⸩ :=
  Hrat (kacC (bGerm (bsC b))) (HahnSeries.C dvar) M

open Classical in
/-- The colliding group `G^{(M)}_μ = ∑_{g ∈ C⋆_{μ,M}} R_g H_{M-ℓ_g}(c(b), z_g(b), d)/(Δ - h_g(b))`,
with `H_{M-ℓ_g}(c(b), z_g(b), d) = S_{g,M-ℓ_g}` (Lemma 7.8), so that the numerator is
`B_{g,M}`. -/
noncomputable def groupC (b : ℂ) (M : ℕ) (mu : ℂ) : RatFunc Kd⸨X⸩ :=
  ∑ g ∈ collClass M b mu,
    RatFunc.C (BG (bsC b) dvar M g) / (RatFunc.X - RatFunc.C (hG (bsC b) g))

/-- `Reg^{(M)}_μ = H_M(c(b), Δ, d) - G^{(M)}_μ` (before Lemma 7.11). -/
noncomputable def regC (b : ℂ) (M : ℕ) (mu : ℂ) : RatFunc Kd⸨X⸩ :=
  HgermC b M - groupC b M mu

/-- The right side of (7.8), with the series over `j` cut at `J`. -/
noncomputable def fixedChargeRHS (b : ℂ) (N : ℕ) (lam : ℂ) (k J : ℕ) : Kd :=
  (chainFnC b lam N k 0).coeff 0 +
    ∑ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
      (chainFnC b lam n k j).coeff 0 *
        ((j.factorial : Kd) * lcoeff (HN (kacC b) (N - n)) (pt (lam + n)) j)

/-- Lemma 7.8 (`lem:full-moments`).  For `b⋆ ≠ 0`: `S_{a,M}(t)` is the germ of
`H_M(c(b), z_a(b), d)`; and for `N ≥ 1`, `λ ∈ Kac_N(b⋆)`, `k ≥ 1` the full moment `C_{λ,k,N}`
is regular at `t = 0` with value `A⋆_{λ,k,N}`. -/
def Stmt_lem_full_moments : Prop :=
  ∀ b : ℂ, b ≠ 0 →
    (∀ (M : ℕ) (a : Label), 0 < a.1 → 0 < a.2 →
      SG (bsC b) dvar M a = RatFunc.eval (RingHom.id _) (zG (bsC b) a) (HgermC b M)) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k →
      (0 : WithTop ℤ) ≤ (fullMomentC b N lam k).orderTop ∧ (fullMomentC b N lam k).coeff 0 = Astar b N lam k

/-- Lemma 7.10 (`lem:cutting`).  For `j ≥ 1`,
`j c^{(k)}_{λ→μ,j} = c^{(k+1)}_{λ→μ,j-1} - ∑_ν c^{(k)}_{λ→ν,0} c^{(1)}_{ν→μ,j-1}`, the sum over
`ν = λ + 1, …, μ - 1`; here `μ = λ + D`. -/
def Stmt_lem_cutting : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ (lam : ℂ) (D k j : ℕ), 1 ≤ D → 1 ≤ k → 1 ≤ j →
    (j : Kd⸨X⸩) * chainFnC b lam D k j =
      chainFnC b lam D (k + 1) (j - 1) -
        ∑ n ∈ Finset.Ioo 0 D, chainFnC b lam n k 0 * chainFnC b (lam + n) (D - n) 1 (j - 1)

open Classical in
/-- Lemma 7.11 (`lem:regular-remainder`).  For `b⋆ ≠ 0`, `M ≥ 1` and `μ ∈ ℂ`: the remainder
`Reg^{(M)}_μ` is the sum of the other collision groups (proof of the lemma); it has no pole on the
line `b = b⋆` near `Δ = μ` and satisfies (7.6): as a rational function of `Δ` over the germs it is
a quotient `P/E` of polynomials in `Δ` whose coefficients are power series in `t`, with
`E(0, μ) ≠ 0`, and its restriction `P(0,·)/E(0,·)` to `t = 0` is
`H_M(c⋆,·) - PP_{Δ=μ} H_M(c⋆,·)`.  Consequently its Taylor coefficients
`∂_Δ^j Reg^{(M)}_μ(b, μ) = j! [(Δ-μ)^j] Reg^{(M)}_μ` are the germs `φ^{(M)}_{μ,j}` (`phiRemC`),
regular at `b⋆` with the values of `H_M(c⋆,·) - PP_{Δ=μ} H_M(c⋆,·)`.  Here `d` is indeterminate
and "near `Δ = μ`" refers to the variable `Δ`. -/
def Stmt_lem_regular_remainder : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ M : ℕ, 1 ≤ M → ∀ mu : ℂ,
    regC b M mu =
      (∑ g ∈ (labels M).filter (fun g => kacHL g b ≠ mu),
        RatFunc.C (BG (bsC b) dvar M g) / (RatFunc.X - RatFunc.C (hG (bsC b) g))) ∧
    (∃ P E : Polynomial (PowerSeries Kd),
      (E.map (PowerSeries.constantCoeff : PowerSeries Kd →+* Kd)).eval (pt mu) ≠ 0 ∧
      regC b M mu =
        algebraMap (Polynomial Kd⸨X⸩) (RatFunc Kd⸨X⸩) (P.map (HahnSeries.ofPowerSeries ℤ Kd)) /
          algebraMap (Polynomial Kd⸨X⸩) (RatFunc Kd⸨X⸩) (E.map (HahnSeries.ofPowerSeries ℤ Kd)) ∧
      HN (kacC b) M - PP (HN (kacC b) M) (pt mu) =
        algebraMap (Polynomial Kd) (RatFunc Kd)
            (P.map (PowerSeries.constantCoeff : PowerSeries Kd →+* Kd)) /
          algebraMap (Polynomial Kd) (RatFunc Kd)
            (E.map (PowerSeries.constantCoeff : PowerSeries Kd →+* Kd))) ∧
    ∀ j : ℕ,
      phiRemC b M mu j = (j.factorial : Kd⸨X⸩) * lcoeff (regC b M mu) (HahnSeries.C (pt mu)) j ∧
      (0 : WithTop ℤ) ≤ (phiRemC b M mu j).orderTop ∧
      (phiRemC b M mu j).coeff 0 = (j.factorial : Kd) * lcoeff (HN (kacC b) M) (pt mu) j

/-- Lemma 7.12 (`lem:chain-expansion`).  Equation (7.7): for each end point `μ = λ + n`,
`0 < n < N`, the series `∑_j c^{(k)}_{λ→μ,j} φ^{(N-n)}_{μ,j}` converges `t`-adically, and
`C_{λ,k,N} = c^{(k)}_{λ→λ+N,0} + ∑_{0<n<N} ∑_j c^{(k)}_{λ→λ+n,j} φ^{(N-n)}_{λ+n,j}`. -/
def Stmt_lem_chain_expansion : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N → ∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k →
    (∀ n ∈ Finset.Ioo 0 N, ∀ m : ℤ, ∃ J₀ : ℕ, ∀ J₁ J₂ : ℕ, J₀ ≤ J₁ →
      (m : WithTop ℤ) ≤ (∑ j ∈ Finset.Ico J₁ J₂,
        chainFnC b lam n k j * phiRemC b (N - n) (lam + n) j).orderTop) ∧
    (∀ m : ℤ, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      (m : WithTop ℤ) ≤ (fullMomentC b N lam k -
        (chainFnC b lam N k 0 +
          ∑ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
            chainFnC b lam n k j * phiRemC b (N - n) (lam + n) j)).orderTop)

/-- Lemma 7.13 (`lem:chain-regular`).  Every chain function is regular at `b = b⋆`. -/
def Stmt_lem_chain_regular : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ (lam : ℂ) (D k j : ℕ), 1 ≤ D → 1 ≤ k → (0 : WithTop ℤ) ≤ (chainFnC b lam D k j).orderTop

/-- Theorem 7.14 (`thm:fixed-charge`).  For `b⋆ ≠ 0` and `N ≥ 1`: at every `λ ∈ Kac_N(b⋆)` and
`k ≥ 1`, (7.8) has finitely many nonzero terms (for each end point `λ + n`, `0 < n < N`, the values
`c^{(k)}_{λ→λ+n,j}(b⋆)` vanish for `j` large) and holds (the cut at `J` is exact for `J` large);
`H_N(c⋆,·)` is the sum of its principal parts over `Kac_N(b⋆)`; and the chain functions are
regular at `b⋆`, so no term of (7.8) has a pole there.  The coefficients do not depend on `N`
(`chainFnC` has no level argument besides the level of the chains), and (7.8) uses `H_M` at the
levels `M = N - n < N` only. -/
def Stmt_thm_fixed_charge : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
    (∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k →
      (∀ n ∈ Finset.Ioo 0 N, ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j → (chainFnC b lam n k j).coeff 0 = 0) ∧
      ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → Astar b N lam k = fixedChargeRHS b N lam k J) ∧
    HN (kacC b) N = ∑ lam ∈ Lam N b, PP (HN (kacC b) N) (pt lam) ∧
    (∀ (lam : ℂ) (D k j : ℕ), 1 ≤ D → 1 ≤ k → (0 : WithTop ℤ) ≤ (chainFnC b lam D k j).orderTop)

/-- Corollary 7.15 (`cor:fixed-charge-generic`).  If `b⋆² ∉ ℚ`, the right side of (7.8) is the
coefficient of `(Δ - λ)^{-k}` of the generic recursion (Proposition 6.4) at `b = b⋆`:
`∑_{a ∈ C⋆_{λ,N}} R_a(b⋆) H_{N-ℓ_a}(c⋆, z_a(b⋆), d)` for `k = 1`, and `0` for `k ≥ 2`. -/
def Stmt_cor_fixed_charge_generic : Prop :=
  ∀ b : ℂ, b ≠ 0 → (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) → ∀ N : ℕ, 1 ≤ N →
    ∀ lam ∈ Lam N b, ∀ k : ℕ, 1 ≤ k → ∀ J : ℕ, 1 ≤ J →
      fixedChargeRHS b N lam k J =
        if k = 1 then
          ∑ a ∈ collClass N b lam,
            genR a.1 a.2 (bsC b) dvar *
              RatFunc.eval (RingHom.id Kd) (pt (kacHL a b + (a.lvl : ℂ))) (HN (kacC b) (N - a.lvl))
        else 0

end Virasoro
