import Virasoro.Sphere.Fock
import Virasoro.Sphere.Statements.Sec2
import Virasoro.NormalOrder

/-!
# Frozen statement: sphere paper Lemma 3.2 (`lem:fock-verma`)

Awaiting statement review.  The operators (3.2) and the form (3.1) are in `Sphere/Fock.lean`;
the two facts the paper cites for them (Virasoro relations with `c = 1 + 24μ²`, and
`l_k† = l_{-k}` for real `μ, λ`) are `Cited_FeiginFuchsOperators` in `Sphere/Cited.lean`.
-/

namespace Virasoro.Sphere

open MvPolynomial

/-- The body of Theorem 3.1 (`Stmt_thm_large_delta`) at one level `N`: the limit
`lim_{Δ→∞} H_N(c,Δ,Δ_i) = δ_{N,0}` for all complex `(c,Δ_i)` and its equivalent degree form.
`Stmt_thm_large_delta` is `∀ N, LargeDeltaAt N` by definition. -/
def LargeDeltaAt (N : ℕ) : Prop :=
  (∀ (c : ℂ) (Δe : Fin 4 → ℂ),
    Filter.Tendsto (fun Δ : ℂ => RatFunc.eval (RingHom.id ℂ) Δ (Hsph c Δe N))
      (Bornology.cobounded ℂ) (nhds (if N = 0 then 1 else 0))) ∧
  ∃ Q : MvPolynomial (Fin 6) ℚ, ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
    ∃ P : Polynomial ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) P =
        MvPolynomial.aeval
          (![RatFunc.C c, RatFunc.X, RatFunc.C (Δe 0), RatFunc.C (Δe 1), RatFunc.C (Δe 2),
            RatFunc.C (Δe 3)] : Fin 6 → RatFunc ℂ) Q ∧
      Hsph c Δe N * algebraMap (Polynomial ℂ) (RatFunc ℂ) (gramPoly c N).det =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) P ∧
      (1 ≤ N → P.degree < (gramPoly c N).det.degree)

/-- Lemma 3.2 (`lem:fock-verma`), sphere/paper.tex l.446–470.  Fix `μ > 0`, real `Δ₁,…,Δ₄`
and `N ≥ 0`.
(i) For every `λ > 0`, `M(1+24μ², λ²+μ²)` is irreducible and isometric to `ℱ_{μ,λ}` via
`L_{-Y}v_Δ ↦ l_{-Y}1`.
(ii) There is a unique formal series `F = ∑_m F_m` (`F_m` of level `m`, `F_0 = 1`) with
`l_k F = (l_0 + kΔ₂ - Δ₁)F` for all `k ≥ 1`; with `F̃` obtained from `F` by `u ↦ ū`, `i ↦ -i`,
`(Δ₁,Δ₂) ↦ (Δ₄,Δ₃)`, `ℬ_N(1+24μ², λ²+μ², Δ_i) = ⟨F̃_N, F_N⟩`, the coefficients paired through
`∏_m α_m!/(2m)^{α_m}` with no second conjugation.
(iii) If `lim_{λ→+∞} H_N(1+24μ², λ²+μ², Δ_i) = δ_{N,0}` for all `μ > 0` and real `Δ_i`, then
Theorem 3.1 holds for all complex `(c, Δ_i)`.

Demand sheet.
- `μ > 0`, `λ > 0` real, `Δ_i` real (l.447, l.449, l.456); `c = 1 + 24μ²`, `Δ = λ² + μ²` as
  complex numbers;
- (i) irreducible: read as `det G_N(c,Δ) ≠ 0` for every `N`, which is what the paper's proof
  shows and what (ii) uses (l.473–482);
- (i) isometric: `⟨l_{-Y}1, l_{-Y'}1⟩ = ⟨L_{-Y}v, L_{-Y'}v⟩` for partitions `Y, Y'` of any two
  levels, the right side being the Shapovalov value `gramWord` (zero for different levels);
  and the map is a bijection level by level: every Fock vector of level `N` is a unique
  combination of the `l_{-Y}1`, `|Y| = N` (l.450–451, l.481–483);
- (ii) existence and uniqueness of the sequence `(F_m)` (`IsWardSeries`), for every `λ > 0`
  (l.452–455);
- (ii) `F̃_N`: the coefficients of the solution for `(Δ₄,Δ₃)` conjugated (`i ↦ -i` at real
  parameters); the pairing is the bilinear `fockBil`; `ℬ_N` is evaluated at `Δ = λ² + μ²`,
  where it is regular by (i) (l.455–461);
- (iii) per level `N` (the lemma fixes `N`, l.447): hypothesis for all `μ > 0` and all real
  `Δ_i` at that `N`, as a limit along `λ → +∞` of the values of the rational function `H_N` at
  `Δ = λ² + μ²` (regular there by (i)); conclusion: Theorem 3.1 at that `N` for all complex
  `(c, Δ_i)`, which is `LargeDeltaAt N` (l.462–465). -/
def Stmt_lem_fock_verma : Prop :=
  (∀ μ : ℝ, 0 < μ → ∀ lam : ℝ, 0 < lam →
    let c : ℂ := 1 + 24 * (μ : ℂ) ^ 2
    let Δ : ℂ := (lam : ℂ) ^ 2 + (μ : ℂ) ^ 2
    ((∀ N : ℕ, (gram c Δ N).det ≠ 0) ∧
      (∀ (N N' : ℕ) (Y : Nat.Partition N) (Y' : Nat.Partition N'),
        fockForm (fockWord (μ : ℂ) (lam : ℂ) Y.word) (fockWord (μ : ℂ) (lam : ℂ) Y'.word) =
          gramWord c Δ Y.word Y'.word) ∧
      (∀ (N : ℕ) (f : Fock), IsWeightedHomogeneous fockWeight f N →
        ∃! x : Nat.Partition N → ℂ, f = ∑ Y, x Y • fockWord (μ : ℂ) (lam : ℂ) Y.word)) ∧
    ∀ Δe : Fin 4 → ℝ,
      (∃! F : ℕ → Fock, IsWardSeries (μ : ℂ) (lam : ℂ) (Δe 0 : ℂ) (Δe 1 : ℂ) F) ∧
      ∀ F G : ℕ → Fock, IsWardSeries (μ : ℂ) (lam : ℂ) (Δe 0 : ℂ) (Δe 1 : ℂ) F →
        IsWardSeries (μ : ℂ) (lam : ℂ) (Δe 3 : ℂ) (Δe 2 : ℂ) G → ∀ N : ℕ,
          RatFunc.eval (RingHom.id ℂ) Δ (Bsph c (fun i => (Δe i : ℂ)) N) =
            fockBil (map (starRingEnd ℂ) (G N)) (F N)) ∧
  (∀ N : ℕ,
    (∀ μ : ℝ, 0 < μ → ∀ Δe : Fin 4 → ℝ,
      Filter.Tendsto
        (fun lam : ℝ => RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
          (Hsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) N))
        Filter.atTop (nhds (if N = 0 then 1 else 0))) →
    LargeDeltaAt N)

end Virasoro.Sphere
