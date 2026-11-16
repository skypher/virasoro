import Virasoro.Statements.Prelude
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Frozen statements: Section 11 (Irreducible Ising specialization)
-/

namespace Virasoro

open Polynomial

/-- Proposition 11.1 (`prop:identity-verma`): for `d = 0`, `H_Δ^{(1/2)}(0|q) = 1` as a rational
function of `Δ`, i.e. `H₀(1/2,Δ,0) = 1` and `H_N(1/2,Δ,0) = 0` for `N ≥ 1`. -/
def Stmt_prop_identity_verma : Prop :=
  Hrat (1 / 2 : ℂ) 0 0 = 1 ∧ ∀ N : ℕ, 1 ≤ N → Hrat (1 / 2 : ℂ) 0 N = 0

/-- The coefficient of `q^N` in the eta-reduced irreducible identity block
`Ĥ_h(q) = ∏_{m≥1}(1-q^m) ∑_{N≥0} dim L(1/2,h)_{h+N} q^N` (paper Definition 11.2).  The level-`N`
space of the irreducible quotient `L(1/2,h) = M(1/2,h)/rad` has dimension `rank G_N(1/2,h)`. -/
noncomputable def hatH (h : ℂ) (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1), eta j * ((gram (1 / 2 : ℂ) h (N - j)).rank : ℤ)

/-- The coefficient of `q^N` in `∑_{j∈ℤ} (q^{e₁(j)} - q^{e₂(j)})`, for exponent functions with
`|j| ≤ e_i(j)`: the number of `j ∈ [-N, N]` with `e₁(j) = N` minus the number with
`e₂(j) = N` (the index `j` is written `i - N` with `0 ≤ i ≤ 2N`). -/
def thetaCoeff (e₁ e₂ : ℤ → ℤ) (N : ℕ) : ℤ :=
  (((Finset.range (2 * N + 1)).filter fun i : ℕ => e₁ ((i : ℤ) - (N : ℤ)) = (N : ℤ)).card : ℤ) -
    (((Finset.range (2 * N + 1)).filter fun i : ℕ => e₂ ((i : ℤ) - (N : ℤ)) = (N : ℤ)).card : ℤ)

/-- Theorem 11.3 (`thm:ising-characters`).
`Ĥ_0(q) = ∑_j (q^{((24j+1)²-1)/48} - q^{((24j+7)²-1)/48})`,
`Ĥ_{1/2}(q) = ∑_j (q^{((24j+5)²-25)/48} - q^{((24j+11)²-25)/48})`,
`Ĥ_{1/16}(q) = ∑_j (q^{((24j-2)²-4)/48} - q^{((24j+10)²-4)/48})`, with beginnings
`Ĥ_0 = 1 - q - q⁶ + q¹¹ + q¹³ - q²⁰ + ⋯`,
`Ĥ_{1/2} = 1 - q² - q³ + q⁷ + q¹⁷ - q²⁵ - q²⁸ + ⋯`,
`Ĥ_{1/16} = 1 - q² - q⁴ + q¹⁰ + q¹⁴ - q²⁴ - q³⁰ + ⋯`.
The exponents are written with the division carried out:
`((24j+1)²-1)/48 = 12j²+j`, `((24j+7)²-1)/48 = 12j²+7j+1`, `((24j+5)²-25)/48 = 12j²+5j`,
`((24j+11)²-25)/48 = 12j²+11j+2`, `((24j-2)²-4)/48 = 12j²-2j`,
`((24j+10)²-4)/48 = 12j²+10j+2`.  The beginnings are the coefficients up to the last displayed
power of `q`. -/
def Stmt_thm_ising_characters : Prop :=
  (∀ N : ℕ, hatH 0 N =
    thetaCoeff (fun j => 12 * j ^ 2 + j) (fun j => 12 * j ^ 2 + 7 * j + 1) N) ∧
  (∀ N : ℕ, hatH (1 / 2) N =
    thetaCoeff (fun j => 12 * j ^ 2 + 5 * j) (fun j => 12 * j ^ 2 + 11 * j + 2) N) ∧
  (∀ N : ℕ, hatH (1 / 16) N =
    thetaCoeff (fun j => 12 * j ^ 2 - 2 * j) (fun j => 12 * j ^ 2 + 10 * j + 2) N) ∧
  (∀ N : ℕ, N ≤ 20 → hatH 0 N =
    if N = 0 ∨ N = 11 ∨ N = 13 then 1 else if N = 1 ∨ N = 6 ∨ N = 20 then -1 else 0) ∧
  (∀ N : ℕ, N ≤ 28 → hatH (1 / 2) N =
    if N = 0 ∨ N = 7 ∨ N = 17 then 1
    else if N = 2 ∨ N = 3 ∨ N = 25 ∨ N = 28 then -1 else 0) ∧
  (∀ N : ℕ, N ≤ 30 → hatH (1 / 16) N =
    if N = 0 ∨ N = 10 ∨ N = 14 then 1
    else if N = 2 ∨ N = 4 ∨ N = 24 ∨ N = 30 then -1 else 0)

end Virasoro
