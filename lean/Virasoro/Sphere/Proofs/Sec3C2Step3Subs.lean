import Virasoro.Sphere.Proofs.Sec3C2Steps
import Virasoro.Sphere.Proofs.Sec3GaussExp

/-!
# Lemma 3.7, Step 3: frozen sub-statements (sphere paper)

sphere/paper.tex l.1111–1156.  `Stmt_sub_c2_diag` (l.1111–1149):
`U(W_*)^† F_2 = exp(-∑_m (m/16^m) u_m²)`.  `Stmt_sub_c2_diag_norm` (l.1150–1156): the level-`n`
Fock norms of that Gaussian.  Together they give `Stmt_sub_c2_step3`.
-/

namespace Virasoro.Sphere

open MvPolynomial PowerSeries

/-- The level-`n` part of `exp(-∑_{m≥1} (m/16^m) u_m²)` (sphere/paper.tex l.1148). -/
noncomputable def diagF (n : ℕ) : Fock :=
  ∑ α ∈ (finite_level n).toFinset, monomial α (MvPowerSeries.coeff α (mexp diagExpo))

/-- Lemma 3.7, Step 3, first part (sphere/paper.tex l.1111–1149): for every `U(W)` with
`(D_k + l_k^{(2)})U(W) = 0`, `U(0) = id`,
`U(W_*)^† F_2(u) = exp(-∑_{m≥1} (m/16^m) u_m²)`.

Demand sheet.
- every `U` with `IsDiffeoU`;
- level by level: `(U(W_*)^† F_2)_n` is `UdagF U n`, the right side `diagF n`. -/
def Stmt_sub_c2_diag : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U → ∀ n : ℕ, UdagF U n = diagF n

/-- Lemma 3.7, Step 3, second part (sphere/paper.tex l.1150–1156): the level-`n` Fock norms
of `exp(-∑_m (m/16^m) u_m²)` have the generating function
`∑_n 16^n ‖·‖_n² q^n = ∏_m (1 - q^{2m})^{-1/2}`.

Demand sheet.
- without the fractional power, as in `Stmt_sub_c2_step3`. -/
def Stmt_sub_c2_diag_norm : Prop :=
  (mk fun n => (16 : ℂ) ^ n * fockForm (diagF n) (diagF n)) ^ 2 *
    (etaSqPow 1).map (algebraMap ℚ ℂ) = 1

theorem sub_c2_step3_of (h1 : Stmt_sub_c2_diag) (h2 : Stmt_sub_c2_diag_norm) :
    Stmt_sub_c2_step3 := by
  intro U hU
  have e : (mk fun n => (16 : ℂ) ^ n * fockForm (UdagF U n) (UdagF U n)) =
      mk fun n => (16 : ℂ) ^ n * fockForm (diagF n) (diagF n) := by
    ext n
    rw [coeff_mk, coeff_mk, h1 U hU n]
  rw [e]
  exact h2

end Virasoro.Sphere
