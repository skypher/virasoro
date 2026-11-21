import Virasoro.Sphere.Proofs.Sec3BergmanLaurent
import Virasoro.Sphere.Proofs.Sec3BergmanIds
import Virasoro.Sphere.Proofs.Sec3BergmanF1

/-!
# Sphere paper Lemma 3.5 from the three steps of its proof (`sphere/paper.tex` l.825–970)

`Stmt_lem_bergman_det` from the cited identity `₂F₁(z(q)) = θ₃(q)²` and the sub-statements
`Stmt_sub_bergman_liouville`, `Stmt_sub_bergman_zero_mode`, `Stmt_sub_bergman_residue`.  The
convergence clause of `IsWFormula` is `summable_WnoTerm`.

Consumer: `Stmt_lem_bergman_det`.
-/

namespace Virasoro.Sphere

open PowerSeries

/-- The convergence clause of `IsWFormula` holds for every `C(z)` (sphere/paper.tex l.878–880). -/
theorem isWFormula_of_eq {Cz : PowerSeries ℂ}
    (h : ∀ x1 x2 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → 0 < ‖x2‖ → ‖x2‖ < 1 → x1 ≠ x2 →
      Wser x1 x2 = YYinv x1 x2 * (C (((x1 - x2) ^ 2)⁻¹) * Sser x1 x2 + 2 * Cz)) :
    IsWFormula Cz :=
  fun x1 x2 h1 h1' h2 h2' hne => ⟨fun j => summable_WnoTerm j h1' h2', h x1 x2 h1 h1' h2 h2' hne⟩

/-- Lemma 3.5 from the cited Jacobi identity and the three sub-statements of its proof. -/
theorem lem_bergman_det_of_steps (hJ2 : Cited_JacobiIdentities2)
    (hL : Stmt_sub_bergman_liouville) (hZ : Stmt_sub_bergman_zero_mode)
    (hR : Stmt_sub_bergman_residue) : Stmt_lem_bergman_det :=
  lem_bergman_det_of_trace hJ2 (bergman_trace_of_steps hL hZ hR)

end Virasoro.Sphere
