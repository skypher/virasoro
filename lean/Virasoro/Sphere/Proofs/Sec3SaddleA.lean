import Virasoro.Sphere.Proofs.Sec3WHSaddle

/-!
# Sphere paper Lemma 3.4(iii): the recursion for `a_m(z)` (`sphere/paper.tex` l.725–728)

`a_m = ₂F₁⁻¹ ∑_l h_{m+l} h_l z^l` satisfies `a_m = h_m - ∑_{n≥1} (B_{m,n}/n) z^n a_n`,
coefficient by coefficient in `z` (the saddle-point equations, from (3.6)).

Consumer: the saddle-point claim in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset PowerSeries

/-- `∑_l h_{m+l} h_l z^l`, the numerator of `a_m(z)`. -/
noncomputable def Nser (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun l => halfBinom (m + l) * halfBinom l

theorem hyp2F1_eq : hyp2F1 = PowerSeries.mk fun n => halfBinom n ^ 2 := by
  ext n
  rw [hyp2F1, coeff_mk, coeff_mk, halfBinom_eq]

theorem hyp2F1_unit : PowerSeries.constantCoeff hyp2F1 ≠ 0 := by
  rw [constantCoeff_hyp2F1]
  exact one_ne_zero

theorem aSer_mul (m : ℕ) : aSer m * hyp2F1 = Nser m := by
  rw [aSer, OmegaCoef, mul_assoc, PowerSeries.inv_mul_cancel _ hyp2F1_unit, mul_one]
  ext l
  have h1 : (0 : ℤ) ≤ (m : ℤ) + (l : ℤ) := by positivity
  have h2 : ((m : ℤ) + (l : ℤ)).toNat = m + l := by omega
  rw [coeff_mk, Nser, coeff_mk, if_pos h1, h2]

/-- `[z^K]a_m = h_m δ_{K,0} - ∑_{n=1}^K (B_{m,n}/n) [z^{K-n}]a_n`: the saddle-point equations,
from part (ii), the Wiener–Hopf identity (3.6) and the change of variables `p = p(w)`
(`Sec3WHSaddle.lean`). -/
theorem coeff_aSer (m K : ℕ) :
    coeff K (aSer m) = (if K = 0 then halfBinom m else 0) -
      ∑ n ∈ Icc 1 K, Bcoef m n / (n : ℚ) * coeff (K - n) (aSer n) :=
  coeff_aSer_WH m K

end Virasoro.Sphere
