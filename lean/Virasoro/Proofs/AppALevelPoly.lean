import Virasoro.Statements.AppA20261125
import Virasoro.Proofs.Sec6H13DegRed
import Virasoro.Proofs.Sec6H13TFinal

/-!
# Lemma A.3 of `paper.tex` (`lem:level-poly`, l.3001–3009)

`R_M = (M!/2^M) Y^M F_M(c(b),Y/t²,−2/t+ζ)` in `ℚ[Y,Y⁻¹][[t]]` is `Rfam`.  Its product with
`det G̃_M` is the image of `(M!/2^M) Y^M ∑ adj(G̃_M) ρ̃_M` (`iM_numS`), and the same polynomial
is `(M!/2^M) Y^M F_M · det G̃_M` in `ℚ(t)(Δ)` (`Frat_psi`); `det G̃_M` is a unit of
`ℚ[Y,Y⁻¹][[t]]` because `G̃_M(0,Y) = D₀(Y)` (`isUnit_det_GL`).  The degree bound for
`[t^i Y^j] R_M` is the expansion `R_M = (M!/2^M) Y^M ∑_r (−t)^r Tr(D₀⁻¹(G₁D₀⁻¹)^r ρ̃)` with the
degree bound for each term (`degFam_R_of_chain`, `sub_h13_degree_chain`), as in the proof in
the paper.
-/

namespace Virasoro

open Polynomial H13D

theorem psi_CC (q : ℚ) : psi (C (C q)) = (q : RatFunc (RatFunc ℚ)) :=
  RingHom.congr_fun (RingHom.ext_rat ((psi.comp C).comp C) (Rat.castHom _)) q

theorem psi_X_eq : psi X = RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X := by
  rw [← aeval_thetaMv]
  simp [thetaMv]

theorem tyToRat_thetaMv (P : PS) : tyToRat (thetaMv P) = psi P := aeval_thetaMv P

theorem tyToSer_thetaMv (P : PS) : tyToSer (thetaMv P) = iM P := by
  have h : ((tyToSer : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] SerTY) :
      MvPolynomial (Fin 2) ℚ →+* SerTY).comp thetaMv = iM :=
    PS_ringHom_ext _ _ (by rw [iM_tS]; simp [thetaMv, tS, tyToSer])
      (by simp [thetaMv, tyToSer, iM_X, Yp])
  exact RingHom.congr_fun h P

theorem GsM_det_ne_zero (M : ℕ) : (GsM M).det ≠ 0 := by
  intro h
  have h1 := psi1_det M
  rw [h, map_zero] at h1
  exact mul_ne_zero (pow_ne_zero 2 (tauL_ne_zero M))
    (gramPoly_det_ne_zero (cT (RatFunc.X : RatFunc ℚ)) M) h1.symm

/-- `R_M` is the expansion in `t` of `(M!/2^M) Y^M F_M` at `Δ = Y/t²` (paper.tex l.3003–3005). -/
theorem isTExpansion_Rfam (ν : Fin 2) (M : ℕ) : IsTExpansion (appRrat ν M) (Rfam ν M) := by
  refine ⟨thetaMv (C (C ((M.factorial : ℚ) / 2 ^ M)) * X ^ M * numS ν M), thetaMv (GsM M).det,
    ?_, ?_, ?_, ?_⟩
  · rw [tyToRat_thetaMv]
    intro h
    exact GsM_det_ne_zero M (psi_injective (h.trans (map_zero psi).symm))
  · rw [tyToRat_thetaMv, tyToRat_thetaMv, map_mul, map_mul, map_pow, psi_CC, psi_X_eq,
      ← Frat_psi]
    simp only [appRrat, d13]
    push_cast
    ring
  · rw [tyToSer_thetaMv, iM_det]
    exact isUnit_det_GL M
  · rw [tyToSer_thetaMv, tyToSer_thetaMv, iM_det, map_mul, map_mul, map_pow, iM_CC, iM_X,
      iM_numS, Rfam, Yp_pow]
    simp only [mul_one]
    ring

/-- Lemma A.3 (paper.tex l.3001–3009).
Paper label: lem:level-poly -/
theorem lem_level_poly : Stmt_lem_level_poly := by
  intro ν
  refine ⟨Rfam ν, isTExpansion_Rfam ν, fun i j => ?_⟩
  exact degFam_R_of_chain H13T.sub_h13_degree_chain ν i j

end Virasoro
