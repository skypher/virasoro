import Virasoro.Statements.AppA20261125
import Virasoro.Proofs.Sec6H13DegRed
import Virasoro.Proofs.Sec6H13TFinal
import Virasoro.Proofs.AppABridge

/-!
# Lemma A.3 of `paper.tex` (`lem:level-poly`, l.3001–3009)

`R_M = (M!/2^M) Y^M F_M(c(b),Y/t²,−2/t+ζ)` in `ℚ[Y,Y⁻¹][[t]]` is `Rfam`.  Its product with
`det G̃_M` is the image of `(M!/2^M) Y^M ∑ adj(G̃_M) ρ̃_M` (`iM_numS`), and the same polynomial
is `(M!/2^M) Y^M F_M · det G̃_M` in `ℚ(t)(Δ)` (`Frat_psi`).  As in the proof in the paper
(l.3010–3102), the notation is that of Lemma A.1: `G̃ = D₀ + tG₁` (`lem_mode_count`, through
`GsM_ev0_of_modeCount`) makes `det G̃_M` a unit of `ℚ[Y,Y⁻¹][[t]]` (`isUnit_det_GL_of`) and gives
the expansion `R_M = (M!/2^M) Y^M ∑_r (−t)^r Tr(D₀⁻¹(G₁D₀⁻¹)^r ρ̃)`, of which only `0 ≤ r ≤ i`
contribute to `[t^i Y^j]` (`cf_Rfam_eq_of`).  The degree bound for each term is
`H13T.sub_h13_degree_chain`.
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

/-! ### `G̃ = D₀ + tG₁` over `ℚ[Y,Y⁻¹][[t]]`, from Lemma A.1 -/

section ModeCount

variable (hG : ∀ n : ℕ, (GsM n).map ev0 = Matrix.diagonal fun Y : Nat.Partition n => D0 Y)
include hG

/-- `G̃(0,Y) = D₀(Y)` in `ℚ[Y,Y⁻¹]`. -/
theorem cc_GL_of (n : ℕ) (Y Y' : Nat.Partition n) :
    PowerSeries.constantCoeff (Gser n Y Y') =
      if Y = Y' then ((topNat Y.word Y.word : ℕ) : LQ) * LaurentPolynomial.T Y.word.length
      else 0 := by
  have h := congrFun (congrFun (hG n) Y) Y'
  rw [Matrix.map_apply] at h
  have h2 : PowerSeries.constantCoeff (Gser n Y Y') = Polynomial.toLaurent (ev0 (GsM n Y Y')) :=
    cc_iM _
  rw [h2, h, Matrix.diagonal_apply]
  split_ifs
  · rw [D0, map_mul, map_natCast, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.T_pow,
      mul_one]
  · rw [map_zero]

/-- `det G̃_n` is a unit of `ℚ[Y,Y⁻¹][[t]]`. -/
theorem isUnit_det_GL_of (n : ℕ) : IsUnit (Gser n).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have h : (PowerSeries.constantCoeff (R := LQ)).mapMatrix (Gser n) =
      Matrix.diagonal fun Y : Nat.Partition n =>
        ((topNat Y.word Y.word : ℕ) : LQ) * LaurentPolynomial.T Y.word.length := by
    ext Y Y'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, cc_GL_of hG, Matrix.diagonal_apply]
  rw [h, Matrix.det_diagonal]
  refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one fun Y _ => ?_
  refine IsUnit.mul ?_ (LaurentPolynomial.isUnit_T _)
  rw [← map_natCast (LaurentPolynomial.C (R := ℚ))]
  exact IsUnit.map _ (IsUnit.mk0 _ (topNat_word_ne Y))

/-- `t` divides `tG₁D₀⁻¹ = G̃D₀⁻¹ − 1` entrywise. -/
theorem Em_dvd_of (n : ℕ) (Y Y' : Nat.Partition n) : (PowerSeries.X : LS) ∣ Em n Y Y' := by
  rw [PowerSeries.X_dvd_iff, Em, Matrix.sub_apply, D0i, Matrix.mul_diagonal, map_sub, map_mul,
    cc_GL_of hG, Matrix.one_apply]
  by_cases h : Y = Y'
  · subst h
    have hK : (topNat Y.word Y.word : ℚ) ≠ 0 := topNat_word_ne Y
    have e1 : PowerSeries.constantCoeff
        (cQ (1 / (topNat Y.word Y.word : ℚ)) * Yp (-(Y.word.length : ℤ))) =
        LaurentPolynomial.C (1 / (topNat Y.word Y.word : ℚ)) *
          LaurentPolynomial.T (-(Y.word.length : ℤ)) := by
      simp [cQ, Yp]
    have e2 : ((topNat Y.word Y.word : ℕ) : LQ) =
        LaurentPolynomial.C (topNat Y.word Y.word : ℚ) := (map_natCast _ _).symm
    have e3 : (LaurentPolynomial.T (Y.word.length : ℤ) : LQ) *
        LaurentPolynomial.T (-(Y.word.length : ℤ)) = 1 := by
      rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
    have e4 : (LaurentPolynomial.C (topNat Y.word Y.word : ℚ) : LQ) *
        LaurentPolynomial.C (1 / (topNat Y.word Y.word : ℚ)) = 1 := by
      rw [← map_mul, mul_one_div_cancel hK, map_one]
    rw [if_pos rfl, if_pos rfl, map_one, e1, e2]
    linear_combination (-1 : LQ) * e3 -
      (LaurentPolynomial.T (Y.word.length : ℤ) * LaurentPolynomial.T (-(Y.word.length : ℤ))) * e4
  · rw [if_neg h, if_neg h, zero_mul, map_zero, sub_zero]

theorem pow_Em_dvd_of (n r : ℕ) :
    ∀ Y Y' : Nat.Partition n, (PowerSeries.X : LS) ^ r ∣ (Em n ^ r) Y Y' := by
  induction r with
  | zero => intro Y Y'; rw [pow_zero]; exact one_dvd _
  | succ r ih =>
    intro Y Y'
    rw [pow_succ, pow_succ, Matrix.mul_apply]
    exact Finset.dvd_sum fun Z _ => mul_dvd_mul (ih Y Z) (Em_dvd_of hG n Z Y')

/-- `G̃⁻¹ = D₀⁻¹ ∑_{r ≤ i} (−tG₁D₀⁻¹)^r + G̃⁻¹(−tG₁D₀⁻¹)^{i+1}`. -/
theorem neumann_of (n i : ℕ) :
    (Gser n)⁻¹ = D0i n * ∑ r ∈ Finset.range (i + 1), Em n ^ r + (Gser n)⁻¹ * Em n ^ (i + 1) := by
  have h1 : Gser n * D0i n = 1 - Em n := by
    rw [Em]
    abel
  have h2 : (1 - Em n) * ∑ r ∈ Finset.range (i + 1), Em n ^ r = 1 - Em n ^ (i + 1) :=
    mul_neg_geom_sum (Em n) (i + 1)
  have h3 : (Gser n)⁻¹ * Gser n = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_GL_of hG n)
  have h4 : (Gser n)⁻¹ * (Gser n * D0i n * ∑ r ∈ Finset.range (i + 1), Em n ^ r) =
      D0i n * ∑ r ∈ Finset.range (i + 1), Em n ^ r := by
    rw [mul_assoc, ← mul_assoc, h3, one_mul]
  rw [← h4, h1, h2]
  noncomm_ring

/-- Only the terms `0 ≤ r ≤ i` of the expansion contribute to `[t^i Y^j] R_n`
(paper.tex l.3011–3016). -/
theorem cf_Rfam_eq_of (ν : Fin 2) (n i : ℕ) (j : ℤ) :
    cf (Rfam ν n) i j = ∑ r ∈ Finset.range (i + 1), cf (Tfam ν r n) i j := by
  have hdec : Rfam ν n = ∑ r ∈ Finset.range (i + 1), Tfam ν r n +
      cQ ((n.factorial : ℚ) / 2 ^ n) * Yp n * trR ν n ((Gser n)⁻¹ * Em n ^ (i + 1)) := by
    rw [Rfam, Fhat]
    conv_lhs => rw [neumann_of hG n i]
    rw [trR_add, Matrix.mul_sum, trR_sum, mul_add, Finset.mul_sum]
    rfl
  have hdvd : (PowerSeries.X : LS) ^ (i + 1) ∣
      cQ ((n.factorial : ℚ) / 2 ^ n) * Yp n * trR ν n ((Gser n)⁻¹ * Em n ^ (i + 1)) := by
    refine Dvd.dvd.mul_left ?_ _
    refine Finset.dvd_sum fun Y _ => Finset.dvd_sum fun Y' _ => Dvd.dvd.mul_right ?_ _
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun Z _ => Dvd.dvd.mul_left (pow_Em_dvd_of hG n (i + 1) Z Y') _
  rw [hdec, cf_add, cf_sum, cf_of_dvd hdvd (Nat.lt_succ_self i), add_zero]

end ModeCount

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
    exact isUnit_det_GL_of (GsM_ev0_of_modeCount lem_mode_count) M
  · rw [tyToSer_thetaMv, tyToSer_thetaMv, iM_det, map_mul, map_mul, map_pow, iM_CC, iM_X,
      iM_numS, Rfam, Yp_pow]
    simp only [mul_one]
    ring

/-- Lemma A.3 (paper.tex l.3001–3009).
Paper label: lem:level-poly -/
theorem lem_level_poly : Stmt_lem_level_poly := by
  intro ν
  refine ⟨Rfam ν, isTExpansion_Rfam ν, fun i j => ?_⟩
  exact (PolyDeg.sum _ fun r _ => H13T.sub_h13_degree_chain ν r i j).congr
    fun M => cf_Rfam_eq_of (GsM_ev0_of_modeCount lem_mode_count) ν M i j

end Virasoro
