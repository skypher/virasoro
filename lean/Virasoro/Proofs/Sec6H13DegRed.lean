import Virasoro.Proofs.Sec6H13DegSer
import Virasoro.Proofs.Sec6H13Final
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing

/-!
# Proposition 6.8(ii): reduction to the terms of the expansion in `t` (paper.tex l.1293–1306)

`P_M^{(ν)}/4^M = N_M · ∑_s η_s M(M−1)⋯(M−s+1) (Y/2)^s R_{M−s}` in `ℚ[Y,Y⁻¹][[t]]`, with
`N_M` the normalized product and `R_M = (M!/2^M) Y^M Tr(G̃⁻¹ρ̃)` (l.1299–1302); the expansion
`R_M = (M!/2^M) Y^M ∑_r (−t)^r Tr(D₀⁻¹(G₁D₀⁻¹)^r ρ̃)`, of which only `0 ≤ r ≤ i` contribute to
`[t^i Y^j]` (l.1304–1306).  Clause (ii) follows from the statement that each term of the expansion
has `[t^i Y^j]` polynomial in `M` of degree at most `2i + 2j` (`Stmt_sub_h13_degree_chain`,
l.1306–1378).
-/

namespace Virasoro.H13D

open Polynomial

/-- `G̃_n` over `ℚ[Y,Y⁻¹][[t]]`. -/
noncomputable def Gser (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) LS := (GsM n).map iM

/-- `ρ̃_n` at `d = d_ν` over `ℚ[Y,Y⁻¹][[t]]`. -/
noncomputable def RL (ν : Fin 2) (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) LS :=
  (RsM ν n).map iM

/-- `B ↦ ∑_{λ,λ'} B_{λ,λ'} ρ̃_{λ,λ'}`, the pairing of Definition 2.2 (`Frat`). -/
noncomputable def trR (ν : Fin 2) (n : ℕ) (B : Matrix (Nat.Partition n) (Nat.Partition n) LS) :
    LS :=
  ∑ Y, ∑ Y', B Y Y' * RL ν n Y Y'

theorem trR_zero (ν : Fin 2) (n : ℕ) : trR ν n 0 = 0 := by simp [trR]

theorem trR_add (ν : Fin 2) (n : ℕ) (A B : Matrix (Nat.Partition n) (Nat.Partition n) LS) :
    trR ν n (A + B) = trR ν n A + trR ν n B := by
  simp [trR, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem trR_sum (ν : Fin 2) (n : ℕ) {ι : Type*} (S : Finset ι)
    (A : ι → Matrix (Nat.Partition n) (Nat.Partition n) LS) :
    trR ν n (∑ a ∈ S, A a) = ∑ a ∈ S, trR ν n (A a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [trR_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, trR_add, ih]

/-- `F_n = Tr(G̃_n⁻¹ ρ̃_n)` in `ℚ[Y,Y⁻¹][[t]]`. -/
noncomputable def Fhat (ν : Fin 2) (n : ℕ) : LS := trR ν n (Gser n)⁻¹

/-- `R_n(t,Y) = (n!/2ⁿ) Yⁿ F_n(c(b), Y/t², −2/t + ζ)` (paper.tex l.1299–1300). -/
noncomputable def Rfam (ν : Fin 2) (n : ℕ) : LS :=
  cQ ((n.factorial : ℚ) / 2 ^ n) * Yp n * Fhat ν n

/-- `∑_s η_s M(M−1)⋯(M−s+1) (Y/2)^s R_{M−s}` (paper.tex l.1300–1301). -/
noncomputable def Sfam (ν : Fin 2) (M : ℕ) : LS :=
  ∑ s ∈ Finset.range (M + 1),
    cQ ((eta s : ℚ) * (M.descFactorial s : ℚ) / 2 ^ s) * Yp s * Rfam ν (M - s)

/-! ### `G̃` at `t = 0` -/

theorem cc_iM (p : PS) :
    PowerSeries.constantCoeff (iM p) = Polynomial.toLaurent (ev0 p) := by
  have h := PS_ringHom_ext ((PowerSeries.constantCoeff (R := LQ)).comp iM)
    ((Polynomial.toLaurent (R := ℚ)).comp ev0)
    (by simp [iM_tS, ev0_tS]) (by simp [iM_X, ev0_X, Yp])
  exact RingHom.congr_fun h p

theorem cc_GL (n : ℕ) (Y Y' : Nat.Partition n) :
    PowerSeries.constantCoeff (Gser n Y Y') =
      if Y = Y' then ((topNat Y.word Y.word : ℕ) : LQ) * LaurentPolynomial.T Y.word.length
      else 0 := by
  have h := congrFun (congrFun (GsM_ev0 n) Y) Y'
  rw [Matrix.map_apply] at h
  have h2 : PowerSeries.constantCoeff (Gser n Y Y') = Polynomial.toLaurent (ev0 (GsM n Y Y')) :=
    cc_iM _
  rw [h2, h, Matrix.diagonal_apply]
  split_ifs
  · rw [map_mul, map_natCast, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_one]
  · rw [map_zero]

theorem isUnit_det_GL (n : ℕ) : IsUnit (Gser n).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have h : (PowerSeries.constantCoeff (R := LQ)).mapMatrix (Gser n) =
      Matrix.diagonal fun Y : Nat.Partition n =>
        ((topNat Y.word Y.word : ℕ) : LQ) * LaurentPolynomial.T Y.word.length := by
    ext Y Y'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, cc_GL, Matrix.diagonal_apply]
  rw [h, Matrix.det_diagonal]
  refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one fun Y _ => ?_
  refine IsUnit.mul ?_ (LaurentPolynomial.isUnit_T _)
  rw [← map_natCast (LaurentPolynomial.C (R := ℚ))]
  exact IsUnit.map _ (IsUnit.mk0 _ (topNat_word_ne Y))

/-! ### The identity `P_M/4^M = N_M · ∑_s …` (l.1299–1302) -/

theorem iM_det (n : ℕ) : iM (GsM n).det = (Gser n).det := by
  rw [Gser, RingHom.map_det]
  rfl

theorem iM_numS (ν : Fin 2) (n : ℕ) : iM (numS ν n) = (Gser n).det * Fhat ν n := by
  have hadj : ((GsM n).adjugate).map iM = (Gser n).adjugate := RingHom.map_adjugate iM (GsM n)
  have hinv : (Gser n).adjugate = (Gser n).det • (Gser n)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ (isUnit_det_GL n), one_smul]
  rw [numS, map_sum, Fhat, trR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  have h1 : iM ((GsM n).adjugate Y Y') = (Gser n).det * (Gser n)⁻¹ Y Y' := by
    have h := congrFun (congrFun hadj Y) Y'
    rw [Matrix.map_apply, hinv, Matrix.smul_apply, smul_eq_mul] at h
    exact h
  rw [map_mul, h1, mul_assoc]
  rfl

theorem iM_Q {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) :
    iM Q = cQ (4 ^ M) * (Nfam M * Sfam ν M) := by
  have hk := congrArg iM (key_PS h)
  have hB : iM (Bden M) = ∏ j ∈ Finset.range (M + 1), (Gser (M - j)).det := by
    rw [Bden, map_prod]
    exact Finset.prod_congr rfl fun j _ => iM_det _
  have hA : iM (Anum ν M) = (∏ j ∈ Finset.range (M + 1), (Gser (M - j)).det) *
      ∑ j ∈ Finset.range (M + 1), (eta j : LS) * Fhat ν (M - j) := by
    rw [Anum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_mul, map_mul, map_intCast, iM_numS, map_prod,
      ← Finset.mul_prod_erase _ (fun i => (Gser (M - i)).det) hj]
    simp only [iM_det]
    ring
  have hU : IsUnit (∏ j ∈ Finset.range (M + 1), (Gser (M - j)).det) :=
    Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one fun j _ => isUnit_det_GL _
  rw [map_mul, map_mul, iM_prefS, hB, hA] at hk
  have hQ : iM Q = cQ (M.factorial : ℚ) * (cQ 2 * Yp 1) ^ M * Nfam M *
      ∑ j ∈ Finset.range (M + 1), (eta j : LS) * Fhat ν (M - j) := by
    apply hU.mul_right_cancel
    rw [hk]
    ring
  rw [hQ, Sfam, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Rfam]
  have hY : Yp (j : ℤ) * Yp ((M - j : ℕ) : ℤ) = Yp 1 ^ M := by
    rw [← Yp_add, Yp_pow, mul_one]
    congr 1
    omega
  have hsc : cQ (4 ^ M) * cQ ((eta j : ℚ) * (M.descFactorial j : ℚ) / 2 ^ j) *
      cQ (((M - j).factorial : ℚ) / 2 ^ (M - j)) =
      cQ (M.factorial : ℚ) * cQ 2 ^ M * (eta j : LS) := by
    rw [← map_intCast cQ, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    have h1 : ((M - j).factorial : ℚ) * (M.descFactorial j : ℚ) = M.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial hj'
    have h2 : (2 : ℚ) ^ M = 2 ^ j * 2 ^ (M - j) := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : (4 : ℚ) ^ M = 2 ^ M * 2 ^ M := by
      rw [← mul_pow]
      norm_num
    rw [h4, ← h1]
    field_simp
    rw [h2]
    ring
  rw [mul_pow]
  linear_combination (-(Nfam M * Fhat ν (M - j) * Yp 1 ^ M)) * hsc -
    (cQ (4 ^ M) * cQ ((eta j : ℚ) * (M.descFactorial j : ℚ) / 2 ^ j) *
      cQ (((M - j).factorial : ℚ) / 2 ^ (M - j)) * Nfam M * Fhat ν (M - j)) * hY

/-- The reduction of l.1300–1304: `∑_s η_s M(M−1)⋯(M−s+1) (Y/2)^s R_{M−s}` is in `DegFam` when
`R` is. -/
theorem DegFam.S {ν : Fin 2} (hR : DegFam (Rfam ν)) : DegFam (Sfam ν) := by
  intro i j
  set B : ℕ := ((i : ℤ) + j).toNat + 1 with hBdef
  have key : ∀ M, cf (Sfam ν M) i j = ∑ s ∈ Finset.range B, ((eta s : ℚ) / 2 ^ s) *
      ((M.descFactorial s : ℚ) * cf (Rfam ν (M - s)) i (j - s)) := by
    intro M
    have term : ∀ s : ℕ,
        cf (cQ ((eta s : ℚ) * (M.descFactorial s : ℚ) / 2 ^ s) * Yp s * Rfam ν (M - s)) i j =
        ((eta s : ℚ) / 2 ^ s) * ((M.descFactorial s : ℚ) * cf (Rfam ν (M - s)) i (j - s)) := by
      intro s
      rw [mul_assoc, cf_cQ_mul, cf_Yp_mul]
      ring
    have hz : ∀ s : ℕ, (M < s ∨ B ≤ s) → ((eta s : ℚ) / 2 ^ s) *
        ((M.descFactorial s : ℚ) * cf (Rfam ν (M - s)) i (j - s)) = 0 := by
      intro s hs
      rcases hs with hs | hs
      · rw [Nat.descFactorial_eq_zero_iff_lt.2 hs]
        simp
      · have h0 : cf (Rfam ν (M - s)) i (j - s) = 0 :=
          (hR i (j - s)).eq_zero (by omega) (M - s)
        rw [h0]
        simp
    rw [Sfam, cf_sum]
    simp only [term]
    exact (Finset.sum_subset (Finset.range_mono (show M + 1 ≤ M + 1 + B by omega))
        (fun s _ hs => hz s (Or.inl (by simpa using hs)))).trans
      (Finset.sum_subset (Finset.range_mono (show B ≤ M + 1 + B by omega))
        (fun s _ hs => hz s (Or.inr (by simpa using hs)))).symm
  refine PolyDeg.congr ?_ key
  refine PolyDeg.sum _ fun s _ => PolyDeg.const_mul _ ?_
  exact ((hR i (j - s)).shift s).mono (by omega)

/-! ### The expansion in `t` (l.1304–1306) -/

/-- `D₀⁻¹ = diag(K_λ⁻¹ Y^{−ℓ(λ)})`. -/
noncomputable def D0i (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) LS :=
  Matrix.diagonal fun Y => cQ (1 / (topNat Y.word Y.word : ℚ)) * Yp (-(Y.word.length : ℤ))

/-- `−tG₁D₀⁻¹ = 1 − G̃D₀⁻¹`; the paper's `(tG₁D₀⁻¹)_{λ,λ'} = G̃_{λ,λ'}/D₀(λ') − δ_{λ,λ'}`
(l.1313). -/
noncomputable def Em (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) LS :=
  1 - Gser n * D0i n

/-- The `r`-th term `(n!/2ⁿ) Yⁿ (−t)^r Tr(D₀⁻¹(G₁D₀⁻¹)^r ρ̃)` of the expansion of `R_n`
(paper.tex l.1304–1305). -/
noncomputable def Tfam (ν : Fin 2) (r n : ℕ) : LS :=
  cQ ((n.factorial : ℚ) / 2 ^ n) * Yp n * trR ν n (D0i n * Em n ^ r)

theorem Em_dvd (n : ℕ) (Y Y' : Nat.Partition n) : (PowerSeries.X : LS) ∣ Em n Y Y' := by
  rw [PowerSeries.X_dvd_iff, Em, Matrix.sub_apply, D0i, Matrix.mul_diagonal, map_sub, map_mul,
    cc_GL, Matrix.one_apply]
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

theorem pow_Em_dvd (n r : ℕ) :
    ∀ Y Y' : Nat.Partition n, (PowerSeries.X : LS) ^ r ∣ (Em n ^ r) Y Y' := by
  induction r with
  | zero => intro Y Y'; rw [pow_zero]; exact one_dvd _
  | succ r ih =>
    intro Y Y'
    rw [pow_succ, pow_succ, Matrix.mul_apply]
    exact Finset.dvd_sum fun Z _ => mul_dvd_mul (ih Y Z) (Em_dvd n Z Y')

theorem neumann (n i : ℕ) :
    (Gser n)⁻¹ = D0i n * ∑ r ∈ Finset.range (i + 1), Em n ^ r + (Gser n)⁻¹ * Em n ^ (i + 1) := by
  have h1 : Gser n * D0i n = 1 - Em n := by
    rw [Em]
    abel
  have h2 : (1 - Em n) * ∑ r ∈ Finset.range (i + 1), Em n ^ r = 1 - Em n ^ (i + 1) :=
    mul_neg_geom_sum (Em n) (i + 1)
  have h3 : (Gser n)⁻¹ * Gser n = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_GL n)
  have h4 : (Gser n)⁻¹ * (Gser n * D0i n * ∑ r ∈ Finset.range (i + 1), Em n ^ r) =
      D0i n * ∑ r ∈ Finset.range (i + 1), Em n ^ r := by
    rw [mul_assoc, ← mul_assoc, h3, one_mul]
  rw [← h4, h1, h2]
  noncomm_ring

theorem cf_Rfam_eq (ν : Fin 2) (n i : ℕ) (j : ℤ) :
    cf (Rfam ν n) i j = ∑ r ∈ Finset.range (i + 1), cf (Tfam ν r n) i j := by
  have hdec : Rfam ν n = ∑ r ∈ Finset.range (i + 1), Tfam ν r n +
      cQ ((n.factorial : ℚ) / 2 ^ n) * Yp n * trR ν n ((Gser n)⁻¹ * Em n ^ (i + 1)) := by
    rw [Rfam, Fhat]
    conv_lhs => rw [neumann n i]
    rw [trR_add, Matrix.mul_sum, trR_sum, mul_add, Finset.mul_sum]
    rfl
  have hdvd : (PowerSeries.X : LS) ^ (i + 1) ∣
      cQ ((n.factorial : ℚ) / 2 ^ n) * Yp n * trR ν n ((Gser n)⁻¹ * Em n ^ (i + 1)) := by
    refine Dvd.dvd.mul_left ?_ _
    refine Finset.dvd_sum fun Y _ => Finset.dvd_sum fun Y' _ => Dvd.dvd.mul_right ?_ _
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun Z _ => Dvd.dvd.mul_left (pow_Em_dvd n (i + 1) Z Y') _
  rw [hdec, cf_add, cf_sum, cf_of_dvd hdvd (Nat.lt_succ_self i), add_zero]

end Virasoro.H13D

namespace Virasoro

open Polynomial H13D

/-- Frozen sub-statement of Proposition 6.8(ii) (paper.tex l.1304–1378): for every `r ≥ 0`, each
`[t^i Y^j]` of the `r`-th term `(M!/2^M) Y^M (−t)^r Tr(D₀⁻¹(G₁D₀⁻¹)^r ρ̃)` of the expansion of
`R_M` is a polynomial in `M` of degree at most `2i + 2j` for all `M ≥ 0`.
Demand sheet: `ν ∈ {1,2}` (`ζ ∈ {−1,2}`, l.1299); every `r ≥ 0` (the consumer sums `0 ≤ r ≤ i`,
l.1305–1306, `cf_Rfam_eq`); every `i ≥ 0` and `j ∈ ℤ` (l.1303; negative `j` is reached through
the factors `(Y/2)^s` and `Y^{−b}`, `DegFam.S`, `DegFam.N_mul`); degree at most `2i + 2j`, the
zero polynomial when `2i + 2j < 0` (used to bound the `s`- and `b`-sums); all `M ≥ 0`
(l.1303–1304, l.1381–1382).  `(−t)^r D₀⁻¹(G₁D₀⁻¹)^r` is `D₀⁻¹(1 − G̃D₀⁻¹)^r` (`Tfam`), as in
l.1313. -/
def Stmt_sub_h13_degree_chain : Prop :=
  ∀ (ν : Fin 2) (r : ℕ), DegFam (Tfam ν r)

/-- `[t^i Y^j] R_M` is a polynomial in `M` of degree at most `2i + 2j` (the statement to which
l.1299–1304 reduces clause (ii)), from the terms of the expansion. -/
theorem degFam_R_of_chain (h : Stmt_sub_h13_degree_chain) (ν : Fin 2) : DegFam (Rfam ν) := by
  intro i j
  exact (PolyDeg.sum _ fun r _ => h ν r i j).congr fun M => cf_Rfam_eq ν M i j

/-- Proposition 6.8(ii) from the terms of the expansion of `R_M` (paper.tex l.1293–1306). -/
theorem sub_h13_degree_of_chain (h : Stmt_sub_h13_degree_chain) : Stmt_sub_h13_degree := by
  intro P hP ν i j
  obtain ⟨f, hf1, hf2⟩ := ((degFam_R_of_chain h ν).S).N_mul i (j : ℤ)
  refine ⟨f, natDegree_le_iff_coeff_eq_zero.2 fun N hN => hf1 N (by omega), fun M => ?_⟩
  have hQ : clearedH ν M = psi (thetaInv (P ν M)) := by
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  have h3 := cf_iM_thetaInv (P ν M) i j
  rw [iM_Q hQ, cf_cQ_mul] at h3
  have h4 : cf (Nfam M * Sfam ν M) i (j : ℤ) = f.eval (M : ℚ) := hf2 M
  rw [← h4, ← h3]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))

end Virasoro
