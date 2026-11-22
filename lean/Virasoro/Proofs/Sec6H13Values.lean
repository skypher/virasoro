import Virasoro.Proofs.Sec6H13Poly
import Virasoro.Proofs.SingularDegree
import Virasoro.Proofs.PBWBridge

/-!
# Proposition 6.8(i) of `paper.tex` at 70bac53: the values at `t = 0` (l.1248–1256)

`ρ̃(0,Y;ζ)` is independent of `ζ`, so `P_M^{(2)}(0,Y) = P_M^{(1)}(0,Y)`, and
`P_M^{(ν)}(0,Y) = M! (2Y)^M ∑_s η_s ∑_{λ ⊢ M-s} (K_λ Y^{ℓ(λ)})⁻¹ ρ̃^{(M-s)}(0,Y)_{λ,λ}`.
Only `(s,λ) = (0,(1^M))` has `M - ℓ(λ) = 0`, where `M! 2^M / K_{(1^M)} = 1` and
`ρ̃^{(M)}(0,0)_{(1^M),(1^M)} = (-2)^{2M} = 4^M`; so `P_M^{(ν)}(0,0) = 4^M`.
-/

namespace Virasoro

open Polynomial

/-- Frozen sub-statement of Proposition 6.8(i) (paper.tex l.1185–1187, proof l.1248–1256):
`P_M^{(2)}(0,Y) = P_M^{(1)}(0,Y)` and `P_M^{(ν)}(0,0) = 4^M`.
Demand sheet: for every family `P` of polynomials tied to the definition by
`P(t, t²Δ) = clearedH ν M` (this determines `P`), the second and third conjuncts of clause (i)
of `Stmt_prop_h13_nonvanishing`, word for word, for `M ≥ 1`. -/
def Stmt_sub_h13_values : Prop :=
  ∀ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    (∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M) →
    ∀ (ν : Fin 2) (M : ℕ), 1 ≤ M →
      MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
        MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
      MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M

/-! ### `ℚ[t][Y]` and `ℚ[t,Y]` -/

theorem PS_ringHom_ext {A : Type*} [Semiring A] (f g : PS →+* A) (h1 : f tS = g tS)
    (h2 : f X = g X) : f = g := by
  refine Polynomial.ringHom_ext (fun p => ?_) h2
  have h3 : f.comp C = g.comp C := by
    refine Polynomial.ringHom_ext (fun r => ?_) h1
    exact RingHom.congr_fun (RingHom.ext_rat ((f.comp C).comp C) ((g.comp C).comp C)) r
  exact RingHom.congr_fun h3 p

/-- `ℚ[t,Y] → ℚ[t][Y]`. -/
noncomputable def thetaInv : MvPolynomial (Fin 2) ℚ →+* PS :=
  ((MvPolynomial.aeval (![tS, X] : Fin 2 → PS) : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] PS) :
    MvPolynomial (Fin 2) ℚ →+* PS)

theorem thetaMv_thetaInv (Q : MvPolynomial (Fin 2) ℚ) : thetaMv (thetaInv Q) = Q := by
  have h : thetaMv.comp thetaInv = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · exact RingHom.congr_fun (RingHom.ext_rat ((thetaMv.comp thetaInv).comp MvPolynomial.C)
        ((RingHom.id _).comp MvPolynomial.C)) r
    · fin_cases i <;> simp [thetaInv, thetaMv, tS]
  exact RingHom.congr_fun h Q

theorem aeval0_thetaMv (Q : PS) :
    MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (thetaMv Q) = ev0 Q := by
  have h : ((MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℚ[X]) :
      MvPolynomial (Fin 2) ℚ →+* ℚ[X]).comp thetaMv = ev0 :=
    PS_ringHom_ext _ _ (by simp [thetaMv, tS, ev0]) (by simp [thetaMv, ev0])
  exact RingHom.congr_fun h Q

theorem eval00_thetaMv (Q : PS) :
    MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (thetaMv Q) = (ev0 Q).eval 0 := by
  have h : (MvPolynomial.eval (![0, 0] : Fin 2 → ℚ)).comp thetaMv =
      (evalRingHom (0 : ℚ)).comp ev0 :=
    PS_ringHom_ext _ _ (by simp [thetaMv, tS, ev0]) (by simp [thetaMv, ev0])
  exact RingHom.congr_fun h Q

/-- `P_M^{(ν)}` is determined by `P(t, t²Δ) = clearedH ν M`. -/
theorem eq_thetaMv_of_aeval {P' : MvPolynomial (Fin 2) ℚ} {Q : PS}
    (h : MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        P' = psi Q) : P' = thetaMv Q := by
  have h1 := aeval_thetaMv (thetaInv P')
  rw [thetaMv_thetaInv, h] at h1
  rw [psi_injective h1, thetaMv_thetaInv]

/-! ### `P_M^{(ν)}` as a quotient in `ℚ[t][Y]` -/

/-- `M! t^{2M} ∏ (2Δ - 2h_{u,1}) = M! ∏ (2Y + (u-1)t² + (u²-1)/2 t³)` (paper.tex l.1250–1251). -/
noncomputable def prefS (M : ℕ) : PS :=
  (M.factorial : PS) * ∏ u ∈ Finset.Icc 1 M, (2 * X - C (polH u))

theorem clearedH_pref (ν : Fin 2) (M : ℕ) :
    clearedH ν M = psi (prefS M) * Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M := by
  have h1 : clearedH ν M =
      (M.factorial : RatFunc (RatFunc ℚ)) *
        (∏ u ∈ Finset.Icc 1 M, (RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 *
          (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))))) *
        Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, clearedH, ← pow_mul]
    simp only [Nat.add_sub_cancel]
    rw [d13]
    ring
  rw [h1, prefS, map_mul, map_natCast, map_prod]
  congr 2
  exact Finset.prod_congr rfl fun u _ => psi_pref u

theorem Frat_psi (ν : Fin 2) (N : ℕ) :
    Frat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N * psi (GsM N).det = psi (numS ν N) := by
  have hdet : algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
      (gramPoly (cT (RatFunc.X : RatFunc ℚ)) N).det ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)))]
    exact gramPoly_det_ne_zero _ N
  simp only [psi, RingHom.comp_apply]
  rw [psi1_det, psi1_numS, map_mul, map_mul, Frat]
  field_simp

/-- The common denominator `∏_s det G̃_{M-s}`. -/
noncomputable def Bden (M : ℕ) : PS := ∏ j ∈ Finset.range (M + 1), (GsM (M - j)).det

/-- The numerator of `H_M = ∑_s η_s Tr(G̃_{M-s}⁻¹ ρ̃_{M-s})` over the common denominator. -/
noncomputable def Anum (ν : Fin 2) (M : ℕ) : PS :=
  ∑ j ∈ Finset.range (M + 1), (eta j : PS) * numS ν (M - j) *
    ∏ i ∈ (Finset.range (M + 1)).erase j, (GsM (M - i)).det

theorem Hrat_psi (ν : Fin 2) (M : ℕ) :
    Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M * psi (Bden M) = psi (Anum ν M) := by
  unfold Hrat Bden Anum
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.mul_prod_erase _ (fun i => (GsM (M - i)).det) hj, map_mul, map_mul, map_mul,
    map_intCast, ← Frat_psi]
  ring

theorem key_PS {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) :
    Q * Bden M = prefS M * Anum ν M := by
  apply psi_injective
  rw [map_mul, map_mul, ← h, clearedH_pref, ← Hrat_psi]
  ring

/-! ### The value at `t = 0` -/

/-- `D₀(λ) = K_λ Y^{ℓ(λ)}`. -/
noncomputable def D0 {n : ℕ} (Y : Nat.Partition n) : ℚ[X] :=
  ((topNat Y.word Y.word : ℕ) : ℚ[X]) * X ^ Y.word.length

theorem topNat_word_ne {n : ℕ} (Y : Nat.Partition n) : (topNat Y.word Y.word : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.2 (topNat_self_pos Y.word (word_pos Y)).ne'

theorem D0_ne_zero {n : ℕ} (Y : Nat.Partition n) : D0 Y ≠ 0 := by
  refine mul_ne_zero ?_ (pow_ne_zero _ X_ne_zero)
  rw [← C_eq_natCast]
  exact C_ne_zero.2 (topNat_word_ne Y)

/-- `ρ̃_n(0,Y)_{λ,λ}`; it does not depend on `ζ`. -/
noncomputable def rr0 (n : ℕ) (Y : Nat.Partition n) : ℚ[X] :=
  torusWordT (0 : ℚ[X]) (ev0 cS) X (-2) Y.word Y.word

theorem ev0_dS (ν : Fin 2) : ev0 (dS ν) = -2 := by
  unfold dS ev0
  split_ifs <;> simp <;> exact map_ofNat C 2

theorem ev0_det (n : ℕ) : ev0 (GsM n).det = ∏ Y : Nat.Partition n, D0 Y := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, GsM_ev0, Matrix.det_diagonal]
  rfl

theorem ev0_det_ne_zero (n : ℕ) : ev0 (GsM n).det ≠ 0 := by
  rw [ev0_det]
  exact Finset.prod_ne_zero_iff.2 fun Y _ => D0_ne_zero Y

theorem ev0_numS (ν : Fin 2) (n : ℕ) :
    ev0 (numS ν n) = ∑ Y : Nat.Partition n, (∏ Z ∈ Finset.univ.erase Y, D0 Z) * rr0 n Y := by
  rw [numS, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  have hadj : ∀ Y', ev0 ((GsM n).adjugate Y Y') =
      (Matrix.diagonal fun Z : Nat.Partition n => ∏ W ∈ Finset.univ.erase Z, D0 W) Y Y' := by
    intro Y'
    have h1 := RingHom.map_adjugate ev0 (GsM n)
    have h2 : ev0 ((GsM n).adjugate Y Y') = (ev0.mapMatrix (GsM n).adjugate) Y Y' := rfl
    rw [h2, h1, RingHom.mapMatrix_apply, GsM_ev0, Matrix.adjugate_diagonal]
    rfl
  rw [Finset.sum_eq_single Y]
  · rw [map_mul, hadj, Matrix.diagonal_apply_eq]
    congr 1
    simp only [RsM, Matrix.of_apply]
    rw [← torusWordT_map, ev0_tS, ev0_X, ev0_dS]
    rfl
  · intro Y' _ hne
    rw [map_mul, hadj, Matrix.diagonal_apply_ne _ hne.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ Y) h

theorem ev0_Bden_ne_zero (M : ℕ) : ev0 (Bden M) ≠ 0 := by
  rw [Bden, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun j _ => ev0_det_ne_zero (M - j)

theorem ev0_Anum (ν : Fin 2) (M : ℕ) :
    ev0 (Anum ν M) = ∑ j ∈ Finset.range (M + 1), (eta j : ℚ[X]) *
      (∑ Y : Nat.Partition (M - j), (∏ Z ∈ Finset.univ.erase Y, D0 Z) * rr0 (M - j) Y) *
      ∏ i ∈ (Finset.range (M + 1)).erase j, ∏ Y : Nat.Partition (M - i), D0 Y := by
  simp only [Anum, map_sum, map_mul, map_prod, map_intCast, ev0_numS, ev0_det]

/-- `P_M^{(2)}(0,Y) = P_M^{(1)}(0,Y)` (paper.tex l.1248, l.1252). -/
theorem ev0_nu_indep {M : ℕ} {Q₀ Q₁ : PS} (h0 : clearedH 0 M = psi Q₀)
    (h1 : clearedH 1 M = psi Q₁) : ev0 Q₁ = ev0 Q₀ := by
  have k0 := congrArg ev0 (key_PS h0)
  have k1 := congrArg ev0 (key_PS h1)
  rw [map_mul, map_mul] at k0 k1
  apply mul_right_cancel₀ (ev0_Bden_ne_zero M)
  rw [k0, k1, ev0_Anum, ev0_Anum]

theorem ev0_prefS (M : ℕ) : ev0 (prefS M) = (M.factorial : ℚ[X]) * (2 * X) ^ M := by
  rw [prefS, map_mul, map_natCast, map_prod]
  have : ∀ u ∈ Finset.Icc 1 M, ev0 (2 * X - C (polH u)) = 2 * X := by
    intro u _
    simp [ev0, polH]
  rw [Finset.prod_congr rfl this, Finset.prod_const, Nat.card_Icc]
  simp

theorem perY {n M : ℕ} (Y : Nat.Partition n) (hn : n ≤ M) :
    C (1 / (topNat Y.word Y.word : ℚ)) * X ^ (M - Y.word.length) * D0 Y = X ^ M := by
  have hle : Y.word.length ≤ M := (word_length_le Y).trans hn
  have h1 : C (1 / (topNat Y.word Y.word : ℚ)) * ((topNat Y.word Y.word : ℕ) : ℚ[X]) = 1 := by
    rw [← C_eq_natCast, ← C_mul, one_div, inv_mul_cancel₀ (topNat_word_ne Y), C_1]
  have h2 : (X : ℚ[X]) ^ (M - Y.word.length) * X ^ Y.word.length = X ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [D0]
  linear_combination (X ^ (M - Y.word.length) * X ^ Y.word.length) * h1 + h2

theorem sumY (n M : ℕ) (hn : n ≤ M) :
    (∑ Y : Nat.Partition n, C (1 / (topNat Y.word Y.word : ℚ)) * X ^ (M - Y.word.length) *
        rr0 n Y) * ∏ Y : Nat.Partition n, D0 Y =
      X ^ M * ∑ Y : Nat.Partition n, (∏ Z ∈ Finset.univ.erase Y, D0 Z) * rr0 n Y := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ D0 (Finset.mem_univ Y)]
  linear_combination (rr0 n Y * ∏ Z ∈ Finset.univ.erase Y, D0 Z) * perY Y hn

/-- `P_M^{(ν)}(0,Y) = M! 2^M ∑_s η_s ∑_{λ ⊢ M-s} K_λ⁻¹ Y^{M-ℓ(λ)} ρ̃^{(M-s)}(0,Y)_{λ,λ}`
(paper.tex l.1252–1253). -/
theorem ev0_formula {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) :
    ev0 Q = (M.factorial : ℚ[X]) * 2 ^ M * ∑ j ∈ Finset.range (M + 1), (eta j : ℚ[X]) *
      ∑ Y : Nat.Partition (M - j), C (1 / (topNat Y.word Y.word : ℚ)) *
        X ^ (M - Y.word.length) * rr0 (M - j) Y := by
  have k := congrArg ev0 (key_PS h)
  rw [map_mul, map_mul, ev0_prefS, ev0_Anum] at k
  apply mul_right_cancel₀ (ev0_Bden_ne_zero M)
  rw [k, Bden, map_prod]
  simp only [ev0_det]
  rw [mul_assoc ((M.factorial : ℚ[X]) * 2 ^ M), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.mul_prod_erase _ (fun i => ∏ Y : Nat.Partition (M - i), D0 Y) hj]
  have := sumY (M - j) M (Nat.sub_le M j)
  linear_combination ((M.factorial : ℚ[X]) * 2 ^ M * (eta j : ℚ[X]) *
    ∏ i ∈ (Finset.range (M + 1)).erase j, ∏ Y : Nat.Partition (M - i), D0 Y) * this.symm

/-! ### The value at `(0,0)` -/

theorem delOne_replicate (n : ℕ) :
    delOne 1 (List.replicate (n + 1) 1) = List.replicate (n + 1) (List.replicate n 1) := by
  induction n with
  | zero => simp [delOne]
  | succ n ih =>
    rw [List.replicate_succ (n := n + 1) (a := 1), delOne, if_pos rfl, ih, List.map_replicate]
    rfl

/-- `K_{(1^n)} = n! 2^n` (paper.tex l.1254). -/
theorem topNat_ones (n : ℕ) :
    topNat (List.replicate n 1) (List.replicate n 1) = n.factorial * 2 ^ n := by
  induction n with
  | zero => simp [topNat]
  | succ n ih =>
    rw [List.replicate_succ, topNat, ← List.replicate_succ, delOne_replicate, List.map_replicate,
      List.sum_replicate, ih, smul_eq_mul, Nat.factorial_succ, pow_succ]
    ring

section TZero

variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem phiT_tau_zero (dt : R) : ∀ w : List ℕ, phiT 0 dt w = (w.prod : R) * dt ^ w.length
  | [] => by simp [phiT]
  | m :: w => by
    rw [phiT, phiT_tau_zero dt w, List.prod_cons, List.length_cons]
    push_cast
    ring

/-- `ρ̃(0,0)`: at `t = 0`, `Y = 0` every mode is commuted through the field (paper.tex l.1255). -/
theorem torusWordT_zero (ct dt : R) : ∀ (Y w : List ℕ), (∀ y ∈ Y, 0 < y) →
    torusWordT 0 ct 0 dt Y w = (Y.prod : R) * dt ^ Y.length * ((w.prod : R) * dt ^ w.length)
  | [], w, _ => by simp [torusWordT, phiT_tau_zero]
  | y :: Y, w, hY => by
    have hy : 0 < y := hY y (List.mem_cons_self ..)
    rw [torusWordT, dAct_tau_zero ct 0 w y hy,
      torusWordT_zero ct dt Y w fun z hz => hY z (List.mem_cons_of_mem _ hz), List.prod_cons,
      List.length_cons]
    simp only [mul_zero, zero_mul, List.map_const', List.sum_replicate, smul_zero, zero_add]
    push_cast
    ring

end TZero

theorem eval_rr0_ones (n : ℕ) : (rr0 n (onesPartition n)).eval 0 = 4 ^ n := by
  have h := torusWordT_map (evalRingHom (0 : ℚ)) (0 : ℚ[X]) (ev0 cS) X (-2)
    (onesPartition n).word (onesPartition n).word
  rw [coe_evalRingHom] at h
  rw [rr0, ← h]
  simp only [eval_zero, eval_X, eval_neg, eval_ofNat]
  rw [torusWordT_zero _ _ _ _ (word_pos _), word_onesPartition]
  simp only [List.prod_replicate, one_pow, Nat.cast_one, one_mul, List.length_replicate]
  rw [← mul_pow]
  norm_num

theorem innerEval (n M : ℕ) (hn : n ≤ M) :
    ∑ Y : Nat.Partition n, 1 / (topNat Y.word Y.word : ℚ) * (0 : ℚ) ^ (M - Y.word.length) *
        (rr0 n Y).eval 0 =
      if n = M then (4 : ℚ) ^ M / ((M.factorial : ℚ) * 2 ^ M) else 0 := by
  split_ifs with hnM
  · subst hnM
    rw [Finset.sum_eq_single (onesPartition n)]
    · rw [eval_rr0_ones, word_onesPartition, topNat_ones, List.length_replicate, Nat.sub_self,
        pow_zero]
      push_cast
      ring
    · intro Y _ hY
      have := word_length_lt Y hY
      rw [zero_pow (by omega), mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun Y _ => ?_
    have := word_length_le Y
    rw [zero_pow (by omega), mul_zero, zero_mul]

/-- `P_M^{(ν)}(0,0) = 4^M` (paper.tex l.1253–1256). -/
theorem eval_ev0 {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) :
    (ev0 Q).eval 0 = 4 ^ M := by
  rw [ev0_formula h]
  simp only [eval_mul, eval_finsetSum, eval_pow, eval_X, eval_C, eval_natCast, eval_intCast,
    eval_ofNat]
  have hin : ∀ j ∈ Finset.range (M + 1),
      ((eta j : ℤ) : ℚ) * ∑ Y : Nat.Partition (M - j), 1 / (topNat Y.word Y.word : ℚ) *
        (0 : ℚ) ^ (M - Y.word.length) * (rr0 (M - j) Y).eval 0 =
      if j = 0 then (4 : ℚ) ^ M / ((M.factorial : ℚ) * 2 ^ M) else 0 := by
    intro j hj
    rw [innerEval (M - j) M (Nat.sub_le M j)]
    have hj' := Finset.mem_range.1 hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, if_pos (Nat.sub_zero M), eta_zero]
      simp
    · rw [if_neg hj0, if_neg (by omega), mul_zero]
  rw [Finset.sum_congr rfl hin, Finset.sum_ite_eq' (Finset.range (M + 1)) 0,
    if_pos (Finset.mem_range.2 (Nat.succ_pos M))]
  have h1 : ((M.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
  field_simp

/-- The values of `P_M^{(ν)}` at `t = 0` (paper.tex l.1248–1256). -/
theorem sub_h13_values : Stmt_sub_h13_values := by
  intro P hP ν M _
  have hQ : ∀ ν, clearedH ν M = psi (thetaInv (P ν M)) := by
    intro ν
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  have hth : ∀ ν, P ν M = thetaMv (thetaInv (P ν M)) := fun ν => (thetaMv_thetaInv _).symm
  refine ⟨?_, ?_⟩
  · rw [hth 1, hth 0, aeval0_thetaMv, aeval0_thetaMv]
    exact ev0_nu_indep (hQ 0) (hQ 1)
  · rw [hth ν, eval00_thetaMv]
    exact eval_ev0 (hQ ν)

example : Stmt_sub_h13_values := sub_h13_values

end Virasoro
