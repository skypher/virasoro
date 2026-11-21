import Virasoro.Proofs.GenPZero
import Virasoro.Proofs.GenericH
import Virasoro.Proofs.IsingAux
import Virasoro.Proofs.Germs
import Virasoro.Statements.Sec6b

/-!
# Lemma 6.5 of `paper.tex` at 70bac53: the external weight `d = 0`

Every `ℛ_{r,s}` vanishes at `d = 0` and `∂_d ℛ_{r,s}|_{d=0} = -φ(r,s)/(2φ(1,1))`
(`Virasoro/Proofs/GenPZero.lean`).  By the generic recursion (Proposition 6.4) at the generic
point `b` of `ℚ(b)`, `H_N` vanishes at `d = 0` for `N ≥ 1`, and differentiating the recursion
there leaves only the labels with `rs = N` (paper.tex l.1083–1086).

The recursion is an identity in `ℚ(b)(Δ)` for each value of `d` in `ℚ(b)`; both sides are values
of polynomials in `d`, so it is an identity of polynomials in `d` over `ℚ(b)(Δ)`.
-/

namespace Virasoro

open Polynomial

section Bridge

variable {K : Type*} [Field K] [CharZero K]

theorem eval_torus_X (c Δ d : K) (M : ℕ) (Y Y' : Nat.Partition M) :
    (torus (C c) (C Δ) (X : K[X]) M Y Y').eval d = torus c Δ d M Y Y' := by
  have := torus_map (Polynomial.evalRingHom d) (C c) (C Δ) (X : K[X]) M
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  rw [this]
  rfl

/-- The polynomial `F_M(c,Δ,d)` in `d` has the values `Fval`. -/
theorem eval_FpolyD (c Δ d : K) (M : ℕ) : (FpolyD c Δ M).eval d = Fval c d Δ M := by
  simp only [FpolyD, Fval, eval_finsetSum, eval_mul, eval_C, eval_torus_X, Matrix.inv_def,
    Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun Y' _ => mul_assoc _ _ _

theorem eval_HpolyD (c Δ d : K) (N : ℕ) : (HpolyD c Δ N).eval d = Hval c d Δ N := by
  simp only [HpolyD, Hval, eval_finsetSum, eval_mul, eval_intCast, eval_FpolyD]

theorem Hval_level_zero (c d z : K) : Hval c d z 0 = 1 := by
  simp [Hval, eta_zero, Fval_zero]

theorem gram_ratFunc (c : K) (M : ℕ) :
    gram (RatFunc.C c) (RatFunc.X : RatFunc K) M =
      (gramPoly c M).map (algebraMap K[X] (RatFunc K)) := by
  have := gram_map (algebraMap K[X] (RatFunc K)) (C c) (X : K[X]) M
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_X] at this
  exact this

theorem torus_ratFunc (c d : K) (M : ℕ) :
    torus (RatFunc.C c) (RatFunc.X : RatFunc K) (RatFunc.C d) M =
      (torusPoly c d M).map (algebraMap K[X] (RatFunc K)) := by
  have := torus_map (algebraMap K[X] (RatFunc K)) (C c) (X : K[X]) (C d) M
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at this
  exact this

/-- `F_M(c,Δ,d)` as a rational function of `Δ` is `Fval` at the generic point `Δ` of `K(Δ)`. -/
theorem Frat_eq_Fval (c d : K) (M : ℕ) :
    Frat c d M = Fval (RatFunc.C c) (RatFunc.C d) (RatFunc.X : RatFunc K) M := by
  have hdet : ((gramPoly c M).map (algebraMap K[X] (RatFunc K))).det =
      algebraMap K[X] (RatFunc K) (gramPoly c M).det :=
    (RingHom.map_det (algebraMap K[X] (RatFunc K)) (gramPoly c M)).symm
  have hadj : ((gramPoly c M).map (algebraMap K[X] (RatFunc K))).adjugate =
      ((gramPoly c M).adjugate).map (algebraMap K[X] (RatFunc K)) :=
    (RingHom.map_adjugate (algebraMap K[X] (RatFunc K)) (gramPoly c M)).symm
  rw [Frat, Fval, gram_ratFunc, torus_ratFunc, hdet, hadj, Fnum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_mul]
  rfl

theorem Hrat_eq_Hval (c d : K) (N : ℕ) :
    Hrat c d N = Hval (RatFunc.C c) (RatFunc.C d) (RatFunc.X : RatFunc K) N := by
  rw [Hrat, Hval]
  exact Finset.sum_congr rfl fun j _ => by rw [Frat_eq_Fval]

end Bridge

/-- The generic point `b` of `ℚ(b)` satisfies the genericity conditions of Proposition 6.4. -/
theorem genericAt_X (hN : NormalizationIdentities) (N : ℕ) :
    GenericAt hN N (RatFunc.X : RatFunc ℚ) := by
  refine ⟨RatFunc.X_ne_zero, ?_, ?_⟩
  · intro m n _ _ hmn h0
    have h1 : algebraMap ℚ[X] (RatFunc ℚ) (C (m : ℚ) * X ^ 2 + C (n : ℚ)) = 0 := by
      simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, map_intCast]
      exact h0
    have h2 := (map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).1 h1
    have h3 := congrArg (fun P : ℚ[X] => P.coeff 2) h2
    have h4 := congrArg (fun P : ℚ[X] => P.coeff 0) h2
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_zero] at h3 h4
    norm_num at h3 h4
    rcases hmn with h | h
    · exact h h3
    · exact h h4
  · intro a _ Y h0
    have e : eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X (RatFunc.denom (normP hN a.1 a.2 Y)) =
        algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom (normP hN a.1 a.2 Y)) := by
      have := Polynomial.hom_eval₂ (RatFunc.denom (normP hN a.1 a.2 Y)) (C : ℚ →+* ℚ[X])
        (algebraMap ℚ[X] (RatFunc ℚ)) X
      rw [eval₂_C_X, RatFunc.algebraMap_X] at this
      rw [this]
      congr 1
      exact Subsingleton.elim _ _
    rw [e] at h0
    exact RatFunc.denom_ne_zero _ ((map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).1 h0)

section Main

/-- The generic recursion at the generic point of `ℚ(b)`, as an identity of polynomials in
`d` over `ℚ(b)(Δ)`. -/
theorem HpolyD_recursion (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (N : ℕ)
    (hN1 : 1 ≤ N) :
    HpolyD (kacC ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) RatFunc.X))
        (RatFunc.X : RatFunc (RatFunc ℚ)) N =
      ∑ a ∈ labels N,
        C (((RatFunc.X : RatFunc (RatFunc ℚ)) -
            (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) (kacHL a RatFunc.X))⁻¹) *
          (C (genA a.1 a.2 (RatFunc.X : RatFunc ℚ)) * genPpoly a.1 a.2 RatFunc.X *
            HpolyD (kacC (RatFunc.X : RatFunc ℚ))
              (kacHL a RatFunc.X + (a.lvl : RatFunc ℚ)) (N - a.lvl)).map
            (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) := by
  have hgen := genericAt_X hH N
  have key : ∀ d₀ : RatFunc ℚ,
      (HpolyD (kacC ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) RatFunc.X))
        (RatFunc.X : RatFunc (RatFunc ℚ)) N).eval
          ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) d₀) =
      (∑ a ∈ labels N,
        C (((RatFunc.X : RatFunc (RatFunc ℚ)) -
            (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) (kacHL a RatFunc.X))⁻¹) *
          (C (genA a.1 a.2 (RatFunc.X : RatFunc ℚ)) * genPpoly a.1 a.2 RatFunc.X *
            HpolyD (kacC (RatFunc.X : RatFunc ℚ))
              (kacHL a RatFunc.X + (a.lvl : RatFunc ℚ)) (N - a.lvl)).map
            (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))).eval
          ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) d₀) := by
    intro d₀
    have hrec := hgen.recursion hK hN1 d₀
    unfold GenericRecursionAt at hrec
    rw [eval_HpolyD, ← map_kacC (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)), ← Hrat_eq_Hval,
      hrec, eval_finsetSum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hH' : RatFunc.eval (RingHom.id (RatFunc ℚ)) (kacHL a RatFunc.X + (a.lvl : RatFunc ℚ))
        (Hrat (kacC (RatFunc.X : RatFunc ℚ)) d₀ (N - a.lvl)) =
        Hval (kacC (RatFunc.X : RatFunc ℚ)) d₀ (kacHL a RatFunc.X + (a.lvl : RatFunc ℚ))
          (N - a.lvl) :=
      evalAt_Hrat fun M hM => hgen.gram_det_shift_ne hK ha (by omega)
    rw [eval_mul, eval_C, eval_map, eval₂_at_apply, eval_mul, eval_mul, eval_C, genPpoly_eval,
      eval_HpolyD, hH', genR, div_eq_mul_inv]
    simp only [map_mul]
    ring
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective fun n : ℕ =>
      (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) (n : RatFunc ℚ) := by
    intro m n h
    have h' : ((m : ℕ) : RatFunc (RatFunc ℚ)) = ((n : ℕ) : RatFunc (RatFunc ℚ)) := by
      simpa using h
    exact_mod_cast h'
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨n, rfl⟩
  exact key (n : RatFunc ℚ)

theorem label_pos {N : ℕ} {a : Label} (ha : a ∈ labels N) : 0 < a.1 ∧ 0 < a.2 ∧ a.1 * a.2 ≤ N := by
  have := mem_labels.1 ha
  omega

/-- `H_N` vanishes at `d = 0` for `N ≥ 1`. -/
theorem HpolyD_coeff_zero (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (N : ℕ)
    (hN1 : 1 ≤ N) :
    (HpolyD (kacC ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) RatFunc.X))
        (RatFunc.X : RatFunc (RatFunc ℚ)) N).coeff 0 = 0 := by
  rw [HpolyD_recursion hK hH N hN1, finsetSum_coeff]
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨hr, hs, -⟩ := label_pos ha
  rw [coeff_C_mul, coeff_map, mul_assoc (C _), coeff_C_mul, mul_coeff_zero,
    (genPpoly_coeff a.1 a.2 hr hs _).1]
  simp

/-- The value at `d = 0` of `H_M` at a shifted weight, `M ≥ 1`. -/
theorem Hval_shift_zero (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {N : ℕ}
    {a : Label} (ha : a ∈ labels N) {M : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N) :
    Hval (kacC (RatFunc.X : RatFunc ℚ)) 0 (kacHL a RatFunc.X + (a.lvl : RatFunc ℚ)) M = 0 := by
  have hgen := genericAt_X hH N
  have h0 : Hrat (kacC (RatFunc.X : RatFunc ℚ)) (0 : RatFunc ℚ) M = 0 := by
    rw [Hrat_eq_Hval, map_kacC, ← eval_HpolyD, map_zero, ← coeff_zero_eq_eval_zero]
    exact HpolyD_coeff_zero hK hH M hM1
  rw [← evalAt_Hrat (d := (0 : RatFunc ℚ)) fun M' hM' =>
    hgen.gram_det_shift_ne hK ha (by omega), h0]
  simp

/-- Lemma 6.5 from the cited inputs of Proposition 6.4. -/
theorem lem_d_derivatives_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_lem_d_derivatives := by
  classical
  intro N hN1
  have hgen := genericAt_X hH N
  have hb : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hb1 : (RatFunc.X : RatFunc ℚ) ^ 2 + 1 ≠ 0 := by
    have := hgen.lin 1 1 (by rw [abs_one]; omega) (by rw [abs_one]; omega) (Or.inl one_ne_zero)
    simpa using this
  refine ⟨fun M _ => ?_, HpolyD_coeff_zero hK hH N hN1, ?_⟩
  · have hdet : ((gramPoly (kacC (RatFunc.X : RatFunc ℚ)) M).map
        (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)))).det =
        algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (gramPoly (kacC RatFunc.X) M).det :=
      (RingHom.map_det (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))) _).symm
    rw [← map_kacC (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)), gram_ratFunc, hdet]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (RatFunc ℚ))).2
      (gramPoly_det_ne_zero _ M)
  · rw [HpolyD_recursion hK hH N hN1, finsetSum_coeff]
    have hterm : ∀ a ∈ labels N,
        (C (((RatFunc.X : RatFunc (RatFunc ℚ)) -
            (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) (kacHL a RatFunc.X))⁻¹) *
          (C (genA a.1 a.2 (RatFunc.X : RatFunc ℚ)) * genPpoly a.1 a.2 RatFunc.X *
            HpolyD (kacC (RatFunc.X : RatFunc ℚ))
              (kacHL a RatFunc.X + (a.lvl : RatFunc ℚ)) (N - a.lvl)).map
            (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))).coeff 1 =
        if a.1 * a.2 = N then
          -((((a.1 : ℕ) : RatFunc (RatFunc ℚ)) *
              ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) RatFunc.X) ^ 2 +
              ((a.2 : ℕ) : RatFunc (RatFunc ℚ))) /
            (2 * (((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) RatFunc.X) ^ 2 + 1) *
              ((RatFunc.X : RatFunc (RatFunc ℚ)) -
                kacHL a ((RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) RatFunc.X))))
        else 0 := by
      intro a ha
      obtain ⟨hr, hs, hle⟩ := label_pos ha
      rw [coeff_C_mul, coeff_map, mul_assoc (C _), coeff_C_mul, mul_coeff_one,
        (genPpoly_coeff a.1 a.2 hr hs _).1, zero_mul, zero_add, coeff_zero_eq_eval_zero,
        eval_HpolyD]
      split_ifs with hlvl
      · have hM : N - a.lvl = 0 := by
          simp only [Label.lvl]
          omega
        rw [hM, Hval_level_zero, mul_one,
          genA_mul_coeff_one a.1 a.2 hr hs hb hb1 (hgen.cross_ne ha),
          ← map_kacHL (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))]
        simp only [map_neg, map_div₀, map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one]
        rw [mul_comm, neg_mul, ← div_eq_mul_inv, div_div]
      · have hM1 : 1 ≤ N - a.lvl := by
          simp only [Label.lvl]
          omega
        rw [Hval_shift_zero hK hH ha hM1 (Nat.sub_le _ _), mul_zero, mul_zero, map_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_neg_distrib]

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) : Stmt_lem_d_derivatives :=
  lem_d_derivatives_of_cited hK hH

end Main

end Virasoro
