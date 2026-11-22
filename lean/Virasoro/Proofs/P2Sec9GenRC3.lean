import Virasoro.Proofs.P2Sec9GenRC2

/-!
# Theorem 9.3(b): `T^irr_N(c⋆,λ,d) ∈ ℚ` (paper.tex l.1949–1953, 3079–3088)

By (9.3), `T^irr_N(c⋆,λ,d)` is a finite combination, with coefficients `±Ω ∈ ℚ`, of values
`F_M(c⋆,μ,d)` at orbit weights, where `F_M` is regular (Theorem 9.1).  With `c⋆`, `d`, `μ`
rational, `F_M(c⋆,Δ,d)` is a quotient of polynomials with rational coefficients, and its value at
the rational regular point `μ` is rational.
-/

namespace Virasoro.P2

open Virasoro Polynomial

section Map

variable (f : ℚ →+* ℂ)

theorem gramPoly_map (c : ℚ) (M : ℕ) :
    gramPoly (f c) M = (gramPoly c M).map (Polynomial.mapRingHom f) := by
  have h := gram_map (Polynomial.mapRingHom f) (C c) (X : ℚ[X]) M
  simp only [coe_mapRingHom, map_C, map_X] at h
  exact h

theorem torusPoly_map (c d : ℚ) (M : ℕ) :
    torusPoly (f c) (f d) M = (torusPoly c d M).map (Polynomial.mapRingHom f) := by
  have h := torus_map (Polynomial.mapRingHom f) (C c) (X : ℚ[X]) (C d) M
  simp only [coe_mapRingHom, map_C, map_X] at h
  exact h

theorem Fnum_map (c d : ℚ) (M : ℕ) : Fnum (f c) (f d) M = (Fnum c d M).map f := by
  have hadj := RingHom.map_adjugate (Polynomial.mapRingHom f) (gramPoly c M)
  rw [Fnum, Fnum, gramPoly_map, torusPoly_map, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [Polynomial.map_mul]
  have e1 := congrFun (congrFun hadj Y) Y'
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, coe_mapRingHom] at e1
  simp only [coe_mapRingHom, Matrix.map_apply]
  rw [e1]

theorem gramPoly_det_map (c : ℚ) (M : ℕ) :
    (gramPoly (f c) M).det = ((gramPoly c M).det).map f := by
  rw [gramPoly_map]
  have h := RingHom.map_det (Polynomial.mapRingHom f) (gramPoly c M)
  rw [coe_mapRingHom] at h
  rw [h]
  rfl

end Map

/-- The value at a rational regular point of `F_M(c,Δ,d)` with rational `c`, `d` is rational. -/
theorem Fval_rat {qc qd qμ : ℚ} {M : ℕ}
    (hreg : RegAt (qμ : ℂ) (Frat (qc : ℂ) (qd : ℂ) M)) :
    ∃ q : ℚ, FvalAt (qc : ℂ) (qd : ℂ) M (qμ : ℂ) = q := by
  classical
  set f : ℚ →+* ℂ := algebraMap ℚ ℂ with hf
  set P := Fnum qc qd M with hPdef
  set Q := (gramPoly qc M).det with hQdef
  have hQ : Q ≠ 0 := gramPoly_det_ne_zero _ _
  have hcf : (qc : ℂ) = f qc := (eq_ratCast f qc).symm
  have hdf : (qd : ℂ) = f qd := (eq_ratCast f qd).symm
  have hF : Frat (qc : ℂ) (qd : ℂ) M =
      algebraMap ℂ[X] (RatFunc ℂ) (P.map f) / algebraMap ℂ[X] (RatFunc ℂ) (Q.map f) := by
    rw [Frat, hcf, hdf, Fnum_map, gramPoly_det_map]
  have hQm : Q.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).2 hQ
  have hQa : algebraMap ℂ[X] (RatFunc ℂ) (Q.map f) ≠ 0 := RatFunc.algebraMap_ne_zero hQm
  have hrel : Frat (qc : ℂ) (qd : ℂ) M * algebraMap ℂ[X] (RatFunc ℂ) (Q.map f) =
      algebraMap ℂ[X] (RatFunc ℂ) (P.map f) := by
    rw [hF, div_mul_cancel₀ _ hQa]
  by_cases hP : P = 0
  · refine ⟨0, ?_⟩
    rw [FvalAt, hF, hP, Polynomial.map_zero, map_zero, zero_div]
    simp
  obtain ⟨B, hQB, hBnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ qμ
  obtain ⟨A, hPA, hAnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP qμ
  set e := rootMultiplicity qμ Q with he
  set e' := rootMultiplicity qμ P with he'
  have hB0 : B.eval qμ ≠ 0 := fun h => hBnd (Polynomial.dvd_iff_isRoot.2 h)
  have hA0 : A.eval qμ ≠ 0 := fun h => hAnd (Polynomial.dvd_iff_isRoot.2 h)
  have hXm : (X - C qμ).map f = X - C (qμ : ℂ) := by
    rw [Polynomial.map_sub, map_X, map_C, eq_ratCast]
  set u : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (X - C (qμ : ℂ)) with hu
  have hu0 : u ≠ 0 := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero _)
  have hQu : algebraMap ℂ[X] (RatFunc ℂ) (Q.map f) = u ^ e * algebraMap ℂ[X] (RatFunc ℂ) (B.map f) := by
    conv_lhs => rw [hQB]
    rw [Polynomial.map_mul, Polynomial.map_pow, hXm, map_mul, map_pow]
  have hPu : algebraMap ℂ[X] (RatFunc ℂ) (P.map f) = u ^ e' * algebraMap ℂ[X] (RatFunc ℂ) (A.map f) := by
    conv_lhs => rw [hPA]
    rw [Polynomial.map_mul, Polynomial.map_pow, hXm, map_mul, map_pow]
  rw [hQu, hPu] at hrel
  have hAe : (A.map f).eval (qμ : ℂ) = ((A.eval qμ : ℚ) : ℂ) := eval_map_ratCast qμ A
  have hBe : (B.map f).eval (qμ : ℂ) = ((B.eval qμ : ℚ) : ℂ) := eval_map_ratCast qμ B
  by_cases hee : e ≤ e'
  · have hrel' : Frat (qc : ℂ) (qd : ℂ) M * algebraMap ℂ[X] (RatFunc ℂ) (B.map f) =
        algebraMap ℂ[X] (RatFunc ℂ) ((X - C (qμ : ℂ)) ^ (e' - e) * A.map f) := by
      rw [map_mul, map_pow, ← hu]
      apply mul_left_cancel₀ (pow_ne_zero e hu0)
      rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hee, mul_comm (u ^ e), mul_assoc,
        hrel]
    have hBc : (B.map f).eval (qμ : ℂ) ≠ 0 := by rw [hBe]; exact_mod_cast hB0
    obtain ⟨-, hval⟩ := value_of_mul hrel' hBc
    refine ⟨((0 : ℚ) ^ (e' - e) * A.eval qμ) / B.eval qμ, ?_⟩
    rw [FvalAt]
    change evalAt (qμ : ℂ) _ = _
    rw [hval, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, hAe, hBe]
    push_cast
    rfl
  · exfalso
    push_neg at hee
    have hrel2 : Frat (qc : ℂ) (qd : ℂ) M *
        algebraMap ℂ[X] (RatFunc ℂ) ((X - C (qμ : ℂ)) ^ (e - e') * B.map f) =
          algebraMap ℂ[X] (RatFunc ℂ) (A.map f) := by
      rw [map_mul, map_pow, ← hu]
      apply mul_left_cancel₀ (pow_ne_zero e' hu0)
      rw [← mul_assoc, mul_comm (u ^ e') (Frat _ _ _), mul_assoc, ← mul_assoc (u ^ e'), ← pow_add,
        Nat.add_sub_cancel' hee.le, hrel]
    set F := Frat (qc : ℂ) (qd : ℂ) M with hFdef
    have hnd : F * algebraMap ℂ[X] (RatFunc ℂ) F.denom = algebraMap ℂ[X] (RatFunc ℂ) F.num := by
      have h := RatFunc.num_div_denom F
      rw [div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero F))] at h
      exact h.symm
    have hpoly : F.num * ((X - C (qμ : ℂ)) ^ (e - e') * B.map f) = A.map f * F.denom := by
      apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
      rw [map_mul (algebraMap ℂ[X] (RatFunc ℂ)) F.num, map_mul (algebraMap ℂ[X] (RatFunc ℂ)) (A.map f),
        ← hnd, ← hrel2]
      ring
    have h0 := congrArg (Polynomial.eval (qμ : ℂ)) hpoly
    rw [eval_mul, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (by omega), zero_mul, mul_zero, eval_mul] at h0
    have hAc : (A.map f).eval (qμ : ℂ) ≠ 0 := by rw [hAe]; exact_mod_cast hA0
    exact (mul_ne_zero hAc hreg) h0.symm

/-- `c⋆`, `h_{u,v}(b⋆)` and the orbit weights are rational. -/
theorem momWt_rat (p p' : ℕ) (n : ℤ) :
    momWt p p' n = (((((n : ℚ)) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p') : ℚ) : ℂ) := by
  unfold momWt
  push_cast
  rfl

/-- Part (b) (l.1949–1953, 3079–3088). -/
theorem gen_rc_b (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k m : ℕ} (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (N : ℕ) (T : ℂ)
    (hT : IsIrrTrace (kacC b) (kacH r s b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N T) :
    ∃ q : ℚ, T = (q : ℂ) := by
  classical
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  set K : Subfield ℂ := (algebraMap ℚ ℂ).fieldRange with hKdef
  have hKq : ∀ q : ℚ, (q : ℂ) ∈ K := fun q => ⟨q, eq_ratCast _ q⟩
  have hc : kacC b ∈ K := by rw [kacC_min hp hp' hbsq]; exact hKq _
  have hd : kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b ∈ K := by
    rw [kacH_momWt hp hp' hbsq, momWt_rat]; exact hKq _
  have hμK : ∀ ε j, muOrb p p' r s ε j ∈ K := fun ε j => by
    rw [muOrb, momWt_rat]; exact hKq _
  have hval : ∀ ε j M, FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) M
      (muOrb p p' r s ε j) ∈ K := by
    intro ε j M
    obtain ⟨qc, hqc⟩ := hc
    obtain ⟨qd, hqd⟩ := hd
    obtain ⟨qμ, hqμ⟩ := hμK ε j
    have hreg := gen_rc_regular hK hH hU hF hJ hI hset hk hm ε j M
    rw [← hqc, ← hqd, ← hqμ, eq_ratCast, eq_ratCast, eq_ratCast] at hreg ⊢
    obtain ⟨q, hq⟩ := Fval_rat hreg
    rw [hq]
    exact hKq q
  have hmain := (gen_rc_main hK hE hH hU hF hLau hJ hI hset hk hm N).2 T hT
  have hmem : T ∈ K := by
    rw [hmain, ← muOrb_true_zero hset]
    refine K.add_mem (hval true 0 N) (K.sum_mem fun j _ => K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) _)
      (K.add_mem ?_ ?_))
    · split_ifs
      · exact K.mul_mem (hKq _) (hval _ _ _)
      · exact K.zero_mem
    · split_ifs
      · exact K.mul_mem (hKq _) (hval _ _ _)
      · exact K.zero_mem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, by rw [← hq, eq_ratCast]⟩

end Virasoro.P2
