import Virasoro.Proofs.P2Sec11Joint
import Virasoro.Proofs.RegEvalK
import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.SmithBasic

/-!
# Theorem 9.1(ii), first half (paper.tex l.2570–2574)

"Lemma 11.3 gives joint regularity of `F_N(c(b),Δ,h_{2k+1,ε(2m+1)}(b))` at `(b⋆,μ)`, and hence
regularity of `F_N(c⋆,Δ,d)` at `Δ = μ`": a rational function of `(b,Δ)` that is `P/Q` with
`Q(b⋆,μ) ≠ 0` specializes at `b = b⋆` to `P(b⋆,Δ)/Q(b⋆,Δ)`, which is regular at `Δ = μ`.
-/

namespace Virasoro

open Polynomial

/-- A rational function `P/Q` with `Q(a) ≠ 0` has no pole at `a`. -/
theorem poleOrder_eq_zero_of_mul {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽] {f : RatFunc 𝔽} {a : 𝔽}
    {P Q : 𝔽[X]}
    (h : f * algebraMap 𝔽[X] (RatFunc 𝔽) Q = algebraMap 𝔽[X] (RatFunc 𝔽) P)
    (hQ : Q.eval a ≠ 0) : poleOrder f a = 0 := by
  have e := congrArg (expandHom a) h
  rw [map_mul, expandHom_algebraMap, expandHom_algebraMap] at e
  have hunit : IsUnit (shiftPS a Q) :=
    PowerSeries.isUnit_iff_constantCoeff.2 (by rw [constantCoeff_shiftPS]; exact hQ.isUnit)
  obtain ⟨u, hu⟩ := hunit
  have hf : expandHom a f =
      HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a P * (↑u⁻¹ : PowerSeries 𝔽)) := by
    rw [map_mul, ← e, mul_assoc, ← map_mul, ← hu, Units.mul_inv, map_one, mul_one]
  have hord : OrdGE (expandAt f a) (-((0 : ℕ) : ℤ)) := by
    rw [expandAt_eq, hf]
    simpa using ordGE_ofPowerSeries (shiftPS a P * (↑u⁻¹ : PowerSeries 𝔽))
  have := poleOrder_le_of_ordGE hord
  omega

/-- Joint regularity at `(b⋆,μ)` of `F_N(c(b),Δ,h_{u,v}(b))` gives regularity of
`F_N(c(b⋆),Δ,h_{u,v}(b⋆))` at `Δ = μ` (paper.tex l.2571–2573). -/
theorem poleOrder_zero_of_jointRegular {b : ℂ} (hb : b ≠ 0) (u v : ℤ) (N : ℕ) (μ : ℂ)
    (h : JointRegular (Frat (kacC (RatFunc.X : RatFunc ℂ)) (kacH u v (RatFunc.X : RatFunc ℂ)) N)
      b μ) :
    poleOrder (Frat (kacC b) (kacH u v b) N) μ = 0 := by
  obtain ⟨P, Q, hQ, hPQ⟩ := h
  let A := regSubK ℂ b
  let incl : A →+* RatFunc ℂ := (regSubK ℂ b).val.toRingHom
  let ev : A →+* ℂ := evRegK ℂ b
  let cA : A := ⟨kacC RatFunc.X, (evToK_kacC hb).1⟩
  let dA : A := ⟨kacH u v RatFunc.X, (evToK_kacH hb u v).1⟩
  let xA : A := ⟨RatFunc.X, (evToK_X (K := ℂ) (b := b)).1⟩
  let j : ℂ[X] →+* A := (Polynomial.aeval xA : ℂ[X] →ₐ[ℂ] A).toRingHom
  have hevc : ev cA = kacC b := evRegK_mk ℂ (evToK_kacC hb)
  have hevd : ev dA = kacH u v b := evRegK_mk ℂ (evToK_kacH hb u v)
  have hinclj : incl.comp j = algebraMap ℂ[X] (RatFunc ℂ) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [j, incl]
    · simp [j, incl, xA]
  have hevj : ev.comp j = Polynomial.evalRingHom b := by
    apply Polynomial.ringHom_ext
    · intro z
      simp only [j, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
        coe_evalRingHom, eval_C]
      exact evRegK_mk ℂ (evToK_C (K := ℂ) (b := b) z)
    · simp only [j, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
        coe_evalRingHom, eval_X]
      exact evRegK_mk ℂ (evToK_X (K := ℂ) (b := b))
  have hnumX : Fnum (kacC (RatFunc.X : RatFunc ℂ)) (kacH u v RatFunc.X) N =
      (numR (C cA) X (C dA) N).map incl := by
    have := map_numR (Polynomial.mapRingHom incl) (C cA) (X : A[X]) (C dA) N
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
    rw [this]
    rfl
  have hdetX : (gramPoly (kacC (RatFunc.X : RatFunc ℂ)) N).det = (detR (C cA) X N).map incl := by
    have := map_detR (Polynomial.mapRingHom incl) (C cA) (X : A[X]) N
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
    rw [this]
    rfl
  have hnumb : Fnum (kacC b) (kacH u v b) N = (numR (C cA) X (C dA) N).map ev := by
    have := map_numR (Polynomial.mapRingHom ev) (C cA) (X : A[X]) (C dA) N
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
    rw [this, hevc, hevd]
    rfl
  have hdetb : (gramPoly (kacC b) N).det = (detR (C cA) X N).map ev := by
    have := map_detR (Polynomial.mapRingHom ev) (C cA) (X : A[X]) N
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
    rw [this, hevc]
    rfl
  have hdet0 : algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ))
      (gramPoly (kacC (RatFunc.X : RatFunc ℂ)) N).det ≠ 0 := fun h0 =>
    gramPoly_det_ne_zero _ N
      ((map_eq_zero_iff _ (IsFractionRing.injective (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ)))).1 h0)
  have hidX : Fnum (kacC (RatFunc.X : RatFunc ℂ)) (kacH u v RatFunc.X) N *
        Q.map (algebraMap ℂ[X] (RatFunc ℂ)) =
      P.map (algebraMap ℂ[X] (RatFunc ℂ)) * (gramPoly (kacC (RatFunc.X : RatFunc ℂ)) N).det := by
    apply IsFractionRing.injective (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ))
    rw [map_mul, map_mul, ← hPQ, Frat]
    field_simp
  have hidA : numR (C cA) X (C dA) N * Q.map j = P.map j * detR (C cA) X N := by
    apply Polynomial.map_injective incl Subtype.val_injective
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map, hinclj,
      ← hnumX, ← hdetX]
    exact hidX
  have hidb := congrArg (Polynomial.map ev) hidA
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map, hevj,
    ← hnumb, ← hdetb] at hidb
  have hdetb0 : algebraMap ℂ[X] (RatFunc ℂ) (gramPoly (kacC b) N).det ≠ 0 := fun h0 =>
    gramPoly_det_ne_zero _ N
      ((map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).1 h0)
  refine poleOrder_eq_zero_of_mul (P := P.map (Polynomial.evalRingHom b))
    (Q := Q.map (Polynomial.evalRingHom b)) ?_ ?_
  · have h2 := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hidb
    rw [map_mul, map_mul] at h2
    rw [Frat]
    field_simp
    exact h2.trans (mul_comm _ _)
  · rw [eval_map]
    have h3 := Polynomial.hom_eval₂ Q (RingHom.id ℂ[X]) (Polynomial.evalRingHom b) (C μ)
    simp only [RingHom.comp_id, coe_evalRingHom, eval_C] at h3
    rw [← h3]
    exact hQ

/-- `Stmt_sub_orbit_regular` from Lemma 11.3 (paper.tex l.2570–2574). -/
theorem sub_orbit_regular (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_orbit_regular := by
  intro p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m ε hk hm μ hμ N
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  exact poleOrder_zero_of_jointRegular hb0 _ _ N μ
    (lem_joint_holomorphicity_of_cited hK hH p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m ε hk hm
      N μ hμ)

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_orbit_regular := sub_orbit_regular hK hH

end Virasoro
