import Virasoro.Proofs.P2Sec13Limit
import Virasoro.Proofs.P2Sec9OrbitReg

/-!
# Lemma 13.1: the limits of the Verma terms of (13.2) (paper.tex l.3029–3034)

"By Lemma 11.3 the remaining terms are regular at `τ = 0` and converge to
`F_N(c⋆,μ,d⋆)` and `F_{N-R₁S₁}(c⋆,ν₁,d⋆)`."  Lemma 11.3 writes `F_N(c(b),Δ,d(b)) = P/Q` with
`P, Q ∈ ℂ[b][Δ]`, `Q(b⋆,μ) ≠ 0`.  Along the curve `Δ = h_{u,v}(b)` this is the rational function
`P(b,h_{u,v}(b))/Q(b,h_{u,v}(b))` of `b`, regular at `b⋆`.
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- An identity `F_N(c(b),Δ,h_{u,v}(b)) Q = P` over `ℂ(b)` specializes at every `b ≠ 0`
(l.2571–2573; the computation of `poleOrder_zero_of_jointRegular`). -/
theorem joint_specialize {b : ℂ} (hb : b ≠ 0) (u v : ℤ) (N : ℕ) {P Q : ℂ[X][X]}
    (hPQ : Frat (kacC (RatFunc.X : RatFunc ℂ)) (kacH u v (RatFunc.X : RatFunc ℂ)) N *
        algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
          (Q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) =
      algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))) :
    Frat (kacC b) (kacH u v b) N * algebraMap ℂ[X] (RatFunc ℂ) (Q.map (evalRingHom b)) =
      algebraMap ℂ[X] (RatFunc ℂ) (P.map (evalRingHom b)) := by
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
  have h2 := congrArg (algebraMap ℂ[X] (RatFunc ℂ)) hidb
  rw [map_mul, map_mul] at h2
  rw [Frat]
  field_simp
  exact h2.trans (mul_comm _ _)

/-- A rational function `f` with `f Q = P`, `Q(a) ≠ 0`, is regular at `a` with value
`P(a)/Q(a)`. -/
theorem value_of_mul {f : RatFunc ℂ} {a : ℂ} {P Q : ℂ[X]}
    (h : f * algebraMap ℂ[X] (RatFunc ℂ) Q = algebraMap ℂ[X] (RatFunc ℂ) P)
    (hQ : Q.eval a ≠ 0) : RegAt a f ∧ evalAt a f = P.eval a / Q.eval a := by
  have hQ0 : algebraMap ℂ[X] (RatFunc ℂ) Q ≠ 0 := by
    intro h0
    apply hQ
    rw [(map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).1 h0, eval_zero]
  have e : f = algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q :=
    eq_div_of_mul_eq hQ0 h
  rw [e]
  exact ⟨regAt_div a P hQ, evalAt_div a P hQ⟩

/-- A polynomial `P ∈ ℂ[b][Δ]` along the curve `Δ = h_{u,v}(b)` is a rational function of `b`,
regular at every `b ≠ 0`, with value `P(b,h_{u,v}(b))`. -/
theorem evToK_curve {b : ℂ} (hb : b ≠ 0) (P : ℂ[X][X]) (u v : ℤ) :
    EvToK b ((P.map (algebraMap ℂ[X] (RatFunc ℂ))).eval (kacH u v (RatFunc.X : RatFunc ℂ)))
      ((P.map (evalRingHom b)).eval (kacH u v b)) := by
  let A := regSubK ℂ b
  let incl : A →+* RatFunc ℂ := (regSubK ℂ b).val.toRingHom
  let ev : A →+* ℂ := evRegK ℂ b
  let hA : A := ⟨kacH u v RatFunc.X, (evToK_kacH hb u v).1⟩
  let xA : A := ⟨RatFunc.X, (evToK_X (K := ℂ) (b := b)).1⟩
  let j : ℂ[X] →+* A := (Polynomial.aeval xA : ℂ[X] →ₐ[ℂ] A).toRingHom
  have hevh : ev hA = kacH u v b := evRegK_mk ℂ (evToK_kacH hb u v)
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
  have h := evToK_of_reg (b := b) (Polynomial.eval₂ j hA P)
  have e1 : ((Polynomial.eval₂ j hA P : A) : RatFunc ℂ) =
      (P.map (algebraMap ℂ[X] (RatFunc ℂ))).eval (kacH u v (RatFunc.X : RatFunc ℂ)) := by
    have := Polynomial.hom_eval₂ P j incl hA
    rw [hinclj] at this
    rw [eval_map]
    exact this
  have e2 : evRegK ℂ b (Polynomial.eval₂ j hA P) =
      (P.map (evalRingHom b)).eval (kacH u v b) := by
    have := Polynomial.hom_eval₂ P j ev hA
    rw [hevj, hevh] at this
    rw [eval_map]
    exact this
  rw [e1, e2] at h
  exact h

/-- `Stmt_sub_tau_verma_limit` (l.3029–3034), from Lemma 11.3. -/
theorem sub_tau_verma_limit_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_sub_tau_verma_limit := by
  classical
  intro p p' r s b hset k m hk hm u v hμ N
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  obtain ⟨P, Q, hQ, hPQ⟩ := lem_joint_holomorphicity_of_cited hK hH p p' r s b hp2 hp2' hcop hb
    hr0 hr hs0 hs k m true hk hm N (kacH u v b) hμ
  have hPQ' : Frat (kacC (RatFunc.X : RatFunc ℂ))
        (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (RatFunc.X : RatFunc ℂ)) N *
        algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
          (Q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) =
      algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) := hPQ
  set nK : RatFunc ℂ :=
    (P.map (algebraMap ℂ[X] (RatFunc ℂ))).eval (kacH u v (RatFunc.X : RatFunc ℂ)) with hnK
  set dK : RatFunc ℂ :=
    (Q.map (algebraMap ℂ[X] (RatFunc ℂ))).eval (kacH u v (RatFunc.X : RatFunc ℂ)) with hdK
  have hQb : (Q.map (evalRingHom b)).eval (kacH u v b) ≠ 0 := by
    rw [eval_map]
    have h3 := Polynomial.hom_eval₂ Q (RingHom.id ℂ[X]) (Polynomial.evalRingHom b)
      (C (kacH u v b))
    simp only [RingHom.comp_id, coe_evalRingHom, eval_C] at h3
    rw [← h3]
    exact hQ
  have key : ∀ b' : ℂ, b' ≠ 0 → (Q.map (evalRingHom b')).eval (kacH u v b') ≠ 0 →
      RegAt b' (nK / dK) ∧ evalAt b' (nK / dK) =
        FvalAt (kacC b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b') N (kacH u v b') := by
    intro b' hb' hne
    have h1 := (evToK_curve hb' P u v).div (evToK_curve hb' Q u v) hne
    obtain ⟨-, h2⟩ := value_of_mul (joint_specialize hb' _ _ N hPQ') hne
    refine ⟨h1.1, ?_⟩
    have h3 : evalAt b' (nK / dK) = _ := h1.2
    rw [h3]
    exact h2.symm
  have hdK0 : dK ≠ 0 := by
    intro h0
    have h1 := evToK_curve hb0 Q u v
    rw [← hdK, h0] at h1
    exact hQb (evToK_uniq h1 evToK_zero)
  refine ⟨nK / dK, dK.num.roots.toFinset, fun b' hb' _ hS₀ => key b' hb' fun h0 => hS₀ ?_,
    key b hb0 hQb⟩
  have h1 := evToK_curve hb' Q u v
  rw [← hdK, h0] at h1
  obtain ⟨h1a, h1b⟩ := h1
  rw [Multiset.mem_toFinset, mem_roots (RatFunc.num_ne_zero hdK0)]
  have h2 : dK.num.eval b' / dK.denom.eval b' = 0 := h1b
  have h3 : dK.denom.eval b' ≠ 0 := h1a
  rcases div_eq_zero_iff.1 h2 with h | h
  · exact h
  · exact absurd h h3

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_tau_verma_limit := sub_tau_verma_limit_of_cited hK hH

end Virasoro.P2
