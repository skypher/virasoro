import Virasoro.Proofs.Sec5TopLayerFinal
import Virasoro.Proofs.Sec6DDeriv
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.IsingAux
import Virasoro.Proofs.LevelComp
import Virasoro.Cited2

/-!
# The top-layer residue formula for `F_N` at a complex external weight

The proof of Theorem 9.1 (paper.tex l.2585–2603) applies the top-layer residue formula of
Theorem 5.9 to `F_N(c⋆,Δ,d)` at a complex `d`:
`[(Δ-λ)^{-k}] F_{N'}(c⋆,Δ,d) = ∑_± τ^±_k(d)/γ^±_k · F_{N'-ℓ^±_k}(c⋆,μ^±_k,d)` for
`ℓ_k ≤ N' < ℓ_{k+1}`.  This is the identity for `F_{N'}` in the proof of Theorem 5.9
(l.871–886) with `d` a complex number; and `τ^±_1(d)` is a nonzero multiple of
`𝒫_{r,s}(b⋆,d)`, `𝒫_{p-r,p'-s}(b⋆,d)` (l.2580–2582).
-/

namespace Virasoro

open scoped LaurentSeries
open Verma Module Polynomial

/-- If `G_N(c,Δ)⁻¹` has pole order at most `k` at `Δ = a`, then
`[(Δ-a)^{-k}] F_N(c,Δ,d) = ∑ ([x^{-k}] G_N(c,a+x)⁻¹)_{Y,Y'} ρ_N(c,a,d)_{Y,Y'}`. -/
theorem ppCoeff_Frat_top (c a d : ℂ) (N k : ℕ) (hp : poleOrderInv (gramLocal c a N) ≤ k) :
    ppCoeff (Frat c d N) a k =
      (∑ Y, ∑ Y', C (invCoeff (gramLocal c a N) (-(k : ℤ)) Y Y') *
        torus (C c) (C a) (X : ℂ[X]) N Y Y').eval d := by
  classical
  have hord : MatOrdGE (invLaurent (gramLocal c a N)) (-(k : ℤ)) := fun i j =>
    (matOrdGE_inv (gramLocal c a N) i j).mono (by
      have : (poleOrderInv (gramLocal c a N) : ℤ) ≤ k := by exact_mod_cast hp
      omega)
  have h0 := mul_scaledInv (gramLocal_det_ne_zero c a N) hord
  have hc : ∀ Y Y', PowerSeries.constantCoeff (scaledInv (gramLocal c a N) k Y Y') =
      invCoeff (gramLocal c a N) (-(k : ℤ)) Y Y' := by
    intro Y Y'
    have := congrFun (congrFun (coeffMat_scaledInv (gramLocal c a N) k 0) Y) Y'
    simpa [coeffMat, PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
  rw [ppCoeff_Frat_of_scaled _ _ _ _ _ _ h0]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_torus_poly, hc]

/-- Paper.tex l.871–886: for `ℓ_k ≤ N' < ℓ_{k+1}` the trace of `[x^{-k}] G_{N'}⁻¹` against
`ρ_{N'}` is `∑_± τ^±/γ^± F_{N'-ℓ^±}(c⋆,μ^±,d)`, as polynomials in `d`. -/
theorem top_poly_eq (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)}
    (hT : TopLayerSetting p p' r s b wp wm) {k N' : ℕ} (hk : 1 ≤ k)
    (hN1 : ellMin p p' r s k ≤ N') (hN2 : N' < ellMin p p' r s (k + 1))
    (xp : Nat.Partition (ellPlus p p' r s k) → ℂ) (xm : Nat.Partition (ellMinus p p' r s k) → ℂ)
    (hxp : pbwCoord (ellPlus p p' r s k) xp = wp k)
    (hxm : pbwCoord (ellMinus p p' r s k) xm = wm k) :
    ∑ Y, ∑ Y', C (invCoeff (gramLocal (kacC b) (kacH r s b) N') (-(k : ℤ)) Y Y') *
        torus (C (kacC b)) (C (kacH r s b)) (X : ℂ[X]) N' Y Y' =
      blockPoly (kacC b) (kacH r s b) k (ellPlus p p' r s k) xp N' +
        blockPoly (kacC b) (kacH r s b) k (ellMinus p p' r s k) xm N' := by
  classical
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  have hJ := hT.2 k hk
  have hsing := hT.1 k hk
  obtain ⟨hndp, hndm⟩ :=
    sub_top_layer_nondeg_of_cited hI p p' r s b hset' wp wm hT k N' hk hN1 hN2
  have hpo := poleOrderInv_eq_jDepth hset' hT N'
  have htop : ∃ s' : Multiset ℕ,
      IsSmith (gramLocal (kacC b) (kacH r s b) N') s' ∧ s'.sup = k := by
    obtain ⟨e, he⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH r s b) N')
    refine ⟨e, he, ?_⟩
    rw [← (smith_main he).2.2, hpo]
    exact jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2
  have hχp : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s k) xp)
      (ellPlus p p' r s k) := by
    rw [hxp]
    exact hsing.1
  have hχm : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s k) xm)
      (ellMinus p p' r s k) := by
    rw [hxm]
    exact hsing.2
  have hJ' : jantzen (kacC b) (kacH r s b) k =
      negSpan (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s k) xp) ⊔
        negSpan (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s k) xm) := by
    rw [hxp, hxm]
    exact hJ
  rw [invCoeff_top_eq hI hχp hχm hne hJ' N' (N' - ellPlus p p' r s k)
    (N' - ellMinus p p' r s k) (by omega) (by omega) htop
    (fun hle => by
      rw [jv_pbwCoord]
      exact (hndp xp hxp hle).1)
    (fun hle => by
      rw [jv_pbwCoord]
      exact (hndm xm hxm hle).1)
    (fun hle => (hndp xp hxp hle).2 _ (by omega))
    (fun hle => (hndm xm hxm hle).2 _ (by omega))]
  simp only [Matrix.add_apply, C_add, add_mul, Finset.sum_add_distrib]
  rw [topBlock_trace _ _ k xp hχp N', topBlock_trace _ _ k xm hχm N']

/-- The top-layer residue formula for `F_{N'}(c⋆,Δ,d)` at a complex `d`, `ℓ_k ≤ N' < ℓ_{k+1}`. -/
theorem ppCoeff_Frat_window (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)}
    (hT : TopLayerSetting p p' r s b wp wm) {k N' : ℕ} (hk : 1 ≤ k)
    (hN1 : ellMin p p' r s k ≤ N') (hN2 : N' < ellMin p p' r s (k + 1))
    (xp : Nat.Partition (ellPlus p p' r s k) → ℂ) (xm : Nat.Partition (ellMinus p p' r s k) → ℂ)
    (hxp : pbwCoord (ellPlus p p' r s k) xp = wp k)
    (hxm : pbwCoord (ellMinus p p' r s k) xm = wm k) (d : ℂ) :
    ppCoeff (Frat (kacC b) d N') (kacH r s b) k =
      (blockPoly (kacC b) (kacH r s b) k (ellPlus p p' r s k) xp N' +
        blockPoly (kacC b) (kacH r s b) k (ellMinus p p' r s k) xm N').eval d := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  rw [ppCoeff_Frat_top _ _ _ _ _ (by
      rw [poleOrderInv_eq_jDepth hset hT N',
        jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2]),
    top_poly_eq hI hset hT hk hN1 hN2 xp xm hxp hxm]

theorem eval_blockPoly (c h : ℂ) (k ℓ : ℕ) (x : Nat.Partition ℓ → ℂ) (N' : ℕ) (d : ℂ) :
    (blockPoly c h k ℓ x N').eval d =
      if ℓ ≤ N' then
        (jform c h ℓ k x x)⁻¹ * (torusPolyForm c h x).eval d * Fval c d (h + ℓ) (N' - ℓ)
      else 0 := by
  unfold blockPoly
  split_ifs
  · rw [eval_mul, eval_mul, eval_C, eval_FpolyD]
  · rw [eval_zero]

theorem eval_torusPolyForm (c h : ℂ) {N : ℕ} (x : Nat.Partition N → ℂ) (d : ℂ) :
    (torusPolyForm c h x).eval d = torusForm c h d N x x := by
  have := map_torusForm (Polynomial.evalRingHom d) (C c) (C h) (X : ℂ[X]) N
    (fun Y => C (x Y)) (fun Y => C (x Y))
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  exact this

theorem torusForm_smul_smul (c h d a : ℂ) {N : ℕ} (u : Nat.Partition N → ℂ) :
    torusForm c h d N (a • u) (a • u) = a ^ 2 * torusForm c h d N u u := by
  simp only [torusForm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- `τ(d) = ⟨w|V_d(1)|w⟩` for a singular vector `w` of level `RS` in `M(c(b),h_{R,S}(b))` is a
nonzero multiple of `𝒫_{R,S}(b,d)` (paper.tex l.2580–2582; the normalization (6.2) and
uniqueness of singular vectors). -/
theorem tau_eq_genP (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) {b : ℂ}
    (hb : b ≠ 0) {R S : ℕ} (hR : 0 < R) (hS : 0 < S) {h : ℂ} (hh : h = kacH R S b) {ℓ : ℕ}
    (hℓ : ℓ = R * S) (x : Nat.Partition ℓ → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := h) ℓ x) ℓ) (d : ℂ) :
    ∃ a : ℂ, a ≠ 0 ∧ (torusPolyForm (kacC b) h x).eval d = a ^ 2 * genP R S b d := by
  subst hh
  subst hℓ
  obtain ⟨p, ⟨hp1, hsing⟩, -⟩ := hH R S hR hS
  obtain ⟨-, h1, hs1, htor, -⟩ := lem_regular_everywhere_of_cited hH R S hR hS p hp1 hsing b hb
  obtain ⟨a, ha⟩ := hU _ _ (R * S) _ _ hs1 hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx.1 (ha.trans (by module))
  have hxa : x = a • (fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (p Y)) := by
    have := congrArg (comp (c := kacC b) (h := kacH R S b) (R * S)) ha
    rwa [map_smul, comp_pbwCoord_same, comp_pbwCoord_same] at this
  refine ⟨a, ha0, ?_⟩
  rw [eval_torusPolyForm, hxa, torusForm_smul_smul, htor d]

end Virasoro
