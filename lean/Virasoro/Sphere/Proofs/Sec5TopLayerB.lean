import Virasoro.Sphere.Proofs.Sec5TopB

/-!
# Sphere paper Theorem 5.3: equation (5.1), and the theorem from its `H`-coefficient part

`sphere/paper.tex` l.1571–1582: the two blocks of `[x^{-k}] G_{N'}⁻¹` contracted with the
vectors `γ_Y` give `∑_± π^±(Δ₄,Δ₃) π^±(Δ₁,Δ₂)/γ^± · ℬ_{N'-ℓ^±}(c⋆,μ^±,Δ_i)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Verma Polynomial

/-- The inverse Shapovalov matrix over `ℂ(Δ₁,…,Δ₄)` at a complex point. -/
theorem gramK_inv (c μ : ℂ) (M : ℕ) :
    (gram (cK c) (cK μ) M)⁻¹ = ((gram c μ M)⁻¹).map (algebraMap ℂ K4) := by
  have hg : gram (cK c) (cK μ) M = (gram c μ M).map (algebraMap ℂ K4) :=
    gram_map (algebraMap ℂ K4) c μ M
  have hd : ((gram c μ M).map (algebraMap ℂ K4)).det = algebraMap ℂ K4 (gram c μ M).det :=
    (RingHom.map_det (algebraMap ℂ K4) (gram c μ M)).symm
  have ha : ((gram c μ M).map (algebraMap ℂ K4)).adjugate =
      ((gram c μ M).adjugate).map (algebraMap ℂ K4) :=
    (RingHom.map_adjugate (algebraMap ℂ K4) (gram c μ M)).symm
  rw [hg, Matrix.inv_def, Matrix.inv_def, hd, ha, Ring.inverse_eq_inv', Ring.inverse_eq_inv']
  ext Y Z
  simp [Matrix.smul_apply, map_inv₀]

theorem gramK_det_ne_zero {c μ : ℂ} {M : ℕ} (h : (gram c μ M).det ≠ 0) :
    (gram (cK c) (cK μ) M).det ≠ 0 := by
  have hg : gram (cK c) (cK μ) M = (gram c μ M).map (algebraMap ℂ K4) :=
    gram_map (algebraMap ℂ K4) c μ M
  have hd : ((gram c μ M).map (algebraMap ℂ K4)).det = algebraMap ℂ K4 (gram c μ M).det :=
    (RingHom.map_det (algebraMap ℂ K4) (gram c μ M)).symm
  rw [hg, hd]
  exact (map_ne_zero (algebraMap ℂ K4)).2 h

/-- The block of a level-`ℓ` vector with coordinates `p`, contracted with the vectors `γ_Y`. -/
theorem topBlock_gamma (c h : ℂ) (k : ℕ) {ℓ : ℕ} (p : Nat.Partition ℓ → ℂ) (N' : ℕ)
    (hdet : ℓ ≤ N' → (gram c (h + (ℓ : ℂ)) (N' - ℓ)).det ≠ 0) :
    ∑ Y, ∑ Z, gammaY (cK h) (ΔK 3) (ΔK 2) Y.word *
        cK (topBlock k ℓ (pbwCoord (c := c) (h := h) ℓ p) N' (N' - ℓ) Y Z) *
        gammaY (cK h) (ΔK 0) (ΔK 1) Z.word =
      topTermSph (Bsph (cK c) ΔK) c h N' ℓ k p := by
  classical
  unfold topTermSph
  by_cases hle : ℓ ≤ N'
  · rw [if_pos hle]
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hd := hdet hle
    revert hd
    generalize hM' : ℓ + M - ℓ = M'
    obtain rfl : M = M' := by omega
    intro hd
    set U := Umat (pbwCoord (c := c) (h := h) ℓ p) (ℓ + M) M with hU
    set Gi := (gram c (h + (ℓ : ℂ)) M)⁻¹ with hGi
    set UK := U.map (algebraMap ℂ K4) with hUK
    set GK := Gi.map (algebraMap ℂ K4) with hGK
    set a : Nat.Partition (ℓ + M) → K4 := fun Y => gammaY (cK h) (ΔK 3) (ΔK 2) Y.word with ha
    set b : Nat.Partition (ℓ + M) → K4 := fun Y => gammaY (cK h) (ΔK 0) (ΔK 1) Y.word with hb
    have hWm : (U * Gi * U.transpose).map (algebraMap ℂ K4) = UK * GK * UK.transpose := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have hlhs : ∑ Y, ∑ Z, a Y * cK (topBlock k ℓ (pbwCoord (c := c) (h := h) ℓ p) (ℓ + M) M Y Z)
        * b Z = cK (jform c h ℓ k p p)⁻¹ * (a ⬝ᵥ (UK * GK * UK.transpose).mulVec b) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Z _ => ?_
      rw [topBlock, jv_pbwCoord, Matrix.smul_apply, smul_eq_mul, ← hWm, Matrix.map_apply]
      show a Y * algebraMap ℂ K4 ((jform c h ℓ k p p)⁻¹ * (U * Gi * U.transpose) Y Z) * b Z = _
      rw [map_mul]
      ring
    have hL : Matrix.vecMul a UK = fun Z =>
        piScalar h p (ΔK 3) (ΔK 2) * gammaY (cK (h + (ℓ : ℂ))) (ΔK 3) (ΔK 2) Z.word := by
      funext Z
      exact gamma_Umat (ΔK 3) (ΔK 2) ℓ M p Z
    have hR : UK.transpose.mulVec b = fun Z =>
        piScalar h p (ΔK 0) (ΔK 1) * gammaY (cK (h + (ℓ : ℂ))) (ΔK 0) (ΔK 1) Z.word := by
      rw [Matrix.mulVec_transpose]
      funext Z
      exact gamma_Umat (ΔK 0) (ΔK 1) ℓ M p Z
    have hev : RatFunc.eval (RingHom.id K4) (cK (h + (ℓ : ℂ))) (Bsph (cK c) ΔK M) =
        ∑ Y, ∑ Z, gammaY (cK (h + (ℓ : ℂ))) (ΔK 3) (ΔK 2) Y.word * GK Y Z *
          gammaY (cK (h + (ℓ : ℂ))) (ΔK 0) (ΔK 1) Z.word := by
      have := evalAt_Bsph ΔK (gramK_det_ne_zero hd)
      rw [gramK_inv] at this
      exact this
    rw [hlhs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hL, hR,
      hev]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Z _ => ?_
    ring
  · rw [if_neg hle]
    have hU : Umat (pbwCoord (c := c) (h := h) ℓ p) N' (N' - ℓ) = 0 := by
      ext Y Z
      have hl := negOp_smul_mem_level (c := c) (h := h) (ℓ := ℓ) (v := pbwCoord ℓ p) ⟨p, rfl⟩
        Z.word
      rw [word_sum'] at hl
      simp only [Umat, Matrix.of_apply, Matrix.zero_apply]
      rw [comp_of_mem_level_ne (by omega) hl]
      rfl
    simp [topBlock, hU]

/-- The `H`-part of Theorem 5.3 (sphere/paper.tex l.1584–1604, equation (5.2)): for `k ≥ 1`
and `ℓ_k ≤ N < ℓ_{k+1}`, the coefficient of `(Δ-λ)^{-k}` of `H_N(c⋆,Δ,Δ_i)` is
`∑_± π^±_k(Δ₄,Δ₃) π^±_k(Δ₁,Δ₂)/γ^±_k · H_{N-ℓ^±_k}(c⋆,μ^±_k,Δ_i)`. -/
def Stmt_sub_top_layer_Hcoeff : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → ellMin p p' r s k ≤ N → N < ellMin p p' r s (k + 1) →
        ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            ppCoeff (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) k =
              topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N
                  (ellPlus p p' r s k) k xp +
                topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N
                  (ellMinus p p' r s k) k xm

/-- Equation (5.1) of Theorem 5.3 at every level `N' ≤ N` (sphere/paper.tex l.1572–1582). -/
theorem top_layer_B (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)}
    (hT : TopLayerSetting p p' r s b wp wm) {k N : ℕ} (hk : 1 ≤ k)
    (hN1 : ellMin p p' r s k ≤ N) (hN2 : N < ellMin p p' r s (k + 1))
    (xp : Nat.Partition (ellPlus p p' r s k) → ℂ) (xm : Nat.Partition (ellMinus p p' r s k) → ℂ)
    (hxp : Verma.pbwCoord (ellPlus p p' r s k) xp = wp k)
    (hxm : Verma.pbwCoord (ellMinus p p' r s k) xm = wm k) (N' : ℕ) (hN' : N' ≤ N) :
    ppCoeff (Bsph (cK (kacC b)) ΔK N') (cK (kacH r s b)) k =
      topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N' (ellPlus p p' r s k) k xp +
        topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N' (ellMinus p p' r s k) k
          xm := by
  classical
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  have hJ := hT.2 k hk
  have hsing := hT.1 k hk
  obtain ⟨hndp, hndm⟩ :=
    sub_top_layer_nondeg_of_cited hI p p' r s b hset' wp wm hT k N hk hN1 hN2
  have hjN : jDepth p p' r s N = k := jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2
  have hpo := poleOrderInv_eq_jDepth hset' hT N'
  rw [ppCoeff_BsphK_top _ _ _ _ (by rw [hpo, ← hjN]; exact jDepth_mono p p' r s hN')]
  by_cases hlow : ellMin p p' r s k ≤ N'
  · have htop : ∃ s' : Multiset ℕ,
        IsSmith (gramLocal (kacC b) (kacH r s b) N') s' ∧ s'.sup = k := by
      obtain ⟨e, he⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH r s b) N')
      refine ⟨e, he, ?_⟩
      rw [← (smith_main he).2.2, hpo]
      exact jDepth_eq_of_range hp hp' hr hrp hs hsp hk hlow (lt_of_le_of_lt hN' hN2)
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
        exact (hndp xp hxp (le_trans hle hN')).1)
      (fun hle => by
        rw [jv_pbwCoord]
        exact (hndm xm hxm (le_trans hle hN')).1)
      (fun hle => (hndp xp hxp (le_trans hle hN')).2 _ (by omega))
      (fun hle => (hndm xm hxm (le_trans hle hN')).2 _ (by omega))]
    simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]
    rw [topBlock_gamma _ _ k xp N' fun hle => (hndp xp hxp (le_trans hle hN')).2 _ (by omega),
      topBlock_gamma _ _ k xm N' fun hle => (hndm xm hxm (le_trans hle hN')).2 _ (by omega)]
  · have hlt' : jDepth p p' r s N' < k := by
      unfold jDepth
      rw [Finset.sup_lt_iff (by rw [Nat.bot_eq_zero]; omega : (⊥ : ℕ) < k)]
      intro i hi
      rw [Finset.mem_filter, Finset.mem_Icc] at hi
      by_contra hik
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hik)
      have := ellMin_mono (p := p) (p' := p') hr hrp hs hsp hk m
      have h2 : ellMin p p' r s (k + m) ≤ N' := hi.2
      omega
    have hzero : invCoeff (gramLocal (kacC b) (kacH r s b) N') (-(k : ℤ)) = 0 := by
      ext Y Y'
      have h1 := matOrdGE_inv (gramLocal (kacC b) (kacH r s b) N') Y Y'
      rw [hpo] at h1
      exact h1.coeff_eq_zero (by omega)
    have hlp : ¬ ellPlus p p' r s k ≤ N' := fun h1 => hlow (le_trans (min_le_left _ _) h1)
    have hlm : ¬ ellMinus p p' r s k ≤ N' := fun h1 => hlow (le_trans (min_le_right _ _) h1)
    rw [hzero, topTermSph, if_neg hlp, topTermSph, if_neg hlm]
    simp

/-- Theorem 5.3 from its `H`-coefficient part and the cited injectivity of the singular
embedding (sphere/paper.tex l.1571–1582 for `ℬ`; torus Theorem 5.9 for the first clauses). -/
theorem thm_top_layer_of_sub (hI : Cited_VermaHomInjective) (hH : Stmt_sub_top_layer_Hcoeff) :
    Stmt_thm_top_layer := by
  intro p p' r s b hset wp wm hT k N hk hN1 hN2
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  obtain ⟨hndp, hndm⟩ :=
    sub_top_layer_nondeg_of_cited hI p p' r s b hset' wp wm hT k N hk hN1 hN2
  have hjN : jDepth p p' r s N = k := jDepth_eq_of_range hp hp' hr hrp hs hsp hk hN1 hN2
  have hBM : ∀ M ≤ N, OrdGE (expandAt (Bsph (cK (kacC b)) ΔK M) (cK (kacH r s b)))
      (-(k : ℤ)) := by
    intro M hM
    refine (ordGE_expandAt_BsphK (kacC b) (kacH r s b) M).mono ?_
    rw [poleOrderInv_eq_jDepth hset' hT M]
    have := jDepth_mono p p' r s hM
    omega
  exact ⟨hjN, hndp, hndm, fun xp xm hxp hxm =>
    ⟨⟨poleOrder_le_of_ordGE (hBM N le_rfl),
        top_layer_B hI hset' hT hk hN1 hN2 xp xm hxp hxm N le_rfl⟩,
      ⟨poleOrder_le_of_ordGE (ordGE_expandAt_Hsph _ _ _ N _ hBM),
        hH p p' r s b hset' wp wm hT k N hk hN1 hN2 xp xm hxp hxm⟩⟩⟩

example (hI : Cited_VermaHomInjective) (hH : Stmt_sub_top_layer_Hcoeff) : Stmt_thm_top_layer :=
  thm_top_layer_of_sub hI hH

end Virasoro.Sphere
