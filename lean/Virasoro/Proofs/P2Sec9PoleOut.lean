import Virasoro.Proofs.P2Sec9TopF
import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Proofs.Sec5Sharp
import Virasoro.Proofs.Sec4Ising
import Virasoro.Proofs.P2Sec9Main

/-!
# Theorem 9.1(ii), converse half (paper.tex l.2578–2606)

If `d ∉ ℱ^±_{p,p'}(r,s)`, one of `τ⁺₁(d) = 𝒫_{r,s}(b⋆,d)`, `τ⁻₁(d) = 𝒫_{p-r,p'-s}(b⋆,d)` is
nonzero (Lemma 11.1(iii)).  Both levels `ℓ_min < ℓ_max` lie in the first Jantzen window
(Lemma 10.3(iv)), and by the top-layer residue formula `F_N(c⋆,Δ,d)` has a simple pole at
`Δ = λ` for `N = ℓ_min` (when `τ^small_1(d) ≠ 0`) or `N = ℓ_max` (when `τ^small_1(d) = 0`).
-/

namespace Virasoro

open Verma Polynomial

/-- The setting of Theorem 5.8 from the cited Jantzen layers at the node `μ_0 = λ` of the
orbit. -/
theorem jantzenLayers_of_orbit (hJ : Cited_JantzenLayersOrbit) : Cited_JantzenLayers := by
  intro p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hset : MinimalSetting p p' r s b := ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩
  have hμ : muOrb p p' r s true 0 = kacH r s b := by
    rw [kacH_momWt (by omega) (by omega) hb, muOrb]
    congr 1
    simp [nOrb]
  have h := hJ p p' r s b hset true 0
  simp only [OrbitLayerSetting] at h
  rw [hμ] at h
  obtain ⟨wp, wm, ⟨hsing, hlayer⟩, -⟩ := h
  refine ⟨wp, wm, fun k hk => ?_, hlayer⟩
  have hk0 : k ≠ 0 := by omega
  have e1 : ellOrb p p' r s true (0 + k) - ellOrb p p' r s true 0 = ellPlus p p' r s k := by
    simp [ellOrb, hk0]
  have e2 : ellOrb p p' r s false (0 + k) - ellOrb p p' r s true 0 = ellMinus p p' r s k := by
    simp [ellOrb, hk0]
  have := hsing k hk
  rw [e1, e2] at this
  exact this

/-- The two cases of paper.tex l.2590–2600. -/
theorem window_pole {c h d : ℂ} {ℓ₁ ℓ₂ : ℕ} (x₁ : Nat.Partition ℓ₁ → ℂ)
    (x₂ : Nat.Partition ℓ₂ → ℂ) (hlt : ℓ₁ < ℓ₂) (hγ₁ : jform c h ℓ₁ 1 x₁ x₁ ≠ 0)
    (hγ₂ : jform c h ℓ₂ 1 x₂ x₂ ≠ 0)
    (hτ : (torusPolyForm c h x₁).eval d ≠ 0 ∨ (torusPolyForm c h x₂).eval d ≠ 0) :
    (blockPoly c h 1 ℓ₁ x₁ ℓ₁ + blockPoly c h 1 ℓ₂ x₂ ℓ₁).eval d ≠ 0 ∨
      (blockPoly c h 1 ℓ₁ x₁ ℓ₂ + blockPoly c h 1 ℓ₂ x₂ ℓ₂).eval d ≠ 0 := by
  by_cases h1 : (torusPolyForm c h x₁).eval d = 0
  · right
    have h2 := hτ.resolve_left (not_not.2 h1)
    rw [eval_add, eval_blockPoly, eval_blockPoly, if_pos hlt.le, if_pos le_rfl, h1, mul_zero,
      zero_mul, zero_add, Nat.sub_self, Fval_zero, mul_one]
    exact mul_ne_zero (inv_ne_zero hγ₂) h2
  · left
    rw [eval_add, eval_blockPoly, eval_blockPoly, if_pos le_rfl, if_neg (by omega), add_zero,
      Nat.sub_self, Fval_zero, mul_one]
    exact mul_ne_zero (inv_ne_zero hγ₁) h1

/-- The converse half of Theorem 9.1(ii) under the labelling `p'r + ps < pp'`. -/
theorem pole_outside_minimal (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) (d : ℂ)
    (hd : genP r s b d ≠ 0 ∨ genP (p - r) (p' - s) b d ≠ 0) :
    ∃ N : ℕ, poleOrder (Frat (kacC b) d N) (kacH r s b) ≠ 0 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  obtain ⟨wp, wm, hsing, hjan, -, -⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsing, hjan⟩
  have hcp : pbwCoord (ellPlus p p' r s 1) (comp (ellPlus p p' r s 1) (wp 1)) = wp 1 :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing 1 le_rfl).1.2.1)
  have hcm : pbwCoord (ellMinus p p' r s 1) (comp (ellMinus p p' r s 1) (wm 1)) = wm 1 :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing 1 le_rfl).2.2.1)
  have e1 : ellPlus p p' r s 1 = r * s := by simp [ellPlus]
  have e2 : ellMinus p p' r s 1 = (p - r) * (p' - s) := by simp [ellMinus]
  have h12 := ell_one_lt_two (p := p) (p' := p') hr hrp hs hsp
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt (le_refl 1)
  obtain ⟨ap, hap, hτp⟩ := tau_eq_genP hH hU hb0 hr hs rfl e1 _
    (by rw [hcp]; exact (hsing 1 le_rfl).1) d
  obtain ⟨am, ham, hτm⟩ := tau_eq_genP hH hU hb0 (by omega : 0 < p - r) (by omega : 0 < p' - s)
    (kacH_reflect (by omega) (by omega) hb hrp.le hsp.le) e2 _
    (by rw [hcm]; exact (hsing 1 le_rfl).2) d
  have hτ : (torusPolyForm (kacC b) (kacH r s b)
        (comp (ellPlus p p' r s 1) (wp 1))).eval d ≠ 0 ∨
      (torusPolyForm (kacC b) (kacH r s b) (comp (ellMinus p p' r s 1) (wm 1))).eval d ≠ 0 := by
    rcases hd with h | h
    · left; rw [hτp]; exact mul_ne_zero (pow_ne_zero 2 hap) h
    · right; rw [hτm]; exact mul_ne_zero (pow_ne_zero 2 ham) h
  obtain ⟨hndp, hndm⟩ := sub_top_layer_nondeg_of_cited hI p p' r s b hset wp wm hT 1
    (max (ellPlus p p' r s 1) (ellMinus p p' r s 1)) le_rfl min_le_max h12
  have hγp := (hndp _ hcp (le_max_left _ _)).1
  have hγm := (hndm _ hcm (le_max_right _ _)).1
  have key : ∀ N : ℕ, ellMin p p' r s 1 ≤ N → N < ellMin p p' r s (1 + 1) →
      (blockPoly (kacC b) (kacH r s b) 1 (ellPlus p p' r s 1)
          (comp (ellPlus p p' r s 1) (wp 1)) N +
        blockPoly (kacC b) (kacH r s b) 1 (ellMinus p p' r s 1)
          (comp (ellMinus p p' r s 1) (wm 1)) N).eval d ≠ 0 →
      poleOrder (Frat (kacC b) d N) (kacH r s b) ≠ 0 := by
    intro N h1 h2 hne0 h0
    apply hne0
    rw [← ppCoeff_Frat_window hI hset hT le_rfl h1 h2 _ _ hcp hcm d]
    exact ppCoeff_eq_zero_of_gt _ _ (by omega)
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · rcases window_pole _ _ hlt' hγp hγm hτ with h | h
    · exact ⟨_, key _ (min_le_left _ _) (lt_of_le_of_lt (le_max_left _ _) h12) h⟩
    · exact ⟨_, key _ (min_le_right _ _) (lt_of_le_of_lt (le_max_right _ _) h12) h⟩
  · rcases window_pole _ _ hlt' hγm hγp hτ.symm with h | h
    · exact ⟨_, key _ (min_le_right _ _) (lt_of_le_of_lt (le_max_right _ _) h12)
        (by rw [add_comm]; exact h)⟩
    · exact ⟨_, key _ (min_le_left _ _) (lt_of_le_of_lt (le_max_left _ _) h12)
        (by rw [add_comm]; exact h)⟩

/-- `Stmt_sub_pole_outside` (paper.tex l.2578–2606) from Lemma 11.1(iii), the cited Jantzen
layers, the top-layer residue formula and the normalization (6.2). -/
theorem sub_pole_outside (hJ : Cited_JantzenLayersOrbit) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) : Stmt_sub_pole_outside := by
  intro p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs d hd
  have h3 := (lem_fusion_injective p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs).2.2 d
  have hne : genP r s b d ≠ 0 ∨ genP (p - r) (p' - s) b d ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hd (h3.1 hcon)
  by_cases hn : p' * r + p * s < p * p'
  · exact pole_outside_minimal (jantzenLayers_of_orbit hJ) hI hH hU
      ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn, hb⟩ d hne
  · have hne' : p' * r + p * s ≠ p * p' := by
      intro h
      have hz : (p' : ℤ) * r = p * ((p' : ℤ) - s) := by
        have : ((p' * r + p * s : ℕ) : ℤ) = ((p * p' : ℕ) : ℤ) := by rw [h]
        push_cast at this
        linarith
      have h0 := Int.eq_zero_of_abs_lt_dvd (coprime_two_dvd hcop hz).1
        (abs_lt.2 ⟨by omega, by omega⟩)
      omega
    have hn' : p' * (p - r) + p * (p' - s) < p * p' := by
      rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm p' p]
      have h1 : p' * r < p * p' := by
        rw [Nat.mul_comm p p']; exact Nat.mul_lt_mul_of_pos_left hr (by omega)
      have h2 : p * s < p * p' := Nat.mul_lt_mul_of_pos_left hs (by omega)
      omega
    have h := pole_outside_minimal (jantzenLayers_of_orbit hJ) hI hH hU
      ⟨hp2, hp2', hcop, (by omega : 0 < p - r), (by omega : p - r < p), (by omega : 0 < p' - s),
        (by omega : p' - s < p'), hn', hb⟩ d
      (by rw [Nat.sub_sub_self hr.le, Nat.sub_sub_self hs.le]; exact hne.symm)
    rw [← kacH_reflect (by omega) (by omega) hb hr.le hs.le] at h
    exact h

example (hJ : Cited_JantzenLayersOrbit) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) : Stmt_sub_pole_outside :=
  sub_pole_outside hJ hI hH hU

end Virasoro
