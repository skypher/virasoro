import Virasoro.Proofs.Sec8Smith7
import Virasoro.Proofs.Sec9Theta10
import Virasoro.Proofs.Ising4
import Virasoro.Statements.Sec9

/-!
# Proposition 9.1: the level-ten Smith profile at `Δ = 1/16`

`M(1/2,33/16)` and `M(1/2,65/16)` have singular vectors `ψ₈`, `ψ₆` of levels `8` and `6`
(lowest radical vectors; Kac determinant).  `χ₁₀ = j_{χ₂}(ψ₈)` is singular, proportional to
`j_{χ₄}(ψ₆)` (Cited_SingularUnique), so it spans `(U₂ ∩ U₄)₁₀`; below level `10` the
intersection vanishes by the pullback argument.  The Smith exponents `(0¹⁰,1³¹,2)` come from
Theorem 5.7 (levels `10, 14` and `24, 30`) and the valuation `p(8) + p(6) = 33`, and
`[x⁻²] G₁₀⁻¹` has rank one since its image lies in the one-dimensional `K₂` (Prop 5.3).
-/

namespace Virasoro

open Verma Module

set_option maxRecDepth 100000

theorem chi2_singular' :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2) 2 := by
  rw [chi2_eq]; exact chi2_singular ℂ

theorem chi4_singular' :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) 4 := by
  rw [chi4_eq]; exact chi4_singular ℂ

/-- `det G_M(1/2, h_a(b₀) + ℓ) ≠ 0` when no label of level `M` has that weight. -/
theorem det_ne_shift (hK : Cited_KacDeterminant) (a : Label) (ℓ : ℕ) {M : ℕ}
    (hno : ∀ g ∈ labels M, isingKey g ≠ isingKey a + 48 * (ℓ : ℤ)) :
    (gram (1 / 2 : ℂ) (kacHL a b0 + (ℓ : ℂ)) M).det ≠ 0 := by
  have h := gram_det_ne_of_labels hK (b := b0) (z := kacHL a b0 + (ℓ : ℂ)) b0_ne_zero (M := M)
    fun g hg => by
      rw [kacHL_b0_cast, kacHL_b0_cast, Ne, isingDelta_cast_shift_iff]
      exact hno g hg
  rwa [kacC_b0'] at h

theorem no_label_33_16 : ∀ M ∈ Finset.range 8, ∀ g ∈ labels M,
    isingKey g ≠ isingKey (1, 2) + 48 * ((2 : ℕ) : ℤ) := by decide

theorem no_label_65_16 : ∀ M ∈ Finset.range 6, ∀ g ∈ labels M,
    isingKey g ≠ isingKey (2, 2) + 48 * ((4 : ℕ) : ℤ) := by decide

theorem kacHL_22_b0 : kacHL (2, 2) b0 = 1 / 16 := by
  rw [kacHL_b0_cast]; norm_num [isingDelta]

/-- `ψ₈`: a singular vector of level `8` in `M(1/2, 1/16 + 2)`. -/
theorem exists_psi8 (hK : Cited_KacDeterminant) :
    ∃ u : Verma ℂ (1 / 2 : ℂ) ((1 / 16 : ℂ) + ((2 : ℕ) : ℂ)), IsSingular u 8 := by
  have e : (1 / 16 : ℂ) + ((2 : ℕ) : ℂ) = kacHL (1, 2) b0 + ((2 : ℕ) : ℂ) := by
    rw [kacHL_12_b0]
  refine exists_singular_of_det ?_ fun m hm => ?_
  · have h := gram_det_eq_zero_of_label hK b0_ne_zero (M := 8) (a := (4, 2)) (by decide)
    have e' : kacHL (4, 2) b0 = (1 / 16 : ℂ) + ((2 : ℕ) : ℂ) := by
      rw [kacHL_b0_cast]; norm_num [isingDelta]
    rwa [kacC_b0', e'] at h
  · rw [e]
    exact det_ne_shift hK (1, 2) 2 (no_label_33_16 m (Finset.mem_range.2 hm))

/-- `ψ₆`: a singular vector of level `6` in `M(1/2, 1/16 + 4)`. -/
theorem exists_psi6 (hK : Cited_KacDeterminant) :
    ∃ u : Verma ℂ (1 / 2 : ℂ) ((1 / 16 : ℂ) + ((4 : ℕ) : ℂ)), IsSingular u 6 := by
  have e : (1 / 16 : ℂ) + ((4 : ℕ) : ℂ) = kacHL (2, 2) b0 + ((4 : ℕ) : ℂ) := by
    rw [kacHL_22_b0]
  refine exists_singular_of_det ?_ fun m hm => ?_
  · have h := gram_det_eq_zero_of_label hK b0_ne_zero (M := 6) (a := (1, 6)) (by decide)
    have e' : kacHL (1, 6) b0 = (1 / 16 : ℂ) + ((4 : ℕ) : ℂ) := by
      rw [kacHL_b0_cast]; norm_num [isingDelta]
    rwa [kacC_b0', e'] at h
  · rw [e]
    exact det_ne_shift hK (2, 2) 4 (no_label_65_16 m (Finset.mem_range.2 hm))

/-- `U₂ ∩ U₄` vanishes below level `10`. -/
theorem U24_low (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective) :
    ∀ N : ℕ, N < 10 →
      negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2) ⊓
        negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) ⊓ level N = ⊥ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rw [eq_bot_iff]
    rintro v ⟨⟨hv2, hv4⟩, hvl⟩
    rw [Submodule.mem_bot]
    by_contra hv0
    have hW := isVirSubmodule_inf (negSpan_isVir chi2_singular') (negSpan_isVir chi4_singular')
    have hvs := isSingular_of_lowest hW (fun M hM => ih M hM (by omega)) ⟨hv2, hv4⟩ hvl hv0
    obtain ⟨h4, -⟩ := singular_pullback hI chi4_singular' hv4 hvs
    obtain ⟨-, u, hu⟩ := singular_pullback hI chi2_singular' hv2 hvs
    have hdet := det_ne_shift hK (1, 2) 2 (M := N - 2)
      (no_label_33_16 (N - 2) (Finset.mem_range.2 (by omega)))
    rw [kacHL_12_b0] at hdet
    exact not_isSingular_of_det_ne (by omega) hdet u hu

set_option maxHeartbeats 2000000 in
/-- The singular vector `χ₁₀ = j_{χ₂}(ψ₈)` spans `(U₂ ∩ U₄)₁₀`. -/
theorem U24_ten (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective)
    (hU : Cited_SingularUnique) :
    ∃ χ₁₀ : Verma ℂ (1 / 2) (1 / 16), IsSingular χ₁₀ 10 ∧
      (∀ N : ℕ, N < 10 →
        negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2) ⊓
          negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) ⊓ level N = ⊥) ∧
      negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2) ⊓
          negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) ⊓ level 10 =
        Submodule.span ℂ {χ₁₀} := by
  obtain ⟨ψ8, hψ8⟩ := exists_psi8 hK
  obtain ⟨ψ6, hψ6⟩ := exists_psi6 hK
  obtain ⟨j2, hj2i, hj2r, hj2L, -⟩ := exists_embedding hI chi2_singular'
  obtain ⟨j4, hj4i, hj4r, hj4L, -⟩ := exists_embedding hI chi4_singular'
  have hχ : IsSingular (j2 ψ8) 10 := isSingular_map rfl j2 hj2i hj2L hψ8
  have hχ' : IsSingular (j4 ψ6) 10 := isSingular_map rfl j4 hj4i hj4L hψ6
  have hmem2 : j2 ψ8 ∈ negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2) := by
    rw [← hj2r]; exact ⟨ψ8, rfl⟩
  have hmem4' : j4 ψ6 ∈ negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) := by
    rw [← hj4r]; exact ⟨ψ6, rfl⟩
  obtain ⟨a, ha⟩ := hU _ _ 10 _ _ hχ hχ'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hχ'.1 (by rw [ha, zero_smul])
  have hmem4 : j2 ψ8 ∈ negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4) := by
    have : j2 ψ8 = a⁻¹ • j4 ψ6 := by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem4'
  refine ⟨j2 ψ8, hχ, U24_low hK hI, le_antisymm ?_ ?_⟩
  · rintro v ⟨⟨hv2, hv4⟩, hvl⟩
    by_cases hv0 : v = 0
    · rw [hv0]; exact zero_mem _
    have hW := isVirSubmodule_inf (negSpan_isVir chi2_singular') (negSpan_isVir chi4_singular')
    have hvs := isSingular_of_lowest hW (fun M hM => U24_low hK hI M hM) ⟨hv2, hv4⟩ hvl hv0
    obtain ⟨b, hb⟩ := hU _ _ 10 _ _ hχ hvs
    rw [hb]
    exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨⟨hmem2, hmem4⟩, mem_level_of_L_zero hχ.2.1⟩

theorem labels10_h0 : ((labels 10).filter fun g => kacHL g b0 = kacHL ((1, 2) : Label) b0) =
    {(1, 2), (2, 2)} := by
  classical
  rw [Finset.filter_congr (q := fun g : Label => isingKey g = isingKey (1, 2))
    (fun g _ => by rw [kacHL_b0_cast, kacHL_b0_cast, isingDelta_cast_eq_iff])]
  decide

theorem card_partition_six : Fintype.card (Nat.Partition 6) = 11 := by
  rw [card_partition_of_isEnum (isEnum_decWords 6 (by decide) (by unfold PosWord; decide))]
  decide

theorem card_partition_eight : Fintype.card (Nat.Partition 8) = 22 := by
  rw [card_partition_of_isEnum (isEnum_decWords 8 (by decide) (by unfold PosWord; decide))]
  decide

theorem card_partition_ten : Fintype.card (Nat.Partition 10) = 42 := by
  rw [card_partition_of_isEnum (isEnum_decWords 10 (by decide +kernel)
    (by unfold PosWord; decide +kernel))]
  decide

/-- The local Smith exponents of `G₁₀(1/2, 1/16 + x)`. -/
theorem smith10 (hK : Cited_KacDeterminant) (hJ : Cited_JantzenLayers) :
    IsSmith (gramLocal (1 / 2 : ℂ) (1 / 16) 10)
      (Multiset.replicate 10 0 + Multiset.replicate 31 1 + {2}) := by
  classical
  have hb : b0 ^ 2 = -((4 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by rw [b0_sq]; norm_num
  obtain ⟨wp, wm, hsing, -, hcount, -⟩ := thm_jantzen_smith hJ 3 4 1 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) b0 hb
  have hh : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0 = 1 / 16 := by
    rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]
  have hG : gramLocal (kacC b0) (kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0) 10
      = gramLocal (1 / 2 : ℂ) (1 / 16) 10 := by rw [kacC_b0', hh]
  obtain ⟨s, hs⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b0)
    (kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0) 10)
  have hl2p : ellPlus 3 4 1 2 2 = 10 := by decide
  have hl2m : ellMinus 3 4 1 2 2 = 14 := by decide
  have hl3p : ellPlus 3 4 1 2 3 = 24 := by decide
  have hl3m : ellMinus 3 4 1 2 3 = 30 := by decide
  obtain ⟨hp2, hm2⟩ := hsing 2 (by norm_num)
  obtain ⟨hp3, hm3⟩ := hsing 3 (by norm_num)
  rw [hl2p] at hp2
  rw [hl2m] at hm2
  rw [hl3p] at hp3
  rw [hl3m] at hm3
  have hI2 : (negSpan (wp 2) ⊔ negSpan (wm 2)) ⊓ level 10 = Submodule.span ℂ {wp 2} := by
    apply le_antisymm
    · rintro v ⟨hv, hvl⟩
      obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.1 hv
      rw [← pbwCoord_comp_of_mem_level hvl, map_add, map_add,
        comp_negSpan_eq_zero (mem_level_of_L_zero hm2.2.1) (by norm_num) hb', map_zero, add_zero]
      exact pbwCoord_comp_negSpan_mem (mem_level_of_L_zero hp2.2.1) ha
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨Submodule.mem_sup_left (Submodule.subset_span ⟨[], by simp [negOp_nil_smul]⟩),
        mem_level_of_L_zero hp2.2.1⟩
  have hI3 : (negSpan (wp 3) ⊔ negSpan (wm 3)) ⊓ level 10 = ⊥ := by
    by_contra hne
    have := (inf_level_ne_bot_iff hp3 hm3).1 hne
    norm_num at this
  have h2 : Multiset.card (s.filter (2 ≤ ·)) = 1 := by
    rw [hcount 10 s hs 2 (by norm_num), hI2, finrank_span_singleton hp2.1]
  have h3 : Multiset.card (s.filter (3 ≤ ·)) = 0 := by
    rw [hcount 10 s hs 3 (by norm_num), hI3, finrank_bot]
  have hsum : s.sum = 33 := by
    have h1 := (smith_main hs).1
    rw [gramLocal_det_order_kac hK b0_ne_zero 10] at h1
    have e : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0 = kacHL ((1, 2) : Label) b0 := rfl
    rw [e, labels10_h0] at h1
    rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h1
    have e8 : (10 - Label.lvl (1, 2)) = 8 := rfl
    have e6 : (10 - Label.lvl (2, 2)) = 6 := rfl
    rw [e8, e6, card_partition_eight, card_partition_six] at h1
    exact_mod_cast h1.symm
  have hcard : Multiset.card s = 42 := by
    obtain ⟨e, -, -, -, -, -, rfl⟩ := hs
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, card_partition_ten]
  have hle : ∀ x ∈ s, x ≤ 2 := by
    intro x hx
    by_contra hx2
    have hmem : x ∈ s.filter (3 ≤ ·) := Multiset.mem_filter.2 ⟨hx, by omega⟩
    have := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hmem⟩
    omega
  have h1 : Multiset.card (s.filter (1 ≤ ·)) = 31 + 1 := by
    have := sum_filter_card s 2 hle
    rw [hsum] at this
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ 2 by norm_num), Finset.Icc_self,
      Finset.sum_singleton] at this
    rw [h2] at this
    omega
  have hs_eq := multiset_eq_012 s 10 31 1 h3 h2 h1 (by rw [hcard])
  rw [← hG, show Multiset.replicate 10 0 + Multiset.replicate 31 1 + ({2} : Multiset ℕ)
      = Multiset.replicate 10 0 + Multiset.replicate 31 1 + Multiset.replicate 1 2 from rfl,
    ← hs_eq]
  exact hs

/-- Proposition 9.1 (`prop:level-ten-smith`).

Paper label: prop:level-ten-smith -/
theorem prop_level_ten_smith (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective)
    (hU : Cited_SingularUnique) (hJ : Cited_JantzenLayers) : Stmt_prop_level_ten_smith := by
  unfold Stmt_prop_level_ten_smith
  dsimp only
  set G := gramLocal (1 / 2 : ℂ) (1 / 16) 10 with hGdef
  have hs := smith10 hK hJ
  have hGs : G.IsSymm := gramLocal_isSymm (1 / 2 : ℂ) (1 / 16) 10
  have hdet : G.det ≠ 0 := gramLocal_det_ne_zero _ _ _
  obtain ⟨hcnt1, hcnt2, -⟩ := cross2_counts hGs hs
  have hker : finrank ℂ (LinearMap.ker (gram (1 / 2 : ℂ) (1 / 16) 10).mulVecLin) = 32 := by
    have : finrank ℂ (ker0 G) = 32 := by
      rw [← hcnt1]; decide
    rwa [ker0, coeffMat_zero_gramLocal] at this
  have hk2 : finrank ℂ (ker2 G) = 1 := by
    rw [← hcnt2]; decide
  have hp : poleOrderInv G ≤ 2 := by
    rw [(smith_main hs).2.2]; decide
  refine ⟨U24_ten hK hI hU, hker, hs, ?_⟩
  -- `[x⁻²] G⁻¹` has rank one
  have hrange : LinearMap.range (invCoeff G (-2)).mulVecLin ≤ ker2 G := by
    rintro _ ⟨w, rfl⟩
    exact (cross2_coeff hGs hdet hp w).1
  have hne : LinearMap.range (invCoeff G (-2)).mulVecLin ≠ ⊥ := by
    have hk2ne : ker2 G ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hk2
      exact absurd hk2 (by norm_num)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk2ne
    obtain ⟨Y0, hY0⟩ : ∃ Y0, u Y0 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu0 (funext hall)
    intro hb
    have hz : (invCoeff G (-2)).mulVec (Pi.single Y0 1) = 0 := by
      have : (invCoeff G (-2)).mulVecLin (Pi.single Y0 1) ∈ LinearMap.range
          (invCoeff G (-2)).mulVecLin := ⟨_, rfl⟩
      rw [hb] at this
      exact (Submodule.mem_bot ℂ).1 this
    have h0 := (cross2_coeff hGs hdet hp (Pi.single Y0 1)).2 u hu 0 (by
      rw [hz, Matrix.mulVec_zero, Matrix.mulVec_zero, neg_zero])
    rw [hz] at h0
    simp [cross2, dotProduct_single] at h0
    exact hY0 h0.symm
  unfold Matrix.rank
  apply le_antisymm
  · rw [← hk2]
    exact Submodule.finrank_mono hrange
  · exact Nat.one_le_iff_ne_zero.2 fun h0 => hne (Submodule.finrank_eq_zero.1 h0)

end Virasoro
