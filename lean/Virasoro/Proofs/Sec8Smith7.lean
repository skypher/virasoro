import Virasoro.Proofs.Sec8Gamma7
import Virasoro.Proofs.SingularPull
import Virasoro.Proofs.Sec8NoDouble
import Virasoro.Proofs.TwoBranchA
import Virasoro.Proofs.Ising3

/-!
# Proposition 8.1: the first nontransverse Smith layer

The explicit parts (the singular vectors `φ₅`, `φ₄`, `ξ₇` and `γ₇`) are in `Sec8Smith7Comp`
and `Sec8Gamma7`.  Here: `U₂ ∩ U₃` vanishes below level `7` (a lowest vector would be singular
and would pull back to a singular vector of `M(1/2,5/2)` below level `5`, where the Kac
determinant does not vanish), `(U₂ ∩ U₃)₇ = ℂ ξ₇` by uniqueness of singular vectors, and the
Smith exponents `(0⁴,1¹⁰,2)` from Theorem 5.7 and the determinant valuation `p(5) + p(4) = 12`.
-/

namespace Virasoro

open Verma Module

set_option maxRecDepth 100000

/-! ### Counting multisets of exponents -/

theorem card_filter_le_eq (s : Multiset ℕ) (a b : ℕ) (hb : b = a + 1) :
    Multiset.card (s.filter (a ≤ ·)) = Multiset.card (s.filter (b ≤ ·)) + s.count a := by
  subst hb
  have h := Multiset.filter_add_not (fun x => a + 1 ≤ x) (s.filter (a ≤ ·))
  rw [Multiset.filter_filter, Multiset.filter_filter] at h
  have e1 : s.filter (fun x => a + 1 ≤ x ∧ a ≤ x) = s.filter (a + 1 ≤ ·) :=
    Multiset.filter_congr fun x _ => ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have e2 : s.filter (fun x => ¬ a + 1 ≤ x ∧ a ≤ x) = s.filter (fun x => x = a) :=
    Multiset.filter_congr fun x _ => ⟨fun h => by omega, fun h => by omega⟩
  rw [e1, e2] at h
  rw [← h, Multiset.card_add, Multiset.count_eq_card_filter_eq]
  congr 2
  exact Multiset.filter_congr fun x _ => eq_comm

theorem multiset_eq_012 (s : Multiset ℕ) (n0 n1 n2 : ℕ)
    (h3 : Multiset.card (s.filter (3 ≤ ·)) = 0) (h2 : Multiset.card (s.filter (2 ≤ ·)) = n2)
    (h1 : Multiset.card (s.filter (1 ≤ ·)) = n1 + n2) (hc : Multiset.card s = n0 + n1 + n2) :
    s = Multiset.replicate n0 0 + Multiset.replicate n1 1 + Multiset.replicate n2 2 := by
  have c2 := card_filter_le_eq s 2 3 rfl
  have c1 := card_filter_le_eq s 1 2 rfl
  have c0 := card_filter_le_eq s 0 1 rfl
  rw [Multiset.filter_eq_self.2 (fun x _ => Nat.zero_le x)] at c0
  have hge : ∀ a, 3 ≤ a → s.count a = 0 := by
    intro a ha
    rw [Multiset.count_eq_card_filter_eq]
    refine Nat.eq_zero_of_le_zero
      (h3 ▸ Multiset.card_le_card (Multiset.monotone_filter_right s ?_))
    intro x hx
    omega
  ext a
  simp only [Multiset.count_add, Multiset.count_replicate]
  rcases Nat.lt_or_ge a 3 with ha | ha
  · interval_cases a <;> simp <;> omega
  · rw [hge a ha]
    split_ifs <;> omega

/-! ### Partition counts -/

theorem card_partition_four : Fintype.card (Nat.Partition 4) = 5 := by
  rw [card_partition_of_isEnum (isEnum_decWords 4 (by decide) (by unfold PosWord; decide))]
  decide

theorem card_partition_five : Fintype.card (Nat.Partition 5) = 7 := by
  rw [card_partition_of_isEnum (isEnum_decWords 5 (by decide) (by unfold PosWord; decide))]
  decide

theorem card_partition_seven : Fintype.card (Nat.Partition 7) = 15 := by
  rw [card_partition_of_isEnum (isEnum_decWords 7 (by decide) (by unfold PosWord; decide))]
  decide

/-! ### Membership in the singular submodules -/

theorem negOp_smul_mem_negSpan {c h : ℂ} (χ : Verma ℂ c h) {w : List ℕ} (hw : PosWord w) :
    VirEnv.negOp c w • χ ∈ negSpan χ := by
  have hmap : (w.map Nat.toPNat').map PNat.val = w := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    refine List.map_congr_left fun y hy => ?_
    simp [Nat.toPNat'_coe, hw y hy]
  refine Submodule.subset_span ⟨w.map Nat.toPNat', ?_⟩
  show VirEnv.negOp c (List.map PNat.val _) • χ = _
  rw [hmap]

theorem toOp_smul_mem_negSpan {c h : ℂ} (χ : Verma ℂ c h) (s : St ℂ) (hs : PosSt s) :
    St.toOp c s • χ ∈ negSpan χ := by
  induction s with
  | nil => simp [St.toOp]
  | cons t s ih =>
    simp only [St.toOp, List.map_cons, List.sum_cons, add_smul, smul_assoc] at ih ⊢
    exact add_mem (Submodule.smul_mem _ _ (negOp_smul_mem_negSpan χ (hs t List.mem_cons_self)))
      (ih fun u hu => hs u (List.mem_cons_of_mem _ hu))

theorem posSt_mapSt_of_level {N : ℕ} {s : List (List ℕ × ℚ)} (h : IsLevelSt N s) :
    PosSt (mapSt qC s) := fun t ht => (isLevelSt_mapSt qC h t ht).1

/-! ### The intersection `U₂ ∩ U₃` -/

/-- The labels below level `5` do not have the weight `5/2`. -/
theorem no_label_five_halves : ∀ M ∈ Finset.range 5, ∀ g ∈ labels M,
    isingKey g ≠ isingKey (2, 1) + 48 * ((2 : ℕ) : ℤ) := by
  decide

theorem kacC_b0' : kacC b0 = 1 / 2 := def_fixed_specialization_ising.1

theorem det_ne_five_halves (hK : Cited_KacDeterminant) {M : ℕ} (hM : M < 5) :
    (gram (1 / 2 : ℂ) ((1 / 2 : ℂ) + ((2 : ℕ) : ℂ)) M).det ≠ 0 := by
  have h := gram_det_ne_of_labels hK (b := b0) (z := (1 / 2 : ℂ) + ((2 : ℕ) : ℂ)) b0_ne_zero
    (M := M) fun g hg => by
      rw [kacHL_b0_cast]
      have e : (1 / 2 : ℂ) + ((2 : ℕ) : ℂ)
          = ((isingDelta ((2, 1) : Label).1 ((2, 1) : Label).2 : ℚ) : ℂ) + ((2 : ℕ) : ℂ) := by
        norm_num [isingDelta]
      rw [e, Ne, isingDelta_cast_shift_iff]
      exact no_label_five_halves M (Finset.mem_range.2 hM) g hg
  rwa [kacC_b0'] at h

theorem xi2_singular' :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi2) 2 := by
  rw [xi2_eq]; exact xi2_singular ℂ

theorem xi3_singular' :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi3) 3 := by
  rw [xi3_eq]; exact xi3_singular ℂ

theorem U23_low (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective) :
    ∀ N : ℕ, N < 7 →
      negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi2) ⊓
        negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi3) ⊓ level N = ⊥ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rw [eq_bot_iff]
    rintro v ⟨⟨hv2, hv3⟩, hvl⟩
    rw [Submodule.mem_bot]
    by_contra hv0
    have hW := isVirSubmodule_inf (negSpan_isVir xi2_singular') (negSpan_isVir xi3_singular')
    have hvs := isSingular_of_lowest hW (fun M hM => ih M hM (by omega)) ⟨hv2, hv3⟩ hvl hv0
    obtain ⟨h3, -⟩ := singular_pullback hI xi3_singular' hv3 hvs
    obtain ⟨-, u, hu⟩ := singular_pullback hI xi2_singular' hv2 hvs
    exact not_isSingular_of_det_ne (by omega) (det_ne_five_halves hK (by omega)) u hu

theorem U23_seven (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective)
    (hU : Cited_SingularUnique) :
    negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi2) ⊓
        negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) xi3) ⊓ level 7 =
      Submodule.span ℂ {St.toOp (1 / 2 : ℂ) phi5 • St.toVerma (c := (1 / 2 : ℂ))
        (h := (1 / 2 : ℂ)) xi2} := by
  have hξ := x7_singular
  rw [← xi7_eq_x7] at hξ
  apply le_antisymm
  · rintro v ⟨⟨hv2, hv3⟩, hvl⟩
    by_cases hv0 : v = 0
    · rw [hv0]; exact zero_mem _
    have hW := isVirSubmodule_inf (negSpan_isVir xi2_singular') (negSpan_isVir xi3_singular')
    have hvs := isSingular_of_lowest hW (fun M hM => U23_low hK hI M hM) ⟨hv2, hv3⟩ hvl hv0
    obtain ⟨a, ha⟩ := hU _ _ 7 _ _ hξ hvs
    rw [ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [phi5_eq_mapSt]
      exact toOp_smul_mem_negSpan _ _ (posSt_mapSt_of_level isLevel_phi5Q)
    · rw [xi7_eq_x7, ← xi7_eq_x7', phi4_eq_mapSt]
      exact toOp_smul_mem_negSpan _ _ (posSt_mapSt_of_level isLevel_phi4Q)
    · rw [xi7_eq_x7]
      exact mem_level_of_L_zero x7_singular.2.1

/-! ### The Smith exponents -/

theorem labels7_half : ((labels 7).filter fun g => kacHL g b0 = kacHL ((2, 1) : Label) b0) =
    {(2, 1), (1, 3)} := by
  classical
  rw [Finset.filter_congr (q := fun g : Label => isingKey g = isingKey (2, 1))
    (fun g _ => by rw [kacHL_b0_cast, kacHL_b0_cast, isingDelta_cast_eq_iff])]
  decide

theorem smith7 (hK : Cited_KacDeterminant) (hJ : Cited_JantzenLayers) :
    IsSmith (gramLocal (1 / 2 : ℂ) (1 / 2) 7)
      (Multiset.replicate 4 0 + Multiset.replicate 10 1 + {2}) := by
  classical
  have hb : b0 ^ 2 = -((4 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by rw [b0_sq]; norm_num
  obtain ⟨wp, wm, hsing, -, hcount, -⟩ := thm_jantzen_smith hJ 3 4 2 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) b0 hb
  have hh : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = 1 / 2 := by
    rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]
  have hG : gramLocal (kacC b0) (kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0) 7
      = gramLocal (1 / 2 : ℂ) (1 / 2) 7 := by rw [kacC_b0', hh]
  obtain ⟨s, hs⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b0)
    (kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0) 7)
  -- the second layer: `ℂ w⁻₂`
  have hl2p : ellPlus 3 4 2 1 2 = 17 := by decide
  have hl2m : ellMinus 3 4 2 1 2 = 7 := by decide
  have hl3p : ellPlus 3 4 2 1 3 = 25 := by decide
  have hl3m : ellMinus 3 4 2 1 3 = 28 := by decide
  obtain ⟨hp2, hm2⟩ := hsing 2 (by norm_num)
  obtain ⟨hp3, hm3⟩ := hsing 3 (by norm_num)
  rw [hl2p] at hp2
  rw [hl2m] at hm2
  rw [hl3p] at hp3
  rw [hl3m] at hm3
  have hI2 : (negSpan (wp 2) ⊔ negSpan (wm 2)) ⊓ level 7 = Submodule.span ℂ {wm 2} := by
    apply le_antisymm
    · rintro v ⟨hv, hvl⟩
      obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.1 hv
      rw [← pbwCoord_comp_of_mem_level hvl, map_add, map_add,
        comp_negSpan_eq_zero (mem_level_of_L_zero hp2.2.1) (by norm_num) ha, map_zero, zero_add]
      exact pbwCoord_comp_negSpan_mem (mem_level_of_L_zero hm2.2.1) hb'
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨Submodule.mem_sup_right (Submodule.subset_span ⟨[], by simp [negOp_nil_smul]⟩),
        mem_level_of_L_zero hm2.2.1⟩
  have hI3 : (negSpan (wp 3) ⊔ negSpan (wm 3)) ⊓ level 7 = ⊥ := by
    by_contra hne
    have := (inf_level_ne_bot_iff hp3 hm3).1 hne
    norm_num at this
  have h2 : Multiset.card (s.filter (2 ≤ ·)) = 1 := by
    rw [hcount 7 s hs 2 (by norm_num), hI2, finrank_span_singleton hm2.1]
  have h3 : Multiset.card (s.filter (3 ≤ ·)) = 0 := by
    rw [hcount 7 s hs 3 (by norm_num), hI3, finrank_bot]
  -- the sum of the exponents: `p(5) + p(4) = 12`
  have hsum : s.sum = 12 := by
    have h1 := (smith_main hs).1
    rw [gramLocal_det_order_kac hK b0_ne_zero 7] at h1
    have e : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = kacHL ((2, 1) : Label) b0 := rfl
    rw [e, labels7_half] at h1
    rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h1
    have e5 : (7 - Label.lvl (2, 1)) = 5 := rfl
    have e4 : (7 - Label.lvl (1, 3)) = 4 := rfl
    rw [e5, e4, card_partition_five, card_partition_four] at h1
    exact_mod_cast h1.symm
  have hcard : Multiset.card s = 15 := by
    obtain ⟨e, -, -, -, -, -, rfl⟩ := hs
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, card_partition_seven]
  have hle : ∀ x ∈ s, x ≤ 2 := by
    intro x hx
    by_contra hx2
    have hmem : x ∈ s.filter (3 ≤ ·) := Multiset.mem_filter.2 ⟨hx, by omega⟩
    have := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hmem⟩
    omega
  have h1 : Multiset.card (s.filter (1 ≤ ·)) = 10 + 1 := by
    have := sum_filter_card s 2 hle
    rw [hsum] at this
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ 2 by norm_num), Finset.Icc_self,
      Finset.sum_singleton] at this
    rw [h2] at this
    omega
  have hs_eq := multiset_eq_012 s 4 10 1 h3 h2 h1 (by rw [hcard])
  rw [← hG, show Multiset.replicate 4 0 + Multiset.replicate 10 1 + ({2} : Multiset ℕ)
      = Multiset.replicate 4 0 + Multiset.replicate 10 1 + Multiset.replicate 1 2 from rfl,
    ← hs_eq]
  exact hs

/-! ### Proposition 8.1 -/

/-- Proposition 8.1 (`prop:level-seven-smith`).

Paper label: prop:level-seven-smith -/
theorem prop_level_seven_smith (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective)
    (hU : Cited_SingularUnique) (hJ : Cited_JantzenLayers) : Stmt_prop_level_seven_smith := by
  unfold Stmt_prop_level_seven_smith
  dsimp only
  obtain ⟨hv1, hker2, hγ⟩ := x7_ker2_gamma
  refine ⟨phi5_singular, phi4_singular, ?_, ?_, U23_low hK hI, U23_seven hK hI hU,
    smith7 hK hJ, ?_⟩
  · rw [xi7_eq_x7, xi7_eq_x7']
  · rw [xi7_eq_x7]; exact x7_singular
  · refine ⟨St.coords 7 (mapSt qC x7Q), ?_, ?_, hker2, fun v₁ hv₁ => ?_⟩
    · rw [xi7_eq_x7, toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_x7Q)]
    · rw [coords_mapSt, coords_ones,
        show ((x7Q.filter fun t => t.1 = List.replicate 7 1).map Prod.snd).sum = 1 by
          decide +kernel, map_one]
    · rw [cross2_indep (gramLocal_isSymm (1 / 2 : ℂ) (1 / 2) 7) hker2 hv₁ hv1]
      exact hγ

end Virasoro
