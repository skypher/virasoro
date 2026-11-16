import Virasoro.Statements.Sec8
import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Proofs.ResidueCore3
import Virasoro.Proofs.KacField
import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.Sec5Cross
import Virasoro.Proofs.Sec5Smith
import Virasoro.Proofs.SmithExist
import Virasoro.Proofs.Sec3
import Virasoro.Proofs.Generic

/-!
# Proposition 8.2: no double pole below level seven

For `N < 7` and every weight `λ`, the local Smith exponents of `G_N(1/2, λ + x)` are at most `1`.
At the three repeated Ising weights `0, 1/16, 1/2` this is Theorem 5.7 (`j_N(λ) ≤ 1` for
`N < 7`).  At every other weight at most one Kac label of level `≤ N` carries `λ`; then the kernel
at the singular level is spanned by a singular vector with nonzero crossing scalar, the shifted
Gram matrix is invertible, and `ord_x det G_N = p(N - ℓ)`, so the pole is simple
(`residue_inverse`).
-/

namespace Virasoro

open Polynomial Module

/-- The root multiplicity of a product of powers of linear factors. -/
theorem rootMultiplicity_prod_pow {K ι : Type*} [Field K] [DecidableEq K] (s : Finset ι)
    (a : ι → K) (k : ι → ℕ) (z : K) :
    (∏ i ∈ s, (X - C (a i)) ^ k i).rootMultiplicity z = ∑ i ∈ s.filter (fun i => a i = z), k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.filter_insert]
    have hne1 : (X - C (a j)) ^ k j ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
    have hne2 : ∏ i ∈ s, (X - C (a i)) ^ k i ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _)
    rw [rootMultiplicity_mul (mul_ne_zero hne1 hne2), ih]
    by_cases hz : a j = z
    · rw [if_pos hz, Finset.sum_insert (fun h => hj (Finset.mem_filter.1 h).1), hz,
        rootMultiplicity_X_sub_C_pow]
    · rw [if_neg hz]
      have : ((X - C (a j)) ^ k j).rootMultiplicity z = 0 := by
        refine rootMultiplicity_eq_zero fun h => ?_
        rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C] at h
        exact hz (sub_eq_zero.1 (pow_eq_zero_iff'.1 h).1).symm
      rw [this, zero_add]

/-- `ord_x det G_M(c(b), λ + x) = ∑_{labels g, ℓ_g ≤ M, h_g(b) = λ} p(M - ℓ_g)` (Kac). -/
theorem gramLocal_det_order_kac (hK : Cited_KacDeterminant) {b : ℂ} (hb : b ≠ 0) (M : ℕ)
    (z : ℂ) :
    (gramLocal (kacC b) z M).det.order =
      ((∑ g ∈ (labels M).filter (fun g => kacHL g b = z),
        Fintype.card (Nat.Partition (M - g.lvl)) : ℕ) : ℕ∞) := by
  classical
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hb M
  have hne : C C₀ * kacProd b M ≠ 0 := by
    rw [← hdet]
    exact gramPoly_det_ne_zero _ _
  rw [gramLocal_det_order, hdet, rootMultiplicity_mul hne, rootMultiplicity_C, zero_add, kacProd,
    rootMultiplicity_prod_pow]

/-- At `b₀`, the Kac weight of a label is its Ising weight. -/
theorem kacHL_b0_cast (g : Label) : kacHL g b0 = ((isingDelta (g.1 : ℤ) (g.2 : ℤ) : ℚ) : ℂ) :=
  def_fixed_specialization_ising.2 _ _


open Verma in
/-- A single Kac label at weight `z`: if the Gram determinant at `z` vanishes to order exactly `1`
at the singular level `ℓ` and not at all below it, the shifted Gram matrix `G_M(c, z + ℓ)` is
invertible, and `ord_x det G_{ℓ+M}(c, z + x) = p(M)`, then `G_{ℓ+M}(c, z + x)⁻¹` has at most a
simple pole. -/
theorem poleOrderInv_le_one_of_single (c z : ℂ) (ℓ M : ℕ) (hℓ : 1 ≤ ℓ)
    (hlow : ∀ m < ℓ, (gramPoly c m).det.rootMultiplicity z = 0)
    (hone : (gramPoly c ℓ).det.rootMultiplicity z = 1)
    (hshift : (gramPoly c M).det.rootMultiplicity (z + (ℓ : ℂ)) = 0)
    (hord : (gramPoly c (ℓ + M)).det.rootMultiplicity z = Fintype.card (Nat.Partition M)) :
    poleOrderInv (gramLocal c z (ℓ + M)) ≤ 1 := by
  classical
  -- determinants from root multiplicities
  have hdet_ne : ∀ (m : ℕ) (w : ℂ), (gramPoly c m).det.rootMultiplicity w = 0 →
      (gram c w m).det ≠ 0 := by
    intro m w hw h0
    rw [← gramPoly_det_eval] at h0
    have : 0 < (gramPoly c m).det.rootMultiplicity w :=
      (rootMultiplicity_pos (gramPoly_det_ne_zero c m)).2 h0
    omega
  have hdet0 : (gram c z ℓ).det = 0 := by
    rw [← gramPoly_det_eval]
    have : 0 < (gramPoly c ℓ).det.rootMultiplicity z := by omega
    exact (rootMultiplicity_pos (gramPoly_det_ne_zero c ℓ)).1 this
  -- a kernel vector at the singular level
  obtain ⟨p, hp0, hp⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  set χ : Verma ℂ c z := pbwCoord ℓ p with hχdef
  have hχlev : χ ∈ level ℓ := LinearMap.mem_range_self _ _
  -- `χ` is singular
  have hsing : IsSingular χ ℓ := by
    refine ⟨fun h0 => hp0 (pbwCoord_injective ℓ (by rw [← hχdef, h0, map_zero])),
      L_zero_of_mem_level hχlev, fun n hn => ?_⟩
    by_cases hnl : (ℓ : ℤ) < n
    · exact L_eq_zero_of_level hnl hχlev
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = (ℓ : ℤ) - n := ⟨(ℓ - n.toNat), by omega⟩
      have hml : m < ℓ := by omega
      obtain ⟨q, hq⟩ := L_mem_level hm hχlev
      have hGq : (gram c z m).mulVec q = 0 := by
        funext Y
        rw [Pi.zero_apply, ← shap_neg_pbwCoord Y q, hq]
        have hc := isShapovalov_shap.2 (-n) (neg (c := c) (h := z) Y.word) χ
        rw [neg_neg] at hc
        rw [← hc]
        have hYm : ((m : ℕ) : ℤ) = ((Y.word.sum : ℕ) : ℤ) := by rw [word_sum']
        obtain ⟨w, hw⟩ := L_neg_mem_level (c := c) (h := z) (posWord_word Y)
          (n := -n) (M := ℓ) (by rw [← hYm]; omega)
        rw [← hw, hχdef, shap_pbwCoord, gramForm, hp, dotProduct_zero]
      have hq0 : q = 0 := Matrix.eq_zero_of_mulVec_eq_zero (hdet_ne m z (hlow m hml)) hGq
      rw [← hq, hq0, map_zero]
  -- the crossing scalar is nonzero
  have hβ : crossScalar c z p ≠ 0 := by
    have hcs : crossScalar c z p = cross1 (gramLocal c z ℓ) p p := by
      rw [← dAt_gramForm]
      rfl
    set G := gramLocal c z ℓ
    have hG := gramLocal_isSymm c z ℓ
    have hGdet := gramLocal_det_ne_zero c z ℓ
    have hpk : p ∈ ker0 G := by
      rw [mem_ker0, coeffMat_zero_gramLocal]
      exact hp
    have hord1 : G.det.order = 1 := by
      rw [gramLocal_det_order, hone]
      rfl
    obtain ⟨s, hs⟩ := exists_isSmith hGdet
    obtain ⟨h1, h2, -⟩ := smith_main hs
    have hfin_le : finrank ℂ (ker0 G) ≤ 1 := by
      have := multiset_filter_pos_card_le_sum s
      rw [hord1] at h1
      have hs1 : s.sum = 1 := by exact_mod_cast h1.symm
      rw [h2]
      omega
    have hfin : finrank ℂ (ker0 G) = 1 := by
      refine le_antisymm hfin_le (Nat.one_le_iff_ne_zero.2 fun h0 => hp0 ?_)
      have := Submodule.finrank_eq_zero.1 h0
      have hmem : p ∈ (⊥ : Submodule ℂ (Nat.Partition ℓ → ℂ)) := this ▸ hpk
      exact (Submodule.mem_bot ℂ).1 hmem
    have hnd : Cross1NondegK G :=
      ((cross1_main hG hGdet).2).2 (by rw [hord1, hfin]; rfl)
    rw [hcs]
    intro h0
    have hpv : (⟨p, hpk⟩ : ker0 G) ≠ 0 := fun h => hp0 (congrArg Subtype.val h)
    have hspan := (finrank_eq_one_iff_of_nonzero' (⟨p, hpk⟩ : ker0 G) hpv).1 hfin
    refine hp0 (hnd p hpk fun u hu => ?_)
    obtain ⟨t, ht⟩ := hspan ⟨u, hu⟩
    have hu' : u = t • p := by
      have := congrArg Subtype.val ht
      simpa using this.symm
    rw [hu', cross1_def, smul_dotProduct, ← cross1_def, h0, smul_zero]
  -- the shifted Gram matrix is invertible
  have hg : (gram c (z + (ℓ : ℂ)) M).det ≠ 0 := hdet_ne M _ hshift
  have hordN : (gramLocal c z (ℓ + M)).det.order = ((Fintype.card (Nat.Partition M) : ℕ) : ℕ∞) := by
    rw [gramLocal_det_order, hord]
  exact (residue_inverse c z ℓ M p hℓ hsing hβ hg hordN).1


/-- The integer key `(4r - 3s)²` of an Ising label. -/
def isingKey (g : Label) : ℤ := (4 * (g.1 : ℤ) - 3 * (g.2 : ℤ)) ^ 2

/-- Below level seven, a weight other than `0, 1/16, 1/2` carries at most one label, and its
shifted weight carries no label of the remaining level. -/
theorem ising_single_labels :
    ∀ N ∈ Finset.range 7, ∀ a ∈ labels N, isingKey a ≠ 1 → isingKey a ≠ 4 → isingKey a ≠ 25 →
      (∀ g ∈ labels N, isingKey g = isingKey a → g = a) ∧
      ∀ g ∈ labels (N - a.1 * a.2), isingKey g ≠ isingKey a + 48 * ((a.1 * a.2 : ℕ) : ℤ) := by
  decide

theorem isingDelta_cast_eq_iff (g a : Label) :
    ((isingDelta (g.1 : ℤ) (g.2 : ℤ) : ℚ) : ℂ) = ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : ℂ) ↔
      isingKey g = isingKey a := by
  rw [Rat.cast_inj, isingDelta_eq_iff]
  rfl

theorem isingDelta_cast_shift_iff (g a : Label) (ℓ : ℕ) :
    ((isingDelta (g.1 : ℤ) (g.2 : ℤ) : ℚ) : ℂ) =
        ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : ℂ) + (ℓ : ℂ) ↔
      isingKey g = isingKey a + 48 * (ℓ : ℤ) := by
  have e : ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : ℂ) + (ℓ : ℂ) =
      (((isingDelta (a.1 : ℤ) (a.2 : ℤ) + ℓ : ℚ)) : ℂ) := by push_cast; ring
  rw [e, Rat.cast_inj, isingKey, isingKey]
  unfold isingDelta
  constructor
  · intro h
    have h' : ((4 * (g.1 : ℤ) - 3 * (g.2 : ℤ)) ^ 2 : ℚ) =
        ((4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)) ^ 2 + 48 * (ℓ : ℤ) : ℚ) := by
      push_cast at h ⊢
      linarith
    exact_mod_cast h'
  · intro h
    have h' : ((4 * (g.1 : ℤ) - 3 * (g.2 : ℤ)) ^ 2 : ℚ) =
        ((4 * (a.1 : ℤ) - 3 * (a.2 : ℤ)) ^ 2 + 48 * (ℓ : ℤ) : ℚ) := by exact_mod_cast h
    push_cast at h' ⊢
    linarith

/-- The Kac root multiplicities at `c = 1/2`. -/
theorem rootMult_ising (hK : Cited_KacDeterminant) (M : ℕ) (z : ℂ) :
    (gramPoly (1 / 2 : ℂ) M).det.rootMultiplicity z =
      ∑ g ∈ (labels M).filter (fun g => ((isingDelta (g.1 : ℤ) (g.2 : ℤ) : ℚ) : ℂ) = z),
        Fintype.card (Nat.Partition (M - g.lvl)) := by
  classical
  have h := gramLocal_det_order_kac hK b0_ne_zero M z
  rw [gramLocal_det_order, def_fixed_specialization_ising.1] at h
  have h' := ENat.natCast_inj.1 h
  rw [h']
  refine Finset.sum_congr (Finset.filter_congr fun g _ => by rw [kacHL_b0_cast]) fun _ _ => rfl

theorem jDepth_11_le : ∀ N : ℕ, N < 7 → jDepth 3 4 1 1 N ≤ 1 := by decide +kernel
theorem jDepth_12_le : ∀ N : ℕ, N < 7 → jDepth 3 4 1 2 N ≤ 1 := by decide +kernel
theorem jDepth_21_le : ∀ N : ℕ, N < 7 → jDepth 3 4 2 1 N ≤ 1 := by decide +kernel

set_option maxHeartbeats 400000 in
/-- The local Smith exponents of `G_N(1/2, λ + x)` are at most `1` below level seven. -/
theorem poleOrderInv_ising_le_one (hK : Cited_KacDeterminant) (hJ : Cited_JantzenLayers)
    (N : ℕ) (hN : N < 7) (z : ℂ) : poleOrderInv (gramLocal (1 / 2 : ℂ) z N) ≤ 1 := by
  classical
  have hc : kacC b0 = (1 / 2 : ℂ) := def_fixed_specialization_ising.1
  -- the three repeated weights: Theorem 5.7
  have hJS : ∀ r s : ℕ, 0 < r → r < 3 → 0 < s → s < 4 → 4 * r + 3 * s < 3 * 4 →
      (∀ N : ℕ, N < 7 → jDepth 3 4 r s N ≤ 1) →
      poleOrderInv (gramLocal (1 / 2 : ℂ) (kacH (r : ℤ) (s : ℤ) b0) N) ≤ 1 := by
    intro r s hr hr3 hs hs4 hrs hj
    obtain ⟨wp, wm, -, -, -, hD⟩ := thm_jantzen_smith hJ 3 4 r s (by norm_num) (by norm_num)
      (by norm_num) hr hr3 hs hs4 hrs b0 (by rw [b0_sq]; norm_num)
    have := (hD N).1
    rw [hc] at this
    rw [this]
    exact hj N hN
  have hz0 : kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = 0 := by
    rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]
  have hz1 : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0 = 1 / 16 := by
    rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]
  have hz2 : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = 1 / 2 := by
    rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]
  by_cases hA : z = 0 ∨ z = 1 / 16 ∨ z = 1 / 2
  · rcases hA with h | h | h
    · have hb := hJS 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        jDepth_11_le
      rw [hz0] at hb
      rw [h]
      exact hb
    · have hb := hJS 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        jDepth_12_le
      rw [hz1] at hb
      rw [h]
      exact hb
    · have hb := hJS 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        jDepth_21_le
      rw [hz2] at hb
      rw [h]
      exact hb
  push_neg at hA
  obtain ⟨hA0, hA1, hA2⟩ := hA
  by_cases hS : ∃ a ∈ labels N, ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : ℂ) = z
  · obtain ⟨a, ha, rfl⟩ := hS
    -- the key of `a` is not that of a repeated weight
    have hk : ∀ k : ℤ, k ∈ ({1, 4, 25} : Finset ℤ) → isingKey a ≠ k := by
      intro k hk hka
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      have hval : ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : ℂ) = ((k - 1) / 48 : ℚ) := by
        unfold isingDelta
        rw [show (4 * ((a.1 : ℤ) : ℚ) - 3 * ((a.2 : ℤ) : ℚ)) ^ 2 = (k : ℚ) by
          rw [← hka, isingKey]; push_cast; ring]
      rcases hk with rfl | rfl | rfl
      · exact hA0 (by rw [hval]; norm_num)
      · exact hA1 (by rw [hval]; norm_num)
      · exact hA2 (by rw [hval]; norm_num)
    obtain ⟨huniq, hshift⟩ := ising_single_labels N (Finset.mem_range.2 hN) a ha
      (hk 1 (by simp)) (hk 4 (by simp)) (hk 25 (by simp))
    obtain ⟨ha1, ha2, ha3⟩ := mem_labels.1 ha
    set ℓ := a.1 * a.2 with hℓdef
    have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    -- filters of weight `λ`
    have hfilt : ∀ M ≤ N, (labels M).filter (fun g =>
        ((isingDelta (g.1 : ℤ) (g.2 : ℤ) : ℚ) : ℂ) = ((isingDelta (a.1 : ℤ) (a.2 : ℤ) : ℚ) : ℂ))
          = if ℓ ≤ M then {a} else ∅ := by
      intro M hM
      ext g
      simp only [Finset.mem_filter, isingDelta_cast_eq_iff]
      constructor
      · rintro ⟨hg, hgk⟩
        have := huniq g (labels_subset hM hg) hgk
        subst this
        have := (mem_labels.1 hg).2.2
        rw [if_pos this]
        exact Finset.mem_singleton_self _
      · intro hg
        split_ifs at hg with hl
        · rw [Finset.mem_singleton.1 hg]
          exact ⟨mem_labels.2 ⟨ha1, ha2, hl⟩, rfl⟩
        · exact absurd hg (Finset.notMem_empty _)
    have hpart0 : Fintype.card (Nat.Partition 0) = 1 := by decide
    have hM : ℓ + (N - ℓ) = N := by omega
    rw [← hM]
    refine poleOrderInv_le_one_of_single (1 / 2) _ ℓ (N - ℓ) hℓ1 (fun m hm => ?_) ?_ ?_ ?_
    · rw [rootMult_ising hK, hfilt m (by omega), if_neg (by omega), Finset.sum_empty]
    · rw [rootMult_ising hK, hfilt ℓ (by omega), if_pos le_rfl, Finset.sum_singleton]
      show Fintype.card (Nat.Partition (ℓ - ℓ)) = 1
      rw [Nat.sub_self, hpart0]
    · rw [rootMult_ising hK]
      refine Finset.sum_eq_zero fun g hg => ?_
      exfalso
      obtain ⟨hgM, hgk⟩ := Finset.mem_filter.1 hg
      rw [isingDelta_cast_shift_iff] at hgk
      exact hshift g hgM hgk
    · rw [hM, rootMult_ising hK, hfilt N le_rfl, if_pos ha3, Finset.sum_singleton]
      rfl
  · -- no label carries `λ`: the determinant does not vanish
    have h0 : (gramPoly (1 / 2 : ℂ) N).det.rootMultiplicity z = 0 := by
      rw [rootMult_ising hK]
      refine Finset.sum_eq_zero fun g hg => ?_
      obtain ⟨hgN, hgz⟩ := Finset.mem_filter.1 hg
      exact absurd ⟨g, hgN, hgz⟩ hS
    obtain ⟨s, hs⟩ := exists_isSmith (gramLocal_det_ne_zero (1 / 2 : ℂ) z N)
    obtain ⟨h1, -, h3⟩ := smith_main hs
    rw [gramLocal_det_order, h0] at h1
    have hsum : s.sum = 0 := by exact_mod_cast h1.symm
    rw [h3]
    refine Multiset.sup_le.2 fun e he => ?_
    have := (Multiset.sum_eq_zero_iff.1 hsum) e he
    omega


/-- Proposition 8.2 (`prop:no-earlier-double-pole`), from the Kac determinant formula and, at the
three repeated weights, the Jantzen layers of Theorem 5.7. -/
theorem prop_no_earlier_double_pole (hK : Cited_KacDeterminant) (hJ : Cited_JantzenLayers) :
    Stmt_prop_no_earlier_double_pole := by
  intro N hN z
  have hP := poleOrderInv_ising_le_one hK hJ N hN z
  refine ⟨fun s hs e he => ?_, hP, (poleOrder_FN_le _ _ _).trans hP,
    poleOrder_HN_le _ _ _ _ fun M hM => poleOrderInv_ising_le_one hK hJ M (by omega) z⟩
  obtain ⟨-, -, h3⟩ := smith_main hs
  rw [h3] at hP
  exact (Multiset.le_sup he).trans hP

end Virasoro
