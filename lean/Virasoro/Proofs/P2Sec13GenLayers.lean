import Virasoro.Proofs.P2Sec13Split
import Virasoro.Proofs.P2Sec9BoxFinal
import Virasoro.Proofs.P2Sec11LayerZero
import Virasoro.Proofs.Sec8Smith7
import Virasoro.Proofs.Sec8NoDouble
import Virasoro.Proofs.JantzenDim
import Virasoro.Proofs.ResidueCore3

/-!
# Lemma 13.1, Step 1: the generic degenerate module (paper.tex l.2884–2887)

For generic `b` the module `M(c(b),h_{R,S}(b))` has the one proper submodule `U(Vir_-)χ`.  The
consumer uses this as `J¹ = U(Vir_-)χ` and `J^i_N = 0` for `i ≥ 2`.  The proof: by the Kac
determinant, `ord_x det G_N(c(b),h_{R,S}(b)+x) = p(N-RS)` at irrational `b²` (the Kac weights of
distinct positive labels differ); the vectors `L_{-Z}χ`, `|Z| = N-RS`, are `p(N-RS)` independent
vectors of the radical `J¹_N`; and `∑_{i≥1} dim J^i_N = ord_x det` (Lemma 5.6).
-/

namespace Virasoro.P2

open Virasoro Polynomial Verma Module

theorem card_filter_add_le_sum (s : Multiset ℕ) :
    (s.filter fun e => 1 ≤ e).card + (s.filter fun e => 2 ≤ e).card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.sum_cons]
    by_cases h1 : 1 ≤ a <;> by_cases h2 : 2 ≤ a <;>
      simp only [h1, h2, if_true, if_false, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_zero] <;> omega

section Level

variable {b : ℂ} (hb : b ≠ 0) (hirr : ∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) {R S : ℕ} (hR : 0 < R)
  (hS : 0 < S)

include hb hirr hR hS

/-- At irrational `b²`, `ord_x det G_N(c(b),h_{R,S}(b)+x)` is `p(N-RS)` for `RS ≤ N` and `0`
below (Kac determinant; the weights `h_{r,s}(b)` of distinct positive labels differ). -/
theorem generic_det_order (hK : Cited_KacDeterminant) (N : ℕ) :
    (gramLocal (kacC b) (kacH R S b) N).det.order =
      (((if R * S ≤ N then Fintype.card (Nat.Partition (N - R * S)) else 0 : ℕ)) : ℕ∞) := by
  classical
  rw [gramLocal_det_order_kac hK hb]
  congr 1
  have hfil : (labels N).filter (fun g => kacHL g b = kacH R S b) =
      if R * S ≤ N then {((R, S) : Label)} else ∅ := by
    ext g
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hg, he⟩
      obtain ⟨g1, g2, g3⟩ := mem_labels.1 hg
      have hgRS : g = (R, S) := by
        by_contra hne
        refine kacH_ne hb hirr (g.1 : ℤ) (g.2 : ℤ) (R : ℤ) (S : ℤ) (by exact_mod_cast g1)
          (by exact_mod_cast g2) (by exact_mod_cast hR) (by exact_mod_cast hS) ?_ ?_
        · intro h
          apply hne
          rw [Prod.mk.injEq] at h
          exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)
        · rw [← he, kacHL, sub_self]
      subst hgRS
      rw [if_pos g3]
      exact Finset.mem_singleton_self _
    · intro hg
      split_ifs at hg with hle
      · rw [Finset.mem_singleton] at hg
        subst hg
        exact ⟨mem_labels.2 ⟨hR, hS, hle⟩, rfl⟩
      · exact absurd hg (Finset.notMem_empty _)
  rw [hfil]
  split_ifs with hle
  · rw [Finset.sum_singleton]
    rfl
  · rw [Finset.sum_empty]

/-- Below the level `RS` the Jantzen layers `J^i_N`, `i ≥ 1`, vanish. -/
theorem generic_layer_below (hK : Cited_KacDeterminant) {N : ℕ} (hN : N < R * S) {i : ℕ}
    (hi : 1 ≤ i) : jantzenLayer (kacC b) (kacH R S b) N i = ⊥ := by
  obtain ⟨s, hs⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH R S b) N)
  have hord := (smith_main hs).1
  rw [generic_det_order hb hirr hR hS hK N, if_neg (by omega)] at hord
  have hsum : s.sum = 0 := by exact_mod_cast hord.symm
  have h1 := (jantzen_dim (kacC b) (kacH R S b) N s hs).1 i
  have hc := card_filter_add_le_sum s
  have hfil : (s.filter fun e => i ≤ e) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he hie
    have hmem : e ∈ s.filter fun e => 1 ≤ e := Multiset.mem_filter.2 ⟨he, by omega⟩
    have := Multiset.card_pos_iff_exists_mem.2 ⟨e, hmem⟩
    omega
  rw [hfil, Multiset.card_zero] at h1
  exact Submodule.finrank_eq_zero.1 h1

variable {x : Nat.Partition (R * S) → ℂ}
  (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x) (R * S))
  (hβ : crossScalar (kacC b) (kacH R S b) x ≠ 0)

include hx hβ

/-- At the level `RS + M`: `J¹` is the image of `ι` (the span of the `L_{-Z}χ`, `|Z| = M`) and
`J^i = 0` for `i ≥ 2`. -/
theorem generic_layer_above (hK : Cited_KacDeterminant) (M : ℕ) :
    jantzenLayer (kacC b) (kacH R S b) (R * S + M) 1 =
        LinearMap.range (iotaMat (kacC b) (kacH R S b) (R * S) M x).mulVecLin ∧
      ∀ i : ℕ, 2 ≤ i → jantzenLayer (kacC b) (kacH R S b) (R * S + M) i = ⊥ := by
  have hℓ : 1 ≤ R * S := Nat.mul_pos hR hS
  obtain ⟨s, hs⟩ := exists_isSmith (gramLocal_det_ne_zero (kacC b) (kacH R S b) (R * S + M))
  have hord := (smith_main hs).1
  rw [generic_det_order hb hirr hR hS hK, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    at hord
  have hsum : s.sum = Fintype.card (Nat.Partition M) := by exact_mod_cast hord.symm
  have hdim := (jantzen_dim (kacC b) (kacH R S b) (R * S + M) s hs).1
  have hg : (gram (kacC b) (kacH R S b + ((R * S : ℕ) : ℂ)) M).det ≠ 0 := by
    have h := (generic_out_regular hK hb hirr hR hS (0 : ℂ) M).1
    have e : kacH (R : ℤ) (-(S : ℤ)) b = kacH R S b + ((R * S : ℕ) : ℂ) := by
      simp only [kacH]
      push_cast
      field_simp
      ring
    rwa [e] at h
  have hinj := iotaMat_injective (kacC b) (kacH R S b) (R * S) M x hℓ hx hβ hg
  have hle : LinearMap.range (iotaMat (kacC b) (kacH R S b) (R * S) M x).mulVecLin ≤
      jantzenLayer (kacC b) (kacH R S b) (R * S + M) 1 := by
    rintro _ ⟨y, rfl⟩
    rw [jantzenLayer_one, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, gram_mul_iotaMat (kacC b) (kacH R S b) (R * S) M x hℓ hx,
      Matrix.zero_mulVec]
  have hrk : finrank ℂ (LinearMap.range (iotaMat (kacC b) (kacH R S b) (R * S) M x).mulVecLin) =
      Fintype.card (Nat.Partition M) := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hmono := Submodule.finrank_mono hle
  rw [hrk, hdim 1] at hmono
  have hc := card_filter_add_le_sum s
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hle (by rw [hrk, hdim 1]; omega)).symm,
    fun i hi => ?_⟩
  have hfil : (s.filter fun e => i ≤ e) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he hie
    have hmem : e ∈ s.filter fun e => 2 ≤ e := Multiset.mem_filter.2 ⟨he, by omega⟩
    have := Multiset.card_pos_iff_exists_mem.2 ⟨e, hmem⟩
    omega
  have h1 := hdim i
  rw [hfil, Multiset.card_zero] at h1
  exact Submodule.finrank_eq_zero.1 h1

/-- `J¹(c(b),h_{R,S}(b)) = U(Vir_-)χ` at generic `b`. -/
theorem generic_jantzen_one (hK : Cited_KacDeterminant) :
    jantzen (kacC b) (kacH R S b) 1 =
      negSpan (pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x) := by
  have hℓ : 1 ≤ R * S := Nat.mul_pos hR hS
  apply le_antisymm
  · unfold jantzen
    refine iSup_le fun N => ?_
    rintro _ ⟨v, hv, rfl⟩
    by_cases hN : N < R * S
    · have hv0 : v = 0 := by
        rw [generic_layer_below hb hirr hR hS hK hN le_rfl] at hv
        exact (Submodule.mem_bot ℂ).1 hv
      rw [hv0, map_zero]
      exact zero_mem _
    · obtain ⟨M, rfl⟩ : ∃ M, N = R * S + M := ⟨N - R * S, by omega⟩
      rw [(generic_layer_above hb hirr hR hS hx hβ hK M).1] at hv
      obtain ⟨y, rfl⟩ := hv
      have e : (iotaMat (kacC b) (kacH R S b) (R * S) M x).mulVecLin y =
          ∑ Z, y Z • (fun Y => iotaMat (kacC b) (kacH R S b) (R * S) M x Y Z) := by
        funext Y
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [e, map_sum]
      refine Submodule.sum_mem _ fun Z _ => ?_
      rw [map_smul, pbwCoord_iotaMat_col]
      exact Submodule.smul_mem _ _ (negOp_smul_mem_negSpan _ (posWord_word Z))
  · unfold negSpan
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    have hrad := jantzen_one_eq_radical (c := kacC b) (h := kacH R S b)
    have hmem : VirEnv.negOp (kacC b) (w.map (↑)) • pbwCoord (c := kacC b) (h := kacH R S b)
        (R * S) x ∈ (jantzen (kacC b) (kacH R S b) 1 : Set (Verma ℂ (kacC b) (kacH R S b))) := by
      rw [hrad]
      intro u
      rw [Verma.isShapovalov_shap.symm]
      exact shap_singular _ _ hx hℓ _ u
    exact hmem

end Level

/-- Lemma 13.1, Step 1, the structure of the generic degenerate module (l.2884–2887). -/
theorem sub_generic_layers_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) : Stmt_sub_generic_layers := by
  intro b hb hirr R S hR hS χ hχ
  have hlev : χ ∈ level (R * S) := mem_level_of_L_zero (by exact_mod_cast hχ.2.1)
  obtain ⟨x, rfl⟩ := hlev
  have hβ := (sub_first_layer_box_of_cited hE hH hU hF b hb hirr R S 0 0 hR hS hR hS x hχ).1
  refine ⟨generic_jantzen_one hb hirr hR hS hχ hβ hK, fun N i hi => ?_⟩
  by_cases hN : N < R * S
  · exact generic_layer_below hb hirr hR hS hK hN (by omega)
  · obtain ⟨M, rfl⟩ : ∃ M, N = R * S + M := ⟨N - R * S, by omega⟩
    exact (generic_layer_above hb hirr hR hS hχ hβ hK M).2 i hi

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) :
    Stmt_sub_generic_layers :=
  sub_generic_layers_of_cited hK hE hH hU hF

end Virasoro.P2
