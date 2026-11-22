import Virasoro.Proofs.P2Sec11Block
import Virasoro.Proofs.Sec8Smith7

/-!
# Proposition 11.2(ii): the two summands of a layer (paper.tex l.2487–2495)

`J^{i+1} = U(Vir_-)χ + U(Vir_-)χ'` with singular vectors of different levels `ℓ ≠ ℓ'`:
* the two summands are `B^{(i+1)}`-orthogonal ("a direct sum of non-isomorphic irreducibles,
  which are orthogonal under the contravariant form");
* for each summand, the images under `j_χ` of a family giving `T^irr_{N-ℓ}(c,μ+ℓ,d)` have Gram
  matrix `γ g`, vertex matrix `σ ρ`, and span the level-`N` part of `U(Vir_-)χ` modulo
  `J^{i+2}`.
-/

namespace Virasoro

open Polynomial Verma

variable {c μ d : ℂ} {i : ℕ}

/-- The two summands are `B^{(i+1)}`-orthogonal. -/
theorem jv_cross (hI : Cited_VermaHomInjective) {ℓ ℓ' N : ℕ} {χ χ' : Verma ℂ c μ}
    (hχ : IsSingular χ ℓ) (hχ' : IsSingular χ' ℓ') (hne : ℓ ≠ ℓ')
    (hJ : jantzen c μ (i + 1) = negSpan χ ⊔ negSpan χ') {z z' : Verma ℂ c μ}
    (hz : z ∈ negSpan χ) (hzl : z ∈ level N) (hz' : z' ∈ negSpan χ') (hzl' : z' ∈ level N) :
    jv c μ (i + 1) N z z' = 0 := by
  have hsub : negSpan χ ≤ jantzen c μ (i + 1) := by rw [hJ]; exact le_sup_left
  have hsub' : negSpan χ' ≤ jantzen c μ (i + 1) := by rw [hJ]; exact le_sup_right
  by_cases h1 : ℓ ≤ N
  · by_cases h2 : ℓ' ≤ N
    · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le h1
      obtain ⟨M', hM'⟩ := Nat.exists_eq_add_of_le h2
      obtain ⟨j, -, hjhw, hjL, hjr, hjl, hjneg⟩ := exists_emb hI hχ
      obtain ⟨j', -, hjhw', hjL', hjr', hjl', hjneg'⟩ := exists_emb hI hχ'
      rw [negSpan_eq_range j hjneg] at hz
      rw [negSpan_eq_range j' hjneg'] at hz'
      obtain ⟨y, rfl⟩ := hz
      obtain ⟨y', rfl⟩ := hz'
      have e1 : j y = j (pbwCoord M (Verma.comp M y)) := by
        rw [← emb_level_comp j hjl M y, pbwCoord_comp_of_mem_level hzl]
      have hzl2 : j' y' ∈ level (ℓ' + M') := hM' ▸ hzl'
      have e2 : j' y' = j' (pbwCoord M' (Verma.comp M' y')) := by
        rw [← emb_level_comp j' hjl' M' y', pbwCoord_comp_of_mem_level hzl2]
      rw [e1, e2]
      have hx : j' (pbwCoord M' (Verma.comp M' y')) ∈ jantzen c μ (i + 1) := hsub' (hjr' _)
      have hxl : j' (pbwCoord M' (Verma.comp M' y')) ∈ level (ℓ + M) := by
        rw [hM']
        exact hjl' M' _ ⟨_, rfl⟩
      have hneg : ∀ Y : Nat.Partition M, neg (c := c) (h := μ + ℓ) Y.word ∈ level M :=
        fun Y => by
          have := neg_mem_level (c := c) (h := μ + ℓ) _ Y.word (posWord_word Y) le_rfl
          rwa [word_sum'] at this
      have e3 : j (pbwCoord M (Verma.comp M y)) =
          ∑ Y : Nat.Partition M, Verma.comp M y Y • j (neg Y.word) := by
        rw [pbwCoord_apply, map_sum]
        exact Finset.sum_congr rfl fun Y _ => map_smul _ _ _
      rw [jv_symm (hsub (hjr _)) (hjl M _ ⟨_, rfl⟩) hx hxl, e3,
        jv_sum_right _ _ _ hx hxl (fun Y _ => hsub (hjr _)) (fun Y _ => hjl M _ (hneg Y))]
      refine Finset.sum_eq_zero fun Y _ => ?_
      have h := jv_orth hχ hne hsub hsub' j hjhw hjL hjr hjl j' hjL' hjr' hjl' Y.word
        (posWord_word Y) M' (by rw [word_sum']; exact hM') (pbwCoord M' (Verma.comp M' y'))
        ⟨_, rfl⟩
      rw [word_sum'] at h
      rw [jv_symm hx hxl (hsub (hjr _)) (hjl M _ (hneg Y)), h, mul_zero]
    · have h0 : z' = 0 := by
        rw [← pbwCoord_comp_of_mem_level hzl',
          comp_negSpan_eq_zero (mem_level_of_L_zero hχ'.2.1) (not_le.1 h2) hz', map_zero]
      rw [h0]
      exact jv_zero_right (hsub hz) hzl
  · have h0 : z = 0 := by
      rw [← pbwCoord_comp_of_mem_level hzl,
        comp_negSpan_eq_zero (mem_level_of_L_zero hχ.2.1) (not_le.1 h1) hz, map_zero]
    rw [h0]
    exact jv_zero_left (hsub' hz') hzl'

/-- The summand of `χ` in the layer `i + 1` at level `N`: a family `F` in the level-`N` part of
`U(Vir_-)χ` with Gram matrix `γ g`, vertex matrix `σ ρ`, `tr(g⁻¹ρ) = T^irr_{N-ℓ}(c,μ+ℓ,d)`
(absent for `N < ℓ`), spanning that part modulo `J^{i+2}`. -/
theorem sign_block (hI : Cited_VermaHomInjective) (HV : VertexPartI c μ d) {ℓ ℓ' N : ℕ}
    {χ χ' : Verma ℂ c μ} (hχ : IsSingular χ ℓ) (hχ' : IsSingular χ' ℓ') (hne : ℓ ≠ ℓ')
    (hJ : jantzen c μ (i + 1) = negSpan χ ⊔ negSpan χ') (x : Nat.Partition ℓ → ℂ)
    (hx : pbwCoord ℓ x = χ) (Tirr : ℂ)
    (hT : ℓ ≤ N → IsIrrTrace c (μ + ℓ) d (N - ℓ) Tirr) :
    ∃ (n : ℕ) (F : Fin n → Nat.Partition N → ℂ) (g ρm : Matrix (Fin n) (Fin n) ℂ),
      (∀ α, pbwCoord (c := c) (h := μ) N (F α) ∈ negSpan χ) ∧ g.det ≠ 0 ∧
      (∀ α β, jform c μ N (i + 1) (F α) (F β) = jform c μ ℓ (i + 1) x x * g α β) ∧
      (∀ α β, vform c μ d N (i + 1) (F α) (F β) = vform c μ d ℓ (i + 1) x x * ρm α β) ∧
      (∑ α, ∑ β, g⁻¹ α β * ρm β α = if ℓ ≤ N then Tirr else 0) ∧
      (∀ z ∈ negSpan χ, z ∈ level N → Verma.comp N z ∈
        Submodule.span ℂ (Set.range F) ⊔ jantzenLayer c μ N (i + 1 + 1)) := by
  have hsub : negSpan χ ≤ jantzen c μ (i + 1) := by rw [hJ]; exact le_sup_left
  by_cases hle : ℓ ≤ N
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hT' := hT hle
    rw [Nat.add_sub_cancel_left] at hT'
    obtain ⟨n, E, hLI, hc, hdet, hTe⟩ := hT'
    obtain ⟨j, -, hjhw, hjL, hjr, hjl, hjneg⟩ := exists_emb hI hχ
    have hF : ∀ a : Nat.Partition M → ℂ,
        pbwCoord (ℓ + M) (Verma.comp (ℓ + M) (j (pbwCoord M a))) = j (pbwCoord M a) :=
      fun a => pbwCoord_comp_of_mem_level (hjl M _ ⟨a, rfl⟩)
    have hFl : ∀ a : Nat.Partition M → ℂ,
        Verma.comp (ℓ + M) (j (pbwCoord M a)) ∈ jantzenLayer c μ (ℓ + M) (i + 1) :=
      fun a => comp_mem_layer (hsub (hjr _)) (hjl M _ ⟨a, rfl⟩)
    have hχJ : χ ∈ jantzen c μ (i + 1) := by rw [← hjhw]; exact hsub (hjr _)
    have hxl : x ∈ jantzenLayer c μ ℓ (i + 1) := by
      have := comp_mem_layer hχJ (mem_level_of_L_zero hχ.2.1)
      rwa [← hx, comp_pbwCoord_same] at this
    have hγ : jv c μ (i + 1) ℓ χ χ = jform c μ ℓ (i + 1) x x := by
      unfold jv
      rw [← hx, comp_pbwCoord_same]
    have hσ : rhoJ (pairing (C c) (C μ + X) (C d)) (i + 1) χ χ = vform c μ d ℓ (i + 1) x x := by
      rw [← hx]
      exact rhoJ_pbwCoord HV hxl hxl
    refine ⟨n, fun α => Verma.comp (ℓ + M) (j (pbwCoord M (E α))),
      Matrix.of fun α β => gramForm c (μ + ℓ) M (E α) (E β),
      Matrix.of fun α β => torusForm c (μ + ℓ) d M (E α) (E β), fun α => ?_, hdet,
      fun α β => ?_, fun α β => ?_, ?_, ?_⟩
    · rw [hF]
      exact hjr _
    · show jv c μ (i + 1) (ℓ + M) (j (pbwCoord M (E α))) (j (pbwCoord M (E β))) = _
      rw [jv_emb_coord j hjl hχ hsub hjhw hjL hjr, hγ]
      rfl
    · rw [← rhoJ_pbwCoord HV (hFl _) (hFl _), hF, hF, rhoJ_emb_coord j hjl hsub hjhw hjL hjr HV,
        hσ]
      rfl
    · rw [if_pos hle]
      exact hTe.symm
    · intro z hz _
      rw [negSpan_eq_range j hjneg] at hz
      obtain ⟨y₀, rfl⟩ := hz
      have e := congrArg (Verma.comp (c := c) (h := μ) (ℓ + M)) (emb_level_comp j hjl M y₀)
      rw [comp_pbwCoord_same] at e
      rw [e]
      have ha : Verma.comp M y₀ ∈ Submodule.span ℂ (Set.range E) ⊔
          LinearMap.ker (gram c (μ + ℓ) M).mulVecLin := by
        rw [hc.sup_eq_top]
        trivial
      obtain ⟨a₁, ha₁, k, hk, hak⟩ := Submodule.mem_sup.1 ha
      rw [← hak, map_add, map_add, map_add]
      refine Submodule.add_mem_sup ?_ ?_
      · let Φ : (Nat.Partition M → ℂ) →ₗ[ℂ] (Nat.Partition (ℓ + M) → ℂ) :=
          (Verma.comp (ℓ + M)) ∘ₗ j ∘ₗ (pbwCoord M)
        have h1 : Φ a₁ ∈ (Submodule.span ℂ (Set.range E)).map Φ := Submodule.mem_map_of_mem ha₁
        rw [Submodule.map_span, ← Set.range_comp] at h1
        exact h1
      · have hk0 : (gram c (μ + ℓ) M).mulVec k = 0 := by
          rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
          exact hk
        exact comp_mem_layer (layer_kernel hI hχ hχ' hne hJ k (Or.inr hk0) j hjhw hjL hjr hjl
          hjneg) (hjl M _ ⟨k, rfl⟩)
  · have hlt : N < ℓ := not_le.1 hle
    refine ⟨0, fun α => α.elim0, 0, 0, fun α => α.elim0, ?_, fun α => α.elim0,
      fun α => α.elim0, ?_, ?_⟩
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    · rw [if_neg hle]
      simp
    · intro z hz _
      rw [comp_negSpan_eq_zero (mem_level_of_L_zero hχ.2.1) hlt hz]
      exact Submodule.zero_mem _

end Virasoro
