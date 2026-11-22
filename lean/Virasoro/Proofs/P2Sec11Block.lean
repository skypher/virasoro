import Virasoro.Proofs.P2Sec11LayerIndep

/-!
# Proposition 11.2(ii): the summand `L(c⋆,μ^±)` of a layer (paper.tex l.2487–2495)

For a singular vector `χ` of level `ℓ` with `U(Vir_-)χ ⊂ J^{i+1}` (layer index `i + 1 ≥ 1`) and
the embedding `j_χ : M(c,μ+ℓ) → M(c,μ)`:
* `B^{(i+1)}(j_χ a, j_χ a') = γ ⟨a,a'⟩_{μ+ℓ}`, `γ = B^{(i+1)}(χ,χ)` (uniqueness of the
  contravariant form);
* `ρ^{(i+1)}(j_χ a, j_χ a') = σ ρ_{c,μ+ℓ,d}(a,a')`, `σ = ρ^{(i+1)}(χ,χ)` (uniqueness of the
  primary form);
* the images of a basis of `L(c,μ+ℓ)_M` span the level-`(ℓ+M)` part of `U(Vir_-)χ` modulo
  `J^{i+2}`.
-/

namespace Virasoro

open Polynomial Verma

variable {c μ d : ℂ} {i : ℕ}

/-- `ρ^{(i+1)}` is a Ward form on `J^{i+1}` (part (i)). -/
theorem isJWard_rhoJ (HV : VertexPartI c μ d) :
    IsJWard d (jantzen c μ (i + 1)) (rhoJ (pairing (C c) (C μ + X) (C d)) (i + 1)) := by
  have hT := isPrimaryPairing_pairing (c := C c) (h := C μ + (X : ℂ[X])) (C d)
  have G : VertexGen c μ (pairing (C c) (C μ + X) (C d)) i := vertexGen_of_clauses (HV i)
  exact ⟨fun hx hx' hy => rhoJ_add_left hT G hx hx' hy,
    fun a _ _ hx hy => rhoJ_smul_left hT G a hx hy, rhoJ_symm hT _,
    fun n _ _ hx hy => rhoJ_ward hT G n hx hy, fun n _ hx => L_mem_jantzen _ _ (i + 1) n hx⟩

/-- `ρ^{(i+1)}` on vectors is the vertex form on coordinates. -/
theorem rhoJ_pbwCoord (HV : VertexPartI c μ d) {N : ℕ} {u v : Nat.Partition N → ℂ}
    (hu : u ∈ jantzenLayer c μ N (i + 1)) (hv : v ∈ jantzenLayer c μ N (i + 1)) :
    rhoJ (pairing (C c) (C μ + X) (C d)) (i + 1) (pbwCoord N u) (pbwCoord N v) =
      vform c μ d N (i + 1) u v := by
  have hT := isPrimaryPairing_pairing (c := C c) (h := C μ + (X : ℂ[X])) (C d)
  have G : VertexGen c μ (pairing (C c) (C μ + X) (C d)) i := vertexGen_of_clauses (HV i)
  obtain ⟨wu, hwu⟩ := hu
  obtain ⟨wv, hwv⟩ := hv
  have h1 : IsJFamily c μ N (i + 1) u wu := hwu
  have h2 : IsJFamily c μ N (i + 1) v wv := hwv
  have e := rhoJ_eq hT G h1.inLat h2.inLat
  rw [h1.ev0, h2.ev0] at e
  rw [← e, primary_pbwCoord hT]
  exact (vform_fam HV h1 h2).2

section Emb

variable {ℓ : ℕ} {χ : Verma ℂ c μ} (j : Verma ℂ c (μ + ℓ) →ₗ[ℂ] Verma ℂ c μ)
  (hjl : ∀ (n : ℕ) (x : Verma ℂ c (μ + ℓ)), x ∈ level n → j x ∈ level (ℓ + n))

include hjl in
/-- The embedding commutes with the level components. -/
theorem emb_level_comp (M : ℕ) (y : Verma ℂ c (μ + ℓ)) :
    pbwCoord (ℓ + M) (Verma.comp (ℓ + M) (j y)) = j (pbwCoord M (Verma.comp M y)) := by
  have key : (pbwCoord (c := c) (h := μ) (ℓ + M)) ∘ₗ (Verma.comp (ℓ + M)) ∘ₗ j =
      j ∘ₗ (pbwCoord M) ∘ₗ (Verma.comp M) := by
    refine (pbwBasis c (μ + ℓ)).ext fun Y => ?_
    obtain ⟨m, Z⟩ := Y
    have hl : neg (c := c) (h := μ + ℓ) Z.word ∈ level m := by
      have := neg_mem_level (c := c) (h := μ + ℓ) _ Z.word (posWord_word Z) le_rfl
      rwa [word_sum'] at this
    simp only [LinearMap.comp_apply]
    rw [pbwBasis_apply]
    by_cases hm : m = M
    · subst hm
      rw [pbwCoord_comp_of_mem_level (hjl _ _ hl), pbwCoord_comp_of_mem_level hl]
    · rw [comp_of_mem_level_ne (by omega : ℓ + m ≠ ℓ + M) (hjl m _ hl),
        comp_of_mem_level_ne hm hl, map_zero, map_zero, map_zero]
  exact LinearMap.congr_fun key y

variable (hχ : IsSingular χ ℓ) (hsub : negSpan χ ≤ jantzen c μ (i + 1)) (hjhw : j hw = χ)
  (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v)) (hjr : ∀ x, j x ∈ negSpan χ)

include hjl hχ hsub hjhw hjL hjr in
/-- `B^{(i+1)}(j_χ a, j_χ a') = B^{(i+1)}(χ,χ) ⟨a,a'⟩_{μ+ℓ}` (l.2491–2493). -/
theorem jv_emb_coord {M : ℕ} (a a' : Nat.Partition M → ℂ) :
    jv c μ (i + 1) (ℓ + M) (j (pbwCoord M a)) (j (pbwCoord M a')) =
      jv c μ (i + 1) ℓ χ χ * gramForm c (μ + ℓ) M a a' := by
  have hx : j (pbwCoord M a') ∈ jantzen c μ (i + 1) := hsub (hjr _)
  have hxl : j (pbwCoord M a') ∈ level (ℓ + M) := hjl M _ ⟨a', rfl⟩
  have hneg : ∀ Y : Nat.Partition M, neg (c := c) (h := μ + ℓ) Y.word ∈ level M := fun Y => by
    have := neg_mem_level (c := c) (h := μ + ℓ) _ Y.word (posWord_word Y) le_rfl
    rwa [word_sum'] at this
  have e1 : j (pbwCoord M a) = ∑ Y : Nat.Partition M, a Y • j (neg Y.word) := by
    rw [pbwCoord_apply, map_sum]
    exact Finset.sum_congr rfl fun Y _ => map_smul _ _ _
  rw [jv_symm (hsub (hjr _)) (hjl M _ ⟨a, rfl⟩) hx hxl, e1,
    jv_sum_right _ _ _ hx hxl (fun Y _ => hsub (hjr _)) (fun Y _ => hjl M _ (hneg Y)),
    gramForm, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have h := jv_emb hχ hsub j hjhw hjL hjr hjl Y.word (posWord_word Y) (pbwCoord M a')
    (by rw [word_sum']; exact ⟨a', rfl⟩)
  rw [word_sum'] at h
  rw [jv_symm hx hxl (hsub (hjr _)) (hjl M _ (hneg Y)), h, shap_neg_pbwCoord]
  ring

include hjl hsub hjL hjr hjhw in
/-- `ρ^{(i+1)}(j_χ a, j_χ a') = ρ^{(i+1)}(χ,χ) ρ_{c,μ+ℓ,d}(a,a')` (l.2493–2494). -/
theorem rhoJ_emb_coord (HV : VertexPartI c μ d) {M : ℕ} (a a' : Nat.Partition M → ℂ) :
    rhoJ (pairing (C c) (C μ + X) (C d)) (i + 1) (j (pbwCoord M a)) (j (pbwCoord M a')) =
      rhoJ (pairing (C c) (C μ + X) (C d)) (i + 1) χ χ * torusForm c (μ + ℓ) d M a a' := by
  obtain ⟨η, hη, hW⟩ := (isJWard_rhoJ HV).pullback j hjL fun v => hsub (hjr v)
  have h1 := ward_eq_smul_pairing hW (pbwCoord M a) (pbwCoord M a')
  rw [hη, hη, hjhw, primary_pbwCoord (isPrimaryPairing_pairing d)] at h1
  exact h1

end Emb

end Virasoro
