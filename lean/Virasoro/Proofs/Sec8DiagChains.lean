import Virasoro.Proofs.Sec8DiagLead

/-!
# Lemma 8.5(i): the leading term of a node chain

Every member of `nodeChains a μ` has odd positive steps and ends at `μ`; the germ `δ_g` of the
label from `ν` to `ν'` is `h_{νν'} t + O(t²)`; consecutive slopes differ; and the tail of a chain
entered from `π` has order `j - D(ν,μ)` with leading coefficient
`∏ρ / ∏(h_{i-1} - h_i) · h_n^j/j!`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

/-- The steps of a list of nodes are odd and positive and it ends at `μ`. -/
def StepsOK (μ : Node) : List Node → Prop
  | [] => False
  | [x] => x = μ
  | x :: y :: l => x.2 < y.2 ∧ (y.2 - x.2) % 2 = 1 ∧ StepsOK μ (y :: l)

theorem stepsOK_of_mem {a μ : Node} {γ : List Node} (hγ : γ ∈ nodeChains a μ) :
    ∃ x l, γ = a :: x :: l ∧ a.2 < x.2 ∧ (x.2 - a.2) % 2 = 1 ∧ StepsOK μ (x :: l) := by
  rcases Nat.lt_or_ge a.2 μ.2 with h | h
  · rw [nodeChains_of_lt h] at hγ
    rcases Finset.mem_union.1 hγ with h1 | h1
    · split_ifs at h1 with ho
      · rw [Finset.mem_singleton.1 h1]; exact ⟨μ, [], rfl, h, ho, rfl⟩
      · simp at h1
    · obtain ⟨θ, -, h2⟩ := Finset.mem_biUnion.1 h1
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h2
      have hθ := (Finset.mem_filter.1 θ.2).1
      obtain ⟨hlt, hodd⟩ := firstSteps_props hθ
      obtain ⟨x, l, rfl, h3, h4, h5⟩ := stepsOK_of_mem hγ'
      exact ⟨θ.1, x :: l, rfl, hlt, hodd, ⟨h3, h4, h5⟩⟩
  · rw [nodeChains_of_le h] at hγ; simp at hγ
termination_by μ.2 - a.2
decreasing_by
  have hm := (Finset.mem_filter.1 θ.2).1
  simp only [firstSteps, Finset.mem_union, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_Ioo] at hm
  rcases hm with hm | hm
  · omega
  · split_ifs at hm <;> simp_all

theorem stepsOK_last {μ x : Node} {l : List Node} (h : StepsOK μ (x :: l)) : x.2 ≤ μ.2 := by
  induction l generalizing x with
  | nil => simp only [StepsOK] at h; rw [h]
  | cons y l ih => obtain ⟨h1, -, h3⟩ := h; exact h1.le.trans (ih h3)

section Germs

variable (hset : MinimalSetting p p' r s b)
include hset

theorem b_ne_zero_of : b ≠ 0 := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  rintro rfl
  have h0 : -(p' : ℂ) / p ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
  exact h0 (by simpa using hset.2.2.2.2.2.2.2.2.symm)

/-- `δ_g = h_{νν'} t + O(t²)` for the label from `ν` to `ν'`. -/
theorem lv_nodeDel {ν ν' : Node} (hlt : ν.2 < ν'.2) (hodd : (ν'.2 - ν.2) % 2 = 1) :
    LV (nodeDel p p' r s b ν ν') 1 (nodeH p p' r s b ν ν') := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb0 := b_ne_zero_of hset
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  obtain ⟨-, -, -, hxy⟩ := node_labels_ii hset ν ν' hlt hodd
  have hv := regVal_hG hbs (nodeLabel p p' r s ν ν')
  have h0 : (nodeDel p p' r s b ν ν').coeff 0 = 0 := by
    unfold nodeDel delG deltaG
    rw [HahnSeries.coeff_sub, hv.2, (j2_C (kacHL (nodeLabel p p' r s ν ν') (bsC b))).2.1, sub_self]
  have hreg : OrdGE (nodeDel p p' r s b ν ν') 0 := by
    unfold nodeDel delG deltaG
    exact hv.1.sub (j2_C _).1
  refine ⟨?_, ?_⟩
  · rw [ordGE_iff] at hreg ⊢
    intro m hm
    rcases lt_or_eq_of_le (show m ≤ 0 by omega) with h | h
    · exact hreg m h
    · rw [h]; exact h0
  · unfold nodeDel nodeH
    rw [node_slope hp hp' hset.2.2.2.2.2.2.2.2]
    congr 2
    have : ((((p' : ℤ) * (nodeLabel p p' r s ν ν').1 - p * (nodeLabel p p' r s ν ν').2 : ℤ) : ℂ) *
        (((p' : ℤ) * (nodeLabel p p' r s ν ν').1 + p * (nodeLabel p p' r s ν ν').2 : ℤ) : ℂ)) =
        ((nodeS p p' r s ν : ℤ) : ℂ) * ((nodeS p p' r s ν' : ℤ) : ℂ) := by
      rw [← Int.cast_mul, ← Int.cast_mul, hxy]
    rw [this]

/-- Consecutive slopes differ: `h_{πν} ≠ h_{νν'}` along odd positive steps. -/
theorem nodeH_link_ne {π ν ν' : Node} (h1 : π.2 < ν.2) (h1o : (ν.2 - π.2) % 2 = 1)
    (h2 : ν.2 < ν'.2) (h2o : (ν'.2 - ν.2) % 2 = 1) :
    nodeH p p' r s b π ν - nodeH p p' r s b ν ν' ≠ 0 := by
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb0 := b_ne_zero_of hset
  have hS : nodeS p p' r s ν ≠ 0 := by
    have := node_abs_lt hset h1 h1o
    intro h; rw [h, abs_zero] at this; linarith [abs_nonneg (nodeS p p' r s π)]
  have hne : nodeS p p' r s ν' ≠ nodeS p p' r s π := by
    have a1 := node_abs_lt hset h1 h1o
    have a2 := node_abs_lt hset h2 h2o
    intro h; rw [h] at a2; linarith
  unfold nodeH
  rw [← map_sub]
  refine (map_ne_zero _).2 ?_
  have e : varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) - (nodeS p p' r s π : ℂ) *
      (nodeS p p' r s ν : ℂ)) - varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) -
      (nodeS p p' r s ν : ℂ) * (nodeS p p' r s ν' : ℂ)) =
      varsig p' b * (nodeS p p' r s ν : ℂ) * ((nodeS p p' r s ν' : ℂ) - (nodeS p p' r s π : ℂ)) := by
    ring
  rw [e]
  refine mul_ne_zero (mul_ne_zero ?_ (by exact_mod_cast hS)) (sub_ne_zero.2 (by exact_mod_cast hne))
  unfold varsig
  exact div_ne_zero hb0 (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp'.ne')))

/-- The tail of a chain entered from `π`. -/
theorem tail_lead (j : ℕ) (μ : Node) :
    ∀ (l : List Node) (π ν : Node), StepsOK μ (ν :: l) → π.2 < ν.2 → (ν.2 - π.2) % 2 = 1 →
      LV (chainTailProd p p' r s b j (nodeDel p p' r s b π ν) ν l) ((j : ℤ) - (μ.2 - ν.2))
        (chainRho p p' r s b (ν :: l) / chainLinks p p' r s b (π :: ν :: l) *
          chainHn p p' r s b (π :: ν :: l) ^ j / (j.factorial : Kd)) := by
  intro l
  induction l with
  | nil =>
    intro π ν hok hlt hodd
    simp only [StepsOK] at hok
    subst hok
    have h := ((lv_nodeDel hset hlt hodd).pow j).div (lv_natCast (K := Kd) j.factorial)
      (by exact_mod_cast (Nat.factorial_pos j).ne')
    simp only [chainTailProd, chainRho, chainLinks, chainHn]
    refine h.congr (by push_cast; ring) (by ring)
  | cons ν' l ih =>
    intro π ν hok hlt hodd
    obtain ⟨h2, h2o, hok'⟩ := hok
    have hR := lem_node_poles p p' r s b hset ν ν' h2 h2o
    have hRv : LV (nodeR p p' r s b ν ν') (1 - ((ν'.2 : ℤ) - ν.2)) (nodeRho p p' r s b ν ν') :=
      ⟨by simpa [OrdGE] using hR.1, rfl⟩
    have hlink := (lv_nodeDel hset hlt hodd).sub (lv_nodeDel hset h2 h2o)
    have hlne := nodeH_link_ne hset hlt hodd h2 h2o
    have hq := hRv.div hlink hlne
    have hIH := ih ν ν' hok' h2 h2o
    have hprod := hq.mul hIH
    simp only [chainTailProd]
    refine hprod.congr (by push_cast; ring) ?_
    simp only [chainRho, chainLinks, chainHn]
    field_simp

end Germs

end Virasoro
