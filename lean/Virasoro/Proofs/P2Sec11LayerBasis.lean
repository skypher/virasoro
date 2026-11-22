import Virasoro.Proofs.P2Sec11SignBlock

/-!
# Proposition 11.2: the layers `i ≥ 1` and the proposition (paper.tex l.2487–2495)

`J^i/J^{i+1} ≅ L(c⋆,μ⁺_{k₀+i}) ⊕ L(c⋆,μ⁻_{k₀+i})`: the images under `j_±` of families giving the
irreducible traces of the two summands form a basis of `J^i_N/J^{i+1}_N` in which `B̄^{(i)}_N`
is block diagonal with blocks `γ^±_i B̄_L`, and the diagonal blocks of `ρ̄^{(i)}_N` are
`σ^±_i ρ̄_L`; the off-diagonal blocks of `ρ̄^{(i)}_N` drop out of the trace.
-/

namespace Virasoro

open Polynomial Verma

variable {c μ d : ℂ} {i : ℕ}

theorem jantzenLayer_succ_le (N j : ℕ) : jantzenLayer c μ N (j + 1) ≤ jantzenLayer c μ N j := by
  rintro v ⟨w, h0, hd⟩
  exact ⟨w, h0, fun Y => (pow_dvd_pow _ (Nat.le_succ j)).trans (hd Y)⟩

theorem jform_sum_left {κ : Type*} [Fintype κ] {N j : ℕ} (cc : κ → ℂ)
    (E : κ → Nat.Partition N → ℂ) (hE : ∀ k, E k ∈ jantzenLayer c μ N j)
    {v : Nat.Partition N → ℂ} (hv : v ∈ jantzenLayer c μ N j) :
    jform c μ N j (∑ k, cc k • E k) v = ∑ k, cc k * jform c μ N j (E k) v := by
  have h : jformL c μ N j (∑ k, cc k • (⟨E k, hE k⟩ : jantzenLayer c μ N j)) ⟨v, hv⟩ =
      ∑ k, cc k * jform c μ N j (E k) v := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    rfl
  have e : ((∑ k, cc k • (⟨E k, hE k⟩ : jantzenLayer c μ N j) : jantzenLayer c μ N j) :
      Nat.Partition N → ℂ) = ∑ k, cc k • E k := by
    rw [Submodule.coe_sum]
    rfl
  rw [← e]
  exact h

/-- The level-`N` part of a vector of `U(Vir_-)χ` lies in `U(Vir_-)χ`. -/
theorem level_part_mem {ℓ : ℕ} {χ : Verma ℂ c μ} (hχ : IsSingular χ ℓ) (N : ℕ)
    {b : Verma ℂ c μ} (hb : b ∈ negSpan χ) : pbwCoord N (Verma.comp N b) ∈ negSpan χ := by
  have h := pbwCoord_comp_negSpan_mem_span (mem_level_of_L_zero hχ.2.1) N hb
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨w, hw, -, rfl⟩
  exact negOp_smul_mem_negSpan χ hw

set_option maxHeartbeats 800000 in
/-- The trace of the layer `i + 1` in the basis adapted to the two summands
(l.2487–2495). -/
theorem layer_trace_two (hI : Cited_VermaHomInjective) (HV : VertexPartI c μ d)
    {ℓp ℓm N : ℕ} {χp χm : Verma ℂ c μ} (hχp : IsSingular χp ℓp) (hχm : IsSingular χm ℓm)
    (hne : ℓp ≠ ℓm) (hJ : jantzen c μ (i + 1) = negSpan χp ⊔ negSpan χm)
    (xp : Nat.Partition ℓp → ℂ) (hxp : pbwCoord ℓp xp = χp) (xm : Nat.Partition ℓm → ℂ)
    (hxm : pbwCoord ℓm xm = χm) (hγp : jform c μ ℓp (i + 1) xp xp ≠ 0)
    (hγm : jform c μ ℓm (i + 1) xm xm ≠ 0) (Tp Tm : ℂ)
    (hTp : ℓp ≤ N → IsIrrTrace c (μ + ℓp) d (N - ℓp) Tp)
    (hTm : ℓm ≤ N → IsIrrTrace c (μ + ℓm) d (N - ℓm) Tm) :
    IsLayerTrace c μ d N (i + 1)
      ((if ℓp ≤ N then
          vform c μ d ℓp (i + 1) xp xp / jform c μ ℓp (i + 1) xp xp * Tp else 0) +
        (if ℓm ≤ N then
          vform c μ d ℓm (i + 1) xm xm / jform c μ ℓm (i + 1) xm xm * Tm else 0)) := by
  classical
  obtain ⟨np, Fp, gp, rp, mp, dp, jp, vp, tp, sp⟩ :=
    sign_block hI HV hχp hχm hne hJ xp hxp Tp hTp
  obtain ⟨nm, Fm, gm, rm, mm, dm, jm, vm, tm, sm⟩ :=
    sign_block hI HV hχm hχp hne.symm (by rw [hJ, sup_comm]) xm hxm Tm hTm
  have hsubp : negSpan χp ≤ jantzen c μ (i + 1) := by rw [hJ]; exact le_sup_left
  have hsubm : negSpan χm ≤ jantzen c μ (i + 1) := by rw [hJ]; exact le_sup_right
  have memp : ∀ α, Fp α ∈ jantzenLayer c μ N (i + 1) := fun α => by
    have := comp_mem_layer (hsubp (mp α)) ⟨Fp α, rfl⟩
    rwa [comp_pbwCoord_same] at this
  have memm : ∀ β, Fm β ∈ jantzenLayer c μ N (i + 1) := fun β => by
    have := comp_mem_layer (hsubm (mm β)) ⟨Fm β, rfl⟩
    rwa [comp_pbwCoord_same] at this
  have cross : ∀ α β, jform c μ N (i + 1) (Fp α) (Fm β) = 0 := fun α β => by
    have := jv_cross hI hχp hχm hne hJ (mp α) ⟨Fp α, rfl⟩ (mm β) ⟨Fm β, rfl⟩
    unfold jv at this
    rwa [comp_pbwCoord_same, comp_pbwCoord_same] at this
  have cross' : ∀ β α, jform c μ N (i + 1) (Fm β) (Fp α) = 0 := fun β α => by
    rw [jform_symm c μ (memm β) (memp α)]
    exact cross α β
  have memE : ∀ k, Sum.elim Fp Fm k ∈ jantzenLayer c μ N (i + 1) := by
    rintro (α | β)
    · exact memp α
    · exact memm β
  have hzero : ∀ cc : Fin np ⊕ Fin nm → ℂ,
      (∑ k, cc k • Sum.elim Fp Fm k) ∈ jantzenLayer c μ N (i + 1 + 1) → ∀ k, cc k = 0 := by
    intro cc hmem
    have hpair : ∀ v ∈ jantzenLayer c μ N (i + 1),
        ∑ k, cc k * jform c μ N (i + 1) (Sum.elim Fp Fm k) v = 0 := fun v hv =>
      (jform_sum_left cc _ memE hv).symm.trans (jform_rad_zero hmem hv)
    have hp : (fun α => cc (Sum.inl α)) = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero dp
      funext α₀
      have h := hpair (Fp α₀) (memp α₀)
      rw [Fintype.sum_sum_type] at h
      simp only [Sum.elim_inl, Sum.elim_inr, jp, cross', mul_zero, Finset.sum_const_zero,
        add_zero] at h
      have h' : jform c μ ℓp (i + 1) xp xp *
          (Matrix.vecMul (fun α => cc (Sum.inl α)) gp α₀) = 0 := by
        simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
        rw [← h]
        exact Finset.sum_congr rfl fun _ _ => by ring
      exact (mul_eq_zero.1 h').resolve_left hγp
    have hm : (fun β => cc (Sum.inr β)) = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero dm
      funext β₀
      have h := hpair (Fm β₀) (memm β₀)
      rw [Fintype.sum_sum_type] at h
      simp only [Sum.elim_inl, Sum.elim_inr, jm, cross, mul_zero, Finset.sum_const_zero,
        zero_add] at h
      have h' : jform c μ ℓm (i + 1) xm xm *
          (Matrix.vecMul (fun β => cc (Sum.inr β)) gm β₀) = 0 := by
        simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
        rw [← h]
        exact Finset.sum_congr rfl fun _ _ => by ring
      exact (mul_eq_zero.1 h').resolve_left hγm
    rintro (α | β)
    · exact congrFun hp α
    · exact congrFun hm β
  have hA : (Matrix.of fun k k' =>
      jform c μ N (i + 1) (Sum.elim Fp Fm k) (Sum.elim Fp Fm k')) =
      Matrix.fromBlocks (jform c μ ℓp (i + 1) xp xp • gp) 0 0
        (jform c μ ℓm (i + 1) xm xm • gm) := by
    refine Matrix.ext fun k k' => ?_
    rcases k with α | β <;> rcases k' with α' | β' <;> simp [jp, jm, cross, cross']
  have hAinv : (Matrix.fromBlocks (jform c μ ℓp (i + 1) xp xp • gp) 0 0
      (jform c μ ℓm (i + 1) xm xm • gm))⁻¹ =
      Matrix.fromBlocks ((jform c μ ℓp (i + 1) xp xp)⁻¹ • gp⁻¹) 0 0
        ((jform c μ ℓm (i + 1) xm xm)⁻¹ • gm⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, smul_zero, mul_inv_cancel₀ hγp, mul_inv_cancel₀ hγm, inv_mul_cancel₀ hγp,
      inv_mul_cancel₀ hγm, one_smul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 dp),
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 dm), Matrix.fromBlocks_one]
  refine ⟨Fin np ⊕ Fin nm, inferInstance, inferInstance, Sum.elim Fp Fm, memE, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact Fintype.linearIndependent_iff.2 fun cc h0 =>
      hzero cc (by rw [h0]; exact Submodule.zero_mem _)
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨cc, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
    exact Finset.sum_eq_zero fun k _ => by rw [hzero cc hv' k, zero_smul]
  · apply le_antisymm
    · exact sup_le (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact memE k))
        (jantzenLayer_succ_le N (i + 1))
    · intro u hu
      have huJ : pbwCoord (c := c) (h := μ) N u ∈ jantzen c μ (i + 1) := pbwCoord_mem_jantzen hu
      rw [hJ] at huJ
      obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.1 huJ
      have h1 := sp _ (level_part_mem hχp N hb) ⟨_, rfl⟩
      rw [comp_pbwCoord_same] at h1
      have h2 := sm _ (level_part_mem hχm N hb') ⟨_, rfl⟩
      rw [comp_pbwCoord_same] at h2
      have e : u = Verma.comp N b + Verma.comp N b' := by
        rw [← map_add, hbb, comp_pbwCoord_same]
      rw [e]
      have lp : Submodule.span ℂ (Set.range Fp) ⊔ jantzenLayer c μ N (i + 1 + 1) ≤
          Submodule.span ℂ (Set.range (Sum.elim Fp Fm)) ⊔ jantzenLayer c μ N (i + 1 + 1) :=
        sup_le_sup_right (Submodule.span_mono (by
          rintro _ ⟨α, rfl⟩; exact ⟨Sum.inl α, rfl⟩)) _
      have lm : Submodule.span ℂ (Set.range Fm) ⊔ jantzenLayer c μ N (i + 1 + 1) ≤
          Submodule.span ℂ (Set.range (Sum.elim Fp Fm)) ⊔ jantzenLayer c μ N (i + 1 + 1) :=
        sup_le_sup_right (Submodule.span_mono (by
          rintro _ ⟨β, rfl⟩; exact ⟨Sum.inr β, rfl⟩)) _
      exact Submodule.add_mem _ (lp h1) (lm h2)
  · rw [hA, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hγp) dp) (mul_ne_zero (pow_ne_zero _ hγm) dm)
  · rw [hA, hAinv, Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add, vp, vm,
      Matrix.smul_apply, smul_eq_mul]
    have ep : ∑ α, ∑ β, (jform c μ ℓp (i + 1) xp xp)⁻¹ * gp⁻¹ α β *
        (vform c μ d ℓp (i + 1) xp xp * rp β α) =
        vform c μ d ℓp (i + 1) xp xp / jform c μ ℓp (i + 1) xp xp *
          ∑ α, ∑ β, gp⁻¹ α β * rp β α := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have em : ∑ α, ∑ β, (jform c μ ℓm (i + 1) xm xm)⁻¹ * gm⁻¹ α β *
        (vform c μ d ℓm (i + 1) xm xm * rm β α) =
        vform c μ d ℓm (i + 1) xm xm / jform c μ ℓm (i + 1) xm xm *
          ∑ α, ∑ β, gm⁻¹ α β * rm β α := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [ep, em, tp, tm]
    split_ifs <;> ring

/-- `Stmt_sub_vertex_layer_basis` (paper.tex l.2487–2495). -/
theorem sub_vertex_layer_basis (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_layer_basis := by
  intro p p' r s b hset ε k₀ k m hk hm c μ d lev wp wm hw xp xm hx N i hi Tp Tm hTp hTm
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have HV : VertexPartI c μ d := fun i N₁ N₂ a a₂ wa wb ha hb =>
    vertex_part_i hJ hH hU hF hI p p' r s b hset ε k₀ k m hk hm _
      (Verma.isPrimaryPairing_pairing _) i N₁ N₂ a a₂ wa wb ha hb
  have hγ := sub_vertex_gamma hJ hU hI p p' r s b hset ε k₀ wp wm hw xp xm hx (i + 1) hi
  obtain ⟨hsing, hlayer⟩ := id hw
  obtain ⟨hsp, hsm⟩ := hsing (i + 1) hi
  have h1 := ellOrb_lt_add (by omega) (by omega) hr0 hr hs0 hs ε k₀ (i + 1) hi true
  have h2 := ellOrb_lt_add (by omega) (by omega) hr0 hr hs0 hs ε k₀ (i + 1) hi false
  have hne : ellOrb p p' r s true (k₀ + (i + 1)) - ellOrb p p' r s ε k₀ ≠
      ellOrb p p' r s false (k₀ + (i + 1)) - ellOrb p p' r s ε k₀ := by
    have hk0 : k₀ + (i + 1) ≠ 0 := by omega
    have h3 : ellOrb p p' r s true (k₀ + (i + 1)) ≠ ellOrb p p' r s false (k₀ + (i + 1)) := by
      have := ellPlus_ne_ellMinus hcop hr0 hr hs hn1 (k := k₀ + (i + 1)) (by omega)
      unfold ellOrb
      rw [if_neg hk0, if_neg hk0]
      simpa using this
    omega
  have hTp' : ellOrb p p' r s true (k₀ + (i + 1)) - ellOrb p p' r s ε k₀ ≤ N →
      IsIrrTrace c (μ + ((ellOrb p p' r s true (k₀ + (i + 1)) - ellOrb p p' r s ε k₀ : ℕ) : ℂ))
        d (N - (ellOrb p p' r s true (k₀ + (i + 1)) - ellOrb p p' r s ε k₀)) Tp := fun h => by
    have := hTp h
    rwa [← muOrb_add_lev (by omega) (by omega) hr hs ε k₀ true (k₀ + (i + 1)) h1.le] at this
  have hTm' : ellOrb p p' r s false (k₀ + (i + 1)) - ellOrb p p' r s ε k₀ ≤ N →
      IsIrrTrace c (μ + ((ellOrb p p' r s false (k₀ + (i + 1)) - ellOrb p p' r s ε k₀ : ℕ) : ℂ))
        d (N - (ellOrb p p' r s false (k₀ + (i + 1)) - ellOrb p p' r s ε k₀)) Tm := fun h => by
    have := hTm h
    rwa [← muOrb_add_lev (by omega) (by omega) hr hs ε k₀ false (k₀ + (i + 1)) h2.le] at this
  exact layer_trace_two hI HV hsp hsm hne (hlayer (i + 1) hi) (xp (i + 1)) (hx (i + 1) hi).1
    (xm (i + 1)) (hx (i + 1) hi).2 hγ.1 hγ.2 Tp Tm hTp' hTm'

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_layer_basis := sub_vertex_layer_basis hJ hH hU hF hI

/-- Proposition 11.2 (Jantzen vertex filtration), paper.tex l.2374–2495, from the cited Jantzen
layers of the orbit, the normalization identities, uniqueness of singular vectors, the fusion
polynomial and injectivity of homomorphisms between Verma modules.

Paper label: prop:jantzen-vertex -/
theorem prop_jantzen_vertex_of_cited (hJ : Cited_JantzenLayersOrbit)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) : Stmt_prop_jantzen_vertex :=
  prop_jantzen_vertex_of_basis hJ hH hU hF hI (sub_vertex_layer_basis hJ hH hU hF hI)

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_prop_jantzen_vertex := prop_jantzen_vertex_of_cited hJ hH hU hF hI

end Virasoro
