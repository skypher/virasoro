import Virasoro.Proofs.P2Sec11LayerNondeg
import Virasoro.Proofs.P2Sec11TraceChange

/-!
# Proposition 11.2(ii): the trace of a layer does not depend on the basis (paper.tex l.2472–2495)

`B^{(i)}` and `ρ^{(i)}` are bilinear forms on `J^i_N` that vanish on `J^{i+1}_N` in both slots,
so `Tr_{J^i_N/J^{i+1}_N}((B̄^{(i)}_N)⁻¹ρ̄^{(i)}_N)` is the same in every basis of
`J^i_N/J^{i+1}_N`.  The identification of the layers `i ≥ 1` then needs the trace in one basis:
the sub-statement `Stmt_sub_vertex_layer_basis`.
-/

namespace Virasoro

open Polynomial Verma

variable {c μ d : ℂ} {N i : ℕ}

theorem IsJFamily.add' {u u' : Nat.Partition N → ℂ} {w w' : Nat.Partition N → ℂ[X]}
    (h : IsJFamily c μ N i u w) (h' : IsJFamily c μ N i u' w') :
    IsJFamily c μ N i (u + u') (w + w') :=
  ⟨fun Y => by simp [h.1 Y, h'.1 Y], fun Y => by
    rw [Matrix.mulVec_add]; exact dvd_add (h.2 Y) (h'.2 Y)⟩

theorem IsJFamily.smul' (a : ℂ) {u : Nat.Partition N → ℂ} {w : Nat.Partition N → ℂ[X]}
    (h : IsJFamily c μ N i u w) : IsJFamily c μ N i (a • u) (C a • w) :=
  ⟨fun Y => by simp [h.1 Y], fun Y => by
    rw [Matrix.mulVec_smul]; exact Dvd.dvd.mul_left (h.2 Y) _⟩

section JForm

variable {u u' v : Nat.Partition N → ℂ}

theorem jform_add_left' (hu : u ∈ jantzenLayer c μ N i) (hu' : u' ∈ jantzenLayer c μ N i)
    (hv : v ∈ jantzenLayer c μ N i) :
    jform c μ N i (u + u') v = jform c μ N i u v + jform c μ N i u' v := by
  have h := jform_add_smul_left (1 : ℂ) hu hu' hv
  rwa [one_smul, one_mul] at h

theorem jform_zero_left' (hv : v ∈ jantzenLayer c μ N i) : jform c μ N i 0 v = 0 := by
  have h := jform_add_left' (Submodule.zero_mem _) (Submodule.zero_mem _) hv
  have e : (0 : Nat.Partition N → ℂ) + 0 = 0 := add_zero 0
  rw [e] at h
  linear_combination -h

theorem jform_smul_left' (a : ℂ) (hu : u ∈ jantzenLayer c μ N i)
    (hv : v ∈ jantzenLayer c μ N i) : jform c μ N i (a • u) v = a * jform c μ N i u v := by
  have h := jform_add_smul_left a hu (Submodule.zero_mem _) hv
  rwa [add_zero, jform_zero_left' hv, add_zero] at h

/-- `J^{i+1}_N ⊂ rad B^{(i)}`. -/
theorem jform_rad_zero (hu : u ∈ jantzenLayer c μ N (i + 1)) (hv : v ∈ jantzenLayer c μ N i) :
    jform c μ N i u v = 0 := by
  obtain ⟨wu, hu0, hud⟩ := hu
  obtain ⟨wv, hv'⟩ := hv
  have hu' : IsJFamily c μ N i u wu :=
    ⟨hu0, fun Y => (pow_dvd_pow _ (Nat.le_succ i)).trans (hud Y)⟩
  rw [← jformFam_eq_jform c μ hu' hv', jformFam]
  exact (Polynomial.X_pow_dvd_iff.1 (dvd_dot_right hud)) i (Nat.lt_succ_self i)

/-- `B^{(i)}` as a bilinear form on `J^i_N`. -/
noncomputable def jformL (c μ : ℂ) (N i : ℕ) :
    jantzenLayer c μ N i →ₗ[ℂ] jantzenLayer c μ N i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun u v => jform c μ N i u.1 v.1)
    (fun u u' v => jform_add_left' u.2 u'.2 v.2)
    (fun a u v => jform_smul_left' a u.2 v.2)
    (fun u v v' => by
      show jform c μ N i u.1 (v.1 + v'.1) = _
      rw [jform_symm c μ u.2 (Submodule.add_mem _ v.2 v'.2), jform_add_left' v.2 v'.2 u.2,
        jform_symm c μ v.2 u.2, jform_symm c μ v'.2 u.2])
    (fun a u v => by
      show jform c μ N i u.1 (a • v.1) = _
      rw [jform_symm c μ u.2 (Submodule.smul_mem _ a v.2), jform_smul_left' a v.2 u.2,
        jform_symm c μ v.2 u.2]
      rfl)

end JForm

section VForm

variable (HV : VertexPartI c μ d) {u u' v : Nat.Partition N → ℂ}

include HV

theorem vform_key {wu wv : Nat.Partition N → ℂ[X]} (hu : IsJFamily c μ N i u wu)
    (hv : IsJFamily c μ N i v wv) :
    vform c μ d N i u v = (wu ⬝ᵥ (torusShift c μ d N).mulVec wv).coeff i :=
  ((vform_fam HV hu hv).2).symm

theorem vform_add_left' (hu : u ∈ jantzenLayer c μ N i) (hu' : u' ∈ jantzenLayer c μ N i)
    (hv : v ∈ jantzenLayer c μ N i) :
    vform c μ d N i (u + u') v = vform c μ d N i u v + vform c μ d N i u' v := by
  obtain ⟨wu, hwu⟩ := hu
  obtain ⟨wu', hwu'⟩ := hu'
  obtain ⟨wv, hwv⟩ := hv
  have h1 : IsJFamily c μ N i u wu := hwu
  have h2 : IsJFamily c μ N i u' wu' := hwu'
  have h3 : IsJFamily c μ N i v wv := hwv
  rw [vform_key HV (h1.add' h2) h3, vform_key HV h1 h3, vform_key HV h2 h3, add_dotProduct,
    coeff_add]

theorem vform_smul_left' (a : ℂ) (hu : u ∈ jantzenLayer c μ N i)
    (hv : v ∈ jantzenLayer c μ N i) : vform c μ d N i (a • u) v = a * vform c μ d N i u v := by
  obtain ⟨wu, hwu⟩ := hu
  obtain ⟨wv, hwv⟩ := hv
  have h1 : IsJFamily c μ N i u wu := hwu
  have h3 : IsJFamily c μ N i v wv := hwv
  rw [vform_key HV (h1.smul' a) h3, vform_key HV h1 h3, smul_dotProduct, smul_eq_mul,
    coeff_C_mul]

theorem vform_symm' (hu : u ∈ jantzenLayer c μ N i) (hv : v ∈ jantzenLayer c μ N i) :
    vform c μ d N i u v = vform c μ d N i v u := by
  obtain ⟨wu, hwu⟩ := hu
  obtain ⟨wv, hwv⟩ := hv
  have h1 : IsJFamily c μ N i u wu := hwu
  have h3 : IsJFamily c μ N i v wv := hwv
  have hT := isPrimaryPairing_pairing (c := C c) (h := C μ + (X : ℂ[X])) (C d)
  have k1 : pairing (C c) (C μ + X) (C d) (pbwCoord N wu) (pbwCoord N wv) =
      wu ⬝ᵥ (torusShift c μ d N).mulVec wv := primary_pbwCoord hT N wu wv
  have k2 : pairing (C c) (C μ + X) (C d) (pbwCoord N wv) (pbwCoord N wu) =
      wv ⬝ᵥ (torusShift c μ d N).mulVec wu := primary_pbwCoord hT N wv wu
  rw [vform_key HV h1 h3, vform_key HV h3 h1, ← k1, ← k2, primary_symm' hT]

/-- `J^{i+1}_N ⊂ rad ρ^{(i)}` (part (i)). -/
theorem vform_rad_zero (hu : u ∈ jantzenLayer c μ N (i + 1)) (hv : v ∈ jantzenLayer c μ N i) :
    vform c μ d N i u v = 0 := by
  obtain ⟨wu, hu0, hud⟩ := hu
  obtain ⟨wv, hwv⟩ := hv
  have h3 : IsJFamily c μ N i v wv := hwv
  have h1 : IsJFamily c μ N i u wu :=
    ⟨hu0, fun Y => (pow_dvd_pow _ (Nat.le_succ i)).trans (hud Y)⟩
  have hT := isPrimaryPairing_pairing (c := C c) (h := C μ + (X : ℂ[X])) (C d)
  have k1 : pairing (C c) (C μ + X) (C d) (pbwCoord N wu) (pbwCoord N wv) =
      wu ⬝ᵥ (torusShift c μ d N).mulVec wv := primary_pbwCoord hT N wu wv
  rw [vform_key HV h1 h3, ← k1]
  exact (HV i N N u v wu wv h1 h3).2.2.2 (Or.inl ⟨wu, hu0, hud⟩)

/-- `ρ^{(i)}` as a bilinear form on `J^i_N`. -/
noncomputable def vformL : jantzenLayer c μ N i →ₗ[ℂ] jantzenLayer c μ N i →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun u v => vform c μ d N i u.1 v.1)
    (fun u u' v => vform_add_left' HV u.2 u'.2 v.2)
    (fun a u v => vform_smul_left' HV a u.2 v.2)
    (fun u v v' => by
      show vform c μ d N i u.1 (v.1 + v'.1) = _
      rw [vform_symm' HV u.2 (Submodule.add_mem _ v.2 v'.2), vform_add_left' HV v.2 v'.2 u.2,
        vform_symm' HV v.2 u.2, vform_symm' HV v'.2 u.2])
    (fun a u v => by
      show vform c μ d N i u.1 (a • v.1) = _
      rw [vform_symm' HV u.2 (Submodule.smul_mem _ a v.2), vform_smul_left' HV a v.2 u.2,
        vform_symm' HV v.2 u.2]
      rfl)

end VForm

/-- A family of `J^i_N` whose classes form a basis of `J^i_N/J^{i+1}_N`, as a family of the
space `J^i_N`. -/
theorem lift_family {κ : Type} (E : κ → Nat.Partition N → ℂ)
    (hmem : ∀ a, E a ∈ jantzenLayer c μ N i) (hLI : LinearIndependent ℂ E)
    (hdisj : Disjoint (Submodule.span ℂ (Set.range E)) (jantzenLayer c μ N (i + 1)))
    (hsup : Submodule.span ℂ (Set.range E) ⊔ jantzenLayer c μ N (i + 1) =
      jantzenLayer c μ N i) :
    LinearIndependent ℂ (fun a => (⟨E a, hmem a⟩ : jantzenLayer c μ N i)) ∧
    Disjoint (Submodule.span ℂ (Set.range fun a => (⟨E a, hmem a⟩ : jantzenLayer c μ N i)))
      (Submodule.comap (jantzenLayer c μ N i).subtype (jantzenLayer c μ N (i + 1))) ∧
    ∀ x : jantzenLayer c μ N i,
      x ∈ Submodule.span ℂ (Set.range fun a => (⟨E a, hmem a⟩ : jantzenLayer c μ N i)) ⊔
        Submodule.comap (jantzenLayer c μ N i).subtype (jantzenLayer c μ N (i + 1)) := by
  have hle : jantzenLayer c μ N (i + 1) ≤ jantzenLayer c μ N i := by
    rw [← hsup]; exact le_sup_right
  have hmap : (Submodule.span ℂ (Set.range fun a =>
      (⟨E a, hmem a⟩ : jantzenLayer c μ N i))).map (jantzenLayer c μ N i).subtype =
      Submodule.span ℂ (Set.range E) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  refine ⟨LinearIndependent.of_comp (jantzenLayer c μ N i).subtype hLI, ?_, fun x => ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hxW
    have h1 : (x : Nat.Partition N → ℂ) ∈ Submodule.span ℂ (Set.range E) := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    exact Subtype.ext (Submodule.disjoint_def.1 hdisj _ h1 hxW)
  · have hx : (x : Nat.Partition N → ℂ) ∈
        Submodule.span ℂ (Set.range E) ⊔ jantzenLayer c μ N (i + 1) := by
      rw [hsup]; exact x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
    rw [← hmap] at hy
    obtain ⟨y₁, hy₁, rfl⟩ := hy
    exact Submodule.mem_sup.2 ⟨y₁, hy₁, ⟨z, hle hz⟩, hz, Subtype.ext hyz⟩

/-- The trace of a layer does not depend on the basis of `J^i_N/J^{i+1}_N`. -/
theorem layer_trace_unique (HV : VertexPartI c μ d) {t t' : ℂ}
    (ht : IsLayerTrace c μ d N i t) (ht' : IsLayerTrace c μ d N i t') : t = t' := by
  obtain ⟨κ, _, _, E, hmem, hLI, hdisj, hsup, hdet, rfl⟩ := ht
  obtain ⟨κ', _, _, E', hmem', hLI', hdisj', hsup', -, rfl⟩ := ht'
  obtain ⟨l1, l2, l3⟩ := lift_family E hmem hLI hdisj hsup
  obtain ⟨l1', l2', l3'⟩ := lift_family E' hmem' hLI' hdisj' hsup'
  have h := trace_change (jformL c μ N i) (vformL HV)
    (Submodule.comap (jantzenLayer c μ N i).subtype (jantzenLayer c μ N (i + 1)))
    (fun k hk u => ⟨jform_rad_zero hk u.2, by
      show jform c μ N i u.1 k.1 = 0
      rw [jform_symm c μ u.2 k.2]; exact jform_rad_zero hk u.2⟩)
    (fun k hk u => ⟨vform_rad_zero HV hk u.2, by
      show vform c μ d N i u.1 k.1 = 0
      rw [vform_symm' HV u.2 k.2]; exact vform_rad_zero HV hk u.2⟩)
    l1 l1' l2 l2' l3 l3' hdet
  exact h

/-- The trace of the layer `i ≥ 1` in the basis adapted to
`J^i/J^{i+1} ≅ L(c⋆,μ⁺_{k₀+i}) ⊕ L(c⋆,μ⁻_{k₀+i})`, paper.tex l.2487–2495: the summands are
`B̄^{(i)}`-orthogonal, `B̄^{(i)} = γ^±_i B̄_L` and `ρ̄^{(i)} = σ^±_i ρ̄_L` on them, so
`∑_± σ^±_i/γ^±_i · T^irr_{N-(μ^±_{k₀+i}-μ)}(c⋆,μ^±_{k₀+i},d)` is a trace of the layer.

Demand sheet: as in `Stmt_sub_vertex_layer_pos`; the conclusion is that the right-hand side of
(11.3) for the layer `i` is a layer trace (`IsLayerTrace`, in the images under the embeddings
`j_±` of families giving `Tp`, `Tm`). -/
def Stmt_sub_vertex_layer_basis : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let μ : ℂ := muOrb p p' r s ε k₀
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      let lev : Bool → ℕ → ℕ := fun ε' i => ellOrb p p' r s ε' (k₀ + i) - ellOrb p p' r s ε k₀
      ∀ wp wm : ℕ → Verma ℂ c μ, OrbitLayerSetting p p' r s b ε k₀ wp wm →
        ∀ (xp : (i : ℕ) → Nat.Partition (lev true i) → ℂ)
            (xm : (i : ℕ) → Nat.Partition (lev false i) → ℂ),
          (∀ i, 1 ≤ i → Verma.pbwCoord (lev true i) (xp i) = wp i ∧
            Verma.pbwCoord (lev false i) (xm i) = wm i) →
          ∀ N i : ℕ, 1 ≤ i → ∀ Tp Tm : ℂ,
            (lev true i ≤ N →
              IsIrrTrace c (muOrb p p' r s true (k₀ + i)) d (N - lev true i) Tp) →
            (lev false i ≤ N →
              IsIrrTrace c (muOrb p p' r s false (k₀ + i)) d (N - lev false i) Tm) →
              IsLayerTrace c μ d N i
                ((if lev true i ≤ N then
                    vform c μ d (lev true i) i (xp i) (xp i) /
                      jform c μ (lev true i) i (xp i) (xp i) * Tp else 0) +
                  (if lev false i ≤ N then
                    vform c μ d (lev false i) i (xm i) (xm i) /
                      jform c μ (lev false i) i (xm i) (xm i) * Tm else 0))

/-- The identification of the layers `i ≥ 1` from the trace in the adapted basis. -/
theorem sub_vertex_layer_pos_of_basis (hJ : Cited_JantzenLayersOrbit)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) (h : Stmt_sub_vertex_layer_basis) :
    Stmt_sub_vertex_layer_pos := by
  intro p p' r s b hset ε k₀ k m hk hm c μ d lev wp wm hw xp xm hx N i hi t Tp Tm ht hTp hTm
  have HV : VertexPartI c μ d := fun i N₁ N₂ a a₂ wa wb ha hb =>
    vertex_part_i hJ hH hU hF hI p p' r s b hset ε k₀ k m hk hm _
      (Verma.isPrimaryPairing_pairing _) i N₁ N₂ a a₂ wa wb ha hb
  exact layer_trace_unique HV ht
    (h p p' r s b hset ε k₀ k m hk hm wp wm hw xp xm hx N i hi Tp Tm hTp hTm)

/-- Proposition 11.2 from the trace of the layers `i ≥ 1` in the adapted basis. -/
theorem prop_jantzen_vertex_of_basis (hJ : Cited_JantzenLayersOrbit)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) (h : Stmt_sub_vertex_layer_basis) :
    Stmt_prop_jantzen_vertex :=
  prop_jantzen_vertex_of_subs hJ hH hU hF hI (sub_vertex_gamma hJ hU hI)
    (sub_vertex_trace_of_layers (sub_vertex_layer_sum hJ hH hU hF hI)
      (sub_vertex_layer_ident_of_layers (sub_vertex_layer_zero hJ hH hU hF hI)
        (sub_vertex_layer_pos_of_basis hJ hH hU hF hI h)))

end Virasoro
