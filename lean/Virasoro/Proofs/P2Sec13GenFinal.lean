import Virasoro.Proofs.P2Sec13GenLayerOne
import Virasoro.Proofs.Sec5TopCoeff
import Virasoro.Proofs.ResidueCore1

/-!
# Lemma 13.1, Step 1: equation (13.2) (paper.tex l.2883–2913)

The layer `1` of the generic module has `γ = ∂_Δ B_Δ(χ,χ)` and `σ = ∂_Δ ρ_{Δ,d}(χ,χ)`, whose
ratio is the box ratio of Theorem 9.2; with `layer_trace_one` this gives
`Stmt_sub_generic_layer_one`, and then Step 1.
-/

namespace Virasoro.P2

open Virasoro Polynomial Verma

variable {c μ d : ℂ}

/-- The constant family of a vector of `ker G_ℓ(c,μ)` is a family of order `1`. -/
theorem isJFamily_const {ℓ : ℕ} {x : Nat.Partition ℓ → ℂ} (hx : (gram c μ ℓ).mulVec x = 0) :
    IsJFamily c μ ℓ 1 x fun Y => C (x Y) := by
  refine ⟨fun Y => eval_C, fun Y => ?_⟩
  rw [pow_one, X_dvd_iff, coeff_zero_eq_eval_zero, eval_mulVec_gramShift]
  have e : (fun Z => (C (x Z) : ℂ[X]).eval 0) = x := funext fun Z => eval_C
  rw [e, hx]
  rfl

/-- `B^{(1)}(χ,χ) = ∂_Δ B_Δ(χ,χ)` at `Δ = μ`. -/
theorem jform_one_eq_crossScalar {ℓ : ℕ} {x : Nat.Partition ℓ → ℂ}
    (hx : x ∈ jantzenLayer c μ ℓ 1) : jform c μ ℓ 1 x x = crossScalar c μ x := by
  rw [jform_one c μ hx hx, ← dAt_gramForm]
  rfl

/-- `ρ^{(1)}(χ,χ) = ∂_Δ ρ_{Δ,d}(χ,χ)` at `Δ = μ`. -/
theorem vform_one_eq_torusCrossScalar (HV : VertexPartI c μ d) {ℓ : ℕ}
    {x : Nat.Partition ℓ → ℂ} (hx : (gram c μ ℓ).mulVec x = 0) :
    vform c μ d ℓ 1 x x = torusCrossScalar c μ d x := by
  have hfam := isJFamily_const hx
  rw [← (vform_fam HV hfam hfam).2]
  set Q : ℂ[X] := torusForm (C c) (X : ℂ[X]) (C d) ℓ (fun Y => C (x Y)) (fun Y => C (x Y))
    with hQ
  have hmap : torusShift c μ d ℓ = (torus (C c) (X : ℂ[X]) (C d) ℓ).map
      (compRingHom (C μ + X)) := by
    have := torus_map (compRingHom (C μ + (X : ℂ[X]))) (C c) (X : ℂ[X]) (C d) ℓ
    simp only [coe_compRingHom, C_comp, X_comp] at this
    rw [torusShift, this]
    rfl
  have hcomp : (fun Y => C (x Y)) ⬝ᵥ (torusShift c μ d ℓ).mulVec (fun Y => C (x Y)) =
      Q.comp (C μ + X) := by
    rw [hQ, torusForm, hmap]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, coe_compRingHom, sum_comp, mul_comp,
      C_comp]
  rw [hcomp, torusCrossScalar]
  have h1 : (Q.comp (C μ + X)).coeff 1 = (derivative (Q.comp (C μ + X))).coeff 0 := by
    rw [coeff_derivative]
    simp
  rw [h1, derivative_comp, coeff_zero_eq_eval_zero]
  simp
  rfl

/-- `Stmt_sub_generic_layer_one` from the layer structure and part (i). -/
theorem sub_generic_layer_one_of_layers (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective)
    (hL : Stmt_sub_generic_layers) (hV : Stmt_sub_generic_vertex) :
    Stmt_sub_generic_layer_one := by
  intro b hb hirr R S k m hR hS hk hm N t ht
  have HV := hV b hb hirr R S k m hR hS hk hm
  obtain ⟨p, ⟨hp1, hsing⟩, -⟩ := hH R S hR hS
  obtain ⟨-, h1, hs1, -, -⟩ := lem_regular_everywhere_of_cited hH R S hR hS p hp1 hsing b hb
  obtain ⟨hJ1, hJ2⟩ := hL b hb hirr R S hR hS _ hs1
  set x : Nat.Partition (R * S) → ℂ := fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (p Y) with hxdef
  have hℓ : 1 ≤ R * S := Nat.mul_pos hR hS
  obtain ⟨hβ, hbox⟩ := sub_first_layer_box_of_cited hE hH hU hF b hb hirr R S k m hR hS hk hm
    x hs1
  have hχJ : pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x ∈
      jantzen (kacC b) (kacH R S b) 1 := by
    rw [hJ1]
    exact mem_negSpan_self _
  have hxl : x ∈ jantzenLayer (kacC b) (kacH R S b) (R * S) 1 := by
    have := comp_mem_layer hχJ ⟨x, rfl⟩
    rwa [comp_pbwCoord_same] at this
  have hxk : (gram (kacC b) (kacH R S b) (R * S)).mulVec x = 0 := by
    rw [jantzenLayer_one] at hxl
    exact hxl
  have hγe := jform_one_eq_crossScalar hxl
  have hσe := vform_one_eq_torusCrossScalar HV hxk
  by_cases hN : R * S ≤ N
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [if_pos hN, Nat.add_sub_cancel_left]
    have e : kacH (R : ℤ) (-(S : ℤ)) b = kacH R S b + ((R * S : ℕ) : ℂ) := by
      simp only [kacH]
      push_cast
      field_simp
      ring
    have hg : (gram (kacC b) (kacH R S b + ((R * S : ℕ) : ℂ)) M).det ≠ 0 := by
      have h := (generic_out_regular hK hb hirr hR hS (0 : ℂ) M).1
      rwa [e] at h
    have hγ : jform (kacC b) (kacH R S b) (R * S) (0 + 1) x x ≠ 0 := by
      show jform (kacC b) (kacH R S b) (R * S) 1 x x ≠ 0
      rw [hγe]
      exact hβ
    have ht' := layer_trace_one (i := 0) (d := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) hI HV
      hs1 hJ1 (hJ2 (R * S + M) 2 le_rfl) x rfl hγ hg
    have htt := layer_trace_unique HV ht ht'
    have hFv : FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) M
        (kacH (R : ℤ) (-(S : ℤ)) b) =
        Fval (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
          (kacH R S b + ((R * S : ℕ) : ℂ)) M := by
      rw [e]
      exact evalAt_Frat hg
    rw [htt, hFv]
    show vform (kacC b) (kacH R S b) _ (R * S) 1 x x / jform (kacC b) (kacH R S b) (R * S) 1 x x *
      _ * _ = _
    rw [hγe, hσe]
    field_simp
    linear_combination Fval (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
      (kacH R S b + ((R * S : ℕ) : ℂ)) M * hbox
  · rw [if_neg hN, mul_zero]
    have hJ0 : jantzenLayer (kacC b) (kacH R S b) N (0 + 1) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have huJ : pbwCoord (c := kacC b) (h := kacH R S b) N u ∈
          jantzen (kacC b) (kacH R S b) 1 := pbwCoord_mem_jantzen hu
      rw [hJ1] at huJ
      have h0 := comp_negSpan_eq_zero (mem_level_of_L_zero hs1.2.1) (not_le.1 hN) huJ
      rw [comp_pbwCoord_same] at h0
      rw [h0]
      exact Submodule.zero_mem _
    have ht' := layer_trace_one_below (d := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) hJ0
    rw [layer_trace_unique HV ht ht', zero_mul]

/-- Step 1 of Lemma 13.1: equation (13.2) at generic `b` (l.2883–2913). -/
theorem sub_generic_tau_split_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_generic_tau_split := by
  have hL := sub_generic_layers_of_cited hK hE hH hU hF
  have hV := sub_generic_vertex_of_layers hH hU hF hL
  exact sub_generic_tau_split_of_subs hK hH hU hF hL hV
    (sub_generic_layer_one_of_layers hK hE hH hU hF hI hL hV)

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) : Stmt_sub_generic_tau_split :=
  sub_generic_tau_split_of_cited hK hE hH hU hF hI

end Virasoro.P2
