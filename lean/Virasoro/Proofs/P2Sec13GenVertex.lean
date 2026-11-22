import Virasoro.Proofs.P2Sec13GenLayers
import Virasoro.Proofs.P2Sec11VertexStep

/-!
# Lemma 13.1, Step 1: part (i) of Proposition 11.2 for the generic module (l.2893–2901)

The induction of Proposition 11.2(i) (l.2412–2459) at `(c(b),h_{R,S}(b),h_{2k+1,2m+1}(b))` for
generic `b`.  The case `i = 0` is `J¹ ⊂ rad ρ` (Proposition 10.2(ii) and the Ward induction,
l.2893–2897).  In the step, `J^{i+2} ⊂ rad ρ^{(i+1)}` holds because `J^{i+2} = 0`.
-/

namespace Virasoro.P2

open Virasoro Polynomial Verma

theorem jantzen_eq_bot_of_layers {c μ : ℂ} {i : ℕ} (h : ∀ N, jantzenLayer c μ N i = ⊥) :
    jantzen c μ i = ⊥ := by
  unfold jantzen
  simp [h]

/-- The induction step of Proposition 11.2(i) (l.2423–2438, 2459) at any `(c,μ,d)`, given
`J^{i+2} ⊂ rad ρ^{(i+1)}`. -/
theorem vertex_step_of_rad {c μ d : ℂ}
    {T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X]}
    (hT : IsPrimaryPairing (C d) T) {i : ℕ}
    (H : ∀ (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
      (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
      IsJFamily c μ N₁ i a wa → IsJFamily c μ N₂ i a₂ wb →
        VertexClausesAt c μ d i T N₁ N₂ a a₂ wa wb)
    (hrad : ∀ x ∈ jantzen c μ (i + 1 + 1), ∀ y ∈ jantzen c μ (i + 1), rhoJ T (i + 1) x y = 0)
    (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
    (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X])
    (ha : IsJFamily c μ N₁ (i + 1) a wa) (hb : IsJFamily c μ N₂ (i + 1) a₂ wb) :
    VertexClausesAt c μ d (i + 1) T N₁ N₂ a a₂ wa wb := by
  have G := vertexGen_of_clauses H
  have hUl := ha.inLat
  have hWl := hb.inLat
  refine ⟨vg_dvd G hUl hWl, fun wa' wb' ha' hb' => ?_,
    fun n N₁' N₂' a' b' wa' wb' ha' hb' e1 e2 => ?_, fun hex => ?_⟩
  · rw [vg_congr_left G ha'.inLat hUl hb'.inLat (ha'.ev0.trans ha.ev0.symm),
      vg_congr_right hT G hUl hb'.inLat hWl (hb'.ev0.trans hb.ev0.symm)]
  · have e := congrArg (fun q : ℂ[X] => q.coeff (i + 1))
      (hT.2 n (pbwCoord N₁ wa) (pbwCoord N₂ wb))
    beta_reduce at e
    have l1 : (T (pbwCoord N₁' wa') (pbwCoord N₂ wb)).coeff (i + 1) =
        (T (Verma.L (-n) (pbwCoord N₁ wa)) (pbwCoord N₂ wb)).coeff (i + 1) :=
      vg_congr_left G ha'.inLat (hUl.L (-n)) hWl (by rw [ha'.ev0, latEv0_L, ha.ev0, e1])
    have l2 : (T (pbwCoord N₁ wa) (pbwCoord N₂' wb')).coeff (i + 1) =
        (T (pbwCoord N₁ wa) (Verma.L n (pbwCoord N₂ wb))).coeff (i + 1) :=
      vg_congr_right hT G hUl hb'.inLat (hWl.L n) (by rw [hb'.ev0, latEv0_L, hb.ev0, e2])
    have hc : ∀ q : ℂ[X], (C μ + X + (N₁ : ℂ[X])) * q - (C μ + X + (N₂ : ℂ[X])) * q +
          (n : ℂ[X]) * C d * q = C (((N₁ : ℂ) - (N₂ : ℂ)) + (n : ℂ) * d) * q := by
      intro q
      simp only [map_sub, map_add, map_mul, map_natCast, map_intCast]
      ring
    rw [L_zero_of_mem_level ⟨wa, rfl⟩, L_zero_of_mem_level ⟨wb, rfl⟩, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, hc, coeff_sub, coeff_C_mul] at e
    rw [l1, l2]
    exact e
  · rw [rhoJ_eq hT G hUl hWl, ha.ev0, hb.ev0]
    rcases hex with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact hrad _ (pbwCoord_mem_jantzen ⟨w, hw.1, hw.2⟩) _
        (pbwCoord_mem_jantzen ⟨wb, hb.1, hb.2⟩)
    · rw [rhoJ_symm hT]
      exact hrad _ (pbwCoord_mem_jantzen ⟨w, hw.1, hw.2⟩) _
        (pbwCoord_mem_jantzen ⟨wa, ha.1, ha.2⟩)

/-- Part (i) of Proposition 11.2 for the generic module, from its layer structure. -/
theorem sub_generic_vertex_of_layers (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    (hF : Cited_FusionPolynomial) (hL : Stmt_sub_generic_layers) : Stmt_sub_generic_vertex := by
  intro b hb hirr R S k m hR hS hk hm
  obtain ⟨p, ⟨hp1, hsing⟩, -⟩ := hH R S hR hS
  obtain ⟨-, h1, hs1, -, -⟩ := lem_regular_everywhere_of_cited hH R S hR hS p hp1 hsing b hb
  obtain ⟨-, hJ2⟩ := hL b hb hirr R S hR hS _ hs1
  have hdesc := generic_descends hH hU hF hL hb hirr hR hS hk hm
  have hT := isPrimaryPairing_pairing (c := C (kacC b)) (h := C (kacH R S b) + (X : ℂ[X]))
    (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b))
  intro i
  induction i with
  | zero =>
    intro N₁ N₂ a a₂ wa wb ha hb'
    refine vertex_base (fun T₀ hT₀ u hu v => ?_) _ hT N₁ N₂ a a₂ wa wb ha hb'
    have hrad := jantzen_one_eq_radical (kacC b) (kacH R S b)
    have hu' : u ∈ (jantzen (kacC b) (kacH R S b) 1 : Set (Verma ℂ (kacC b) (kacH R S b))) := hu
    rw [hrad] at hu'
    exact hdesc T₀ hT₀ _ Verma.isShapovalov_shap u hu' v
  | succ i ih =>
    intro N₁ N₂ a a₂ wa wb ha hb'
    refine vertex_step_of_rad hT ih (fun x hx y hy => ?_) N₁ N₂ a a₂ wa wb ha hb'
    have G := vertexGen_of_clauses ih
    have hRw : IsJWard (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
        (jantzen (kacC b) (kacH R S b) (i + 1))
        (rhoJ (pairing (C (kacC b)) (C (kacH R S b) + X)
          (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b))) (i + 1)) :=
      ⟨fun hx hx' hy => rhoJ_add_left hT G hx hx' hy,
        fun a _ _ hx hy => rhoJ_smul_left hT G a hx hy, rhoJ_symm hT _,
        fun n _ _ hx hy => rhoJ_ward hT G n hx hy, fun n _ hx => L_mem_jantzen _ _ (i + 1) n hx⟩
    rw [jantzen_eq_bot_of_layers (fun N => hJ2 N (i + 1 + 1) (by omega)),
      Submodule.mem_bot] at hx
    rw [hx]
    exact hRw.zero_left hy

example (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hL : Stmt_sub_generic_layers) : Stmt_sub_generic_vertex :=
  sub_generic_vertex_of_layers hH hU hF hL

/-- `Stmt_sub_generic_vertex` (l.2893–2901). -/
theorem sub_generic_vertex_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) : Stmt_sub_generic_vertex :=
  sub_generic_vertex_of_layers hH hU hF (sub_generic_layers_of_cited hK hE hH hU hF)

end Virasoro.P2
