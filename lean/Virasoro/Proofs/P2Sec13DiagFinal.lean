import Virasoro.Proofs.P2Sec13DiagTools

/-!
# Lemma 13.1, Step 4 (paper.tex l.2990–3028)

The trace `trRat` on `𝒱_N` is regular at `b⋆`, with value
`T^irr_N(c⋆,μ,d⋆) + Ω_{u,v}(μ→ν₂) T^irr_{N-R₂S₂}(c⋆,ν₂,d⋆)`.

The proof is the paper's.  Diagonalize the Gram matrix of `E` over `ℂ⟦X⟧` (`b = b⋆ + X`):
`B(v_a,v_b) = δ_{ab} X^{e_a} u_a`, `e_a ∈ {0,1}` (Step 3).  The trace is
`∑_a ρ_X(v_a,v_a)/(X^{e_a}u_a)`; for `e_a = 1`, `v_a(0) ∈ J¹ ⊂ rad ρ₀`.  The terms with `e_a = 0`
give `T^irr_N(μ)` (the `v_a(0)` are an orthogonal complement of `J¹`).  The terms with `e_a = 1`
are `[X¹]ρ/[X¹]B` on `J¹_τ = L(c⋆,ν₂)`, where both forms are multiples of the canonical forms
of `M(c⋆,ν₂)`, with ratio `Ω_{u,v}(μ→ν₂)` (Step 3, equation (13.3)).
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial

open scoped PowerSeries Matrix

section Local

variable {n N : ℕ} {E : Fin n → (Nat.Partition N → ℂ)}

/-- The expansion of `trRat` at `b⋆` through an orthogonal basis of the Gram matrix of `E`. -/
theorem trRat_local {b : ℂ} (hb : b ≠ 0) {R S : ℕ} {u v : ℤ} (hden : (GLam E R S).det ≠ 0)
    {w : Fin n → Fin n → ℂ⟦X⟧} {e : Fin n → ℕ} {uu : Fin n → ℂ⟦X⟧}
    (h : OrthBasis ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) w e uu)
    {r : Fin n → ℂ⟦X⟧}
    (hr : ∀ a, w a ⬝ᵥ ((Fm E)ᵀ * torus (cLoc b) (hLoc R S b) (hLoc u v b) N * Fm E).mulVec (w a) =
      (PowerSeries.X : ℂ⟦X⟧) ^ e a * r a) :
    RegAt b (trRat E R S u v) ∧
      evalAt b (trRat E R S u v) =
        ∑ a, (PowerSeries.constantCoeff (uu a))⁻¹ * PowerSeries.constantCoeff (r a) := by
  set GX := (Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E with hGX
  set PX := (Fm E)ᵀ * torus (cLoc b) (hLoc R S b) (hLoc u v b) N * Fm E with hPX
  have hent : (Matrix.of fun i j => gramForm (cLoc b) (hLoc R S b) N
      (fun Y => PowerSeries.C (E i Y)) (fun Y => PowerSeries.C (E j Y))) = GX := by
    ext i j
    rw [Matrix.of_apply, hGX, gramForm_Fm]
    rfl
  have hG := map_GLam (E := E) (e := fun i Y => PowerSeries.C (E i Y)) (locLam b hb)
    (locLam_cLam hb) (locLam_hLam hb R S) (locLam_ELam hb)
  rw [hent] at hG
  have hN := map_trNum (E := E) (e := fun i Y => PowerSeries.C (E i Y)) (u := u) (v := v)
    (locLam b hb) (locLam_cLam hb) (locLam_hLam hb R S) (locLam_hLam hb u v) (locLam_ELam hb)
  rw [hent] at hN
  have hN' : locLam b hb (trNum E R S u v) = ∑ i, ∑ j, GX.adjugate i j * PX j i := by
    rw [hN]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hPX, gramForm_Fm]
    rfl
  have hD : locLam b hb (GLam E R S).det = GX.det := by rw [RingHom.map_det, hG]
  have hD0 : GX.det ≠ 0 := by
    rw [← hD]
    intro h0
    exact hden (locLam_injective hb (h0.trans (map_zero _).symm))
  have htr := orth_trace h PX hr
  have hexp : expandHom b (trRat E R S u v) = HahnSeries.ofPowerSeries ℤ ℂ
      (∑ a, (uu a)⁻¹ * r a) := by
    have hne : HahnSeries.ofPowerSeries ℤ ℂ GX.det ≠ 0 := by
      intro h0
      exact hD0 (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [h0, map_zero]))
    rw [expand_trRat hb, hN', hD, htr, map_mul, mul_div_cancel_left₀ _ hne]
  obtain ⟨hreg, hval⟩ := regAt_of_expand hexp
  refine ⟨hreg, ?_⟩
  rw [hval, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, PowerSeries.constantCoeff_inv]

end Local

section Forms

variable {b : ℂ} {R S : ℕ}

theorem RB_add_left {x x' y : Verma ℂ (kacC b) (kacH R S b)}
    (hx : x ∈ jantzen (kacC b) (kacH R S b) 1) (hx' : x' ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : y ∈ jantzen (kacC b) (kacH R S b) 1) :
    RB b R S (x + x') y = RB b R S x y + RB b R S x' y := by
  rw [← RB_lift (Submodule.add_mem _ hx hx') hy (U := lft b R S x + lft b R S x')
    (by rw [map_add, ev0_lft, ev0_lft]) (ev0_lft y), map_add, LinearMap.add_apply, map_add]
  rfl

theorem RB_add_right {x y y' : Verma ℂ (kacC b) (kacH R S b)}
    (hx : x ∈ jantzen (kacC b) (kacH R S b) 1) (hy : y ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy' : y' ∈ jantzen (kacC b) (kacH R S b) 1) :
    RB b R S x (y + y') = RB b R S x y + RB b R S x y' := by
  rw [← RB_lift hx (Submodule.add_mem _ hy hy') (V := lft b R S y + lft b R S y') (ev0_lft x)
    (by rw [map_add, ev0_lft, ev0_lft]), map_add, map_add]
  rfl

theorem Rρ_add_left {u v : ℤ}
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH u v b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH u v b) z x = 0)
    {x x' y : Verma ℂ (kacC b) (kacH R S b)}
    (hx : x ∈ jantzen (kacC b) (kacH R S b) 1) (hx' : x' ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : y ∈ jantzen (kacC b) (kacH R S b) 1) :
    Rρ b R S u v (x + x') y = Rρ b R S u v x y + Rρ b R S u v x' y := by
  rw [← Rρ_lift hrad (Submodule.add_mem _ hx hx') hy (U := lft b R S x + lft b R S x')
    (by rw [map_add, ev0_lft, ev0_lft]) (ev0_lft y), map_add, LinearMap.add_apply, map_add]
  rfl

theorem Rρ_add_right {u v : ℤ}
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH u v b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH u v b) z x = 0)
    {x y y' : Verma ℂ (kacC b) (kacH R S b)}
    (hx : x ∈ jantzen (kacC b) (kacH R S b) 1) (hy : y ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy' : y' ∈ jantzen (kacC b) (kacH R S b) 1) :
    Rρ b R S u v x (y + y') = Rρ b R S u v x y + Rρ b R S u v x y' := by
  rw [← Rρ_lift hrad hx (Submodule.add_mem _ hy hy') (V := lft b R S y + lft b R S y') (ev0_lft x)
    (by rw [map_add, ev0_lft, ev0_lft]), map_add, map_add]
  rfl

/-- `R_B` and `R_ρ` on coordinate lifts at one level. -/
theorem RB_coord {N : ℕ} {xv yv : Nat.Partition N → ℂ}
    (hx : pbwCoord N xv ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : pbwCoord N yv ∈ jantzen (kacC b) (kacH R S b) 1) {U V : Nat.Partition N → ℂ⟦X⟧}
    (hU : ∀ Y, PowerSeries.constantCoeff (U Y) = xv Y)
    (hV : ∀ Y, PowerSeries.constantCoeff (V Y) = yv Y) :
    PowerSeries.coeff 1 (U ⬝ᵥ (gram (cLoc b) (hLoc R S b) N).mulVec V) =
      RB b R S (pbwCoord N xv) (pbwCoord N yv) := by
  rw [← RB_lift hx hy (U := pbwCoord N U) (V := pbwCoord N V)
    (by rw [ev0_pbwCoord]; congr 1; funext Y; exact hU Y)
    (by rw [ev0_pbwCoord]; congr 1; funext Y; exact hV Y), shap_pbwCoord]
  rfl

theorem Rρ_coord {u v : ℤ}
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH u v b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH u v b) z x = 0)
    {N : ℕ} {xv yv : Nat.Partition N → ℂ}
    (hx : pbwCoord N xv ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : pbwCoord N yv ∈ jantzen (kacC b) (kacH R S b) 1) {U V : Nat.Partition N → ℂ⟦X⟧}
    (hU : ∀ Y, PowerSeries.constantCoeff (U Y) = xv Y)
    (hV : ∀ Y, PowerSeries.constantCoeff (V Y) = yv Y) :
    PowerSeries.coeff 1 (U ⬝ᵥ (torus (cLoc b) (hLoc R S b) (hLoc u v b) N).mulVec V) =
      Rρ b R S u v (pbwCoord N xv) (pbwCoord N yv) := by
  rw [← Rρ_lift hrad hx hy (U := pbwCoord N U) (V := pbwCoord N V)
    (by rw [ev0_pbwCoord]; congr 1; funext Y; exact hU Y)
    (by rw [ev0_pbwCoord]; congr 1; funext Y; exact hV Y),
    primary_pbwCoord (isPrimaryPairing_pairing _)]
  rfl

/-- Vectors of `U(Vir_-)χ_{R,S}(b⋆)` have exact kernel lifts, so `R_B` and `R_ρ` vanish on them
(l.2893–2897, 3000–3003). -/
theorem R_kill {u v : ℤ}
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH u v b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH u v b) z x = 0)
    {N : ℕ} {nv yv : Nat.Partition N → ℂ} {K : Nat.Partition N → ℂ⟦X⟧}
    (hK0 : ∀ Y, PowerSeries.constantCoeff (K Y) = nv Y)
    (hKG : (gram (cLoc b) (hLoc R S b) N).mulVec K = 0)
    (hKT : (torus (cLoc b) (hLoc R S b) (hLoc u v b) N).mulVec K = 0)
    (hKT' : Matrix.vecMul K (torus (cLoc b) (hLoc R S b) (hLoc u v b) N) = 0)
    (hn : pbwCoord N nv ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : pbwCoord N yv ∈ jantzen (kacC b) (kacH R S b) 1) :
    RB b R S (pbwCoord N nv) (pbwCoord N yv) = 0 ∧ RB b R S (pbwCoord N yv) (pbwCoord N nv) = 0 ∧
      Rρ b R S u v (pbwCoord N nv) (pbwCoord N yv) = 0 ∧
        Rρ b R S u v (pbwCoord N yv) (pbwCoord N nv) = 0 := by
  have hC : ∀ Y, PowerSeries.constantCoeff (PowerSeries.C (yv Y)) = yv Y := fun Y =>
    PowerSeries.constantCoeff_C _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← RB_coord hn hy hK0 hC, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      gram_transpose, hKG, zero_dotProduct, map_zero]
  · rw [← RB_coord hy hn hC hK0, hKG, dotProduct_zero, map_zero]
  · rw [← Rρ_coord hrad hn hy hK0 hC, Matrix.dotProduct_mulVec, hKT', zero_dotProduct, map_zero]
  · rw [← Rρ_coord hrad hy hn hC hK0, hKT, dotProduct_zero, map_zero]

end Forms

/-- `E_i = ∑_a (W₀⁻¹)_{ia} v_a`: the `v_a = ∑_i (W₀)_{ai} E_i` span the span of `E` when `W₀` is
invertible. -/
theorem span_of_unit {n N : ℕ} {E : Fin n → (Nat.Partition N → ℂ)} {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : IsUnit W.det) (z : Nat.Partition N → ℂ) (hz : z ∈ Submodule.span ℂ (Set.range E)) :
    z ∈ Submodule.span ℂ (Set.range fun a => ∑ i, W a i • E i) := by
  have hE : ∀ i, E i ∈ Submodule.span ℂ (Set.range fun a => ∑ i, W a i • E i) := by
    intro i
    have e1 : E i = ∑ a, W⁻¹ i a • ∑ j, W a j • E j := by
      have h1 : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have h2 : ∀ j, (∑ a, W⁻¹ i a * W a j) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
        intro j
        rw [← h1, Matrix.mul_apply]
      simp only [← Finset.sum_smul, h2, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e1]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  exact (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hE i)) hz

/-- Equation (13.3) at the node `μ`: `[X¹]ρ_X(χ₂,χ₂) = Ω_{u,v}(μ→ν₂) [X¹]B_X(χ₂,χ₂)` and
`[X¹]B_X(χ₂,χ₂) ≠ 0`, for the singular vector `χ₂ ∈ M(c⋆,μ)` of level `ℓ₂ = R₂S₂`. -/
theorem ratio_at (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) {k m : ℕ}
    (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (ε : Bool) (k₀ : ℕ) (ε₁ : Bool)
    {R S R₂ S₂ : ℕ}
    (hlab : arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1)) = ((R : ℤ), (S : ℤ)))
    (hlab₂ : arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s (!ε₁) (k₀ + 1)) =
      ((R₂ : ℤ), (S₂ : ℤ)))
    (hμ₂ : kacH R S b = kacH R₂ S₂ b) {ℓ₂ : ℕ} (hℓ : ℓ₂ = R₂ * S₂) {χ₂ : Verma ℂ (kacC b) (kacH R S b)}
    (hχ₂ : IsSingular χ₂ ℓ₂) (hJχ : χ₂ ∈ jantzen (kacC b) (kacH R S b) 1)
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) z x = 0) :
    Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) χ₂ χ₂ =
        (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) * RB b R S χ₂ χ₂ ∧ RB b R S χ₂ χ₂ ≠ 0 := by
  subst hℓ
  have hχl : χ₂ ∈ level (R₂ * S₂) := mem_level_of_L_zero hχ₂.2.1
  set x₂ := Verma.comp (R₂ * S₂) χ₂ with hx₂
  have hχx : pbwCoord (R₂ * S₂) x₂ = χ₂ := pbwCoord_comp_of_mem_level hχl
  have hs : IsSingular (pbwCoord (c := kacC b) (h := kacH R₂ S₂ b) (R₂ * S₂) x₂) (R₂ * S₂) := by
    have h1 : IsSingular (pbwCoord (c := kacC b) (h := kacH R S b) (R₂ * S₂) x₂) (R₂ * S₂) := by
      rw [hχx]; exact hχ₂
    exact isSingular_pbwCoord_congr hμ₂ h1
  set V₂ : Nat.Partition (R₂ * S₂) → ℂ⟦X⟧ := fun Y => PowerSeries.C (x₂ Y) with hV₂
  have hV₂0 : ∀ Y, PowerSeries.constantCoeff (V₂ Y) = x₂ Y := fun Y => PowerSeries.constantCoeff_C _
  have hJ' : pbwCoord (R₂ * S₂) x₂ ∈ jantzen (kacC b) (kacH R S b) 1 := by rw [hχx]; exact hJχ
  have hβ := RB_coord hJ' hJ' hV₂0 hV₂0
  have hβ' := Rρ_coord hrad hJ' hJ' hV₂0 hV₂0
  rw [hχx] at hβ hβ'
  have hrat := sub_tau_ratio_of_cited hK hE hH hU hF hLau p p' r s b hset k m hk hm ε k₀ ε₁ R S R₂ S₂
    hlab hlab₂ x₂ hs V₂ hV₂0
  have hne := tau_first_order_gram hJ hH hU hLau p p' r s b hset ε k₀ ε₁ R S R₂ S₂ hlab hlab₂ x₂ hs V₂
    hV₂0
  rw [← hβ, ← hβ']
  exact ⟨hrat, hne⟩

end Virasoro.P2
