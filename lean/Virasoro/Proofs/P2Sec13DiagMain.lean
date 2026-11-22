import Virasoro.Proofs.P2Sec13DiagFinal

/-!
# Lemma 13.1, Step 4: `Stmt_sub_tau_diag_limit` (paper.tex l.2990–3028)
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial

open scoped PowerSeries Matrix

theorem memJ_of_ker {c h : ℂ} {N : ℕ} {x : Nat.Partition N → ℂ} (hx : (gram c h N).mulVec x = 0) :
    pbwCoord N x ∈ jantzen c h 1 := by
  rw [← SetLike.mem_coe, jantzen_one_eq_radical]
  exact shap_radical_of_ker hx

theorem ker_of_memJ {c h : ℂ} {N : ℕ} {x : Nat.Partition N → ℂ} (hx : pbwCoord N x ∈ jantzen c h 1) :
    (gram c h N).mulVec x = 0 := by
  classical
  have hx' : pbwCoord N x ∈ ({v | ∀ u, shap c h u v = 0} : Set _) := by
    rw [← jantzen_one_eq_radical]; exact hx
  funext Y
  rw [gram_mulVec_eq_gramForm, ← shap_pbwCoord, isShapovalov_shap.symm]
  exact hx' _

theorem cc_dot (M : Matrix (Nat.Partition N) (Nat.Partition N) ℂ⟦X⟧) (U V : Nat.Partition N → ℂ⟦X⟧) :
    PowerSeries.constantCoeff (U ⬝ᵥ M.mulVec V) =
      (fun Y => PowerSeries.constantCoeff (U Y)) ⬝ᵥ
        (M.map PowerSeries.constantCoeff).mulVec (fun Y => PowerSeries.constantCoeff (V Y)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext Y
  exact (RingHom.map_mulVec _ M V Y)

theorem cc_gram {b : ℂ} {R S : ℕ} :
    (gram (cLoc b) (hLoc R S b) N).map PowerSeries.constantCoeff = gram (kacC b) (kacH R S b) N := by
  rw [← gram_map, constantCoeff_cLoc, constantCoeff_hLoc]

theorem cc_torus {b : ℂ} {R S : ℕ} {u v : ℤ} :
    (torus (cLoc b) (hLoc R S b) (hLoc u v b) N).map PowerSeries.constantCoeff =
      torus (kacC b) (kacH R S b) (kacH u v b) N := by
  rw [← torus_map, constantCoeff_cLoc, constantCoeff_hLoc, constantCoeff_hLoc]

theorem gram_ker_of_negSpan {c h : ℂ} {ℓ N : ℕ} {χ : Verma ℂ c h} (hχ : IsSingular χ ℓ) (hℓ : 1 ≤ ℓ)
    {v : Nat.Partition N → ℂ} (hv : pbwCoord N v ∈ negSpan χ) : (gram c h N).mulVec v = 0 := by
  classical
  funext Y
  rw [gram_mulVec_eq_gramForm, ← shap_pbwCoord]
  exact shap_negSpan_left hχ hℓ hv _

set_option maxHeartbeats 4000000 in
/-- `Stmt_sub_tau_diag_limit` (paper.tex l.2990–3028). -/
theorem sub_tau_diag_limit_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_sub_tau_diag_limit := by
  classical
  intro p p' r s b hset k m hk hm ε k₀ ε₁ N R S hlab χ hχ n E S₀ hLI hc hgen
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb := minimalSetting_b_ne_zero hset
  obtain ⟨hR, hS, hμ, hlev⟩ := arrow_facts hset ε k₀ ε₁ hlab
  obtain ⟨hkR, hmS⟩ := box_of_label hset hk hm ε k₀ ε₁ hlab
  have hRS : 1 ≤ R * S := Nat.mul_pos hR hS
  have hLay := sub_generic_layers_of_cited hK hE hH hU hF
  -- the generic values
  have hgenpart : ∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₀ →
      RegAt b' (trRat E R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) ∧
        ∀ T : ℂ, IsIrrTrace (kacC b') (kacH R S b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b')
          N T → evalAt b' (trRat E R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1)) = T := by
    intro b' hb' hirr hS₀
    have hcomp := hgen b' hb' hirr hS₀
    have hdet' := det_ne_zero_of_compl hLI hcomp
    obtain ⟨hreg, hval⟩ := trRat_generic (E := E) hb' R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) hdet'
    refine ⟨hreg, fun T hT => ?_⟩
    have hd := generic_descends hH hU hF hLay hb' hirr hR hS hkR hmS
    rw [hval]
    exact ((irrTrace_existsUnique hd N).unique hT ⟨n, E, hLI, hcomp, hdet', rfl⟩).symm
  -- `det G_E ≠ 0` over `ℂ[b,b⁻¹]`
  have hden : (GLam E R S).det ≠ 0 := by
    obtain ⟨b', hb', hirr, hS₀⟩ := (generic_infinite S₀).nonempty
    intro h0
    have h1 := congrArg (evLam b' hb') h0
    rw [RingHom.map_det, map_GLam (E := E) (e := E) (evLam b' hb') (evLam_cLam hb')
      (evLam_hLam hb' R S) (evLam_ELam hb'), map_zero] at h1
    exact det_ne_zero_of_compl hLI (hgen b' hb' hirr hS₀) h1
  -- the Gram matrix of `E` over `ℂ⟦X⟧` and an orthogonal basis
  have hentG : (Matrix.of fun i j => gramForm (cLoc b) (hLoc R S b) N
      (fun Y => PowerSeries.C (E i Y)) (fun Y => PowerSeries.C (E j Y))) =
      (Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E := by
    ext i j
    rw [Matrix.of_apply, gramForm_Fm]
    rfl
  have hdetX : ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E).det ≠ 0 := by
    have hG := map_GLam (E := E) (e := fun i Y => PowerSeries.C (E i Y)) (locLam b hb)
      (locLam_cLam hb) (locLam_hLam hb R S) (locLam_ELam hb)
    rw [hentG] at hG
    rw [← hG, ← RingHom.map_det]
    intro h0
    exact hden (locLam_injective hb (h0.trans (map_zero _).symm))
  have hsymm : ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      gram_transpose, Matrix.mul_assoc]
  obtain ⟨w, e, uu, hw, hu, hdg, ho⟩ := exists_orth_basis hsymm hdetX
  have h : OrthBasis ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) w e uu := ⟨hw, hu, hdg, ho⟩
  -- Step 3 and the kernel lifts of Step 2
  have hdepth := sub_tau_depth_one_of_cited hK hE hH hU hF hLau hJ p p' r s b hset ε k₀ ε₁ R S
    hlab χ hχ N
  have hKL := sub_tau_kernel_lift_of_cited hK hE hH hU hF hLau b hb R S hR hS χ hχ
  have hlift : ∀ v : Nat.Partition N → ℂ, pbwCoord N v ∈ negSpan χ →
      ∃ V : Nat.Partition N → ℂ⟦X⟧, (∀ Y, PowerSeries.constantCoeff (V Y) = v Y) ∧
        (gram (cLoc b) (hLoc R S b) N).mulVec V = 0 := fun v hv => by
    obtain ⟨V, h0, hG, -⟩ := hKL N v hv
    exact ⟨V, h0, hG⟩
  obtain ⟨va, hva⟩ : ∃ va : Fin n → (Nat.Partition N → ℂ),
      ∀ a, va a = ∑ i, (fun Z => PowerSeries.constantCoeff (w a Z)) i • E i := ⟨_, fun a => rfl⟩
  have he : ∀ a, e a ≤ 1 ∧ (e a = 1 → (gram (kacC b) (kacH R S b) N).mulVec (va a) = 0) := by
    intro a
    rw [hva a]
    exact e_le_one hLI hc hdepth hlift h a
  have hWv0 : ∀ a Y, PowerSeries.constantCoeff ((Fm E).mulVec (w a) Y) = va a Y := by
    intro a Y
    rw [hva a]
    exact constantCoeff_Fm_mulVec E _ Y
  -- the radical of `ρ₀` at `μ`
  have hradμ : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) z x = 0 := by
    rw [hμ]
    exact fun x hx z => sub_vertex_radical_zero hJ hH hU hF p p' r s b hset ε k₀ k m hk hm _
      (isPrimaryPairing_pairing _) x hx z
  have hdμ : TorusDescends (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) := by
    rw [hμ]
    exact torusDescends_of_radical fun T hT =>
      sub_vertex_radical_zero hJ hH hU hF p p' r s b hset ε k₀ k m hk hm T hT
  -- the forms on the basis
  have hbfG : ∀ a a', bf ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) (w a) (w a') =
      (Fm E).mulVec (w a) ⬝ᵥ (gram (cLoc b) (hLoc R S b) N).mulVec ((Fm E).mulVec (w a')) :=
    fun a a' => bf_Fm E _ _ _
  have hbfT : ∀ a a', w a ⬝ᵥ ((Fm E)ᵀ * torus (cLoc b) (hLoc R S b)
      (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N * Fm E).mulVec (w a') =
      (Fm E).mulVec (w a) ⬝ᵥ (torus (cLoc b) (hLoc R S b)
        (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N).mulVec ((Fm E).mulVec (w a')) :=
    fun a a' => bf_Fm E _ _ _
  have hccG : ∀ a a', PowerSeries.constantCoeff
      (bf ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) (w a) (w a')) =
      gramForm (kacC b) (kacH R S b) N (va a) (va a') := by
    intro a a'
    rw [hbfG, cc_dot, cc_gram]
    have e1 : (fun Y => PowerSeries.constantCoeff ((Fm E).mulVec (w a) Y)) = va a := funext (hWv0 a)
    have e2 : (fun Y => PowerSeries.constantCoeff ((Fm E).mulVec (w a') Y)) = va a' :=
      funext (hWv0 a')
    rw [e1, e2]
    rfl
  have hccT : ∀ a a', PowerSeries.constantCoeff (w a ⬝ᵥ ((Fm E)ᵀ * torus (cLoc b) (hLoc R S b)
      (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N * Fm E).mulVec (w a')) =
      torusForm (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N (va a)
        (va a') := by
    intro a a'
    rw [hbfT, cc_dot, cc_torus]
    have e1 : (fun Y => PowerSeries.constantCoeff ((Fm E).mulVec (w a) Y)) = va a := funext (hWv0 a)
    have e2 : (fun Y => PowerSeries.constantCoeff ((Fm E).mulVec (w a') Y)) = va a' :=
      funext (hWv0 a')
    rw [e1, e2]
    rfl
  have hJva : ∀ a, e a = 1 → pbwCoord N (va a) ∈ jantzen (kacC b) (kacH R S b) 1 :=
    fun a h1 => memJ_of_ker ((he a).2 h1)
  have hRBa : ∀ a a', e a = 1 → e a' = 1 → PowerSeries.coeff 1
      (bf ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) (w a) (w a')) =
        RB b R S (pbwCoord N (va a)) (pbwCoord N (va a')) := by
    intro a a' h1 h1'
    rw [hbfG]
    exact RB_coord (hJva a h1) (hJva a' h1') (hWv0 a) (hWv0 a')
  have hRρa : ∀ a, e a = 1 → PowerSeries.coeff 1 (w a ⬝ᵥ ((Fm E)ᵀ * torus (cLoc b) (hLoc R S b)
      (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N * Fm E).mulVec (w a)) =
        Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (pbwCoord N (va a)) (pbwCoord N (va a)) := by
    intro a h1
    rw [hbfT]
    exact Rρ_coord hradμ (hJva a h1) (hJva a h1) (hWv0 a) (hWv0 a)
  -- the divisibility of `ρ_X(v_a,v_a)`
  have hr : ∀ a, ∃ ra : ℂ⟦X⟧, w a ⬝ᵥ ((Fm E)ᵀ * torus (cLoc b) (hLoc R S b)
      (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N * Fm E).mulVec (w a) =
        (PowerSeries.X : ℂ⟦X⟧) ^ e a * ra := by
    intro a
    rcases Nat.lt_or_ge (e a) 1 with h0 | h1
    · refine ⟨_, by rw [show e a = 0 by omega, pow_zero, one_mul]⟩
    · have h1' : e a = 1 := le_antisymm (he a).1 h1
      rw [h1', pow_one]
      show (PowerSeries.X : ℂ⟦X⟧) ∣ _
      rw [PowerSeries.X_dvd_iff, hccT]
      exact (torusForm_ker_of_descends hdμ ((he a).2 h1') (va a)).1
  choose rr hrr using hr
  obtain ⟨hregb, hvalb⟩ := trRat_local hb hden h hrr
  have hcu : ∀ a, PowerSeries.constantCoeff (uu a) = PowerSeries.coeff (e a)
      (bf ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) (w a) (w a)) := by
    intro a
    rw [h.diag a, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hcr : ∀ a, PowerSeries.constantCoeff (rr a) = PowerSeries.coeff (e a)
      (w a ⬝ᵥ ((Fm E)ᵀ * torus (cLoc b) (hLoc R S b)
        (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N * Fm E).mulVec (w a)) := by
    intro a
    rw [hrr a, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hu0 : ∀ a, PowerSeries.constantCoeff (uu a) ≠ 0 := fun a => by
    have := h.hu a
    rw [PowerSeries.isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  have horth0 : ∀ a a', a ≠ a' → gramForm (kacC b) (kacH R S b) N (va a) (va a') = 0 := by
    intro a a' hne
    rw [← hccG, h.orth a a' hne, map_zero]
  refine ⟨trRat E R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1), S₀, hgenpart, hregb, ?_⟩
  intro T₁ T₂ hT₁ hT₂ hT₂0
  rw [hvalb, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => e a = 0)]
  -- Part A: the terms with `e_a = 0`
  have hA : (∑ a ∈ Finset.univ.filter (fun a => e a = 0),
      (PowerSeries.constantCoeff (uu a))⁻¹ * PowerSeries.constantCoeff (rr a)) = T₁ := by
    have hT₁' : IsIrrTrace (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N T₁ := by
      rw [hμ]; exact hT₁
    have hterm : ∀ a, e a = 0 → (PowerSeries.constantCoeff (uu a))⁻¹ *
        PowerSeries.constantCoeff (rr a) =
          torusForm (kacC b) (kacH R S b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N (va a)
            (va a) / gramForm (kacC b) (kacH R S b) N (va a) (va a) := by
      intro a h0
      rw [hcu, hcr, h0, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hccG, hccT, inv_mul_eq_div]
    rw [Finset.sum_congr rfl fun a ha => hterm a (Finset.mem_filter.1 ha).2]
    have hdiagA : ∀ a : {a // e a = 0}, gramForm (kacC b) (kacH R S b) N (va a) (va a) ≠ 0 := by
      intro a
      rw [← hccG, h.diag, a.2, pow_zero, one_mul]
      exact hu0 a
    have hspanA : ∀ z, z ∈ Submodule.span ℂ (Set.range fun a : {a // e a = 0} => va a) ⊔
        LinearMap.ker (gram (kacC b) (kacH R S b) N).mulVecLin := by
      intro z
      obtain ⟨x, hx, n', hn', rfl⟩ := Submodule.mem_sup.1
        (show z ∈ Submodule.span ℂ (Set.range E) ⊔ (negSpan χ).comap (pbwCoord N) by
          rw [hc.sup_eq_top]; exact Submodule.mem_top)
      have hW : IsUnit ((Matrix.of w).map PowerSeries.constantCoeff).det := by
        have e4 : ((Matrix.of w).map PowerSeries.constantCoeff).det =
            PowerSeries.constantCoeff (Matrix.of w).det :=
          (RingHom.map_det (PowerSeries.constantCoeff (R := ℂ)) (Matrix.of w)).symm
        rw [e4]
        exact h.unit.map _
      have hx' := span_of_unit hW x hx
      have e3 : (fun a => ∑ i, (Matrix.of w).map PowerSeries.constantCoeff a i • E i) = va := by
        funext a
        rw [hva a]
        rfl
      rw [e3] at hx'
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => e a = 0), add_assoc]
      refine Submodule.add_mem_sup ?_ ?_
      · refine Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨a, (Finset.mem_filter.1 ha).2⟩, rfl⟩)
      · refine Submodule.add_mem _ (Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_) ?_
        · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          exact (he a).2 (le_antisymm (he a).1 (Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 ha).2))
        · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          exact gram_ker_of_negSpan hχ hRS hn'
    have := irrTrace_of_diag hdμ (fun a : {a // e a = 0} => va a)
      (fun a a' hne => horth0 a a' (fun h' => hne (Subtype.ext h'))) hdiagA hspanA hT₁'
    rw [this, Finset.sum_subtype (Finset.univ.filter (fun a => e a = 0)) (p := fun a => e a = 0)
      (by simp)]
  rw [hA]
  congr 1
  -- Part B: the terms with `e_a = 1`
  have hterm1 : ∀ a, e a ≠ 0 → (PowerSeries.constantCoeff (uu a))⁻¹ *
      PowerSeries.constantCoeff (rr a) =
        Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (pbwCoord N (va a)) (pbwCoord N (va a)) /
          RB b R S (pbwCoord N (va a)) (pbwCoord N (va a)) := by
    intro a h0
    have h1 : e a = 1 := le_antisymm (he a).1 (Nat.one_le_iff_ne_zero.2 h0)
    rw [hcu, hcr, h1, hRBa a a h1 h1, hRρa a h1, inv_mul_eq_div]
  rw [Finset.sum_congr rfl fun a ha => hterm1 a (Finset.mem_filter.1 ha).2]
  -- the second arrow `μ → ν₂`
  obtain ⟨R₂, S₂, hR₂, hS₂, hsum₂, hdiff₂, -, hcS₂, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ (!ε₁)
  have hlab₂ := arrowLabel_eq hcop hp hp' hsum₂ hdiff₂ (not_dvd_of_congr hs0 hs hcS₂)
  obtain ⟨-, -, hμ₂, hlev₂⟩ := arrow_facts hset ε k₀ (!ε₁) hlab₂
  have hR₂S₂ : 1 ≤ R₂ * S₂ := Nat.mul_pos hR₂ hS₂
  have hle₂ : ellOrb p p' r s ε k₀ ≤ ellOrb p p' r s (!ε₁) (k₀ + 1) := by omega
  have hν₂ : kacH R S b + ((R₂ * S₂ : ℕ) : ℂ) = muOrb p p' r s (!ε₁) (k₀ + 1) := by
    rw [hμ, ← hlev₂]
    exact muOrb_add_lev hp hp' hr hs ε k₀ (!ε₁) (k₀ + 1) hle₂
  rw [hlev₂] at hT₂ hT₂0
  -- `J¹ = M(ν₁) + M(ν₂)` (Lemma 10.3(i))
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, hJ1, -⟩ := orbit_length_two hJ hset ε k₀ ε₁ (kacH R S b) hμ
  rw [hlev] at hχ₁
  rw [hlev₂] at hχ₂
  obtain ⟨a₁, ha₁⟩ := hU _ _ _ χ χ₁ hχ hχ₁
  have ha₁0 : a₁ ≠ 0 := by
    rintro rfl
    exact hχ₁.1 (ha₁.trans (zero_smul ℂ χ))
  rw [ha₁, negSpan_smul _ ha₁0] at hJ1
  have hnegJ : ∀ {N₀ : ℕ} {x : Nat.Partition N₀ → ℂ}, pbwCoord N₀ x ∈ negSpan χ →
      pbwCoord N₀ x ∈ jantzen (kacC b) (kacH R S b) 1 := fun hx => by
    rw [hJ1]; exact Submodule.mem_sup_left hx
  -- `j : M(c⋆,ν₂) → J¹`
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hχ₂.2.1 hχ₂.2.2
  have hjJ : ∀ v, j v ∈ jantzen (kacC b) (kacH R S b) 1 := by
    intro v
    rw [hJ1]
    exact Submodule.mem_sup_right (by rw [negSpan_eq_range j hjneg]; exact ⟨v, rfl⟩)
  have hχ₂J : χ₂ ∈ jantzen (kacC b) (kacH R S b) 1 := by rw [← hjhw]; exact hjJ _
  obtain ⟨hratio, hβ0⟩ := ratio_at hK hE hH hU hF hLau hJ hset hk hm ε k₀ ε₁ hlab hlab₂
    (hμ.trans hμ₂.symm) rfl hχ₂ hχ₂J hradμ
  have hRBj := RB_hom j hjL hjJ
  have hRρj := Rρ_hom j hjL hjJ hradμ
  rw [hjhw] at hRBj hRρj
  -- coordinates of `χ₂` and the level structure of `M(ν₂)`
  have hχl : χ₂ ∈ level (R₂ * S₂) := mem_level_of_L_zero hχ₂.2.1
  set x₂ := Verma.comp (R₂ * S₂) χ₂ with hx₂
  have hχx : pbwCoord (R₂ * S₂) x₂ = χ₂ := pbwCoord_comp_of_mem_level hχl
  have hjneg' : ∀ w' : List ℕ, j (neg w') = VirEnv.negOp (kacC b) w' •
      pbwCoord (c := kacC b) (h := kacH R S b) (R₂ * S₂) x₂ := fun w' => by rw [hjneg, hχx]
  have hχ₂' : IsSingular (pbwCoord (c := kacC b) (h := kacH R S b) (R₂ * S₂) x₂) (R₂ * S₂) := by
    rw [hχx]; exact hχ₂
  have hNL := negSpan_level hI hχ₂'
  -- the decomposition of `v_a(0)`, `e_a = 1`
  have hdec0 : ∀ a, e a ≠ 0 → ∃ nN mN : Nat.Partition N → ℂ, pbwCoord N nN ∈ negSpan χ ∧
      pbwCoord N mN ∈ negSpan (pbwCoord (c := kacC b) (h := kacH R S b) (R₂ * S₂) x₂) ∧
        va a = nN + mN := by
    intro a h0
    have h1 : e a = 1 := le_antisymm (he a).1 (Nat.one_le_iff_ne_zero.2 h0)
    have hy := hJva a h1
    rw [hJ1] at hy
    obtain ⟨n0, hn0, m0, hm0, hnm⟩ := Submodule.mem_sup.1 hy
    refine ⟨Verma.comp N n0, Verma.comp N m0, level_part_mem hχ N hn0, ?_, ?_⟩
    · rw [hχx]; exact level_part_mem hχ₂ N hm0
    · have := congrArg (Verma.comp N) hnm
      rw [map_add, comp_pbwCoord_same] at this
      exact this.symm
  have hva0 : ∀ a, va a ≠ 0 := by
    intro a h0
    have hz : (fun Z => PowerSeries.constantCoeff (w a Z)) = 0 := by
      rw [hva a] at h0
      funext Z
      exact (Fintype.linearIndependent_iff.1 hLI) _ h0 Z
    exact (OrthBasis.linearIndependent_val0 h).ne_zero a hz
  by_cases hN : R₂ * S₂ ≤ N
  swap
  · -- `N < ℓ₂`: no terms with `e_a = 1`
    push_neg at hN
    rw [hT₂0 hN, mul_zero]
    refine Finset.sum_eq_zero fun a ha => ?_
    exfalso
    obtain ⟨nN, mN, hnN, hmN, hsum⟩ := hdec0 a (Finset.mem_filter.1 ha).2
    have hm0 : mN = 0 := by
      have := hNL.2 N hN
      have hmem : mN ∈ (negSpan (pbwCoord (c := kacC b) (h := kacH R S b) (R₂ * S₂) x₂)).comap
          (pbwCoord N) := hmN
      rw [this, Submodule.mem_bot] at hmem
      exact hmem
    rw [hm0, add_zero] at hsum
    have hbot : va a ∈ Submodule.span ℂ (Set.range E) ⊓ (negSpan χ).comap (pbwCoord N) := by
      refine ⟨?_, by rw [hsum]; exact hnN⟩
      rw [hva a]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hbot
    exact hva0 a hbot
  · obtain ⟨N', rfl⟩ := Nat.exists_eq_add_of_le hN
    have hT₂' : IsIrrTrace (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ))
        (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N' T₂ := by
      have := hT₂ hN
      rw [Nat.add_sub_cancel_left, ← hν₂] at this
      exact this
    have hdν₂ : TorusDescends (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ))
        (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) := by
      rw [hν₂]
      exact torusDescends_of_radical fun T hT =>
        sub_vertex_radical_zero hJ hH hU hF p p' r s b hset (!ε₁) (k₀ + 1) k m hk hm T hT
    have hjz : ∀ z : Nat.Partition N' → ℂ, j (pbwCoord N' z) = pbwCoord (R₂ * S₂ + N')
        (Fintype.linearCombination ℂ (iotaCols (kacC b) (kacH R S b) (R₂ * S₂) N' x₂) z) :=
      fun z => j_pbwCoord hjneg' N' z
    -- `v_a(0) = n_a + j(z_a)` with `n_a ∈ U(Vir_-)χ_{R,S}(b⋆)`
    have hdec : ∀ a, ∃ nN : Nat.Partition (R₂ * S₂ + N') → ℂ, ∃ z : Nat.Partition N' → ℂ,
        e a ≠ 0 → pbwCoord (R₂ * S₂ + N') nN ∈ negSpan χ ∧
          va a = nN + Fintype.linearCombination ℂ (iotaCols (kacC b) (kacH R S b) (R₂ * S₂) N' x₂) z := by
      intro a
      by_cases h0 : e a = 0
      · exact ⟨0, 0, fun h' => absurd h0 h'⟩
      obtain ⟨nN, mN, hnN, hmN, hsum⟩ := hdec0 a h0
      have hmem : mN ∈ Submodule.span ℂ
          (Set.range (iotaCols (kacC b) (kacH R S b) (R₂ * S₂) N' x₂)) := by
        rw [← (hNL.1 N').1]; exact hmN
      rw [← Fintype.range_linearCombination] at hmem
      obtain ⟨z, hz⟩ := hmem
      exact ⟨nN, z, fun _ => ⟨hnN, by rw [hsum, hz]⟩⟩
    choose nN z hnz using hdec
    have hlcJ : ∀ zz : Nat.Partition N' → ℂ, pbwCoord (R₂ * S₂ + N')
        (Fintype.linearCombination ℂ (iotaCols (kacC b) (kacH R S b) (R₂ * S₂) N' x₂) zz) ∈
          jantzen (kacC b) (kacH R S b) 1 := fun zz => by rw [← hjz]; exact hjJ _
    have hkill : ∀ nv : Nat.Partition (R₂ * S₂ + N') → ℂ, pbwCoord (R₂ * S₂ + N') nv ∈ negSpan χ →
        ∀ yv : Nat.Partition (R₂ * S₂ + N') → ℂ,
          pbwCoord (R₂ * S₂ + N') yv ∈ jantzen (kacC b) (kacH R S b) 1 →
        RB b R S (pbwCoord _ nv) (pbwCoord _ yv) = 0 ∧ RB b R S (pbwCoord _ yv) (pbwCoord _ nv) = 0 ∧
          Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (pbwCoord _ nv) (pbwCoord _ yv) = 0 ∧
            Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (pbwCoord _ yv) (pbwCoord _ nv) = 0 := by
      intro nv hnv yv hyv
      obtain ⟨K, hK0, hKG, hKT⟩ := hKL _ nv hnv
      exact R_kill hradμ hK0 hKG (hKT k m hkR hmS).1 (hKT k m hkR hmS).2 (hnegJ hnv) hyv
    -- the forms on the vectors `v_a(0)`, `e_a = 1`
    have hY : ∀ a, e a ≠ 0 → pbwCoord (c := kacC b) (h := kacH R S b) (R₂ * S₂ + N') (va a) =
        pbwCoord (R₂ * S₂ + N') (nN a) + pbwCoord (R₂ * S₂ + N')
          (Fintype.linearCombination ℂ (iotaCols (kacC b) (kacH R S b) (R₂ * S₂) N' x₂) (z a)) :=
      fun a h0 => by rw [(hnz a h0).2, map_add]
    have hRBY : ∀ a a', e a ≠ 0 → e a' ≠ 0 →
        RB b R S (pbwCoord _ (va a)) (pbwCoord _ (va a')) =
          RB b R S χ₂ χ₂ * gramForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N' (z a) (z a') := by
      intro a a' h0 h0'
      have hnJ := hnegJ (hnz a h0).1
      have hnJ' := hnegJ (hnz a' h0').1
      rw [hY a h0, hY a' h0', RB_add_left hnJ (hlcJ _) (Submodule.add_mem _ hnJ' (hlcJ _)),
        RB_add_right hnJ hnJ' (hlcJ _), RB_add_right (hlcJ _) hnJ' (hlcJ _),
        (hkill _ (hnz a h0).1 _ hnJ').1, (hkill _ (hnz a h0).1 _ (hlcJ _)).1,
        (hkill _ (hnz a' h0').1 _ (hlcJ _)).2.1, zero_add, zero_add, zero_add, ← hjz, ← hjz,
        hRBj, shap_pbwCoord]
    have hRρY : ∀ a, e a ≠ 0 →
        Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (pbwCoord _ (va a)) (pbwCoord _ (va a)) =
          Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) χ₂ χ₂ *
            torusForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ))
              (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N' (z a) (z a) := by
      intro a h0
      have hnJ := hnegJ (hnz a h0).1
      rw [hY a h0, Rρ_add_left hradμ hnJ (hlcJ _) (Submodule.add_mem _ hnJ (hlcJ _)),
        Rρ_add_right hradμ hnJ hnJ (hlcJ _), Rρ_add_right hradμ (hlcJ _) hnJ (hlcJ _),
        (hkill _ (hnz a h0).1 _ hnJ).2.2.1, (hkill _ (hnz a h0).1 _ (hlcJ _)).2.2.1,
        (hkill _ (hnz a h0).1 _ (hlcJ _)).2.2.2, zero_add, zero_add, zero_add, ← hjz, hRρj,
        primary_pbwCoord (isPrimaryPairing_pairing _)]
    have hterm2 : ∀ a, e a ≠ 0 →
        Rρ b R S (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) (pbwCoord _ (va a)) (pbwCoord _ (va a)) /
          RB b R S (pbwCoord _ (va a)) (pbwCoord _ (va a)) =
        (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) *
          (torusForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ))
              (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N' (z a) (z a) /
            gramForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N' (z a) (z a)) := by
      intro a h0
      rw [hRρY a h0, hRBY a a h0 h0, hratio, mul_comm (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ),
        mul_assoc, mul_div_mul_left _ _ hβ0, mul_div_assoc]
    rw [Finset.sum_congr rfl fun a ha => hterm2 a (Finset.mem_filter.1 ha).2, ← Finset.mul_sum]
    congr 1
    -- `T₂` through the family `z_a`
    have hgB : ∀ a a', e a ≠ 0 → e a' ≠ 0 → RB b R S χ₂ χ₂ *
        gramForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N' (z a) (z a') =
          PowerSeries.coeff 1 (bf ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) (R₂ * S₂ + N') * Fm E)
            (w a) (w a')) := by
      intro a a' h0 h0'
      rw [← hRBY a a' h0 h0', hRBa a a' (le_antisymm (he a).1 (Nat.one_le_iff_ne_zero.2 h0))
        (le_antisymm (he a').1 (Nat.one_le_iff_ne_zero.2 h0'))]
    have horthB : ∀ a a' : {a // ¬ e a = 0}, a ≠ a' →
        gramForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N' (z a) (z a') = 0 := by
      intro a a' hne
      have h1 := hgB a a' a.2 a'.2
      rw [h.orth a a' (fun h' => hne (Subtype.ext h')), map_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hβ0
    have hdiagB : ∀ a : {a // ¬ e a = 0},
        gramForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N' (z a) (z a) ≠ 0 := by
      intro a h0
      have h1 := hgB a a a.2 a.2
      have h2 := hcu a
      rw [le_antisymm (he a).1 (Nat.one_le_iff_ne_zero.2 a.2)] at h2
      rw [h0, mul_zero, ← h2] at h1
      exact hu0 a h1.symm
    have hspanB : ∀ zz : Nat.Partition N' → ℂ, zz ∈ Submodule.span ℂ
        (Set.range fun a : {a // ¬ e a = 0} => z a) ⊔
          LinearMap.ker (gram (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N').mulVecLin := by
      intro zz
      set lc := Fintype.linearCombination ℂ (iotaCols (kacC b) (kacH R S b) (R₂ * S₂) N' x₂)
        with hlc
      have hqker := ker_of_memJ (hlcJ zz)
      obtain ⟨x, hx, n', hn', hxn⟩ := Submodule.mem_sup.1
        (show lc zz ∈ Submodule.span ℂ (Set.range E) ⊔ (negSpan χ).comap (pbwCoord _) by
          rw [hc.sup_eq_top]; exact Submodule.mem_top)
      have hW : IsUnit ((Matrix.of w).map PowerSeries.constantCoeff).det := by
        have e4 : ((Matrix.of w).map PowerSeries.constantCoeff).det =
            PowerSeries.constantCoeff (Matrix.of w).det :=
          (RingHom.map_det (PowerSeries.constantCoeff (R := ℂ)) (Matrix.of w)).symm
        rw [e4]
        exact h.unit.map _
      have hx' := span_of_unit hW x hx
      have e3 : (fun a => ∑ i, (Matrix.of w).map PowerSeries.constantCoeff a i • E i) = va := by
        funext a
        rw [hva a]
        rfl
      rw [e3] at hx'
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
      have hn'ker := gram_ker_of_negSpan hχ hRS hn'
      have hc0 : ∀ a', e a' = 0 → c a' = 0 := by
        intro a' h0
        have h1 : gramForm (kacC b) (kacH R S b) _ (va a') (lc zz) = 0 := by
          rw [gramForm, hqker, dotProduct_zero]
        have h2 : gramForm (kacC b) (kacH R S b) _ (va a') n' = 0 := by
          rw [gramForm, hn'ker, dotProduct_zero]
        rw [← hxn] at h1
        have h3 : gramForm (kacC b) (kacH R S b) _ (va a') ((∑ a, c a • va a) + n') =
            gramForm (kacC b) (kacH R S b) _ (va a') (∑ a, c a • va a) +
              gramForm (kacC b) (kacH R S b) _ (va a') n' := by
          simp only [gramForm, Matrix.mulVec_add, dotProduct_add]
        rw [h3, h2, add_zero, gramForm_sum_right, Finset.sum_eq_single a'
          (fun a _ hne => by rw [horth0 a' a hne.symm, mul_zero])
          (fun h' => absurd (Finset.mem_univ a') h')] at h1
        have hg : gramForm (kacC b) (kacH R S b) _ (va a') (va a') ≠ 0 := by
          rw [← hccG, h.diag, h0, pow_zero, one_mul]
          exact hu0 a'
        exact (mul_eq_zero.1 h1).resolve_right hg
      have hxsum : (∑ a, c a • va a) = ∑ a ∈ Finset.univ.filter (fun a => ¬ e a = 0), c a • va a := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => e a = 0),
          Finset.sum_eq_zero (fun a ha => by rw [hc0 a (Finset.mem_filter.1 ha).2, zero_smul]),
          zero_add]
      set zz' := zz - ∑ a ∈ Finset.univ.filter (fun a => ¬ e a = 0), c a • z a with hzz'
      set nn := (∑ a ∈ Finset.univ.filter (fun a => ¬ e a = 0), c a • nN a) + n' with hnn
      have hlczz' : lc zz' = nn := by
        rw [hzz', map_sub, map_sum, ← hxn, hxsum, hnn]
        have e5 : ∀ a ∈ Finset.univ.filter (fun a => ¬ e a = 0),
            c a • va a = c a • nN a + lc (c a • z a) := by
          intro a ha
          rw [(hnz a (Finset.mem_filter.1 ha).2).2, map_smul, smul_add]
        rw [Finset.sum_congr rfl e5, Finset.sum_add_distrib]
        abel
      have hnnneg : pbwCoord _ nn ∈ negSpan χ := by
        rw [hnn, map_add, map_sum]
        exact Submodule.add_mem _ (Submodule.sum_mem _ fun a ha => by
          rw [map_smul]; exact Submodule.smul_mem _ _ (hnz a (Finset.mem_filter.1 ha).2).1) hn'
      have hgz : ∀ z'', gramForm (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N' zz' z'' = 0 := by
        intro z''
        have h1 := hRBj (pbwCoord N' zz') (pbwCoord N' z'')
        rw [hjz, hjz, hlczz', (hkill _ hnnneg _ (hlcJ z'')).1, shap_pbwCoord] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_left hβ0
      have hker : zz' ∈ LinearMap.ker
          (gram (kacC b) (kacH R S b + ((R₂ * S₂ : ℕ) : ℂ)) N').mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        funext Y
        have := hgz (Pi.single Y 1)
        rw [gramForm_symm', gramForm, single_dotProduct, one_mul] at this
        exact this
      have hzz : zz = (∑ a ∈ Finset.univ.filter (fun a => ¬ e a = 0), c a • z a) + zz' := by
        rw [hzz']; abel
      rw [hzz]
      refine Submodule.add_mem_sup (Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨a, (Finset.mem_filter.1 ha).2⟩, rfl⟩)) hker
    have := irrTrace_of_diag hdν₂ (fun a : {a // ¬ e a = 0} => z a) horthB hdiagB hspanB hT₂'
    rw [this, Finset.sum_subtype (Finset.univ.filter (fun a => ¬ e a = 0))
      (p := fun a => ¬ e a = 0) (by simp)]

/-- Lemma 13.1 (paper.tex l.2851–3038), from its cited inputs.
Paper label: lem:degenerate-quotient-t -/
theorem lem_degenerate_quotient_t_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_diag hK hE hH hU hF hLau hI
    (sub_tau_diag_limit_of_cited hK hE hH hU hF hLau hJ hI)

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_cited hK hE hH hU hF hLau hJ hI

end Virasoro.P2
