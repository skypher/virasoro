import Virasoro.Proofs.P2Sec13TauSteps
import Virasoro.Proofs.P2Sec9BoxFinal
import Virasoro.Proofs.ResidueCore1

/-!
# Lemma 13.1, Step 2: the complement of the descendants (paper.tex l.2910–2918)

"The PBW descendants `{L_{-I}χ_{R₁,S₁}(b⋆)}` are linearly independent in `M(c⋆,μ)_N`.
Completing them to a basis yields a free submodule complement."  The descendants have Laurent
coordinates in `b`; the determinant of the completed family is a Laurent polynomial that is
nonzero at `b⋆`, so the completion `E` stays a complement of the span of the descendants outside
a finite set, and at generic `b` this span is the radical `ker G_N` (Step 1).
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial Module

/-- A nonzero Laurent polynomial has finitely many zeros. -/
theorem lam_zeros_finite {a : Lam} (ha : a ≠ 0) :
    {b : ℂ | ∃ hb : b ≠ 0, evLam b hb a = 0}.Finite := by
  by_contra hinf
  refine ha (lam_eq_zero_of_infinite (G := {b : ℂ | ∃ hb : b ≠ 0, evLam b hb a = 0}) hinf ?_)
  rintro b hb ⟨_, h0⟩
  exact h0

section Level

variable {c h : ℂ} {ℓ : ℕ} {x : Nat.Partition ℓ → ℂ}

/-- The coordinates of the descendants `L_{-Z}χ`, `|Z| = M`. -/
noncomputable def iotaCols (c h : ℂ) (ℓ M : ℕ) (x : Nat.Partition ℓ → ℂ) :
    Nat.Partition M → (Nat.Partition (ℓ + M) → ℂ) := fun Z Y => iotaMat c h ℓ M x Y Z

theorem iota_mulVecLin_eq (M : ℕ) :
    (iotaMat c h ℓ M x).mulVecLin = Fintype.linearCombination ℂ (iotaCols c h ℓ M x) := by
  refine LinearMap.ext fun u => ?_
  funext Y
  simp [iotaCols, Fintype.linearCombination_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem pbwCoord_linearCombination_iota (M : ℕ) (u : Nat.Partition M → ℂ) :
    pbwCoord (c := c) (h := h) (ℓ + M) (Fintype.linearCombination ℂ (iotaCols c h ℓ M x) u) =
      ∑ Z, u Z • (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h) ℓ x) := by
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [map_smul]
  congr 1
  exact pbwCoord_iotaMat_col c h ℓ M x Z

theorem j_pbwCoord {j : Verma ℂ c (h + ℓ) →ₗ[ℂ] Verma ℂ c h}
    (hjneg : ∀ w : List ℕ, j (neg w) = VirEnv.negOp c w • pbwCoord (c := c) (h := h) ℓ x)
    (M : ℕ) (u : Nat.Partition M → ℂ) :
    j (pbwCoord M u) =
      pbwCoord (ℓ + M) (Fintype.linearCombination ℂ (iotaCols c h ℓ M x) u) := by
  rw [pbwCoord_linearCombination_iota, pbwCoord_apply, map_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [map_smul, hjneg]

/-- The level structure of `U(Vir_-)χ` for a singular vector `χ` of level `ℓ` (l.2910–2913):
on the level `ℓ + M` it is spanned by the descendants `L_{-Z}χ`, `|Z| = M`, which are linearly
independent, and it has no vectors below the level `ℓ`. -/
theorem negSpan_level (hI : Cited_VermaHomInjective)
    (hχ : IsSingular (pbwCoord (c := c) (h := h) ℓ x) ℓ) :
    (∀ M : ℕ, (negSpan (pbwCoord (c := c) (h := h) ℓ x)).comap (pbwCoord (ℓ + M)) =
        Submodule.span ℂ (Set.range (iotaCols c h ℓ M x)) ∧
      LinearIndependent ℂ (iotaCols c h ℓ M x)) ∧
    ∀ N : ℕ, N < ℓ → (negSpan (pbwCoord (c := c) (h := h) ℓ x)).comap (pbwCoord N) = ⊥ := by
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hχ.2.1 hχ.2.2
  have hj0 : j ≠ 0 := by
    intro h0
    apply hχ.1
    rw [← hjhw, h0]
    rfl
  have hjinj := hI c h (h + ℓ) j hjL hj0
  have hrange := negSpan_eq_range j hjneg
  have hdec : ∀ y, ∃ T : Finset ℕ, j y = ∑ M' ∈ T, pbwCoord (ℓ + M')
      (Fintype.linearCombination ℂ (iotaCols c h ℓ M' x) (Verma.comp M' y)) := by
    intro y
    obtain ⟨T, hT⟩ := exists_decomp y
    refine ⟨T, ?_⟩
    conv_lhs => rw [hT]
    rw [map_sum]
    exact Finset.sum_congr rfl fun M' _ => j_pbwCoord hjneg M' _
  refine ⟨fun M => ⟨?_, ?_⟩, fun N hN => ?_⟩
  · rw [← Fintype.range_linearCombination]
    ext v
    rw [Submodule.mem_comap, hrange]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨T, hT⟩ := hdec y
      have h1 := congrArg (Verma.comp (ℓ + M)) (hy.symm.trans hT)
      rw [comp_pbwCoord_same, map_sum] at h1
      by_cases hM : M ∈ T
      · have hz : ∀ M' ∈ T, M' ≠ M → Verma.comp (c := c) (h := h) (ℓ + M) (pbwCoord (ℓ + M')
            (Fintype.linearCombination ℂ (iotaCols c h ℓ M' x) (Verma.comp M' y))) = 0 :=
          fun M' _ hne => comp_pbwCoord_ne (by omega) _
        rw [Finset.sum_eq_single M hz (fun hn => absurd hM hn), comp_pbwCoord_same] at h1
        exact ⟨_, h1.symm⟩
      · have hz : ∀ M' ∈ T, Verma.comp (c := c) (h := h) (ℓ + M) (pbwCoord (ℓ + M')
            (Fintype.linearCombination ℂ (iotaCols c h ℓ M' x) (Verma.comp M' y))) = 0 := by
          intro M' hM'
          refine comp_pbwCoord_ne (fun he => hM ?_) _
          have : M' = M := by omega
          rwa [this] at hM'
        rw [Finset.sum_eq_zero hz] at h1
        exact ⟨0, by rw [map_zero, h1]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨pbwCoord M u, j_pbwCoord hjneg M u⟩
  · rw [linearIndependent_iff_injective_fintypeLinearCombination, injective_iff_map_eq_zero]
    intro u hu
    have h1 := j_pbwCoord hjneg M u
    rw [hu, map_zero] at h1
    have h2 := hjinj (h1.trans (map_zero j).symm)
    exact pbwCoord_injective M (h2.trans (map_zero _).symm)
  · rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_comap, hrange] at hv
    obtain ⟨y, hy⟩ := hv
    obtain ⟨T, hT⟩ := hdec y
    have h1 := congrArg (Verma.comp N) (hy.symm.trans hT)
    have hz : ∀ M' ∈ T, Verma.comp (c := c) (h := h) N (pbwCoord (ℓ + M')
        (Fintype.linearCombination ℂ (iotaCols c h ℓ M' x) (Verma.comp M' y))) = 0 :=
      fun M' _ => comp_pbwCoord_ne (by omega) _
    rw [comp_pbwCoord_same, map_sum, Finset.sum_eq_zero hz] at h1
    rw [Submodule.mem_bot]
    exact h1

end Level

set_option maxHeartbeats 1600000 in
/-- `Stmt_sub_tau_lattice` (paper.tex l.2910–2918). -/
theorem sub_tau_lattice_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hI : Cited_VermaHomInjective) :
    Stmt_sub_tau_lattice := by
  classical
  intro b hb R S hR hS χ hχ N
  obtain ⟨x₂, rfl⟩ := mem_level_of_L_zero hχ.2.1
  obtain ⟨pf, xLam, a, ha0, hp1, hsingQ, hxev, hxs, hx₂a⟩ := lam_setup hH hU hLau hb hR hS hχ
  have hneg : negSpan (pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x₂) =
      negSpan (pbwCoord (c := kacC b) (h := kacH R S b) (R * S)
        fun Y => evLam b hb (xLam Y)) := by
    rw [hx₂a, map_smul, negSpan_smul _ ha0]
  rw [hneg]
  have hlev := negSpan_level hI (hxs b hb)
  by_cases hN : N < R * S
  · refine ⟨_, Module.finBasis ℂ (Nat.Partition N → ℂ), ∅,
      (Module.finBasis ℂ (Nat.Partition N → ℂ)).linearIndependent, ?_, ?_⟩
    · rw [Basis.span_eq, hlev.2 N hN]
      exact isCompl_top_bot
    · intro b' hb' hirr _
      rw [Basis.span_eq, ← jantzenLayer_one, generic_layer_below hb' hirr hR hS hK hN le_rfl]
      exact isCompl_top_bot
  · obtain ⟨M, rfl⟩ : ∃ M, N = R * S + M := ⟨N - R * S, by omega⟩
    obtain ⟨hK1, hcolsLI⟩ := hlev.1 M
    rw [hK1]
    obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range
      (iotaCols (kacC b) (kacH R S b) (R * S) M fun Y => evLam b hb (xLam Y))))
    set E : Fin (finrank ℂ Cc) → (Nat.Partition (R * S + M) → ℂ) :=
      fun i => ((Module.finBasis ℂ Cc i : Cc) : Nat.Partition (R * S + M) → ℂ) with hEdef
    have hLI : LinearIndependent ℂ E :=
      (Module.finBasis ℂ Cc).linearIndependent.map' Cc.subtype (Submodule.ker_subtype Cc)
    have hspanE : Submodule.span ℂ (Set.range E) = Cc := by
      have h1 : Set.range E = Cc.subtype '' Set.range (Module.finBasis ℂ Cc) := by
        rw [← Set.range_comp]
        rfl
      rw [h1, Submodule.span_image, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hcompl : IsCompl (Submodule.span ℂ (Set.range E)) (Submodule.span ℂ (Set.range
        (iotaCols (kacC b) (kacH R S b) (R * S) M fun Y => evLam b hb (xLam Y)))) := by
      rw [hspanE]
      exact hCc.symm
    -- the completed family at each `b'`
    set Fb : ∀ (b' : ℂ), b' ≠ 0 → Fin (finrank ℂ Cc) ⊕ Nat.Partition M →
        (Nat.Partition (R * S + M) → ℂ) := fun b' hb' =>
      Sum.elim E (iotaCols (kacC b') (kacH R S b') (R * S) M fun Y => evLam b' hb' (xLam Y))
      with hFb
    have hF₀LI : LinearIndependent ℂ (Fb b hb) := hLI.sum_type hcolsLI hcompl.disjoint
    have hF₀span : Submodule.span ℂ (Set.range (Fb b hb)) = ⊤ := by
      rw [hFb, Set.Sum.elim_range, Submodule.span_union]
      exact hcompl.sup_eq_top
    have hcard : Fintype.card (Fin (finrank ℂ Cc) ⊕ Nat.Partition M) =
        Fintype.card (Nat.Partition (R * S + M)) := by
      have h1 := linearIndependent_iff_card_eq_finrank_span.1 hF₀LI
      rw [Set.finrank, hF₀span, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
      exact h1
    set e : Nat.Partition (R * S + M) ≃ Fin (finrank ℂ Cc) ⊕ Nat.Partition M :=
      (Fintype.equivOfCardEq hcard).symm with he
    -- the Laurent matrix
    set FΛ : Fin (finrank ℂ Cc) ⊕ Nat.Partition M → Nat.Partition (R * S + M) → Lam :=
      Sum.elim (fun i Y => algebraMap ℂ[X] Lam (C (E i Y)))
        (fun Z Y => Verma.comp (R * S + M) (VirEnv.negOp cLam Z.word •
          pbwCoord (c := cLam) (h := hLam R S) (R * S) xLam) Y) with hFΛ
    have hFev : ∀ (b' : ℂ) (hb' : b' ≠ 0) (k : Fin (finrank ℂ Cc) ⊕ Nat.Partition M)
        (Y : Nat.Partition (R * S + M)), evLam b' hb' (FΛ k Y) = Fb b' hb' k Y := by
      rintro b' hb' (i | Z) Y
      · simp only [hFΛ, hFb, Sum.elim_inl, evLam_algebraMap, eval_C]
      · simp only [hFΛ, hFb, Sum.elim_inr]
        show _ = iotaMat (kacC b') (kacH R S b') (R * S) M _ Y Z
        rw [iotaMat, Matrix.of_apply, ← comp_baseChange (evLam b' hb') (evLam_cLam hb')
          (evLam_hLam hb' R S), Verma.baseChange_negOp_smul, Verma.baseChange_pbwCoord]
    set AΛ : Matrix (Nat.Partition (R * S + M)) (Nat.Partition (R * S + M)) Lam :=
      Matrix.of fun Y Y' => FΛ (e Y) Y' with hAΛ
    have hdet : ∀ (b' : ℂ) (hb' : b' ≠ 0), evLam b' hb' AΛ.det =
        (Matrix.of fun Y Y' => Fb b' hb' (e Y) Y').det := by
      intro b' hb'
      rw [RingHom.map_det]
      congr 1
      ext Y Y'
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hAΛ, Matrix.of_apply, hFev]
    have hrowLI : ∀ (b' : ℂ) (hb' : b' ≠ 0),
        LinearIndependent ℂ (Fb b' hb') ↔
          (Matrix.of fun Y Y' => Fb b' hb' (e Y) Y').det ≠ 0 := by
      intro b' hb'
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
        ← Matrix.linearIndependent_rows_iff_isUnit]
      constructor
      · intro hli
        exact hli.comp e e.injective
      · intro hli
        have h1 := hli.comp e.symm e.symm.injective
        have h2 : (Matrix.of fun Y Y' => Fb b' hb' (e Y) Y').row ∘ e.symm = Fb b' hb' := by
          funext k
          show (fun Y' => Fb b' hb' (e (e.symm k)) Y') = Fb b' hb' k
          rw [Equiv.apply_symm_apply]
        rwa [h2] at h1
    have hdΛ : AΛ.det ≠ 0 := by
      intro h0
      have h1 := hdet b hb
      rw [h0, map_zero] at h1
      exact (hrowLI b hb).1 hF₀LI h1.symm
    refine ⟨_, E, (lam_zeros_finite hdΛ).toFinset, hLI, hcompl, ?_⟩
    intro b' hb' hirr hnot
    have hd : evLam b' hb' AΛ.det ≠ 0 := fun h0 =>
      hnot ((Set.Finite.mem_toFinset _).2 ⟨hb', h0⟩)
    rw [hdet] at hd
    have hLIb := (hrowLI b' hb').2 hd
    obtain ⟨-, -, hdisj⟩ := linearIndependent_sum.1 hLIb
    have hspan : Submodule.span ℂ (Set.range (Fb b' hb')) = ⊤ :=
      hLIb.span_eq_top_of_card_eq_finrank'
        (by rw [hcard, Module.finrank_fintype_fun_eq_card])
    rw [hFb, Set.Sum.elim_range, Submodule.span_union] at hspan
    have hβ := (thm_first_layer_ratio_of_cited hE hH hU hF b' hb' hirr R S 0 0 hR hS hR hS _
      (hxs b' hb')).2.1
    have hker : LinearMap.ker (gram (kacC b') (kacH R S b') (R * S + M)).mulVecLin =
        Submodule.span ℂ (Set.range
          (iotaCols (kacC b') (kacH R S b') (R * S) M fun Y => evLam b' hb' (xLam Y))) := by
      rw [← jantzenLayer_one, (generic_layer_above hb' hirr hR hS (hxs b' hb') hβ hK M).1,
        iota_mulVecLin_eq, Fintype.range_linearCombination]
    rw [hker]
    exact ⟨hdisj, codisjoint_iff.2 hspan⟩

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hI : Cited_VermaHomInjective) :
    Stmt_sub_tau_lattice := sub_tau_lattice_of_cited hK hE hH hU hF hLau hI

end Virasoro.P2
