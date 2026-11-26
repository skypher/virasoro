import Virasoro.Statements.Rev20261126
import Virasoro.Proofs.P2Sec12Cocycle
import Virasoro.Proofs.P2Sec9GenRC5
import Virasoro.Proofs.P2Sec13DiagMain

/-!
# Proofs of the statements of `irreducible/paper.tex` restated on 2026-11-26

`Ψ⋆` is `psiNode` at the node's momentum.  The arrow identity and the path products come from
`cArrow_psi`, `pathProd_psi` and `psiNode_ne_zero` (P2Sec12Cocycle.lean), which already follow the
paper's proof of Proposition 6.1(ii).  Every node is reached from `λ = (true, 0)` by a directed
path, so every BGG weight is a quotient of two nonzero path products.  Theorem 4.3 and Lemma 7.1
in the new form follow from their earlier forms, since `Omega` from `λ` and `cArrow` agree with
the BGG weights.
-/

namespace Virasoro

theorem psiStar_eq_psiNode (p p' r s k m : ℕ) (b : ℂ) (ε : Bool) (j : ℕ) :
    psiStar p p' r s k m b ε j = psiNode p' k m b (nOrb p p' r s ε j) := rfl

theorem nOrb_false_zero (p p' r s : ℕ) : nOrb p p' r s false 0 = -nOrb p p' r s true 0 := by
  simp [nOrb]

section Rev26

variable {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) {k m : ℕ}
  (hk : k < min r (p - r)) (hm : m < min s (p' - s))
include hset hk hm

theorem psiStar_ne_zero (ε : Bool) (j : ℕ) : psiStar p p' r s k m b ε j ≠ 0 :=
  psiNode_ne_zero hset hk hm ε j

theorem cArrow_eq_OmegaPsi (ε : Bool) (j : ℕ) (ε' : Bool) :
    ((cArrow p p' r s k m ε j ε' : ℚ) : ℂ) = OmegaPsi p p' r s k m b ε j ε' (j + 1) := by
  unfold OmegaPsi
  rw [eq_div_iff (psiStar_ne_zero hset hk hm ε j)]
  exact cArrow_psi hset hk hm ε j ε'

theorem pathProd_eq_OmegaPsi (l : List Bool) (ε : Bool) (j : ℕ) (e : Bool)
    (h : l.getLast? = some e) :
    ((pathProd p p' r s k m ε j l : ℚ) : ℂ) = OmegaPsi p p' r s k m b ε j e (j + l.length) := by
  unfold OmegaPsi
  rw [eq_div_iff (psiStar_ne_zero hset hk hm ε j)]
  exact pathProd_psi hset hk hm l ε j e h

theorem OmegaPsi_lam_zero (ε : Bool) : OmegaPsi p p' r s k m b true 0 ε 0 = 1 := by
  have h0 := psiStar_ne_zero hset hk hm true 0
  have he : psiStar p p' r s k m b ε 0 = psiStar p p' r s k m b true 0 := by
    cases ε
    · rw [psiStar_eq_psiNode, psiStar_eq_psiNode, nOrb_false_zero, psiNode_neg]
    · rfl
  unfold OmegaPsi
  rw [he, div_self h0]

theorem OmegaPsi_lam_succ (ε : Bool) (n : ℕ) :
    ((pathProd p p' r s k m true 0 (List.replicate n true ++ [ε]) : ℚ) : ℂ) =
      OmegaPsi p p' r s k m b true 0 ε (n + 1) := by
  have h := pathProd_eq_OmegaPsi hset hk hm (List.replicate n true ++ [ε]) true 0 ε (by simp)
  have hl : 0 + (List.replicate n true ++ [ε]).length = n + 1 := by simp
  rwa [hl] at h

/-- Every node is reached from `λ` with a nonzero rational weight. -/
theorem exists_rat_from_lam (ε : Bool) (j : ℕ) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = OmegaPsi p p' r s k m b true 0 ε j := by
  cases j with
  | zero => exact ⟨1, one_ne_zero, by rw [OmegaPsi_lam_zero hset hk hm]; simp⟩
  | succ n =>
    refine ⟨pathProd p p' r s k m true 0 (List.replicate n true ++ [ε]), fun hq => ?_,
      OmegaPsi_lam_succ hset hk hm ε n⟩
    have h := OmegaPsi_lam_succ hset hk hm ε n
    rw [hq, Rat.cast_zero] at h
    unfold OmegaPsi at h
    exact div_ne_zero (psiStar_ne_zero hset hk hm ε (n + 1))
      (psiStar_ne_zero hset hk hm true 0) h.symm

theorem OmegaPsi_rat (ε : Bool) (j : ℕ) (ε' : Bool) (j' : ℕ) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = OmegaPsi p p' r s k m b ε j ε' j' := by
  obtain ⟨q1, hq1, h1⟩ := exists_rat_from_lam hset hk hm ε j
  obtain ⟨q2, hq2, h2⟩ := exists_rat_from_lam hset hk hm ε' j'
  refine ⟨q2 / q1, div_ne_zero hq2 hq1, ?_⟩
  have h0 := psiStar_ne_zero hset hk hm true 0
  have ha := psiStar_ne_zero hset hk hm ε j
  have hb' := psiStar_ne_zero hset hk hm ε' j'
  rw [Rat.cast_div, h1, h2]
  unfold OmegaPsi
  field_simp

theorem Omega_eq_OmegaPsi (ε : Bool) (j : ℕ) :
    ((Omega p p' r s k m true 0 ε j : ℚ) : ℂ) = OmegaPsi p p' r s k m b true 0 ε j := by
  cases j with
  | zero => simp [Omega, OmegaPsi_lam_zero hset hk hm]
  | succ n =>
    have h := OmegaPsi_lam_succ hset hk hm ε n
    simpa [Omega] using h

end Rev26

/-- Proposition 6.1 in its current form.

Paper label: prop:bgg-cocycle -/
theorem prop_bgg_cocycle_rev26 : Stmt_prop_bgg_cocycle_rev26 := by
  intro p p' r s b hset k m hk hm
  exact ⟨(prop_bgg_cocycle p p' r s b hset k m hk hm).1, psiStar_ne_zero hset hk hm,
    cArrow_eq_OmegaPsi hset hk hm, fun l ε j e h => pathProd_eq_OmegaPsi hset hk hm l ε j e h,
    OmegaPsi_rat hset hk hm⟩

/-- Theorem 4.3 in its current form, from the form with `Omega`. -/
theorem thm_gen_rocha_caridi_rev26_of (h : Stmt_thm_gen_rocha_caridi) :
    Stmt_thm_gen_rocha_caridi_rev26 := by
  intro p p' r s b hset k m hk hm
  have key : ∀ (ε : Bool) (j : ℕ),
      OmegaPsi p p' r s k m b true 0 ε j = ((Omega p p' r s k m true 0 ε j : ℚ) : ℂ) :=
    fun ε j => (Omega_eq_OmegaPsi hset hk hm ε j).symm
  have h0 := h p p' r s b hset k m hk hm
  dsimp only at h0 ⊢
  simp only [key]
  obtain ⟨h1, h2, h3, h4, h5⟩ := h0
  refine ⟨h1, h2, fun hk0 hm0 => ?_, h4, h5⟩
  obtain ⟨hd, hO, hF⟩ := h3 hk0 hm0
  exact ⟨hd, fun ε j => by rw [hO ε j, Rat.cast_one], hF⟩

/-- Theorem 4.3, from the cited results.

Paper label: thm:gen-rocha-caridi -/
theorem thm_gen_rocha_caridi_rev26_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_thm_gen_rocha_caridi_rev26 :=
  thm_gen_rocha_caridi_rev26_of (P2.thm_gen_rocha_caridi_of_cited hK hE hH hU hF hLau hJ hI)

/-- Lemma 7.1 in its current form, from the form with `cArrow`. -/
theorem lem_degenerate_quotient_t_rev26_of (h : Stmt_lem_degenerate_quotient_t) :
    Stmt_lem_degenerate_quotient_t_rev26 := by
  intro p p' r s b hset k m hk hm ε k₀ ε₁ N
  have h0 := h p p' r s b hset k m hk hm ε k₀ ε₁ N
  dsimp only at h0 ⊢
  rw [← cArrow_eq_OmegaPsi hset hk hm, ← cArrow_eq_OmegaPsi hset hk hm]
  exact h0

/-- Lemma 7.1, from the cited results.

Paper label: lem:degenerate-quotient-t -/
theorem lem_degenerate_quotient_t_rev26_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_lem_degenerate_quotient_t_rev26 :=
  lem_degenerate_quotient_t_rev26_of
    (P2.lem_degenerate_quotient_t_of_cited hK hE hH hU hF hLau hJ hI)

end Virasoro
