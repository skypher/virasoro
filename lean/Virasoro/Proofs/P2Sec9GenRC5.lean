import Virasoro.Proofs.P2Sec9GenRC4
import Virasoro.Proofs.P2Sec11LayerBasis

/-!
# Theorem 9.3 (paper.tex l.1926–1960, proof l.3040–3105)
-/

namespace Virasoro.P2

open Virasoro Verma

/-- Part (c) at the node `μ⁺_0 = λ` for a family `w^±_j` of Lemma 10.3(i) (l.3089–3105). -/
theorem c_core (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k m : ℕ} (hk : k < min r (p - r)) (hm : m < min s (p' - s))
    (wp wm : ℕ → Verma ℂ (kacC b) (muOrb p p' r s true 0))
    (hOL : OrbitLayerSetting p p' r s b true 0 wp wm)
    (xp : (i : ℕ) → Nat.Partition (ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0) → ℂ)
    (xm : (i : ℕ) → Nat.Partition (ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0) → ℂ)
    (hx : ∀ i, 1 ≤ i → pbwCoord _ (xp i) = wp i ∧ pbwCoord _ (xm i) = wm i)
    (j : ℕ) (hj : 1 ≤ j) :
    vform (kacC b) (muOrb p p' r s true 0) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) _ j
        (xp j) (xp j) =
      (Omega p p' r s k m true 0 true j : ℂ) *
        jform (kacC b) (muOrb p p' r s true 0) _ j (xp j) (xp j) ∧
    vform (kacC b) (muOrb p p' r s true 0) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) _ j
        (xm j) (xm j) =
      (Omega p p' r s k m true 0 false j : ℂ) *
        jform (kacC b) (muOrb p p' r s true 0) _ j (xm j) (xm j) := by
  classical
  have h131 := lem_degenerate_quotient_t_of_cited hK hE hH hU hF hLau hJ hI
  have hd := orbit_descends hJ hH hU hF hset hk hm
  choose tv htv using fun ε j M => (irrTrace_existsUnique (hd ε j) M).exists
  obtain ⟨-, h112⟩ := prop_jantzen_vertex_of_cited hJ hH hU hF hI p p' r s b hset true 0 k m hk hm
  obtain ⟨hγ, hdec⟩ := h112 wp wm hOL xp xm hx
  set ρp : ℕ → ℂ := fun i =>
    vform (kacC b) (muOrb p p' r s true 0) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) _ i
        (xp i) (xp i) / jform (kacC b) (muOrb p p' r s true 0) _ i (xp i) (xp i) with hρp
  set ρm : ℕ → ℂ := fun i =>
    vform (kacC b) (muOrb p p' r s true 0) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) _ i
        (xm i) (xm i) / jform (kacC b) (muOrb p p' r s true 0) _ i (xm i) (xm i) with hρm
  set ρ : Bool → ℕ → ℂ := fun ε i => if ε then ρp i else ρm i with hρ
  have hz : ∀ (ε : Bool) (i : ℕ), ellOrb p p' r s ε (0 + i) - ellOrb p p' r s true 0 =
      ellOrb p p' r s ε i := fun ε i => by simp [ellOrb_zero']
  -- the comparison at each level
  have hdiff : ∀ N : ℕ, ∑ i ∈ Finset.Icc 1 N,
      ((if ellOrb p p' r s true i ≤ N then
          (ρ true i - (Omega p p' r s k m true 0 true i : ℂ)) *
            tv true i (N - ellOrb p p' r s true i) else 0) +
        (if ellOrb p p' r s false i ≤ N then
          (ρ false i - (Omega p p' r s k m true 0 false i : ℂ)) *
            tv false i (N - ellOrb p p' r s false i) else 0)) = 0 := by
    intro N
    have hN : FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N
        (muOrb p p' r s true 0) = tv true 0 N + ∑ i ∈ Finset.Icc 1 N,
          ((if ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0 ≤ N then
              ρp i * tv true (0 + i) (N - (ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0))
            else 0) +
           (if ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0 ≤ N then
              ρm i * tv false (0 + i) (N - (ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0))
            else 0)) :=
      ((hdec N).2 (tv true 0 N)
        (fun i => tv true (0 + i) (N - (ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0)))
        (fun i => tv false (0 + i) (N - (ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0)))
        (htv _ _ _) (fun i _ _ => htv _ _ _) (fun i _ _ => htv _ _ _))
    simp only [hz, zero_add, ellOrb_zero', Nat.sub_zero] at hN
    have hinv := inv_formula h131 hset hk hm N tv htv N le_rfl true (Or.inr rfl)
    rw [Nat.sub_self] at hinv
    have hF0 : Fsh p p' r s k m b N true 0 = FvalAt (kacC b)
        (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N (muOrb p p' r s true 0) := by
      simp [Fsh, ellOrb_zero', Omega]
    have hT0 : Tsh p p' r s k m N tv true 0 = tv true 0 N := by
      simp [Tsh, ellOrb_zero', Omega]
    have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hF0, hT0, hIoc, hN, add_right_inj] at hinv
    have hsplit : (∑ i ∈ Finset.Icc 1 N,
        ((if ellOrb p p' r s true i ≤ N then
            (ρ true i - (Omega p p' r s k m true 0 true i : ℂ)) *
              tv true i (N - ellOrb p p' r s true i) else 0) +
          (if ellOrb p p' r s false i ≤ N then
            (ρ false i - (Omega p p' r s k m true 0 false i : ℂ)) *
              tv false i (N - ellOrb p p' r s false i) else 0))) =
        (∑ i ∈ Finset.Icc 1 N,
          ((if ellOrb p p' r s true i ≤ N then ρp i * tv true i (N - ellOrb p p' r s true i)
              else 0) +
            (if ellOrb p p' r s false i ≤ N then ρm i * tv false i (N - ellOrb p p' r s false i)
              else 0))) -
        ∑ i ∈ Finset.Icc 1 N,
          (Tsh p p' r s k m N tv true i + Tsh p p' r s k m N tv false i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold Tsh
      simp only [hρ, if_true, Bool.false_eq_true, if_false]
      split_ifs <;> ring
    rw [hsplit, hinv, sub_self]
  -- strong induction on the level
  have hval : ∀ n : ℕ, ∀ (ε : Bool) (i : ℕ), 1 ≤ i → ellOrb p p' r s ε i = n →
      ρ ε i = (Omega p p' r s k m true 0 ε i : ℂ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ε₀ i₀ hi₀ hn
      have hge := ellOrb_ge (by omega : 0 < p) (by omega : 0 < p') hset.2.2.2.1 hset.2.2.2.2.1
        hset.2.2.2.2.2.1 hset.2.2.2.2.2.2.1 i₀ ε₀
      have hD : ∀ (ε : Bool) (i : ℕ), 1 ≤ i → (ε, i) ≠ (ε₀, i₀) →
          (if ellOrb p p' r s ε i ≤ n then
            (ρ ε i - (Omega p p' r s k m true 0 ε i : ℂ)) * tv ε i (n - ellOrb p p' r s ε i)
          else 0) = 0 := by
        intro ε i hi hne
        split_ifs with hle
        · rcases lt_or_eq_of_le hle with hlt | heq
          · rw [ih _ hlt ε i hi rfl, sub_self, zero_mul]
          · exfalso
            obtain ⟨h1, h2⟩ := ellOrb_inj hset hi hi₀ (heq.trans hn.symm)
            exact hne (by rw [h1, h2])
        · rfl
      have hsum := hdiff n
      rw [Finset.sum_eq_single i₀] at hsum
      · have h1 : tv ε₀ i₀ (n - ellOrb p p' r s ε₀ i₀) = 1 := by
          rw [hn, Nat.sub_self]
          exact irrTrace_zero_orbit h131 hset hk hm ε₀ i₀ (htv ε₀ i₀ 0)
        cases ε₀
        · rw [hD true i₀ hi₀ (by simp), zero_add, if_pos hn.le, h1, mul_one, sub_eq_zero] at hsum
          exact hsum
        · rw [hD false i₀ hi₀ (by simp), add_zero, if_pos hn.le, h1, mul_one, sub_eq_zero] at hsum
          exact hsum
      · intro i hi hne
        have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
        rw [hD true i hi1 (by simp [hne]), hD false i hi1 (by simp [hne]), add_zero]
      · intro h
        exact absurd (Finset.mem_Icc.2 ⟨hi₀, by omega⟩) h
  have hp := hval _ true j hj rfl
  have hm' := hval _ false j hj rfl
  simp only [hρ, if_true, Bool.false_eq_true, if_false, hρp, hρm] at hp hm'
  obtain ⟨hγp, hγm⟩ := hγ j hj
  rw [div_eq_iff hγp] at hp
  rw [div_eq_iff hγm] at hm'
  exact ⟨hp, hm'⟩

/-- Part (c) of Theorem 9.3 for a family of Theorem 5.8 at `λ` (l.1954–1959). -/
theorem gen_rc_c (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k m : ℕ} (hk : k < min r (p - r)) (hm : m < min s (p' - s)) :
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ j : ℕ, 1 ≤ j →
        (∀ xp : Nat.Partition (ellPlus p p' r s j) → ℂ,
          Verma.pbwCoord (ellPlus p p' r s j) xp = wp j →
            vform (kacC b) (kacH r s b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                (ellPlus p p' r s j) j xp xp =
              (Omega p p' r s k m true 0 true j : ℂ) *
                jform (kacC b) (kacH r s b) (ellPlus p p' r s j) j xp xp) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s j) → ℂ,
          Verma.pbwCoord (ellMinus p p' r s j) xm = wm j →
            vform (kacC b) (kacH r s b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                (ellMinus p p' r s j) j xm xm =
              (Omega p p' r s k m true 0 false j : ℂ) *
                jform (kacC b) (kacH r s b) (ellMinus p p' r s j) j xm xm) := by
  unfold TopLayerSetting
  suffices H : ∀ μ : ℂ, muOrb p p' r s true 0 = μ → ∀ wp wm : ℕ → Verma ℂ (kacC b) μ,
      ((∀ k : ℕ, 1 ≤ k → IsSingular (wp k) (ellPlus p p' r s k) ∧
          IsSingular (wm k) (ellMinus p p' r s k)) ∧
        ∀ i : ℕ, 1 ≤ i → jantzen (kacC b) μ i = negSpan (wp i) ⊔ negSpan (wm i)) →
      ∀ j : ℕ, 1 ≤ j →
        (∀ xp : Nat.Partition (ellPlus p p' r s j) → ℂ, pbwCoord (ellPlus p p' r s j) xp = wp j →
            vform (kacC b) μ (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                (ellPlus p p' r s j) j xp xp =
              (Omega p p' r s k m true 0 true j : ℂ) * jform (kacC b) μ (ellPlus p p' r s j) j xp xp) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s j) → ℂ, pbwCoord (ellMinus p p' r s j) xm = wm j →
            vform (kacC b) μ (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                (ellMinus p p' r s j) j xm xm =
              (Omega p p' r s k m true 0 false j : ℂ) * jform (kacC b) μ (ellMinus p p' r s j) j xm xm) by
    exact H _ (muOrb_true_zero hset)
  intro μ hμ
  subst hμ
  intro wp wm ⟨hsing, hjan⟩ j hj
  have hlp : ∀ i, 1 ≤ i → ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0 = ellPlus p p' r s i :=
    fun i hi => by simp [ellOrb, Nat.pos_iff_ne_zero.1 hi]
  have hlm : ∀ i, 1 ≤ i → ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0 =
      ellMinus p p' r s i := fun i hi => by simp [ellOrb, Nat.pos_iff_ne_zero.1 hi]
  have hOL : OrbitLayerSetting p p' r s b true 0 wp wm := by
    refine ⟨fun i hi => ?_, hjan⟩
    rw [hlp i hi, hlm i hi]
    exact hsing i hi
  have hsp : ∀ i, 1 ≤ i → IsSingular (wp i) (ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0) :=
    fun i hi => (hOL.1 i hi).1
  have hsm : ∀ i, 1 ≤ i → IsSingular (wm i) (ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0) :=
    fun i hi => (hOL.1 i hi).2
  set xpf : (i : ℕ) → Nat.Partition (ellOrb p p' r s true (0 + i) - ellOrb p p' r s true 0) → ℂ :=
    fun i => Verma.comp _ (wp i) with hxpf
  set xmf : (i : ℕ) → Nat.Partition (ellOrb p p' r s false (0 + i) - ellOrb p p' r s true 0) → ℂ :=
    fun i => Verma.comp _ (wm i) with hxmf
  have hx : ∀ i, 1 ≤ i → pbwCoord _ (xpf i) = wp i ∧ pbwCoord _ (xmf i) = wm i := fun i hi =>
    ⟨pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsp i hi).2.1),
      pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsm i hi).2.1)⟩
  obtain ⟨hcp, hcm⟩ := c_core hK hE hH hU hF hLau hJ hI hset hk hm wp wm hOL xpf xmf hx j hj
  have keyp : ∀ L : ℕ, ellOrb p p' r s true (0 + j) - ellOrb p p' r s true 0 = L →
      vform (kacC b) (muOrb p p' r s true 0) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) L j
          (Verma.comp L (wp j)) (Verma.comp L (wp j)) =
        (Omega p p' r s k m true 0 true j : ℂ) *
          jform (kacC b) (muOrb p p' r s true 0) L j (Verma.comp L (wp j)) (Verma.comp L (wp j)) := by
    intro L hL
    subst hL
    exact hcp
  have keym : ∀ L : ℕ, ellOrb p p' r s false (0 + j) - ellOrb p p' r s true 0 = L →
      vform (kacC b) (muOrb p p' r s true 0) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) L j
          (Verma.comp L (wm j)) (Verma.comp L (wm j)) =
        (Omega p p' r s k m true 0 false j : ℂ) *
          jform (kacC b) (muOrb p p' r s true 0) L j (Verma.comp L (wm j)) (Verma.comp L (wm j)) := by
    intro L hL
    subst hL
    exact hcm
  refine ⟨fun xp hxp => ?_, fun xm hxm => ?_⟩
  · have e : xp = Verma.comp _ (wp j) := by rw [← hxp, comp_pbwCoord_same]
    rw [e]
    exact keyp _ (hlp j hj)
  · have e : xm = Verma.comp _ (wm j) := by rw [← hxm, comp_pbwCoord_same]
    rw [e]
    exact keym _ (hlm j hj)

/-- Theorem 9.3 (paper.tex l.1926–1960, proof l.3040–3105).
Paper label: thm:gen-rocha-caridi -/
theorem thm_gen_rocha_caridi_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_thm_gen_rocha_caridi := by
  intro p p' r s b hset k m hk hm
  have hb := minimalSetting_b_ne_zero hset
  refine ⟨fun N => gen_rc_main hK hE hH hU hF hLau hJ hI hset hk hm N,
    fun ε j M => gen_rc_regular hK hH hU hF hJ hI hset hk hm ε j M, fun hk0 hm0 => ?_,
    fun N T hT => gen_rc_b hK hE hH hU hF hLau hJ hI hset hk hm N T hT,
    gen_rc_c hK hE hH hU hF hLau hJ hI hset hk hm⟩
  subst hk0 hm0
  exact gen_rc_a b hb

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) : Stmt_thm_gen_rocha_caridi :=
  thm_gen_rocha_caridi_of_cited hK hE hH hU hF hLau hJ hI

end Virasoro.P2
