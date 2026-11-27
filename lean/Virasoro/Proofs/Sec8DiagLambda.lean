import Virasoro.Proofs.Sec8DiagThm
import Virasoro.Proofs.Sec5TopLayerFinal
import Virasoro.Proofs.Sec6TTFrame
import Virasoro.Proofs.LevelComp
import Virasoro.Proofs.PBWBasis
import Virasoro.Proofs.Sec7Generic

/-!
# Corollary 8.9 (`cor:diagonal-lambda`), first part: `Top(λ → μ^±_L) = 𝒩^±_L/γ^±_L`

In (7.8) at `λ` with `k = L` and `ℓ^±_L ≤ N < ℓ_{L+1}`, the chain values with `L_μ < L`, or with
`L_μ = L` and `j ≥ 1`, vanish at `b⋆` (Lemma 8.5(i)); no node of layer larger than `L` has level at
most `N`; and `H_{N-ℓ^±_L}(c⋆,·)` is regular at `μ^±_L`.  Comparing with (8.1) at
`N = min(ℓ^+_L, ℓ^-_L)` and then at `N = max(ℓ^+_L, ℓ^-_L)` gives `Top(λ → μ^±_L) = 𝒩^±_L/γ^±_L`.
-/

namespace Virasoro

open scoped LaurentSeries Polynomial

variable {p p' r s : ℕ} {b : ℂ}

section Base

variable (hset : MinimalSetting p p' r s b)
include hset

theorem nodeWt_base : nodeWt p p' r s (true, 0) = kacH r s b := by
  have hb := hset.2.2.2.2.2.2.2.2
  unfold nodeWt
  rw [kacH_momWt (by have := hset.1; omega) (by have := hset.2.1; omega) hb, muOrb]
  congr 1
  simp [nOrb]

theorem nodeLev_ge_next {ν : Node} {L : ℕ} (h : L + 1 ≤ ν.2) :
    nodeLev p p' r s (ν.1, L + 1) ≤ nodeLev p p' r s ν := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact (nodeLev_lt_of_lt hset (show (ν.1, L + 1).2 < ν.2 from h')).le
  · have : ν = (ν.1, L + 1) := Prod.ext rfl h'.symm
    rw [← this]

/-- The chain values from `λ` to a point of level `n` below the layer `L + 1` vanish at `b⋆`,
unless the point is a node of layer `L` and `j = 0`. -/
theorem cval_zero {L n j : ℕ} (hL : 1 ≤ L) (hn : ∀ σ' : Bool, n < nodeLev p p' r s (σ', L + 1))
    (hno : ∀ σ : Bool, nodeLev p p' r s (σ, L) = n → 1 ≤ j) :
    (chainFnC b (nodeWt p p' r s (true, 0)) n L j).coeff 0 = 0 := by
  by_cases hnode : ∃ ν : Node, 0 < ν.2 ∧ nodeLev p p' r s ν = n
  · obtain ⟨ν, h0, hν⟩ := hnode
    have hνL : ν.2 ≤ L := by
      by_contra hc
      have := nodeLev_ge_next hset (ν := ν) (L := L) (by omega)
      have := hn ν.1
      omega
    have hlt : ν.2 - (true, 0).2 < L + j := by
      show ν.2 - 0 < L + j
      rcases lt_or_eq_of_le hνL with h | h
      · omega
      · have hj := hno ν.1 (by rw [← hν]; congr 1; exact Prod.ext rfl h.symm)
        omega
    have hz := nodeChain_coeff_zero hset (a := (true, 0)) (μ := ν) h0 L j hL hlt
    unfold nodeChain at hz
    rwa [nodeLev_zero, Nat.sub_zero, hν] at hz
  · push_neg at hnode
    rw [chainFn_dead hset (true, 0) n L j (fun μ hμ => by rw [nodeLev_zero, zero_add]; exact hnode μ hμ),
      HahnSeries.coeff_zero]

theorem nodeLev_ne_sign {L : ℕ} (hL : 1 ≤ L) :
    nodeLev p p' r s (true, L) ≠ nodeLev p p' r s (false, L) := by
  intro h
  have := node_eq_of_lev hset (show 1 ≤ (true, L).2 from hL) (show 1 ≤ (false, L).2 from hL) h
  simp at this

/-- The right side of (7.8) at `λ`, `k = L`, below the layer `L + 1`. -/
theorem fc_rhs_eval {L N J : ℕ} (hL : 1 ≤ L) (hJ : 1 ≤ J)
    (hN : ∀ σ' : Bool, N < nodeLev p p' r s (σ', L + 1)) :
    fixedChargeRHS b N (nodeWt p p' r s (true, 0)) L J =
      ∑ σ : Bool, ((if nodeLev p p' r s (σ, L) = N then nodeTop p p' r s b (true, 0) (σ, L) else 0) +
        (if nodeLev p p' r s (σ, L) < N then nodeTop p p' r s b (true, 0) (σ, L) *
          lcoeff (HN (kacC b) (N - nodeLev p p' r s (σ, L))) (pt (nodeWt p p' r s (σ, L))) 0
        else 0)) := by
  have hne := nodeLev_ne_sign hset hL
  have htop : ∀ σ : Bool, nodeTop p p' r s b (true, 0) (σ, L) =
      (chainFnC b (nodeWt p p' r s (true, 0)) (nodeLev p p' r s (σ, L)) L 0).coeff 0 := by
    intro σ
    simp only [nodeTop, nodeChain, nodeLev_zero, Nat.sub_zero]
  unfold fixedChargeRHS
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_bool]
    by_cases h1 : nodeLev p p' r s (true, L) = N
    · rw [if_pos h1, if_neg (fun h => hne (h1.trans h.symm)), add_zero, htop, h1]
    · by_cases h2 : nodeLev p p' r s (false, L) = N
      · rw [if_neg h1, if_pos h2, zero_add, htop, h2]
      · rw [if_neg h1, if_neg h2, add_zero]
        exact cval_zero hset hL hN (fun σ hσ => by cases σ <;> simp_all)
  · have hF : ∀ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
        (chainFnC b (nodeWt p p' r s (true, 0)) n L j).coeff 0 *
          ((j.factorial : Kd) * lcoeff (HN (kacC b) (N - n)) (pt (nodeWt p p' r s (true, 0) + n)) j) =
        ∑ σ : Bool, (if n = nodeLev p p' r s (σ, L) then nodeTop p p' r s b (true, 0) (σ, L) *
          lcoeff (HN (kacC b) (N - nodeLev p p' r s (σ, L))) (pt (nodeWt p p' r s (σ, L))) 0
          else 0) := by
      intro n hn
      rw [Finset.mem_Ioo] at hn
      by_cases hex : ∃ σ : Bool, nodeLev p p' r s (σ, L) = n
      · obtain ⟨σ, hσ⟩ := hex
        subst hσ
        rw [Fintype.sum_bool, Finset.sum_eq_single 0]
        · rw [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero,
            ← nodeWt_add_lev hset (σ, L), ← htop]
          cases σ
          · rw [if_neg (fun e => hne e.symm), if_pos rfl, zero_add]
          · rw [if_pos rfl, if_neg hne, add_zero]
        · intro j _ hj0
          rw [cval_zero hset hL (fun σ' => (hn.2.trans (hN σ'))) (fun _ _ => by omega), zero_mul]
        · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
      · push_neg at hex
        rw [Fintype.sum_bool, if_neg (fun h => hex true h.symm), if_neg (fun h => hex false h.symm),
          add_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [cval_zero hset hL (fun σ' => (hn.2.trans (hN σ'))) (fun σ hσ => absurd hσ (hex σ)),
          zero_mul]
    rw [Finset.sum_congr rfl hF, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq' (Finset.Ioo 0 N) (nodeLev p p' r s (σ, L))]
    have hpos : 0 < nodeLev p p' r s (σ, L) := by
      have := nodeLev_lt_of_lt hset (ν := (true, 0)) (ν' := (σ, L)) (show 0 < L by omega)
      rwa [nodeLev_zero] at this
    simp only [Finset.mem_Ioo, hpos, true_and]

/-- `H_M(c⋆,·)` is regular at the node `μ = (σ, L)` when no node of layer `L + 1` has level at most
`ℓ_μ + M`: the coefficient of `(Δ - μ)⁰` is the value. -/
theorem reg_lcoeff (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {σ : Bool} {L M : ℕ}
    (hM1 : 1 ≤ M) (hM : ∀ σ' : Bool, nodeLev p p' r s (σ, L) + M < nodeLev p p' r s (σ', L + 1)) :
    lcoeff (HN (kacC b) M) (pt (nodeWt p p' r s (σ, L))) 0 =
      evalAt (pt (nodeWt p p' r s (σ, L))) (HN (kacC b) M) := by
  have hb0 := b_ne_zero_of hset
  have hpf := ((thm_fixed_charge_of_cited hK hH) b hb0 M hM1).2.1
  have hz : ∀ lam' ∈ Lam M b, pt (nodeWt p p' r s (σ, L)) ≠ pt lam' := by
    intro lam' hlam' heq
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hlam'
    rw [mem_labels_iff] at hg
    have h1 := RatFunc.C_injective heq
    obtain ⟨ν', hlt, -, hw'⟩ := node_labels_iii hset (σ, L) g (by omega) (by omega) h1.symm
    have e1 := nodeWt_add_lev hset ν'
    have e2 := nodeWt_add_lev hset (σ, L)
    have hc : (nodeLev p p' r s ν' : ℂ) = nodeLev p p' r s (σ, L) + g.lvl := by
      linear_combination -e1 + e2 - hw' - h1
    have hnat : nodeLev p p' r s ν' = nodeLev p p' r s (σ, L) + g.lvl := by exact_mod_cast hc
    have hge := nodeLev_ge_next hset (ν := ν') (L := L) (by simp only at hlt; omega)
    have := hM ν'.1
    omega
  rw [hpf]
  unfold PP
  exact (evalAt_eq_lcoeff_zero (Lam M b) (fun lam' => pt lam')
    (fun lam' => poleOrder (HN (kacC b) M) (pt lam'))
    (fun lam' k => ppCoeff (HN (kacC b) M) (pt lam') k) hz).symm

theorem lam_mem {ε : Bool} {N : ℕ} (hN : nodeLev p p' r s (ε, 1) ≤ N) : kacH r s b ∈ Lam N b := by
  obtain ⟨hiff, h1, h2, -⟩ := node_labels_ii hset (true, 0) (ε, 1) (by show 0 < 1; omega)
    (by show (1 - 0) % 2 = 1; omega)
  obtain ⟨hw, -⟩ := (hiff _ h1 h2).2 rfl
  have hl := lvl_nodeLabel hset (ν := (true, 0)) (θ := (ε, 1)) (by show 0 < 1; omega)
    (by show (1 - 0) % 2 = 1; omega)
  rw [nodeLev_zero, add_zero] at hl
  refine Finset.mem_image.2 ⟨nodeLabel p p' r s (true, 0) (ε, 1),
    mem_labels_iff.2 ⟨h1, h2, by omega⟩, ?_⟩
  rw [hw, nodeWt_base hset]

end Base

/-- `Top(λ → μ^±_L) = 𝒩^±_L/γ^±_L`. -/
theorem top_lambda (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hI : Cited_VermaHomInjective) (hset : MinimalSetting p p' r s b)
    (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)) (htl : TopLayerSetting p p' r s b wp wm)
    {L : ℕ} (hL : 1 ≤ L) (xp : Nat.Partition (ellPlus p p' r s L) → ℂ)
    (xm : Nat.Partition (ellMinus p p' r s L) → ℂ)
    (hxp : Verma.pbwCoord (ellPlus p p' r s L) xp = wp L)
    (hxm : Verma.pbwCoord (ellMinus p p' r s L) xm = wm L) :
    nodeTop p p' r s b (true, 0) (true, L) =
        algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) xp) *
          RatFunc.C (jform (kacC b) (kacH r s b) (ellPlus p p' r s L) L xp xp)⁻¹ ∧
      nodeTop p p' r s b (true, 0) (false, L) =
        algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) xm) *
          RatFunc.C (jform (kacC b) (kacH r s b) (ellMinus p p' r s L) L xm xm)⁻¹ := by
  have hb0 := b_ne_zero_of hset
  have hlam := nodeWt_base hset
  have hlp : nodeLev p p' r s (true, L) = ellPlus p p' r s L := TT.ellOrb_true hL
  have hlm : nodeLev p p' r s (false, L) = ellMinus p p' r s L := TT.ellOrb_false hL
  have hlp1 : nodeLev p p' r s (true, L + 1) = ellPlus p p' r s (L + 1) := TT.ellOrb_true (by omega)
  have hlm1 : nodeLev p p' r s (false, L + 1) = ellMinus p p' r s (L + 1) := TT.ellOrb_false (by omega)
  have hne := nodeLev_ne_sign hset hL
  have hnext : ∀ σ σ' : Bool, nodeLev p p' r s (σ, L) < nodeLev p p' r s (σ', L + 1) :=
    fun σ σ' => nodeLev_lt_of_lt hset (show (σ, L).2 < (σ', L + 1).2 from by simp)
  have hone : ∀ σ : Bool, nodeLev p p' r s (σ, 1) ≤ nodeLev p p' r s (σ, L) := by
    intro σ
    rcases lt_or_eq_of_le hL with h | h
    · exact (nodeLev_lt_of_lt hset (show (σ, 1).2 < (σ, L).2 from h)).le
    · rw [← h]
  -- the identity of (7.8) and (8.1) at a level `N` of a node of layer `L`
  have key : ∀ σ : Bool, ∀ N : ℕ, N = nodeLev p p' r s (σ, L) →
      ∑ σ' : Bool, ((if nodeLev p p' r s (σ', L) = N then nodeTop p p' r s b (true, 0) (σ', L) else 0) +
        (if nodeLev p p' r s (σ', L) < N then nodeTop p p' r s b (true, 0) (σ', L) *
          lcoeff (HN (kacC b) (N - nodeLev p p' r s (σ', L))) (pt (nodeWt p p' r s (σ', L))) 0
        else 0)) =
      topTerm (kacC b) (kacH r s b) N (ellPlus p p' r s L) L xp +
        topTerm (kacC b) (kacH r s b) N (ellMinus p p' r s L) L xm := by
    intro σ N hN
    have hN1 : 1 ≤ N := by
      have := nodeLev_lt_of_lt hset (ν := (true, 0)) (ν' := (σ, L)) (show 0 < L by omega)
      rw [nodeLev_zero] at this; omega
    have hfc := (thm_fixed_charge_of_cited hK hH) b hb0 N hN1
    obtain ⟨J₀, hJ₀⟩ := (hfc.1 (kacH r s b) (lam_mem hset ((hone σ).trans hN.ge)) L hL).2
    have hA := hJ₀ (J₀ + 1) (by omega)
    rw [← hlam, fc_rhs_eval hset hL (by omega) (fun σ' => hN ▸ hnext σ σ')] at hA
    have hmin : ellMin p p' r s L ≤ N := by
      unfold ellMin; rw [← hlp, ← hlm]; cases σ <;> omega
    have hmax : N < ellMin p p' r s (L + 1) := by
      unfold ellMin; rw [← hlp1, ← hlm1]
      have := hnext σ true; have := hnext σ false; omega
    have htop := (thm_top_layer_of_cited hI p p' r s b hset wp wm htl L N hL hmin hmax).2.2.2
      xp xm hxp hxm
    rw [← hA]
    unfold Astar
    rw [hlam]
    exact htop.2
  have hval : ∀ (N ℓ : ℕ) (x : Nat.Partition ℓ → ℂ), ℓ = N →
      topTerm (kacC b) (kacH r s b) N ℓ L x =
        algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
          RatFunc.C (jform (kacC b) (kacH r s b) ℓ L x x)⁻¹ := by
    intro N ℓ x h
    subst h
    unfold topTerm
    rw [if_pos le_rfl, Nat.sub_self, HN_zero, RatFunc.eval_one, mul_one]
  have hzero : ∀ (N ℓ : ℕ) (x : Nat.Partition ℓ → ℂ), N < ℓ →
      topTerm (kacC b) (kacH r s b) N ℓ L x = 0 := by
    intro N ℓ x h
    unfold topTerm
    rw [if_neg (by omega)]
  have hlow : ∀ (N ℓ : ℕ) (x : Nat.Partition ℓ → ℂ), ℓ < N →
      topTerm (kacC b) (kacH r s b) N ℓ L x =
        algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
          RatFunc.C (jform (kacC b) (kacH r s b) ℓ L x x)⁻¹ *
            evalAt (pt (kacH r s b + (ℓ : ℂ))) (HN (kacC b) (N - ℓ)) := by
    intro N ℓ x h
    unfold topTerm
    rw [if_pos h.le]
  have hpt : ∀ σ : Bool, pt (nodeWt p p' r s (σ, L)) = pt (kacH r s b + (nodeLev p p' r s (σ, L) : ℂ)) := by
    intro σ; rw [nodeWt_add_lev hset, hlam]
  rcases lt_or_gt_of_ne hne with h | h
  · -- `ℓ⁺_L < ℓ⁻_L`
    have k1 := key true _ rfl
    rw [Fintype.sum_bool, if_pos rfl, if_neg (lt_irrefl _), if_neg (fun e => hne e.symm),
      if_neg (by omega), hval _ _ _ hlp.symm, hzero _ _ _ (by rw [← hlm]; exact h)] at k1
    simp only [add_zero, zero_add] at k1
    have k2 := key false _ rfl
    rw [Fintype.sum_bool, if_neg hne, if_pos h, if_pos rfl, if_neg (lt_irrefl _),
      hlow _ _ _ (by rw [← hlp]; exact h), hval _ _ _ hlm.symm,
      reg_lcoeff hset hK hH (σ := true) (L := L)
        (M := nodeLev p p' r s (false, L) - nodeLev p p' r s (true, L)) (by omega)
        (fun σ' => by have := hnext false σ'; omega), hpt true, hlp] at k2
    simp only [add_zero, zero_add] at k2
    refine ⟨k1, ?_⟩
    rw [k1] at k2
    linear_combination k2
  · -- `ℓ⁻_L < ℓ⁺_L`
    have k1 := key false _ rfl
    rw [Fintype.sum_bool, if_neg hne, if_neg (by omega), if_pos rfl, if_neg (lt_irrefl _),
      hval _ _ _ hlm.symm, hzero _ _ _ (by rw [← hlp]; exact h)] at k1
    simp only [add_zero, zero_add] at k1
    have k2 := key true _ rfl
    rw [Fintype.sum_bool, if_pos rfl, if_neg (lt_irrefl _), if_neg (fun e => hne e.symm), if_pos h,
      hval _ _ _ hlp.symm, hlow _ _ _ (by rw [← hlm]; exact h),
      reg_lcoeff hset hK hH (σ := false) (L := L)
        (M := nodeLev p p' r s (true, L) - nodeLev p p' r s (false, L)) (by omega)
        (fun σ' => by have := hnext true σ'; omega), hpt false, hlm] at k2
    simp only [add_zero, zero_add] at k2
    refine ⟨?_, k1⟩
    rw [k1] at k2
    linear_combination k2

end Virasoro
