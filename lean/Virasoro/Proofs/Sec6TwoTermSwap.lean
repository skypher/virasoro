import Virasoro.Proofs.Sec6TwoTerm

/-!
# Proposition 6.9: the reduction `b ↦ b⁻¹` (paper.tex l.1429–1430)

"By `b ↦ b⁻¹` (swapping `p ↔ p'`, `r ↔ s`), assume an odd prime `ℓ ∣ p'`."  The swap fixes
`c(b)` and `h_{r,s}(b)`, fixes `ℓ^±_k` for odd `k` and exchanges `ℓ⁺_k` and `ℓ⁻_k` for even `k`;
the statement `P_N ≢ 0` is symmetric in the two branches.
-/

namespace Virasoro

/-- Frozen sub-statement of Proposition 6.9 (paper.tex l.1430–1565): `P_N(d) ≢ 0` on a two-vector
level, when an odd prime divides `p'`.
Demand sheet: `Stmt_sub_two_term_nonzero` word for word, with the added hypothesis
`∃ ℓ` prime, `ℓ ≠ 2`, `ℓ ∣ p'` (the assumption made at l.1429–1430 and used in all three cases,
l.1451, l.1464–1565). -/
def Stmt_sub_two_term_nonzero_odd : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    (∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ p') →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → max (ellPlus p p' r s k) (ellMinus p p' r s k) < N →
        N < ellMin p p' r s (k + 1) →
        ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            topTerm (kacC b) (kacH r s b) N (ellPlus p p' r s k) k xp +
                topTerm (kacC b) (kacH r s b) N (ellMinus p p' r s k) k xm ≠ 0

theorem kacC_inv_swap (b : ℂ) : kacC b⁻¹ = kacC b := by
  unfold kacC
  rw [inv_inv]
  ring

theorem kacH_inv_swap (r s : ℤ) (b : ℂ) : kacH s r b⁻¹ = kacH r s b := by
  unfold kacH
  rw [inv_inv]
  ring

theorem ellPlus_swap_odd {k : ℕ} (hk : k % 2 = 1) (p p' r s : ℕ) :
    ellPlus p' p s r k = ellPlus p p' r s k := by
  unfold ellPlus
  rw [if_neg (by omega), if_neg (by omega)]
  ring

theorem ellMinus_swap_odd {k : ℕ} (hk : k % 2 = 1) (p p' r s : ℕ) :
    ellMinus p' p s r k = ellMinus p p' r s k := by
  unfold ellMinus
  rw [if_neg (by omega), if_neg (by omega), mul_comm]

theorem ellPlus_swap_even {k : ℕ} (hk : k % 2 = 0) (p p' r s : ℕ) :
    ellPlus p' p s r k = ellMinus p p' r s k := by
  unfold ellPlus ellMinus
  rw [if_pos hk, if_pos hk]
  congr 1
  ring

theorem ellMinus_swap_even {k : ℕ} (hk : k % 2 = 0) (p p' r s : ℕ) :
    ellMinus p' p s r k = ellPlus p p' r s k := by
  unfold ellPlus ellMinus
  rw [if_pos hk, if_pos hk]
  congr 1
  ring

theorem ellMin_swap (p p' r s k : ℕ) : ellMin p' p s r k = ellMin p p' r s k := by
  unfold ellMin
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [ellPlus_swap_even hk p p' r s, ellMinus_swap_even hk p p' r s, min_comm]
  · rw [ellPlus_swap_odd hk p p' r s, ellMinus_swap_odd hk p p' r s]

/-- The statement `P_N ≢ 0` for a pair `(c, h)` and the levels of `(p, p', r, s)`. -/
def TwoTermAt (c h : ℂ) (p p' r s : ℕ) : Prop :=
  ∀ wp wm : ℕ → Verma ℂ c h,
    ((∀ k : ℕ, 1 ≤ k →
        Verma.IsSingular (wp k) (ellPlus p p' r s k) ∧
          Verma.IsSingular (wm k) (ellMinus p p' r s k)) ∧
      (∀ i : ℕ, 1 ≤ i → jantzen c h i = Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i))) →
    ∀ k N : ℕ, 1 ≤ k → max (ellPlus p p' r s k) (ellMinus p p' r s k) < N →
      N < ellMin p p' r s (k + 1) →
      ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
          (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
        Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
        Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
          topTerm c h N (ellPlus p p' r s k) k xp + topTerm c h N (ellMinus p p' r s k) k xm ≠ 0

set_option maxHeartbeats 2000000 in
/-- The reduction of l.1429–1430: it suffices to treat the case of an odd prime `ℓ ∣ p'`. -/
theorem sub_two_term_nonzero_of_odd (h : Stmt_sub_two_term_nonzero_odd) :
    Stmt_sub_two_term_nonzero := by
  intro p p' r s b hset wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  by_cases hodd : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ p'
  · exact h p p' r s b hset hodd wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have h2p' : 2 ∣ p' := by
    by_contra hc
    exact hodd ⟨p'.minFac, Nat.minFac_prime (by omega),
      fun h2 => hc (h2 ▸ Nat.minFac_dvd p'), Nat.minFac_dvd p'⟩
  have h2p : ¬ 2 ∣ p := fun h2 => by
    have h3 := Nat.dvd_gcd h2 h2p'
    rw [hcop.gcd_eq_one] at h3
    omega
  have hodd' : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ p :=
    ⟨p.minFac, Nat.minFac_prime (by omega), fun h2 => h2p (h2 ▸ Nat.minFac_dvd p),
      Nat.minFac_dvd p⟩
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'C : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hset' : MinimalSetting p' p s r b⁻¹ := by
    refine ⟨hp', hp, hcop.symm, hs, hsp, hr, hrp, by nlinarith, ?_⟩
    rw [inv_pow, hb]
    field_simp
  have H0 : TwoTermAt (kacC b⁻¹) (kacH (s : ℤ) (r : ℤ) b⁻¹) p' p s r :=
    fun wp wm hT => h p' p s r b⁻¹ hset' hodd' wp wm hT
  have H : TwoTermAt (kacC b) (kacH (r : ℤ) (s : ℤ) b) p' p s r := by
    rw [← kacC_inv_swap b, ← kacH_inv_swap (r : ℤ) (s : ℤ) b]
    exact H0
  obtain ⟨hsing, hjan⟩ := hT
  have H2 := H (fun i => if i % 2 = 0 then wm i else wp i)
    (fun i => if i % 2 = 0 then wp i else wm i)
    ⟨fun i hi => by
        rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2
        · rw [if_pos hi2, if_pos hi2, ellPlus_swap_even hi2 p p' r s, ellMinus_swap_even hi2 p p' r s]
          exact ⟨(hsing i hi).2, (hsing i hi).1⟩
        · rw [if_neg (by omega), if_neg (by omega), ellPlus_swap_odd hi2 p p' r s,
            ellMinus_swap_odd hi2 p p' r s]
          exact hsing i hi,
      fun i hi => by
        rcases Nat.mod_two_eq_zero_or_one i with hi2 | hi2
        · rw [if_pos hi2, if_pos hi2, sup_comm]
          exact hjan i hi
        · rw [if_neg (by omega), if_neg (by omega)]
          exact hjan i hi⟩ k N hk
  rw [ellMin_swap] at H2
  rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
  · rw [ellPlus_swap_even hk2 p p' r s, ellMinus_swap_even hk2 p p' r s] at H2
    rw [if_pos hk2, if_pos hk2, max_comm] at H2
    have H3 := H2 hN1 hN2 xm xp hxm hxp
    rwa [add_comm] at H3
  · rw [ellPlus_swap_odd hk2 p p' r s, ellMinus_swap_odd hk2 p p' r s] at H2
    have hne : ¬ k % 2 = 0 := by omega
    rw [if_neg hne, if_neg hne] at H2
    exact H2 hN1 hN2 xp xm hxp hxm

end Virasoro
