import Virasoro.Proofs.Sec6TTCase2a

/-!
# Proposition 6.9, Case 2: `2 ≤ s ≤ p'−2`, `s ≢ ±1 (mod ℓ)` (paper.tex l.1464–1509)

Now `e₊ = e₋ = k`; the two summands of `[(d−d₁)^k]P_N(d)` have `ℓ`-adic valuations
`W + v_ℓ(H_{M^±}(c⋆, μ^±_k, d₁))`, where `W = ∑ v_ℓ(x² − x₁²) − ∑ v_ℓ(x² − x₀²)` over the factors
of `τ^±_k` does not depend on the sign (`0` for `ℓ ≥ 5`, `−k v₃(p'−3p)` for `ℓ = 3`), and the
last sum of Proposition 6.8(iii) vanishes; so they differ by
`−(v_ℓ(M⁺!) − v_ℓ(M⁻!)) − (M⁺ − M⁻)a ≠ 0`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

section Case2

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `∑ v_ℓ(x² − y²)` over the factors of `𝒫_{R,S}`. -/
def Wv (ℓ p p' : ℕ) (y : ℤ) (RS : ℕ × ℕ) : ℤ :=
  ∑ i ∈ idx RS.1 RS.2, (padicValInt ℓ (xv p p' i ^ 2 - y ^ 2) : ℤ)

theorem dQ_x0 (p p' : ℕ) : dQ p p' ((p' : ℤ) - p) = 0 := by
  rw [dQ]
  push_cast
  ring

theorem val_neg_one_pow (n : ℕ) : padicValRat ℓ ((-1 : ℚ) ^ n) = 0 := by
  rcases neg_one_pow_eq_or ℚ n with h | h <;> rw [h]
  · exact padicValRat.one
  · rw [padicValRat.neg, padicValRat.one]

/-- `v_ℓ(∏ cof(d₁)) − v_ℓ(∏ cof(0)) = ∑ (W₁ − W₀) − a(∑ cnt₀ − ∑ cnt₁)`. -/
theorem val_list {p p' : ℕ} (hℓ2 : ℓ ≠ 2) (hp : 0 < p) (hp' : 0 < p') (hℓp : ¬ ℓ ∣ p)
    (L : List (ℕ × ℕ)) :
    padicValRat ℓ ((L.map (cof p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod) -
      padicValRat ℓ ((L.map (cof p p' 0)).prod) =
      (L.map fun RS => Wv ℓ p p' ((p' : ℤ) - 3 * p) RS - Wv ℓ p p' ((p' : ℤ) - p) RS).sum -
        (padicValNat ℓ p' : ℤ) * ((L.map fun RS => (cnt p p' 0 RS : ℤ)).sum -
          (L.map fun RS => (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS : ℤ)).sum) := by
  induction L with
  | nil => simp
  | cons RS L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [padicValRat.mul (cof_ne_zero _ _ _ _)
        (List.prod_ne_zero fun h => by
          obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
          exact cof_ne_zero _ _ _ _ hx0),
      padicValRat.mul (cof_ne_zero _ _ _ _)
        (List.prod_ne_zero fun h => by
          obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
          exact cof_ne_zero _ _ _ _ hx0)]
    have h1 := val_cof hℓ2 hp hp' hℓp RS ((p' : ℤ) - 3 * p)
    have h0 := val_cof hℓ2 hp hp' hℓp RS ((p' : ℤ) - p)
    rw [dQ_x0] at h0
    rw [h1, h0]
    unfold Wv at ih ⊢
    linear_combination ih

/-- The sign-independent part `W` (paper.tex l.1478–1503). -/
theorem W_total {p p' r s : ℕ} (hp : 2 ≤ p) (hcop : Nat.Coprime p p') (hs : 0 < s)
    (hsp : s < p') (hℓ2 : ℓ ≠ 2) (hℓp' : ℓ ∣ p') (hs1 : ¬ (ℓ : ℤ) ∣ (s : ℤ) - 1)
    (hs2 : ¬ (ℓ : ℤ) ∣ (s : ℤ) + 1) (ε : Bool) {k : ℕ} (hk : 1 ≤ k)
    (hcnt : ((facs p p' r s ε k).map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum = k) :
    ((facs p p' r s ε k).map fun RS =>
        Wv ℓ p p' ((p' : ℤ) - 3 * p) RS - Wv ℓ p p' ((p' : ℤ) - p) RS).sum =
      if ℓ = 3 then -(padicValInt 3 ((p' : ℤ) - 3 * p) : ℤ) * k else 0 := by
  have hℓp'z : (ℓ : ℤ) ∣ p' := Int.natCast_dvd_natCast.2 hℓp'
  have hℓpz : ¬ (ℓ : ℤ) ∣ p := by
    intro h
    have h1 : ℓ ∣ p := Int.natCast_dvd_natCast.1 h
    have := Nat.dvd_gcd h1 hℓp'
    rw [hcop] at this
    exact hℓ.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hS := facs_S (p := p) (r := r) hsp ε hk
  split_ifs with h3
  · subst h3
    have hp0 : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
    have hx1 : (p' : ℤ) - 3 * p ≠ 0 := by
      intro h0
      have h3p : p' = 3 * p := by omega
      have := Nat.Coprime.coprime_dvd_right (show p ∣ p' by rw [h3p]; exact dvd_mul_left p 3) hcop
      rw [Nat.coprime_self] at this
      omega
    have h3s : (3 : ℤ) ∣ s := by
      have h := Int.emod_emod_of_dvd (s : ℤ) (show (3 : ℤ) ∣ 3 from dvd_refl 3)
      omega
    have key : ∀ RS ∈ facs p p' r s ε k, Wv 3 p p' ((p' : ℤ) - 3 * p) RS -
        Wv 3 p p' ((p' : ℤ) - p) RS =
        -(padicValInt 3 ((p' : ℤ) - 3 * p) : ℤ) *
          (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS : ℤ) := by
      intro RS hRS
      obtain ⟨t, σ, hσ, hS'⟩ := hS RS hRS
      have h3S : 3 ∣ RS.2 := by
        have : (3 : ℤ) ∣ (RS.2 : ℤ) := by
          rw [hS']
          exact dvd_add (dvd_mul_of_dvd_left hℓp'z t) (dvd_mul_of_dvd_right h3s σ)
        exact_mod_cast this
      obtain ⟨T, hT⟩ := h3S
      have hW := W_three (p := p) (p' := p') hℓp'z hℓpz hx1 RS.1 T
      rw [← hT] at hW
      have hc : cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) RS = m1 p p' RS.1 RS.2 :=
        card_d1 (by omega) (by omega) RS.1 RS.2
      unfold Wv
      rw [hc]
      exact hW
    have hc : ((facs p p' r s ε k).map fun a =>
        (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)) a : ℤ)).sum = (k : ℤ) := by
      have := congrArg (Nat.cast : ℕ → ℤ) hcnt
      rw [Nat.cast_list_sum, List.map_map] at this
      exact this
    rw [List.map_congr_left key, List.sum_map_mul_left, hc]
  · have hℓ5 : 5 ≤ ℓ := by
      have := hℓ.out.two_le
      rcases Nat.lt_or_ge ℓ 5 with h | h
      · interval_cases ℓ
        · exact absurd rfl hℓ2
        · exact absurd rfl h3
        · exact absurd hℓ.out (by decide)
      · exact h
    have key : ∀ RS ∈ facs p p' r s ε k, Wv ℓ p p' ((p' : ℤ) - 3 * p) RS -
        Wv ℓ p p' ((p' : ℤ) - p) RS = 0 := by
      intro RS hRS
      obtain ⟨t, σ, hσ, hS'⟩ := hS RS hRS
      obtain ⟨hS1, hS2⟩ := S_not_pm1 hℓp'z hs1 hs2 hσ hS'
      unfold Wv
      rw [sub_eq_zero]
      exact_mod_cast W_five hℓ5 hℓp'z hℓpz RS.1 RS.2 hS1 hS2
    rw [List.map_congr_left key]
    simp

theorem fact_val_mono {ℓ : ℕ} [Fact ℓ.Prime] {m n : ℕ} (h : m ≤ n) :
    padicValNat ℓ m.factorial ≤ padicValNat ℓ n.factorial :=
  (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).1
    (dvd_trans pow_padicValNat_dvd (Nat.factorial_dvd_factorial h))

/-- One branch at `d₁`: the split of order `k` and the valuation of its coefficient
(paper.tex l.1466–1477, l.1504–1508). -/
theorem branch_val (h68 : Stmt_prop_h13_nonvanishing) {p p' r s k N : ℕ}
    (hyp : CoreHyp p p' r s k N) {ℓ : ℕ} [hℓF : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p')
    (hs2 : 2 ≤ s) (hsp2 : s + 2 ≤ p') (hs1 : ¬ (ℓ : ℤ) ∣ (s : ℤ) - 1)
    (hs1' : ¬ (ℓ : ℤ) ∣ (s : ℤ) + 1) (ε : Bool) :
    ∃ Q : ℚ[X], SplitAt (dQ p p' ((p' : ℤ) - 3 * p)) (tauQ p p' r s ε k) k Q ∧
      padicValRat ℓ (Q.eval (dQ p p' ((p' : ℤ) - 3 * p)) *
        (C ((if ε then 1 else (-1 : ℚ) ^ k) * ((tauQ p p' r s ε k).coeff k)⁻¹) *
          HpolyD (cs p p') (muQ p p' r s ε k) (N - ellOrb p p' r s ε k)).eval
            (dQ p p' ((p' : ℤ) - 3 * p))) =
        (if ℓ = 3 then -(padicValInt 3 ((p' : ℤ) - 3 * p) : ℤ) * k else 0) -
          (padicValNat ℓ (N - ellOrb p p' r s ε k).factorial : ℤ) -
          ((N - ellOrb p p' r s ε k : ℕ) : ℤ) * (padicValNat ℓ p' : ℤ) := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, -, hk, hN1, hN2, hdet, hc0, hck⟩ := id hyp
  have hp3 := three_le_of_odd_prime hp' hℓF.out hℓ2 hℓp
  have h0p : 0 < p := by omega
  have h0p' : 0 < p' := by omega
  have hℓpn : ¬ ℓ ∣ p := by
    intro h
    have := Nat.dvd_gcd h hℓp
    rw [hcop] at this
    exact hℓF.out.one_lt.ne' (Nat.dvd_one.1 this)
  set d1 := dQ p p' ((p' : ℤ) - 3 * p) with hd1
  set L := facs p p' r s ε k with hL
  have hsplit := splitAt_prodPQ p p' d1 L
  rw [← tauQ_eq_facs] at hsplit
  obtain ⟨Q', hQ'⟩ := tau_split_d1 hp hp3 hcop hr hrp hs hsp ε hk
  have he1 : e1 p' s ε k = k := by unfold e1; split_ifs <;> omega
  have hcnt1 : (L.map (cnt p p' d1)).sum = k := (split_unique hsplit hQ').trans he1
  have hsplit0 := splitAt_prodPQ p p' 0 L
  rw [← tauQ_eq_facs] at hsplit0
  have hcnt0 : (L.map (cnt p p' 0)).sum = k := split0_eq hsplit0 (hc0 ε) (hck ε)
  have ht := coeff_split0 hsplit0
  rw [hcnt0, eval_cofP_prod, hcnt0] at ht
  refine ⟨_, hcnt1 ▸ hsplit, ?_⟩
  -- the value of `H` at `d₁` (Proposition 6.8(iii))
  have hM : 1 ≤ N - ellOrb p p' r s ε k := by
    cases ε
    · rw [ellOrb_false hk]
      have := le_max_right (ellPlus p p' r s k) (ellMinus p p' r s k)
      omega
    · rw [ellOrb_true hk]
      have := le_max_left (ellPlus p p' r s k) (ellMinus p p' r s k)
      omega
  obtain ⟨hHne, hHv⟩ := H_at h68 hp hp' hcop hℓF.out hℓ2 hℓp (nOrb p p' r s ε k) hM (hdet ε) 0
  have hHne' : (HpolyD (cs p p') (muQ p p' r s ε k) (N - ellOrb p p' r s ε k)).eval d1 ≠ 0 := by
    simp only [ite_true, if_true, Fin.isValue] at hHne
    exact hHne
  have hHv' : padicValRat ℓ ((HpolyD (cs p p') (muQ p p' r s ε k) (N - ellOrb p p' r s ε k)).eval
      d1) = -(padicValNat ℓ (N - ellOrb p p' r s ε k).factorial : ℤ) -
        ((N - ellOrb p p' r s ε k : ℕ) : ℤ) * (padicValNat ℓ p' : ℤ) -
        ∑ u ∈ Finset.Icc 1 (N - ellOrb p p' r s ε k),
          (padicValInt ℓ (nOrb p p' r s ε k ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ) := by
    simp only [ite_true, if_true, Fin.isValue] at hHv
    exact hHv
  clear hHne hHv
  have hlast : ∑ u ∈ Finset.Icc 1 (N - ellOrb p p' r s ε k),
      (padicValInt ℓ (nOrb p p' r s ε k ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ) = 0 :=
    sum_eq_zero fun u _ => by
      rw [lastsum_zero (Int.natCast_dvd_natCast.2 hℓp)
        (fun h => hℓpn (Int.natCast_dvd_natCast.1 h)) hs1 hs1' ε k u]
      rfl
  rw [hlast, sub_zero] at hHv'
  -- the coefficient
  rw [eval_cofP_prod, hcnt1, eval_mul, eval_C, ht]
  have hc1 : (L.map (cof p p' d1)).prod ≠ 0 := List.prod_ne_zero fun h => by
    obtain ⟨x, -, hx0⟩ := List.mem_map.1 h
    exact cof_ne_zero _ _ _ _ hx0
  have hc0' : (L.map (cof p p' 0)).prod ≠ 0 := List.prod_ne_zero fun h => by
    obtain ⟨x, -, hx0⟩ := List.mem_map.1 h
    exact cof_ne_zero _ _ _ _ hx0
  have hsg : (if ε then 1 else (-1 : ℚ) ^ k) ≠ 0 := by split_ifs <;> simp
  have hsgv : padicValRat ℓ (if ε then 1 else (-1 : ℚ) ^ k) = 0 := by
    split_ifs
    · exact padicValRat.one
    · exact val_neg_one_pow k
  have hm1 : ((-1 : ℚ) ^ k) ≠ 0 := by simp
  rw [padicValRat.mul (mul_ne_zero hm1 hc1) (mul_ne_zero (mul_ne_zero hsg
      (inv_ne_zero (mul_ne_zero hm1 hc0'))) hHne'),
    padicValRat.mul hm1 hc1, padicValRat.mul (mul_ne_zero hsg (inv_ne_zero
      (mul_ne_zero hm1 hc0'))) hHne', padicValRat.mul hsg (inv_ne_zero (mul_ne_zero hm1 hc0')),
    padicValRat.inv, padicValRat.mul hm1 hc0', val_neg_one_pow, hsgv, hHv']
  have hvl := val_list hℓ2 h0p h0p' hℓpn L
  have hW := W_total (r := r) hp hcop hs hsp hℓ2 hℓp hs1 hs1' ε hk hcnt1
  have hk1 : (L.map fun RS => (cnt p p' d1 RS : ℤ)).sum = k := by
    have := congrArg (Nat.cast : ℕ → ℤ) hcnt1
    rw [Nat.cast_list_sum, List.map_map] at this
    exact this
  have hk0 : (L.map fun RS => (cnt p p' 0 RS : ℤ)).sum = k := by
    have := congrArg (Nat.cast : ℕ → ℤ) hcnt0
    rw [Nat.cast_list_sum, List.map_map] at this
    exact this
  rw [hk1, hk0, hW, sub_self, mul_zero, sub_zero] at hvl
  linear_combination hvl

/-- Proposition 6.9, Case 2 (paper.tex l.1464–1509). -/
theorem core_case2 (h68 : Stmt_prop_h13_nonvanishing) {p p' r s k N : ℕ}
    (hyp : CoreHyp p p' r s k N) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p')
    (hs2 : 2 ≤ s) (hsp2 : s + 2 ≤ p') (hs1 : ¬ (ℓ : ℤ) ∣ (s : ℤ) - 1)
    (hs1' : ¬ (ℓ : ℤ) ∣ (s : ℤ) + 1) : coreP p p' r s k N ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, -, hk, hN1, hN2, -, -, -⟩ := id hyp
  obtain ⟨Q₁, hQ₁, hv₁⟩ := branch_val h68 hyp hℓ2 hℓp hs2 hsp2 hs1 hs1' true
  obtain ⟨Q₂, hQ₂, hv₂⟩ := branch_val h68 hyp hℓ2 hℓp hs2 hsp2 hs1 hs1' false
  simp only [if_true, Bool.false_eq_true, if_false, one_mul, ellOrb_true hk,
    ellOrb_false hk] at hv₁ hv₂
  rw [coreP_eq]
  refine same_order_ne hQ₁ hQ₂ ?_
  rw [eval_add, eval_mul (p := Q₁), eval_mul (p := Q₂)]
  intro h0
  have h1 := congrArg (padicValRat ℓ) (eq_neg_of_add_eq_zero_left h0)
  rw [padicValRat.neg, hv₁, hv₂] at h1
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  have ha : 1 ≤ padicValNat ℓ p' := one_le_padicValNat_of_dvd (by omega) hℓp
  have hpN := le_max_left (ellPlus p p' r s k) (ellMinus p p' r s k)
  have hmN := le_max_right (ellPlus p p' r s k) (ellMinus p p' r s k)
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · have hv := fact_val_mono (ℓ := ℓ) (show N - ellMinus p p' r s k ≤ N - ellPlus p p' r s k by
      omega)
    have : ((N - ellMinus p p' r s k : ℕ) : ℤ) < (N - ellPlus p p' r s k : ℕ) := by
      exact_mod_cast (show N - ellMinus p p' r s k < N - ellPlus p p' r s k by omega)
    have hv' : (padicValNat ℓ (N - ellMinus p p' r s k).factorial : ℤ) ≤
        padicValNat ℓ (N - ellPlus p p' r s k).factorial := by exact_mod_cast hv
    have ha' : (1 : ℤ) ≤ padicValNat ℓ p' := by exact_mod_cast ha
    nlinarith
  · have hv := fact_val_mono (ℓ := ℓ) (show N - ellPlus p p' r s k ≤ N - ellMinus p p' r s k by
      omega)
    have : ((N - ellPlus p p' r s k : ℕ) : ℤ) < (N - ellMinus p p' r s k : ℕ) := by
      exact_mod_cast (show N - ellPlus p p' r s k < N - ellMinus p p' r s k by omega)
    have hv' : (padicValNat ℓ (N - ellPlus p p' r s k).factorial : ℤ) ≤
        padicValNat ℓ (N - ellMinus p p' r s k).factorial := by exact_mod_cast hv
    have ha' : (1 : ℤ) ≤ padicValNat ℓ p' := by exact_mod_cast ha
    nlinarith

end Case2

end TT

end Virasoro
