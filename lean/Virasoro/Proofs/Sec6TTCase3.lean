import Virasoro.Proofs.Sec6TTCase3c

/-!
# Proposition 6.9, Case 3: `2 ≤ s ≤ p'−2`, `s ≡ ±1 (mod ℓ)` (paper.tex l.1510–1565), and the
assembly of the three cases

If `P_N ≡ 0`, both `[(d−d₁)^k]P_N` and `[(d−d₂)^k]P_N` vanish (`ord_{d₁}τ^± = ord_{d₂}τ^± = k`),
so `T_k H_rat = 1`; this contradicts `v_ℓ(H_rat) = 0`, `v_ℓ(H_rat − 1) ≥ v_ℓ(k) + a` and
`v_ℓ(T_k − 1) ≤ v_ℓ(k) + a − 1`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

variable {p p' r s : ℕ}

/-- The splits of `τ^ε_k` at `d₁` and `d₂`, both of order `k`, with the cofactor values. -/
theorem tau_splits (hyp : CoreHyp p p' r s k N) (hp3 : 3 ≤ p') (hs2 : 2 ≤ s) (hsp2 : s + 2 ≤ p')
    (ε : Bool) :
    ((facs p p' r s ε k).map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum = k ∧
    SplitAt (dQ p p' ((p' : ℤ) - 3 * p)) (tauQ p p' r s ε k) k
      ((facs p p' r s ε k).map (cofP p p' (dQ p p' ((p' : ℤ) - 3 * p)))).prod ∧
    SplitAt (dQ p p' ((p' : ℤ) + 3 * p)) (tauQ p p' r s ε k) k
      ((facs p p' r s ε k).map (cofP p p' (dQ p p' ((p' : ℤ) + 3 * p)))).prod := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, -, hk, -, -, -, -, -⟩ := hyp
  have h1 := splitAt_prodPQ p p' (dQ p p' ((p' : ℤ) - 3 * p)) (facs p p' r s ε k)
  have h2 := splitAt_prodPQ p p' (dQ p p' ((p' : ℤ) + 3 * p)) (facs p p' r s ε k)
  rw [← tauQ_eq_facs] at h1 h2
  obtain ⟨Q', hQ'⟩ := tau_split_d1 hp hp3 hcop hr hrp hs hsp ε hk
  have he1 : e1 p' s ε k = k := by unfold e1; split_ifs <;> omega
  have hc1 : ((facs p p' r s ε k).map (cnt p p' (dQ p p' ((p' : ℤ) - 3 * p)))).sum = k :=
    (split_unique h1 hQ').trans he1
  have hc2 := (list_ratio hp hp3 hcop (facs p p' r s ε k) (facs_R hcop hr hrp ε hk)).1
  refine ⟨hc1, by rw [hc1] at h1; exact h1, ?_⟩
  rw [← hc2, hc1] at h2
  exact h2

/-- Proposition 6.9, Case 3 (paper.tex l.1510–1565). -/
theorem core_case3 (h68 : Stmt_prop_h13_nonvanishing) {k N : ℕ} (hyp : CoreHyp p p' r s k N)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p') (hs2 : 2 ≤ s) (hsp2 : s + 2 ≤ p')
    (hsl : (ℓ : ℤ) ∣ (s : ℤ) - 1 ∨ (ℓ : ℤ) ∣ (s : ℤ) + 1) : coreP p p' r s k N ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, -, hk, hN1, hN2, hdet, hc0, hck⟩ := id hyp
  have hp3 := three_le_of_odd_prime hp' hℓ hℓ2 hℓp
  obtain ⟨hk1t, hd1t, hd2t⟩ := tau_splits hyp hp3 hs2 hsp2 true
  obtain ⟨hk1f, hd1f, hd2f⟩ := tau_splits hyp hp3 hs2 hsp2 false
  set z1 := dQ p p' ((p' : ℤ) - 3 * p) with hz1
  set z2 := dQ p p' ((p' : ℤ) + 3 * p) with hz2
  -- the factors `H/[d^k]τ`
  set Ht : ℚ[X] := HpolyD (cs p p') (muQ p p' r s true k) (N - ellPlus p p' r s k) with hHt
  set Hf : ℚ[X] := HpolyD (cs p p') (muQ p p' r s false k) (N - ellMinus p p' r s k) with hHf
  set κt : ℚ := ((tauQ p p' r s true k).coeff k)⁻¹ with hκt
  set κf : ℚ := (-1 : ℚ) ^ k * ((tauQ p p' r s false k).coeff k)⁻¹ with hκf
  have hκt0 : κt ≠ 0 := inv_ne_zero (hck true)
  have hκf0 : κf ≠ 0 := mul_ne_zero (by simp) (inv_ne_zero (hck false))
  -- the values of `H` (Proposition 6.8(iii))
  have hHv : ∀ (ε : Bool) (ν : Fin 2),
      (HpolyD (cs p p') (muQ p p' r s ε k) (N - ellOrb p p' r s ε k)).eval
        (if ν = 0 then z1 else z2) ≠ 0 := by
    intro ε ν
    have hM : 1 ≤ N - ellOrb p p' r s ε k := by
      cases ε
      · rw [ellOrb_false hk]
        have := le_max_right (ellPlus p p' r s k) (ellMinus p p' r s k)
        omega
      · rw [ellOrb_true hk]
        have := le_max_left (ellPlus p p' r s k) (ellMinus p p' r s k)
        omega
    exact (H_at h68 hp hp' hcop hℓ hℓ2 hℓp (nOrb p p' r s ε k) hM (hdet ε) ν).1
  have hHt1 : Ht.eval z1 ≠ 0 := by
    have := hHv true 0; simp only [ellOrb_true hk, if_true] at this; exact this
  have hHt2 : Ht.eval z2 ≠ 0 := by
    have := hHv true 1; simp only [ellOrb_true hk, Fin.one_eq_zero_iff, if_false] at this
    exact this
  have hHf1 : Hf.eval z1 ≠ 0 := by
    have := hHv false 0; simp only [ellOrb_false hk, if_true] at this; exact this
  have hHf2 : Hf.eval z2 ≠ 0 := by
    have := hHv false 1; simp only [ellOrb_false hk, Fin.one_eq_zero_iff, if_false] at this
    exact this
  -- the cofactor products
  set c1t := ((facs p p' r s true k).map (cof p p' z1)).prod
  set c2t := ((facs p p' r s true k).map (cof p p' z2)).prod
  set c1f := ((facs p p' r s false k).map (cof p p' z1)).prod
  set c2f := ((facs p p' r s false k).map (cof p p' z2)).prod
  have hcne : ∀ (ε : Bool) (z : ℚ), ((facs p p' r s ε k).map (cof p p' z)).prod ≠ 0 :=
    fun ε z => List.prod_ne_zero fun h => by
      obtain ⟨x, -, hx0⟩ := List.mem_map.1 h
      exact cof_ne_zero _ _ _ _ hx0
  have hk2t := hk1t
  rw [(list_ratio hp hp3 hcop (facs p p' r s true k) (facs_R hcop hr hrp true hk)).1] at hk2t
  have hk2f := hk1f
  rw [(list_ratio hp hp3 hcop (facs p p' r s false k) (facs_R hcop hr hrp false hk)).1] at hk2f
  have ev1t : ((facs p p' r s true k).map (cofP p p' z1)).prod.eval z1 = (-1) ^ k * c1t := by
    rw [eval_cofP_prod, hk1t]
  have ev1f : ((facs p p' r s false k).map (cofP p p' z1)).prod.eval z1 = (-1) ^ k * c1f := by
    rw [eval_cofP_prod, hk1f]
  have ev2t : ((facs p p' r s true k).map (cofP p p' z2)).prod.eval z2 = (-1) ^ k * c2t := by
    rw [eval_cofP_prod, hk2t]
  have ev2f : ((facs p p' r s false k).map (cofP p p' z2)).prod.eval z2 = (-1) ^ k * c2f := by
    rw [eval_cofP_prod, hk2f]
  -- the two coefficients vanish
  rw [coreP_eq]
  intro h0
  have hB1 : (((facs p p' r s true k).map (cofP p p' z1)).prod * (C κt * Ht) +
      ((facs p p' r s false k).map (cofP p p' z1)).prod * (C κf * Hf)).eval z1 = 0 := by
    by_contra hB
    exact same_order_ne hd1t hd1f hB h0
  have hB2 : (((facs p p' r s true k).map (cofP p p' z2)).prod * (C κt * Ht) +
      ((facs p p' r s false k).map (cofP p p' z2)).prod * (C κf * Hf)).eval z2 = 0 := by
    by_contra hB
    exact same_order_ne hd2t hd2f hB h0
  simp only [eval_add, eval_mul, eval_C, ev1t, ev1f, ev2t, ev2f] at hB1 hB2
  -- `T_k H_rat = 1`
  have hm1 : ((-1 : ℚ) ^ k) ≠ 0 := by simp
  have hrel : c1t * c2f * (Ht.eval z1 * Hf.eval z2) = c1f * c2t * (Ht.eval z2 * Hf.eval z1) := by
    have e1 : c1t * κt * Ht.eval z1 = -(c1f * κf * Hf.eval z1) := by
      apply mul_left_cancel₀ hm1
      linear_combination hB1
    have e2 : c2t * κt * Ht.eval z2 = -(c2f * κf * Hf.eval z2) := by
      apply mul_left_cancel₀ hm1
      linear_combination hB2
    apply mul_left_cancel₀ (mul_ne_zero hκt0 hκf0)
    linear_combination (c2f * κf * Hf.eval z2) * e1 - (c1f * κf * Hf.eval z1) * e2
  set T : ℚ := c1t * c2f / (c2t * c1f) with hT
  set Hr : ℚ := Ht.eval z1 * Hf.eval z2 / (Ht.eval z2 * Hf.eval z1) with hHr
  have hTH : T * Hr = 1 := by
    rw [hT, hHr, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero (hcne _ _)
      (hcne _ _)) (mul_ne_zero hHt2 hHf1))]
    linear_combination hrel
  -- the closed form and the valuations
  have hTc := T_closed hp hp3 hcop hr hrp hsp hk (fun ε => by cases ε <;> assumption)
  rw [← hT] at hTc
  obtain ⟨hT1, hTv⟩ := T_val hℓ2 hp hp' hcop hr hrp hs hsp hlt hℓp hsl hk
  rw [← hTc] at hT1 hTv
  have hHb := Hr_bound h68 hyp hℓ2 hℓp hsl
  have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
  simp only [ellOrb_true hk, ellOrb_false hk, if_true, h10, if_false] at hHb
  rw [← hHt, ← hHf, ← hz1, ← hz2, ← hHr] at hHb
  obtain ⟨hHr0, hHr1⟩ := hHb
  have hT0 : T ≠ 0 := left_ne_zero_of_mul_eq_one hTH
  have hHr0' : Hr ≠ 0 := right_ne_zero_of_mul_eq_one hTH
  by_cases hvT : padicValRat ℓ T = 0
  · have hne : Hr ≠ 1 := by
      intro h1
      apply hT1
      rw [h1, mul_one] at hTH
      rw [hTH, sub_self]
    have h2 := hHr1 hne
    have e : T * (Hr - 1) = -(T - 1) := by linear_combination hTH
    have hv := congrArg (padicValRat ℓ) e
    rw [padicValRat.neg, padicValRat.mul hT0 (sub_ne_zero.2 hne), hvT, zero_add] at hv
    linarith
  · apply hvT
    have := congrArg (padicValRat ℓ) hTH
    rw [padicValRat.mul hT0 hHr0', hHr0, add_zero, padicValRat.one] at this
    exact this

/-- `coreP ≠ 0` in every case (paper.tex l.1428–1565). -/
theorem core_all (h68 : Stmt_prop_h13_nonvanishing) :
    ∀ p p' r s k N : ℕ, CoreHyp p p' r s k N → coreP p p' r s k N ≠ 0 := by
  intro p p' r s k N hyp
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, ⟨ℓ, hℓ, hℓ2, hℓp⟩, hk, -⟩ := id hyp
  by_cases h1 : s = 1 ∨ s = p' - 1
  · exact core_case1 h68 hyp h1
  · have hs2 : 2 ≤ s := by omega
    have hsp2 : s + 2 ≤ p' := by omega
    by_cases hsl : (ℓ : ℤ) ∣ (s : ℤ) - 1 ∨ (ℓ : ℤ) ∣ (s : ℤ) + 1
    · exact core_case3 h68 hyp hℓ hℓ2 hℓp hs2 hsp2 hsl
    · push_neg at hsl
      exact core_case2 h68 hyp hℓ hℓ2 hℓp hs2 hsp2 hsl.1 hsl.2

end TT

end Virasoro
