import Virasoro.Proofs.Sec8BLabels

/-!
# Lemma 8.10 (`lem:boundary-labels`), the classification and the pole order
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' x₀ : ℕ} {b : ℂ}

section Labels

variable (hB : BoundarySetting p p' x₀ b)
include hB

/-- The weight of `h_{1,1}` gives a minimal-model setting with the same `p, p', b⋆`. -/
theorem bSetting_minimal : MinimalSetting p p' 1 1 b := by
  obtain ⟨hp, hp', hcop, -, -, -, hb⟩ := hB
  refine ⟨hp, hp', hcop, by norm_num, by omega, by norm_num, by omega, ?_, hb⟩
  have hne : ¬ (p = 2 ∧ p' = 2) := by
    rintro ⟨rfl, rfl⟩; exact absurd hcop (by decide)
  by_cases h3 : 3 ≤ p
  · nlinarith
  · have : p = 2 := by omega
    subst this
    have : 3 ≤ p' := by omega
    nlinarith

theorem weight_iff (g : Label) (i : ℕ) :
    kacHL g b = bWt p p' x₀ i ↔ ((p' : ℤ) * g.1 - p * g.2) ^ 2 = bT p p' x₀ i ^ 2 := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  rw [kacHL_eq_momWt hp hp' hB.2.2.2.2.2.2 g]
  unfold bWt
  rw [momWt_eq_iff hp hp', bM_sq hB]

theorem lvl_iff (g : Label) (k : ℕ) :
    kacHL g b + (g.lvl : ℂ) = bWt p p' x₀ k ↔
      ((p' : ℤ) * g.1 + p * g.2) ^ 2 = (bM p p' x₀ k : ℤ) ^ 2 := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  rw [kacH_add_lvl hp hp' hB.2.2.2.2.2.2 g]
  unfold bWt
  exact momWt_eq_iff hp hp' _ _

theorem bEps_sq_mul (z : ℤ) : (-bEps p x₀ * (if 0 < bT p p' x₀ k then 1 else -1) * z) ^ 2 = z ^ 2 := by
  unfold bEps; split_ifs <;> ring

/-- `2T_i ≢ 0 (mod N₀)`. -/
theorem not_dvd_two_bT (i : ℕ) : ¬ (2 * (p : ℤ) * p') ∣ 2 * bT p p' x₀ i := by
  intro h
  apply not_dvd_two_x₀ hB
  have : (2 * (p : ℤ) * p') ∣ 2 * bPi i * (2 * p * p') := ⟨2 * bPi i, by ring⟩
  have := dvd_sub h this
  unfold bT at this
  simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using this

/-- Lemma 8.10: exactly one positive label of weight `μ_i` leads to `μ_k`. -/
theorem label_iff {i k : ℕ} (hik : i < k) (g : Label) (h1 : 0 < g.1) (h2 : 0 < g.2) :
    (kacHL g b = bWt p p' x₀ i ∧ kacHL g b + (g.lvl : ℂ) = bWt p p' x₀ k) ↔
      g = bLabel p p' x₀ i k := by
  obtain ⟨hL1, hL2, hY, hX⟩ := bLabel_xy hB hik
  have hp0 : (0 : ℤ) < p := by have := hB.1; omega
  have hp0' : (0 : ℤ) < p' := by have := hB.2.1; omega
  have hg1 : (0 : ℤ) < g.1 := by exact_mod_cast h1
  have hg2 : (0 : ℤ) < g.2 := by exact_mod_cast h2
  constructor
  · rintro ⟨hw, hw'⟩
    rw [weight_iff hB] at hw
    rw [lvl_iff hB] at hw'
    have hy0 : (0 : ℤ) < (p' : ℤ) * g.1 + p * g.2 := add_pos (mul_pos hp0' hg1) (mul_pos hp0 hg2)
    have hy : (p' : ℤ) * g.1 + p * g.2 = bM p p' x₀ k :=
      (pow_left_inj₀ hy0.le (by positivity) two_ne_zero).1 hw'
    -- `x = ±X`
    have hxX : ((p' : ℤ) * g.1 - p * g.2) ^ 2 =
        ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2) ^ 2 := by
      rw [hw, hX, bEps_sq_mul hB]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hxX with hx | hx
    · apply Prod.ext
      · have : (2 * p' : ℤ) * g.1 = 2 * p' * (bLabel p p' x₀ i k).1 := by linarith
        exact_mod_cast mul_left_cancel₀ (by linarith) this
      · have : (2 * p : ℤ) * g.2 = 2 * p * (bLabel p p' x₀ i k).2 := by linarith
        exact_mod_cast mul_left_cancel₀ (by linarith) this
    · exfalso
      have hcong := label_cong hB (u := g.1) (v := g.2)
      have hcongL := label_cong hB (u := (bLabel p p' x₀ i k).1) (v := (bLabel p p' x₀ i k).2)
      have hXT : ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 = bT p p' x₀ i) ∨
          ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 = -bT p p' x₀ i) := by
        rw [hX]; unfold bEps; split_ifs <;> simp
      by_cases hpx : p ∣ x₀
      · have hpT := (dvd_bT_p hB (i := i)).2 hpx
        have hpX : (p : ℤ) ∣ (p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 := by
          rcases hXT with h | h <;> rw [h]
          · exact hpT
          · exact (dvd_neg).2 hpT
        have hpx' : (p : ℤ) ∣ (p' : ℤ) * g.1 - p * g.2 := by
          rw [hx]; exact (dvd_neg).2 hpX
        have d1 := hcong.1 hpx'
        have d2 := hcongL.1 hpX
        rw [hy, hx] at d1
        rw [hY] at d2
        have d3 := dvd_sub d2 d1
        rw [show (bM p p' x₀ k : ℤ) + ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2) -
            ((bM p p' x₀ k : ℤ) + -((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2)) =
            2 * ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2) by ring] at d3
        apply not_dvd_two_bT hB i
        rcases hXT with h | h
        · rw [h] at d3; exact d3
        · rw [h] at d3
          have d4 := (dvd_neg).2 d3
          rwa [show -(2 * -bT p p' x₀ i) = 2 * bT p p' x₀ i by ring] at d4
      · have hp'x : p' ∣ x₀ := by have := hB.2.2.2.2.2.1; tauto
        have hpT := (dvd_bT_p' hB (i := i)).2 hp'x
        have hpX : (p' : ℤ) ∣ (p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 := by
          rcases hXT with h | h <;> rw [h]
          · exact hpT
          · exact (dvd_neg).2 hpT
        have hpx' : (p' : ℤ) ∣ (p' : ℤ) * g.1 - p * g.2 := by
          rw [hx]; exact (dvd_neg).2 hpX
        have d1 := hcong.2 hpx'
        have d2 := hcongL.2 hpX
        rw [hy, hx] at d1
        rw [hY] at d2
        have d3 := dvd_sub d1 d2
        rw [show (bM p p' x₀ k : ℤ) - -((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2) -
            ((bM p p' x₀ k : ℤ) - ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2)) =
            2 * ((p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2) by ring] at d3
        apply not_dvd_two_bT hB i
        rcases hXT with h | h
        · rw [h] at d3; exact d3
        · rw [h] at d3
          have d4 := (dvd_neg).2 d3
          rwa [show -(2 * -bT p p' x₀ i) = 2 * bT p p' x₀ i by ring] at d4
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [weight_iff hB, hX, bEps_sq_mul hB]
    · rw [lvl_iff hB, hY]

/-- Lemma 8.10: every positive label of weight `μ_i` leads to a node `μ_k`, `k > i`. -/
theorem label_leads (i : ℕ) (g : Label) (h1 : 0 < g.1) (h2 : 0 < g.2)
    (hw : kacHL g b = bWt p p' x₀ i) : ∃ k : ℕ, i < k ∧ kacHL g b + (g.lvl : ℂ) = bWt p p' x₀ k := by
  rw [weight_iff hB] at hw
  have hp0 : (0 : ℤ) < p := by have := hB.1; omega
  have hp0' : (0 : ℤ) < p' := by have := hB.2.1; omega
  have hg1 : (0 : ℤ) < g.1 := by exact_mod_cast h1
  have hg2 : (0 : ℤ) < g.2 := by exact_mod_cast h2
  have hy0 : (0 : ℤ) < (p' : ℤ) * g.1 + p * g.2 := add_pos (mul_pos hp0' hg1) (mul_pos hp0 hg2)
  have hcong := label_cong hB (u := g.1) (v := g.2)
  have hT : ((p' : ℤ) * g.1 - p * g.2 = bT p p' x₀ i) ∨ ((p' : ℤ) * g.1 - p * g.2 = -bT p p' x₀ i) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 hw
  have hTx : bT p p' x₀ i - x₀ = bPi i * (2 * p * p') := by unfold bT; ring
  have hN : (2 * (p : ℤ) * p') ∣ ((p' : ℤ) * g.1 + p * g.2) - x₀ ∨
      (2 * (p : ℤ) * p') ∣ ((p' : ℤ) * g.1 + p * g.2) + x₀ := by
    have hm : (2 * (p : ℤ) * p') ∣ bT p p' x₀ i - x₀ := ⟨bPi i, by rw [hTx]; ring⟩
    by_cases hpx : p ∣ x₀
    · have hpx' : (p : ℤ) ∣ (p' : ℤ) * g.1 - p * g.2 := by
        rcases hT with h | h <;> rw [h]
        · exact (dvd_bT_p hB).2 hpx
        · exact (dvd_neg).2 ((dvd_bT_p hB).2 hpx)
      have d := hcong.1 hpx'
      rcases hT with h | h <;> rw [h] at d
      · right
        have d2 := dvd_sub d hm
        rwa [show (p' : ℤ) * g.1 + p * g.2 + bT p p' x₀ i - (bT p p' x₀ i - x₀) =
          (p' : ℤ) * g.1 + p * g.2 + x₀ by ring] at d2
      · left
        have d2 := dvd_add d hm
        rwa [show (p' : ℤ) * g.1 + p * g.2 + -bT p p' x₀ i + (bT p p' x₀ i - x₀) =
          (p' : ℤ) * g.1 + p * g.2 - x₀ by ring] at d2
    · have hp'x : p' ∣ x₀ := by have := hB.2.2.2.2.2.1; tauto
      have hpx' : (p' : ℤ) ∣ (p' : ℤ) * g.1 - p * g.2 := by
        rcases hT with h | h <;> rw [h]
        · exact (dvd_bT_p' hB).2 hp'x
        · exact (dvd_neg).2 ((dvd_bT_p' hB).2 hp'x)
      have d := hcong.2 hpx'
      rcases hT with h | h <;> rw [h] at d
      · left
        have d2 := dvd_add d hm
        rwa [show (p' : ℤ) * g.1 + p * g.2 - bT p p' x₀ i + (bT p p' x₀ i - x₀) =
          (p' : ℤ) * g.1 + p * g.2 - x₀ by ring] at d2
      · right
        have d2 := dvd_sub d hm
        rwa [show (p' : ℤ) * g.1 + p * g.2 - -bT p p' x₀ i - (bT p p' x₀ i - x₀) =
          (p' : ℤ) * g.1 + p * g.2 + x₀ by ring] at d2
  obtain ⟨m, hm⟩ := exists_bM hB hy0 hN
  refine ⟨m, ?_, (lvl_iff hB g m).2 (by rw [hm])⟩
  by_contra hc
  push_neg at hc
  have hle : (bM p p' x₀ m : ℤ) ≤ bM p p' x₀ i := by exact_mod_cast (bM_strictMono hB).monotone hc
  have habs : |(p' : ℤ) * g.1 - p * g.2| = bM p p' x₀ i := by
    rw [bM_abs hB]
    rcases hT with h | h <;> rw [h]
    exact abs_neg _
  have : |(p' : ℤ) * g.1 - p * g.2| < (p' : ℤ) * g.1 + p * g.2 := by
    rw [abs_lt]; constructor <;> nlinarith [show (0 : ℤ) < g.1 by exact_mod_cast h1,
      show (0 : ℤ) < g.2 by exact_mod_cast h2, show (0 : ℤ) < p by have := hB.1; omega,
      show (0 : ℤ) < p' by have := hB.2.1; omega]
  omega

end Labels

end Virasoro
