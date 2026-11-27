import Virasoro.Proofs.Sec8BNodes
import Virasoro.Proofs.Sec8DiagPoles

/-!
# Lemma 8.10 (`lem:boundary-labels`)

If `p ∣ x_g` then `y_g ≡ -x_g (mod N₀)`, if `p' ∣ x_g` then `y_g ≡ x_g (mod N₀)`.  A label of weight
`μ_i` has `x_g = ±T_i`, so `y_g ≡ -ε x_g`, and `y_g > |x_g|` makes `y_g = M_k` with `k > i`; for given
`k` the sign is fixed since `2x₀ ≢ 0 (mod N₀)`.  The pole order of `𝒜_g` is
`#{i' ≥ 1 : i'N₀ ≤ M_k - M_i} + #{i' ≥ 1 : i'N₀ < M_k - M_i} = Δ - 1`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- The lattice points `i(p, p')` in the box of `𝒜_{u,v}`: `m₁` positive and `m₂` negative
multiples. -/
theorem box_count {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') (hcop : Nat.Coprime p p') {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hx0 : (p' : ℤ) * u - p * v ≠ 0) (m₁ m₂ : ℕ)
    (B1 : ∀ i : ℤ, 0 < i → (2 * (i * ((p : ℤ) * p')) ≤ 2 * p' * u ∧
      2 * (i * ((p : ℤ) * p')) ≤ 2 * p * v ↔ i ≤ m₁))
    (B2 : ∀ i : ℤ, 0 < i → (2 * (i * ((p : ℤ) * p')) < 2 * p' * u ∧
      2 * (i * ((p : ℤ) * p')) < 2 * p * v ↔ i ≤ m₂)) :
    ((genAIndex u v).filter (fun pq => (p : ℤ) * pq.2 = p' * pq.1)).card = m₁ + m₂ := by
  have hcop' : IsCoprime (p : ℤ) p' := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
  have sp : (0 : ℤ) < 2 * p := by positivity
  have sp' : (0 : ℤ) < 2 * p' := by positivity
  have hscale1 : ∀ i : ℤ, 2 * p' * (i * p) = 2 * (i * ((p : ℤ) * p')) := fun i => by ring
  have hscale2 : ∀ i : ℤ, 2 * p * (i * p') = 2 * (i * ((p : ℤ) * p')) := fun i => by ring
  have key : (genAIndex u v).filter (fun pq => (p : ℤ) * pq.2 = p' * pq.1) =
      ((Finset.Icc (-(m₂ : ℤ)) m₁).erase 0).image (fun i : ℤ => (i * p, i * p')) := by
    ext ⟨a, c⟩
    simp only [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_image, Finset.mem_erase, ne_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨ha1, ha2⟩, hc1, hc2⟩, h0, huv⟩, hline⟩
      obtain ⟨i, rfl⟩ := hcop'.dvd_of_dvd_mul_left (show (p : ℤ) ∣ p' * a from ⟨c, by linarith⟩)
      have hci : c = i * p' := by
        have : (p : ℤ) * c = p * (i * p') := by rw [hline]; ring
        exact mul_left_cancel₀ (by exact_mod_cast hp.ne') this
      subst hci
      have hi0 : i ≠ 0 := by rintro rfl; exact h0 (by simp)
      have ha2' : i * p ≤ u := by rw [mul_comm] at ha2; exact ha2
      have ha1' : 1 - (u : ℤ) ≤ i * p := by rw [mul_comm] at ha1; exact ha1
      refine ⟨i, ⟨hi0, ?_, ?_⟩, by ring, rfl⟩
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have hj : 0 < -i := by omega
          have k1 : 2 * ((-i) * ((p : ℤ) * p')) < 2 * p' * u := by
            have : (-i) * p < u := by linarith
            have := mul_lt_mul_of_pos_left this sp'
            rw [hscale1] at this; exact this
          have k2 : 2 * ((-i) * ((p : ℤ) * p')) < 2 * p * v := by
            have : (-i) * p' < v := by linarith
            have := mul_lt_mul_of_pos_left this sp
            rw [hscale2] at this; exact this
          have := (B2 (-i) hj).1 ⟨k1, k2⟩
          omega
        · omega
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · omega
        · have k1 : 2 * (i * ((p : ℤ) * p')) ≤ 2 * p' * u := by
            have := mul_le_mul_of_nonneg_left ha2' sp'.le
            rw [hscale1] at this; exact this
          have k2 : 2 * (i * ((p : ℤ) * p')) ≤ 2 * p * v := by
            have := mul_le_mul_of_nonneg_left hc2 sp.le
            rw [hscale2] at this; exact this
          exact (B1 i hpos).1 ⟨k1, k2⟩
    · rintro ⟨i, ⟨hi0, hi1, hi2⟩, rfl, rfl⟩
      have hpu : (0 : ℤ) < u := by exact_mod_cast hu
      have hpv : (0 : ℤ) < v := by exact_mod_cast hv
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, by ring⟩
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have hj : 0 < -i := by omega
          have k := ((B2 (-i) hj).2 (by omega)).1
          rw [← hscale1] at k
          have := lt_of_mul_lt_mul_left k sp'.le
          linarith [mul_comm i (p : ℤ)]
        · have : 0 < i * p := mul_pos hpos (by exact_mod_cast hp)
          linarith [mul_comm i (p : ℤ)]
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have : i * p < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast hp)
          linarith [mul_comm i (p : ℤ)]
        · have k := ((B1 i hpos).2 hi2).1
          rw [← hscale1] at k
          have := le_of_mul_le_mul_left k sp'
          linarith [mul_comm i (p : ℤ)]
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have hj : 0 < -i := by omega
          have k := ((B2 (-i) hj).2 (by omega)).2
          rw [← hscale2] at k
          have := lt_of_mul_lt_mul_left k sp.le
          linarith
        · have : 0 < i * p' := mul_pos hpos (by exact_mod_cast hp')
          linarith
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have : i * p' < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast hp')
          linarith
        · have k := ((B1 i hpos).2 hi2).2
          rw [← hscale2] at k
          exact le_of_mul_le_mul_left k sp
      · rintro ⟨h1', h2'⟩
        exact hi0 (by rcases mul_eq_zero.1 (show (p : ℤ) * i = 0 by linarith) with h | h
                      · exact absurd h (by exact_mod_cast hp.ne')
                      · exact h)
      · rintro ⟨h1', h2'⟩
        apply hx0
        rw [← h1', ← h2']; ring
  rw [key, Finset.card_image_of_injective]
  · rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
    omega
  · intro i i' h
    simp only [Prod.mk.injEq] at h
    exact mul_right_cancel₀ (by exact_mod_cast hp.ne') h.1

/-- The bounds for an even gap `y - |x| = 2mP`. -/
theorem box_line_bounds_even {P U V x y : ℤ} {m : ℕ} (hP : 0 < P) (hU : U = y + x) (hV : V = y - x)
    (hgap : y - |x| = 2 * m * P) (hx : x ≠ 0) (hm : 1 ≤ m) :
    (∀ i : ℤ, 0 < i → (2 * (i * P) ≤ U ∧ 2 * (i * P) ≤ V ↔ i ≤ m)) ∧
    (∀ i : ℤ, 0 < i → (2 * (i * P) < U ∧ 2 * (i * P) < V ↔ i ≤ ((m - 1 : ℕ) : ℤ))) := by
  have hm' : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hm']
  have hUx : y - |x| ≤ U := by rw [hU]; linarith [neg_abs_le x]
  have hVx : y - |x| ≤ V := by rw [hV]; linarith [le_abs_self x]
  have habs : 0 < |x| := abs_pos.2 hx
  have hmin : (U = y - |x| ∧ y - |x| < V) ∨ (V = y - |x| ∧ y - |x| < U) := by
    rcases abs_cases x with ⟨h, h'⟩ | ⟨h, h'⟩
    · right; refine ⟨by rw [hV, h], by rw [hU, h]; linarith⟩
    · left; refine ⟨by rw [hU, h]; ring, by rw [hV, h]; linarith⟩
  refine ⟨fun i _ => ⟨fun ⟨h1, h2⟩ => ?_, fun hi => ?_⟩, fun i _ => ⟨fun ⟨h1, h2⟩ => ?_, fun hi => ?_⟩⟩
  · by_contra hc; push_neg at hc
    have : ((m : ℤ) + 1) * P ≤ i * P := mul_le_mul_of_nonneg_right (by omega) hP.le
    rcases hmin with ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith
  · have : i * P ≤ (m : ℤ) * P := mul_le_mul_of_nonneg_right hi hP.le
    exact ⟨by linarith, by linarith⟩
  · by_contra hc; push_neg at hc
    have : (m : ℤ) * P ≤ i * P := mul_le_mul_of_nonneg_right (by omega) hP.le
    rcases hmin with ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith
  · have : i * P ≤ ((m : ℤ) - 1) * P := mul_le_mul_of_nonneg_right hi hP.le
    exact ⟨by linarith, by linarith⟩

variable {p p' x₀ : ℕ} {b : ℂ}

section Labels

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem bM_sq (k : ℕ) : (bM p p' x₀ k : ℤ) ^ 2 = bT p p' x₀ k ^ 2 := by
  rw [bM_sgn hB]; split_ifs <;> ring

theorem bM_abs (k : ℕ) : (bM p p' x₀ k : ℤ) = |bT p p' x₀ k| := by
  unfold bM; exact Int.natCast_natAbs _

theorem dvd_bT_p : ((p : ℤ) ∣ bT p p' x₀ i ↔ p ∣ x₀) := by
  unfold bT
  constructor
  · intro h
    have : (p : ℤ) ∣ x₀ := by
      have h2 : (p : ℤ) ∣ bPi i * (2 * p * p') := ⟨bPi i * 2 * p', by ring⟩
      have := dvd_sub h h2
      simpa using this
    exact_mod_cast this
  · intro h
    exact dvd_add (by exact_mod_cast h) ⟨bPi i * 2 * p', by ring⟩

theorem dvd_bT_p' : ((p' : ℤ) ∣ bT p p' x₀ i ↔ p' ∣ x₀) := by
  unfold bT
  constructor
  · intro h
    have : (p' : ℤ) ∣ x₀ := by
      have h2 : (p' : ℤ) ∣ bPi i * (2 * p * p') := ⟨bPi i * 2 * p, by ring⟩
      have := dvd_sub h h2
      simpa using this
    exact_mod_cast this
  · intro h
    exact dvd_add (by exact_mod_cast h) ⟨bPi i * 2 * p, by ring⟩

/-- `N₀ ∤ 2x₀`. -/
theorem not_dvd_two_x₀ : ¬ (2 * (p : ℤ) * p') ∣ 2 * x₀ := by
  intro h
  have h0 := hB.2.2.2.1
  have h1 := hB.2.2.2.2.1
  have := Int.le_of_dvd (by positivity) h
  have : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
  linarith

/-- The congruences of a label: `p ∣ x_g ⇒ N₀ ∣ y_g + x_g`, `p' ∣ x_g ⇒ N₀ ∣ y_g - x_g`. -/
theorem label_cong {u v : ℕ} :
    ((p : ℤ) ∣ (p' : ℤ) * u - p * v → (2 * (p : ℤ) * p') ∣ ((p' : ℤ) * u + p * v) + ((p' : ℤ) * u - p * v)) ∧
    ((p' : ℤ) ∣ (p' : ℤ) * u - p * v → (2 * (p : ℤ) * p') ∣ ((p' : ℤ) * u + p * v) - ((p' : ℤ) * u - p * v)) := by
  have hcop : IsCoprime (p : ℤ) p' := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hB.2.2.1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : (p : ℤ) ∣ p' * u := by
      have := dvd_add h (show (p : ℤ) ∣ p * v from ⟨v, rfl⟩)
      simpa using this
    obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left h2
    exact ⟨t, by rw [show (p' : ℤ) * u + p * v + ((p' : ℤ) * u - p * v) = 2 * p' * u by ring, ht]; ring⟩
  · have h2 : (p' : ℤ) ∣ p * v := by
      have := dvd_sub (show (p' : ℤ) ∣ p' * u from ⟨u, rfl⟩) h
      simpa using this
    obtain ⟨t, ht⟩ := hcop.symm.dvd_of_dvd_mul_left h2
    exact ⟨t, by rw [show (p' : ℤ) * u + p * v - ((p' : ℤ) * u - p * v) = 2 * p * v by ring, ht]; ring⟩

/-- The two sums `y ± x` of the label `bLabel i k` are divisible by `2p'`, resp. `2p`, and positive. -/
theorem bLabel_xy {i k : ℕ} (hik : i < k) :
    0 < (bLabel p p' x₀ i k).1 ∧ 0 < (bLabel p p' x₀ i k).2 ∧
      (p' : ℤ) * (bLabel p p' x₀ i k).1 + p * (bLabel p p' x₀ i k).2 = bM p p' x₀ k ∧
      (p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 =
        -bEps p x₀ * (if 0 < bT p p' x₀ k then 1 else -1) * bT p p' x₀ i := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = bM p p' x₀ k := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = -bEps p x₀ * (if 0 < bT p p' x₀ k then 1 else -1) * bT p p' x₀ i :=
    ⟨_, rfl⟩
  have hMk := bM_sgn hB k
  have hMi := bM_abs hB i
  have hlt : (bM p p' x₀ i : ℤ) < bM p p' x₀ k := by exact_mod_cast bM_strictMono hB hik
  have hXabs : |X| = bM p p' x₀ i := by
    rw [hX, hMi, abs_mul, abs_mul, abs_neg]
    unfold bEps; split_ifs <;> simp
  have hpos1 : 0 < X + Y := by have := neg_abs_le X; rw [hXabs] at this; omega
  have hpos2 : 0 < Y - X := by have := le_abs_self X; rw [hXabs] at this; omega
  -- `T_k - T_i` and `T_k + T_i - 2x₀` are multiples of `N₀`
  have hdiff : bT p p' x₀ k - bT p p' x₀ i = (bPi k - bPi i) * (2 * p * p') := by unfold bT; ring
  have hsum : bT p p' x₀ k + bT p p' x₀ i = 2 * x₀ + (bPi k + bPi i) * (2 * p * p') := by
    unfold bT; ring
  have hdiv : (2 * (p' : ℤ)) ∣ X + Y ∧ (2 * (p : ℤ)) ∣ Y - X := by
    rw [hX, hY, hMk]
    unfold bEps
    by_cases hpx : p ∣ x₀
    · obtain ⟨c, hc⟩ := hpx
      rw [if_pos ⟨c, hc⟩]
      split_ifs
      · refine ⟨⟨(bPi k - bPi i) * p, ?_⟩, ⟨c + (bPi k + bPi i) * p', ?_⟩⟩
        · linear_combination hdiff
        · have : (x₀ : ℤ) = p * c := by exact_mod_cast hc
          linear_combination hsum + 2 * this
      · refine ⟨⟨-(bPi k - bPi i) * p, ?_⟩, ⟨-(c + (bPi k + bPi i) * p'), ?_⟩⟩
        · linear_combination -hdiff
        · have : (x₀ : ℤ) = p * c := by exact_mod_cast hc
          linear_combination -hsum - 2 * this
    · have hp'x : p' ∣ x₀ := by have := hB.2.2.2.2.2.1; tauto
      obtain ⟨c, hc⟩ := hp'x
      rw [if_neg hpx]
      have : (x₀ : ℤ) = p' * c := by exact_mod_cast hc
      split_ifs
      · refine ⟨⟨c + (bPi k + bPi i) * p, ?_⟩, ⟨(bPi k - bPi i) * p', ?_⟩⟩
        · linear_combination hsum + 2 * this
        · linear_combination hdiff
      · refine ⟨⟨-(c + (bPi k + bPi i) * p), ?_⟩, ⟨-(bPi k - bPi i) * p', ?_⟩⟩
        · linear_combination -hsum - 2 * this
        · linear_combination -hdiff
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hdiv
  have hu0 : 0 < u := by
    have : (0 : ℤ) < 2 * p' * u := by rw [← hu]; exact hpos1
    exact pos_of_mul_pos_right this (by positivity)
  have hv0 : 0 < v := by
    have : (0 : ℤ) < 2 * p * v := by rw [← hv]; exact hpos2
    exact pos_of_mul_pos_right this (by positivity)
  have h1 : (bLabel p p' x₀ i k).1 = u.toNat := by
    unfold bLabel
    dsimp only
    rw [← hX, ← hY, hu, Int.mul_ediv_cancel_left _ (by positivity)]
  have h2 : (bLabel p p' x₀ i k).2 = v.toNat := by
    unfold bLabel
    dsimp only
    rw [← hX, ← hY, hv, Int.mul_ediv_cancel_left _ (by positivity)]
  rw [h1, h2, Int.toNat_of_nonneg hu0.le, Int.toNat_of_nonneg hv0.le, ← hY, ← hX]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · linarith
  · linarith

end Labels

end Virasoro
