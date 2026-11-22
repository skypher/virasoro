import Virasoro.Proofs.Sec6ChainEvenSteps

/-!
# Proposition 6.7, `k = 2q + 2`: the tail after `κ = g_q` (paper.tex l.1167–1169)

The chains of level `ℓ^±_{2(q+1)}` through `g_q` consist of `g_q` followed by the single step
`gEnd` to the endpoint: their sum is `(ḣ_κ − ḣ_g)⁻¹ ρ_g y` (the box of `gEnd` meets `ℤ(p,p')` only
at `0`), and `ρ_g/(ḣ_κ − ḣ_g) = −2p'²/((p'−p)(q+1)N₀)`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

theorem Setup.gEnd_mom (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (p' : ℤ) * (gEnd p p' r s q σ).1 + (p : ℤ) * (gEnd p p' r s q σ).2 =
        σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' ∧
      (p' : ℤ) * (gEnd p p' r s q σ).1 - (p : ℤ) * (gEnd p p' r s q σ).2 =
        σ * (n1 p p' r s + q * N0 p p') := by
  rcases hσ with rfl | rfl
  · rw [gEnd, if_pos rfl]
    dsimp only
    push_cast
    rw [Nat.cast_sub h.hsp.le]
    unfold n0 n1 N0
    constructor <;> ring
  · rw [gEnd, if_neg (by norm_num)]
    dsimp only
    push_cast
    rw [Nat.cast_sub h.hrp.le]
    unfold n0 n1 N0
    constructor <;> ring

theorem Setup.gEnd_pos (h : Setup p p' r s) (q : ℕ) (σ : ℤ) :
    1 ≤ (gEnd p p' r s q σ).1 ∧ 1 ≤ (gEnd p p' r s q σ).2 := by
  have := h.hr
  have := h.hs
  have := h.hrp
  have := h.hsp
  unfold gEnd
  split_ifs
  · exact ⟨Nat.le_add_right_of_le h.hr, by omega⟩
  · exact ⟨by omega, Nat.le_add_right_of_le h.hs⟩

/-- The box of `gEnd` meets `ℤ(p,p')` only at `0` (paper.tex l.1167–1168). -/
theorem Setup.box_gEnd (h : Setup p p' r s) (q : ℕ) (σ : ℤ) :
    boxMults p p' (gEnd p p' r s q σ) = ∅ := by
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast h.hp
  have hp' : (2 : ℤ) ≤ p' := by exact_mod_cast h.hp'
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hs : (0 : ℤ) < s := by exact_mod_cast h.hs
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have hsp : (s : ℤ) < p' := by exact_mod_cast h.hsp
  ext j'
  simp only [boxMults, mem_filter, mem_Icc, notMem_empty, iff_false, not_and]
  intro _ h0 h1 h2 h3 h4
  unfold gEnd at h1 h2 h3 h4
  split_ifs at h1 h2 h3 h4
  · dsimp only at h3 h4
    rw [Nat.cast_sub h.hsp.le] at h3 h4
    rcases lt_trichotomy j' 0 with hj | hj | hj
    · have : j' * p' ≤ -1 * p' := mul_le_mul_of_nonneg_right (by omega) (by linarith)
      linarith
    · exact h0 hj
    · have : 1 * p' ≤ j' * p' := mul_le_mul_of_nonneg_right (by omega) (by linarith)
      linarith
  · dsimp only at h1 h2
    rw [Nat.cast_sub h.hrp.le] at h1 h2
    rcases lt_trichotomy j' 0 with hj | hj | hj
    · have : j' * p ≤ -1 * p := mul_le_mul_of_nonneg_right (by omega) (by linarith)
      linarith
    · exact h0 hj
    · have : 1 * p ≤ j' * p := mul_le_mul_of_nonneg_right (by omega) (by linarith)
      linarith

theorem Setup.resLimit_gEnd (h : Setup p p' r s) (q : ℕ) (σ : ℤ) :
    resLimit p p' (gEnd p p' r s q σ) = C (rhoG p p' (gEnd p p' r s q σ)) * X := by
  rw [resLimit, h.box_gEnd, prod_empty, mul_one]

/-- The level of `κ = g_q` lies below the level of the endpoint. -/
theorem Setup.lvl_gq_lt (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (L : ℕ)
    (hL : 2 * N0 p p' * (L : ℤ) =
      (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - n0 p p' r s ^ 2) :
    (gL p p' r s q).lvl < L ∧
      2 * N0 p p' * (((L - (gL p p' r s q).lvl : ℕ) : ℤ)) =
        (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - (n1 p p' r s + q * N0 p p') ^ 2 := by
  have hN := h.N0_pos
  have hd := h.diff_pos
  have hd' := h.diff_lt
  have hs := h.sum_pos
  have hs' := h.sum_lt
  have hn := h.n1_pos
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have l2 := h.lvl_gL (q : ℤ)
  have hX : 0 < n1 p p' r s + q * N0 p p' := by positivity
  have hXm : n1 p p' r s + q * N0 p p' < σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' := by
    rcases hσ with rfl | rfl <;> linarith
  have hsq : (n1 p p' r s + q * N0 p p') ^ 2 < (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 :=
    pow_lt_pow_left₀ hXm hX.le (by norm_num)
  have hlt : ((gL p p' r s q).lvl : ℤ) < L := by
    have : 2 * N0 p p' * ((gL p p' r s q).lvl : ℤ) < 2 * N0 p p' * (L : ℤ) := by
      rw [hL, l2]
      linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hlt' : (gL p p' r s q).lvl < L := by exact_mod_cast hlt
  refine ⟨hlt', ?_⟩
  rw [Nat.cast_sub hlt'.le, mul_sub, hL, l2]
  ring

/-- The tail after `κ = g_q`: only the step `gEnd` to the endpoint contributes. -/
theorem Setup.tail_even (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (L : ℕ)
    (hL : 2 * N0 p p' * (L : ℤ) =
      (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - n0 p p' r s ^ 2) (f : ℕ) :
    chainTc p p' (f + 1) (L - (gL p p' r s q).lvl)
        (((p' : ℤ) * (gL p p' r s q).1 + (p : ℤ) * (gL p p' r s q).2) ^ 2)
        (hdotNu p p' (gL p p' r s q)) =
      C ((hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ))⁻¹) *
        resLimit p p' (gEnd p p' r s q σ) := by
  have hN := h.N0_pos
  have hn := h.n1_pos
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  obtain ⟨hlt, hL'⟩ := h.lvl_gq_lt q σ hσ L hL
  have hsum := h.gL_sum (q : ℤ)
  have hsg : sgnI (q : ℤ) = 1 := by rw [sgnI, if_pos hq]
  rw [hsg, one_mul] at hsum
  set L' := L - (gL p p' r s q).lvl with hL'def
  have hL'0 : L' ≠ 0 := by omega
  obtain ⟨hEm, hEd⟩ := h.gEnd_mom q σ hσ
  have hEl : (gEnd p p' r s q σ).lvl = L' := by
    have e1 := lvl_eq p p' (gEnd p p' r s q σ)
    rw [hEm, hEd] at e1
    have : 2 * N0 p p' * ((gEnd p p' r s q σ).lvl : ℤ) = 2 * N0 p p' * (L' : ℤ) := by
      rw [e1, hL']
      rcases hσ with rfl | rfl <;> ring
    have := mul_left_cancel₀ (by positivity : (2 : ℤ) * N0 p p' ≠ 0) this
    exact_mod_cast this
  have hEmem : gEnd p p' r s q σ ∈ labels L' := by
    rw [mem_labels_iff]
    exact ⟨(h.gEnd_pos q σ).1, (h.gEnd_pos q σ).2, hEl.le⟩
  have hEc : ((p' : ℤ) * (gEnd p p' r s q σ).1 - (p : ℤ) * (gEnd p p' r s q σ).2) ^ 2 =
      ((p' : ℤ) * (gL p p' r s q).1 + (p : ℤ) * (gL p p' r s q).2) ^ 2 := by
    rw [hEd, hsum]
    rcases hσ with rfl | rfl <;> ring
  rw [chainTc, if_neg hL'0]
  rw [sum_eq_single (gEnd p p' r s q σ)]
  · rw [if_pos hEc, hEl, Nat.sub_self, chainTc_zero_level, mul_one]
  · intro b hb hne
    split_ifs with hc
    · rw [mem_labels_iff] at hb
      obtain ⟨hb1, hb2, hb3⟩ := hb
      have hy := lvl_eq p p' b
      rw [hc, hsum] at hy
      have hb3' : (b.lvl : ℤ) ≤ L' := by exact_mod_cast hb3
      have hlv : 1 ≤ (b.lvl : ℤ) := by
        have := Nat.mul_le_mul hb1 hb2
        unfold Label.lvl
        exact_mod_cast this
      have hA := mul_le_mul_of_nonneg_left hb3' (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
      have hA' := mul_le_mul_of_nonneg_left hlv (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
      have hu : (0 : ℤ) < b.1 := by exact_mod_cast hb1
      have hv : (0 : ℤ) < b.2 := by exact_mod_cast hb2
      have hp0 : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
      have hp0' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
      have hpos : 0 < (p' : ℤ) * b.1 + (p : ℤ) * b.2 := by
        have := mul_pos hp0' hu
        have := mul_pos hp0 hv
        linarith
      have hX : 0 ≤ n1 p p' r s + q * N0 p p' := by positivity
      have hm : 0 ≤ σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' := by
        have h6 := h.two_n0_lt
        have h7 := h.neg_two_n0_lt
        have h8 : N0 p p' ≤ ((q : ℤ) + 1) * N0 p p' := le_mul_of_one_le_left hN.le (by linarith)
        rcases hσ with rfl | rfl
        · linarith only [h6, h7, h8]
        · linarith only [h6, h7, h8]
      have hup : ((p' : ℤ) * b.1 + (p : ℤ) * b.2) ^ 2 ≤
          (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 := by
        linarith only [hy, hA, hL']
      have hlo : (n1 p p' r s + q * N0 p p') ^ 2 < ((p' : ℤ) * b.1 + (p : ℤ) * b.2) ^ 2 := by
        linarith only [hy, hA', hN]
      have hY1 := (abs_le_of_sq_le_sq' hup hm).2
      have hY2 := (abs_lt_of_sq_lt_sq' hlo hpos.le).2
      rcases h.second_step q σ hσ b hc hY2 hY1 with ⟨_, hbE⟩ | ⟨hyb, hσn⟩
      · exact absurd hbE hne
      · -- the chains through `b` are dead
        have hblt : b.lvl < L' := by
          by_contra hge
          have hge : (L' : ℤ) ≤ b.lvl := by exact_mod_cast not_lt.1 hge
          have := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
          rw [hL'] at this
          have h9 : (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 ≤
              ((p' : ℤ) * b.1 + (p : ℤ) * b.2) ^ 2 := by linarith only [this, hy]
          rw [hyb] at h9
          have h5 : 0 ≤ -σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p' := by rw [← hyb]; exact hpos.le
          have h10 := (abs_le_of_sq_le_sq' h9 h5).2
          linarith only [h10, hσn]
        have hdead : chainTc p p' f (L' - b.lvl) (((p' : ℤ) * b.1 + (p : ℤ) * b.2) ^ 2)
            (hdotNu p p' b) = 0 := by
          apply chainTc_eq_zero
          · omega
          · intro c hcl he
            rw [mem_labels_iff] at hcl
            obtain ⟨hc1, hc2, hc3⟩ := hcl
            have hz := lvl_eq p p' c
            rw [he] at hz
            have hc3' : (c.lvl : ℤ) ≤ L' - b.lvl := by
              have : c.lvl ≤ L' - b.lvl := hc3
              omega
            have hcv : 1 ≤ (c.lvl : ℤ) := by
              have := Nat.mul_le_mul hc1 hc2
              unfold Label.lvl
              exact_mod_cast this
            have hB := mul_le_mul_of_nonneg_left hc3' (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
            have hB' := mul_le_mul_of_nonneg_left hcv (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
            have hcu : (1 : ℤ) ≤ c.1 := by exact_mod_cast hc1
            have hcw : (1 : ℤ) ≤ c.2 := by exact_mod_cast hc2
            have hzpos : 0 < (p' : ℤ) * c.1 + (p : ℤ) * c.2 := by
              have := mul_pos hp0' (by linarith : (0 : ℤ) < c.1)
              have := mul_pos hp0 (by linarith : (0 : ℤ) < c.2)
              linarith
            have hzup : ((p' : ℤ) * c.1 + (p : ℤ) * c.2) ^ 2 ≤
                (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 := by
              rw [mul_sub] at hB
              linarith only [hB, hz, hy, hL']
            have hzlo : ((p' : ℤ) * b.1 + (p : ℤ) * b.2) ^ 2 < ((p' : ℤ) * c.1 + (p : ℤ) * c.2) ^ 2 := by
              linarith only [hz, hB', hN]
            have hZ1 := (abs_le_of_sq_le_sq' hzup hm).2
            have hZ2 := (abs_lt_of_sq_lt_sq' hzlo hzpos.le).2
            rw [hyb] at hZ2
            have hbX : (p' : ℤ) * b.1 - (p : ℤ) * b.2 = n1 p p' r s + q * N0 p p' ∨
                (p' : ℤ) * b.1 - (p : ℤ) * b.2 = -(n1 p p' r s + q * N0 p p') := by
              rw [hsum] at hc
              exact sq_eq_sq_iff_eq_or_eq_neg.1 hc
            obtain ⟨i', hi' | hi'⟩ := h.next_mom he
            all_goals rcases hbX with hbX | hbX
            all_goals rw [hbX] at hi'
            · exact h.no_mom_gap2 q σ 1 (q + i') hσ (Or.inl rfl) hσn
                (by rw [one_mul]; linarith) (by rw [one_mul]; linarith)
            · exact h.no_mom_gap2 q σ (-1) (i' - q) hσ (Or.inr rfl) hσn
                (by linarith) (by linarith)
            · exact h.no_mom_gap2 q σ (-1) (i' - q) hσ (Or.inr rfl) hσn
                (by linarith) (by linarith)
            · exact h.no_mom_gap2 q σ 1 (q + i') hσ (Or.inl rfl) hσn
                (by rw [one_mul]; linarith) (by rw [one_mul]; linarith)
        rw [hdead, mul_zero]
    · rfl
  · intro hE
    exact absurd hEmem hE

end Virasoro.ChainEval
