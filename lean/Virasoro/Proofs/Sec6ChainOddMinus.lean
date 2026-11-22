import Virasoro.Proofs.Sec6ChainOddPlus

/-!
# Proposition 6.7, the evaluation for `ℓ⁻_k`, `k = 2j + 1` (paper.tex l.1157–1166)

For `k = 2j+1` the minus endpoint is `n₁ − (j+1)N₀`, reached from `λ` in one step by
`g_{−(j+1)} = ((j+1)p − r, (j+1)p' − s)`.  Under `n₁ < pp'` the first steps at level `ℓ⁻_k` are
the `g_i` with `−(j+1) ≤ i ≤ j`; the chains from `g_j` do not reach the endpoint (l.1159–1160:
the first steps of the chains ending there are `−j−1 ≤ i ≤ j−1`), so its coefficient vanishes
and the `k` remaining slopes enter the moment argument with `κ = g_{−(j+1)}`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

theorem gL_negSucc (p p' r s j : ℕ) :
    gL p p' r s (-((j : ℤ) + 1)) = ((j + 1) * p - r, (j + 1) * p' - s) := by
  rw [gL, if_neg (by omega)]
  rw [show (-(-((j : ℤ) + 1))).toNat = j + 1 by omega]

theorem Setup.n1_sub_n0 (h : Setup p p' r s) : 0 < n1 p p' r s - n0 p p' r s := h.diff_pos

theorem Setup.n1_add_n0 (h : Setup p p' r s) : 0 < n1 p p' r s + n0 p p' r s := h.sum_pos

/-- The momentum of a step after a step `(u₁,v₁)`: `p'u + pv = ±(p'u₁ − pv₁) + iN₀`. -/
theorem Setup.next_mom (h : Setup p p' r s) {u v u1 v1 : ℤ}
    (he : ((p' : ℤ) * u - (p : ℤ) * v) ^ 2 = ((p' : ℤ) * u1 + (p : ℤ) * v1) ^ 2) :
    ∃ i : ℤ, (p' : ℤ) * u + p * v = ((p' : ℤ) * u1 - p * v1) + i * N0 p p' ∨
      (p' : ℤ) * u + p * v = -((p' : ℤ) * u1 - p * v1) + i * N0 p p' := by
  obtain ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h.next_step he
  · exact ⟨i, Or.inl (by rw [h1, h2]; unfold N0; ring)⟩
  · exact ⟨i, Or.inr (by rw [h1, h2]; unfold N0; ring)⟩

/-- The first steps at level `ℓ_{g_{−(j+1)}}` are the `g_i`, `−(j+1) ≤ i ≤ j`. -/
theorem Setup.mem_firstSteps_oddm (h : Setup p p' r s) (hlt : 2 * n1 p p' r s < N0 p p')
    (j : ℕ) (i : ℤ) :
    gL p p' r s i ∈ firstSteps p p' (gL p p' r s (-((j : ℤ) + 1))).lvl
        (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) ↔
      -((j : ℤ) + 1) ≤ i ∧ i ≤ j := by
  rw [h.gL_mem]
  have hl := h.lvl_gL (-((j : ℤ) + 1))
  have hN := h.N0_pos
  have hn := h.n1_pos
  have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have key : (n1 p p' r s + i * N0 p p') ^ 2 ≤ n0 p p' r s ^ 2 + 2 * N0 p p' *
      ((gL p p' r s (-((j : ℤ) + 1))).lvl : ℤ) ↔
      (n1 p p' r s + i * N0 p p') ^ 2 ≤ ((j + 1) * N0 p p' - n1 p p' r s) ^ 2 := by
    rw [hl]
    constructor <;> intro hh <;> nlinarith
  rw [key]
  have hb : 0 ≤ ((j : ℤ) + 1) * N0 p p' - n1 p p' r s := by nlinarith
  constructor
  · intro hh
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' hh hb
    constructor
    · by_contra hc
      have hc : i + ((j : ℤ) + 1) ≤ -1 := by omega
      have : (i + ((j : ℤ) + 1)) * N0 p p' ≤ -1 * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      nlinarith
    · by_contra hc
      have hc : (j : ℤ) + 1 ≤ i := by omega
      have : ((j : ℤ) + 1) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      nlinarith
  · rintro ⟨h1, h2⟩
    have h3 : i * N0 p p' ≤ j * N0 p p' := mul_le_mul_of_nonneg_right h2 hN.le
    have h4 : -((j : ℤ) + 1) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right h1 hN.le
    apply sq_le_sq'
    · nlinarith
    · nlinarith

/-- A momentum `y = ±n₀ + iN₀` cannot lie in `(n₁ + jN₀, (j+1)N₀ − n₁]`. -/
theorem Setup.no_mom_gap (h : Setup p p' r s) (j : ℕ) (σ i : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (h1 : n1 p p' r s + j * N0 p p' < σ * n0 p p' r s + i * N0 p p')
    (h2 : σ * n0 p p' r s + i * N0 p p' ≤ ((j : ℤ) + 1) * N0 p p' - n1 p p' r s) : False := by
  have hN := h.N0_pos
  have hd := h.n1_sub_n0
  have hs := h.n1_add_n0
  have h3 : (j : ℤ) + 1 ≤ i := by
    by_contra hc
    have hc : i ≤ j := by omega
    have : i * N0 p p' ≤ j * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
    rcases hσ with rfl | rfl <;> linarith
  have : ((j : ℤ) + 1) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right h3 hN.le
  rcases hσ with rfl | rfl <;> linarith

/-- The chains of level `ℓ_{g_{−(j+1)}}` through `g_j` are dead: no step after `g_j` stays below
the level (no momentum `≡ ±n₀ mod N₀` lies in `(n₁ + jN₀, (j+1)N₀ − n₁]`). -/
theorem Setup.tail_dead_oddm (h : Setup p p' r s) (hlt : 2 * n1 p p' r s < N0 p p') (j fuel : ℕ) :
    chainTc p p' fuel ((gL p p' r s (-((j : ℤ) + 1))).lvl - (gL p p' r s j).lvl)
      (((p' : ℤ) * (gL p p' r s j).1 + (p : ℤ) * (gL p p' r s j).2) ^ 2)
      (hdotNu p p' (gL p p' r s j)) = 0 := by
  have hN := h.N0_pos
  have hn := h.n1_pos
  have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have l1 := h.lvl_gL (-((j : ℤ) + 1))
  have l2 := h.lvl_gL (j : ℤ)
  have hsum := h.gL_sum (j : ℤ)
  have hdif := h.gL_diff (j : ℤ)
  have hsg : sgnI (j : ℤ) = 1 := by rw [sgnI, if_pos hj]
  rw [hsg, one_mul] at hsum hdif
  have hgap : (n1 p p' r s + -((j : ℤ) + 1) * N0 p p') ^ 2 - (n1 p p' r s + j * N0 p p') ^ 2 =
      (N0 p p' - 2 * n1 p p' r s) * ((2 * j + 1) * N0 p p') := by ring
  have hgap' : 0 < (N0 p p' - 2 * n1 p p' r s) * ((2 * j + 1) * N0 p p') :=
    mul_pos (by linarith) (by positivity)
  have hle : (gL p p' r s j).lvl < (gL p p' r s (-((j : ℤ) + 1))).lvl := by
    have : ((gL p p' r s j).lvl : ℤ) < (gL p p' r s (-((j : ℤ) + 1))).lvl := by
      have : 2 * N0 p p' * ((gL p p' r s j).lvl : ℤ) <
          2 * N0 p p' * ((gL p p' r s (-((j : ℤ) + 1))).lvl : ℤ) := by
        rw [l1, l2]
        linarith
      exact lt_of_mul_lt_mul_left this (by positivity)
    exact_mod_cast this
  apply chainTc_eq_zero
  · omega
  · intro g hg he
    rw [mem_labels_iff] at hg
    obtain ⟨hg1, hg2, hg3⟩ := hg
    have hy := lvl_eq p p' g
    rw [he, hsum] at hy
    have hg3' : (g.lvl : ℤ) ≤ (gL p p' r s (-((j : ℤ) + 1))).lvl - (gL p p' r s j).lvl := by
      have : g.lvl ≤ (gL p p' r s (-((j : ℤ) + 1))).lvl - (gL p p' r s j).lvl := hg3
      omega
    have hlv : 1 ≤ (g.lvl : ℤ) := by
      have := Nat.mul_le_mul hg1 hg2
      unfold Label.lvl
      exact_mod_cast this
    have hA := mul_le_mul_of_nonneg_left hg3' (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
    have hA' := mul_le_mul_of_nonneg_left hlv (by positivity : (0 : ℤ) ≤ 2 * N0 p p')
    have hu : (1 : ℤ) ≤ g.1 := by exact_mod_cast hg1
    have hv : (1 : ℤ) ≤ g.2 := by exact_mod_cast hg2
    have hp0 : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
    have hp0' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
    have hpos : 0 < (p' : ℤ) * g.1 + (p : ℤ) * g.2 := by nlinarith
    have hb : 0 ≤ ((j : ℤ) + 1) * N0 p p' - n1 p p' r s := by nlinarith
    set y := (p' : ℤ) * g.1 + (p : ℤ) * g.2 with hydef
    have hup : y ^ 2 ≤ (((j : ℤ) + 1) * N0 p p' - n1 p p' r s) ^ 2 := by
      have e1 : (((j : ℤ) + 1) * N0 p p' - n1 p p' r s) ^ 2 =
          (n1 p p' r s + -((j : ℤ) + 1) * N0 p p') ^ 2 := by ring
      rw [e1]
      rw [mul_sub] at hA
      linarith
    have hlo : (n1 p p' r s + j * N0 p p') ^ 2 < y ^ 2 := by linarith
    have hX : 0 ≤ n1 p p' r s + j * N0 p p' := by positivity
    have hY1 := (abs_le_of_sq_le_sq' hup hb).2
    have hY2 := (abs_lt_of_sq_lt_sq' hlo hpos.le).2
    obtain ⟨i, hi | hi⟩ := h.next_mom he
    · rw [hdif] at hi
      exact h.no_mom_gap j 1 i (Or.inl rfl) (by rw [one_mul, ← hi]; exact hY2)
        (by rw [one_mul, ← hi]; exact hY1)
    · rw [hdif] at hi
      exact h.no_mom_gap j (-1) i (Or.inr rfl) (by rw [neg_one_mul, ← hi]; exact hY2)
        (by rw [neg_one_mul, ← hi]; exact hY1)

/-- The box of `((j+1)p − r, (j+1)p' − s)` meets `ℤ(p,p')` at the `j' ≠ 0` with `|j'| ≤ j`
(paper.tex l.1165–1166). -/
theorem Setup.boxMults_minus (h : Setup p p' r s) (j : ℕ) :
    boxMults p p' ((j + 1) * p - r, (j + 1) * p' - s) = (Icc (-(j : ℤ)) j).erase 0 := by
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast h.hp
  have hp' : (2 : ℤ) ≤ p' := by exact_mod_cast h.hp'
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hs : (0 : ℤ) < s := by exact_mod_cast h.hs
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have hsp : (s : ℤ) < p' := by exact_mod_cast h.hsp
  have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hr1 : r ≤ (j + 1) * p := le_trans h.hrp.le (Nat.le_mul_of_pos_left _ (by omega))
  have hs1 : s ≤ (j + 1) * p' := le_trans h.hsp.le (Nat.le_mul_of_pos_left _ (by omega))
  ext j'
  simp only [boxMults, mem_filter, mem_Icc, mem_erase]
  rw [Nat.cast_sub hr1, Nat.cast_sub hs1]
  push_cast
  constructor
  · rintro ⟨_, h0, h1, h2, h3, h4⟩
    refine ⟨h0, ?_, ?_⟩
    · by_contra hc
      have hc : j' ≤ -((j : ℤ) + 1) := by omega
      have : j' * p ≤ -((j : ℤ) + 1) * p := mul_le_mul_of_nonneg_right hc (by linarith)
      nlinarith
    · by_contra hc
      have hc : (j : ℤ) + 1 ≤ j' := by omega
      have : ((j : ℤ) + 1) * p ≤ j' * p := mul_le_mul_of_nonneg_right hc (by linarith)
      nlinarith
  · rintro ⟨h0, h1, h2⟩
    have a1 : j' * p ≤ j * p := mul_le_mul_of_nonneg_right h2 (by linarith)
    have a2 : -(j : ℤ) * p ≤ j' * p := mul_le_mul_of_nonneg_right h1 (by linarith)
    have a3 : j' * p' ≤ j * p' := mul_le_mul_of_nonneg_right h2 (by linarith)
    have a4 : -(j : ℤ) * p' ≤ j' * p' := mul_le_mul_of_nonneg_right h1 (by linarith)
    refine ⟨⟨?_, ?_⟩, h0, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem Setup.box_value_m (h : Setup p p' r s) (j : ℕ) :
    ∏ b ∈ boxMults p p' (gL p p' r s (-((j : ℤ) + 1))), (-(((b : ℂ) * kappa0 p p')⁻¹)) =
      (-1) ^ j / (((j.factorial : ℕ) : ℂ) ^ 2 * kappa0 p p' ^ (2 * j)) := by
  rw [gL_negSucc, h.boxMults_minus j, prod_box]
  exact box_range_prod _ h.kappa0_ne j

theorem Setup.card_box_m (h : Setup p p' r s) (j : ℕ) :
    (boxMults p p' (gL p p' r s (-((j : ℤ) + 1)))).card = 2 * j := by
  rw [gL_negSucc, h.boxMults_minus j, card_erase_of_mem (by simp), Int.card_Icc]
  omega

/-- `∏_{0<t≤2j} (ḣ_{g_{−(j+1)}} − ḣ_{g_{t−(j+1)}}) = (n₀N₀/4p'²)^{2j} (2j)!`. -/
theorem Setup.slope_prod_m (h : Setup p p' r s) (j : ℕ) :
    ∏ t ∈ (range (2 * j + 1)).erase 0,
        (hdotNu p p' (gL p p' r s (-((j : ℤ) + 1))) -
          hdotNu p p' (gL p p' r s ((t : ℤ) - ((j : ℤ) + 1)))) =
      ((n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2)) ^ (2 * j) *
        (((2 * j).factorial : ℕ) : ℂ) := by
  have hE : (range (2 * j + 1)).erase 0 = Ico 1 (2 * j + 1) := by
    ext t
    simp only [mem_erase, mem_range, mem_Ico]
    omega
  have e : ∀ t ∈ Ico 1 (2 * j + 1),
      hdotNu p p' (gL p p' r s (-((j : ℤ) + 1))) -
          hdotNu p p' (gL p p' r s ((t : ℤ) - ((j : ℤ) + 1))) =
        (n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2) * (t : ℂ) := by
    intro t _
    rw [h.hdot_sub]
    push_cast
    ring
  rw [hE, prod_congr rfl e, prod_mul_distrib, prod_const, Nat.card_Ico,
    show 2 * j + 1 - 1 = 2 * j by omega]
  congr 1
  rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]

/-- Proposition 6.7 for `ℓ⁻_{2j+1}` under `n₁ < pp'` (paper.tex l.1157–1167). -/
theorem Setup.eval_minus_odd (h : Setup p p' r s) (hlt : 2 * n1 p p' r s < N0 p p') (j : ℕ)
    (a : ℂ) (e : RatFunc ℂ) (he : VanishesAtInfinity e)
    (hT : (chainTN p p' r s (ellMinus p p' r s (2 * j + 1))).coeff (2 * j + 1) *
        RatFunc.X ^ (2 * j + 1) = RatFunc.C a + e) :
    a = (layerConst (2 * j + 1) : ℂ) * (-rho p p' r s) ^ (2 * j + 1) := by
  have hE : ellMinus p p' r s (2 * j + 1) = (gL p p' r s (-((j : ℤ) + 1))).lvl := by
    rw [gL_negSucc]
    unfold ellMinus Label.lvl
    rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]
  obtain ⟨n, hn⟩ : ∃ n, (gL p p' r s (-((j : ℤ) + 1))).lvl = n + 1 := by
    refine ⟨(gL p p' r s (-((j : ℤ) + 1))).lvl - 1, ?_⟩
    have h1 := (h.gL_pos (-((j : ℤ) + 1))).1
    have h2 := (h.gL_pos (-((j : ℤ) + 1))).2
    have h3 := Nat.mul_le_mul h1 h2
    unfold Label.lvl
    omega
  rw [hE, hn, coeff_chainTN] at hT
  have hFS : firstSteps p p' (n + 1) (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) =
      (range (2 * j + 2)).image (fun t : ℕ => gL p p' r s ((t : ℤ) - ((j : ℤ) + 1))) := by
    ext g'
    rw [mem_image]
    constructor
    · intro hg'
      obtain ⟨i, rfl⟩ := h.firstSteps_sub (n + 1) hg'
      rw [← hn, h.mem_firstSteps_oddm hlt j i] at hg'
      refine ⟨(i + (j + 1)).toNat, mem_range.2 (by omega), ?_⟩
      have e1 : (((i + (j + 1)).toNat : ℕ) : ℤ) - ((j : ℤ) + 1) = i := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [e1]
    · rintro ⟨t, ht, rfl⟩
      rw [← hn, h.mem_firstSteps_oddm hlt j]
      have := mem_range.1 ht
      omega
  have hinj : Set.InjOn (fun t : ℕ => gL p p' r s ((t : ℤ) - ((j : ℤ) + 1))) (range (2 * j + 2)) := by
    intro t1 _ t2 _ he'
    have := h.gL_inj hlt he'
    omega
  rw [hFS, sum_image hinj, sum_range_succ] at hT
  have hdead : pfCoef p p' n (2 * j + 1)
      (gL p p' r s (((2 * j + 1 : ℕ) : ℤ) - ((j : ℤ) + 1))) = 0 := by
    have e1 : (((2 * j + 1 : ℕ) : ℤ) - ((j : ℤ) + 1)) = j := by push_cast; ring
    rw [e1]
    unfold pfCoef tailOf
    rw [← hn, h.tail_dead_oddm hlt j n, mul_zero, coeff_zero]
  rw [hdead, map_zero, zero_mul, add_zero] at hT
  have hκ : 0 ∈ range (2 * j + 1) := mem_range.2 (by omega)
  have hm := moment_limit (range (2 * j + 1))
    (fun t => hdotNu p p' (gL p p' r s ((t : ℤ) - ((j : ℤ) + 1))))
    (fun t => pfCoef p p' n (2 * j + 1) (gL p p' r s ((t : ℤ) - ((j : ℤ) + 1))))
    (2 * j + 1) (card_range _) a e he hT 0 hκ
  have h0 : ((0 : ℕ) : ℤ) - ((j : ℤ) + 1) = -((j : ℤ) + 1) := by push_cast; ring
  simp only [h0] at hm
  rw [h.slope_prod_m j] at hm
  have htail : tailOf p p' n (n + 1) (gL p p' r s (-((j : ℤ) + 1))) = 1 := by
    unfold tailOf
    rw [← hn, Nat.sub_self, chainTc_zero_level]
  have hC : pfCoef p p' n (2 * j + 1) (gL p p' r s (-((j : ℤ) + 1))) =
      rhoG p p' (gL p p' r s (-((j : ℤ) + 1))) *
        ((-1) ^ j / (((j.factorial : ℕ) : ℂ) ^ 2 * kappa0 p p' ^ (2 * j))) := by
    unfold pfCoef
    rw [htail, mul_one, resLimit,
      show 2 * j + 1 = (boxMults p p' (gL p p' r s (-((j : ℤ) + 1)))).card + 1 by
        rw [h.card_box_m],
      coeff_resLimit_top, h.box_value_m]
  rw [hC, h.rhoG_gL, h.slope_const] at hm
  have hsg : ((sgnI (-((j : ℤ) + 1)) : ℤ) : ℂ) = -1 := by
    rw [sgnI, if_neg (by omega)]
    simp
  rw [hm, hsg, layerConst_odd, fact_two_mul]
  have hκ0 := h.kappa0_ne
  have hf : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [show (-(rho p p' r s) * kappa0 p p') ^ (2 * j) =
      rho p p' r s ^ (2 * j) * kappa0 p p' ^ (2 * j) by
    rw [mul_pow, neg_pow, pow_mul (-1 : ℂ)]
    simp]
  rw [show (-(rho p p' r s)) ^ (2 * j + 1) = -(rho p p' r s ^ (2 * j) * rho p p' r s) by
    rw [neg_pow, pow_succ (-1 : ℂ), pow_mul (-1 : ℂ), pow_succ (rho p p' r s)]
    simp]
  field_simp

end Virasoro.ChainEval
