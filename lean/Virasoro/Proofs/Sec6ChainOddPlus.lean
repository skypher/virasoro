import Virasoro.Proofs.Sec6ChainSlopes
import Virasoro.Proofs.Sec6ChainConst
import Virasoro.Proofs.Sec6ChainMoments

/-!
# Proposition 6.7, the evaluation for `ℓ⁺_k`, `k = 2j + 1` (paper.tex l.1157–1166)

For `k = 2j+1` the endpoint is `n₁ + jN₀`, reached from `λ` in one step by
`g_j = (r + jp, s + jp')`.  Under `n₁ < pp'` the first steps of the chains of level
`ℓ⁺_k = (r+jp)(s+jp')` are the `g_i`, `-j ≤ i ≤ j`: `k` distinct slopes (l.1157–1160).
Taking `κ = g_j`, whose tail is empty, `C_κ = ρ(-1)^j/(j!² κ₀^{2j})` (box of `g_j`, l.1165–1166),
the product of the slope differences is `(n₀N₀/4p'²)^{2j}(2j)!`, and
`n₀N₀/(4p'²κ₀) = -ρ` (l.1166–1167), so the limit is `c_k ρ^k`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

/-- `2N₀ ℓ_{g_i} = (n₁ + iN₀)² − n₀²`. -/
theorem Setup.lvl_gL (h : Setup p p' r s) (i : ℤ) :
    2 * N0 p p' * ((gL p p' r s i).lvl : ℤ) =
      (n1 p p' r s + i * N0 p p') ^ 2 - n0 p p' r s ^ 2 := by
  rw [lvl_eq, h.gL_sum, h.gL_diff, mul_pow, mul_pow, sgnI_sq, one_mul, one_mul]

theorem gL_nat (p p' r s j : ℕ) : gL p p' r s (j : ℤ) = (r + j * p, s + j * p') := by
  simp [gL]

theorem Setup.n1_pos (h : Setup p p' r s) : 0 < n1 p p' r s := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hp' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hs : (0 : ℤ) < s := by exact_mod_cast h.hs
  unfold n1
  positivity

/-- The first steps of the chains of level `ℓ_{g_j}` are the `g_i` with `-j ≤ i ≤ j`, when
`2n₁ < N₀` (that is `n₁ < pp'`). -/
theorem Setup.mem_firstSteps_odd (h : Setup p p' r s) (hlt : 2 * n1 p p' r s < N0 p p') (j : ℕ)
    (i : ℤ) :
    gL p p' r s i ∈ firstSteps p p' (gL p p' r s j).lvl (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) ↔
      -(j : ℤ) ≤ i ∧ i ≤ j := by
  rw [h.gL_mem]
  have hl := h.lvl_gL (j : ℤ)
  have hN := h.N0_pos
  have hn := h.n1_pos
  have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have key : (n1 p p' r s + i * N0 p p') ^ 2 ≤ n0 p p' r s ^ 2 + 2 * N0 p p' *
      ((gL p p' r s j).lvl : ℤ) ↔
      (n1 p p' r s + i * N0 p p') ^ 2 ≤ (n1 p p' r s + j * N0 p p') ^ 2 := by
    rw [hl]
    constructor <;> intro hh <;> linarith
  rw [key]
  constructor
  · intro hh
    have hb : 0 ≤ n1 p p' r s + j * N0 p p' := by positivity
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' hh hb
    constructor
    · by_contra hc
      have hc : i + j < 0 := by omega
      have hc' : i + j ≤ -1 := by omega
      have : (i + j) * N0 p p' ≤ -1 * N0 p p' := mul_le_mul_of_nonneg_right hc' hN.le
      nlinarith
    · by_contra hc
      have hc : (j : ℤ) + 1 ≤ i := by omega
      have : ((j : ℤ) + 1) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right hc hN.le
      nlinarith
  · rintro ⟨h1, h2⟩
    have h3 : i * N0 p p' ≤ j * N0 p p' := mul_le_mul_of_nonneg_right h2 hN.le
    have h4 : -(j : ℤ) * N0 p p' ≤ i * N0 p p' := mul_le_mul_of_nonneg_right h1 hN.le
    apply sq_le_sq'
    · nlinarith
    · linarith

/-- `i ↦ g_i` is injective when `2n₁ ≠ N₀`. -/
theorem Setup.gL_inj (h : Setup p p' r s) (hne : 2 * n1 p p' r s < N0 p p') {i i' : ℤ}
    (he : gL p p' r s i = gL p p' r s i') : i = i' := by
  have h1 := h.gL_sum i
  have h2 := h.gL_sum i'
  rw [he] at h1
  rw [h1] at h2
  have hN := h.N0_pos
  have hn := h.n1_pos
  unfold sgnI at h2
  split_ifs at h2 with ha hb hb
  · have : (i - i') * N0 p p' = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · linarith
  · exfalso
    have h3 : (-(i + i')) * N0 p p' = 2 * n1 p p' r s := by linarith
    rcases le_or_gt (-(i + i')) 0 with h4 | h4
    · nlinarith
    · have h5 : 1 * N0 p p' ≤ (-(i + i')) * N0 p p' := mul_le_mul_of_nonneg_right (by omega) hN.le
      linarith
  · exfalso
    have h3 : (-(i + i')) * N0 p p' = 2 * n1 p p' r s := by linarith
    rcases le_or_gt (-(i + i')) 0 with h4 | h4
    · nlinarith
    · have h5 : 1 * N0 p p' ≤ (-(i + i')) * N0 p p' := mul_le_mul_of_nonneg_right (by omega) hN.le
      linarith
  · have : (i - i') * N0 p p' = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · linarith

/-- `∏_{t<j} (−((t+1)κ)⁻¹)(−(−(t+1)κ)⁻¹) = (−1)^j/(j!² κ^{2j})`. -/
theorem box_range_prod (κ : ℂ) (hκ : κ ≠ 0) (j : ℕ) :
    ∏ t ∈ range j, ((-((((t : ℤ) + 1 : ℤ) : ℂ) * κ)⁻¹) * (-(((-((t : ℤ) + 1) : ℤ) : ℂ) * κ)⁻¹)) =
      (-1) ^ j / (((j.factorial : ℕ) : ℂ) ^ 2 * κ ^ (2 * j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, ih, Nat.factorial_succ]
    have hj : ((j : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    have hf : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    push_cast
    field_simp
    ring

/-- The product over the box of `g_j`: `(−1)^j/(j!² κ₀^{2j})`. -/
theorem Setup.box_value (h : Setup p p' r s) (j : ℕ) :
    ∏ b ∈ boxMults p p' (gL p p' r s j), (-(((b : ℂ) * kappa0 p p')⁻¹)) =
      (-1) ^ j / (((j.factorial : ℕ) : ℂ) ^ 2 * kappa0 p p' ^ (2 * j)) := by
  have hκ : kappa0 p p' ≠ 0 := by
    unfold kappa0
    exact div_ne_zero (mul_ne_zero h.p_ne h.sub_ne) h.p'_ne
  rw [gL_nat, h.boxMults_plus j, prod_box]
  exact box_range_prod _ hκ j

theorem Setup.card_box (h : Setup p p' r s) (j : ℕ) :
    (boxMults p p' (gL p p' r s j)).card = 2 * j := by
  rw [gL_nat, h.boxMults_plus j, card_erase_of_mem (by simp), Int.card_Icc]
  omega

/-- `∏_{t<2j} (ḣ_{g_j} − ḣ_{g_{t−j}}) = (n₀N₀/4p'²)^{2j} (2j)!`. -/
theorem Setup.slope_prod (h : Setup p p' r s) (j : ℕ) :
    ∏ t ∈ range (2 * j), (hdotNu p p' (gL p p' r s j) - hdotNu p p' (gL p p' r s ((t : ℤ) - j))) =
      ((n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2)) ^ (2 * j) *
        (((2 * j).factorial : ℕ) : ℂ) := by
  have e : ∀ t ∈ range (2 * j),
      hdotNu p p' (gL p p' r s j) - hdotNu p p' (gL p p' r s ((t : ℤ) - j)) =
        (n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2) * ((t : ℂ) - ((2 * j : ℕ) : ℂ)) := by
    intro t _
    rw [h.hdot_sub]
    push_cast
    ring
  rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range, prod_range_sub]
  rw [show (-1 : ℂ) ^ (2 * j) = 1 by rw [pow_mul]; simp]
  ring

theorem Setup.kappa0_ne (h : Setup p p' r s) : kappa0 p p' ≠ 0 := by
  unfold kappa0
  exact div_ne_zero (mul_ne_zero h.p_ne h.sub_ne) h.p'_ne

/-- `n₀N₀/(4p'²) = −ρκ₀` (paper.tex l.1166–1167). -/
theorem Setup.slope_const (h : Setup p p' r s) :
    (n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2) = -(rho p p' r s) * kappa0 p p' := by
  have hp' := h.p'_ne
  have hs := h.sub_ne
  unfold rho kappa0 N0
  push_cast
  field_simp
  ring

theorem layerConst_odd (j : ℕ) :
    (layerConst (2 * j + 1) : ℂ) = (-1) ^ j * ((Nat.choose (2 * j) j : ℕ) : ℂ) := by
  unfold layerConst
  rw [show (2 * j + 1) / 2 = j by omega, show 2 * j + 1 - 1 = 2 * j by omega,
    show 2 * j / 2 = j by omega]
  push_cast
  ring

/-- `(2j)! = C(2j,j) j! j!`. -/
theorem fact_two_mul (j : ℕ) :
    (((2 * j).factorial : ℕ) : ℂ) =
      ((Nat.choose (2 * j) j : ℕ) : ℂ) * ((j.factorial : ℕ) : ℂ) * ((j.factorial : ℕ) : ℂ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
  rw [show 2 * j - j = j by omega] at h
  exact_mod_cast h.symm

/-- Proposition 6.7 for `ℓ⁺_{2j+1}` under `n₁ < pp'` (paper.tex l.1157–1167). -/
theorem Setup.eval_plus_odd (h : Setup p p' r s) (hlt : 2 * n1 p p' r s < N0 p p') (j : ℕ)
    (a : ℂ) (e : RatFunc ℂ) (he : VanishesAtInfinity e)
    (hT : (chainTN p p' r s (ellPlus p p' r s (2 * j + 1))).coeff (2 * j + 1) *
        RatFunc.X ^ (2 * j + 1) = RatFunc.C a + e) :
    a = (layerConst (2 * j + 1) : ℂ) * rho p p' r s ^ (2 * j + 1) := by
  have hE : ellPlus p p' r s (2 * j + 1) = (gL p p' r s j).lvl := by
    rw [gL_nat]
    unfold ellPlus Label.lvl
    rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]
  obtain ⟨n, hn⟩ : ∃ n, (gL p p' r s j).lvl = n + 1 := by
    refine ⟨(gL p p' r s j).lvl - 1, ?_⟩
    have h1 := (h.gL_pos j).1
    have h2 := (h.gL_pos j).2
    have h3 := Nat.mul_le_mul h1 h2
    unfold Label.lvl
    omega
  rw [hE, hn, coeff_chainTN] at hT
  have hFS : firstSteps p p' (n + 1) (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) =
      (range (2 * j + 1)).image (fun t : ℕ => gL p p' r s ((t : ℤ) - j)) := by
    ext g'
    rw [mem_image]
    constructor
    · intro hg'
      obtain ⟨i, rfl⟩ := h.firstSteps_sub (n + 1) hg'
      rw [← hn, h.mem_firstSteps_odd hlt j i] at hg'
      refine ⟨(i + j).toNat, mem_range.2 (by omega), ?_⟩
      have e1 : (((i + j).toNat : ℕ) : ℤ) - j = i := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [e1]
    · rintro ⟨t, ht, rfl⟩
      rw [← hn, h.mem_firstSteps_odd hlt j]
      have := mem_range.1 ht
      omega
  have hinj : Set.InjOn (fun t : ℕ => gL p p' r s ((t : ℤ) - j)) (range (2 * j + 1)) := by
    intro t1 _ t2 _ he'
    have := h.gL_inj hlt he'
    omega
  rw [hFS, sum_image hinj] at hT
  have hκ : 2 * j ∈ range (2 * j + 1) := mem_range.2 (by omega)
  have hm := moment_limit (range (2 * j + 1)) (fun t => hdotNu p p' (gL p p' r s ((t : ℤ) - j)))
    (fun t => pfCoef p p' n (2 * j + 1) (gL p p' r s ((t : ℤ) - j))) (2 * j + 1) (card_range _)
    a e he hT (2 * j) hκ
  have h2j : ((2 * j : ℕ) : ℤ) - j = j := by push_cast; ring
  simp only [h2j] at hm
  have herase : (range (2 * j + 1)).erase (2 * j) = range (2 * j) := by
    ext t
    simp only [mem_erase, mem_range]
    omega
  rw [herase, h.slope_prod j] at hm
  have htail : tailOf p p' n (n + 1) (gL p p' r s j) = 1 := by
    unfold tailOf
    rw [← hn, Nat.sub_self, chainTc_zero_level]
  have hC : pfCoef p p' n (2 * j + 1) (gL p p' r s j) =
      rhoG p p' (gL p p' r s j) *
        ((-1) ^ j / (((j.factorial : ℕ) : ℂ) ^ 2 * kappa0 p p' ^ (2 * j))) := by
    unfold pfCoef
    rw [htail, mul_one, resLimit,
      show 2 * j + 1 = (boxMults p p' (gL p p' r s j)).card + 1 by rw [h.card_box],
      coeff_resLimit_top, h.box_value]
  rw [hC, h.rhoG_gL, h.slope_const] at hm
  have hsg : ((sgnI (j : ℤ) : ℤ) : ℂ) = 1 := by
    rw [sgnI, if_pos (Int.natCast_nonneg j)]
    simp
  rw [hm, hsg, layerConst_odd, fact_two_mul]
  have hκ0 := h.kappa0_ne
  have hf : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [show (-(rho p p' r s) * kappa0 p p') ^ (2 * j) =
      rho p p' r s ^ (2 * j) * kappa0 p p' ^ (2 * j) by
    rw [mul_pow, neg_pow, pow_mul (-1 : ℂ)]
    simp]
  field_simp
  ring

end Virasoro.ChainEval
