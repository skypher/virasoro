import Virasoro.Proofs.Sec6ChainEvenTail

/-!
# Proposition 6.7, the evaluation for `k = 2q + 2` (paper.tex l.1157–1169)

Take `κ = g_q` (momentum `n₁ + qN₀`); its chains end with the step `gEnd` of l.1167–1168, so
`C_κ = ρ(−1)^q/(q!² κ₀^{2q}) · ρ_g/(ḣ_κ − ḣ_g)` with `ρ_g/(ḣ_κ − ḣ_g) = −2p'²/((p'−p)(q+1)N₀)`,
the product of the slope differences is `−(n₀N₀/4p'²)^{2q+1}(2q+1)!`, and the limit is
`c_{2q+2} ρ^{2q+2}`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

theorem Setup.n1_lt (h : Setup p p' r s) : n1 p p' r s < N0 p p' := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hp' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have hsp : (s : ℤ) < p' := by exact_mod_cast h.hsp
  unfold n1 N0
  nlinarith

/-- `n₁ ≠ pp'`: otherwise `p ∣ p'r`. -/
theorem Setup.two_n1_ne (h : Setup p p' r s) : 2 * n1 p p' r s ≠ N0 p p' := by
  intro he
  have h1 : (p' : ℤ) * r = p * (p' - s) := by unfold n1 N0 at he; linarith
  have h2 : (p : ℤ) ∣ (p' : ℤ) * r := ⟨p' - s, h1⟩
  have h3 : (p : ℤ) ∣ r := h.isCoprime.dvd_of_dvd_mul_left h2
  have h4 : p ∣ r := by exact_mod_cast h3
  have := Nat.le_of_dvd h.hr h4
  have := h.hrp
  omega

/-- `i ↦ g_i` is injective. -/
theorem Setup.gL_inj' (h : Setup p p' r s) {i i' : ℤ} (he : gL p p' r s i = gL p p' r s i') :
    i = i' := by
  have h1 := h.gL_sum i
  have h2 := h.gL_sum i'
  rw [he] at h1
  rw [h1] at h2
  have hN := h.N0_pos
  have hn := h.n1_pos
  have hlt := h.n1_lt
  have hne := h.two_n1_ne
  unfold sgnI at h2
  split_ifs at h2 with ha hb hb
  · have : (i - i') * N0 p p' = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3 <;> linarith
  all_goals first
    | (have : (i - i') * N0 p p' = 0 := by linarith
       rcases mul_eq_zero.1 this with h3 | h3 <;> linarith)
    | (exfalso
       have h3 : (-(i + i')) * N0 p p' = 2 * n1 p p' r s := by linarith
       rcases lt_trichotomy (-(i + i')) 1 with h4 | h4 | h4
       · have : -(i + i') ≤ 0 := by omega
         nlinarith
       · rw [h4, one_mul] at h3
         exact hne h3.symm
       · have h5 : 2 * N0 p p' ≤ (-(i + i')) * N0 p p' :=
           mul_le_mul_of_nonneg_right (by omega) hN.le
         linarith)

theorem Setup.hdot_gEnd (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ) =
      σ * ((n1 p p' r s : ℂ) + q * N0 p p') * (((q : ℂ) + 1) * N0 p p') / (4 * (p' : ℂ) ^ 2) := by
  have hp' := h.p'_ne
  have e1 := h.hdot_gL (q : ℤ)
  have e2 := h.hdot_formula (gEnd p p' r s q σ)
  obtain ⟨hEm, hEd⟩ := h.gEnd_mom q σ hσ
  have hEm' := congrArg (Int.cast : ℤ → ℂ) hEm
  have hEd' := congrArg (Int.cast : ℤ → ℂ) hEd
  push_cast at hEm' hEd' e1
  rw [hEm', hEd'] at e2
  field_simp
  rcases hσ with rfl | rfl
  · push_cast
    linear_combination e1 - e2
  · push_cast
    linear_combination e1 - e2

theorem Setup.rho_gEnd (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    rhoG p p' (gEnd p p' r s q σ) =
      -(σ * ((n1 p p' r s : ℂ) + q * N0 p p')) / (2 * ((p' : ℂ) - p)) := by
  obtain ⟨_, hEd⟩ := h.gEnd_mom q σ hσ
  have hEd' := congrArg (Int.cast : ℤ → ℂ) hEd
  push_cast at hEd'
  unfold rhoG
  rw [hEd']

/-- `ρ_g/(ḣ_κ − ḣ_g) = −2p'²/((p'−p)(q+1)N₀)` (paper.tex l.1168). -/
theorem Setup.ratio_gEnd (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ))⁻¹ *
        rhoG p p' (gEnd p p' r s q σ) =
      -(2 * (p' : ℂ) ^ 2) / (((p' : ℂ) - p) * (((q : ℂ) + 1) * N0 p p')) := by
  have hp' := h.p'_ne
  have hs := h.sub_ne
  have hN : (N0 p p' : ℂ) ≠ 0 := by exact_mod_cast h.N0_pos.ne'
  have hq : ((q : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  have hX : ((n1 p p' r s : ℂ) + q * N0 p p') ≠ 0 := by
    have : (0 : ℤ) < n1 p p' r s + q * N0 p p' := by
      have := h.n1_pos
      have := h.N0_pos
      positivity
    exact_mod_cast this.ne'
  rw [h.hdot_gEnd q σ hσ, h.rho_gEnd q σ hσ]
  rcases hσ with rfl | rfl
  · push_cast
    field_simp
    norm_num
  · push_cast
    field_simp
    norm_num

/-- `∏_{t<2q+1} (ḣ_{g_q} − ḣ_{g_{t−(q+1)}}) = −(n₀N₀/4p'²)^{2q+1}(2q+1)!`. -/
theorem Setup.slope_prod_e (h : Setup p p' r s) (q : ℕ) :
    ∏ t ∈ range (2 * q + 1),
        (hdotNu p p' (gL p p' r s q) - hdotNu p p' (gL p p' r s ((t : ℤ) - ((q : ℤ) + 1)))) =
      -(((n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2)) ^ (2 * q + 1) *
        (((2 * q + 1).factorial : ℕ) : ℂ)) := by
  have e : ∀ t ∈ range (2 * q + 1),
      hdotNu p p' (gL p p' r s q) - hdotNu p p' (gL p p' r s ((t : ℤ) - ((q : ℤ) + 1))) =
        (n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2) *
          ((t : ℂ) - ((2 * q + 1 : ℕ) : ℂ)) := by
    intro t _
    rw [h.hdot_sub]
    push_cast
    ring
  rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range, prod_range_sub]
  rw [Odd.neg_one_pow ⟨q, rfl⟩]
  ring

theorem layerConst_even (q : ℕ) :
    (layerConst (2 * q + 2) : ℂ) = (-1) ^ (q + 1) * ((Nat.choose (2 * q + 1) q : ℕ) : ℂ) := by
  unfold layerConst
  rw [show (2 * q + 2) / 2 = q + 1 by omega, show 2 * q + 2 - 1 = 2 * q + 1 by omega,
    show (2 * q + 1) / 2 = q by omega]
  push_cast
  ring

theorem fact_two_mul_add_one (q : ℕ) :
    (((2 * q + 1).factorial : ℕ) : ℂ) =
      ((Nat.choose (2 * q + 1) q : ℕ) : ℂ) * ((q.factorial : ℕ) : ℂ) *
        (((q : ℂ) + 1) * ((q.factorial : ℕ) : ℂ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ 2 * q + 1 by omega)
  rw [show 2 * q + 1 - q = q + 1 by omega, Nat.factorial_succ] at h
  have h' := congrArg (Nat.cast : ℕ → ℂ) h
  push_cast at h'
  rw [← h']

/-- Proposition 6.7 for `k = 2q + 2`, both signs: `σ = 1` for `ℓ⁺`, `σ = −1` for `ℓ⁻`
(paper.tex l.1157–1169). -/
theorem Setup.eval_even (h : Setup p p' r s) (q : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (N : ℕ)
    (hN : 2 * N0 p p' * (N : ℤ) =
      (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - n0 p p' r s ^ 2)
    (a : ℂ) (e : RatFunc ℂ) (he : VanishesAtInfinity e)
    (hT : (chainTN p p' r s N).coeff (2 * q + 2) * RatFunc.X ^ (2 * q + 2) = RatFunc.C a + e) :
    a = (layerConst (2 * q + 2) : ℂ) * rho p p' r s ^ (2 * q + 2) := by
  obtain ⟨hlt, _⟩ := h.lvl_gq_lt q σ hσ N hN
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hl1 : 1 ≤ (gL p p' r s q).lvl := by
    have := Nat.mul_le_mul (h.gL_pos q).1 (h.gL_pos q).2
    unfold Label.lvl
    exact this
  obtain ⟨f, hf⟩ : ∃ f, N = f + 2 := ⟨N - 2, by omega⟩
  subst hf
  rw [show f + 2 = (f + 1) + 1 by omega, coeff_chainTN] at hT
  have hFS : firstSteps p p' (f + 1 + 1) (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) =
      (range (2 * q + 2)).image (fun t : ℕ => gL p p' r s ((t : ℤ) - ((q : ℤ) + 1))) := by
    ext g'
    rw [mem_image]
    have hN' : 2 * N0 p p' * ((f + 1 + 1 : ℕ) : ℤ) =
        (σ * n0 p p' r s + ((q : ℤ) + 1) * N0 p p') ^ 2 - n0 p p' r s ^ 2 := by
      rw [← hN]
    constructor
    · intro hg'
      obtain ⟨i, rfl⟩ := h.firstSteps_sub (f + 1 + 1) hg'
      rw [h.mem_firstSteps_even q σ hσ _ hN' i] at hg'
      refine ⟨(i + (q + 1)).toNat, mem_range.2 (by omega), ?_⟩
      have e1 : (((i + (q + 1)).toNat : ℕ) : ℤ) - ((q : ℤ) + 1) = i := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [e1]
    · rintro ⟨t, ht, rfl⟩
      rw [h.mem_firstSteps_even q σ hσ _ hN']
      have := mem_range.1 ht
      omega
  have hinj : Set.InjOn (fun t : ℕ => gL p p' r s ((t : ℤ) - ((q : ℤ) + 1)))
      (range (2 * q + 2)) := by
    intro t1 _ t2 _ he'
    have := h.gL_inj' he'
    omega
  rw [hFS, sum_image hinj] at hT
  have hκ : 2 * q + 1 ∈ range (2 * q + 2) := mem_range.2 (by omega)
  have hm := moment_limit (range (2 * q + 2))
    (fun t => hdotNu p p' (gL p p' r s ((t : ℤ) - ((q : ℤ) + 1))))
    (fun t => pfCoef p p' (f + 1) (2 * q + 2) (gL p p' r s ((t : ℤ) - ((q : ℤ) + 1))))
    (2 * q + 2) (card_range _) a e he hT (2 * q + 1) hκ
  have h2q : ((2 * q + 1 : ℕ) : ℤ) - ((q : ℤ) + 1) = q := by push_cast; ring
  simp only [h2q] at hm
  have herase : (range (2 * q + 2)).erase (2 * q + 1) = range (2 * q + 1) := by
    ext t
    simp only [mem_erase, mem_range]
    omega
  rw [herase, h.slope_prod_e q] at hm
  have htail : tailOf p p' (f + 1) (f + 1 + 1) (gL p p' r s q) =
      C ((hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ))⁻¹) *
        resLimit p p' (gEnd p p' r s q σ) := by
    unfold tailOf
    have := h.tail_even q σ hσ (f + 2) hN f
    rw [show f + 1 + 1 = f + 2 by omega]
    exact this
  have hC : pfCoef p p' (f + 1) (2 * q + 2) (gL p p' r s q) =
      (hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ))⁻¹ *
          rhoG p p' (gEnd p p' r s q σ) *
        (rhoG p p' (gL p p' r s q) *
          ((-1) ^ q / (((q.factorial : ℕ) : ℂ) ^ 2 * kappa0 p p' ^ (2 * q)))) := by
    unfold pfCoef
    rw [htail, h.resLimit_gEnd]
    rw [show resLimit p p' (gL p p' r s q) *
          (C ((hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ))⁻¹) *
            (C (rhoG p p' (gEnd p p' r s q σ)) * X)) =
        C ((hdotNu p p' (gL p p' r s q) - hdotNu p p' (gEnd p p' r s q σ))⁻¹ *
            rhoG p p' (gEnd p p' r s q σ)) * (resLimit p p' (gL p p' r s q) * X) by
      rw [C_mul]; ring]
    rw [coeff_C_mul, show 2 * q + 2 = (2 * q + 1) + 1 by omega, coeff_mul_X]
    congr 1
    rw [resLimit, show 2 * q + 1 = (boxMults p p' (gL p p' r s q)).card + 1 by rw [h.card_box],
      coeff_resLimit_top, h.box_value]
  rw [hC, h.ratio_gEnd q σ hσ, h.rhoG_gL, h.slope_const] at hm
  have hsg : ((sgnI (q : ℤ) : ℤ) : ℂ) = 1 := by
    rw [sgnI, if_pos hq0]
    simp
  rw [hm, hsg, layerConst_even, fact_two_mul_add_one]
  have hκ0 := h.kappa0_ne
  have hf0 : ((q.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos q).ne'
  have hp' := h.p'_ne
  have hp := h.p_ne
  have hs := h.sub_ne
  have hNc : (N0 p p' : ℂ) ≠ 0 := by exact_mod_cast h.N0_pos.ne'
  have hq1 : ((q : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  have hκN : 2 * (p' : ℂ) ^ 2 * kappa0 p p' = ((p' : ℂ) - p) * N0 p p' := by
    unfold kappa0 N0
    push_cast
    field_simp
  have hpow : (-(rho p p' r s) * kappa0 p p') ^ (2 * q + 1) =
      -(rho p p' r s ^ (2 * q + 1) * kappa0 p p' ^ (2 * q + 1)) := by
    rw [neg_mul, Odd.neg_pow ⟨q, rfl⟩, mul_pow]
  have hW : -(2 * (p' : ℂ) ^ 2) / (((p' : ℂ) - p) * (((q : ℂ) + 1) * N0 p p')) =
      -1 / (((q : ℂ) + 1) * kappa0 p p') := by
    rw [div_eq_div_iff (mul_ne_zero hs (mul_ne_zero hq1 hNc)) (mul_ne_zero hq1 hκ0)]
    linear_combination (-((q : ℂ) + 1)) * hκN
  rw [hpow, hW]
  field_simp
  ring

end Virasoro.ChainEval
