import Virasoro.Proofs.P2Sec12TwoStep

/-!
# Proposition 12.1 (finiteness, nonvanishing and path-independence of the BGG cocycle),
paper.tex l.2753–2836
-/

namespace Virasoro

open Polynomial

theorem aeval_linP (t : ℂ) (y : ℤ × ℤ) : Polynomial.aeval t (linP y) = linV t y := by
  simp [linP, linV]

theorem aeval_prod_linP (t : ℂ) (s : Finset (ℤ × ℤ)) :
    Polynomial.aeval t (∏ y ∈ s, linP y) = ∏ y ∈ s, linV t y := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun y _ => aeval_linP t y

/-- The Gamma potential (9.5) at `b⋆`, as a function of the momentum `n_μ` of the node `μ`:
`2ϖ_μ/b⋆ = n_μ/p'` (l.2789–2798). -/
noncomputable def psiNode (p' k m : ℕ) (b : ℂ) (n : ℤ) : ℂ :=
  PsiPot k m ((n : ℂ) * b / (2 * p')) b

/-- `Ψ` is even in `ϖ` (l.2809). -/
theorem PsiPot_neg (k m : ℕ) (ϖ b : ℂ) : PsiPot k m (-ϖ) b = PsiPot k m ϖ b := by
  unfold PsiPot
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    have e1 : 1 + 2 * -ϖ / b + (j : ℂ) / b ^ 2 = 1 - 2 * ϖ / b + (j : ℂ) / b ^ 2 := by ring
    have e2 : 1 - 2 * -ϖ / b + (j : ℂ) / b ^ 2 = 1 + 2 * ϖ / b + (j : ℂ) / b ^ 2 := by ring
    rw [e1, e2, mul_comm]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have e1 : 1 + 2 * -ϖ * b + (i : ℂ) * b ^ 2 + m = 1 - 2 * ϖ * b + (i : ℂ) * b ^ 2 + m := by
      ring
    have e2 : 1 - 2 * -ϖ * b + (i : ℂ) * b ^ 2 + m = 1 + 2 * ϖ * b + (i : ℂ) * b ^ 2 + m := by
      ring
    rw [e1, e2, mul_comm]

theorem psiNode_neg (p' k m : ℕ) (b : ℂ) (n : ℤ) : psiNode p' k m b (-n) = psiNode p' k m b n := by
  unfold psiNode
  rw [← PsiPot_neg]
  congr 1
  push_cast
  ring

variable {p p' r s : ℕ} {b : ℂ}

theorem binv_minimal (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) :
    b⁻¹ = -(p : ℂ) * b / p' := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  refine inv_eq_of_mul_eq_one_right ?_
  have e : b * (-(p : ℂ) * b / p') = -(p : ℂ) * b ^ 2 / p' := by ring
  rw [e, hb]
  field_simp

theorem PsiPot_in_node (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (R S : ℕ)
    (k m : ℕ) :
    PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b =
      psiNode p' k m b ((p' : ℤ) * R - p * S) := by
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  unfold psiNode
  congr 1
  rw [binv_minimal hp hp' hb]
  push_cast
  field_simp
  ring

theorem PsiPot_out_node (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (R S : ℕ)
    (k m : ℕ) :
    PsiPot k m (((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2) b =
      psiNode p' k m b ((p' : ℤ) * R + p * S) := by
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  unfold psiNode
  congr 1
  rw [binv_minimal hp hp' hb]
  push_cast
  field_simp
  ring

/-- A Gamma argument `x/b⋆² + N` is not an integer when `p' ∤ x` (l.2799–2804). -/
theorem recGamma_ne_zero_div (hcop : Nat.Coprime p p') (hp : 0 < p) (hp' : 0 < p')
    (hb : b ^ 2 = -(p' : ℂ) / p) {x : ℤ} (hx : ¬ (p' : ℤ) ∣ x) (z : ℂ) (N : ℤ)
    (hz : z = (x : ℂ) / b ^ 2 + N) : (Complex.Gamma z)⁻¹ ≠ 0 := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  refine inv_ne_zero (Complex.Gamma_ne_zero fun M h => hx ?_)
  rw [hz, hb] at h
  have h' : (x : ℂ) / (-(p' : ℂ) / p) = -(M : ℂ) - N := by linear_combination h
  have e : (x : ℂ) / (-(p' : ℂ) / p) * p' = -((x : ℂ) * p) := by field_simp
  rw [h'] at e
  have h3 : (x : ℂ) * p = ((M : ℂ) + N) * p' := by linear_combination e
  have h4 : x * (p : ℤ) = ((M : ℤ) + N) * p' := by exact_mod_cast h3
  have hc : IsCoprime (p' : ℤ) (p : ℤ) := (Nat.isCoprime_iff_coprime.2 hcop).symm
  exact hc.dvd_of_dvd_mul_left ⟨(M : ℤ) + N, by linear_combination h4⟩

/-- A Gamma argument `a b⋆² + N` is not an integer when `p ∤ a` (l.2804–2807). -/
theorem recGamma_ne_zero_mul (hcop : Nat.Coprime p p') (hp : 0 < p) (hp' : 0 < p')
    (hb : b ^ 2 = -(p' : ℂ) / p) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (z : ℂ) (N : ℤ)
    (hz : z = (a : ℂ) * b ^ 2 + N) : (Complex.Gamma z)⁻¹ ≠ 0 := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  refine inv_ne_zero (Complex.Gamma_ne_zero fun M h => ha ?_)
  rw [hz, hb] at h
  have h' : (a : ℂ) * (-(p' : ℂ) / p) = -(M : ℂ) - N := by linear_combination h
  have e : (a : ℂ) * (-(p' : ℂ) / p) * p = -((a : ℂ) * p') := by field_simp
  rw [h'] at e
  have h3 : (a : ℂ) * p' = ((M : ℂ) + N) * p := by linear_combination e
  have h4 : a * (p' : ℤ) = ((M : ℤ) + N) * p := by exact_mod_cast h3
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  exact hc.dvd_of_dvd_mul_left ⟨(M : ℤ) + N, by linear_combination h4⟩

/-- `Ψ(ϖ_{R,S};b⋆)` is finite and nonzero when `R ≡ ±r (mod p)`, `S ≡ ±s (mod p')` and
`(k,m)` lies in the fusion box (l.2799–2809). -/
theorem PsiPot_in_ne_zero (hcop : Nat.Coprime p p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') (hb : b ^ 2 = -(p' : ℂ) / p) {R S k m : ℕ}
    (hcR : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r))
    (hcS : ∃ a : ℕ, S = a * p' + s ∨ S = a * p' + (p' - s))
    (hk : k < min r (p - r)) (hm : m < min s (p' - s)) :
    PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b ≠ 0 := by
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    rw [zero_pow two_ne_zero] at hb
    exact div_ne_zero (neg_ne_zero.2 hpc') hpc hb.symm
  have h := PsiPot_strip hb0 R k m (S : ℤ) (-(S : ℤ)) rfl
  have e1 : ((R : ℂ) * b + (((S : ℤ) : ℤ) : ℂ) * b⁻¹) / 2 = ((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2 := by
    push_cast; ring
  rw [e1] at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ ?_) <;>
    refine Finset.prod_ne_zero_iff.2 fun x hx => ?_ <;> rw [Finset.mem_Icc] at hx
  · refine recGamma_ne_zero_div hcop hp hp' hb ?_ _ ((R : ℤ) + 1) (by push_cast; ring)
    have h1 := (not_dvd_shift hs0 hs hcS hm (x - S) (by omega) (by omega)).1
    have e : (S : ℤ) + (x - S) = x := by ring
    rwa [e] at h1
  · refine recGamma_ne_zero_div hcop hp hp' hb ?_ _ (1 - (R : ℤ)) (by push_cast; ring)
    have h1 := (not_dvd_shift hs0 hs hcS hm (x + S) (by omega) (by omega)).2
    have e : x + (S : ℤ) - S = x := by ring
    rwa [e] at h1
  · refine recGamma_ne_zero_mul hcop hp hp' hb ?_ _ ((S : ℤ) + m + 1) (by push_cast; ring)
    have h1 := (not_dvd_shift hr0 hr hcR hk (x - R) (by omega) (by omega)).1
    have e : (R : ℤ) + (x - R) = x := by ring
    rwa [e] at h1
  · refine recGamma_ne_zero_mul hcop hp hp' hb ?_ _ (1 + -(S : ℤ) + m) (by push_cast; ring)
    have h1 := (not_dvd_shift hr0 hr hcR hk (x + R) (by omega) (by omega)).2
    have e : x + (R : ℤ) - R = x := by ring
    rwa [e] at h1

theorem linV_minimal (hp : 0 < p) (hb : b ^ 2 = -(p' : ℂ) / p) (y : ℤ × ℤ) :
    linV (b ^ 2) y = (((p : ℤ) * y.2 - (p' : ℤ) * y.1 : ℤ) : ℂ) / p := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [linV, hb]
  push_cast
  field_simp
  ring

/-- Equation (12.3) for a label `(R,S)` (l.2810–2832):
`c_{R,S}(-p'/p;2k+1,2m+1) Ψ(ϖ_{R,S};b⋆) = Ψ(ϖ_{R,-S};b⋆)`. -/
theorem cMM_psi (hcop : Nat.Coprime p p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') (hb : b ^ 2 = -(p' : ℂ) / p) {R S k m : ℕ}
    (hcR : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r))
    (hcS : ∃ a : ℕ, S = a * p' + s ∨ S = a * p' + (p' - s))
    (hk : k < min r (p - r)) (hm : m < min s (p' - s)) :
    ((cMM p p' R S k m : ℚ) : ℂ) * PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b =
      PsiPot k m (((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2) b := by
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hb
    exact div_ne_zero (neg_ne_zero.2 hpc') hpc hb.symm
  have hkR : k < R := lt_of_lt_of_le hk (min_le_of_congr hcR)
  have hmS : m < S := lt_of_lt_of_le hm (min_le_of_congr hcS)
  have hne := symdiff_factor_ne hcop hr0 hr hs0 hs hcR hcS hk hm
  obtain ⟨hDne, hcm, -⟩ := cMM_eval (R : ℤ) (S : ℤ) k m hp hne
  -- the polynomial two-step identity with the common factors cancelled
  have hpoly := two_step_box hkR hmS linP
  rw [← boxNumPoly_shift, boxNumPoly_split hkR hmS] at hpoly
  change _ = boxDenPoly R S * _ at hpoly
  rw [boxDenPoly_split hkR hmS] at hpoly
  have hred := mul_left_cancel₀ (boxCommon_ne_zero (R : ℤ) (S : ℤ) k m)
    (show _ * ((∏ y ∈ boxShift R S k m \ boxSet R S, linP y) *
        ((∏ y ∈ stripD1 R S m, linP y) * ∏ y ∈ stripD2 R S k m, linP y)) =
      _ * ((∏ y ∈ boxSet R S \ boxShift R S k m, linP y) *
        ((∏ y ∈ stripN1 R S m, linP y) * ∏ y ∈ stripN2 R S k m, linP y)) by
      linear_combination hpoly)
  have hcast : ∀ q : ℚ[X], Polynomial.aeval (b ^ 2) q = ((q.eval (-(p' : ℚ) / p) : ℚ) : ℂ) := by
    intro q
    have e : b ^ 2 = algebraMap ℚ ℂ (-(p' : ℚ) / p) := by rw [hb]; simp
    rw [e, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  have hev := congrArg (Polynomial.aeval (b ^ 2)) hred
  rw [map_mul, map_mul, map_mul, map_mul,
    hcast (∏ y ∈ boxShift (R : ℤ) (S : ℤ) k m \ boxSet (R : ℤ) (S : ℤ), linP y),
    hcast (∏ y ∈ boxSet (R : ℤ) (S : ℤ) \ boxShift (R : ℤ) (S : ℤ) k m, linP y),
    aeval_prod_linP, aeval_prod_linP, aeval_prod_linP, aeval_prod_linP] at hev
  have hDc : (((∏ y ∈ boxSet R S \ boxShift R S k m, linP y).eval (-(p' : ℚ) / p) : ℚ) : ℂ)
      ≠ 0 := by exact_mod_cast hDne
  have hcmc : ((cMM p p' R S k m : ℚ) : ℂ) *
      (((∏ y ∈ boxSet R S \ boxShift R S k m, linP y).eval (-(p' : ℚ) / p) : ℚ) : ℂ) =
      (((∏ y ∈ boxShift R S k m \ boxSet R S, linP y).eval (-(p' : ℚ) / p) : ℚ) : ℂ) := by
    rw [hcm, Rat.cast_div, div_mul_cancel₀ _ hDc]
  have hstrip : ((∏ y ∈ stripD1 R S m, linV (b ^ 2) y) * ∏ y ∈ stripD2 R S k m, linV (b ^ 2) y)
      ≠ 0 := by
    refine mul_ne_zero ?_ ?_ <;> refine Finset.prod_ne_zero_iff.2 fun y hy => ?_ <;>
      rw [linV_minimal hp hb] <;> refine div_ne_zero ?_ hpc <;> rw [Int.cast_ne_zero] <;>
      intro h0 <;>
      have hd := coprime_two_dvd hcop (x := y.1) (y := y.2) (by linarith)
    · simp only [stripD1, Finset.mem_product, Finset.mem_Icc] at hy
      have h1 := (not_dvd_shift hs0 hs hcS hm (y.2 + S) (by omega) (by omega)).2
      have e : y.2 + (S : ℤ) - S = y.2 := by ring
      rw [e] at h1
      exact h1 hd.2
    · simp only [stripD2, Finset.mem_product, Finset.mem_Icc] at hy
      have h1 := (not_dvd_shift hr0 hr hcR hk (y.1 + R) (by omega) (by omega)).2
      have e : y.1 + (R : ℤ) - R = y.1 := by ring
      rw [e] at h1
      exact h1 hd.1
  have hpsi := psi_box_core hb0 R S k m
  refine mul_left_cancel₀ (mul_ne_zero hDc hstrip) ?_
  linear_combination
    (((∏ y ∈ stripD1 R S m, linV (b ^ 2) y) * ∏ y ∈ stripD2 R S k m, linV (b ^ 2) y) *
      PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b) * hcmc +
    PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b * hev +
    (((∏ y ∈ boxSet R S \ boxShift R S k m, linP y).eval (-(p' : ℚ) / p) : ℚ) : ℂ) * hpsi

section Orbit

variable (hset : MinimalSetting p p' r s b) {k m : ℕ} (hk : k < min r (p - r))
  (hm : m < min s (p' - s))

include hset hk hm

/-- `Ψ(ϖ_μ;b⋆) ≠ 0` at every node of the orbit, by the paper's argument (l.2803–2822): at
`b = b⋆` the Gamma arguments are `1 + (±n_μ - jp)/p'` and `1 + m + (±n_μ - ip')/p`, and
`n_μ ≡ ±ps (mod p')`, `n_μ ≡ ±p'r (mod p)` make none of them an integer. -/
theorem psiNode_ne_zero (ε : Bool) (j : ℕ) :
    psiNode p' k m b (nOrb p p' r s ε j) ≠ 0 := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hb
    exact div_ne_zero (neg_ne_zero.2 hpc') hpc hb.symm
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨⟨u, hu, hdu⟩, ⟨v, hv, hdv⟩⟩ := nOrb_mod (p := p) (p' := p') (r := r) (s := s) ε j
  set n := nOrb p p' r s ε j with hn
  have small : ∀ {q : ℕ} {t : ℤ}, 0 < t → t < q → ¬ (q : ℤ) ∣ t := fun h0 h1 hd =>
    absurd (Int.le_of_dvd h0 hd) (not_le.2 h1)
  -- `p' ∤ ±n_μ - jp` for `1 ≤ j ≤ m < min(s, p'-s)` (l.2817–2819)
  have hS : ∀ i : ℕ, 1 ≤ i → i ≤ m → ¬ (p' : ℤ) ∣ n - i * p ∧ ¬ (p' : ℤ) ∣ -n - i * p := by
    intro i hi1 him
    have hi : (i : ℤ) < s ∧ (i : ℤ) < p' - s := ⟨by omega, by omega⟩
    constructor
    · intro h
      have h2 := dvd_sub h hdv
      rw [show n - i * p - (n - v * (p * s)) = (p : ℤ) * (v * s - i) by ring] at h2
      have h3 := hc.symm.dvd_of_dvd_mul_left h2
      rcases hv with rfl | rfl
      · exact small (q := p') (t := s - i) (by linarith) (by linarith) (by simpa using h3)
      · exact small (q := p') (t := s + i) (by linarith) (by linarith)
          (dvd_neg.1 (by rw [show -((s : ℤ) + i) = -1 * s - i by ring]; exact h3))
    · intro h
      have h2 := dvd_add h hdv
      rw [show -n - i * p + (n - v * (p * s)) = -((p : ℤ) * (v * s + i)) by ring] at h2
      have h3 := hc.symm.dvd_of_dvd_mul_left (dvd_neg.1 h2)
      rcases hv with rfl | rfl
      · exact small (q := p') (t := s + i) (by linarith) (by linarith) (by simpa using h3)
      · exact small (q := p') (t := s - i) (by linarith) (by linarith)
          (dvd_neg.1 (by rw [show -((s : ℤ) - i) = -1 * s + i by ring]; exact h3))
  -- `p ∤ ±n_μ - ip'` for `1 ≤ i ≤ k < min(r, p-r)` (l.2819–2822)
  have hR : ∀ i : ℕ, 1 ≤ i → i ≤ k → ¬ (p : ℤ) ∣ -n - i * p' ∧ ¬ (p : ℤ) ∣ n - i * p' := by
    intro i hi1 hik
    have hi : (i : ℤ) < r ∧ (i : ℤ) < p - r := ⟨by omega, by omega⟩
    constructor
    · intro h
      have h2 := dvd_add h hdu
      rw [show -n - i * p' + (n - u * (p' * r)) = -((p' : ℤ) * (u * r + i)) by ring] at h2
      have h3 := hc.dvd_of_dvd_mul_left (dvd_neg.1 h2)
      rcases hu with rfl | rfl
      · exact small (q := p) (t := r + i) (by linarith) (by linarith) (by simpa using h3)
      · exact small (q := p) (t := r - i) (by linarith) (by linarith)
          (dvd_neg.1 (by rw [show -((r : ℤ) - i) = -1 * r + i by ring]; exact h3))
    · intro h
      have h2 := dvd_sub h hdu
      rw [show n - i * p' - (n - u * (p' * r)) = (p' : ℤ) * (u * r - i) by ring] at h2
      have h3 := hc.dvd_of_dvd_mul_left h2
      rcases hu with rfl | rfl
      · exact small (q := p) (t := r - i) (by linarith) (by linarith) (by simpa using h3)
      · exact small (q := p) (t := r + i) (by linarith) (by linarith)
          (dvd_neg.1 (by rw [show -((r : ℤ) + i) = -1 * r - i by ring]; exact h3))
  -- `Γ(N + x/q) ≠ 0` when `q ∤ x`
  have gam : ∀ {q : ℕ}, 0 < q → ∀ {x : ℤ}, ¬ (q : ℤ) ∣ x → ∀ (z : ℂ) (N : ℤ),
      z = (x : ℂ) / q + N → Complex.Gamma z ≠ 0 := by
    intro q hq x hx z N hz
    have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    refine Complex.Gamma_ne_zero fun M h => hx ?_
    rw [hz] at h
    have h1 : (x : ℂ) / q = -(M : ℂ) - N := by linear_combination h
    have h2 : (x : ℂ) = (-(M : ℂ) - N) * q := by rw [← h1, div_mul_cancel₀ _ hqc]
    have h3 : x = (-(M : ℤ) - N) * q := by exact_mod_cast h2
    exact ⟨-(M : ℤ) - N, by rw [h3]; ring⟩
  unfold psiNode PsiPot
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i hi => ?_)
    (Finset.prod_ne_zero_iff.2 fun i hi => ?_) <;> rw [Finset.mem_Icc] at hi
  · refine inv_ne_zero (mul_ne_zero (gam hp' (hS i hi.1 hi.2).1 _ 1 ?_)
      (gam hp' (hS i hi.1 hi.2).2 _ 1 ?_))
    · rw [hb]; push_cast; field_simp; ring
    · rw [hb]; push_cast; field_simp; ring
  · refine inv_ne_zero (mul_ne_zero (gam hp (hR i hi.1 hi.2).1 _ (1 + m) ?_)
      (gam hp (hR i hi.1 hi.2).2 _ (1 + m) ?_))
    · have e : 2 * ((n : ℂ) * b / (2 * p')) * b = (n : ℂ) * b ^ 2 / p' := by field_simp
      rw [e, hb]; push_cast; field_simp; ring
    · have e : 2 * ((n : ℂ) * b / (2 * p')) * b = (n : ℂ) * b ^ 2 / p' := by field_simp
      rw [e, hb]; push_cast; field_simp; ring

/-- Equation (12.3) (l.2825–2832): `c(α → β) Ψ(ϖ_α;b⋆) = Ψ(ϖ_β;b⋆)`. -/
theorem cArrow_psi (ε : Bool) (j : ℕ) (ε' : Bool) :
    ((cArrow p p' r s k m ε j ε' : ℚ) : ℂ) * psiNode p' k m b (nOrb p p' r s ε j) =
      psiNode p' k m b (nOrb p p' r s ε' (j + 1)) := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨R, S, -, -, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε j ε'
  have hc : cArrow p p' r s k m ε j ε' = cMM p p' R S k m := by
    unfold cArrow
    rw [arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)]
  have h := cMM_psi hcop hr0 hr hs0 hs hb hcR hcS hk hm
  rw [PsiPot_in_node hp hp' hb, PsiPot_out_node hp hp' hb, hsum] at h
  rw [hc]
  rcases hdiff with hd | hd
  · rwa [hd] at h
  · rwa [hd, psiNode_neg] at h

/-- The product of the box ratios along a path is the ratio of the potentials at its ends
(l.2833–2836). -/
theorem pathProd_psi : ∀ (l : List Bool) (ε : Bool) (j : ℕ) (e : Bool), l.getLast? = some e →
    ((pathProd p p' r s k m ε j l : ℚ) : ℂ) * psiNode p' k m b (nOrb p p' r s ε j) =
      psiNode p' k m b (nOrb p p' r s e (j + l.length))
  | [], _, _, _, h => by simp at h
  | [ε'], ε, j, e, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    simp only [pathProd, mul_one, List.length_singleton]
    exact cArrow_psi hset hk hm ε j ε'
  | ε' :: x :: l, ε, j, e, h => by
    rw [List.getLast?_cons_cons] at h
    have ih := pathProd_psi (x :: l) ε' (j + 1) e h
    have h1 := cArrow_psi hset hk hm ε j ε'
    have e2 : j + (ε' :: x :: l).length = j + 1 + (x :: l).length := by
      simp only [List.length_cons]; omega
    rw [e2, ← ih, ← h1]
    simp only [pathProd]
    push_cast
    ring

end Orbit

/-- Paper label: prop:bgg-cocycle -/
theorem prop_bgg_cocycle : Stmt_prop_bgg_cocycle := by
  intro p p' r s b hset k m hk hm
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  refine ⟨fun ε j ε' => ?_, fun ε j ε'' => ?_, fun ε j l l' hl hlen hlast => ?_⟩
  · -- (i), l.2785–2803
    obtain ⟨R, S, -, -, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε j ε'
    have hL := arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)
    have hkR : k < R := lt_of_lt_of_le hk (min_le_of_congr hcR)
    have hmS : m < S := lt_of_lt_of_le hm (min_le_of_congr hcS)
    have hne := symdiff_factor_ne hcop hr0 hr hs0 hs hcR hcS hk hm
    simp only [hL]
    exact ⟨hne, box_ratio_value hp hkR hmS hne⟩
  · -- (ii), the diamond (l.2833–2834)
    have h0 := psiNode_ne_zero hset hk hm ε j
    have a1 := cArrow_psi hset hk hm ε j true
    have a2 := cArrow_psi hset hk hm true (j + 1) ε''
    have b1 := cArrow_psi hset hk hm ε j false
    have b2 := cArrow_psi hset hk hm false (j + 1) ε''
    have key : ((cArrow p p' r s k m ε j true * cArrow p p' r s k m true (j + 1) ε'' : ℚ) : ℂ) =
        ((cArrow p p' r s k m ε j false * cArrow p p' r s k m false (j + 1) ε'' : ℚ) : ℂ) := by
      refine mul_right_cancel₀ h0 ?_
      push_cast
      rw [mul_right_comm, a1, mul_comm, a2, mul_right_comm, b1, mul_comm, b2]
    exact_mod_cast key
  · -- path independence (l.2834–2836)
    have h0 := psiNode_ne_zero hset hk hm ε j
    obtain ⟨e, he⟩ : ∃ e, l.getLast? = some e := by
      cases h : l.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) hl
      | some e => exact ⟨e, rfl⟩
    have h1 := pathProd_psi hset hk hm l ε j e he
    have h2 := pathProd_psi hset hk hm l' ε j e (hlast ▸ he)
    rw [hlen] at h1
    have key : ((pathProd p p' r s k m ε j l : ℚ) : ℂ) = ((pathProd p p' r s k m ε j l' : ℚ) : ℂ) :=
      mul_right_cancel₀ h0 (h1.trans h2.symm)
    exact_mod_cast key

example : Stmt_prop_bgg_cocycle := prop_bgg_cocycle

end Virasoro
