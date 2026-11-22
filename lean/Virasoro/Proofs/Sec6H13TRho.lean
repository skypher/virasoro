import Virasoro.Proofs.Sec6H13TBr
import Virasoro.Proofs.PairingConstr

/-!
# Proposition 6.8(ii): the `ρ̃` end in `ℚ[Y,Y⁻¹]⸨t⸩` (paper.tex l.1333–1366)

With `c = 6/t + 13 + 6t`, `Δ = Y/t²`, `d = −2/t + ζ` (`ζ = −1, 2`), the entry
`(M!/2^M) Y^M D₀⁻¹(λ_b) ρ̃_{λ_b,λ_k}` (`λ_b = (1^{a_b}, μ_b)`, `λ_k = (1^{a_k}, μ_k)`) is a sum over
`(p₁, r, p₂, q, s)` of
`σ 2^{−(w_k+p₁+r+k+q+s)}/(K_{μ_b} p₁! p₂! k! q! s!) · M^{\underline{w_b+p₁+r}} a_k^{\underline{k+q+s}}
 t^{ℓ_b+ℓ_k+p₁+p₂+q+s} Y^{w_b−ℓ_b} ∏_{u<m_L}(1 + (1+u−ζ)t/2) ∏_{i<m'}(1 + (m'−m_L−ζ−i)t/2)
 ∏_{u<k}(2Y + (a_k−k+u)t²) · ⟨bracket⟩`, `k = r − p₂`, `m_L = a_b − p₁ − r`, `m' = a_k − k − q − s`
(the paper's `M!/s_R!`, `a_r!/s_L!`, `(−2)^{s_L+s_R}/(2^M 2^{a_0})`, l.1344–1352).
-/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Verma Finset

/-- `ζ_ν`: `d_ν = −2/t + ζ_ν`. -/
def zeta (ν : Fin 2) : ℚ := if ν = 0 then -1 else 2

/-- `d_ν = −2/t + ζ_ν` in `LL`. -/
noncomputable def dL (ν : Fin 2) : LL := mono (-1) 0 (-2) + cL (zeta ν)

theorem fL_dS (ν : Fin 2) : fL (dS ν) = tL * dL ν := by
  have e1 : dS ν = Polynomial.C (Polynomial.C (-2)) + Polynomial.C (Polynomial.C (zeta ν)) * tS := by
    rw [dS, tS, zeta]
    split_ifs <;> simp only [map_add, map_mul, map_neg, map_ofNat, map_sub, map_one] <;> ring
  rw [e1, map_add, map_mul, fL_CC, fL_CC, fL_tS, dL, mul_add, cL_eq_mono, cL_eq_mono, tL]
  simp only [mono_mul]
  norm_num

/-- `ρ̃_{Y,w} = t^{ℓ(Y)+ℓ(w)} ⟨Δ|L_Y V_d(1) L_{−w}|Δ⟩` in `LL`. -/
theorem fL_torusWordT (ν : Fin 2) (Y w : List ℕ) (hY : ∀ y ∈ Y, 0 < y) :
    fL (torusWordT tS cS Polynomial.X (dS ν) Y w) =
      tL ^ (Y.length + w.length) * torusWord cLc DL (dL ν) Y w := by
  rw [← torusWordT_map fL, fL_tS, fL_cS, fL_X, fL_dS, ← tL_sq_DL,
    torusWordT_eq tL cLc DL (dL ν) Y w hY]

theorem torusWord_eq_pairing (ν : Fin 2) (Y w : List ℕ) (hY : PosWord Y) (hw : PosWord w) :
    torusWord cLc DL (dL ν) Y w = pairing cLc DL (dL ν) (neg Y) (neg w) :=
  (primary_torusWord (isPrimaryPairing_pairing (dL ν)) Y hY w hw).symm

/-! ### The three products -/

theorem mono_add (e f : ℤ) (r r' : ℚ) : mono e f r + mono e f r' = mono e f (r + r') := by
  rw [mono, mono, mono, ← HahnSeries.single_add]
  congr 1
  rw [map_add, add_mul]

theorem two_mul_DL : (2 : LL) * DL = mono (-2) 1 2 := by
  rw [DL, show (2 : LL) = cL 2 from (map_ofNat cL 2).symm, cL_mul_mono, mul_one]

theorem tL_mul_dL (ν : Fin 2) (x : ℚ) :
    tL * (dL ν + cL x) = mono 0 0 (-2) * (1 + cL (-(zeta ν + x) / 2) * tL) := by
  rw [dL, tL, cL_eq_mono, cL_eq_mono, cL_eq_mono]
  simp only [mul_add, mul_one, mono_mul]
  norm_num
  rw [add_assoc, mono_add]
  congr 2
  ring

theorem prod_gen (ν : Fin 2) (x : ℕ → ℚ) (m : ℕ) :
    tL ^ m * ∏ u ∈ range m, (dL ν + cL (x u)) =
      mono 0 0 ((-2) ^ m) * ∏ u ∈ range m, (1 + cL (-(zeta ν + x u) / 2) * tL) := by
  induction m with
  | zero => simp [mono_zero_one]
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, pow_succ]
    calc tL ^ m * tL * ((∏ u ∈ range m, (dL ν + cL (x u))) * (dL ν + cL (x m)))
        = (tL ^ m * ∏ u ∈ range m, (dL ν + cL (x u))) * (tL * (dL ν + cL (x m))) := by ring
      _ = _ := by
        rw [ih, tL_mul_dL, pow_succ]
        rw [show mono 0 0 ((-2) ^ m * -2) = mono 0 0 ((-2) ^ m) * mono 0 0 (-2) by
          rw [mono_mul]; norm_num]
        ring

/-- `t^{m}∏_{u<m}(d − 1 − u) = (−2)^m ∏_{u<m}(1 + (1+u−ζ)t/2)`. -/
theorem prod_P1 (ν : Fin 2) (m : ℕ) :
    tL ^ m * ∏ u ∈ range m, (dL ν + cL (-1 - (u : ℚ))) =
      mono 0 0 ((-2) ^ m) * ∏ u ∈ range m, (1 + cL ((1 + (u : ℚ) - zeta ν) / 2) * tL) := by
  rw [prod_gen ν (fun u => -1 - (u : ℚ)) m]
  congr 1
  exact prod_congr rfl fun u _ => by congr 3; ring

/-- `t^{m'}∏_{i<m'}(d + m_L − 1 − i) = (−2)^{m'} ∏_{i<m'}(1 + (m' − m_L − ζ − i)t/2)`. -/
theorem prod_P2 (ν : Fin 2) (m' mL : ℕ) :
    tL ^ m' * ∏ i ∈ range m', (dL ν + cL ((mL : ℚ) - 1 - (i : ℚ))) =
      mono 0 0 ((-2) ^ m') *
        ∏ i ∈ range m', (1 + cL (((m' : ℚ) - mL - zeta ν - i) / 2) * tL) := by
  rw [prod_gen ν (fun i => (mL : ℚ) - 1 - (i : ℚ)) m']
  congr 1
  rw [← prod_range_reflect]
  refine prod_congr rfl fun i hi => ?_
  have hi' : i < m' := mem_range.1 hi
  congr 3
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- `t^{2k}∏_{s∈[a−k,a)}(2Δ + s) = ∏_{u<k}(2Y + (a−k+u)t²)`. -/
theorem prod_PI (a k : ℕ) (hk : k ≤ a) :
    tL ^ (2 * k) * ∏ s ∈ Ico (a - k) a, (2 * DL + (s : LL)) =
      ∏ u ∈ range k, (mono 0 1 2 + cL (((a - k + u : ℕ)) : ℚ) * mono 2 0 1) := by
  have e1 : tL ^ (2 * k) = ∏ _u ∈ range k, tL ^ 2 := by rw [prod_const, card_range, pow_mul]
  rw [prod_Ico_eq_prod_range, show a - (a - k) = k by omega, e1, ← prod_mul_distrib]
  refine prod_congr rfl fun u _ => ?_
  rw [cast_LL, two_mul_DL, mul_add, tL, mono_pow, cL_eq_mono]
  simp only [mono_mul]
  norm_num

/-! ### The normalized term -/

/-- The normalized `(p₁, r, p₂, q, s)`-term of the `ρ̃` end, `k = r − p₂`. -/
noncomputable def rhoN (ν : Fin 2) (μb μk : List ℕ) (M p1 r p2 q s : ℕ) : LL :=
  cL ((-1 : ℚ) ^ (μb.sum + μk.sum + p1 + p2 + q + s) /
      (2 ^ (μk.sum + p1 + p2 + 2 * (r - p2) + q + s) * (topNat μb μb : ℚ) * (p1.factorial : ℚ) *
        (p2.factorial : ℚ) * ((r - p2).factorial : ℚ) * (q.factorial : ℚ) * (s.factorial : ℚ))) *
  cL ((M.descFactorial (μb.sum + p1 + r) : ℕ) : ℚ) *
  cL (((M - μk.sum).descFactorial ((r - p2) + q + s) : ℕ) : ℚ) *
  mono (μb.length + μk.length + p1 + p2 + q + s) ((μb.sum : ℤ) - μb.length) 1 *
  (∏ u ∈ range (M - μb.sum - p1 - r), (1 + cL ((1 + (u : ℚ) - zeta ν) / 2) * tL)) *
  (∏ i ∈ range (M - μk.sum - (r - p2) - q - s),
    (1 + cL ((((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) - zeta ν - i)
      / 2) * tL)) *
  (∏ u ∈ range (r - p2), (mono 0 1 2 + cL (((M - μk.sum - (r - p2) + u : ℕ)) : ℚ) * mono 2 0 1)) *
  torBr (pairing cLc DL (dL ν)) μb μk p1 s p2 q

theorem factor_P1 (ν : Fin 2) {wb wk ar a0 p1 : ℕ} (hrel : wb + ar = wk + a0) (hp : p1 ≤ ar)
    (u : ℕ) :
    dL ν + (DL + (((wb : ℤ) + p1 : ℤ) : LL)) - (DL + ((wk + a0 : ℕ) : LL)) + ((ar - p1 : ℕ) : LL) -
      1 - (u : LL) = dL ν + cL (-1 - (u : ℚ)) := by
  have h0 : (((wb : ℤ) + p1 : ℤ) : LL) - ((wk + a0 : ℕ) : LL) + ((ar - p1 : ℕ) : LL) = 0 := by
    have hz : ((wb : ℤ) + p1) - ((wk + a0 : ℕ) : ℤ) + ((ar - p1 : ℕ) : ℤ) = 0 := by omega
    have := congrArg (fun z : ℤ => (z : LL)) hz
    simpa using this
  rw [map_sub, map_neg, map_one, map_natCast]
  linear_combination h0

theorem factor_P2 (ν : Fin 2) {wb wk ar a0 p1 mL p2 q : ℕ} (hrel : wb + ar = wk + a0)
    (hp : p1 + mL + p2 ≤ ar) (hq : ar - p1 - mL - p2 + q ≤ a0) (i : ℕ) :
    dL ν + (DL + (((wk : ℤ) - p2 + q : ℤ) : LL)) - (DL + (((wb : ℤ) + p1 : ℤ) : LL)) +
      ((a0 - (ar - p1 - mL - p2) - q : ℕ) : LL) - 1 - (i : LL) =
      dL ν + cL ((mL : ℚ) - 1 - (i : ℚ)) := by
  have h0 : (((wk : ℤ) - p2 + q : ℤ) : LL) - (((wb : ℤ) + p1 : ℤ) : LL) +
      ((a0 - (ar - p1 - mL - p2) - q : ℕ) : LL) = (mL : LL) := by
    have hz : ((wk : ℤ) - p2 + q) - ((wb : ℤ) + p1) + ((a0 - (ar - p1 - mL - p2) - q : ℕ) : ℤ) =
        mL := by omega
    have := congrArg (fun z : ℤ => (z : LL)) hz
    simpa using this
  rw [map_sub, map_sub, map_one, map_natCast, map_natCast]
  linear_combination h0

/-- A raw summand of `torus_ones` at `(c, Δ, d) = (c(b), Y/t², d_ν)`. -/
noncomputable def rawT (ν : Fin 2) (μb μk : List ℕ) (ar a0 p1 mL p2 q m' : ℕ) : LL :=
  ((ar.choose p1 : ℕ) : LL) *
    ((((ar - p1).choose mL : ℕ) : LL) *
      (∏ u ∈ range mL, (dL ν + (DL + (((μb.sum : ℤ) + p1 : ℤ) : LL)) -
        (DL + ((μk.sum + a0 : ℕ) : LL)) + ((ar - p1 : ℕ) : LL) - 1 - (u : LL))) *
      ((((ar - p1 - mL).choose p2 : ℕ) : LL) *
        ((((a0.descFactorial (ar - p1 - mL - p2)) : ℕ) : LL) *
          ∏ s ∈ Ico (a0 - (ar - p1 - mL - p2)) a0, (2 * DL + (s : LL))) *
        ((((a0 - (ar - p1 - mL - p2)).choose q : ℕ) : LL) *
          ((((a0 - (ar - p1 - mL - p2) - q).choose m' : ℕ) : LL) *
            (∏ i ∈ range m', (dL ν + (DL + ((((μk.sum : ℤ) - p2) + q : ℤ) : LL)) -
              (DL + (((μb.sum : ℤ) + p1 : ℤ) : LL)) +
              ((a0 - (ar - p1 - mL - p2) - q : ℕ) : LL) - 1 - (i : LL))) *
            torBr (pairing cLc DL (dL ν)) μb μk p1 (a0 - (ar - p1 - mL - p2) - q - m') p2 q))))

theorem torus_ones_raw (ν : Fin 2) (μb μk : List ℕ) (ar a0 : ℕ) :
    pairing cLc DL (dL ν) (neg (μb ++ List.replicate ar 1)) (neg (μk ++ List.replicate a0 1)) =
      ∑ p1 ∈ range (ar + 1), ∑ mL ∈ range (ar - p1 + 1), ∑ p2 ∈ range (ar - p1 - mL + 1),
        ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
          ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1), rawT ν μb μk ar a0 p1 mL p2 q m' := by
  rw [torus_ones (isPrimaryPairing_pairing (dL ν))]
  simp only [mul_sum]
  rfl

theorem cast_descFactorial_q {n k : ℕ} (h : k ≤ n) :
    ((n.descFactorial k : ℕ) : ℚ) = (n.factorial : ℚ) / ((n - k).factorial : ℚ) := by
  have := Nat.factorial_mul_descFactorial h
  have h0 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff h0, mul_comm]
  exact_mod_cast this

/-- The scalar identity of the normalized `ρ̃`-end term. -/
theorem rho_scalar {wb wk M p1 mL p2 k q m' s K : ℕ} (hK : (K : ℚ) ≠ 0)
    (hM1 : M = wb + (p1 + mL + p2 + k)) (hM2 : M = wk + (k + q + m' + s)) :
    (M.factorial : ℚ) / 2 ^ M * (1 / (((p1 + mL + p2 + k).factorial * 2 ^ (p1 + mL + p2 + k) * K :
        ℕ) : ℚ)) * ((p1 + mL + p2 + k).choose p1 : ℚ) * ((mL + p2 + k).choose mL : ℚ) *
        (-2) ^ mL * ((p2 + k).choose p2 : ℚ) *
        (((k + q + m' + s).descFactorial k : ℕ) : ℚ) * ((q + m' + s).choose q : ℚ) *
        ((m' + s).choose m' : ℚ) * (-2) ^ m' =
      (-1 : ℚ) ^ (wb + wk + p1 + p2 + q + s) /
          (2 ^ (wk + p1 + p2 + 2 * k + q + s) * (K : ℚ) * (p1.factorial : ℚ) *
            (p2.factorial : ℚ) * (k.factorial : ℚ) * (q.factorial : ℚ) * (s.factorial : ℚ)) *
        ((M.descFactorial (wb + p1 + (p2 + k)) : ℕ) : ℚ) *
        (((M - wk).descFactorial (k + q + s) : ℕ) : ℚ) := by
  have hd1 : M - (wb + p1 + (p2 + k)) = mL := by omega
  have hd2 : M - wk = k + q + m' + s := by omega
  have hd3 : k + q + m' + s - (k + q + s) = m' := by omega
  rw [cast_descFactorial_q (n := M) (k := wb + p1 + (p2 + k)) (by omega), hd1,
    cast_descFactorial_q (n := M - wk) (k := k + q + s) (by omega), hd2, hd3,
    cast_descFactorial_q (n := k + q + m' + s) (k := k) (by omega),
    show k + q + m' + s - k = q + m' + s by omega,
    Nat.cast_choose ℚ (a := p1) (b := p1 + mL + p2 + k) (by omega),
    Nat.cast_choose ℚ (a := mL) (b := mL + p2 + k) (by omega),
    Nat.cast_choose ℚ (a := p2) (b := p2 + k) (by omega),
    Nat.cast_choose ℚ (a := q) (b := q + m' + s) (by omega),
    Nat.cast_choose ℚ (a := m') (b := m' + s) (by omega)]
  rw [show p1 + mL + p2 + k - p1 = mL + p2 + k by omega, show mL + p2 + k - mL = p2 + k by omega,
    show p2 + k - p2 = k by omega, show q + m' + s - q = m' + s by omega,
    show m' + s - m' = s by omega]
  -- the powers of 2 and the sign
  have hexp : mL + m' + (wk + p1 + p2 + 2 * k + q + s) = M + (p1 + mL + p2 + k) := by omega
  have h2 : (2 : ℚ) ^ (mL + m') * 2 ^ (wk + p1 + p2 + 2 * k + q + s) =
      2 ^ M * 2 ^ (p1 + mL + p2 + k) := by
    rw [← pow_add, ← pow_add, hexp]
  have hsg : (-1 : ℚ) ^ (mL + m') = (-1) ^ (wb + wk + p1 + p2 + q + s) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := wb + wk + p1 + p2 + q + s)]
    congr 1
    omega
  have hm2 : (-2 : ℚ) ^ mL * (-2) ^ m' = (-1) ^ (mL + m') * 2 ^ (mL + m') := by
    rw [← pow_add, ← mul_pow]
    norm_num
  push_cast
  have hf : ∀ n : ℕ, (n.factorial : ℚ) ≠ 0 := fun n => by positivity
  have h2M : (2 : ℚ) ^ M ≠ 0 := by positivity
  have h2a : (2 : ℚ) ^ (p1 + mL + p2 + k) ≠ 0 := by positivity
  have h2E : (2 : ℚ) ^ (wk + p1 + p2 + 2 * k + q + s) ≠ 0 := by positivity
  rw [show (M.factorial : ℚ) / 2 ^ M * (1 / ((p1 + mL + p2 + k).factorial *
      2 ^ (p1 + mL + p2 + k) * (K : ℚ))) * ((p1 + mL + p2 + k).factorial /
      (p1.factorial * (mL + p2 + k).factorial)) * ((mL + p2 + k).factorial /
      (mL.factorial * (p2 + k).factorial)) * (-2) ^ mL * ((p2 + k).factorial /
      (p2.factorial * k.factorial)) * ((k + q + m' + s).factorial / (q + m' + s).factorial) *
      ((q + m' + s).factorial / (q.factorial * (m' + s).factorial)) *
      ((m' + s).factorial / (m'.factorial * s.factorial)) * (-2) ^ m' =
      (M.factorial : ℚ) * (k + q + m' + s).factorial *
        ((-2) ^ mL * (-2) ^ m' / (2 ^ M * 2 ^ (p1 + mL + p2 + k))) /
        ((K : ℚ) * p1.factorial * mL.factorial * p2.factorial * k.factorial * q.factorial *
          m'.factorial * s.factorial) by field_simp]
  rw [hm2, hsg, show (-1 : ℚ) ^ (wb + wk + p1 + p2 + q + s) * 2 ^ (mL + m') /
      (2 ^ M * 2 ^ (p1 + mL + p2 + k)) =
      (-1 : ℚ) ^ (wb + wk + p1 + p2 + q + s) / 2 ^ (wk + p1 + p2 + 2 * k + q + s) by
    rw [div_eq_div_iff (mul_ne_zero h2M h2a) h2E, ← h2]; ring]
  field_simp

theorem mono_eq_of {e f e' f' : ℤ} {r r' : ℚ} (he : e = e') (hf : f = f') (hr : r = r') :
    mono e f r = mono e' f' r' := by rw [he, hf, hr]

theorem tL_pow (n : ℕ) : tL ^ n = mono n 0 1 := by
  rw [tL, mono_pow]
  norm_num

/-- One raw summand times the prefactor `(M!/2^M) Y^M D₀⁻¹(λ_b) t^{ℓ(λ_b)+ℓ(λ_k)}` is the normalized
term (paper.tex l.1344–1352). -/
theorem rho_term_eq (ν : Fin 2) (μb μk : List ℕ) (hμb : ∀ y ∈ μb, 2 ≤ y)
    {M ar a0 p1 mL p2 k q m' s : ℕ} (hM1 : M = μb.sum + ar) (hM2 : M = μk.sum + a0)
    (har : ar = p1 + mL + p2 + k) (ha0 : a0 = k + q + m' + s) :
    cL ((M.factorial : ℚ) / 2 ^ M) * mono 0 M 1 *
        (cL (1 / (topNat (μb ++ List.replicate ar 1) (μb ++ List.replicate ar 1) : ℚ)) *
          mono 0 (-((μb.length + ar : ℕ) : ℤ)) 1) *
        tL ^ ((μb.length + ar) + (μk.length + a0)) * rawT ν μb μk ar a0 p1 mL p2 q m' =
      rhoN ν μb μk M p1 (p2 + k) p2 q s := by
  have hrel : μb.sum + ar = μk.sum + a0 := by omega
  have hP1 := prod_congr (s₁ := range mL) rfl
    fun u (_ : u ∈ range mL) => factor_P1 ν hrel (by omega : p1 ≤ ar) u
  have hP2 := prod_congr (s₁ := range m') rfl
    fun i (_ : i ∈ range m') => factor_P2 ν (p1 := p1) (mL := mL) (p2 := p2) (q := q) hrel (by omega)
      (by omega) i
  unfold rawT
  rw [hP1, hP2]
  subst har ha0
  rw [show p1 + mL + p2 + k - p1 = mL + p2 + k by omega,
    show mL + p2 + k - mL = p2 + k by omega, show p2 + k - p2 = k by omega,
    show k + q + m' + s - k = q + m' + s by omega, show q + m' + s - q = m' + s by omega,
    show m' + s - m' = s by omega]
  unfold rhoN
  rw [show M - μb.sum - p1 - (p2 + k) = mL by omega, show p2 + k - p2 = k by omega,
    show M - μk.sum - k - q - s = m' by omega]
  -- the products
  have hL : (μb.length + (p1 + mL + p2 + k)) + (μk.length + (k + q + m' + s)) =
      mL + m' + 2 * k + (μb.length + μk.length + p1 + p2 + q + s) := by omega
  rw [hL, pow_add, pow_add, pow_add]
  have hQ3 : ∀ u ∈ range k, mono 0 1 2 + cL (((q + m' + s + u : ℕ)) : ℚ) * mono 2 0 1 =
      mono 0 1 2 + cL (((M - μk.sum - k + u : ℕ)) : ℚ) * mono 2 0 1 := by
    intro u _
    rw [show q + m' + s + u = M - μk.sum - k + u by omega]
  have hQ2 : ∀ i ∈ range m', 1 + cL (((m' : ℚ) - mL - zeta ν - i) / 2) * tL =
      1 + cL ((((μb.sum + p1 + (p2 + k) : ℕ) : ℚ) - ((μk.sum + k + q + s : ℕ) : ℚ) - zeta ν - i)
        / 2) * tL := by
    intro i _
    have : (m' : ℚ) - mL = ((μb.sum + p1 + (p2 + k) : ℕ) : ℚ) - ((μk.sum + k + q + s : ℕ) : ℚ) := by
      have h1 : ((μb.sum + (p1 + mL + p2 + k) : ℕ) : ℚ) = ((μk.sum + (k + q + m' + s) : ℕ) : ℚ) := by
        rw [hrel]
      push_cast at h1 ⊢
      linarith
    rw [show ((m' : ℚ) - mL - zeta ν - i) = (((μb.sum + p1 + (p2 + k) : ℕ) : ℚ) -
      ((μk.sum + k + q + s : ℕ) : ℚ) - zeta ν - i) by rw [← this]]
  have hPI := prod_PI (k + q + m' + s) k (by omega)
  rw [show k + q + m' + s - k = q + m' + s by omega] at hPI
  -- collect
  set Q1 := ∏ u ∈ range mL, (1 + cL ((1 + (u : ℚ) - zeta ν) / 2) * tL) with hQ1
  set Q2 := ∏ i ∈ range m', (1 + cL ((((μb.sum + p1 + (p2 + k) : ℕ) : ℚ) -
      ((μk.sum + k + q + s : ℕ) : ℚ) - zeta ν - i) / 2) * tL) with hQ2'
  set Q3 := ∏ u ∈ range k, (mono 0 1 2 + cL (((M - μk.sum - k + u : ℕ)) : ℚ) * mono 2 0 1)
    with hQ3'
  set Br := torBr (pairing cLc DL (dL ν)) μb μk p1 s p2 q with hBr
  have e1 := prod_P1 ν mL
  have e2 := prod_P2 ν m' mL
  rw [prod_congr rfl hQ2] at e2
  rw [prod_congr rfl hQ3] at hPI
  have hscal : cL ((M.factorial : ℚ) / 2 ^ M) * mono 0 M 1 *
      (cL (1 / (topNat (μb ++ List.replicate (p1 + mL + p2 + k) 1)
        (μb ++ List.replicate (p1 + mL + p2 + k) 1) : ℚ)) *
        mono 0 (-((μb.length + (p1 + mL + p2 + k) : ℕ) : ℤ)) 1) *
      tL ^ (μb.length + μk.length + p1 + p2 + q + s) *
      (((p1 + mL + p2 + k).choose p1 : ℕ) : LL) * (((mL + p2 + k).choose mL : ℕ) : LL) *
      mono 0 0 ((-2) ^ mL) * (((p2 + k).choose p2 : ℕ) : LL) *
      ((((k + q + m' + s).descFactorial k) : ℕ) : LL) * (((q + m' + s).choose q : ℕ) : LL) *
      (((m' + s).choose m' : ℕ) : LL) * mono 0 0 ((-2) ^ m') =
      cL ((-1 : ℚ) ^ (μb.sum + μk.sum + p1 + p2 + q + s) /
        (2 ^ (μk.sum + p1 + p2 + 2 * k + q + s) * (topNat μb μb : ℚ) * (p1.factorial : ℚ) *
          (p2.factorial : ℚ) * (k.factorial : ℚ) * (q.factorial : ℚ) * (s.factorial : ℚ))) *
      cL ((M.descFactorial (μb.sum + p1 + (p2 + k)) : ℕ) : ℚ) *
      cL (((M - μk.sum).descFactorial (k + q + s) : ℕ) : ℚ) *
      mono (μb.length + μk.length + p1 + p2 + q + s) ((μb.sum : ℤ) - μb.length) 1 := by
    rw [topNat_append_ones μb hμb, tL_pow]
    simp only [cast_LL, cL_eq_mono, mono_mul]
    refine mono_eq_of (by push_cast; ring) (by omega) ?_
    have hK : (topNat μb μb : ℚ) ≠ 0 := by
      rw [topNat_perm _ _ (List.Perm.refl _)]
      have : 0 < μb.prod := List.prod_pos fun y hy => by have := hμb y hy; omega
      have : 0 < facs (μb : Multiset ℕ) := Finset.prod_pos fun n _ => Nat.factorial_pos _
      positivity
    have := rho_scalar (wb := μb.sum) (wk := μk.sum) (M := M) (p1 := p1) (mL := mL) (p2 := p2)
      (k := k) (q := q) (m' := m') (s := s) (K := topNat μb μb) hK (by omega) (by omega)
    rw [← this]
    push_cast
    ring
  calc _ = (cL ((M.factorial : ℚ) / 2 ^ M) * mono 0 M 1 *
      (cL (1 / (topNat (μb ++ List.replicate (p1 + mL + p2 + k) 1)
        (μb ++ List.replicate (p1 + mL + p2 + k) 1) : ℚ)) *
        mono 0 (-((μb.length + (p1 + mL + p2 + k) : ℕ) : ℤ)) 1) *
      tL ^ (μb.length + μk.length + p1 + p2 + q + s) *
      (((p1 + mL + p2 + k).choose p1 : ℕ) : LL) * (((mL + p2 + k).choose mL : ℕ) : LL) *
      (((p2 + k).choose p2 : ℕ) : LL) *
      ((((k + q + m' + s).descFactorial k) : ℕ) : LL) * (((q + m' + s).choose q : ℕ) : LL) *
      (((m' + s).choose m' : ℕ) : LL)) *
      (tL ^ mL * ∏ u ∈ range mL, (dL ν + cL (-1 - (u : ℚ)))) *
      (tL ^ m' * ∏ i ∈ range m', (dL ν + cL ((mL : ℚ) - 1 - (i : ℚ)))) *
      (tL ^ (2 * k) * ∏ s ∈ Ico (q + m' + s) (k + q + m' + s), (2 * DL + (s : LL))) * Br := by
        ring
    _ = _ := by
        rw [e1, e2, hPI]
        rw [← hscal]
        ring

end Virasoro.H13T
