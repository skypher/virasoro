import Virasoro.Proofs.Sec6LimGr3
import Virasoro.Proofs.Sec6LimChain

/-!
# Proposition 6.7, the chain limit (b): the two lines `S = 1` and `S = 0` (paper.tex l.1141–1146)

* `σ₁ : ℂ[S,W,Y][[t]] → K⸨t⸩` for a field `K ⊇ ℂ` and `w, y ∈ K`, `S ↦ 1`, `W ↦ 2b⋆w`, `Y ↦ 2b⋆y`: the line
  `(b⋆ + t, λ + 2b⋆w t, 2b⋆y t)` of the germ computation;
* `σ₀ : ℂ[S,W,Y][[t]] → ℂ[d][u][[t]]`, `S ↦ 0`, `W ↦ u`, `Y ↦ d`: the line `b = b⋆`;
* `γ : ℂ[d][u] → ℂ[d][u][[t]]`, `u ↦ u t`, `d ↦ d t`, whose `t^i` coefficient is the part of total
  degree `i`.
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries
open PowerSeries

/-! ### The line `S = 1` -/

section Line1

variable {K : Type} [Field K] [CharZero K] [Algebra ℂ K]

/-- `S ↦ 1`, `W ↦ 2b⋆w`, `Y ↦ 2b⋆y`. -/
noncomputable def ev1 (bs : ℂ) (w y : K) : R3 →+* K :=
  (MvPolynomial.aeval ![(1 : K), 2 * algebraMap ℂ K bs * w, 2 * algebraMap ℂ K bs * y]).toRingHom

/-- `σ₁`, coefficientwise `ev1`. -/
noncomputable def sig1 (bs : ℂ) (w y : K) : PS →+* K⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (ev1 bs w y))

variable (bs : ℂ) (w y : K)

theorem sig1_C (r : R3) : sig1 bs w y (PowerSeries.C r) = HahnSeries.C (ev1 bs w y r) := by
  simp [sig1]

theorem sig1_X : sig1 bs w y PowerSeries.X = tX := by
  simp [sig1, HahnSeries.ofPowerSeries_X, tX]

theorem ev1_C (z : ℂ) : ev1 bs w y (MvPolynomial.C z) = algebraMap ℂ K z := by
  simp [ev1]

theorem ev1_X0 : ev1 bs w y (MvPolynomial.X 0) = 1 := by
  simp [ev1]

theorem ev1_X1 : ev1 bs w y (MvPolynomial.X 1) = 2 * algebraMap ℂ K bs * w := by
  simp [ev1]

theorem ev1_X2 : ev1 bs w y (MvPolynomial.X 2) = 2 * algebraMap ℂ K bs * y := by
  simp [ev1]

theorem sig1_Bb : sig1 bs w y (Bb bs) = bGerm (algebraMap ℂ K bs) := by
  rw [Bb, map_add, map_mul, sig1_C, sig1_C, sig1_X, ev1_C, ev1_X0, map_one, one_mul, bGerm_eq]

variable {bs} in
theorem sig1_Binv (hbs : bs ≠ 0) : sig1 bs w y (Binv bs) = (bGerm (algebraMap ℂ K bs))⁻¹ := by
  have h := congrArg (sig1 bs w y) (Bb_mul_Binv bs hbs)
  rw [map_mul, map_one, sig1_Bb] at h
  exact eq_inv_of_mul_eq_one_right h

variable {bs} in
theorem sig1_cR (hbs : bs ≠ 0) : sig1 bs w y (cR bs) = kacC (bGerm (algebraMap ℂ K bs)) := by
  rw [cR, kacC, map_add, map_one, map_mul, map_pow, map_add, sig1_Bb, sig1_Binv w y hbs,
    map_ofNat]

theorem sig1_DR (lam : ℂ) : sig1 bs w y (DR lam) =
    HahnSeries.C (algebraMap ℂ K lam) + tX * HahnSeries.C (2 * algebraMap ℂ K bs * w) := by
  rw [DR, map_add, map_mul, sig1_C, sig1_C, sig1_X, ev1_C, ev1_X1, mul_comm (HahnSeries.C _)]

theorem sig1_dR : sig1 bs w y dR = tX * HahnSeries.C (2 * algebraMap ℂ K bs * y) := by
  rw [dR, map_mul, sig1_C, sig1_X, ev1_X2, mul_comm]

theorem coeff_sig1 (f : PS) (i : ℕ) : (sig1 bs w y f).coeff (i : ℤ) = ev1 bs w y (coeff i f) := by
  simp [sig1, HahnSeries.ofPowerSeries_apply_coeff]

end Line1

/-! ### The line `S = 0` -/

/-- `ℂ[d][u]`: polynomials in the outer variable `u = Δ − λ` over `ℂ[d]`. -/
abbrev P2 : Type := Polynomial (Polynomial ℂ)

/-- `S ↦ 0`, `W ↦ u`, `Y ↦ d`. -/
noncomputable def ev0 : R3 →+* P2 :=
  (MvPolynomial.aeval ![(0 : P2), Polynomial.X, Polynomial.C Polynomial.X]).toRingHom

/-- `σ₀`, coefficientwise `ev0`. -/
noncomputable def sig0 : PS →+* PowerSeries P2 := PowerSeries.map ev0

theorem ev0_C (z : ℂ) : ev0 (MvPolynomial.C z) = Polynomial.C (Polynomial.C z) := by
  simp [ev0, Polynomial.algebraMap_apply]

theorem sig0_Bb (bs : ℂ) : sig0 (Bb bs) = PowerSeries.C (Polynomial.C (Polynomial.C bs)) := by
  simp [sig0, Bb, ev0_C, ev0]

theorem sig0_Binv {bs : ℂ} (hbs : bs ≠ 0) :
    sig0 (Binv bs) = PowerSeries.C (Polynomial.C (Polynomial.C bs⁻¹)) := by
  have h := congrArg sig0 (Bb_mul_Binv bs hbs)
  rw [map_mul, map_one, sig0_Bb] at h
  have h2 : PowerSeries.C (Polynomial.C (Polynomial.C bs)) *
      PowerSeries.C (Polynomial.C (Polynomial.C bs⁻¹)) = (1 : PowerSeries P2) := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hbs, map_one, map_one, map_one]
  calc sig0 (Binv bs) = sig0 (Binv bs) * (PowerSeries.C (Polynomial.C (Polynomial.C bs)) *
        PowerSeries.C (Polynomial.C (Polynomial.C bs⁻¹))) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, mul_comm (sig0 _), h, one_mul]

theorem sig0_cR {bs : ℂ} (hbs : bs ≠ 0) :
    sig0 (cR bs) = PowerSeries.C (Polynomial.C (Polynomial.C (kacC bs))) := by
  rw [cR, kacC, map_add, map_one, map_mul, map_pow, map_add, sig0_Bb, sig0_Binv hbs, map_ofNat]
  simp only [map_add, map_one, map_mul, map_pow, map_ofNat, map_inv₀]

theorem sig0_DR (lam : ℂ) : sig0 (DR lam) = PowerSeries.C (Polynomial.C (Polynomial.C lam)) +
    PowerSeries.C Polynomial.X * PowerSeries.X := by
  simp [sig0, DR, ev0_C, ev0]

theorem sig0_dR : sig0 dR = PowerSeries.C (Polynomial.C Polynomial.X) * PowerSeries.X := by
  simp [sig0, dR, ev0]

/-! ### The graded embedding `γ` -/

/-- `γ(f)(t) = f(u t, d t)`. -/
noncomputable def gam : P2 →+* PowerSeries P2 :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      ((PowerSeries.C : P2 →+* PowerSeries P2).comp ((Polynomial.C).comp Polynomial.C))
      (PowerSeries.C (Polynomial.C Polynomial.X) * PowerSeries.X))
    (PowerSeries.C Polynomial.X * PowerSeries.X)

theorem gam_CC (z : ℂ) : gam (Polynomial.C (Polynomial.C z)) =
    PowerSeries.C (Polynomial.C (Polynomial.C z)) := by
  simp [gam]

theorem gam_X : gam Polynomial.X = PowerSeries.C Polynomial.X * PowerSeries.X := by
  simp [gam]

theorem gam_CX : gam (Polynomial.C Polynomial.X) =
    PowerSeries.C (Polynomial.C Polynomial.X) * PowerSeries.X := by
  simp [gam]

theorem gam_monomial (a n : ℕ) (c : ℂ) :
    gam (Polynomial.monomial a (Polynomial.monomial n c)) =
      PowerSeries.C (Polynomial.monomial a (Polynomial.monomial n c)) * PowerSeries.X ^ (a + n) := by
  have e : Polynomial.monomial a (Polynomial.monomial n c) =
      Polynomial.C (Polynomial.C c) * (Polynomial.C Polynomial.X) ^ n * (Polynomial.X : P2) ^ a := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
      map_pow]
  rw [e]
  simp only [map_mul, map_pow, gam_CC, gam_X, gam_CX]
  ring

/-- The `t^i` coefficient of `γ f` is the part of `f` of total degree `i`. -/
theorem coeff_gam (f : P2) (i a n : ℕ) :
    ((coeff i (gam f)).coeff a).coeff n = if a + n = i then (f.coeff a).coeff n else 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, map_add, Polynomial.coeff_add, Polynomial.coeff_add, hf, hg]
    simp only [Polynomial.coeff_add]
    split_ifs <;> simp
  | monomial a' g =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 =>
      have e : Polynomial.monomial a' (g1 + g2) =
          Polynomial.monomial a' g1 + Polynomial.monomial a' g2 := map_add _ _ _
      rw [e, map_add, map_add, Polynomial.coeff_add, Polynomial.coeff_add, h1, h2]
      simp only [Polynomial.coeff_add]
      split_ifs <;> simp
    | monomial n' c =>
      rw [gam_monomial, coeff_C_mul_X_pow]
      by_cases h1 : i = a' + n'
      · rw [if_pos h1]
        split_ifs with h2
        · rfl
        · rw [Polynomial.coeff_monomial]
          split_ifs with h3
          · rw [Polynomial.coeff_monomial, if_neg (by omega)]
          · rw [Polynomial.coeff_zero]
      · rw [if_neg h1, Polynomial.coeff_zero, Polynomial.coeff_zero]
        split_ifs with h2
        · rw [Polynomial.coeff_monomial]
          split_ifs with h3
          · rw [Polynomial.coeff_monomial, if_neg (by omega)]
          · rw [Polynomial.coeff_zero]
        · rfl

end Virasoro.ChainLim
