import Virasoro.Sphere.Proofs.Sec3GaussExp
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Weight

/-!
# Algebraic Gaussian expectations (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.637–661, l.698–706.  An algebraic Gaussian expectation in finitely many
variables `x_i` over a ring `R` is an `R`-linear functional `W` on `R[[x]]` that depends on
finitely many coefficients (`IsLocal`) and satisfies the Wick rule
`W(x_i Φ) = m_i W(Φ) + ∑_j C_{ij} W(∂_j Φ)` (`IBP`), with mean `m` and covariance `C`.
Proved here: such a functional is determined by `W(1)`, and for mean zero
`W(exp(∑ a_i x_i)) = W(1) exp(½ ∑ a_i C_{ij} a_j)`, the expectation of a linear exponential
(l.703–706).
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries

section Local

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The functional `W` depends only on the coefficients of degree at most `d`. -/
def IsLocal (d : ℕ) (W : MvPowerSeries ι R →ₗ[R] R) : Prop :=
  ∀ Φ : MvPowerSeries ι R, (∀ α : ι →₀ ℕ, α.degree ≤ d → coeff α Φ = 0) → W Φ = 0

theorem IsLocal.mono {d d' : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    (hd : d ≤ d') : IsLocal d' W :=
  fun Φ hΦ => h Φ fun α hα => hΦ α (hα.trans hd)

theorem IsLocal.congr {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    {Φ Ψ : MvPowerSeries ι R} (hc : ∀ α : ι →₀ ℕ, α.degree ≤ d → coeff α Φ = coeff α Ψ) :
    W Φ = W Ψ := by
  have := h (Φ - Ψ) fun α hα => by rw [map_sub, hc α hα, sub_self]
  rwa [map_sub, sub_eq_zero] at this

theorem monomial_eq_smul (α : ι →₀ ℕ) (c : R) :
    (monomial α c : MvPowerSeries ι R) = c • monomial α 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

theorem apply_monomial (W : MvPowerSeries ι R →ₗ[R] R) (α : ι →₀ ℕ) (c : R) :
    W (monomial α c) = c * W (monomial α 1) := by
  rw [monomial_eq_smul, map_smul, smul_eq_mul]

theorem apply_C_mul (W : MvPowerSeries ι R →ₗ[R] R) (c : R) (Φ : MvPowerSeries ι R) :
    W (C c * Φ) = c * W Φ := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem apply_coe_eq_zero {W : MvPowerSeries ι R →ₗ[R] R}
    (hm : ∀ α : ι →₀ ℕ, W (monomial α 1) = 0) (p : MvPolynomial ι R) :
    W (p : MvPowerSeries ι R) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c => rw [MvPolynomial.coe_monomial, apply_monomial, hm, mul_zero]
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add, hp, hq, add_zero]

theorem IsLocal.eq_zero {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    (hm : ∀ α : ι →₀ ℕ, W (monomial α 1) = 0) : W = 0 := by
  ext Φ
  have h1 := h.congr (Φ := Φ)
    (Ψ := ((trunc' R (Finsupp.equivFunOnFinite.symm fun _ : ι => d) Φ : MvPolynomial ι R) :
      MvPowerSeries ι R)) fun α hα => by
    rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos]
    intro i
    simpa using (Finsupp.le_degree i α).trans hα
  rw [h1, LinearMap.zero_apply]
  exact apply_coe_eq_zero hm _

/-- A local functional is determined by its values on the monomials. -/
theorem IsLocal.ext {d : ℕ} {W W' : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    (h' : IsLocal d W') (hm : ∀ α : ι →₀ ℕ, W (monomial α 1) = W' (monomial α 1)) :
    W = W' := by
  refine sub_eq_zero.1 (IsLocal.eq_zero (d := d) (fun Φ hΦ => ?_) fun α => ?_)
  · rw [LinearMap.sub_apply, h Φ hΦ, h' Φ hΦ, sub_zero]
  · rw [LinearMap.sub_apply, hm α, sub_self]

theorem IsLocal.comp_mul {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    (Ψ : MvPowerSeries ι R) : IsLocal d (W.comp (LinearMap.mulLeft R Ψ)) := by
  intro Φ hΦ
  refine h _ fun α hα => ?_
  rw [LinearMap.mulLeft_apply, coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  have h2 : p.2.degree ≤ d := by
    have := congrArg Finsupp.degree hp'
    rw [map_add] at this
    omega
  rw [hΦ p.2 h2, mul_zero]

theorem IsLocal.comp_pderiv {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W) (j : ι) :
    IsLocal (d + 1) (W.comp (pderiv R j).toLinearMap) := by
  intro Φ hΦ
  refine h _ fun α hα => ?_
  have h1 : (α + Finsupp.single j 1).degree ≤ d + 1 := by
    rw [map_add, Finsupp.degree_single]
    omega
  change coeff α (pderiv R j Φ) = 0
  rw [coeff_pderiv, hΦ _ h1, zero_mul]

theorem sub_single_add {α : ι →₀ ℕ} {i : ι} (hi : α i ≠ 0) :
    α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_eq_same]
    omega
  · simp [Finsupp.single_eq_of_ne hj]

theorem degree_sub_single {α : ι →₀ ℕ} {i : ι} (hi : α i ≠ 0) :
    (α - Finsupp.single i 1).degree + 1 = α.degree := by
  have := congrArg Finsupp.degree (sub_single_add hi)
  rwa [map_add, Finsupp.degree_single] at this

theorem pderiv_monomial_one (j : ι) (α : ι →₀ ℕ) :
    pderiv R j (monomial α (1 : R)) = monomial (α - Finsupp.single j 1) ((α j : ℕ) : R) := by
  rw [← MvPolynomial.coe_monomial, pderiv_coe, MvPolynomial.pderiv_monomial,
    MvPolynomial.coe_monomial, one_mul]

/-- The Wick rule (integration by parts) with mean `m` and covariance `C`. -/
def IBP (W : MvPowerSeries ι R →ₗ[R] R) (m : ι → R) (C : ι → ι → R) : Prop :=
  ∀ (i : ι) (Φ : MvPowerSeries ι R),
    W (X i * Φ) = m i * W Φ + ∑ j, C i j * W (pderiv R j Φ)

/-- The Wick rule holds for all series once it holds for the monomials. -/
theorem ibp_of_monomials {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W) {m : ι → R}
    {C : ι → ι → R}
    (hm : ∀ (i : ι) (α : ι →₀ ℕ), W (X i * monomial α 1) =
      m i * W (monomial α 1) + ∑ j, C i j * W (pderiv R j (monomial α 1))) : IBP W m C := by
  intro i Φ
  have hloc : IsLocal (d + 1)
      (m i • W + ∑ j, C i j • W.comp (pderiv R j).toLinearMap) := by
    intro Ψ hΨ
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      h Ψ fun α hα => hΨ α (hα.trans (Nat.le_succ d)), smul_zero, zero_add]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [LinearMap.smul_apply, (h.comp_pderiv j) Ψ hΨ, smul_zero]
  have h1 := IsLocal.ext ((h.comp_mul (X i)).mono (Nat.le_succ d)) hloc fun α => by
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, hm i α, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    congr 1
  have h2 := LinearMap.congr_fun h1 Φ
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul] at h2
  rw [h2]
  congr 1

/-- A local functional satisfying the Wick rule is determined by its value at `1`. -/
theorem ibp_unique {d : ℕ} {W W' : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    (h' : IsLocal d W') {m : ι → R} {C : ι → ι → R} (hI : IBP W m C) (hI' : IBP W' m C)
    (h1 : W 1 = W' 1) : W = W' := by
  refine IsLocal.ext h h' ?_
  have key : ∀ N : ℕ, ∀ α : ι →₀ ℕ, α.degree = N → W (monomial α 1) = W' (monomial α 1) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro α hα
      by_cases h0 : α = 0
      · subst h0
        simpa [monomial_zero_one] using h1
      · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact h0 (Finsupp.ext hcon)
        have hee := sub_single_add hi
        have hdeg := degree_sub_single hi
        have hx : (monomial α (1 : R) : MvPowerSeries ι R) =
            X i * monomial (α - Finsupp.single i 1) 1 := by
          rw [X_def, monomial_mul_monomial, one_mul, add_comm, hee]
        rw [hx, hI, hI', ih _ (by omega) _ rfl]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pderiv_monomial_one]
        by_cases hj : (α - Finsupp.single i 1 : ι →₀ ℕ) j = 0
        · rw [hj, Nat.cast_zero, map_zero, map_zero, map_zero]
        · have hdeg2 := degree_sub_single hj
          have hlt : (α - Finsupp.single i 1 - Finsupp.single j 1 : ι →₀ ℕ).degree < N := by
            omega
          rw [apply_monomial W, apply_monomial W', ih _ hlt _ rfl]
  exact fun α => key _ α rfl

end Local

section LinExp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The linear form `∑_i a_i x_i`. -/
noncomputable def linForm (a : ι → R) : MvPowerSeries ι R := ∑ i, C (a i) * X i

theorem constantCoeff_linForm (a : ι → R) : constantCoeff (linForm a) = 0 := by
  simp [linForm]

theorem pderiv_linForm (a : ι → R) (j : ι) : pderiv R j (linForm a) = C (a j) := by
  rw [linForm, map_sum, Finset.sum_eq_single j]
  · rw [Derivation.leibniz, pderiv_X_self, pderiv_C, smul_zero, add_zero, smul_eq_mul, mul_one]
  · intro i _ hij
    rw [Derivation.leibniz, pderiv_X_of_ne hij, pderiv_C, smul_zero, smul_zero, add_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The moment recursion `W(L^{k+1}) = k (∑ a_i C_{ij} a_j) W(L^{k-1})` for a centered Gaussian
expectation and the linear form `L = ∑ a_i x_i`. -/
theorem moment_rec {W : MvPowerSeries ι R →ₗ[R] R} {C : ι → ι → R} (hI : IBP W 0 C)
    (a : ι → R) (k : ℕ) :
    W (linForm a ^ (k + 1)) =
      (k : R) * (∑ i, ∑ j, a i * C i j * a j) * W (linForm a ^ (k - 1)) := by
  have h1 : linForm a ^ (k + 1) = ∑ i, MvPowerSeries.C (a i) * (X i * linForm a ^ k) := by
    rw [pow_succ', linForm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  rw [h1, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_C_mul, hI, Pi.zero_apply, zero_mul, zero_add, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : pderiv R j (linForm a ^ k) =
      MvPowerSeries.C ((k : R) * a j) * linForm a ^ (k - 1) := by
    rw [pderiv_pow, pderiv_linForm, map_mul, map_natCast]
    ring
  rw [h2, apply_C_mul]
  ring

theorem sum_range_two_mul (f : ℕ → R) (M : ℕ) :
    ∑ k ∈ range (2 * M), f k = ∑ j ∈ range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

variable [Algebra ℚ R]

theorem moment_odd {W : MvPowerSeries ι R →ₗ[R] R} {C : ι → ι → R} (hI : IBP W 0 C)
    (a : ι → R) (j : ℕ) : W (linForm a ^ (2 * j + 1)) = 0 := by
  induction j with
  | zero => rw [moment_rec hI]; simp
  | succ j ih =>
    rw [moment_rec hI, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, ih, mul_zero]

theorem moment_even {W : MvPowerSeries ι R →ₗ[R] R} {C : ι → ι → R} (hI : IBP W 0 C)
    (a : ι → R) (j : ℕ) :
    W (linForm a ^ (2 * j)) =
      (((2 * j).factorial : ℚ) / (j.factorial * 2 ^ j)) •
        ((∑ i, ∑ j, a i * C i j * a j) ^ j * W 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, moment_rec hI,
      show 2 * j + 1 - 1 = 2 * j by omega, ih, pow_succ]
    rw [show ((2 * j + 1 : ℕ) : R) = algebraMap ℚ R ((2 * j + 1 : ℕ) : ℚ) from
        (map_natCast (algebraMap ℚ R) _).symm, mul_assoc,
      ← Algebra.smul_def, mul_smul_comm, smul_smul]
    rw [show (∑ i, ∑ j, a i * C i j * a j) *
        ((∑ i, ∑ j, a i * C i j * a j) ^ j * W 1) =
      (∑ i, ∑ j, a i * C i j * a j) ^ j * (∑ i, ∑ j, a i * C i j * a j) * W 1 by ring]
    refine congrArg₂ (· • ·) ?_ (by ring)
    rw [Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j), Nat.factorial_succ j]
    push_cast
    field_simp
    ring

/-- The expectation of a linear exponential in a centered algebraic Gaussian expectation
(sphere/paper.tex l.703–706): `W(exp(∑ a_i x_i)) = W(1) exp(½ ∑ a_i C_{ij} a_j)`. -/
theorem ibp_exp_linear {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W)
    {C : ι → ι → R} (hI : IBP W 0 C) (a : ι → R)
    (hv : IsNilpotent (∑ i, ∑ j, a i * C i j * a j)) :
    W (mexp (linForm a)) =
      W 1 * IsNilpotent.exp ((1 / 2 : ℚ) • ∑ i, ∑ j, a i * C i j * a j) := by
  classical
  set v := ∑ i, ∑ j, a i * C i j * a j with hvdef
  obtain ⟨kv, hkv⟩ := hv
  set M := max (d + 1) kv with hM
  have hL0 := constantCoeff_linForm a
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  -- the exponential series up to degree `2M`
  have e1 : W (mexp (linForm a)) =
      ∑ k ∈ range (2 * M), algebraMap ℚ R (1 / (k.factorial : ℚ)) * W (linForm a ^ k) := by
    have h2 : ∀ α : ι →₀ ℕ, α.degree ≤ d → coeff α (mexp (linForm a)) =
        coeff α (∑ k ∈ range (2 * M), algebraMap ℚ R (1 / (k.factorial : ℚ)) • linForm a ^ k) := by
      intro α hα
      obtain ⟨M', hM'⟩ : ∃ M', 2 * M = M' + 1 := ⟨2 * M - 1, by omega⟩
      rw [mexp, coeff_subst_truncG hL0 _ α (2 * M) (by omega), PowerSeries.subst_coe hs, hM',
        Polynomial.aeval_eq_sum_range' (PowerSeries.natDegree_trunc_lt _ M')]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [PowerSeries.coeff_trunc, if_pos (Finset.mem_range.1 hk), PowerSeries.coeff_exp]
    rw [h.congr h2, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [e1, sum_range_two_mul]
  have hpow : ((1 / 2 : ℚ) • v) ^ M = 0 := by
    rw [smul_pow, pow_eq_zero_of_le (le_max_right _ _) hkv, smul_zero]
  rw [IsNilpotent.exp_eq_sum hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr : W 1 * ((1 / 2 : ℚ) ^ j • v ^ j) = ((1 / 2 : ℚ) ^ j) • (v ^ j * W 1) := by
    rw [mul_smul_comm, mul_comm]
  rw [moment_odd hI, mul_zero, add_zero, moment_even hI, ← Algebra.smul_def, smul_smul,
    smul_pow, mul_smul_comm, hr, smul_smul]
  congr 1
  have h3 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((1 / 2 : ℚ)) ^ j = 1 / 2 ^ j := by rw [one_div, one_div, inv_pow]
  rw [h4]
  field_simp

end LinExp

end Virasoro.Sphere
