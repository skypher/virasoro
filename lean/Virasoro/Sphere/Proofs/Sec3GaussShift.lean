import Virasoro.Sphere.Proofs.Sec3GaussWick

/-!
# Completing the square (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.663–668: completing the square shifts the variables to the saddle point.
For a centered algebraic Gaussian expectation `W` with covariance `C` and a linear form
`J·x`, `W(e^{J·x} Φ) = e^{½ J·C J} W(Φ(x + CJ))`.  The translation `Φ ↦ Φ(x + a)` by a vector
with nilpotent entries is a substitution; it commutes with the partial derivatives on
polynomials, and its coefficients of bounded degree involve finitely many coefficients of `Φ`.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries

section Shift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The translation `Φ(x) ↦ Φ(x + a)`. -/
noncomputable def trans (a : ι → R) (Φ : MvPowerSeries ι R) : MvPowerSeries ι R :=
  subst (fun i => X i + C (a i)) Φ

theorem hasSubst_trans {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) :
    HasSubst (fun i => (X i + C (a i) : MvPowerSeries ι R)) :=
  hasSubst_of_constantCoeff_nilpotent fun i => by simpa using ha i

/-- The translation as a linear map. -/
noncomputable def transLin {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) :
    MvPowerSeries ι R →ₗ[R] MvPowerSeries ι R :=
  (substAlgHom (hasSubst_trans ha)).toLinearMap

theorem transLin_apply {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) (Φ : MvPowerSeries ι R) :
    transLin ha Φ = trans a Φ := by
  rw [transLin, AlgHom.toLinearMap_apply, coe_substAlgHom]
  rfl

theorem trans_mul {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) (Φ Ψ : MvPowerSeries ι R) :
    trans a (Φ * Ψ) = trans a Φ * trans a Ψ :=
  subst_mul (hasSubst_trans ha) Φ Ψ

theorem trans_X {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) (i : ι) :
    trans a (X i : MvPowerSeries ι R) = X i + C (a i) :=
  subst_X (hasSubst_trans ha) i

theorem trans_one {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) :
    trans a (1 : MvPowerSeries ι R) = 1 := by
  rw [← transLin_apply ha, transLin, AlgHom.toLinearMap_apply, map_one]

/-- On polynomials the translation commutes with the partial derivatives. -/
theorem pderiv_aeval_trans (a : ι → R) (p : MvPolynomial ι R) (j : ι) :
    pderiv R j (MvPolynomial.aeval (fun i => (X i + C (a i) : MvPowerSeries ι R)) p) =
      MvPolynomial.aeval (fun i => (X i + C (a i) : MvPowerSeries ι R))
        (MvPolynomial.pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero]
    exact pderiv_C
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p k ih =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, ih, Derivation.leibniz, map_add,
      map_add, pderiv_C, add_zero, pderiv_X, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul, MvPolynomial.aeval_X]
    by_cases hk : j = k
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne' hk]

theorem pderiv_trans_monomial (a : ι → R) (α : ι →₀ ℕ) (j : ι) :
    pderiv R j (trans a (monomial α 1)) = trans a (pderiv R j (monomial α 1)) := by
  rw [← MvPolynomial.coe_monomial, pderiv_coe, trans, trans, subst_coe, subst_coe,
    pderiv_aeval_trans]

/-- A coefficient of bounded degree of `Φ(x + a)` involves finitely many coefficients of `Φ`. -/
theorem coeff_trans_eq_zero {a : ι → R} {k0 : ℕ} (hk : ∀ i, a i ^ k0 = 0) (d : ℕ)
    (Φ : MvPowerSeries ι R)
    (hΦ : ∀ α : ι →₀ ℕ, α.degree ≤ Fintype.card ι * (d + k0) → coeff α Φ = 0) (e : ι →₀ ℕ)
    (he : e.degree ≤ d) : coeff e (trans a Φ) = 0 := by
  have ha : ∀ i, IsNilpotent (a i) := fun i => ⟨k0, hk i⟩
  rw [trans, coeff_subst (hasSubst_trans ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
  by_cases hδ : δ.degree ≤ Fintype.card ι * (d + k0)
  · rw [hΦ δ hδ, zero_smul]
  · obtain ⟨i, hi⟩ : ∃ i, d + k0 < δ i := by
      by_contra hcon
      push_neg at hcon
      refine hδ ?_
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, δ i ≤ ∑ _i : ι, (d + k0) := Finset.sum_le_sum fun i _ => hcon i
        _ = Fintype.card ι * (d + k0) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hdvd : (X i : MvPowerSeries ι R) ^ (d + 1) ∣ (X i + C (a i)) ^ δ i := by
      rw [add_pow]
      refine Finset.dvd_sum fun m _ => ?_
      by_cases hm : d + 1 ≤ m
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow _ hm) _) _
      · have h0 : (C (a i) : MvPowerSeries ι R) ^ (δ i - m) = 0 := by
          rw [← map_pow, pow_eq_zero_of_le (by omega) (hk i), map_zero]
        rw [h0, mul_zero, zero_mul]
        exact dvd_zero _
    have hdvd2 : (X i : MvPowerSeries ι R) ^ (d + 1) ∣
        δ.prod fun s n => (X s + C (a s) : MvPowerSeries ι R) ^ n := by
      have hi' : i ∈ δ.support := by
        rw [Finsupp.mem_support_iff]
        omega
      exact hdvd.trans (Finset.dvd_prod_of_mem _ hi')
    have h1 := (X_pow_dvd_iff.1 hdvd2) e (by
      have := Finsupp.le_degree i e
      omega)
    rw [h1, smul_zero]

theorem IsLocal.comp_trans {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W) {a : ι → R}
    {k0 : ℕ} (hk : ∀ i, a i ^ k0 = 0) (ha : ∀ i, IsNilpotent (a i)) :
    IsLocal (Fintype.card ι * (d + k0)) (W.comp (transLin ha)) := by
  intro Φ hΦ
  rw [LinearMap.comp_apply, transLin_apply]
  exact h _ fun e he => coeff_trans_eq_zero hk d Φ hΦ e he

variable [Algebra ℚ R]

/-- Completing the square (sphere/paper.tex l.663–668):
`W(e^{J·x} Φ) = e^{½ J·CJ} W(Φ(x + CJ))` for a centered algebraic Gaussian expectation `W` with
covariance `C`, when the entries of `CJ` are nilpotent. -/
theorem ibp_shift {d : ℕ} {W : MvPowerSeries ι R →ₗ[R] R} (h : IsLocal d W) {C : ι → ι → R}
    (hI : IBP W 0 C) (J : ι → R) {k0 : ℕ} (hk : ∀ i, (∑ j, C i j * J j) ^ k0 = 0)
    (hv : IsNilpotent (∑ i, ∑ j, J i * C i j * J j)) (Φ : MvPowerSeries ι R) :
    W (mexp (linForm J) * Φ) =
      IsNilpotent.exp ((1 / 2 : ℚ) • ∑ i, ∑ j, J i * C i j * J j) *
        W (trans (fun i => ∑ j, C i j * J j) Φ) := by
  set a : ι → R := fun i => ∑ j, C i j * J j with ha
  have hnil : ∀ i, IsNilpotent (a i) := fun i => ⟨k0, hk i⟩
  set c := IsNilpotent.exp ((1 / 2 : ℚ) • ∑ i, ∑ j, J i * C i j * J j) with hc
  set D := max d (Fintype.card ι * (d + k0)) with hD
  have hL0 := constantCoeff_linForm J
  -- the two functionals
  have loc2 : IsLocal D (W.comp (LinearMap.mulLeft R (mexp (linForm J)))) :=
    (h.comp_mul _).mono (le_max_left _ _)
  have loc3 : IsLocal D (c • W.comp (transLin hnil)) := by
    intro Ψ hΨ
    rw [LinearMap.smul_apply, ((h.comp_trans hk hnil).mono (le_max_right _ _)) Ψ hΨ, smul_zero]
  have ibp2 : IBP (W.comp (LinearMap.mulLeft R (mexp (linForm J)))) a C := by
    intro i Ψ
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [mul_left_comm, hI, Pi.zero_apply, zero_mul, zero_add, ha, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : pderiv R j (mexp (linForm J) * Ψ) =
        MvPowerSeries.C (J j) * (mexp (linForm J) * Ψ) + mexp (linForm J) * pderiv R j Ψ := by
      rw [Derivation.leibniz, pderiv_mexp_zero hL0, pderiv_linForm, smul_eq_mul, smul_eq_mul]
      ring
    rw [h1, map_add, apply_C_mul]
    ring
  have ibp3 : IBP (c • W.comp (transLin hnil)) a C := by
    refine ibp_of_monomials loc3 fun i α => ?_
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, transLin_apply, smul_eq_mul]
    rw [trans_mul hnil, trans_X hnil, add_mul, map_add, hI, Pi.zero_apply, zero_mul, zero_add,
      apply_C_mul, mul_add, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [pderiv_trans_monomial]
      ring
  have h1 : (W.comp (LinearMap.mulLeft R (mexp (linForm J)))) 1 =
      (c • W.comp (transLin hnil)) 1 := by
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one, LinearMap.smul_apply,
      LinearMap.comp_apply, transLin_apply, trans_one hnil, ibp_exp_linear h hI J hv, smul_eq_mul,
      mul_comm]
  have h2 := LinearMap.congr_fun (ibp_unique loc2 loc3 ibp2 ibp3 h1) Φ
  rwa [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    transLin_apply, smul_eq_mul] at h2

end Shift

end Virasoro.Sphere
