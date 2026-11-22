import Virasoro.Sphere.Proofs.Sec3GaussEuler
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The formal Gaussian determinant (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.652–655: `𝔼_{Q₀}[e^q] = det(Q₀⁻¹Q(z))^{-1/2} = det(I - M(z)²)^{-1/2}` for the
quadratic part `q = ∑ B_{m,n}(u_m u_n + ū_m ū_n)`.  With `θ = z d/dz`, the pairing satisfies
`θ P(Φ) = P(E Φ)` for the level operator `E`, so `Z = P(e^q)` solves `θ Z = Tr(D M²(I-M²)⁻¹) Z`
modulo `z^{K+1}` (`fockP_euler_quad`); `det(I - M²)^{-1/2}` solves the same equation
(`theta_detInvSqrt`, Lemma 3.5), and both have constant term `1`.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries Matrix

section Det

variable {n K : ℕ}

theorem coeff_eulerU_rat (Φ : MvPowerSeries (Modes n) ℚ) (γ : Modes n →₀ ℕ) :
    coeff γ (eulerU Φ) = (wtF (fun i => γ (Sum.inl i)) : ℚ) * coeff γ Φ := by
  rw [eulerU, map_sum, wtF, Nat.cast_sum, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.coeff_C_mul, coeff_X_mul_pderiv]
  push_cast
  ring

theorem algebraMap_rat_ps (q : ℚ) : algebraMap ℚ (PowerSeries ℚ) q = PowerSeries.C q :=
  RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (PowerSeries ℚ)) PowerSeries.C) q

/-- `θ P(Φ) = P(E Φ)` for a series `Φ` with rational coefficients, `θ = z d/dz`. -/
theorem theta_fockP (Φ0 : MvPowerSeries (Modes n) ℚ) :
    theta (fockP n K (PowerSeries.X : PowerSeries ℚ)
        (MvPowerSeries.map (PowerSeries.C : ℚ →+* PowerSeries ℚ) Φ0)) =
      fockP n K (PowerSeries.X : PowerSeries ℚ)
        (MvPowerSeries.map (PowerSeries.C : ℚ →+* PowerSeries ℚ) (eulerU Φ0)) := by
  rw [fockP, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun γ _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, coeff_eulerU_rat, fockMom, momF]
  split_ifs with h
  · rw [algebraMap_rat_ps, mul_assoc, thetaC_mul, Derivation.leibniz, theta_C, smul_zero,
      zero_add, theta_X_pow, smul_eq_mul, map_mul, map_natCast]
    ring
  · rw [zero_mul, zero_mul, map_zero]

/-- Two solutions of `θ f = g f` modulo `z^{K+1}` with the same constant term agree up to
order `K`. -/
theorem ode_unique {f d g G : PowerSeries ℚ} {K : ℕ}
    (h0 : PowerSeries.coeff 0 f = PowerSeries.coeff 0 d)
    (hg : ∀ j ≤ K, PowerSeries.coeff j G = PowerSeries.coeff j g)
    (hg0 : PowerSeries.coeff 0 g = 0)
    (hf : (PowerSeries.X : PowerSeries ℚ) ^ (K + 1) ∣ theta f - G * f)
    (hd : theta d = d * g) : ∀ j ≤ K, PowerSeries.coeff j f = PowerSeries.coeff j d := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact h0
    · have h1 := PowerSeries.X_pow_dvd_iff.1 hf j (by omega)
      rw [map_sub, sub_eq_zero, coeff_theta, PowerSeries.coeff_mul] at h1
      have h2 := congrArg (PowerSeries.coeff j) hd
      rw [coeff_theta, mul_comm d g, PowerSeries.coeff_mul] at h2
      have h3 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j,
          PowerSeries.coeff p.1 G * PowerSeries.coeff p.2 f =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j,
            PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 d := by
        refine sum_congr rfl fun p hp => ?_
        have hp' : p.1 + p.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        rw [hg p.1 (by omega)]
        rcases Nat.eq_zero_or_pos p.1 with h10 | h1p
        · rw [h10, hg0, zero_mul, zero_mul]
        · rw [ih p.2 (by omega) (by omega)]
      rw [h3, ← h2] at h1
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      exact mul_left_cancel₀ hj0 h1

theorem fockP_zero {R : Type*} [CommRing R] [Algebra ℚ R] (Φ : MvPowerSeries (Modes n) R) :
    fockP n K (0 : R) Φ = MvPowerSeries.coeff 0 Φ := by
  rw [fockP, LinearMap.sum_apply, Finset.sum_eq_single 0]
  · have h1 : wtF (fun i : Fin n => (0 : Modes n →₀ ℕ) (Sum.inl i)) = 0 := by simp [wtF]
    have h2 : nrmF (fun i : Fin n => (0 : Modes n →₀ ℕ) (Sum.inl i)) = 1 := by simp [nrmF]
    have hc : (fun i : Fin n => (0 : Modes n →₀ ℕ) (Sum.inl i)) =
        fun i : Fin n => (0 : Modes n →₀ ℕ) (Sum.inr i) := rfl
    rw [LinearMap.smul_apply, smul_eq_mul, fockMom, momF, if_pos hc, h1, h2, pow_zero, map_one,
      mul_one, one_mul]
  · intro γ _ hγ
    rw [LinearMap.smul_apply, fockMom, momF]
    split_ifs with h
    · have hw : wtF (fun i => γ (Sum.inl i)) ≠ 0 := by
        intro hw0
        apply hγ
        have hall : ∀ i : Fin n, γ (Sum.inl i) = 0 := by
          intro i
          have := (Finset.sum_eq_zero_iff.1 hw0) i (Finset.mem_univ i)
          simpa using this
        ext a
        rcases a with i | i
        · simpa using hall i
        · have := congrFun h i
          rw [← this]
          simpa using hall i
      rw [zero_pow hw, mul_zero, zero_smul]
    · rw [zero_smul]
  · intro h
    exact absurd (Finset.mem_Iic.2 zero_le) h

theorem map_mexp_quadB {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    (ψ : R →+* S) : MvPowerSeries.map ψ (mexp (quadB n R)) = mexp (quadB n S) := by
  rw [map_mexp ψ (by rw [constantCoeff_quadB]; exact IsNilpotent.zero), map_quadB]

theorem phi_fockP_quadB {R : Type*} [CommRing R] [Algebra ℚ R] (φ : PowerSeries ℚ →+* R) :
    φ (fockP n K (PowerSeries.X : PowerSeries ℚ) (mexp (quadB n (PowerSeries ℚ)))) =
      fockP n K (φ PowerSeries.X) (mexp (quadB n R)) := by
  rw [map_fockP, map_mexp_quadB]

/-- The formal Gaussian determinant (sphere/paper.tex l.652–655): modulo `z^{K+1}`, `K ≤ n`,
`𝔼_{Q₀}[e^q] = det(I - M(z)²)^{-1/2}`. -/
theorem fockP_mexp_quadB {R : Type*} [CommRing R] [Algebra ℚ R] (hK : K ≤ n)
    (φ : PowerSeries ℚ →+* R) (hz : φ PowerSeries.X ^ (K + 1) = 0) :
    fockP n K (φ PowerSeries.X) (mexp (quadB n R)) = φ detInvSqrt := by
  set ZF := fockP n K (PowerSeries.X : PowerSeries ℚ) (mexp (quadB n (PowerSeries ℚ))) with hZF
  set GN : PowerSeries ℚ := ∑ k ∈ Icc 1 n, Matrix.trace (Dmat n * Mmat n ^ (2 * k)) with hGN
  have hq0 : constantCoeff (quadB n ℚ) = 0 := constantCoeff_quadB n ℚ
  -- the equation `θ Z = G Z` modulo `z^{K+1}`
  have hθ : theta ZF = fockP n K (PowerSeries.X : PowerSeries ℚ)
      (MvPowerSeries.map (PowerSeries.C : ℚ →+* PowerSeries ℚ) (eulerU (mexp (quadB n ℚ)))) := by
    rw [hZF, ← map_mexp_quadB (PowerSeries.C : ℚ →+* PowerSeries ℚ), theta_fockP]
  set π := Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ℚ) ^ (K + 1)}) with hπ
  have hzπ : π PowerSeries.X ^ (K + 1) = 0 := by
    rw [← map_pow, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have key : π (theta ZF) = π GN * π ZF := by
    have e1 : MvPowerSeries.map π (MvPowerSeries.map (PowerSeries.C : ℚ →+* PowerSeries ℚ)
        (eulerU (mexp (quadB n ℚ)))) =
        mexp (quadB n _) * eulerU (quadB n _) := by
      have e2 : MvPowerSeries.map π (MvPowerSeries.map (PowerSeries.C : ℚ →+* PowerSeries ℚ)
          (eulerU (mexp (quadB n ℚ)))) =
          MvPowerSeries.map (π.comp PowerSeries.C) (eulerU (mexp (quadB n ℚ))) := by
        ext γ
        simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
      rw [e2, map_eulerU, map_mexp_quadB, eulerU_mexp (constantCoeff_quadB n _)]
    rw [hθ, map_fockP, e1, fockP_euler_quad π hzπ (by omega), hGN, hZF, phi_fockP_quadB]
  have hdvd : (PowerSeries.X : PowerSeries ℚ) ^ (K + 1) ∣ theta ZF - GN * ZF := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ, map_sub, map_mul, key,
      sub_self]
  -- constant terms
  have h0 : PowerSeries.coeff 0 ZF = PowerSeries.coeff 0 detInvSqrt := by
    have h1 := phi_fockP_quadB (n := n) (K := K) (PowerSeries.constantCoeff : PowerSeries ℚ →+* ℚ)
    rw [PowerSeries.constantCoeff_X, fockP_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_mexp hq0] at h1
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_detInvSqrt]
    exact h1
  -- the traces agree up to order `K`
  have hg : ∀ j ≤ K, PowerSeries.coeff j GN = PowerSeries.coeff j traceDM := by
    intro j hj
    have e : ∀ N : ℕ, ∑ k ∈ Icc 1 N, Matrix.trace (Dmat N * Mmat N ^ (2 * k)) =
        Sd (fun _ => 1) (fun m => (m : PowerSeries ℚ)) N := by
      intro N
      simp only [Sd, map_one, one_mul]
    rw [hGN, e, traceDM, PowerSeries.coeff_mk, e,
      coeff_Sd_trunc (fun _ => 1) _ le_rfl (hj.trans hK)]
  have hall := ode_unique h0 hg coeff_zero_traceDM hdvd theta_detInvSqrt
  have hd2 : (PowerSeries.X : PowerSeries ℚ) ^ (K + 1) ∣ ZF - detInvSqrt :=
    PowerSeries.X_pow_dvd_iff.2 fun j hj => by
      rw [map_sub, hall j (by omega), sub_self]
  obtain ⟨c, hc⟩ := hd2
  have h3 : φ ZF - φ detInvSqrt = 0 := by
    rw [← map_sub, hc, map_mul, map_pow, hz, zero_mul]
  rw [← phi_fockP_quadB, ← hZF]
  exact sub_eq_zero.1 h3

end Det

end Virasoro.Sphere
