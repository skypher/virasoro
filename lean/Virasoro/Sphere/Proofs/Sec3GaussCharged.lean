import Virasoro.Sphere.Proofs.Sec3GaussDet

/-!
# The Gaussian with a linear term (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.652–668, l.684.  For the quadratic part `q` and a linear form `J·x`, modulo
`z^{K+1}` (`K ≤ n`):
`𝔼_{Q₀}[e^{q + J·x} Φ] = e^{½ J·CJ} 𝔼_{Q₀}[e^q Φ(x + CJ)]`, with `C` the Neumann covariance, and
`𝔼_{Q₀}[e^{q + J·x}] = det(I - M(z)²)^{-1/2} e^{½ J·CJ}`: the saddle value factors out and the
variables are shifted to the saddle point `CJ`.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries Matrix

section Charged

variable {n K : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R] (φ : PowerSeries ℚ →+* R)

/-- The entries of the Neumann covariance are multiples of `z`. -/
theorem covN_dvd (i j : Modes n) : φ PowerSeries.X ∣ covN n φ K i j := by
  have h1 : ER n φ = φ PowerSeries.X • (Matrix.diagonal fun i : Fin n =>
      algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * φ PowerSeries.X ^ (i : ℕ)) := by
    ext a b
    rw [ER, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [smul_eq_mul, pow_succ]
      ring
    · rw [smul_zero]
  have h2 : Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 = φ PowerSeries.X •
      Matrix.fromBlocks 0
        (Matrix.diagonal fun i : Fin n =>
          algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * φ PowerSeries.X ^ (i : ℕ))
        (Matrix.diagonal fun i : Fin n =>
          algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * φ PowerSeries.X ^ (i : ℕ)) 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero, ← h1]
  rw [covN, h2, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

/-- Completing the square in the Fock pairing (sphere/paper.tex l.663–668). -/
theorem fockP_gauss_shift (hz : φ PowerSeries.X ^ (K + 1) = 0) (J : Modes n → R)
    (Φ : MvPowerSeries (Modes n) R) :
    fockP n K (φ PowerSeries.X) (mexp (quadB n R + linForm J) * Φ) =
      IsNilpotent.exp ((1 / 2 : ℚ) • ∑ i, ∑ j, J i * covN n φ K i j * J j) *
        fockP n K (φ PowerSeries.X)
          (mexp (quadB n R) * trans (fun i => ∑ j, covN n φ K i j * J j) Φ) := by
  have hq0 : IsNilpotent (constantCoeff (quadB n R)) := by
    rw [constantCoeff_quadB]
    exact IsNilpotent.zero
  have hl0 : IsNilpotent (constantCoeff (linForm J)) := by
    rw [constantCoeff_linForm]
    exact IsNilpotent.zero
  have hloc : IsLocal (Fintype.card (Modes n) * K)
      ((fockP n K (φ PowerSeries.X)).comp (LinearMap.mulLeft R (mexp (quadB n R)))) :=
    fockP_local.comp_mul _
  have hk : ∀ i, (∑ j, covN n φ K i j * J j) ^ (K + 1) = 0 := by
    intro i
    have hd : φ PowerSeries.X ∣ ∑ j, covN n φ K i j * J j :=
      Finset.dvd_sum fun j _ => (covN_dvd φ i j).mul_right _
    obtain ⟨c, hc⟩ := hd
    rw [hc, mul_pow, hz, zero_mul]
  have hv : IsNilpotent (∑ i, ∑ j, J i * covN n φ K i j * J j) := by
    have hd : φ PowerSeries.X ∣ ∑ i, ∑ j, J i * covN n φ K i j * J j :=
      Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ =>
        ((covN_dvd φ i j).mul_left _).mul_right _
    obtain ⟨c, hc⟩ := hd
    exact ⟨K + 1, by rw [hc, mul_pow, hz, zero_mul]⟩
  have h := ibp_shift hloc (fockP_quad_ibp (n := n) (φ := φ) hz) J hk hv Φ
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
  rw [mexp_add hq0 hl0, mul_assoc]
  exact h

/-- `𝔼_{Q₀}[e^{q + J·x}] = det(I - M(z)²)^{-1/2} e^{½ J·CJ}` modulo `z^{K+1}`, `K ≤ n`
(sphere/paper.tex l.652–655, l.684). -/
theorem fockP_gauss_linear (hK : K ≤ n) (hz : φ PowerSeries.X ^ (K + 1) = 0) (J : Modes n → R) :
    fockP n K (φ PowerSeries.X) (mexp (quadB n R + linForm J)) =
      IsNilpotent.exp ((1 / 2 : ℚ) • ∑ i, ∑ j, J i * covN n φ K i j * J j) * φ detInvSqrt := by
  have hnil : ∀ i, IsNilpotent (∑ j, covN n φ K i j * J j) := by
    intro i
    have hd : φ PowerSeries.X ∣ ∑ j, covN n φ K i j * J j :=
      Finset.dvd_sum fun j _ => (covN_dvd φ i j).mul_right _
    obtain ⟨c, hc⟩ := hd
    exact ⟨K + 1, by rw [hc, mul_pow, hz, zero_mul]⟩
  have h := fockP_gauss_shift φ hz J 1
  rw [mul_one, trans_one hnil, mul_one, fockP_mexp_quadB hK φ hz] at h
  exact h

end Charged

end Virasoro.Sphere
