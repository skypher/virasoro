import Virasoro.Sphere.Proofs.Sec3GaussCov
import Virasoro.Sphere.Proofs.Sec3BergmanTrace

/-!
# The level operator in the perturbed Gaussian (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.652–655: the formal Gaussian determinant.  The level operator
`E = ∑_m m u_m ∂_{u_m}` satisfies `E e^q = e^q E q`, and by the Wick rule with the Neumann
covariance, `P(e^q E q) = (∑_{k≥1} Tr(D M^{2k})) P(e^q)`, with `D = diag(1,2,…)` and
`M_{m,n} = z^m B_{m,n}/m`.  The functional `P` and the objects built from it are compatible with
changes of the coefficient ring.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries Matrix

section Naturality

variable {n K : ℕ} {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

theorem map_algebraMap_rat (ψ : R →+* S) (q : ℚ) : ψ (algebraMap ℚ R q) = algebraMap ℚ S q :=
  RingHom.congr_fun (Subsingleton.elim (ψ.comp (algebraMap ℚ R)) (algebraMap ℚ S)) q

theorem map_momF (ψ : R →+* S) (z : R) (f g : Fin n → ℕ) :
    ψ (momF n z f g) = momF n (ψ z) f g := by
  unfold momF
  split_ifs
  · rw [map_mul, map_pow, map_algebraMap_rat]
  · exact map_zero ψ

theorem map_fockP (ψ : R →+* S) (z : R) (Φ : MvPowerSeries (Modes n) R) :
    ψ (fockP n K z Φ) = fockP n K (ψ z) (MvPowerSeries.map ψ Φ) := by
  rw [fockP, fockP, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun γ _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, fockMom,
    fockMom, map_momF, MvPowerSeries.coeff_map]

theorem map_quadB (ψ : R →+* S) : MvPowerSeries.map ψ (quadB n R) = quadB n S := by
  simp only [quadB, map_sum, map_mul, map_add, MvPowerSeries.map_C, MvPowerSeries.map_X,
    map_algebraMap_rat]

theorem map_pderiv (ψ : R →+* S) (a : Modes n) (Φ : MvPowerSeries (Modes n) R) :
    pderiv S a (MvPowerSeries.map ψ Φ) = MvPowerSeries.map ψ (pderiv R a Φ) := by
  ext γ
  rw [coeff_pderiv, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, coeff_pderiv, map_mul,
    map_add, map_natCast, map_one]

/-- The level operator `E = ∑_m m u_m ∂_{u_m}` on the variables `u`. -/
noncomputable def eulerU (Φ : MvPowerSeries (Modes n) R) : MvPowerSeries (Modes n) R :=
  ∑ i : Fin n, MvPowerSeries.C ((((i : ℕ) + 1 : ℕ) : R)) *
    (X (Sum.inl i) * pderiv R (Sum.inl i) Φ)

theorem map_eulerU (ψ : R →+* S) (Φ : MvPowerSeries (Modes n) R) :
    MvPowerSeries.map ψ (eulerU Φ) = eulerU (MvPowerSeries.map ψ Φ) := by
  simp only [eulerU, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, map_natCast,
    map_pderiv]

theorem eulerU_mexp {q : MvPowerSeries (Modes n) R} (hq : constantCoeff q = 0) :
    eulerU (mexp q) = mexp q * eulerU q := by
  simp only [eulerU, pderiv_mexp_zero hq, Finset.mul_sum]
  exact sum_congr rfl fun i _ => by ring

end Naturality

section Trace

variable {n K : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R] (φ : PowerSeries ℚ →+* R)

theorem hessB_symm (a b : Modes n) : hessB n R a b = hessB n R b a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [hessB] <;>
    rw [Bcoef_symm]

theorem NR_pow_even (k : ℕ) :
    NR n φ ^ (2 * k) = Matrix.fromBlocks (MR n φ ^ (2 * k)) 0 0 (MR n φ ^ (2 * k)) := by
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, pow_succ, ih, NR,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [pow_succ, pow_succ]

theorem NR_pow_odd (k : ℕ) :
    NR n φ ^ (2 * k + 1) =
      Matrix.fromBlocks 0 (MR n φ ^ (2 * k + 1)) (MR n φ ^ (2 * k + 1)) 0 := by
  rw [pow_succ, NR_pow_even, NR, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [pow_succ]

/-- `Tr(𝔻 N^s)`, `𝔻 = diag(1,…,n)` on the variables `u`. -/
noncomputable def tauN (s : ℕ) : R :=
  ∑ i : Fin n, (((i : ℕ) + 1 : ℕ) : R) * (NR n φ ^ s) (Sum.inl i) (Sum.inl i)

theorem tauN_odd (k : ℕ) : tauN (n := n) φ (2 * k + 1) = 0 := by
  rw [tauN]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [NR_pow_odd, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, mul_zero]

theorem tauN_even (k : ℕ) :
    tauN (n := n) φ (2 * k) = φ (Matrix.trace (Dmat n * Mmat n ^ (2 * k))) := by
  rw [tauN, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (MR n φ ^ (2 * k)) i i = φ ((Mmat n ^ (2 * k)) i i) := by
    have h2 : MR n φ = φ.mapMatrix (Mmat n) := rfl
    rw [h2, ← map_pow, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [NR_pow_even, Matrix.fromBlocks_apply₁₁, h1, Matrix.diag_apply, Matrix.diagonal_mul, map_mul,
    map_natCast]

theorem tauN_eq_zero (hz : φ PowerSeries.X ^ (K + 1) = 0) {s : ℕ} (hs : K + 1 ≤ s) :
    tauN (n := n) φ s = 0 := by
  rw [tauN]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [pow_eq_zero_of_le hs (NR_pow_eq_zero hz), Matrix.zero_apply, mul_zero]

/-- `∑_{r ≤ K} Tr(𝔻 N^{r+1}) = ∑_{k=1}^{n} Tr(D M^{2k})` when `z^{K+1} = 0` and `K ≤ 2n`. -/
theorem sum_tauN (hz : φ PowerSeries.X ^ (K + 1) = 0) (hK : K ≤ 2 * n) :
    ∑ r ∈ range (K + 1), tauN (n := n) φ (r + 1) =
      φ (∑ k ∈ Icc 1 n, Matrix.trace (Dmat n * Mmat n ^ (2 * k))) := by
  have h1 : ∑ s ∈ range (2 * (n + 1)), tauN (n := n) φ s =
      tauN (n := n) φ 0 + ∑ k ∈ Icc 1 n, tauN (n := n) φ (2 * k) := by
    have hr : range (n + 1) = insert 0 (Icc 1 n) := by
      ext x
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [sum_range_two_mul]
    simp only [tauN_odd, add_zero]
    rw [hr, Finset.sum_insert (by simp)]
  have h2 : ∑ s ∈ range (2 * (n + 1)), tauN (n := n) φ s =
      tauN (n := n) φ 0 + ∑ r ∈ range (K + 1), tauN (n := n) φ (r + 1) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Finset.sum_range_succ', add_comm]
    congr 1
    refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r _ hr => ?_).symm
    exact tauN_eq_zero φ hz (by
      have := Finset.mem_range.not.1 hr
      omega)
  rw [map_sum]
  simp only [← tauN_even]
  exact add_left_cancel (h2.symm.trans h1)

/-- `P(e^q E q) = (∑_{k=1}^n Tr(D M^{2k})) P(e^q)` (sphere/paper.tex l.652–655). -/
theorem fockP_euler_quad (hz : φ PowerSeries.X ^ (K + 1) = 0) (hK : K ≤ 2 * n) :
    fockP n K (φ PowerSeries.X) (mexp (quadB n R) * eulerU (quadB n R)) =
      φ (∑ k ∈ Icc 1 n, Matrix.trace (Dmat n * Mmat n ^ (2 * k))) *
        fockP n K (φ PowerSeries.X) (mexp (quadB n R)) := by
  have hI := fockP_quad_ibp (n := n) (φ := φ) hz
  set W := (fockP n K (φ PowerSeries.X)).comp (LinearMap.mulLeft R (mexp (quadB n R))) with hW
  have hW1 : ∀ Φ, W Φ = fockP n K (φ PowerSeries.X) (mexp (quadB n R) * Φ) := fun Φ => rfl
  have hterm : ∀ i : Fin n,
      W (X (Sum.inl i) * pderiv R (Sum.inl i) (quadB n R)) =
        (∑ l, covN n φ K (Sum.inl i) l * hessB n R (Sum.inl i) l) * W 1 := by
    intro i
    rw [hI, Pi.zero_apply, zero_mul, zero_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h3 : pderiv R l (pderiv R (Sum.inl i) (quadB n R)) =
        MvPowerSeries.C (hessB n R (Sum.inl i) l) * 1 := by
      rw [pderiv_quadB, mul_one]
      exact pderiv_linForm (fun k => hessB n R (Sum.inl i) k) l
    rw [h3, apply_C_mul]
    ring
  have hsum : ∀ i : Fin n, ∑ l, covN n φ K (Sum.inl i) l * hessB n R (Sum.inl i) l =
      ∑ r ∈ range (K + 1), (NR n φ ^ (r + 1)) (Sum.inl i) (Sum.inl i) := by
    intro i
    have h4 : covN n φ K * Matrix.of (hessB n R) = ∑ r ∈ range (K + 1), NR n φ ^ (r + 1) := by
      have h5 : Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 * Matrix.of (hessB n R) = NR n φ := by
        rw [← NR_eq, ← cov0_eq]
        ext a b
        rw [Matrix.mul_apply]
        rfl
      rw [covN, Matrix.mul_assoc, h5, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => (pow_succ _ _).symm
    have h6 := congrFun (congrFun h4 (Sum.inl i)) (Sum.inl i)
    rw [Matrix.mul_apply, Matrix.sum_apply] at h6
    rw [← h6]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply, hessB_symm]
  have hW0 : fockP n K (φ PowerSeries.X) (mexp (quadB n R)) = W 1 := by rw [hW1, mul_one]
  rw [← hW1, eulerU, map_sum, ← sum_tauN φ hz hK, hW0]
  simp only [tauN]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_C_mul, hterm, hsum, ← mul_assoc, Finset.mul_sum]

end Trace

end Virasoro.Sphere
