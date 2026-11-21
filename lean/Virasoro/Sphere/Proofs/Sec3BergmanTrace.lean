import Virasoro.Sphere.Proofs.Sec3BergmanMatTools
import Virasoro.Sphere.Proofs.Sec3BergmanSecond
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Sphere paper Lemma 3.5: `z d/dz log det(I - M(z)²)^{-1/2} = Tr(D M(z)² (I - M(z)²)⁻¹)`
(`sphere/paper.tex` l.864–865, l.943–945)

`M(z)_{m,n} = z^m B_{m,n}/m`, `D = diag(1,2,…)`.  The trace `Tr(D M² (I-M²)⁻¹) = ∑_{k≥1} Tr(D M^{2k})`
is the series `traceDM`; at order `z^n` it only involves the truncation to indices at most `n`
and the powers `k ≤ n`.  This file proves `θ detInvSqrt = detInvSqrt · traceDM` for `θ = z d/dz`.

Consumer: `Sec3BergmanOde.lean`.
-/

namespace Virasoro.Sphere

open PowerSeries Matrix Finset

/-- The truncation to indices `1 ≤ m ≤ N` of the diagonal matrix `diag(d(1), d(2), …)`. -/
noncomputable abbrev diagN (d : ℕ → PowerSeries ℚ) (N : ℕ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℚ) :=
  Matrix.diagonal fun i => d ((i : ℕ) + 1)

/-- The truncation of `D = diag(1,2,…)` (sphere/paper.tex l.837). -/
noncomputable abbrev Dmat (N : ℕ) : Matrix (Fin N) (Fin N) (PowerSeries ℚ) :=
  diagN (fun m => (m : PowerSeries ℚ)) N

/-- `Tr(D M(z)² (I - M(z)²)⁻¹) = ∑_{k≥1} Tr(D M(z)^{2k})` (sphere/paper.tex l.943). -/
noncomputable def traceDM : PowerSeries ℚ :=
  PowerSeries.mk fun n => coeff n (∑ k ∈ Icc 1 n, trace (Dmat n * Mmat n ^ (2 * k)))

theorem X_dvd_Mmat (N : ℕ) (i j : Fin N) : (X : PowerSeries ℚ) ∣ Mmat N i j := by
  simp only [Mmat, Matrix.of_apply]
  exact (dvd_pow_self X (Nat.succ_ne_zero _)).mul_left _

/-- Modulo `z^{n+1}` the rows `m > n` of `M(z)` vanish, so `Tr(d M^{k+1})` is computed in the
truncation to indices at most `n`. -/
theorem trace_trunc (d : ℕ → PowerSeries ℚ) {n N : ℕ} (h : n ≤ N) (k : ℕ) :
    (X : PowerSeries ℚ) ^ (n + 1) ∣
      trace (diagN d N * Mmat N ^ (k + 1)) - trace (diagN d n * Mmat n ^ (k + 1)) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  set π := Ideal.Quotient.mk (Ideal.span {(X : PowerSeries ℚ) ^ (n + 1)}) with hπdef
  have hπ : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) (PowerSeries ℚ)),
      π (trace A) = trace (π.mapMatrix A) := fun m A => by
    simp [trace, map_sum, RingHom.mapMatrix_apply]
  have e1 : ∀ m : ℕ, π.mapMatrix (diagN d m) = diagonal fun i : Fin m => π (d ((i : ℕ) + 1)) :=
    fun m => by rw [RingHom.mapMatrix_apply, diagonal_map (map_zero π)]
  have hM : ∀ i : Fin N, i ∉ Set.range (Fin.castLEEmb h) →
      ∀ j, π.mapMatrix (Mmat N) i j = 0 := by
    intro i hi j
    have hi' : n ≤ (i : ℕ) := by
      by_contra hlt
      exact hi ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hπdef, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    simp only [Mmat, Matrix.of_apply]
    exact (pow_dvd_pow X (by omega)).mul_left _
  have hs : (π.mapMatrix (Mmat N)).submatrix (Fin.castLEEmb h) (Fin.castLEEmb h) =
      π.mapMatrix (Mmat n) := by
    ext a b
    simp [Mmat, RingHom.mapMatrix_apply]
  rw [hπ, hπ, map_mul, map_mul, map_pow, map_pow, e1, e1,
    trace_diag_mul_pow_emb (Fin.castLEEmb h) _ hM, hs]
  rfl

theorem coeff_trace_trunc (d : ℕ → PowerSeries ℚ) {m n N : ℕ} (hm : m ≤ n) (h : n ≤ N) (k : ℕ) :
    coeff m (trace (diagN d N * Mmat N ^ (k + 1))) =
      coeff m (trace (diagN d n * Mmat n ^ (k + 1))) := by
  have := X_pow_dvd_iff.1 (trace_trunc d h k) m (by omega)
  rwa [map_sub, sub_eq_zero] at this

theorem coeff_trace_of_lt (d : ℕ → PowerSeries ℚ) (N : ℕ) {m k : ℕ} (h : m < k) :
    coeff m (trace (diagN d N * Mmat N ^ k)) = 0 :=
  X_pow_dvd_iff.1 (dvd_trace_diag_mul_pow X (Mmat N) (X_dvd_Mmat N) _ k) m h

/-- `∑_{k=1}^N c_k Tr(d M^{2k})` in the truncation to indices at most `N`. -/
noncomputable def Sd (c : ℕ → ℚ) (d : ℕ → PowerSeries ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Icc 1 N, C (c k) * trace (diagN d N * Mmat N ^ (2 * k))

theorem coeff_Sd_trunc (c : ℕ → ℚ) (d : ℕ → PowerSeries ℚ) {m n N : ℕ} (hm : m ≤ n)
    (h : n ≤ N) : coeff m (Sd c d N) = coeff m (Sd c d n) := by
  simp only [Sd, map_sum, coeff_C_mul]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right h)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 1 := ⟨2 * k - 1, by have := (Finset.mem_Icc.1 hk).1; omega⟩
    rw [hj, coeff_trace_trunc d hm h]
  · intro k hk hk'
    rw [coeff_trace_of_lt d N, mul_zero]
    have h1 := Finset.mem_Icc.1 hk
    have h2 : ¬(1 ≤ k ∧ k ≤ n) := fun hc => hk' (Finset.mem_Icc.2 hc)
    omega

theorem coeff_zero_Sd (c : ℕ → ℚ) (d : ℕ → PowerSeries ℚ) (N : ℕ) : coeff 0 (Sd c d N) = 0 := by
  simp only [Sd, map_sum, coeff_C_mul]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [coeff_trace_of_lt d N, mul_zero]
  have := (Finset.mem_Icc.1 hk).1
  omega

/-- The weights `1/(2k)` of `½ ∑_k Tr(M^{2k})/k`. -/
noncomputable def hw (k : ℕ) : ℚ := (2 : ℚ)⁻¹ * (k : ℚ)⁻¹

theorem diagN_one (N : ℕ) : diagN (fun _ => 1) N = 1 := Matrix.diagonal_one

/-- The exponent of the definition of `detInvSqrt`, in the truncation to indices at most `n`. -/
theorem Gexpr_eq (n : ℕ) :
    (2 : ℚ)⁻¹ • ∑ k ∈ Icc 1 n, ((k : ℚ)⁻¹) • Matrix.trace (Mmat n ^ (2 * k)) =
      Sd hw (fun _ => 1) n := by
  simp only [Sd, diagN_one, Matrix.one_mul, Finset.smul_sum, smul_smul, hw]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_C_mul]

/-- `½ ∑_{k≥1} Tr(M(z)^{2k})/k` as a formal series (sphere/paper.tex l.864–865). -/
noncomputable def Ginf : PowerSeries ℚ := PowerSeries.mk fun n => coeff n (Sd hw (fun _ => 1) n)

theorem coeff_Ginf {m n : ℕ} (h : m ≤ n) : coeff m Ginf = coeff m (Sd hw (fun _ => 1) n) := by
  rw [Ginf, coeff_mk, coeff_Sd_trunc hw _ le_rfl h]

theorem constantCoeff_Ginf : constantCoeff Ginf = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Ginf le_rfl, coeff_zero_Sd]

theorem coeff_pow_congr {u u' : PowerSeries ℚ} {n : ℕ}
    (h : ∀ m ≤ n, coeff m u = coeff m u') (k : ℕ) : coeff n (u ^ k) = coeff n (u' ^ k) := by
  have hd : (X : PowerSeries ℚ) ^ (n + 1) ∣ u - u' :=
    X_pow_dvd_iff.2 fun m hm => by rw [map_sub, h m (by omega), sub_self]
  have := X_pow_dvd_iff.1 (hd.trans (sub_dvd_pow_sub_pow u u' k)) n (by omega)
  rwa [map_sub, sub_eq_zero] at this

/-- The series `detInvSqrt` is `exp(½ ∑_{k≥1} Tr(M(z)^{2k})/k)`. -/
theorem detInvSqrt_eq : detInvSqrt = (PowerSeries.exp ℚ).subst Ginf := by
  ext n
  have h0 : constantCoeff (Sd hw (fun _ => 1) n) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_Sd]
  have he : PowerSeries.exp ℚ = PowerSeries.mk fun k => algebraMap ℚ ℚ (1 / (k.factorial : ℚ)) :=
    rfl
  rw [detInvSqrt, coeff_mk, Gexpr_eq, he, ← compS_eq_subst _ h0, ← compS_eq_subst _ constantCoeff_Ginf]
  simp only [compS, coeff_mk]
  exact Finset.sum_congr rfl fun k _ => by
    rw [coeff_pow_congr (fun m hm => (coeff_Ginf hm).symm)]

theorem constantCoeff_detInvSqrt : constantCoeff detInvSqrt = 1 := by
  rw [detInvSqrt_eq]
  exact constantCoeff_subst_of_one' constantCoeff_Ginf _ (constantCoeff_exp)

theorem Mmat_map_theta (N : ℕ) : (Mmat N).map theta = Dmat N * Mmat N := by
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_mul, Mmat, Matrix.of_apply]
  rw [thetaC_mul, theta_X_pow]
  ring

/-- `θ (½ ∑_k Tr(M^{2k})/k) = ∑_k Tr(D M^{2k})` in each truncation, `θ = z d/dz`. -/
theorem theta_Sd (N : ℕ) :
    theta (Sd hw (fun _ => 1) N) = ∑ k ∈ Icc 1 N, trace (Dmat N * Mmat N ^ (2 * k)) := by
  simp only [Sd, diagN_one, Matrix.one_mul, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 := (Finset.mem_Icc.1 hk).1
  obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 1 := ⟨2 * k - 1, by omega⟩
  have hc : ((j : PowerSeries ℚ) + 1) = C ((2 * k : ℕ) : ℚ) := by
    rw [hj, map_natCast]
    push_cast
    rfl
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [thetaC_mul, hj, deriv_trace_pow, Mmat_map_theta, Matrix.mul_assoc, ← pow_succ', hc,
    ← mul_assoc, ← map_mul, show hw k * ((2 * k : ℕ) : ℚ) = 1 by
      rw [hw]; push_cast; field_simp, map_one, one_mul]

theorem theta_Ginf : theta Ginf = traceDM := by
  ext n
  rw [coeff_theta, coeff_Ginf le_rfl, ← coeff_theta, theta_Sd, traceDM, coeff_mk]

/-- `z d/dz det(I - M(z)²)^{-1/2} = det(I - M(z)²)^{-1/2} · Tr(D M(z)² (I - M(z)²)⁻¹)`
(sphere/paper.tex l.943–945). -/
theorem theta_detInvSqrt : theta detInvSqrt = detInvSqrt * traceDM := by
  have hs := HasSubst.of_constantCoeff_zero' constantCoeff_Ginf
  rw [← theta_Ginf, theta_apply, theta_apply]
  nth_rewrite 1 [detInvSqrt_eq]
  rw [derivative_subst hs, derivative_exp, ← detInvSqrt_eq]
  ring

theorem coeff_zero_traceDM : coeff 0 traceDM = 0 := by
  simp [traceDM]

end Virasoro.Sphere
