import Virasoro.Sphere.Proofs.Sec3BergmanTraceAmp

/-!
# Sphere paper Lemma 3.5: `Tr(B^{(z)} K₂₁ M₂) = Tr(D M(z)² (I - M(z)²)⁻¹)` (`sphere/paper.tex` l.877, l.941–943)

The diagonal of `A₊₋ = B^{(z)} K₂₁ M₂` has the same trace as that of `A₋₊ = B K₁₂ M₁`:
`B^{(z)} = Z D M₂ Z`, `(M₂M₁)^r M₂ = M₂ (M(z)²)^r`, so
`Tr(B^{(z)} (M₂M₁)^r M₂) = Tr(D M^{2r+2})` in every truncation.

Consumer: `Stmt_sub_bergman_residue` (the coefficient of `x⁻²` of `W_no(x,x)`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset Matrix

theorem M2M1_zero_left (n : ℕ) : imul M2inf M1inf 0 n = 0 := by
  ext i
  rw [imul, coeff_mk, map_zero]
  exact Finset.sum_eq_zero fun k _ => by rw [M2inf_zero_left, zero_mul, map_zero]

theorem H_ipow21 {j N : ℕ} (hN : j ≤ N) (r m n k i : ℕ) (_hm : 1 ≤ m) (hmN : m ≤ N)
    (_hn : 1 ≤ n) (_hnN : n ≤ N) (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (ipow (imul M2inf M1inf) r m k * imul M2inf M1inf k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [M2M1_zero_left, mul_zero, map_zero]
  · cases r with
    | zero =>
      rw [ipow, ione, if_neg (by omega), zero_mul, map_zero]
    | succ r => exact coeff_zero_of_dvd ((dvd_ipow_M2M1 r m k).mul_right _) (by omega)

theorem H_BzK21 {j N : ℕ} (hN : j ≤ N) (m n k i : ℕ) (hm : 1 ≤ m) (_hmN : m ≤ N) (_hn : 1 ≤ n)
    (_hnN : n ≤ N) (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (Bzinf m k * K21 k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Bzinf_zero_right, zero_mul, map_zero]
  · exact coeff_zero_of_dvd ((dvd_Bzinf m k).mul_right _) (by omega)

theorem H_BzK21M2 {j N : ℕ} (hN : j ≤ N) (m n k i : ℕ) (hm : 1 ≤ m) (_hmN : m ≤ N)
    (_hn : 1 ≤ n) (_hnN : n ≤ N) (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (imul Bzinf K21 m k * M2inf k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [M2inf_zero_left, mul_zero, map_zero]
  · exact coeff_zero_of_dvd ((dvd_BzK21 m k).mul_right _) (by omega)

theorem dvd_ipow_pow21 (r m n : ℕ) :
    (X : PowerSeries ℚ) ^ r ∣ ipow (imul M2inf M1inf) r m n := by
  induction r generalizing m n with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ r ih =>
    refine dvd_imul fun k => ?_
    rw [pow_succ]
    exact mul_dvd_mul (ih m k) ((dvd_pow_self X (Nat.succ_ne_zero n)).trans (dvd_M2M1 k n))

theorem bridge_ipow21 {j N : ℕ} (hN : j ≤ N) (r : ℕ) :
    (piJ j).mapMatrix (trN N (ipow (imul M2inf M1inf) r)) =
      ((piJ j).mapMatrix (trN N M2inf) * (piJ j).mapMatrix (trN N M1inf)) ^ r := by
  induction r with
  | zero => rw [ipow, trN_ione, map_one, pow_zero]
  | succ r ih =>
    rw [ipow, bridge_mul (H_ipow21 hN r), ih, bridge_mul (H_M1 hN M2inf)]
    exact (pow_succ _ r).symm

theorem bridge_K21 {j N : ℕ} (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N K21) =
      ∑ r ∈ range (j + 1),
        ((piJ j).mapMatrix (trN N M2inf) * (piJ j).mapMatrix (trN N M1inf)) ^ r := by
  have h1 : (piJ j).mapMatrix (trN N K21) =
      ∑ r ∈ range (j + 1), (piJ j).mapMatrix (trN N (ipow (imul M2inf M1inf) r)) := by
    rw [← map_sum]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, trN, Matrix.of_apply, Matrix.sum_apply]
    rw [piJ_eq_iff]
    intro i hi
    rw [K21, ineumann, coeff_mk, map_sum]
    exact Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr =>
      coeff_zero_of_dvd (dvd_ipow_pow21 r _ _) (by have := Finset.mem_range.not.1 hr; omega)
  rw [h1]
  exact Finset.sum_congr rfl fun r _ => bridge_ipow21 hN r

theorem bridge_Apm {j N : ℕ} (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N Apm) =
      (piJ j).mapMatrix
        (trN N Bzinf * (∑ r ∈ range (j + 1), (trN N M2inf * trN N M1inf) ^ r) * trN N M2inf) := by
  rw [Apm, bridge_mul (H_BzK21M2 hN), bridge_mul (H_BzK21 hN), bridge_K21 hN]
  simp only [map_mul, map_sum, map_pow]

theorem trN_Bzinf (N : ℕ) : trN N Bzinf = Zmat N * trN N Binf * Zmat N := by
  refine Matrix.ext fun a b => ?_
  simp only [Zmat, trN, Bzinf, Binf, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [pow_add]
  ring

/-- `Tr(B^{(z)} (M₂M₁)^r M₂) = Tr(D M^{2r+2})` in every truncation. -/
theorem trace_exact21 (N r : ℕ) :
    trace (trN N Bzinf * (trN N M2inf * trN N M1inf) ^ r * trN N M2inf) =
      trace (Dmat N * Mmat N ^ (2 * r + 2)) := by
  have hsw : (trN N M2inf * trN N M1inf) ^ r * trN N M2inf =
      trN N M2inf * (Mmat N * Mmat N) ^ r := by
    have hs : SemiconjBy (trN N M2inf) (trN N M1inf * trN N M2inf)
        (trN N M2inf * trN N M1inf) := by
      rw [SemiconjBy, Matrix.mul_assoc]
    have := (hs.pow_right r).eq
    rw [← this, trN_M1inf, Matrix.mul_assoc (Mmat N), ← Mmat_eq]
  rw [Matrix.mul_assoc, hsw, trN_Bzinf, trN_Binf, ← Matrix.mul_assoc (Zmat N), Zmat_mul_Dmat,
    Matrix.mul_assoc (Dmat N), ← Mmat_eq, Matrix.mul_assoc (Dmat N * Mmat N),
    ← Matrix.mul_assoc (Zmat N), ← Mmat_eq, ← pow_two, ← pow_mul, ← pow_succ',
    Matrix.mul_assoc, ← pow_succ']

/-- `Tr(A₊₋) = Tr(B^{(z)} K₂₁ M₂)`: at order `z^j` only the entries `m ≤ j` contribute. -/
noncomputable def traceApm : PowerSeries ℚ :=
  PowerSeries.mk fun j => ∑ m ∈ range (j + 1), coeff j (Apm (m + 1) (m + 1))

/-- `Tr(B^{(z)} K₂₁ M₂) = Tr(D M(z)² (I - M(z)²)⁻¹)`. -/
theorem traceApm_eq : traceApm = traceDM := by
  ext j
  rw [traceApm, coeff_mk, traceDM, coeff_mk]
  have hL : ∑ m ∈ range (j + 1), coeff j (Apm (m + 1) (m + 1)) =
      coeff j (trace (trN (j + 1) Apm)) := by
    rw [Matrix.trace, map_sum,
      ← Fin.sum_univ_eq_sum_range (fun m => coeff j (Apm (m + 1) (m + 1))) (j + 1)]
    rfl
  have hπ : ∀ A : Matrix (Fin (j + 1)) (Fin (j + 1)) (PowerSeries ℚ),
      piJ j (trace A) = trace ((piJ j).mapMatrix A) := fun A => by
    simp [Matrix.trace, map_sum, RingHom.mapMatrix_apply]
  have h1 : piJ j (trace (trN (j + 1) Apm)) =
      piJ j (trace (trN (j + 1) Bzinf *
        (∑ r ∈ range (j + 1), (trN (j + 1) M2inf * trN (j + 1) M1inf) ^ r) *
        trN (j + 1) M2inf)) := by
    rw [hπ, hπ, bridge_Apm (Nat.le_succ j)]
  have h2 := piJ_eq_iff.1 h1 j le_rfl
  rw [hL, h2, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, map_sum, map_sum]
  simp only [trace_exact21]
  rw [sum_Icc_shift (fun k => coeff j (trace (Dmat j * Mmat j ^ (2 * k)))) j,
    Finset.sum_range_succ, coeff_trace_of_lt _ (j + 1) (by omega), add_zero]
  exact Finset.sum_congr rfl fun r _ => coeff_trace_trunc _ le_rfl (Nat.le_succ j) (2 * r + 1)

end Virasoro.Sphere
