import Virasoro.Sphere.Proofs.Sec3BergmanBridge

/-!
# Sphere paper Lemma 3.5: `Tr(B K₁₂ M₁) = Tr(D M(z)² (I - M(z)²)⁻¹)` (`sphere/paper.tex` l.943)

With `Z = diag(z, z², …)`: `B = D M₂`, `M(z) = Z M₂`, `M₁ = M(z) Z`, so `M₁M₂ = M(z)²` and
`Tr(B (M₁M₂)^r M₁) = Tr(D M₂ M^{2r+1} Z) = Tr(D M^{2r+2})` by cyclicity of the trace, in every
truncation; the truncations compute the infinite trace modulo `z^{j+1}`.

Consumer: `Stmt_sub_bergman_residue`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Matrix

/-- The truncation of `Z = diag(z, z², …)`. -/
noncomputable def Zmat (N : ℕ) : Matrix (Fin N) (Fin N) (PowerSeries ℚ) :=
  Matrix.diagonal fun b => (X : PowerSeries ℚ) ^ ((b : ℕ) + 1)

theorem trN_Binf (N : ℕ) : trN N Binf = Dmat N * trN N M2inf := by
  refine Matrix.ext fun a b => ?_
  simp only [trN, Binf, M2inf, Matrix.of_apply, Matrix.diagonal_mul]
  rw [show (((a : ℕ) + 1 : ℕ) : PowerSeries ℚ) = C ((((a : ℕ) + 1 : ℕ)) : ℚ) from
    (map_natCast (C (R := ℚ)) ((a : ℕ) + 1)).symm, ← map_mul]
  congr 1
  have : ((((a : ℕ) + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero (a : ℕ))
  field_simp

theorem Mmat_eq (N : ℕ) : Mmat N = Zmat N * trN N M2inf := by
  refine Matrix.ext fun a b => ?_
  simp only [Mmat, Zmat, trN, M2inf, Matrix.of_apply, Matrix.diagonal_mul]
  rw [mul_comm]

theorem trN_M1inf (N : ℕ) : trN N M1inf = Mmat N * Zmat N := by
  refine Matrix.ext fun a b => ?_
  simp only [Mmat, Zmat, trN, M1inf, Matrix.of_apply, Matrix.mul_diagonal]
  rw [pow_add, mul_assoc]

theorem Zmat_mul_Dmat (N : ℕ) : Zmat N * Dmat N = Dmat N * Zmat N := by
  show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/-- `Tr(B (M₁M₂)^r M₁) = Tr(D M^{2r+2})` in every truncation. -/
theorem trace_exact (N r : ℕ) :
    trace (trN N Binf * (trN N M1inf * trN N M2inf) ^ r * trN N M1inf) =
      trace (Dmat N * Mmat N ^ (2 * r + 2)) := by
  have hMM : trN N M1inf * trN N M2inf = Mmat N * Mmat N := by
    rw [trN_M1inf, Matrix.mul_assoc, ← Mmat_eq]
  rw [hMM, trN_Binf, trN_M1inf, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Zmat_mul_Dmat, Matrix.mul_assoc (Dmat N) (Zmat N),
    ← Mmat_eq, ← pow_two, ← pow_mul, Matrix.mul_assoc (Dmat N), ← pow_succ', Matrix.mul_assoc,
    ← pow_succ]

/-- `Tr(A₋₊) = Tr(B K₁₂ M₁)`: at order `z^j` only the entries `m ≤ j` contribute. -/
noncomputable def traceAmp : PowerSeries ℚ :=
  PowerSeries.mk fun j => ∑ m ∈ range (j + 1), coeff j (Amp (m + 1) (m + 1))

theorem sum_Icc_shift (g : ℕ → ℚ) (n : ℕ) : ∑ k ∈ Icc 1 n, g k = ∑ r ∈ range n, g (r + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `Tr(B K₁₂ M₁) = Tr(D M(z)² (I - M(z)²)⁻¹)` (sphere/paper.tex l.943). -/
theorem traceAmp_eq : traceAmp = traceDM := by
  ext j
  rw [traceAmp, coeff_mk, traceDM, coeff_mk]
  have hL : ∑ m ∈ range (j + 1), coeff j (Amp (m + 1) (m + 1)) =
      coeff j (trace (trN (j + 1) Amp)) := by
    rw [Matrix.trace, map_sum,
      ← Fin.sum_univ_eq_sum_range (fun m => coeff j (Amp (m + 1) (m + 1))) (j + 1)]
    rfl
  have hπ : ∀ A : Matrix (Fin (j + 1)) (Fin (j + 1)) (PowerSeries ℚ),
      piJ j (trace A) = trace ((piJ j).mapMatrix A) := fun A => by
    simp [Matrix.trace, map_sum, RingHom.mapMatrix_apply]
  have h1 : piJ j (trace (trN (j + 1) Amp)) =
      piJ j (trace (trN (j + 1) Binf *
        (∑ r ∈ range (j + 1), (trN (j + 1) M1inf * trN (j + 1) M2inf) ^ r) *
        trN (j + 1) M1inf)) := by
    rw [hπ, hπ, bridge_Amp (Nat.le_succ j)]
  have h2 := piJ_eq_iff.1 h1 j le_rfl
  rw [hL, h2, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, map_sum, map_sum]
  simp only [trace_exact]
  rw [sum_Icc_shift (fun k => coeff j (trace (Dmat j * Mmat j ^ (2 * k)))) j,
    Finset.sum_range_succ, coeff_trace_of_lt _ (j + 1) (by omega), add_zero]
  exact Finset.sum_congr rfl fun r _ => coeff_trace_trunc _ le_rfl (Nat.le_succ j) (2 * r + 1)

end Virasoro.Sphere
