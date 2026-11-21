import Virasoro.Sphere.Proofs.Sec3BergmanSupport

/-!
# Sphere paper Lemma 3.5: infinite matrices and their truncations (`sphere/paper.tex` l.837–844)

Modulo `z^{j+1}` the truncation to indices `1 ≤ m, n ≤ N` (`N ≥ j`) of a product of the infinite
matrices of the proof is the product of the truncations, and the truncation of `K₁₂` is the
finite Neumann sum `∑_{r ≤ j} (M₁M₂)^r` of truncations.

Consumer: `traceAmp_eq` (`Tr(B K₁₂ M₁) = Tr(D M² (I - M²)⁻¹)`, l.943).
-/

namespace Virasoro.Sphere

open PowerSeries Finset Matrix

/-- The truncation of an infinite matrix to the indices `1 ≤ m, n ≤ N`. -/
noncomputable def trN (N : ℕ) (A : IMat) : Matrix (Fin N) (Fin N) (PowerSeries ℚ) :=
  Matrix.of fun a b => A ((a : ℕ) + 1) ((b : ℕ) + 1)

/-- Reduction modulo `z^{j+1}`. -/
noncomputable abbrev piJ (j : ℕ) :
    PowerSeries ℚ →+* PowerSeries ℚ ⧸ Ideal.span {(X : PowerSeries ℚ) ^ (j + 1)} :=
  Ideal.Quotient.mk (Ideal.span {(X : PowerSeries ℚ) ^ (j + 1)})

theorem piJ_eq_iff {j : ℕ} {f g : PowerSeries ℚ} :
    piJ j f = piJ j g ↔ ∀ i ≤ j, coeff i f = coeff i g := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton, X_pow_dvd_iff]
  constructor
  · intro h i hi
    have := h i (by omega)
    rwa [map_sub, sub_eq_zero] at this
  · intro h i hi
    rw [map_sub, h i (by omega), sub_self]

theorem coeff_zero_of_dvd {f : PowerSeries ℚ} {d i : ℕ} (h : (X : PowerSeries ℚ) ^ d ∣ f)
    (hi : i < d) : coeff i f = 0 :=
  X_pow_dvd_iff.1 h i hi

/-- Modulo `z^{j+1}`, the truncation of a product is the product of the truncations when the
terms `k = 0`, `k > N` and `k > m + n + i` have no coefficient of `z^i`, `i ≤ j`. -/
theorem bridge_mul {A B : IMat} {j N : ℕ}
    (H : ∀ m n k i, 1 ≤ m → m ≤ N → 1 ≤ n → n ≤ N → i ≤ j → (k = 0 ∨ N < k ∨ m + n + i < k) →
      coeff i (A m k * B k n) = 0) :
    (piJ j).mapMatrix (trN N (imul A B)) =
      (piJ j).mapMatrix (trN N A) * (piJ j).mapMatrix (trN N B) := by
  rw [← map_mul]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, trN, Matrix.of_apply, Matrix.mul_apply]
  rw [piJ_eq_iff]
  intro i hi
  rw [imul, coeff_mk, map_sum]
  set f : ℕ → ℚ := fun k => coeff i (A ((a : ℕ) + 1) k * B k ((b : ℕ) + 1)) with hf
  have hb : (b : ℕ) + 1 ≤ N := b.isLt
  have ha : (a : ℕ) + 1 ≤ N := a.isLt
  have h0 : f 0 = 0 := H _ _ 0 i (by omega) ha (by omega) hb hi (Or.inl rfl)
  have e2 : ∑ c : Fin N, f ((c : ℕ) + 1) = ∑ k ∈ range (N + 1), f k := by
    rw [Fin.sum_univ_eq_sum_range (fun c => f (c + 1)) N, Finset.sum_range_succ' f N, h0,
      add_zero]
  have s1 : ∑ k ∈ range ((a : ℕ) + 1 + ((b : ℕ) + 1) + i + 1), f k =
      ∑ k ∈ range (max ((a : ℕ) + 1 + ((b : ℕ) + 1) + i + 1) (N + 1)), f k :=
    Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun k _ hk =>
      H _ _ k i (by omega) ha (by omega) hb hi
        (Or.inr (Or.inr (by have := Finset.mem_range.not.1 hk; omega)))
  have s2 : ∑ k ∈ range (N + 1), f k =
      ∑ k ∈ range (max ((a : ℕ) + 1 + ((b : ℕ) + 1) + i + 1) (N + 1)), f k :=
    Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun k _ hk =>
      H _ _ k i (by omega) ha (by omega) hb hi
        (Or.inr (Or.inl (by have := Finset.mem_range.not.1 hk; omega)))
  exact s1.trans (s2.symm.trans e2.symm)

theorem M1M2_zero_left (n : ℕ) : imul M1inf M2inf 0 n = 0 := by
  ext i
  rw [imul, coeff_mk, map_zero]
  exact Finset.sum_eq_zero fun k _ => by rw [M1inf_zero_left, zero_mul, map_zero]

theorem H_M1M2 {j N : ℕ} (hN : j ≤ N) (m n k i : ℕ) (hm : 1 ≤ m) (_hmN : m ≤ N)
    (_hn : 1 ≤ n) (_hnN : n ≤ N)
    (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (M1inf m k * M2inf k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [M1inf_zero_right, zero_mul, map_zero]
  · exact coeff_zero_of_dvd ((dvd_M1inf m k).mul_right _) (by omega)

theorem H_ipow {j N : ℕ} (hN : j ≤ N) (r m n k i : ℕ) (_hm : 1 ≤ m) (_hmN : m ≤ N) (_hn : 1 ≤ n)
    (_hnN : n ≤ N) (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (ipow (imul M1inf M2inf) r m k * imul M1inf M2inf k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [M1M2_zero_left, mul_zero, map_zero]
  · exact coeff_zero_of_dvd ((dvd_M1M2 k n).mul_left _) (by omega)

theorem H_BK12 {j N : ℕ} (hN : j ≤ N) (m n k i : ℕ) (_hm : 1 ≤ m) (_hmN : m ≤ N)
    (_hn : 1 ≤ n) (hnN : n ≤ N)
    (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (Binf m k * K12 k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Binf, Bcoef_zero_right, map_zero, zero_mul, map_zero]
  · have hkn : k ≠ n := by omega
    have h := dvd_K12_sub k n
    rw [ione, if_neg hkn, sub_zero] at h
    exact coeff_zero_of_dvd (h.mul_left _) (by omega)

theorem H_M1 {j N : ℕ} (hN : j ≤ N) (A : IMat) (m n k i : ℕ) (_hm : 1 ≤ m)
    (_hmN : m ≤ N) (hn : 1 ≤ n)
    (_hnN : n ≤ N) (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (A m k * M1inf k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [M1inf_zero_left, mul_zero, map_zero]
  · exact coeff_zero_of_dvd ((dvd_M1inf k n).mul_left _) (by omega)

theorem dvd_ipow_pow (r m n : ℕ) :
    (X : PowerSeries ℚ) ^ r ∣ ipow (imul M1inf M2inf) r m n := by
  induction r generalizing m n with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ r ih =>
    refine dvd_imul fun k => ?_
    rw [pow_succ]
    exact mul_dvd_mul (ih m k) ((dvd_pow_self X (Nat.succ_ne_zero k)).trans (dvd_M1M2 k n))

theorem trN_ione (N : ℕ) : trN N ione = 1 := by
  ext a b
  simp only [trN, ione, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h (Fin.ext (by omega)))]

theorem bridge_ipow {j N : ℕ} (hN : j ≤ N) (r : ℕ) :
    (piJ j).mapMatrix (trN N (ipow (imul M1inf M2inf) r)) =
      ((piJ j).mapMatrix (trN N M1inf) * (piJ j).mapMatrix (trN N M2inf)) ^ r := by
  induction r with
  | zero => rw [ipow, trN_ione, map_one, pow_zero]
  | succ r ih =>
    rw [ipow, bridge_mul (H_ipow hN r), ih, bridge_mul (H_M1M2 hN)]
    exact (pow_succ _ r).symm

/-- Modulo `z^{j+1}` the truncation of `K₁₂` is `∑_{r ≤ j} (M₁M₂)^r`. -/
theorem bridge_K12 {j N : ℕ} (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N K12) =
      ∑ r ∈ range (j + 1),
        ((piJ j).mapMatrix (trN N M1inf) * (piJ j).mapMatrix (trN N M2inf)) ^ r := by
  have h1 : (piJ j).mapMatrix (trN N K12) =
      ∑ r ∈ range (j + 1), (piJ j).mapMatrix (trN N (ipow (imul M1inf M2inf) r)) := by
    rw [← map_sum]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, trN, Matrix.of_apply, Matrix.sum_apply]
    rw [piJ_eq_iff]
    intro i hi
    rw [K12, ineumann, coeff_mk, map_sum]
    exact Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr =>
      coeff_zero_of_dvd (dvd_ipow_pow r _ _) (by have := Finset.mem_range.not.1 hr; omega)
  rw [h1]
  exact Finset.sum_congr rfl fun r _ => bridge_ipow hN r

/-- Modulo `z^{j+1}` the truncation of `A₋₊ = B K₁₂ M₁` is the product of truncations with the
finite Neumann sum. -/
theorem bridge_Amp {j N : ℕ} (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N Amp) =
      (piJ j).mapMatrix
        (trN N Binf * (∑ r ∈ range (j + 1), (trN N M1inf * trN N M2inf) ^ r) * trN N M1inf) := by
  rw [Amp, bridge_mul (H_M1 hN _), bridge_mul (H_BK12 hN), bridge_K12 hN]
  simp only [map_mul, map_sum, map_pow]

end Virasoro.Sphere
