import Virasoro.Sphere.Proofs.Sec3BergmanTraceApm

/-!
# Sphere paper Lemma 3.5, Step 2: `D + B K₁₂ M₁ = D K₂₁` and `B K₁₂ = D K₂₁ M₂`
(`sphere/paper.tex` l.891)

Both identities hold in every truncation modulo `z^{j+1}` (`B = D M₂` and
`M₂ (M₁M₂)^r = (M₂M₁)^r M₂`), hence for the infinite matrices.

Consumer: the inner and outer patches of Step 2 (`Stmt_sub_bergman_liouville`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset Matrix

theorem neumann_shift {R : Type*} [Ring R] (a b : R) (r : ℕ) :
    a * (b * a) ^ r * b = (a * b) ^ (r + 1) := by
  have hs : SemiconjBy a (b * a) (a * b) := by rw [SemiconjBy, mul_assoc]
  rw [(hs.pow_right r).eq, mul_assoc, ← pow_succ]

theorem neumann_swap {R : Type*} [Ring R] (a b : R) (r : ℕ) :
    a * (b * a) ^ r = (a * b) ^ r * a := by
  have hs : SemiconjBy a (b * a) (a * b) := by rw [SemiconjBy, mul_assoc]
  exact (hs.pow_right r).eq

theorem bridge_Amp_add_D {j N : ℕ} (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N Amp + Dmat N) = (piJ j).mapMatrix (Dmat N * trN N K21) := by
  have hz : (piJ j).mapMatrix ((trN N M2inf * trN N M1inf) ^ (j + 1)) = 0 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine dvd_pow_entry X _ (fun a b => ?_) (j + 1) a b
    rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun c _ => Dvd.dvd.mul_left ?_ _
    simp only [trN, Matrix.of_apply]
    exact (dvd_pow_self X (by omega)).trans (dvd_M1inf _ _)
  rw [map_add, bridge_Amp hN, map_mul (piJ j).mapMatrix (Dmat N), bridge_K21 hN, trN_Binf]
  simp only [map_mul, map_sum, map_pow] at hz ⊢
  set d := (piJ j).mapMatrix (Dmat N)
  set m1 := (piJ j).mapMatrix (trN N M1inf)
  set m2 := (piJ j).mapMatrix (trN N M2inf)
  have h1 : d * m2 * (∑ r ∈ range (j + 1), (m1 * m2) ^ r) * m1 =
      d * ∑ r ∈ range (j + 1), (m2 * m1) ^ (r + 1) := by
    rw [Matrix.mul_assoc d, Matrix.mul_assoc d, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun r _ => neumann_shift m2 m1 r
  have h2 : ∑ r ∈ range (j + 1), (m2 * m1) ^ r =
      ∑ r ∈ range (j + 1), (m2 * m1) ^ (r + 1) + 1 := by
    have := Finset.sum_range_succ' (fun r => (m2 * m1) ^ r) (j + 1)
    rw [Finset.sum_range_succ, hz, add_zero, pow_zero] at this
    exact this
  rw [h1, h2, mul_add, mul_one]

/-- `D + B K₁₂ M₁ = D K₂₁` (sphere/paper.tex l.891), entry `(a+1, b+1)`. -/
theorem Amp_add_D (a b : ℕ) :
    Amp (a + 1) (b + 1) + C (((a + 1 : ℕ)) : ℚ) * ione (a + 1) (b + 1) =
      C (((a + 1 : ℕ)) : ℚ) * K21 (a + 1) (b + 1) := by
  ext j
  have hN : j ≤ max j (max (a + 1) (b + 1)) := le_max_left _ _
  have ha : a < max j (max (a + 1) (b + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self a) ((le_max_left _ _).trans (le_max_right _ _))
  have hb : b < max j (max (a + 1) (b + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self b) ((le_max_right _ _).trans (le_max_right _ _))
  have e := congrFun (congrFun (bridge_Amp_add_D hN) ⟨a, ha⟩) ⟨b, hb⟩
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, trN, Matrix.of_apply,
    Matrix.diagonal_mul, Matrix.diagonal_apply, Fin.mk.injEq] at e
  have e' := piJ_eq_iff.1 e j le_rfl
  have hi : ione (a + 1) (b + 1) = if a = b then 1 else 0 := by
    rw [ione]
    simp only [add_left_inj]
  rw [show C (((a + 1 : ℕ)) : ℚ) = (((a + 1 : ℕ)) : PowerSeries ℚ) from map_natCast _ _, hi,
    mul_ite, mul_one, mul_zero]
  exact e'

theorem H_K21M2 {j N : ℕ} (hN : j ≤ N) (m n k i : ℕ) (_hm : 1 ≤ m) (hmN : m ≤ N) (_hn : 1 ≤ n)
    (_hnN : n ≤ N) (hi : i ≤ j) (hk : k = 0 ∨ N < k ∨ m + n + i < k) :
    coeff i (K21 m k * M2inf k n) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [M2inf_zero_left, mul_zero, map_zero]
  · have hkm : m ≠ k := by omega
    have h := dvd_K21_sub m k
    rw [ione, if_neg hkm, sub_zero] at h
    exact coeff_zero_of_dvd (h.mul_right _) (by omega)

theorem bridge_BK12 {j N : ℕ} (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N (imul Binf K12)) =
      (piJ j).mapMatrix (Dmat N) * (piJ j).mapMatrix (trN N (imul K21 M2inf)) := by
  rw [bridge_mul (H_BK12 hN), bridge_K12 hN, bridge_mul (H_K21M2 hN), bridge_K21 hN, trN_Binf,
    map_mul]
  set d := (piJ j).mapMatrix (Dmat N)
  set m1 := (piJ j).mapMatrix (trN N M1inf)
  set m2 := (piJ j).mapMatrix (trN N M2inf)
  rw [Matrix.mul_assoc d, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun r _ => neumann_swap m2 m1 r

/-- `B K₁₂ = D K₂₁ M₂` (sphere/paper.tex l.891), entry `(a+1, b+1)`. -/
theorem BK12_eq (a b : ℕ) :
    imul Binf K12 (a + 1) (b + 1) =
      C (((a + 1 : ℕ)) : ℚ) * imul K21 M2inf (a + 1) (b + 1) := by
  ext j
  have hN : j ≤ max j (max (a + 1) (b + 1)) := le_max_left _ _
  have ha : a < max j (max (a + 1) (b + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self a) ((le_max_left _ _).trans (le_max_right _ _))
  have hb : b < max j (max (a + 1) (b + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self b) ((le_max_right _ _).trans (le_max_right _ _))
  have e := congrFun (congrFun (bridge_BK12 hN) ⟨a, ha⟩) ⟨b, hb⟩
  rw [← map_mul] at e
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, trN, Matrix.of_apply,
    Matrix.diagonal_mul] at e
  have e' := piJ_eq_iff.1 e j le_rfl
  rw [show C (((a + 1 : ℕ)) : ℚ) = (((a + 1 : ℕ)) : PowerSeries ℚ) from map_natCast _ _]
  exact e'

end Virasoro.Sphere
