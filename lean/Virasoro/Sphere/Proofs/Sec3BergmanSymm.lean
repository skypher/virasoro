import Virasoro.Sphere.Proofs.Sec3BergmanIds

/-!
# Sphere paper Lemma 3.5: symmetry of the blocks and the row relations of the two patches
(`sphere/paper.tex` l.876–877, l.891, l.924)

Modulo `z^{j+1}` and truncated to `1 ≤ m, n ≤ N` (`N ≥ j`) the blocks are
`A₊₊ = -D M₁ Σ₂₁`, `A₋₋ = -D M₂ Σ₁₂`, `A₋₊ = D M₂ Σ₁₂ M₁`, `A₊₋ = D M₁ Σ₂₁ M₂`
with `Σ₁₂ = ∑_{r ≤ j} (M₁M₂)^r`, `Σ₂₁ = ∑_{r ≤ j} (M₂M₁)^r`, and `D M₁`, `D M₂` are symmetric.
Hence `A₊₊`, `A₋₋` are symmetric and `A₊₋ = A₋₊ᵀ` (l.876–877), and

* `A₋₊ = -(B D⁻¹) A₊₊`, `A₋₋ + B = -(B D⁻¹) A₊₋` (outer patch, `D w = (D + A₊₋)x₂^{•-1} + …`);
* `A₊₊ = -(B^{(z)} D⁻¹)(A₋₊ + D)`, `A₊₋ = -(B^{(z)} D⁻¹) A₋₋` (inner patch, l.891–894).

Consumers: `sub_bergman_symm`, the inner and outer patches.
-/

namespace Virasoro.Sphere

open PowerSeries Finset Matrix

section abstract

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (d m1 m2 t : Matrix ι ι R) (n : ℕ)

theorem fin_swapS :
    m1 * ∑ r ∈ range n, (m2 * m1) ^ r = (∑ r ∈ range n, (m1 * m2) ^ r) * m1 := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => neumann_swap m1 m2 r

theorem fin_shiftS (hz : (m1 * m2) ^ n = 0) :
    m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2 = ∑ r ∈ range n, (m1 * m2) ^ r - 1 := by
  rw [Finset.mul_sum, Finset.sum_mul]
  have h1 : ∑ r ∈ range n, m1 * (m2 * m1) ^ r * m2 = ∑ r ∈ range n, (m1 * m2) ^ (r + 1) :=
    Finset.sum_congr rfl fun r _ => neumann_shift m1 m2 r
  have h2 := Finset.sum_range_succ' (fun r => (m1 * m2) ^ r) n
  rw [Finset.sum_range_succ, hz, add_zero, pow_zero] at h2
  rw [h1, h2, add_sub_cancel_right]

theorem fin_semi_tr (hd : dᵀ = d) (h1 : (d * m1)ᵀ = d * m1) (h2 : (d * m2)ᵀ = d * m2) (r : ℕ) :
    ((m2 * m1) ^ r)ᵀ * d = d * (m1 * m2) ^ r := by
  have e1 : m1ᵀ * d = d * m1 := by rw [← h1, transpose_mul, hd]
  have e2 : m2ᵀ * d = d * m2 := by rw [← h2, transpose_mul, hd]
  have hs : SemiconjBy d (m1 * m2) (m1ᵀ * m2ᵀ) := by
    rw [SemiconjBy]
    calc d * (m1 * m2) = (d * m1) * m2 := (Matrix.mul_assoc _ _ _).symm
      _ = (m1ᵀ * d) * m2 := by rw [e1]
      _ = m1ᵀ * (d * m2) := Matrix.mul_assoc _ _ _
      _ = m1ᵀ * (m2ᵀ * d) := by rw [e2]
      _ = m1ᵀ * m2ᵀ * d := (Matrix.mul_assoc _ _ _).symm
  rw [transpose_pow, transpose_mul]
  exact ((hs.pow_right r).eq).symm

theorem fin_A1 (hd : dᵀ = d) (h1 : (d * m1)ᵀ = d * m1) (h2 : (d * m2)ᵀ = d * m2) :
    (d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r)ᵀ = d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r := by
  have key : ∀ r, ((m2 * m1) ^ r)ᵀ * (d * m1) = d * m1 * (m2 * m1) ^ r := fun r => by
    calc ((m2 * m1) ^ r)ᵀ * (d * m1) = ((m2 * m1) ^ r)ᵀ * d * m1 := (Matrix.mul_assoc _ _ _).symm
      _ = d * (m1 * m2) ^ r * m1 := by rw [fin_semi_tr d m1 m2 hd h1 h2 r]
      _ = d * ((m1 * m2) ^ r * m1) := Matrix.mul_assoc _ _ _
      _ = d * (m1 * (m2 * m1) ^ r) := by rw [neumann_swap m1 m2 r]
      _ = d * m1 * (m2 * m1) ^ r := (Matrix.mul_assoc _ _ _).symm
  calc (d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r)ᵀ
      = (∑ r ∈ range n, (m2 * m1) ^ r)ᵀ * (d * m1) := by rw [transpose_mul, h1]
    _ = ∑ r ∈ range n, ((m2 * m1) ^ r)ᵀ * (d * m1) := by rw [transpose_sum, Finset.sum_mul]
    _ = ∑ r ∈ range n, d * m1 * (m2 * m1) ^ r := Finset.sum_congr rfl fun r _ => key r
    _ = d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r := (Finset.mul_sum _ _ _).symm

theorem fin_A3 (hd : dᵀ = d) (h1 : (d * m1)ᵀ = d * m1) (h2 : (d * m2)ᵀ = d * m2) :
    (d * m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2)ᵀ =
      d * m2 * (∑ r ∈ range n, (m1 * m2) ^ r) * m1 := by
  have e2 : m2ᵀ * d = d * m2 := by rw [← h2, transpose_mul, hd]
  calc (d * m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2)ᵀ
      = m2ᵀ * (d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r) := by
        rw [transpose_mul, fin_A1 d m1 m2 n hd h1 h2]
    _ = (m2ᵀ * d) * (m1 * ∑ r ∈ range n, (m2 * m1) ^ r) := by simp only [Matrix.mul_assoc]
    _ = d * m2 * ((∑ r ∈ range n, (m1 * m2) ^ r) * m1) := by rw [e2, fin_swapS]
    _ = d * m2 * (∑ r ∈ range n, (m1 * m2) ^ r) * m1 := by simp only [Matrix.mul_assoc]

theorem fin_A4 (ht : t * d = d * m2) (hz : (m1 * m2) ^ n = 0) :
    t * (d * m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2) =
      d * m2 * (∑ r ∈ range n, (m1 * m2) ^ r) - d * m2 := by
  calc t * (d * m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2)
      = (t * d) * (m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2) := by simp only [Matrix.mul_assoc]
    _ = d * m2 * (∑ r ∈ range n, (m1 * m2) ^ r - 1) := by rw [ht, fin_shiftS m1 m2 n hz]
    _ = _ := by rw [Matrix.mul_sub, Matrix.mul_one]

theorem fin_A5 (ht : t * d = d * m2) :
    t * (d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r) =
      d * m2 * (∑ r ∈ range n, (m1 * m2) ^ r) * m1 := by
  calc t * (d * m1 * ∑ r ∈ range n, (m2 * m1) ^ r)
      = (t * d) * (m1 * ∑ r ∈ range n, (m2 * m1) ^ r) := by simp only [Matrix.mul_assoc]
    _ = d * m2 * ((∑ r ∈ range n, (m1 * m2) ^ r) * m1) := by rw [ht, fin_swapS]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem fin_A7 (ht : t * d = d * m2) (hz : (m1 * m2) ^ n = 0) :
    t * (d * m1 * (∑ r ∈ range n, (m2 * m1) ^ r) * m2 + d) =
      d * m2 * ∑ r ∈ range n, (m1 * m2) ^ r := by
  rw [Matrix.mul_add, fin_A4 d m1 m2 t n ht hz, ht, sub_add_cancel]

end abstract

/-- `B D⁻¹` (the transpose of `M₂`). -/
noncomputable def M2tinf : IMat := fun m n => C (Bcoef m n / (n : ℚ))

/-- `B^{(z)} D⁻¹` (the transpose of `M₁`). -/
noncomputable def M1tinf : IMat := fun m n => C (Bcoef m n / (n : ℚ)) * X ^ (m + n)

theorem trN_Bzinf_D (N : ℕ) : trN N Bzinf = Dmat N * trN N M1inf := by
  refine Matrix.ext fun a b => ?_
  simp only [trN, Bzinf, M1inf, Matrix.of_apply, Matrix.diagonal_mul]
  have hne : ((((a : ℕ) + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero (a : ℕ))
  have hq : ((((a : ℕ) + 1 : ℕ)) : ℚ) *
      (Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1) / ((((a : ℕ) + 1 : ℕ)) : ℚ)) =
      Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1) := by field_simp
  rw [show (((a : ℕ) + 1 : ℕ) : PowerSeries ℚ) = C ((((a : ℕ) + 1 : ℕ)) : ℚ) from
    (map_natCast (C (R := ℚ)) ((a : ℕ) + 1)).symm, ← mul_assoc, ← map_mul, hq]

theorem trN_M2t_mul_D (N : ℕ) : trN N M2tinf * Dmat N = trN N Binf := by
  refine Matrix.ext fun a b => ?_
  simp only [trN, Binf, M2tinf, Matrix.of_apply, Matrix.mul_diagonal]
  have hne : ((((b : ℕ) + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero (b : ℕ))
  have hq : Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1) / ((((b : ℕ) + 1 : ℕ)) : ℚ) *
      ((((b : ℕ) + 1 : ℕ)) : ℚ) = Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1) := by field_simp
  rw [show (((b : ℕ) + 1 : ℕ) : PowerSeries ℚ) = C ((((b : ℕ) + 1 : ℕ)) : ℚ) from
    (map_natCast (C (R := ℚ)) ((b : ℕ) + 1)).symm, ← map_mul, hq]

theorem trN_M1t_mul_D (N : ℕ) : trN N M1tinf * Dmat N = trN N Bzinf := by
  refine Matrix.ext fun a b => ?_
  simp only [trN, Bzinf, M1tinf, Matrix.of_apply, Matrix.mul_diagonal]
  have hne : ((((b : ℕ) + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero (b : ℕ))
  have hq : Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1) / ((((b : ℕ) + 1 : ℕ)) : ℚ) *
      ((((b : ℕ) + 1 : ℕ)) : ℚ) = Bcoef ((a : ℕ) + 1) ((b : ℕ) + 1) := by field_simp
  rw [show (((b : ℕ) + 1 : ℕ) : PowerSeries ℚ) = C ((((b : ℕ) + 1 : ℕ)) : ℚ) from
    (map_natCast (C (R := ℚ)) ((b : ℕ) + 1)).symm, mul_right_comm, ← map_mul, hq]

theorem trN_Binf_transpose (N : ℕ) : (trN N Binf)ᵀ = trN N Binf := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.transpose_apply, trN, Binf, Matrix.of_apply]
  rw [Bcoef_symm]

theorem trN_Bzinf_transpose (N : ℕ) : (trN N Bzinf)ᵀ = trN N Bzinf := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.transpose_apply, trN, Bzinf, Matrix.of_apply]
  rw [Bcoef_symm, Nat.add_comm ((b : ℕ) + 1) ((a : ℕ) + 1)]

section model

variable (j N : ℕ)

/-- `D`, `M₁`, `M₂` truncated and reduced modulo `z^{j+1}`. -/
noncomputable abbrev qd := (piJ j).mapMatrix (Dmat N)
noncomputable abbrev qm1 := (piJ j).mapMatrix (trN N M1inf)
noncomputable abbrev qm2 := (piJ j).mapMatrix (trN N M2inf)
noncomputable abbrev qS12 := ∑ r ∈ range (j + 1), (qm1 j N * qm2 j N) ^ r
noncomputable abbrev qS21 := ∑ r ∈ range (j + 1), (qm2 j N * qm1 j N) ^ r

theorem qd_transpose : (qd j N)ᵀ = qd j N := by
  rw [qd, RingHom.mapMatrix_apply, ← Matrix.transpose_map]
  congr 1
  exact Matrix.diagonal_transpose _

theorem qdm1_transpose : (qd j N * qm1 j N)ᵀ = qd j N * qm1 j N := by
  rw [qd, qm1, ← map_mul, ← trN_Bzinf_D, RingHom.mapMatrix_apply, ← Matrix.transpose_map,
    trN_Bzinf_transpose]

theorem qdm2_transpose : (qd j N * qm2 j N)ᵀ = qd j N * qm2 j N := by
  rw [qd, qm2, ← map_mul, ← trN_Binf, RingHom.mapMatrix_apply, ← Matrix.transpose_map,
    trN_Binf_transpose]

theorem qt_mul_d : (piJ j).mapMatrix (trN N M2tinf) * qd j N = qd j N * qm2 j N := by
  rw [qd, qm2, ← map_mul, ← map_mul, trN_M2t_mul_D, trN_Binf]

theorem qu_mul_d : (piJ j).mapMatrix (trN N M1tinf) * qd j N = qd j N * qm1 j N := by
  rw [qd, qm1, ← map_mul, ← map_mul, trN_M1t_mul_D, trN_Bzinf_D]

theorem qz12 : (qm1 j N * qm2 j N) ^ (j + 1) = 0 := by
  have hz : (piJ j).mapMatrix ((trN N M1inf * trN N M2inf) ^ (j + 1)) = 0 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine dvd_pow_entry X _ (fun a b => ?_) (j + 1) a b
    rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun c _ => Dvd.dvd.mul_right ?_ _
    simp only [trN, Matrix.of_apply]
    exact (dvd_pow_self X (by omega)).trans (dvd_M1inf _ _)
  simpa only [map_mul, map_pow] using hz

theorem qz21 : (qm2 j N * qm1 j N) ^ (j + 1) = 0 := by
  have hz : (piJ j).mapMatrix ((trN N M2inf * trN N M1inf) ^ (j + 1)) = 0 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine dvd_pow_entry X _ (fun a b => ?_) (j + 1) a b
    rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun c _ => Dvd.dvd.mul_left ?_ _
    simp only [trN, Matrix.of_apply]
    exact (dvd_pow_self X (by omega)).trans (dvd_M1inf _ _)
  simpa only [map_mul, map_pow] using hz

variable {j N}

theorem fApp (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N App) = -(qd j N * qm1 j N * qS21 j N) := by
  have e : trN N App = -trN N (imul Bzinf K21) := Matrix.ext fun a b => rfl
  rw [e, map_neg, bridge_mul (H_BzK21 hN), bridge_K21 hN, trN_Bzinf_D, map_mul]

theorem fAmm (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N Amm) = -(qd j N * qm2 j N * qS12 j N) := by
  have e : trN N Amm = -trN N (imul Binf K12) := Matrix.ext fun a b => rfl
  rw [e, map_neg, bridge_mul (H_BK12 hN), bridge_K12 hN, trN_Binf, map_mul]

theorem fAmp (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N Amp) = qd j N * qm2 j N * qS12 j N * qm1 j N := by
  rw [bridge_Amp hN, trN_Binf]
  simp only [map_mul, map_sum, map_pow]

theorem fApm (hN : j ≤ N) :
    (piJ j).mapMatrix (trN N Apm) = qd j N * qm1 j N * qS21 j N * qm2 j N := by
  rw [bridge_Apm hN, trN_Bzinf_D]
  simp only [map_mul, map_sum, map_pow]

end model

/-- Bounds for the truncation size `max j (max (a+1) (b+1))`. -/
theorem trunc_bounds (j a b : ℕ) :
    j ≤ max j (max (a + 1) (b + 1)) ∧ a < max j (max (a + 1) (b + 1)) ∧
      b < max j (max (a + 1) (b + 1)) :=
  ⟨le_max_left _ _,
    lt_of_lt_of_le (Nat.lt_succ_self a) ((le_max_left _ _).trans (le_max_right _ _)),
    lt_of_lt_of_le (Nat.lt_succ_self b) ((le_max_right _ _).trans (le_max_right _ _))⟩

theorem entry_transpose {j N a b : ℕ} (ha : a < N) (hb : b < N) {L L' : IMat}
    (h : ((piJ j).mapMatrix (trN N L))ᵀ = (piJ j).mapMatrix (trN N L')) :
    coeff j (L (b + 1) (a + 1)) = coeff j (L' (a + 1) (b + 1)) := by
  have e := congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, trN,
    Matrix.of_apply] at e
  exact piJ_eq_iff.1 e j le_rfl

/-- `A₊₊` is symmetric (l.876). -/
theorem App_symm (a b : ℕ) : App (a + 1) (b + 1) = App (b + 1) (a + 1) := by
  ext j
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  refine (entry_transpose (L := App) (L' := App) ha hb ?_).symm
  rw [fApp hN, Matrix.transpose_neg,
    fin_A1 _ _ _ _ (qd_transpose j _) (qdm1_transpose j _) (qdm2_transpose j _)]

/-- `A₋₋` is symmetric (l.876). -/
theorem Amm_symm (a b : ℕ) : Amm (a + 1) (b + 1) = Amm (b + 1) (a + 1) := by
  ext j
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  refine (entry_transpose (L := Amm) (L' := Amm) ha hb ?_).symm
  rw [fAmm hN, Matrix.transpose_neg,
    fin_A1 _ _ _ _ (qd_transpose j _) (qdm2_transpose j _) (qdm1_transpose j _)]

/-- `A₊₋ = A₋₊ᵀ` (l.877). -/
theorem Apm_eq_Amp_transpose (a b : ℕ) : Apm (b + 1) (a + 1) = Amp (a + 1) (b + 1) := by
  ext j
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  refine entry_transpose (L := Apm) (L' := Amp) ha hb ?_
  rw [fApm hN, fAmp hN,
    fin_A3 _ _ _ _ (qd_transpose j _) (qdm1_transpose j _) (qdm2_transpose j _)]

theorem coeff_trN_mul (j N : ℕ) (T A : IMat) (a b : Fin N) :
    coeff j ((trN N T * trN N A) a b) =
      ∑ c ∈ range N, coeff j (T ((a : ℕ) + 1) (c + 1) * A (c + 1) ((b : ℕ) + 1)) := by
  rw [Matrix.mul_apply, map_sum]
  exact Fin.sum_univ_eq_sum_range
    (fun c => coeff j (T ((a : ℕ) + 1) (c + 1) * A (c + 1) ((b : ℕ) + 1))) N

/-- Entry `(a+1, b+1)` at order `z^j` of a relation `L = -T A` between truncations. -/
theorem entry_neg_mul {j N a b : ℕ} (hN : j ≤ N) (ha : a < N) (hb : b < N) {L T A : IMat}
    (h : (piJ j).mapMatrix (trN N L) =
      -((piJ j).mapMatrix (trN N T) * (piJ j).mapMatrix (trN N A)))
    (hz : ∀ c, j ≤ c → coeff j (T (a + 1) (c + 1) * A (c + 1) (b + 1)) = 0) :
    coeff j (L (a + 1) (b + 1)) =
      -∑ n ∈ range j, coeff j (T (a + 1) (n + 1) * A (n + 1) (b + 1)) := by
  rw [← map_mul, ← map_neg] at h
  have e := congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
  have e' := piJ_eq_iff.1 e j le_rfl
  rw [Matrix.neg_apply, map_neg, coeff_trN_mul] at e'
  rw [show L (a + 1) (b + 1) = trN N L ⟨a, ha⟩ ⟨b, hb⟩ from rfl, e']
  congr 1
  exact (Finset.sum_subset (Finset.range_mono hN) fun c _ hc =>
    hz c (not_lt.1 (Finset.mem_range.not.1 hc))).symm

/-- Outer patch: `A₋₊ = -(B D⁻¹) A₊₊`, entrywise at order `z^j`. -/
theorem Amp_eq_sum (j a b : ℕ) :
    coeff j (Amp (a + 1) (b + 1)) =
      -∑ n ∈ range j, Bcoef (a + 1) (n + 1) / (((n + 1 : ℕ)) : ℚ) *
        coeff j (App (n + 1) (b + 1)) := by
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  have h := entry_neg_mul (L := Amp) (T := M2tinf) (A := App) hN ha hb
    (by rw [fAmp hN, fApp hN, Matrix.mul_neg, neg_neg,
      fin_A5 _ _ _ _ _ (qt_mul_d j _)])
    (fun c hc => coeff_zero_of_dvd ((dvd_App (c + 1) (b + 1)).mul_left _) (by omega))
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [M2tinf, coeff_C_mul]

/-- Outer patch: `A₋₋ + B = -(B D⁻¹) A₊₋`, entrywise at order `z^j`. -/
theorem Amm_eq_sum (j a b : ℕ) :
    coeff j (Amm (a + 1) (b + 1)) + (if j = 0 then Bcoef (a + 1) (b + 1) else 0) =
      -∑ n ∈ range j, Bcoef (a + 1) (n + 1) / (((n + 1 : ℕ)) : ℚ) *
        coeff j (Apm (n + 1) (b + 1)) := by
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  have h := entry_neg_mul (L := fun m n => Amm m n + Binf m n) (T := M2tinf) (A := Apm) hN ha hb
    (by
      have e : trN (max j (max (a + 1) (b + 1))) (fun m n => Amm m n + Binf m n) =
          trN _ Amm + trN _ Binf := Matrix.ext fun a b => rfl
      rw [e, map_add, fAmm hN, fApm hN, fin_A4 _ _ _ _ _ (qt_mul_d j _) (qz12 j _), trN_Binf,
        map_mul]
      abel)
    (fun c hc => coeff_zero_of_dvd ((dvd_Apm (c + 1) (b + 1)).mul_left _) (by omega))
  have hB : coeff j (Binf (a + 1) (b + 1)) = if j = 0 then Bcoef (a + 1) (b + 1) else 0 := by
    rw [Binf, coeff_C]
  rw [← hB, ← map_add, h]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [M2tinf, coeff_C_mul]

/-- Inner patch: `A₊₋ = -(B^{(z)} D⁻¹) A₋₋`, entrywise at order `z^j`. -/
theorem Apm_eq_sum (j a b : ℕ) :
    coeff j (Apm (a + 1) (b + 1)) =
      -∑ n ∈ range j, Bcoef (a + 1) (n + 1) / (((n + 1 : ℕ)) : ℚ) *
        (if a + n + 2 ≤ j then coeff (j - (a + n + 2)) (Amm (n + 1) (b + 1)) else 0) := by
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  have h := entry_neg_mul (L := Apm) (T := M1tinf) (A := Amm) hN ha hb
    (by rw [fApm hN, fAmm hN, Matrix.mul_neg, neg_neg,
      fin_A5 _ _ _ _ _ (qu_mul_d j _)])
    (fun c hc => by
      rw [M1tinf, mul_assoc]
      exact coeff_zero_of_dvd ((Dvd.intro _ rfl : X ^ (a + 1 + (c + 1)) ∣ _).mul_left _)
        (by omega))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [M1tinf, mul_assoc, coeff_C_mul, coeff_X_pow_mul', show a + 1 + (n + 1) = a + n + 2 by ring]

/-- Inner patch: `A₊₊ = -(B^{(z)} D⁻¹)(A₋₊ + D)`, entrywise at order `z^j`. -/
theorem App_eq_sum (j a b : ℕ) :
    coeff j (App (a + 1) (b + 1)) =
      -∑ n ∈ range j, Bcoef (a + 1) (n + 1) / (((n + 1 : ℕ)) : ℚ) *
        (if a + n + 2 ≤ j then
          coeff (j - (a + n + 2)) (Amp (n + 1) (b + 1) +
            C (((n + 1 : ℕ)) : ℚ) * ione (n + 1) (b + 1)) else 0) := by
  obtain ⟨hN, ha, hb⟩ := trunc_bounds j a b
  have h := entry_neg_mul (L := App) (T := M1tinf)
    (A := fun m n => Amp m n + C ((m : ℕ) : ℚ) * ione m n) hN ha hb
    (by
      have e : trN (max j (max (a + 1) (b + 1))) (fun m n => Amp m n + C ((m : ℕ) : ℚ) * ione m n) =
          trN _ Amp + Dmat _ := by
        refine Matrix.ext fun a b => ?_
        simp only [trN, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_apply, ione]
        by_cases hab : a = b
        · rw [if_pos hab, if_pos (by rw [hab]), mul_one, map_natCast]
        · rw [if_neg hab, if_neg (fun hc => hab (Fin.ext (by omega))), mul_zero]
      rw [e, map_add, fApp hN, fAmp hN, fin_A7 _ _ _ _ _ (qu_mul_d j _) (qz21 j _)])
    (fun c hc => by
      rw [M1tinf, mul_assoc]
      exact coeff_zero_of_dvd ((Dvd.intro _ rfl : X ^ (a + 1 + (c + 1)) ∣ _).mul_left _)
        (by omega))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [M1tinf, mul_assoc, coeff_C_mul, coeff_X_pow_mul', show a + 1 + (n + 1) = a + n + 2 by ring]

end Virasoro.Sphere
