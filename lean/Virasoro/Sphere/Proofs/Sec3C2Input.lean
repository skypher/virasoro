import Virasoro.Sphere.Proofs.Sec3C2Fstar
import Virasoro.Sphere.Proofs.Sec3C2Current
import Virasoro.Sphere.Proofs.Sec3C2GaussWard
import Virasoro.Sphere.Proofs.Sec3BergmanStep1
import Virasoro.Sphere.Proofs.Sec3SaddlePde2

/-!
# Lemma 3.7, Step 3: the input from Step 1 of Lemma 3.5 (sphere paper)

sphere/paper.tex l.1131–1134.  `√(x(x-1)) α(x) F_2(u)` has only non-negative powers of `x`:
`∮ x^{k-1} √(x(x-1)) α(x) dx · F_2 = 0` for all `k ≥ 1`.  The coefficient of `x^N` in
`x^{k-1}√(x(x-1)) = x^k √(1-1/x)` is `sk k N`; the residue is the sum over the modes `α_N`.
Level by level the sum is finite.  `α(x)F_2 = i√2 ∑_m u_m f_m(x) F_2`, and
`√(x(x-1)) f_m` is the polynomial of `step1_poly`.
-/

namespace Virasoro.Sphere

open MvPolynomial Finset

/-! ### Level parts of a series -/

/-- The level-`i` part of a series in the `u_m` (`0` for `i < 0`). -/
noncomputable def lp (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) : Fock :=
  if 0 ≤ i then ∑ α ∈ (finite_level i.toNat).toFinset, monomial α (MvPowerSeries.coeff α Φ)
  else 0

theorem coeff_lp (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) (γ : ℕ+ →₀ ℕ) :
    coeff γ (lp Φ i) = if (lvl γ : ℤ) = i then MvPowerSeries.coeff γ Φ else 0 := by
  classical
  unfold lp
  by_cases hi : 0 ≤ i
  · rw [if_pos hi, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h : (lvl γ : ℤ) = i
    · rw [if_pos h, if_pos ((mem_level_iff _ _).mpr (by omega))]
    · rw [if_neg h, if_neg fun h' => h (by have := (mem_level_iff _ _).mp h'; omega)]
  · rw [if_neg hi, coeff_zero, if_neg (by omega)]

theorem lp_eq_zero (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ)
    (h : ∀ γ : ℕ+ →₀ ℕ, (lvl γ : ℤ) = i → MvPowerSeries.coeff γ Φ = 0) : lp Φ i = 0 := by
  ext γ
  rw [coeff_lp, coeff_zero]
  split_ifs with h1
  · exact h γ h1
  · rfl

theorem lp_neg_index (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) (hi : i < 0) : lp Φ i = 0 := by
  rw [lp, if_neg (by omega)]

theorem lp_add (Φ Ψ : MvPowerSeries ℕ+ ℂ) (i : ℤ) : lp (Φ + Ψ) i = lp Φ i + lp Ψ i := by
  ext γ
  rw [coeff_add, coeff_lp, coeff_lp, coeff_lp, map_add]
  split_ifs <;> simp

theorem lp_C_mul (c : ℂ) (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) :
    lp (MvPowerSeries.C c * Φ) i = c • lp Φ i := by
  ext γ
  rw [coeff_smul, coeff_lp, coeff_lp, MvPowerSeries.coeff_C_mul, smul_eq_mul]
  split_ifs <;> simp

theorem lp_zero (i : ℤ) : lp 0 i = 0 := lp_eq_zero 0 i fun _ _ => rfl

theorem lp_sum {ι : Type*} (s : Finset ι) (Φ : ι → MvPowerSeries ℕ+ ℂ) (i : ℤ) :
    lp (∑ a ∈ s, Φ a) i = ∑ a ∈ s, lp (Φ a) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lp_add, ih]

theorem dVar_lp (m : ℕ) (hm : 1 ≤ m) (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) :
    dVar m (lp Φ (i + m)) = lp (pdA m Φ) i := by
  ext γ
  have hl : lvl (γ + Finsupp.single m.toPNat' 1) = lvl γ + m := by
    rw [lvl_add, lvl_single, PNat.toPNat'_coe hm]
  show coeff γ (pderiv m.toPNat' (lp Φ (i + m))) = _
  rw [coeff_pderiv, coeff_lp, coeff_lp, coeff_pdA, hl]
  by_cases h : (lvl γ : ℤ) = i
  · rw [if_pos h, if_pos (by push_cast; omega)]
  · rw [if_neg h, if_neg (by push_cast; omega), zero_mul]

theorem uVar_lp (m : ℕ) (hm : 1 ≤ m) (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) :
    (uVar m : Fock) * lp Φ (i - m) = lp (MvPowerSeries.X m.toPNat' * Φ) i := by
  classical
  ext γ
  show coeff γ (X m.toPNat' * lp Φ (i - m)) = _
  rw [MvPolynomial.coeff_X_mul', coeff_lp, coeff_lp, coeff_X_mulA]
  by_cases hs : m.toPNat' ∈ γ.support
  · have hl : lvl γ = lvl (γ - Finsupp.single m.toPNat' 1) + m := by
      have e := congrArg lvl (sub_add_single hs)
      rw [lvl_add, lvl_single, PNat.toPNat'_coe hm] at e
      exact e.symm
    rw [if_pos hs, if_pos hs]
    by_cases h : (lvl γ : ℤ) = i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg hs, if_neg hs]
    simp

/-! ### The current on series -/

/-- The mode `α_N` on series in the `u_m`. -/
noncomputable def alphaS (N : ℤ) (Φ : MvPowerSeries ℕ+ ℂ) : MvPowerSeries ℕ+ ℂ :=
  if 0 < N then MvPowerSeries.C (Complex.I / sqrt2) * pdA N.toNat Φ
  else if N < 0 then MvPowerSeries.C (-(Complex.I * sqrt2 * ((-N).toNat : ℂ))) *
    (MvPowerSeries.X (-N).toNat.toPNat' * Φ)
  else 0

/-- `α_N` lowers the level by `N`. -/
theorem alphaOp_lp (N : ℤ) (Φ : MvPowerSeries ℕ+ ℂ) (i : ℤ) :
    alphaOp N (lp Φ (i + N)) = lp (alphaS N Φ) i := by
  unfold alphaOp alphaS
  rcases lt_trichotomy N 0 with hN | hN | hN
  · rw [if_neg (by omega), if_pos hN, if_neg (by omega), if_pos hN, LinearMap.smul_apply,
      uMul_apply, lp_C_mul]
    have e : i + N = i - ((-N).toNat : ℤ) := by omega
    rw [e, uVar_lp _ (by omega)]
  · subst hN
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), lp_zero]
    rfl
  · rw [if_pos hN, if_pos hN, LinearMap.smul_apply, lp_C_mul]
    have e : i + N = i + (N.toNat : ℤ) := by omega
    rw [e, dVar_lp _ (by omega)]

/-! ### The Gaussian `F_2` -/

/-- `F_2(u) = exp(∑ B_{m,n} u_m u_n)` as a series. -/
noncomputable def F2s : MvPowerSeries ℕ+ ℂ := mexp (gaussExpo 0)

theorem gaussF_eq_lp (N : ℕ) : gaussF 0 N = lp F2s N := by
  ext γ
  rw [coeff_gaussF, coeff_lp, F2s]
  by_cases h : lvl γ = N
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem coeff_linSeries_mul (c : ℕ → ℂ) (F : MvPowerSeries ℕ+ ℂ) (γ : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff γ (linSeries c * F) =
      ∑ m ∈ γ.support, c m * MvPowerSeries.coeff (γ - Finsupp.single m 1) F := by
  classical
  rw [MvPowerSeries.coeff_mul]
  symm
  refine Finset.sum_bij_ne_zero (fun m _ _ => (Finsupp.single m 1, γ - Finsupp.single m 1))
    ?_ ?_ ?_ ?_
  · intro m hm _
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_comm]
    exact sub_add_single hm
  · intro m _ _ m' _ _ h
    have h1 := congrArg Prod.fst h
    simp only at h1
    exact Finsupp.single_left_injective one_ne_zero h1
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only at hp hne
    have hdeg : p1.degree = 1 := by
      by_contra hd
      apply hne
      rw [coeff_eq_apply, linSeries_of_degree_ne c p1 hd, zero_mul]
    obtain ⟨m, rfl⟩ := exists_single_of_degree_one p1 hdeg
    have hp2 : p2 = γ - Finsupp.single m 1 := by
      rw [← hp, add_tsub_cancel_left]
    have hm : m ∈ γ.support := by
      rw [Finsupp.mem_support_iff, ← hp, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    refine ⟨m, hm, ?_, ?_⟩
    · rw [← hp2]
      have h1 := hne
      rwa [coeff_eq_apply, linSeries_single] at h1
    · rw [hp2]
  · intro m _ _
    rw [coeff_eq_apply (linSeries c), linSeries_single]

theorem pdA_F2s (n : ℕ) (hn : 1 ≤ n) : pdA n F2s = ellB n * F2s := by
  have h0 : IsNilpotent (MvPowerSeries.constantCoeff (gaussExpo 0)) := by
    rw [constantCoeff_gaussExpo]
    exact IsNilpotent.zero
  have h1 : pdA n (gaussExpo 0) = ellB n := by
    rw [gaussExpo_eq, map_zero, zero_mul, zero_add, pdA_S0Q n hn]
  rw [F2s, pdA, pderiv_mexp h0, ← pdA, h1, mul_comm]

/-! ### The input -/

/-- The coefficient of `x^N` in `x^{k-1}√(x(x-1)) = x^k √(1 - x^{-1})`, for `N ≤ k`. -/
noncomputable def sk (k : ℕ) (N : ℤ) : ℂ := PowerSeries.coeff ((k : ℤ) - N).toNat sOneC

/-- `√(x(x-1)) f_m(x)` has no negative power of `x` (`step1_poly`): the coefficient of
`x^{-k}`, `k ≥ 1`. -/
theorem step1_coeff (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∑ n ∈ Icc 1 k, sk k n * (Bcoef n m : ℂ) = (m : ℂ) * sk k (-(m : ℤ)) := by
  have h := congrArg (PowerSeries.coeff (k + m)) (step1_poly m)
  have hU1 : PowerSeries.coeff (k + m) ((2 - PowerSeries.X) * Useries m) = 0 := by
    obtain ⟨K, hK⟩ : ∃ K, k + m = K + 1 := ⟨k + m - 1, by omega⟩
    rw [sub_mul, map_sub, hK, PowerSeries.coeff_succ_X_mul, coeff_Useries_of_le (by omega),
      ← map_ofNat (PowerSeries.C (R := ℚ)) 2, PowerSeries.coeff_C_mul,
      coeff_Useries_of_le (by omega)]
    simp
  have hU2 : PowerSeries.coeff (k + m) (PowerSeries.X * Useries (m - 1)) = 0 := by
    obtain ⟨K, hK⟩ : ∃ K, k + m = K + 1 := ⟨k + m - 1, by omega⟩
    rw [hK, PowerSeries.coeff_succ_X_mul, coeff_Useries_of_le (by omega)]
  have hL : PowerSeries.coeff (k + m) (sOne * (PowerSeries.X ^ m * colB m)) =
      ∑ n ∈ Icc 1 k, PowerSeries.coeff (k - n) sOne * Bcoef n m := by
    rw [mul_left_comm, PowerSeries.coeff_X_pow_mul, mul_comm, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (colB m) * PowerSeries.coeff b sOne),
      range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
    rw [colB, PowerSeries.coeff_mk, Bcoef_zero_left, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_mk, mul_comm]
  rw [map_neg, map_sub, hU1, hU2, sub_zero, neg_zero, ← map_ofNat (PowerSeries.C (R := ℚ)) 2,
    PowerSeries.coeff_C_mul, mul_sub, map_sub, hL, ← map_natCast (PowerSeries.C (R := ℚ)) m,
    PowerSeries.coeff_mul_C] at h
  have h2 : ∑ n ∈ Icc 1 k, PowerSeries.coeff (k - n) sOne * Bcoef n m =
      PowerSeries.coeff (k + m) sOne * (m : ℚ) := by
    linarith
  have h3 : ∑ n ∈ Icc 1 k, algebraMap ℚ ℂ (PowerSeries.coeff (k - n) sOne) *
      algebraMap ℚ ℂ (Bcoef n m) =
      algebraMap ℚ ℂ (PowerSeries.coeff (k + m) sOne) * algebraMap ℚ ℂ (m : ℚ) := by
    rw [← map_mul, ← h2, map_sum]
    simp only [map_mul]
  have e0 : ((k : ℤ) - -(m : ℤ)).toNat = k + m := by omega
  have e1 : sk k (-(m : ℤ)) = algebraMap ℚ ℂ (PowerSeries.coeff (k + m) sOne) := by
    rw [sk, e0, sOneC, PowerSeries.coeff_map]
  have e4 : algebraMap ℚ ℂ (m : ℚ) = (m : ℂ) := map_natCast _ _
  rw [e1, mul_comm, ← e4, ← h3]
  refine Finset.sum_congr rfl fun n hn => ?_
  have e : ((k : ℤ) - (n : ℤ)).toNat = k - n := by omega
  rw [sk, e, sOneC, PowerSeries.coeff_map]
  simp

/-- Sums over an interval of integers, split by sign. -/
theorem sum_Icc_int_split {M : Type*} [AddCommMonoid M] (L k : ℕ) (g : ℤ → M) :
    ∑ N ∈ Icc (-(L : ℤ)) k, g N =
      ∑ m ∈ Icc 1 L, g (-(m : ℤ)) + g 0 + ∑ n ∈ Icc 1 k, g n := by
  classical
  have h1 : ∑ m ∈ Icc 1 L, g (-(m : ℤ)) =
      ∑ N ∈ (Icc (-(L : ℤ)) k).filter (fun N => N < 0), g N := by
    refine Finset.sum_nbij' (fun m : ℕ => -(m : ℤ)) (fun N : ℤ => (-N).toNat) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      have := Finset.mem_Icc.1 hm
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
    · intro N hN
      have h := Finset.mem_filter.1 hN
      have := Finset.mem_Icc.1 h.1
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro m _
      simp
    · intro N hN
      have h := Finset.mem_filter.1 hN
      show -(((-N).toNat : ℕ) : ℤ) = N
      omega
    · intro m _
      rfl
  have h2 : ∑ n ∈ Icc 1 k, g (n : ℤ) =
      ∑ N ∈ (Icc (-(L : ℤ)) k).filter (fun N => 0 < N), g N := by
    refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) (fun N : ℤ => N.toNat) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      have := Finset.mem_Icc.1 hn
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
    · intro N hN
      have h := Finset.mem_filter.1 hN
      have := Finset.mem_Icc.1 h.1
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro n _
      simp
    · intro N hN
      have h := Finset.mem_filter.1 hN
      show ((N.toNat : ℕ) : ℤ) = N
      omega
    · intro n _
      rfl
  have h3 : g 0 = ∑ N ∈ (Icc (-(L : ℤ)) k).filter (fun N => N = 0), g N := by
    rw [Finset.filter_eq' , if_pos (Finset.mem_Icc.2 ⟨by omega, by omega⟩), Finset.sum_singleton]
  rw [h1, h2, h3, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun N _ => ?_
  rcases lt_trichotomy N 0 with hN | hN | hN
  · rw [if_pos hN, if_neg (by omega), if_neg (by omega), add_zero, add_zero]
  · rw [if_neg (by omega), if_pos hN, if_neg (by omega), zero_add, add_zero]
  · rw [if_neg (by omega), if_neg (by omega), if_pos hN, zero_add, zero_add]

/-- `∮ x^{k-1} √(x(x-1)) α(x) dx · F_2 = 0` for `k ≥ 1` (sphere/paper.tex l.1131–1134), at
level `j`; the modes with `N < -j` do not contribute. -/
theorem input_residue (k : ℕ) (hk : 1 ≤ k) (j : ℤ) (L : ℕ) (hL : j ≤ L) :
    ∑ N ∈ Icc (-(L : ℤ)) k, sk k N • alphaOp N (lp F2s (j + N)) = 0 := by
  classical
  simp only [alphaOp_lp]
  rw [sum_Icc_int_split]
  have h0 : alphaS 0 F2s = 0 := by
    rw [alphaS, if_neg (by omega), if_neg (by omega)]
  rw [h0, lp_zero, smul_zero, add_zero]
  have e1 : ∀ m ∈ Icc 1 L, sk k (-(m : ℤ)) • lp (alphaS (-(m : ℤ)) F2s) j =
      lp (MvPowerSeries.C (sk k (-(m : ℤ)) * -(Complex.I * sqrt2 * (m : ℂ))) *
        (MvPowerSeries.X m.toPNat' * F2s)) j := by
    intro m hm
    have hm1 := (Finset.mem_Icc.1 hm).1
    rw [alphaS, if_neg (by omega), if_pos (by omega), ← lp_C_mul, ← mul_assoc, ← map_mul]
    have e : (-(-(m : ℤ))).toNat = m := by omega
    rw [e]
  have e2 : ∀ n ∈ Icc 1 k, sk k (n : ℤ) • lp (alphaS (n : ℤ) F2s) j =
      lp (MvPowerSeries.C (sk k (n : ℤ) * (Complex.I / sqrt2)) * (ellB n * F2s)) j := by
    intro n hn
    have hn1 := (Finset.mem_Icc.1 hn).1
    rw [alphaS, if_pos (by omega), ← lp_C_mul, ← mul_assoc, ← map_mul]
    have e : ((n : ℤ)).toNat = n := by omega
    rw [e, pdA_F2s n hn1]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← lp_sum, ← lp_sum, ← lp_add]
  refine lp_eq_zero _ _ fun γ hγ => ?_
  have hsup : ∀ m ∈ γ.support, (m : ℕ) ≤ L := by
    intro m hm
    have e := congrArg lvl (sub_add_single hm)
    rw [lvl_add, lvl_single] at e
    omega
  have c1 : ∀ m ∈ Icc 1 L, MvPowerSeries.coeff γ
      (MvPowerSeries.C (sk k (-(m : ℤ)) * -(Complex.I * sqrt2 * (m : ℂ))) *
        (MvPowerSeries.X m.toPNat' * F2s)) =
      if m.toPNat' ∈ γ.support then
        (fun i : ℕ+ => sk k (-((i : ℕ) : ℤ)) * -(Complex.I * sqrt2 * ((i : ℕ) : ℂ)) *
          MvPowerSeries.coeff (γ - Finsupp.single i 1) F2s) m.toPNat' else 0 := by
    intro m hm
    have hm1 := (Finset.mem_Icc.1 hm).1
    rw [MvPowerSeries.coeff_C_mul, coeff_X_mulA]
    split_ifs
    · simp only [PNat.toPNat'_coe hm1]
    · rw [mul_zero]
  have c2 : ∀ n ∈ Icc 1 k, MvPowerSeries.coeff γ
      (MvPowerSeries.C (sk k (n : ℤ) * (Complex.I / sqrt2)) * (ellB n * F2s)) =
      ∑ i ∈ γ.support, sk k (n : ℤ) * (Complex.I / sqrt2) *
        (((Bcoef n i : ℂ) + (Bcoef i n : ℂ)) *
          MvPowerSeries.coeff (γ - Finsupp.single i 1) F2s) := by
    intro n _
    rw [MvPowerSeries.coeff_C_mul, ellB, coeff_linSeries_mul, Finset.mul_sum]
  rw [map_add, map_sum, map_sum, Finset.sum_congr rfl c1, Finset.sum_congr rfl c2,
    sum_Icc_toPNat' L γ.support hsup (fun i : ℕ+ => sk k (-((i : ℕ) : ℤ)) *
      -(Complex.I * sqrt2 * ((i : ℕ) : ℂ)) * MvPowerSeries.coeff (γ - Finsupp.single i 1) F2s),
    Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi1 : 1 ≤ (i : ℕ) := i.pos
  have hs := step1_coeff k (i : ℕ) hk hi1
  have h2 := sqrt2_mul
  have h3 := sqrt2_ne
  have h4 : Complex.I / sqrt2 = Complex.I * sqrt2 / 2 := by
    rw [div_eq_div_iff h3 two_ne_zero]
    linear_combination (-Complex.I) * h2
  have hsym : ∀ n : ℕ, (Bcoef i n : ℂ) = (Bcoef n i : ℂ) := fun n => by rw [Bcoef_symm]
  simp only [hsym, h4]
  have e3 : ∑ n ∈ Icc 1 k, sk k (n : ℤ) * (Complex.I * sqrt2 / 2) *
      (((Bcoef n i : ℂ) + (Bcoef n i : ℂ)) *
        MvPowerSeries.coeff (γ - Finsupp.single i 1) F2s) =
      Complex.I * sqrt2 * MvPowerSeries.coeff (γ - Finsupp.single i 1) F2s *
        ∑ n ∈ Icc 1 k, sk k (n : ℤ) * (Bcoef n i : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e3, hs]
  ring

end Virasoro.Sphere
