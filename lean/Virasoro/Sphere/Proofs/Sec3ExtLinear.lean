import Virasoro.Sphere.Proofs.Sec3ExtExpValues
import Virasoro.Sphere.Proofs.Sec3ExtSigma1

/-!
# Sphere paper Lemma 3.6 (sphere/paper.tex l.974–1010): the linear equations

`g(1) = ∑_m c⁺_m σ_m` and `g(-1) = ∑_m c⁻_m σ_m` with `c⁺_m = [p^m] (i/2) p (1-p)^{-3/2}` and
`c⁻_m = [p^m] (-i/2) p (1-p)^{-1/2}` (l.981–990).  For a linear series `g = ∑ c_m σ_m`,
`L_k^{(0)} g` has the `σ⁰`-part `i c_k - ½ ∑_n A_n c_{k-n}` and the `σ_m`-coefficient
`m c_{m+k} - m c_m - ∑_n B_{n,m} c_{k-n}`.  The `σ⁰` identities are the coefficients of
`(i - ½A(p)) C_±(p)`; the `σ¹` identities are the coefficients of the paper's `σ¹`-part
generating functions, proved as rational identities in `(s₁, s₂)` (`Sec3ExtSigma1.lean`:
`sigma1_plus_Icc`, `sigma1_minus_Icc`).
-/

namespace Virasoro.Sphere

open Finset

/-! ### Linear series -/

theorem linSeries_congr {c c' : ℕ → ℂ} (h : ∀ m : ℕ, 1 ≤ m → c m = c' m) :
    linSeries c = linSeries c' := by
  ext α
  rw [coeff_eq_apply, coeff_eq_apply, linSeries, linSeries]
  split_ifs
  · exact sum_congr rfl fun m _ => h m m.pos
  · rfl

theorem pdA_linSeries (c : ℕ → ℂ) (j : ℕ) (hj : 1 ≤ j) :
    pdA j (linSeries c) = MvPowerSeries.C (c j) := by
  rw [pdA, pderiv_linSeries, Nat.toPNat'_coe, if_pos (by omega)]

theorem shiftA_linSeries (c : ℕ → ℂ) (k : ℕ) :
    shiftA k (linSeries c) = linSeries fun m => (m : ℂ) * c (m + k) := by
  ext α
  rw [coeff_shiftA, coeff_eq_apply (linSeries _)]
  by_cases h1 : α.degree = 1
  · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α h1
    rw [linSeries_single, Finsupp.support_single_ne_zero _ one_ne_zero, sum_singleton, tsub_self,
      pdA_linSeries _ _ (by have := m.pos; omega), MvPowerSeries.coeff_zero_C]
  · rw [linSeries_of_degree_ne _ _ h1]
    refine sum_eq_zero fun n hn => ?_
    have hne : α - Finsupp.single n 1 ≠ 0 := by
      intro h0
      apply h1
      have hle : Finsupp.single n 1 ≤ α :=
        Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hn))
      have e := add_tsub_cancel_of_le hle
      rw [h0, add_zero] at e
      rw [← e, Finsupp.degree_single]
    classical
    rw [pdA_linSeries _ _ (by have := n.pos; omega), MvPowerSeries.coeff_C, if_neg hne, mul_zero]

theorem levelA_linSeries (c : ℕ → ℂ) :
    levelA (linSeries c) = linSeries fun m => (m : ℂ) * c m := by
  ext α
  rw [coeff_levelA, coeff_eq_apply, coeff_eq_apply]
  by_cases h1 : α.degree = 1
  · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α h1
    rw [linSeries_single, linSeries_single, lvl, Finsupp.weight_single]
    simp [fockWeight]
  · rw [linSeries_of_degree_ne _ _ h1, linSeries_of_degree_ne _ _ h1, mul_zero]

theorem linSeries_zero (c : ℕ → ℂ) : linSeries c 0 = 0 :=
  linSeries_of_degree_ne c 0 (by simp)

/-- `L_k^{(0)}` on a linear series `∑_m c_m σ_m`: the `σ⁰`-part is
`i c_k - ½ ∑_n A_n c_{k-n}` and the coefficient of `σ_m` is
`m c_{m+k} - m c_m - ∑_n B_{n,m} c_{k-n}`. -/
theorem L0_linSeries (k : ℕ) (hk : 1 ≤ k) (c : ℕ → ℂ) (a0 : ℂ) (a1 : ℕ → ℂ)
    (h0 : Complex.I * c k - (1 / 2) * ∑ n ∈ Icc 1 (k - 1), Acoef n * c (k - n) = a0)
    (h1 : ∀ m : ℕ, 1 ≤ m → (m : ℂ) * c (m + k) - (m : ℂ) * c m -
      ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * c (k - n) = a1 m) :
    L0 k (linSeries c) = MvPowerSeries.C a0 + linSeries a1 := by
  classical
  have hpd : ∀ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) (linSeries c) =
      MvPowerSeries.C (Acoef n * c (k - n)) +
        c (k - n) • linSeries (fun m => (Bcoef n m : ℂ) + (Bcoef m n : ℂ)) := by
    intro n hn
    have hn' := mem_Icc.1 hn
    rw [← pd_eq_pdA, pd_S0 n hn'.1, pdA_linSeries _ _ (by omega), add_mul, ← map_mul,
      mul_comm (linSeries _), ← MvPowerSeries.smul_eq_C_mul]
  rw [L0_eq, pdA_linSeries _ _ hk, shiftA_linSeries, levelA_linSeries, sum_congr rfl hpd]
  ext α
  simp only [map_add, map_sub, map_sum, map_smul, smul_eq_mul, MvPowerSeries.coeff_C,
    coeff_eq_apply (linSeries _)]
  by_cases h1' : α.degree = 1
  · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α h1'
    have hne : (Finsupp.single m 1 : ℕ+ →₀ ℕ) ≠ 0 := by simp
    simp only [if_neg hne, linSeries_single, mul_zero, zero_add]
    have hsum : ∑ n ∈ Icc 1 (k - 1), c (k - n) * ((Bcoef n m : ℂ) + (Bcoef m n : ℂ)) =
        2 * ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * c (k - n) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [Bcoef_symm m n]
      ring
    rw [hsum, ← h1 m m.pos]
    ring
  · simp only [linSeries_of_degree_ne _ _ h1', mul_zero, add_zero, sub_zero]
    by_cases h00 : α = 0
    · simp only [if_pos h00]
      rw [← h0]
    · simp only [if_neg h00, mul_zero, sum_const_zero, sub_zero]

theorem neg_smul_one_sub_linSeries (x : ℂ) (c : ℕ → ℂ) :
    -(x • (1 - linSeries c)) = MvPowerSeries.C (-x) + linSeries fun m => x * c m := by
  classical
  ext α
  simp only [map_neg, map_add, map_sub, map_smul, smul_eq_mul, MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_one, coeff_eq_apply (linSeries _)]
  by_cases h1 : α.degree = 1
  · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α h1
    have hne : (Finsupp.single m 1 : ℕ+ →₀ ℕ) ≠ 0 := by simp
    simp only [if_neg hne, linSeries_single]
    ring
  · simp only [linSeries_of_degree_ne _ _ h1]
    by_cases h00 : α = 0
    · simp only [if_pos h00]
      ring
    · simp only [if_neg h00]
      ring

/-! ### The coefficients of `g(±1)` -/

/-- `c⁺_m = [p^m] (i/2) p (1-p)^{-3/2} = i m h_m`. -/
noncomputable def cPlus (m : ℕ) : ℂ := Complex.I * (m : ℂ) * (halfBinom m : ℂ)

/-- `c⁻_m = [p^m] (-i/2) p (1-p)^{-1/2} = -(i/2) h_{m-1}`. -/
noncomputable def cMinus (m : ℕ) : ℂ := -(Complex.I / 2) * (halfBinom (m - 1) : ℂ)

theorem cMinus_eq (j : ℕ) (hj : 1 ≤ j) : cMinus j = Complex.I * (dM j : ℂ) := by
  rw [cMinus, dM, if_neg (by omega)]
  push_cast
  ring

theorem gAt_one_eq : gAt 1 = linSeries cPlus :=
  linSeries_congr fun m _ => gAt_one_coeff m

theorem gAt_neg_one_eq : gAt (-1) = linSeries cMinus := by
  refine linSeries_congr fun m hm => ?_
  have hc : ∑ n ∈ Icc 1 m, (n : ℂ) * (-1 : ℂ) ^ n * tcoef n m =
      -(halfBinom (m - 1) : ℂ) / 4 := by
    simp only [tcoef_eq, mul_assoc]
    exact_mod_cast sum_n_alt_psi m hm
  rw [hc, cMinus]
  ring

/-! ### Identities for `h_n = [p^n](1-p)^{-1/2}` -/

theorem halfBinom_zero' : halfBinom 0 = 1 := by simp [halfBinom, gbinom]

theorem range_succ_eq_insert_Icc (k : ℕ) : range (k + 1) = insert 0 (Icc 1 k) := by
  ext x
  simp only [mem_range, mem_insert, mem_Icc]
  omega

/-- `∑_{n=1}^{k-1} (k-n) h_n h_{k-n} = (k/2)(1 - 2h_k)`. -/
theorem sum_weighted_hh (k : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Icc 1 (k - 1), halfBinom n * (((k - n : ℕ) : ℚ) * halfBinom (k - n)) =
      (k : ℚ) / 2 * (1 - 2 * halfBinom k) := by
  have h1 := sum_halfBinom_inner k hk
  have h2 := sum_reflect k fun a b => halfBinom a * ((b : ℚ) * halfBinom b)
  have h3 : ∑ n ∈ Icc 1 (k - 1), halfBinom n * (((k - n : ℕ) : ℚ) * halfBinom (k - n)) +
      ∑ n ∈ Icc 1 (k - 1), halfBinom (k - n) * ((n : ℚ) * halfBinom n) =
      (k : ℚ) * ∑ n ∈ Icc 1 (k - 1), halfBinom n * halfBinom (k - n) := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn' := mem_Icc.1 hn
    rw [Nat.cast_sub (by omega)]
    ring
  rw [← h2] at h3
  linear_combination (1 / 2 : ℚ) * h3 + ((k : ℚ) / 2) * h1

/-- `∑_{n=0}^{k} h_n h_{k-n} = 1` with the term `n = 0` split off. -/
theorem sum_hh_Icc (k : ℕ) :
    halfBinom k + ∑ n ∈ Icc 1 k, halfBinom n * halfBinom (k - n) = 1 := by
  have h := sum_halfBinom_mul k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => halfBinom i * halfBinom j) k,
    range_succ_eq_insert_Icc, sum_insert (by simp), Nat.sub_zero, halfBinom_zero', one_mul] at h
  exact h

/-! ### The linear equations -/

theorem L0_gAt_one (k : ℕ) (hk : 1 ≤ k) :
    L0 k (gAt 1) = -(((k : ℂ) / 2) • (1 - gAt 1)) := by
  rw [gAt_one_eq, neg_smul_one_sub_linSeries]
  refine L0_linSeries k hk cPlus _ _ ?_ fun m hm => ?_
  · have hq := sum_weighted_hh k hk
    have hc : ∑ n ∈ Icc 1 (k - 1), (halfBinom n : ℂ) *
        (((k - n : ℕ) : ℂ) * (halfBinom (k - n) : ℂ)) =
        (k : ℂ) / 2 * (1 - 2 * (halfBinom k : ℂ)) := by
      have h' := congrArg (fun x : ℚ => (x : ℂ)) hq
      push_cast at h'
      exact h'
    have e : ∑ n ∈ Icc 1 (k - 1), Acoef n * cPlus (k - n) =
        2 * ∑ n ∈ Icc 1 (k - 1), (halfBinom n : ℂ) *
          (((k - n : ℕ) : ℂ) * (halfBinom (k - n) : ℂ)) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [Acoef, cPlus]
      linear_combination (-2 * (halfBinom n : ℂ) * ((k - n : ℕ) : ℂ) * (halfBinom (k - n) : ℂ)) *
        Complex.I_mul_I
    rw [e, hc, cPlus]
    linear_combination ((k : ℂ) * (halfBinom k : ℂ)) * Complex.I_mul_I
  · have hq := sigma1_plus_Icc k m hk hm
    have hc : (m : ℂ) * ((((k + m : ℕ) : ℂ) * (halfBinom (k + m) : ℂ)) -
        (m : ℂ) * (halfBinom m : ℂ)) -
        ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * (((k - n : ℕ) : ℂ) * (halfBinom (k - n) : ℂ)) =
        (k : ℂ) / 2 * ((m : ℂ) * (halfBinom m : ℂ)) := by
      have h' := congrArg (fun x : ℚ => (x : ℂ)) hq
      push_cast at h' ⊢
      linear_combination h'
    have e : ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * cPlus (k - n) =
        Complex.I * ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) *
          (((k - n : ℕ) : ℂ) * (halfBinom (k - n) : ℂ)) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [cPlus]
      ring
    rw [e, add_comm m k, cPlus, cPlus]
    linear_combination Complex.I * hc

theorem L0_gAt_neg_one (k : ℕ) (hk : 1 ≤ k) :
    L0 k (gAt (-1)) = (1 / 2 : ℂ) • (1 - gAt (-1)) := by
  have hR : (1 / 2 : ℂ) • (1 - gAt (-1)) = -((-(1 / 2) : ℂ) • (1 - gAt (-1))) := by
    rw [neg_smul, neg_neg]
  rw [hR, gAt_neg_one_eq, neg_smul_one_sub_linSeries]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine L0_linSeries (k' + 1) hk cMinus _ _ ?_ fun m hm => ?_
  · have hq := sum_hh_Icc k'
    have hc : (halfBinom k' : ℂ) +
        ∑ n ∈ Icc 1 k', (halfBinom n : ℂ) * (halfBinom (k' - n) : ℂ) = 1 := by exact_mod_cast hq
    have e : ∑ n ∈ Icc 1 (k' + 1 - 1), Acoef n * cMinus (k' + 1 - n) =
        -∑ n ∈ Icc 1 k', (halfBinom n : ℂ) * (halfBinom (k' - n) : ℂ) := by
      rw [Nat.add_sub_cancel, ← sum_neg_distrib]
      refine sum_congr rfl fun n hn => ?_
      have hn' := mem_Icc.1 hn
      rw [Acoef, cMinus, show k' + 1 - n - 1 = k' - n by omega]
      linear_combination ((halfBinom n : ℂ) * (halfBinom (k' - n) : ℂ)) * Complex.I_mul_I
    rw [e, cMinus, Nat.add_sub_cancel]
    linear_combination (-(1 / 2 : ℂ) * (halfBinom k' : ℂ)) * Complex.I_mul_I + (1 / 2 : ℂ) * hc
  · have hq := sigma1_minus_Icc (k' + 1) m hk hm
    have hc : (m : ℂ) * ((dM (k' + 1 + m) : ℂ) - (dM m : ℂ)) -
        ∑ n ∈ Icc 1 (k' + 1 - 1), (Bcoef n m : ℂ) * (dM (k' + 1 - n) : ℂ) =
        -(1 / 2) * (dM m : ℂ) := by
      have h' := congrArg (fun x : ℚ => (x : ℂ)) hq
      push_cast at h' ⊢
      linear_combination h'
    have e : ∑ n ∈ Icc 1 (k' + 1 - 1), (Bcoef n m : ℂ) * cMinus (k' + 1 - n) =
        Complex.I * ∑ n ∈ Icc 1 (k' + 1 - 1), (Bcoef n m : ℂ) * (dM (k' + 1 - n) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn' := mem_Icc.1 hn
      rw [cMinus_eq (k' + 1 - n) (by omega)]
      ring
    rw [e, add_comm m (k' + 1), cMinus_eq (k' + 1 + m) (by omega), cMinus_eq m hm]
    linear_combination Complex.I * hc

/-- The linear equations of sphere/paper.tex l.981–1006. -/
theorem sub_ext_linear : Stmt_sub_ext_linear :=
  fun k hk => ⟨L0_gAt_one k hk, L0_gAt_neg_one k hk⟩

/-- Lemma 3.6 (sphere/paper.tex l.974–1010).
Paper label: lem:ext-exponents -/
theorem lem_ext_exponents_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_lem_ext_exponents :=
  lem_ext_exponents_of_linear hF hK hJ1 hJ2 sub_ext_linear

example (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) : Stmt_lem_ext_exponents :=
  lem_ext_exponents_of_cited hF hK hJ1 hJ2

end Virasoro.Sphere
