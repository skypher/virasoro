import Virasoro.Sphere.Proofs.Sec3SaddleLin

/-!
# Sphere paper Lemma 3.4(i) (`sphere/paper.tex` l.716–718, proof l.737–747)

`pdeZero k S⁽⁰⁾ = 0` for every `k ≥ 1`: the components of degree `0`, `1`, `2` in `σ` are the
three identities of l.739–745, and `pdeZero k S⁽⁰⁾` has no component of degree `≥ 3` because
`S⁽⁰⁾` is quadratic.

Consumer: part (i) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

/-- The `σ¹` identity in the form used below. -/
theorem sigma1_C (k m : ℕ) (hk : 1 ≤ k) :
    (Bcoef k m : ℂ) + ∑ n ∈ Icc 1 (k - 1), (halfBinom n : ℂ) * (Bcoef (k - n) m : ℂ) =
      (m : ℂ) * ((halfBinom (k + m) : ℂ) - (halfBinom m : ℂ)) := by
  have h := sum_halfBinom_Bcoef k m
  have hset : range (k + 1) = insert 0 (insert k (Icc 1 (k - 1))) := by
    ext x
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have h0 : halfBinom 0 = 1 := by simp [halfBinom, gbinom]
  rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
    sum_insert (by simp only [mem_Icc]; omega), Nat.sub_zero, Nat.sub_self, h0,
    Bcoef_zero_left, mul_zero, zero_add, one_mul] at h
  exact_mod_cast h

/-- The `σ²` identity in the form used below. -/
theorem sigma2_C (k m l : ℕ) (hk : 1 ≤ k) :
    (m : ℂ) * ((Bcoef (k + m) l : ℂ) - (Bcoef m l : ℂ)) +
        (l : ℂ) * ((Bcoef (k + l) m : ℂ) - (Bcoef m l : ℂ)) =
      ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * (Bcoef (k - n) l : ℂ) := by
  have h := Bcoef_star k m l hk
  rw [sum_range_eq_Icc k hk (fun n => Bcoef n m * Bcoef (k - n) l)
    (by simp only [Bcoef_zero_left, zero_mul])
    (by simp only [Nat.sub_self, Bcoef_zero_left, mul_zero])] at h
  exact_mod_cast h

theorem S0_single (m : ℕ+) : S0 (Finsupp.single m 1) = Acoef m := by
  rw [S0, if_pos (Finsupp.degree_single m 1), Finsupp.support_single_ne_zero _ one_ne_zero,
    sum_singleton]

/-- The `σ¹` component. -/
theorem coeff_single_pdeZero_S0 (k : ℕ) (hk : 1 ≤ k) (m : ℕ+) :
    MvPowerSeries.coeff (Finsupp.single m 1) (pdeZero k S0) = 0 := by
  rw [coeff_pdeZero_S0 k hk]
  have hne : (Finsupp.single m 1 : ℕ+ →₀ ℕ) ≠ 0 := by simp
  have hshift : shiftOp k S0 (Finsupp.single m 1) = ((m : ℕ) : ℂ) * Acoef ((m : ℕ) + k) := by
    rw [shiftOp, Finsupp.support_single_ne_zero _ one_ne_zero, sum_singleton, tsub_self,
      coeff_zero_pd_S0 _ (by omega)]
  have hlevel : levelOp S0 (Finsupp.single m 1) = ((m : ℕ) : ℂ) * Acoef m := by
    rw [levelOp, Finsupp.weight_single, S0_single]
    simp [fockWeight]
  have hprod : ∀ n, MvPowerSeries.coeff (Finsupp.single m 1)
      (linSeries (cB n) * linSeries (cB (k - n))) = 0 := fun n =>
    coeff_linSeries_mul_of_degree_ne _ _ _ (by rw [Finsupp.degree_single]; norm_num)
  simp only [if_neg hne, hshift, hlevel, hprod, linSeries_single, zero_add, add_zero, sub_zero]
  have hsum : ∑ n ∈ Icc 1 (k - 1), (Acoef n * cB (k - n) m + Acoef (k - n) * cB n m) =
      -8 * Complex.I * ∑ n ∈ Icc 1 (k - 1), (halfBinom n : ℂ) * (Bcoef (k - n) m : ℂ) := by
    rw [sum_add_distrib, sum_Icc_reflect k (fun a b => Acoef a * cB b m), mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [cB_eq, Acoef]
    ring
  rw [hsum, cB_eq, Acoef, Acoef, add_comm (m : ℕ) k]
  linear_combination (2 * Complex.I) * sigma1_C k m hk

/-- The components of degree `≥ 3`. -/
theorem coeff_pdeZero_S0_of_three_le (k : ℕ) (hk : 1 ≤ k) (α : ℕ+ →₀ ℕ) (h : 3 ≤ α.degree) :
    MvPowerSeries.coeff α (pdeZero k S0) = 0 := by
  rw [coeff_pdeZero_S0 k hk]
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  have hlin : ∀ c, linSeries c α = 0 := fun c => linSeries_of_degree_ne c α (by omega)
  have hprod : ∀ n, MvPowerSeries.coeff α (linSeries (cB n) * linSeries (cB (k - n))) = 0 :=
    fun n => coeff_linSeries_mul_of_degree_ne _ _ _ (by omega)
  have hshift : shiftOp k S0 α = 0 := by
    rw [shiftOp]
    refine sum_eq_zero fun n hn => ?_
    have hle : Finsupp.single n 1 ≤ α :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hn))
    have hd : (α - Finsupp.single n 1).degree + 1 = α.degree := by
      have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.degree_single] at this
      exact this
    have hne' : α - Finsupp.single n 1 ≠ 0 := by
      intro h0
      rw [h0] at hd
      simp at hd
      omega
    rw [pd_S0' _ (by have := n.pos; omega), coeff_C_add_lin, if_neg hne',
      linSeries_of_degree_ne _ _ (by omega), add_zero, mul_zero]
  have hlevel : levelOp S0 α = 0 := by
    rw [levelOp, S0, if_neg (by omega), if_neg (by omega), mul_zero]
  simp only [if_neg hne, hlin, hprod, hshift, hlevel, mul_zero, add_zero, sum_const_zero,
    sub_zero]

theorem exists_pair_of_degree_two (α : ℕ+ →₀ ℕ) (h : α.degree = 2) :
    ∃ m l, α = Finsupp.single m 1 + Finsupp.single l 1 := by
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.2 hne
  have hle : Finsupp.single m 1 ≤ α :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hm))
  have e := tsub_add_cancel_of_le hle
  have hd : (α - Finsupp.single m 1).degree = 1 := by
    have := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single, h] at this
    omega
  obtain ⟨l, hl⟩ := exists_single_of_degree_one _ hd
  exact ⟨m, l, by rw [← e, hl, add_comm]⟩

/-- The `σ_m²` component. -/
theorem coeff_pair_eq_pdeZero_S0 (k : ℕ) (hk : 1 ≤ k) (m : ℕ+) :
    MvPowerSeries.coeff (Finsupp.single m 1 + Finsupp.single m 1) (pdeZero k S0) = 0 := by
  rw [coeff_pdeZero_S0 k hk]
  have hdeg : (Finsupp.single m 1 + Finsupp.single m 1 : ℕ+ →₀ ℕ).degree = 2 := by
    rw [map_add, Finsupp.degree_single]
  have hne : (Finsupp.single m 1 + Finsupp.single m 1 : ℕ+ →₀ ℕ) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  have hlin : ∀ c, linSeries c (Finsupp.single m 1 + Finsupp.single m 1) = 0 := fun c =>
    linSeries_of_degree_ne c _ (by omega)
  have hsupp : (Finsupp.single m 1 + Finsupp.single m 1 : ℕ+ →₀ ℕ).support = {m} := by
    rw [← Finsupp.single_add]
    exact Finsupp.support_single_ne_zero _ (by norm_num)
  have hshift : shiftOp k S0 (Finsupp.single m 1 + Finsupp.single m 1) =
      ((m : ℕ) : ℂ) * cB ((m : ℕ) + k) m := by
    rw [shiftOp, hsupp, sum_singleton, add_tsub_cancel_right, pd_S0' _ (by omega),
      coeff_C_add_lin, if_neg (by simp), zero_add, linSeries_single]
  have hlevel : levelOp S0 (Finsupp.single m 1 + Finsupp.single m 1) =
      (((m : ℕ) : ℂ) + ((m : ℕ) : ℂ)) * (Bcoef m m : ℂ) := by
    rw [levelOp, map_add, Finsupp.weight_single, S0_pair, if_pos rfl]
    simp [fockWeight]
  have hprod : ∀ n, MvPowerSeries.coeff (Finsupp.single m 1 + Finsupp.single m 1)
      (linSeries (cB n) * linSeries (cB (k - n))) = cB n m * cB (k - n) m := fun n =>
    coeff_linSeries_mul_eq _ _ m
  simp only [if_neg hne, hlin, hprod, hshift, hlevel, mul_zero, add_zero, zero_add, sub_zero]
  have hsum : ∑ n ∈ Icc 1 (k - 1), cB n m * cB (k - n) m =
      4 * ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * (Bcoef (k - n) m : ℂ) := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [cB_eq, cB_eq]
    ring
  rw [hsum, cB_eq, ← sigma2_C k m m hk, add_comm (m : ℕ) k]
  ring

/-- The `σ_m σ_l` component, `m ≠ l`. -/
theorem coeff_pair_ne_pdeZero_S0 (k : ℕ) (hk : 1 ≤ k) (m l : ℕ+) (hml : m ≠ l) :
    MvPowerSeries.coeff (Finsupp.single m 1 + Finsupp.single l 1) (pdeZero k S0) = 0 := by
  rw [coeff_pdeZero_S0 k hk]
  have hdeg : (Finsupp.single m 1 + Finsupp.single l 1 : ℕ+ →₀ ℕ).degree = 2 := by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
  have hne : (Finsupp.single m 1 + Finsupp.single l 1 : ℕ+ →₀ ℕ) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  have hlin : ∀ c, linSeries c (Finsupp.single m 1 + Finsupp.single l 1) = 0 := fun c =>
    linSeries_of_degree_ne c _ (by omega)
  have hsupp : (Finsupp.single m 1 + Finsupp.single l 1 : ℕ+ →₀ ℕ).support = {m, l} := by
    ext x
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, mem_insert,
      mem_singleton]
    by_cases h1 : m = x <;> by_cases h2 : l = x <;> simp [h1, h2, eq_comm]
  have hshift : shiftOp k S0 (Finsupp.single m 1 + Finsupp.single l 1) =
      ((m : ℕ) : ℂ) * cB ((m : ℕ) + k) l + ((l : ℕ) : ℂ) * cB ((l : ℕ) + k) m := by
    rw [shiftOp, hsupp, sum_pair hml, add_tsub_cancel_left, add_tsub_cancel_right,
      pd_S0' _ (by omega), pd_S0' _ (by omega), coeff_C_add_lin, coeff_C_add_lin,
      if_neg (by simp), if_neg (by simp), zero_add, zero_add, linSeries_single, linSeries_single]
  have hlevel : levelOp S0 (Finsupp.single m 1 + Finsupp.single l 1) =
      (((m : ℕ) : ℂ) + ((l : ℕ) : ℂ)) * ((Bcoef m l : ℂ) + (Bcoef l m : ℂ)) := by
    rw [levelOp, map_add, Finsupp.weight_single, Finsupp.weight_single, S0_pair, if_neg hml]
    simp [fockWeight]
  have hprod : ∀ n, MvPowerSeries.coeff (Finsupp.single m 1 + Finsupp.single l 1)
      (linSeries (cB n) * linSeries (cB (k - n))) =
        cB n m * cB (k - n) l + cB n l * cB (k - n) m := fun n =>
    coeff_linSeries_mul_ne _ _ m l hml
  simp only [if_neg hne, hlin, hprod, hshift, hlevel, mul_zero, add_zero, zero_add, sub_zero]
  have hsum : ∑ n ∈ Icc 1 (k - 1), (cB n m * cB (k - n) l + cB n l * cB (k - n) m) =
      4 * ∑ n ∈ Icc 1 (k - 1), (Bcoef n m : ℂ) * (Bcoef (k - n) l : ℂ) +
        4 * ∑ n ∈ Icc 1 (k - 1), (Bcoef n l : ℂ) * (Bcoef (k - n) m : ℂ) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [cB_eq, cB_eq, cB_eq, cB_eq]
    ring
  rw [hsum, cB_eq, cB_eq, ← sigma2_C k m l hk, ← sigma2_C k l m hk, add_comm (m : ℕ) k,
    add_comm (l : ℕ) k, Bcoef_symm (l : ℕ) (m : ℕ)]
  ring

/-- Lemma 3.4(i), first claim: the functions (3.4) solve the order-`λ⁰` equation of (3.3). -/
theorem pdeZero_S0 (k : ℕ) (hk : 1 ≤ k) : pdeZero k S0 = 0 := by
  ext α
  rw [map_zero]
  rcases Nat.lt_or_ge α.degree 3 with h | h
  · have h0 : α.degree = 0 ∨ α.degree = 1 ∨ α.degree = 2 := by omega
    rcases h0 with hd | hd | hd
    · have : α = 0 := (Finsupp.degree_eq_zero_iff _).1 hd
      subst this
      exact coeff_zero_pdeZero_S0 k hk
    · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α hd
      exact coeff_single_pdeZero_S0 k hk m
    · obtain ⟨m, l, rfl⟩ := exists_pair_of_degree_two α hd
      by_cases hml : m = l
      · subst hml
        exact coeff_pair_eq_pdeZero_S0 k hk m
      · exact coeff_pair_ne_pdeZero_S0 k hk m l hml
  · exact coeff_pdeZero_S0_of_three_le k hk α h

end Virasoro.Sphere
