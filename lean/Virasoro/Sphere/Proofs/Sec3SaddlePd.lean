import Virasoro.Sphere.Proofs.Sec3SaddlePde0

/-!
# Sphere paper Lemma 3.4, the gradient of `S⁽⁰⁾` (`sphere/paper.tex` l.519–525)

`∂_{σ_n} S⁽⁰⁾ = A_n + ∑_m (B_{n,m} + B_{m,n}) σ_m`.

Consumers: the `σ¹`, `σ²` components of `pdeZero k S0` in part (i) of `Stmt_lem_saddle`, and
the saddle-point equations of part (iii).
-/

namespace Virasoro.Sphere

open Finset

theorem exists_single_of_degree_one (α : ℕ+ →₀ ℕ) (h : α.degree = 1) :
    ∃ m, α = Finsupp.single m 1 := by
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.2 hne
  have hm' : 1 ≤ α m := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hm)
  have hle : Finsupp.single m 1 ≤ α := Finsupp.single_le_iff.2 hm'
  have e := add_tsub_cancel_of_le hle
  have hd : (α - Finsupp.single m 1).degree = 0 := by
    have := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single, h] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hd, add_zero] at e
  exact ⟨m, e.symm⟩

theorem coeff_eq_apply (f : MvPowerSeries ℕ+ ℂ) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α f = f α := rfl

theorem linSeries_single (c : ℕ → ℂ) (m : ℕ+) :
    linSeries c (Finsupp.single m 1) = c m := by
  rw [linSeries, if_pos (Finsupp.degree_single m 1),
    Finsupp.support_single _ one_ne_zero, sum_singleton]

/-- The quadratic part of `S⁽⁰⁾` at `σ_m σ_i`. -/
theorem S0_pair (m i : ℕ+) :
    S0 (Finsupp.single m 1 + Finsupp.single i 1) =
      if m = i then (Bcoef m m : ℂ) else (Bcoef m i : ℂ) + (Bcoef i m : ℂ) := by
  have hdeg : (Finsupp.single m 1 + Finsupp.single i 1 : ℕ+ →₀ ℕ).degree = 2 := by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
  rw [S0, if_neg (by rw [hdeg]; norm_num), if_pos hdeg]
  by_cases hmi : m = i
  · subst hmi
    rw [if_pos rfl]
    have hsup : (Finsupp.single m 1 + Finsupp.single m 1 : ℕ+ →₀ ℕ).support = {m} := by
      rw [← Finsupp.single_add]
      exact Finsupp.support_single _ (by norm_num)
    rw [hsup, sum_singleton, sum_singleton, if_pos rfl]
  · rw [if_neg hmi]
    have hsup : (Finsupp.single m 1 + Finsupp.single i 1 : ℕ+ →₀ ℕ).support = {m, i} := by
      ext x
      simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, mem_insert,
        mem_singleton]
      by_cases h1 : m = x <;> by_cases h2 : i = x <;> simp [h1, h2, eq_comm]
    have hmm : (Finsupp.single m 1 + Finsupp.single i 1 : ℕ+ →₀ ℕ) ≠
        Finsupp.single m 1 + Finsupp.single m 1 := fun h => by
      have := DFunLike.congr_fun h i
      simp [Finsupp.single_apply, hmi] at this
    have hii : (Finsupp.single m 1 + Finsupp.single i 1 : ℕ+ →₀ ℕ) ≠
        Finsupp.single i 1 + Finsupp.single i 1 := fun h => by
      have := DFunLike.congr_fun h m
      simp [Finsupp.single_apply, hmi, Ne.symm hmi] at this
    rw [hsup, sum_pair hmi, sum_pair hmi, sum_pair hmi, if_neg hmm, if_pos rfl,
      if_pos (add_comm _ _), if_neg hii]
    ring

/-- `∂_{σ_n} S⁽⁰⁾ = A_n + ∑_m (B_{n,m} + B_{m,n}) σ_m`. -/
theorem pd_S0 (n : ℕ) (hn : 1 ≤ n) :
    pd n S0 = MvPowerSeries.C (Acoef n) +
      linSeries (fun m => (Bcoef n m : ℂ) + (Bcoef m n : ℂ)) := by
  have hi : ((n.toPNat' : ℕ+) : ℕ) = n := by rw [Nat.toPNat'_coe, if_pos (by omega)]
  ext α
  rw [map_add, MvPowerSeries.coeff_C]
  by_cases h0 : α = 0
  · subst h0
    rw [coeff_zero_pd_S0 n hn, if_pos rfl]
    rw [coeff_eq_apply (linSeries _)]
    simp [linSeries]
  rw [if_neg h0, zero_add, pd, MvPowerSeries.coeff_pderiv]
  rw [coeff_eq_apply S0, coeff_eq_apply (linSeries _)]
  by_cases h1 : α.degree = 1
  · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α h1
    rw [S0_pair, linSeries_single, hi]
    by_cases hmi : m = n.toPNat'
    · rw [if_pos hmi, hmi, hi]
      simp
      ring
    · rw [if_neg hmi]
      simp [Finsupp.single_apply, hmi]
      ring
  · have hdeg : (α + Finsupp.single n.toPNat' 1).degree = α.degree + 1 := by
      rw [map_add, Finsupp.degree_single]
    have hpos : α.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff _).1 h)
    rw [S0, if_neg (by rw [hdeg]; omega), if_neg (by rw [hdeg]; omega), zero_mul, linSeries,
      if_neg h1]

end Virasoro.Sphere
