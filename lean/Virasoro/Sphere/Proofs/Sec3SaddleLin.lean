import Virasoro.Sphere.Proofs.Sec3SaddlePd
import Virasoro.Sphere.Proofs.Sec3SaddlePde2b

/-!
# Sphere paper Lemma 3.4(i): the components of `pdeZero k S⁽⁰⁾` (`sphere/paper.tex` l.737–745)

Products of affine-linear series in the `σ_m`, and the coefficient of `σ^α` in
`pdeZero k S⁽⁰⁾` in terms of `A_n` and `B_{m,n}`.

Consumer: `Sec3SaddlePdeAll.lean` (part (i) of `Stmt_lem_saddle`).
-/

namespace Virasoro.Sphere

open Finset

theorem linSeries_of_degree_ne (c : ℕ → ℂ) (α : ℕ+ →₀ ℕ) (h : α.degree ≠ 1) :
    linSeries c α = 0 := by
  rw [linSeries, if_neg h]

theorem coeff_linSeries_mul_of_degree_ne (c c' : ℕ → ℂ) (α : ℕ+ →₀ ℕ) (h : α.degree ≠ 2) :
    MvPowerSeries.coeff α (linSeries c * linSeries c') = 0 := by
  rw [MvPowerSeries.coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  by_cases h1 : p.1.degree = 1
  · by_cases h2 : p.2.degree = 1
    · exfalso
      apply h
      rw [← HasAntidiagonal.mem_antidiagonal.1 hp, map_add, h1, h2]
    · rw [coeff_eq_apply (linSeries c'), linSeries_of_degree_ne c' _ h2, mul_zero]
  · rw [coeff_eq_apply (linSeries c), linSeries_of_degree_ne c _ h1, zero_mul]

theorem pderiv_linSeries (c : ℕ → ℂ) (m : ℕ+) :
    MvPowerSeries.pderiv ℂ m (linSeries c) = MvPowerSeries.C (c m) := by
  ext β
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C]
  by_cases hβ : β = 0
  · subst hβ
    rw [if_pos rfl, zero_add, coeff_eq_apply, linSeries_single]
    simp
  · rw [if_neg hβ, coeff_eq_apply, linSeries_of_degree_ne, zero_mul]
    rw [map_add, Finsupp.degree_single]
    have : β.degree ≠ 0 := fun h => hβ ((Finsupp.degree_eq_zero_iff _).1 h)
    omega

theorem coeff_linSeries_mul_pair (c c' : ℕ → ℂ) (m l : ℕ+) :
    MvPowerSeries.coeff (Finsupp.single l 1 + Finsupp.single m 1) (linSeries c * linSeries c') *
        ((((Finsupp.single l 1 : ℕ+ →₀ ℕ) m : ℕ) : ℂ) + 1) =
      c l * c' m + c' l * c m := by
  rw [← MvPowerSeries.coeff_pderiv, Derivation.leibniz, pderiv_linSeries, pderiv_linSeries,
    smul_eq_mul, smul_eq_mul, map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_mul_C,
    coeff_eq_apply (linSeries c), coeff_eq_apply (linSeries c'), linSeries_single,
    linSeries_single]

theorem coeff_linSeries_mul_ne (c c' : ℕ → ℂ) (m l : ℕ+) (hml : m ≠ l) :
    MvPowerSeries.coeff (Finsupp.single m 1 + Finsupp.single l 1) (linSeries c * linSeries c') =
      c m * c' l + c l * c' m := by
  have h := coeff_linSeries_mul_pair c c' m l
  rw [Finsupp.single_apply, if_neg (Ne.symm hml)] at h
  rw [add_comm]
  simp only [Nat.cast_zero, zero_add, mul_one] at h
  rw [h]
  ring

theorem coeff_linSeries_mul_eq (c c' : ℕ → ℂ) (m : ℕ+) :
    MvPowerSeries.coeff (Finsupp.single m 1 + Finsupp.single m 1) (linSeries c * linSeries c') =
      c m * c' m := by
  have h := coeff_linSeries_mul_pair c c' m m
  rw [Finsupp.single_eq_same] at h
  have h2 : ((1 : ℕ) : ℂ) + 1 = 2 := by norm_num
  rw [h2] at h
  linear_combination (1 / 2 : ℂ) * h

theorem coeff_C_add_lin (a : ℂ) (c : ℕ → ℂ) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (MvPowerSeries.C a + linSeries c) =
      (if α = 0 then a else 0) + linSeries c α := by
  rw [map_add, MvPowerSeries.coeff_C]
  rfl

theorem coeff_affine_mul (a a' : ℂ) (c c' : ℕ → ℂ) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α
        ((MvPowerSeries.C a + linSeries c) * (MvPowerSeries.C a' + linSeries c')) =
      (if α = 0 then a * a' else 0) + a * linSeries c' α + a' * linSeries c α +
        MvPowerSeries.coeff α (linSeries c * linSeries c') := by
  have e : (MvPowerSeries.C a + linSeries c) * (MvPowerSeries.C a' + linSeries c') =
      MvPowerSeries.C (a * a') + MvPowerSeries.C a * linSeries c' +
        MvPowerSeries.C a' * linSeries c + linSeries c * linSeries c' := by
    rw [map_mul]
    ring
  rw [e, map_add, map_add, map_add, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_C_mul]
  rfl

/-- `B_{n,m} + B_{m,n}`, the coefficient of `σ_m` in `∂_{σ_n} S⁽⁰⁾`. -/
noncomputable def cB (n : ℕ) : ℕ → ℂ := fun m => (Bcoef n m : ℂ) + (Bcoef m n : ℂ)

theorem cB_eq (n m : ℕ) : cB n m = 2 * (Bcoef n m : ℂ) := by
  rw [cB, Bcoef_symm m n]
  ring

theorem pd_S0' (n : ℕ) (hn : 1 ≤ n) :
    pd n S0 = MvPowerSeries.C (Acoef n) + linSeries (cB n) := pd_S0 n hn

/-- The coefficient of `σ^α` in `pdeZero k S⁽⁰⁾`. -/
theorem coeff_pdeZero_S0 (k : ℕ) (hk : 1 ≤ k) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (pdeZero k S0) =
      Complex.I * ((if α = 0 then Acoef k else 0) + linSeries (cB k) α) + shiftOp k S0 α
        - levelOp S0 α
        - (1 / 4 : ℂ) * ∑ n ∈ Icc 1 (k - 1),
          ((if α = 0 then Acoef n * Acoef (k - n) else 0) + Acoef n * linSeries (cB (k - n)) α +
            Acoef (k - n) * linSeries (cB n) α +
            MvPowerSeries.coeff α (linSeries (cB n) * linSeries (cB (k - n))))
        - (if α = 0 then 1 else 0) := by
  have h1 : MvPowerSeries.coeff α (pd k S0) =
      (if α = 0 then Acoef k else 0) + linSeries (cB k) α := by
    rw [pd_S0' k hk, coeff_C_add_lin]
  have h2 : ∑ n ∈ Icc 1 (k - 1), MvPowerSeries.coeff α (pd n S0 * pd (k - n) S0) =
      ∑ n ∈ Icc 1 (k - 1),
        ((if α = 0 then Acoef n * Acoef (k - n) else 0) + Acoef n * linSeries (cB (k - n)) α +
          Acoef (k - n) * linSeries (cB n) α +
          MvPowerSeries.coeff α (linSeries (cB n) * linSeries (cB (k - n)))) := by
    refine sum_congr rfl fun n hn => ?_
    have := mem_Icc.1 hn
    rw [pd_S0' n this.1, pd_S0' (k - n) (by omega), coeff_affine_mul]
  rw [pdeZero]
  simp only [map_sub, map_add, map_sum, MvPowerSeries.coeff_smul, smul_eq_mul]
  rw [h1, h2, MvPowerSeries.coeff_one]
  rfl

theorem sum_Icc_reflect (k : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ n ∈ Icc 1 (k - 1), F (k - n) n = ∑ n ∈ Icc 1 (k - 1), F n (k - n) := by
  refine sum_nbij' (fun n => k - n) (fun n => k - n) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    have := mem_Icc.1 hn
    exact mem_Icc.2 (by omega)
  · intro n hn
    have := mem_Icc.1 hn
    exact mem_Icc.2 (by omega)
  · intro n hn
    have := mem_Icc.1 hn
    show k - (k - n) = n
    omega
  · intro n hn
    have := mem_Icc.1 hn
    show k - (k - n) = n
    omega
  · intro n hn
    have := mem_Icc.1 hn
    rw [show k - (k - n) = n by omega]

theorem sum_range_eq_Icc {M : Type*} [AddCommMonoid M] (k : ℕ) (hk : 1 ≤ k) (F : ℕ → M)
    (h0 : F 0 = 0) (hkk : F k = 0) :
    ∑ n ∈ range (k + 1), F n = ∑ n ∈ Icc 1 (k - 1), F n := by
  have hset : range (k + 1) = insert 0 (insert k (Icc 1 (k - 1))) := by
    ext x
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
    sum_insert (by simp only [mem_Icc]; omega), h0, hkk, zero_add, zero_add]

end Virasoro.Sphere
