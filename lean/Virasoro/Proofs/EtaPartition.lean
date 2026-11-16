import Virasoro.Block
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Topology.Instances.Int
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Euler coefficients invert the partition numbers

`(∑_j η_j q^j) (∑_k p(k) q^k) = 1`, in the form `∑_{j=0}^{N} η_j p(N-j) = δ_{N,0}`.
The proof uses the product formula for the generating function of partitions and the fact that
the coefficient of `q^j` in `∏_{m≥1} (1 - q^m)` is already attained by the first `j` factors.
-/

namespace Virasoro

open Finset
open scoped PowerSeries.WithPiTopology

/-- The generating function `∑ p(n) q^n` of the partition numbers. -/
noncomputable def partSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℤ)

/-- The Euler product `∏_{m ≥ 1} (1 - q^m)`. -/
noncomputable def eulerSeries : PowerSeries ℤ :=
  ∏' i : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))

theorem partSeries_mul_eulerSeries : partSeries * eulerSeries = 1 := by
  have h1 : partSeries
      = ∏' i : ℕ, ∑' j : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) := by
    have := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (fun _ => True)
    simp only [if_true] at this
    rw [← this, partSeries]
    congr 1
    funext n
    simp [Nat.Partition.restricted]
  have hm : Multipliable fun i : ℕ =>
      ∑' j : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) := by
    have := Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (fun _ => True)
    simpa using this
  rw [h1, eulerSeries,
    ← hm.tprod_mul (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ)]
  have h2 : ∀ i : ℕ, (∑' j : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j))
      * (1 - PowerSeries.X ^ (i + 1)) = 1 := by
    intro i
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  simp_rw [h2]
  exact tprod_one

theorem tail_prod (j : ℕ) (t : Finset ℕ) (ht : ∀ i ∈ t, j ≤ i) :
    ∃ g : PowerSeries ℤ, ∏ i ∈ t, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
      = 1 + PowerSeries.X ^ (j + 1) * g := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨g, hg⟩ := ih fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have haj : j ≤ a := ht a (Finset.mem_insert_self a t)
    refine ⟨g - PowerSeries.X ^ (a - j) * (1 + PowerSeries.X ^ (j + 1) * g), ?_⟩
    rw [Finset.prod_insert ha, hg]
    have e : (PowerSeries.X : PowerSeries ℤ) ^ (a + 1)
        = PowerSeries.X ^ (j + 1) * PowerSeries.X ^ (a - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    ring

theorem coeff_eulerSeries (j : ℕ) :
    PowerSeries.coeff j eulerSeries
      = PowerSeries.coeff j
          (∏ i ∈ Finset.range j, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) := by
  classical
  have hprod := (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
  have h1 : Filter.Tendsto
      (fun s : Finset ℕ => PowerSeries.coeff j
        (∏ i ∈ s, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))))
      Filter.atTop (nhds (PowerSeries.coeff j eulerSeries)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ j).tendsto _).comp hprod
  have h2 : Filter.Tendsto
      (fun s : Finset ℕ => PowerSeries.coeff j
        (∏ i ∈ s, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))))
      Filter.atTop (nhds (PowerSeries.coeff j
        (∏ i ∈ Finset.range j, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))))) := by
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨Finset.range j, fun s hs => ?_⟩
    obtain ⟨g, hg⟩ := tail_prod j (s \ Finset.range j) (fun i hi => by
      rw [Finset.mem_sdiff, Finset.mem_range] at hi
      omega)
    show PowerSeries.coeff j
        (∏ i ∈ Finset.range j, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
      = PowerSeries.coeff j (∏ i ∈ s, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
    rw [← Finset.prod_sdiff hs, hg, add_mul, one_mul, map_add, mul_assoc,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega), add_zero]
  exact tendsto_nhds_unique h1 h2

theorem coeff_eulerSeries_eq_eta (j : ℕ) : PowerSeries.coeff j eulerSeries = eta j := by
  rw [coeff_eulerSeries, eta]
  have e : (∏ i ∈ Finset.range j, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)))
      = ((∏ m ∈ Finset.Icc 1 j, (1 - (Polynomial.X : Polynomial ℤ) ^ m) : Polynomial ℤ) :
          PowerSeries ℤ) := by
    have e2 : ∏ m ∈ Finset.Icc 1 j, (1 - (Polynomial.X : Polynomial ℤ) ^ m)
        = ∏ i ∈ Finset.range j, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)) := by
      refine Finset.prod_nbij' (fun m => m - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        rw [Finset.mem_Icc] at hm
        rw [Finset.mem_range]
        omega
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        omega
      · intro m hm
        rw [Finset.mem_Icc] at hm
        omega
      · intro i _
        omega
      · intro m hm
        rw [Finset.mem_Icc] at hm
        rw [Nat.sub_add_cancel hm.1]
    have e3 : ∀ p : Polynomial ℤ,
        (p : PowerSeries ℤ) = Polynomial.coeToPowerSeries.ringHom p := fun p => rfl
    rw [e2, e3, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [e, Polynomial.coeff_coe]

/-- `∑_{j=0}^{N} η_j p(N - j) = δ_{N,0}`. -/
theorem eta_partition (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), eta j * (Fintype.card (Nat.Partition (N - j)) : ℤ)
      = if N = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff N) partSeries_mul_eulerSeries
  rw [mul_comm, PowerSeries.coeff_mul, PowerSeries.coeff_one,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => PowerSeries.coeff i eulerSeries * PowerSeries.coeff k partSeries)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_eulerSeries_eq_eta, partSeries, PowerSeries.coeff_mk]

end Virasoro
