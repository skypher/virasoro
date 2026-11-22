import Virasoro.Sphere.Proofs.Sec3L0Unique
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# The first-order operators of equation (3.3) over a commutative ring

sphere/paper.tex l.559–568.  The operators `∂_{σ_n}`, `∑_n nσ_n∂_{σ_{n+k}}` and
`∑_n nσ_n∂_{σ_n}` on formal series in the `σ_m` with coefficients in a commutative ring `A`
(`ℂ(λ)`, Laurent series in `λ⁻¹`, `ℂ`).  On the coefficient of a monomial `σ^α` the two sums
over `n` are finite: they agree with the sums over `n ≤ B` for any `B` bounding the indices of
the variables of `σ^α`.
-/

namespace Virasoro.Sphere

open Finset

section Ops

variable {A : Type*} [CommRing A]

/-- `∂/∂σ_n`. -/
noncomputable def pdA (n : ℕ) (T : MvPowerSeries ℕ+ A) : MvPowerSeries ℕ+ A :=
  MvPowerSeries.pderiv A n.toPNat' T

/-- `∑_{n≥1} n σ_n ∂_{σ_{n+k}} T`. -/
noncomputable def shiftA (k : ℕ) (T : MvPowerSeries ℕ+ A) : MvPowerSeries ℕ+ A :=
  fun α => ∑ n ∈ α.support,
    ((n : ℕ) : A) * MvPowerSeries.coeff (α - Finsupp.single n 1) (pdA ((n : ℕ) + k) T)

/-- `∑_{n≥1} n σ_n ∂_{σ_n} T`. -/
noncomputable def levelA (T : MvPowerSeries ℕ+ A) : MvPowerSeries ℕ+ A :=
  fun α => ((lvl α : ℕ) : A) * MvPowerSeries.coeff α T

theorem pd_eq_pdA (n : ℕ) (T : MvPowerSeries ℕ+ ℂ) : pd n T = pdA n T := rfl

theorem shiftOp_eq_shiftA (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) : shiftOp k T = shiftA k T := rfl

theorem levelOp_eq_levelA (T : MvPowerSeries ℕ+ ℂ) : levelOp T = levelA T := rfl

theorem coeff_pdA (n : ℕ) (T : MvPowerSeries ℕ+ A) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (pdA n T) =
      MvPowerSeries.coeff (α + Finsupp.single n.toPNat' 1) T * ((α n.toPNat' : A) + 1) :=
  MvPowerSeries.coeff_pderiv T α

theorem coeff_shiftA (k : ℕ) (T : MvPowerSeries ℕ+ A) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (shiftA k T) = ∑ n ∈ α.support,
      ((n : ℕ) : A) * MvPowerSeries.coeff (α - Finsupp.single n 1) (pdA ((n : ℕ) + k) T) := rfl

theorem coeff_levelA (T : MvPowerSeries ℕ+ A) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (levelA T) = ((lvl α : ℕ) : A) * MvPowerSeries.coeff α T := rfl

theorem coeff_X_mulA (i : ℕ+) (φ : MvPowerSeries ℕ+ A) (x : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff x (MvPowerSeries.X i * φ) =
      if i ∈ x.support then MvPowerSeries.coeff (x - Finsupp.single i 1) φ else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
  by_cases h : i ∈ x.support
  · have h1 : 1 ≤ x i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    rw [if_pos h, if_pos (Finsupp.single_le_iff.2 h1)]
  · have h0 : x i = 0 := Finsupp.notMem_support_iff.1 h
    rw [if_neg h, if_neg (mt Finsupp.single_le_iff.1 (by omega))]

theorem sum_Icc_toPNat' {M : Type*} [AddCommMonoid M] (B : ℕ) (s : Finset ℕ+)
    (hs : ∀ j ∈ s, (j : ℕ) ≤ B) (g : ℕ+ → M) :
    ∑ n ∈ Icc 1 B, (if n.toPNat' ∈ s then g n.toPNat' else 0) = ∑ j ∈ s, g j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => n.toPNat') (fun j => (j : ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    exact (Finset.mem_filter.1 hn).2
  · intro j hj
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨j.pos, hs j hj⟩, ?_⟩
    rwa [PNat.coe_toPNat']
  · intro n hn
    exact PNat.toPNat'_coe (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
  · intro j _
    exact PNat.coe_toPNat' j
  · intro n _
    rfl

/-- The coefficient of `σ^α` in `∑_n nσ_n∂_{σ_{n+k}}T` only involves `n ≤ B`. -/
theorem coeff_shiftA_eq (k : ℕ) (T : MvPowerSeries ℕ+ A) (α : ℕ+ →₀ ℕ) (B : ℕ)
    (hB : ∀ j ∈ α.support, (j : ℕ) ≤ B) :
    MvPowerSeries.coeff α (shiftA k T) = MvPowerSeries.coeff α
      (∑ n ∈ Icc 1 B, (n : A) • (MvPowerSeries.X n.toPNat' * pdA (n + k) T)) := by
  rw [coeff_shiftA, map_sum, ← sum_Icc_toPNat' B α.support hB]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : (n.toPNat' : ℕ) = n := PNat.toPNat'_coe (Finset.mem_Icc.1 hn).1
  rw [MvPowerSeries.coeff_smul, coeff_X_mulA, hn1]
  split_ifs <;> simp

/-- The coefficient of `σ^α` in `∑_n nσ_n∂_{σ_n}T` only involves `n ≤ B`. -/
theorem coeff_levelA_eq (T : MvPowerSeries ℕ+ A) (α : ℕ+ →₀ ℕ) (B : ℕ)
    (hB : ∀ j ∈ α.support, (j : ℕ) ≤ B) :
    MvPowerSeries.coeff α (levelA T) = MvPowerSeries.coeff α
      (∑ n ∈ Icc 1 B, (n : A) • (MvPowerSeries.X n.toPNat' * pdA n T)) := by
  have hlvl : ((lvl α : ℕ) : A) = ∑ j ∈ α.support, ((j : ℕ) : A) * (α j : A) := by
    rw [lvl, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [fockWeight, mul_comm]
  rw [coeff_levelA, hlvl, Finset.sum_mul, map_sum, ← sum_Icc_toPNat' B α.support hB]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : (n.toPNat' : ℕ) = n := PNat.toPNat'_coe (Finset.mem_Icc.1 hn).1
  rw [MvPowerSeries.coeff_smul, coeff_X_mulA, hn1]
  split_ifs with h
  · rw [coeff_pdA, sub_add_single h]
    have h1 : 1 ≤ α n.toPNat' := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    have e : (((α - Finsupp.single n.toPNat' 1 : ℕ+ →₀ ℕ) n.toPNat' : ℕ) : A) + 1 =
        (α n.toPNat' : A) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      exact_mod_cast congrArg (Nat.cast (R := A)) (Nat.sub_add_cancel h1)
    rw [e]
    ring
  · simp

theorem support_subset_of_add {β δ α : ℕ+ →₀ ℕ} (h : β + δ = α) : δ.support ⊆ α.support := by
  intro j hj
  rw [Finsupp.mem_support_iff] at hj ⊢
  rw [← h, Finsupp.add_apply]
  omega

/-- If `∂_j G = H ∂_j T` for all `j`, then `∑ nσ_n∂_{n+k} G = H ∑ nσ_n∂_{n+k} T`. -/
theorem shiftA_of_pd (k : ℕ) (G H T : MvPowerSeries ℕ+ A) (h : ∀ j, pdA j G = H * pdA j T) :
    shiftA k G = H * shiftA k T := by
  classical
  ext α
  set B := α.support.sup fun j => (j : ℕ) with hBdef
  have hB : ∀ j ∈ α.support, (j : ℕ) ≤ B := fun j hj =>
    Finset.le_sup (f := fun j : ℕ+ => (j : ℕ)) hj
  rw [coeff_shiftA_eq k G α B hB]
  simp_rw [h]
  have e : ∑ n ∈ Icc 1 B, (n : A) • (MvPowerSeries.X n.toPNat' * (H * pdA (n + k) T)) =
      H * ∑ n ∈ Icc 1 B, (n : A) • (MvPowerSeries.X n.toPNat' * pdA (n + k) T) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_smul_comm, mul_left_comm]
  rw [e, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  rw [coeff_shiftA_eq k T p.2 B fun j hj => hB j (support_subset_of_add hp' hj)]

/-- If `∂_j G = H ∂_j T` for all `j`, then `∑ nσ_n∂_n G = H ∑ nσ_n∂_n T`. -/
theorem levelA_of_pd (G H T : MvPowerSeries ℕ+ A) (h : ∀ j, pdA j G = H * pdA j T) :
    levelA G = H * levelA T := by
  classical
  ext α
  set B := α.support.sup fun j => (j : ℕ) with hBdef
  have hB : ∀ j ∈ α.support, (j : ℕ) ≤ B := fun j hj =>
    Finset.le_sup (f := fun j : ℕ+ => (j : ℕ)) hj
  rw [coeff_levelA_eq G α B hB]
  simp_rw [h]
  have e : ∑ n ∈ Icc 1 B, (n : A) • (MvPowerSeries.X n.toPNat' * (H * pdA n T)) =
      H * ∑ n ∈ Icc 1 B, (n : A) • (MvPowerSeries.X n.toPNat' * pdA n T) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_smul_comm, mul_left_comm]
  rw [e, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  rw [coeff_levelA_eq T p.2 B fun j hj => hB j (support_subset_of_add hp' hj)]

/-! ### Base change -/

variable {A' : Type*} [CommRing A'] (f : A →+* A')

theorem map_pdA (n : ℕ) (T : MvPowerSeries ℕ+ A) :
    MvPowerSeries.map f (pdA n T) = pdA n (MvPowerSeries.map f T) := by
  ext α
  rw [MvPowerSeries.coeff_map, coeff_pdA, coeff_pdA, MvPowerSeries.coeff_map]
  simp

theorem map_shiftA (k : ℕ) (T : MvPowerSeries ℕ+ A) :
    MvPowerSeries.map f (shiftA k T) = shiftA k (MvPowerSeries.map f T) := by
  ext α
  rw [MvPowerSeries.coeff_map, coeff_shiftA, coeff_shiftA, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← map_pdA, MvPowerSeries.coeff_map, map_mul, map_natCast]

theorem map_levelA (T : MvPowerSeries ℕ+ A) :
    MvPowerSeries.map f (levelA T) = levelA (MvPowerSeries.map f T) := by
  ext α
  rw [MvPowerSeries.coeff_map, coeff_levelA, coeff_levelA, MvPowerSeries.coeff_map, map_mul,
    map_natCast]

end Ops

end Virasoro.Sphere
