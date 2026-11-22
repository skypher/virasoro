import Virasoro.Sphere.Proofs.Sec3LamRing
import Virasoro.Sphere.Proofs.Sec3LamOps
import Virasoro.Sphere.Saddle

/-!
# The Ward equations for the formal series `F = ∑_m F_m` (sphere paper Lemma 3.3(i))

sphere/paper.tex l.559–560: the Ward equations `l_k F = (l_0 + kΔ₂ - Δ₁)F`, `k ≥ 1`, as
identities of formal series in the `u_m`, with the operators (3.2) acting coefficient by
coefficient.
-/

namespace Virasoro.Sphere

open Finset

section Coeff

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The coefficient of `u^γ` in `∑_{n ≤ B_α} n u_n ∂_{u_{n+k}} u^α`. -/
theorem coeff_shift_monomial (k : ℕ) (α γ : ℕ+ →₀ ℕ) :
    MvPolynomial.coeff γ (∑ n ∈ Icc 1 (α.support.sup fun m => (m : ℕ)),
      (n : R) • (MvPolynomial.X n.toPNat' *
        MvPolynomial.pderiv (n + k).toPNat' (MvPolynomial.monomial α (1 : R)))) =
    ∑ j ∈ γ.support, ((j : ℕ) : R) * MvPolynomial.coeff (γ - Finsupp.single j 1)
      (MvPolynomial.pderiv ((j : ℕ) + k).toPNat' (MvPolynomial.monomial α (1 : R))) := by
  classical
  set Bα := α.support.sup fun m => (m : ℕ) with hBα
  set B := max Bα (γ.support.sup fun m => (m : ℕ)) with hB
  have hext : ∑ n ∈ Icc 1 Bα, (n : R) • (MvPolynomial.X n.toPNat' *
        MvPolynomial.pderiv (n + k).toPNat' (MvPolynomial.monomial α (1 : R))) =
      ∑ n ∈ Icc 1 B, (n : R) • (MvPolynomial.X n.toPNat' *
        MvPolynomial.pderiv (n + k).toPNat' (MvPolynomial.monomial α (1 : R))) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left _ _)) fun n hn hn' => ?_
    have hn1 := (Finset.mem_Icc.1 hn).1
    have hgt : Bα < n := by
      by_contra hle
      exact hn' (Finset.mem_Icc.2 ⟨hn1, not_lt.1 hle⟩)
    have h0 : α (n + k).toPNat' = 0 := by
      by_contra hne
      have hmem : (n + k).toPNat' ∈ α.support := Finsupp.mem_support_iff.2 hne
      have hle := Finset.le_sup (f := fun m : ℕ+ => (m : ℕ)) hmem
      have hc : ((n + k).toPNat' : ℕ) = n + k := PNat.toPNat'_coe (by omega)
      rw [← hBα] at hle
      simp only [hc] at hle
      omega
    rw [MvPolynomial.pderiv_monomial, h0]
    simp
  rw [hext, MvPolynomial.coeff_sum, ← sum_Icc_toPNat' B γ.support fun j hj =>
    le_trans (Finset.le_sup (f := fun m : ℕ+ => (m : ℕ)) hj) (le_max_right _ _)]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : (n.toPNat' : ℕ) = n := PNat.toPNat'_coe (Finset.mem_Icc.1 hn).1
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X_mul', hn1]
  split_ifs <;> simp

/-- The coefficients of `l_k f`, `k ≥ 1`. -/
theorem coeff_ffOpR_pos (μ lam : R) (k : ℕ) (hk : 1 ≤ k) (f : MvPolynomial ℕ+ R)
    (γ : ℕ+ →₀ ℕ) :
    MvPolynomial.coeff γ (ffOpR μ lam (k : ℤ) f) =
      ∑ j ∈ γ.support, ((j : ℕ) : R) * MvPolynomial.coeff (γ - Finsupp.single j 1)
        (MvPolynomial.pderiv ((j : ℕ) + k).toPNat' f)
      - algebraMap ℂ R (1 / 4) * ∑ n ∈ Icc 1 (k - 1),
          MvPolynomial.coeff γ (MvPolynomial.pderiv n.toPNat'
            (MvPolynomial.pderiv (k - n).toPNat' f))
      + (μ * (k : R) + algebraMap ℂ R Complex.I * lam) *
          MvPolynomial.coeff γ (MvPolynomial.pderiv k.toPNat' f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial α r =>
    have hm : MvPolynomial.monomial α r = r • MvPolynomial.monomial α (1 : R) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have h0 : (k : ℤ) ≠ 0 := by omega
    have h1 : (0 : ℤ) < k := by omega
    rw [ffOpR_monomial, MvPolynomial.coeff_smul, hm]
    simp only [Derivation.map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    unfold ffOpMonoR
    simp only [if_neg h0, if_pos h1, Int.toNat_natCast, MvPolynomial.coeff_add,
      MvPolynomial.coeff_sub, coeff_shift_monomial, MvPolynomial.coeff_C_mul]
    rw [← algebraMap_smul R (1 / 4 : ℂ), MvPolynomial.coeff_smul, MvPolynomial.coeff_sum,
      smul_eq_mul]
    simp only [mul_add, mul_sub, Finset.mul_sum]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, hp, hq, Finset.sum_add_distrib, mul_add]
    ring

/-- The coefficients of `l_0 f`. -/
theorem coeff_ffOpR_zero (μ lam : R) (f : MvPolynomial ℕ+ R) (γ : ℕ+ →₀ ℕ) :
    MvPolynomial.coeff γ (ffOpR μ lam 0 f) =
      (((lvl γ : ℕ) : R) + (lam ^ 2 + μ ^ 2)) * MvPolynomial.coeff γ f := by
  induction f using MvPolynomial.induction_on' with
  | monomial α r =>
    have hm : MvPolynomial.monomial α r = r • MvPolynomial.monomial α (1 : R) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [ffOpR_monomial, MvPolynomial.coeff_smul, hm, MvPolynomial.coeff_smul]
    unfold ffOpMonoR
    simp only [if_true, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]
    have h := coeff_shift_monomial (R := R) 0 α γ
    simp only [add_zero] at h
    rw [h]
    have hl : ∑ j ∈ γ.support, ((j : ℕ) : R) * MvPolynomial.coeff (γ - Finsupp.single j 1)
        (MvPolynomial.pderiv (j : ℕ).toPNat' (MvPolynomial.monomial α (1 : R))) =
        ((lvl γ : ℕ) : R) * MvPolynomial.coeff γ (MvPolynomial.monomial α (1 : R)) := by
      have hlvl : ((lvl γ : ℕ) : R) = ∑ j ∈ γ.support, ((j : ℕ) : R) * (γ j : R) := by
        rw [lvl, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [fockWeight, mul_comm]
      rw [hlvl, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [PNat.coe_toPNat', MvPolynomial.coeff_pderiv, sub_add_single hj]
      have h1 : 1 ≤ γ j := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
      have e : (((γ - Finsupp.single j 1 : ℕ+ →₀ ℕ) j : ℕ) : R) + 1 = (γ j : R) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        exact_mod_cast congrArg (Nat.cast (R := R)) (Nat.sub_add_cancel h1)
      rw [e]
      ring
    rw [hl]
    simp only [smul_eq_mul]
    ring
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, hp, hq]
    ring

end Coeff

section Series

variable {K : Type*} [Field K] [Algebra ℂ K]

theorem coeff_wardSeries (F : ℕ → MvPolynomial ℕ+ K) (γ : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff γ (wardSeries F) = MvPolynomial.coeff γ (F (lvl γ)) := rfl

theorem coeff_F_eq (F : ℕ → MvPolynomial ℕ+ K) (j : ℕ) (δ : ℕ+ →₀ ℕ) (h : lvl δ = j) :
    MvPolynomial.coeff δ (F j) = MvPowerSeries.coeff δ (wardSeries F) := by
  subst h
  rfl

theorem constantCoeff_wardSeries {μ lam Δa Δb : K} {F : ℕ → MvPolynomial ℕ+ K}
    (h : IsWardSeries μ lam Δa Δb F) : MvPowerSeries.constantCoeff (wardSeries F) = 1 := by
  have e : MvPowerSeries.constantCoeff (wardSeries F) = MvPolynomial.coeff 0 (F 0) := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_wardSeries]
    simp [lvl]
  rw [e, h.1]
  simp

/-- The Ward equations `l_k F = (l_0 + kΔ_b - Δ_a) F` for the formal series `F = ∑_m F_m`. -/
theorem ward_series_eq {μ lam Δa Δb : K} {F : ℕ → MvPolynomial ℕ+ K}
    (h : IsWardSeries μ lam Δa Δb F) (k : ℕ) (hk : 1 ≤ k) :
    shiftA k (wardSeries F)
      - algebraMap ℂ K (1 / 4) • ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) (wardSeries F))
      + (μ * (k : K) + algebraMap ℂ K Complex.I * lam) • pdA k (wardSeries F) =
    levelA (wardSeries F) + (lam ^ 2 + μ ^ 2 + ((k : K) * Δb - Δa)) • wardSeries F := by
  ext γ
  have hW := congrArg (MvPolynomial.coeff γ) (h.2.2 k hk (lvl γ))
  rw [ffOp_eq_ffOpR, ffOp_eq_ffOpR, coeff_ffOpR_pos _ _ k hk, MvPolynomial.coeff_add,
    coeff_ffOpR_zero, MvPolynomial.coeff_C_mul] at hW
  have hjk : ∀ j : ℕ, 1 ≤ j → ((j.toPNat' : ℕ+) : ℕ) = j := fun j hj => PNat.toPNat'_coe hj
  simp only [map_add, map_sub, MvPowerSeries.coeff_smul, map_sum, coeff_shiftA, coeff_levelA,
    coeff_pdA]
  simp only [MvPolynomial.coeff_pderiv] at hW
  have e1 : ∀ j ∈ γ.support, MvPolynomial.coeff
      (γ - Finsupp.single j 1 + Finsupp.single ((j : ℕ) + k).toPNat' 1) (F (lvl γ + k)) =
      MvPowerSeries.coeff (γ - Finsupp.single j 1 + Finsupp.single ((j : ℕ) + k).toPNat' 1)
        (wardSeries F) := fun j hj => by
    refine coeff_F_eq F _ _ ?_
    have e := congrArg lvl (sub_add_single hj)
    rw [lvl_add, lvl_single] at e
    rw [lvl_add, lvl_single, hjk _ (by omega)]
    omega
  have e2 : ∀ n ∈ Icc 1 (k - 1), MvPolynomial.coeff
      (γ + Finsupp.single n.toPNat' 1 + Finsupp.single (k - n).toPNat' 1) (F (lvl γ + k)) =
      MvPowerSeries.coeff (γ + Finsupp.single n.toPNat' 1 + Finsupp.single (k - n).toPNat' 1)
        (wardSeries F) := fun n hn => by
    have hn' := Finset.mem_Icc.1 hn
    refine coeff_F_eq F _ _ ?_
    rw [lvl_add, lvl_add, lvl_single, lvl_single, hjk _ hn'.1, hjk _ (by omega)]
    omega
  have e3 : MvPolynomial.coeff (γ + Finsupp.single k.toPNat' 1) (F (lvl γ + k)) =
      MvPowerSeries.coeff (γ + Finsupp.single k.toPNat' 1) (wardSeries F) := by
    refine coeff_F_eq F _ _ ?_
    rw [lvl_add, lvl_single, hjk _ hk]
  rw [Finset.sum_congr rfl fun j hj => by rw [e1 j hj],
    Finset.sum_congr (s₁ := Icc 1 (k - 1)) rfl fun n hn => by rw [e2 n hn], e3,
    coeff_F_eq F (lvl γ) γ rfl] at hW
  linear_combination hW

end Series

end Virasoro.Sphere
