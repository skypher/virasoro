import Virasoro.Statements.Sec7ChainValues
import Virasoro.Proofs.Sec7FixedCharge
import Virasoro.Proofs.Sec7Cut
import Virasoro.Proofs.Jets
import Virasoro.Proofs.Sec4Thm

/-!
# Corollary 7.16 (`cor:chain-values`): chain values from data at the fixed charge

Paper proof: (7.9) is (7.8) at the weight `a` and the level `M`, solved for its first term;
(7.10) is Lemma 7.10 at `b = b⋆`, where every chain function is regular (Lemma 7.13), so the
value of a product is the product of the values; the last assertion follows by induction on
the level and then on `j`.  If `a ∉ Kac_D(b⋆)` there is no chain and the value is `0`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- The value at `t = 0` of a product of two germs regular at `0`. -/
theorem coeff_zero_mul_of_ordGE {K : Type*} [Field K] [CharZero K] {x y : K⸨X⸩} (hx : OrdGE x 0)
    (hy : OrdGE y 0) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  obtain ⟨p, rfl, -⟩ := exists_ofPowerSeries hx
  obtain ⟨q, rfl, -⟩ := exists_ofPowerSeries hy
  have h1 := coeff_ofPowerSeries_nat (p * q) 0
  have h2 := coeff_ofPowerSeries_nat p 0
  have h3 := coeff_ofPowerSeries_nat q 0
  push_cast at h1 h2 h3
  rw [h1, h2, h3]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- No chain starts at a weight outside `Kac_D(b⋆)`. -/
theorem chainFnC_eq_zero_of_not_mem {b lam : ℂ} {D k j : ℕ} (h : lam ∉ Lam D b) :
    chainFnC b lam D k j = 0 := by
  unfold chainFnC chainFn
  refine Finset.sum_eq_zero fun g hg => ?_
  exfalso
  obtain ⟨hgl, hgw⟩ := (mem_labelsAt (bsC b)).1 hg
  apply h
  unfold Lam
  refine Finset.mem_image.2 ⟨g, hgl, ?_⟩
  rw [bsC, kacHL_ratC] at hgw
  exact (RatFunc.C : ℂ →+* Kd).injective hgw

theorem chainData_mono {b a : ℂ} {n D : ℕ} (h : n ≤ D) : chainData b a n ⊆ chainData b a D := by
  rintro x ⟨m, n', h1, hm, hn', e, rfl⟩
  exact ⟨m, n', h1, hm.trans h, lt_of_lt_of_le hn' h, e, rfl⟩

theorem chainData_shift {b a : ℂ} {n D : ℕ} (h : n ≤ D) :
    chainData b (a + n) (D - n) ⊆ chainData b a D := by
  rintro x ⟨m, n', h1, hm, hn', e, rfl⟩
  refine ⟨m, n + n', h1, by omega, by omega, e, ?_⟩
  congr 2
  push_cast
  ring

/-- Corollary 7.16 from Theorem 7.14 and Lemma 7.10. -/
theorem cor_chain_values_of (hfc : Stmt_thm_fixed_charge) (hcut : Stmt_lem_cutting) :
    Stmt_cor_chain_values := by
  intro b hb
  have hreg : ∀ (lam : ℂ) (D k j : ℕ), 1 ≤ D → 1 ≤ k → OrdGE (chainFnC b lam D k j) 0 := by
    intro lam D k j hD hk
    have := (hfc b hb 1 le_rfl).2.2 lam D k j hD hk
    simpa [OrdGE] using this
  have h79 : ∀ M : ℕ, 1 ≤ M → ∀ a ∈ Lam M b, ∀ k : ℕ, 1 ≤ k →
      ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
        (chainFnC b a M k 0).coeff 0 =
          Astar b M a k -
            ∑ n ∈ Finset.Ioo 0 M, ∑ j ∈ Finset.range J,
              (chainFnC b a n k j).coeff 0 *
                ((j.factorial : Kd) * lcoeff (HN (kacC b) (M - n)) (pt (a + n)) j) := by
    intro M hM a ha k hk
    obtain ⟨J₀, hJ⟩ := ((hfc b hb M hM).1 a ha k hk).2
    refine ⟨J₀, fun J hJJ => ?_⟩
    rw [hJ J hJJ]
    unfold fixedChargeRHS
    ring
  have h710 : ∀ (a : ℂ) (D k j : ℕ), 1 ≤ D → 1 ≤ k → 1 ≤ j →
      (j : Kd) * (chainFnC b a D k j).coeff 0 =
        (chainFnC b a D (k + 1) (j - 1)).coeff 0 -
          ∑ n ∈ Finset.Ioo 0 D,
            (chainFnC b a n k 0).coeff 0 * (chainFnC b (a + n) (D - n) 1 (j - 1)).coeff 0 := by
    intro a D k j hD hk hj
    have h := congrArg (fun x : Kd⸨X⸩ => x.coeff 0) (hcut b hb a D k j hD hk hj)
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_sum] at h
    rw [← (map_natCast (HahnSeries.C : Kd →+* Kd⸨X⸩) j), HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioo.1 hn
    exact coeff_zero_mul_of_ordGE (hreg a n k 0 hn1 hk) (hreg (a + n) (D - n) 1 (j - 1)
      (by omega) le_rfl)
  refine ⟨h79, h710, ?_⟩
  intro a D
  induction D using Nat.strong_induction_on generalizing a with
  | _ D ihD =>
  intro k j hD hk
  induction j generalizing k with
  | zero =>
    by_cases ha : a ∈ Lam D b
    · obtain ⟨J₀, hJ⟩ := h79 D hD a ha k hk
      rw [hJ J₀ le_rfl]
      refine Subalgebra.sub_mem _ ?_ (Subalgebra.sum_mem _ fun n hn =>
        Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (Subalgebra.mul_mem _ ?_ ?_))
      · apply Algebra.subset_adjoin
        refine ⟨D, 0, hD, le_rfl, by omega, -(k : ℤ), ?_⟩
        simp [Astar, ppCoeff]
      · obtain ⟨hn1, hn2⟩ := Finset.mem_Ioo.1 hn
        exact Algebra.adjoin_mono (chainData_mono hn2.le) (ihD n hn2 a k j hn1 hk)
      · exact Subalgebra.natCast_mem _ _
      · obtain ⟨hn1, hn2⟩ := Finset.mem_Ioo.1 hn
        apply Algebra.subset_adjoin
        exact ⟨D - n, n, by omega, by omega, hn2, j, rfl⟩
    · rw [chainFnC_eq_zero_of_not_mem ha]
      simp
  | succ j ihj =>
    have h := h710 a D k (j + 1) hD hk (by omega)
    simp only [Nat.add_sub_cancel] at h
    have hj0 : ((j + 1 : ℕ) : Kd) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hval : (chainFnC b a D k (j + 1)).coeff 0 =
        ((j + 1 : ℕ) : Kd)⁻¹ *
          ((chainFnC b a D (k + 1) j).coeff 0 -
            ∑ n ∈ Finset.Ioo 0 D,
              (chainFnC b a n k 0).coeff 0 * (chainFnC b (a + n) (D - n) 1 j).coeff 0) := by
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hj0, one_mul]
    rw [hval]
    refine Subalgebra.mul_mem _ ?_ (Subalgebra.sub_mem _ (ihj (k + 1) (by omega))
      (Subalgebra.sum_mem _ fun n hn => Subalgebra.mul_mem _ ?_ ?_))
    · have : ((j + 1 : ℕ) : Kd)⁻¹ = algebraMap ℚ Kd ((j + 1 : ℚ)⁻¹) := by
        rw [map_inv₀]
        push_cast
        rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    · obtain ⟨hn1, hn2⟩ := Finset.mem_Ioo.1 hn
      exact Algebra.adjoin_mono (chainData_mono hn2.le) (ihD n hn2 a k 0 hn1 hk)
    · obtain ⟨hn1, hn2⟩ := Finset.mem_Ioo.1 hn
      exact Algebra.adjoin_mono (chainData_shift hn2.le)
        (ihD (D - n) (by omega) (a + n) 1 j (by omega) le_rfl)

/-- Corollary 7.16 (`cor:chain-values`) from the cited inputs of Theorem 7.14.
Paper label: cor:chain-values -/
theorem cor_chain_values_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_cor_chain_values :=
  cor_chain_values_of (thm_fixed_charge_of_cited hK hH) lem_cutting

end Virasoro
