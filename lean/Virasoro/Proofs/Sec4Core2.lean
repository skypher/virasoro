import Virasoro.Proofs.Sec4Core1
import Virasoro.Proofs.SmithBasic

/-!
# Theorem 4.3, part II: the constant term of `H_N(c(b⋆+t), Δ, d)` is `H_N(c⋆, Δ, d)`
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section Ring

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)

/-- The Cramer numerator `∑ adj(G_M)_{Y,Y'} ρ_M{}_{Y,Y'}` over a commutative ring. -/
noncomputable def numR (c h d : R) (M : ℕ) : R :=
  ∑ Y, ∑ Y', (gram c h M).adjugate Y Y' * torus c h d M Y Y'

/-- The Shapovalov determinant over a commutative ring. -/
noncomputable def detR (c h : R) (M : ℕ) : R := (gram c h M).det

theorem map_detR (c h : R) (M : ℕ) : f (detR c h M) = detR (f c) (f h) M := by
  unfold detR
  rw [gram_map]
  exact RingHom.map_det f (gram c h M)

theorem map_numR (c h d : R) (M : ℕ) : f (numR c h d M) = numR (f c) (f h) (f d) M := by
  unfold numR
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_mul, gram_map, torus_map]
  have h := RingHom.map_adjugate f (gram c h M)
  have h2 := congrFun (congrFun h Y) Y'
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h2
  rw [h2]
  rfl

end Ring

section Field

variable {K : Type*} [Field K] [CharZero K]

theorem Fval_eq (c d z : K) (M : ℕ) : Fval c d z M = numR c z d M / detR c z M := rfl

theorem Frat_eq (c d : K) (M : ℕ) :
    Frat c d M = algebraMap K[X] (RatFunc K) (numR (C c) X (C d) M) /
      algebraMap K[X] (RatFunc K) (detR (C c) X M) := rfl

/-- A Laurent series of nonnegative valuation is a power series. -/
theorem exists_ofPowerSeries {x : K⸨X⸩} (hx : OrdGE x 0) :
    ∃ p : PowerSeries K, x = HahnSeries.ofPowerSeries ℤ K p ∧
      PowerSeries.constantCoeff p = x.coeff 0 := by
  refine ⟨PowerSeries.mk fun n => x.coeff n, ?_, ?_⟩
  · ext m
    rw [PowerSeries.coeff_coe]
    split_ifs with hm
    · exact hx.coeff_eq_zero hm
    · rw [PowerSeries.coeff_mk]
      congr 1
      exact (Int.natAbs_of_nonneg (by omega)).symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simp

theorem regVal_ofPowerSeries (p : PowerSeries K) :
    RegVal (HahnSeries.ofPowerSeries ℤ K p) (PowerSeries.constantCoeff p) := by
  refine ⟨ordGE_ofPowerSeries p, ?_⟩
  have := PowerSeries.coeff_coe (f := p) 0
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using this

theorem RegVal.sum {α : Type*} {s : Finset α} {f : α → K⸨X⸩} {v : α → K}
    (h : ∀ i ∈ s, RegVal (f i) (v i)) : RegVal (∑ i ∈ s, f i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨OrdGE.zero 0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The constant-term step of the proof of Theorem 4.3: over `K(Δ)⸨t⸩`, the value
`H_N(c(b⋆ + t), Δ, d)` is regular at `t = 0` with value `H_N(c(b⋆), Δ, d)`. -/
theorem regVal_Hrat_germ (bs d : K) (hbs : bs ≠ 0) (N : ℕ) :
    RegVal
      (evalAt (HahnSeries.C (RatFunc.X : RatFunc K))
        (Hrat (kacC (mapL (algebraMap K (RatFunc K)) (bGerm bs)))
          (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) N))
      (Hrat (kacC bs) d N) := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  have hιbs : ι bs ≠ 0 := (map_ne_zero ι).2 hbs
  -- the central charge is a power series in `t`
  have hc : RegVal (kacC (mapL ι (bGerm bs))) (ι (kacC bs)) := by
    rw [mapL_bGerm, map_kacC]
    have hb := regVal_bGerm (ι bs)
    have hbi := hb.inv hιbs
    unfold kacC
    have h1 : RegVal (1 : (RatFunc K)⸨X⸩) 1 := by simpa using regVal_C (1 : RatFunc K)
    exact h1.add ((regVal_ofNat 6).mul ((hb.add hbi).pow 2))
  obtain ⟨cp, hcp, hcp0⟩ := exists_ofPowerSeries hc.1
  rw [hc.2] at hcp0
  set ofPS := HahnSeries.ofPowerSeries ℤ (RatFunc K) with hofPS
  have hΔ : (HahnSeries.C (RatFunc.X : RatFunc K) : (RatFunc K)⸨X⸩) =
      ofPS (PowerSeries.C (RatFunc.X : RatFunc K)) := by
    rw [hofPS, HahnSeries.ofPowerSeries_C]
  have hd : mapL ι (HahnSeries.C d) = ofPS (PowerSeries.C (ι d)) := by
    rw [mapL_C, hofPS, HahnSeries.ofPowerSeries_C]
  -- the Cramer data over `K(Δ)⟦t⟧`
  have hdet : ∀ M, detR (kacC (mapL ι (bGerm bs))) (HahnSeries.C (RatFunc.X : RatFunc K)) M =
      ofPS (detR cp (PowerSeries.C RatFunc.X) M) := by
    intro M
    rw [map_detR, ← hcp, ← hΔ]
  have hnum : ∀ M, numR (kacC (mapL ι (bGerm bs))) (HahnSeries.C (RatFunc.X : RatFunc K))
      (mapL ι (HahnSeries.C d)) M =
        ofPS (numR cp (PowerSeries.C RatFunc.X) (PowerSeries.C (ι d)) M) := by
    intro M
    rw [map_numR, ← hcp, ← hΔ, ← hd]
  have halg : ∀ c : K, algebraMap K[X] (RatFunc K) (C c) = ι c := fun c => by
    rw [RatFunc.algebraMap_C, hι, RatFunc.algebraMap_eq_C]
  have hdet0 : ∀ M, PowerSeries.constantCoeff (detR cp (PowerSeries.C RatFunc.X) M) =
      algebraMap K[X] (RatFunc K) (detR (C (kacC bs)) X M) := by
    intro M
    rw [map_detR, map_detR, hcp0, PowerSeries.constantCoeff_C, halg, RatFunc.algebraMap_X]
  have hnum0 : ∀ M, PowerSeries.constantCoeff
      (numR cp (PowerSeries.C RatFunc.X) (PowerSeries.C (ι d)) M) =
        algebraMap K[X] (RatFunc K) (numR (C (kacC bs)) X (C d) M) := by
    intro M
    rw [map_numR, map_numR, hcp0, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C,
      halg, halg, RatFunc.algebraMap_X]
  have hdetne : ∀ M, algebraMap K[X] (RatFunc K) (detR (C (kacC bs)) X M) ≠ 0 := fun M =>
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 (gramPoly_det_ne_zero (kacC bs) M)
  have hFreg : ∀ M, RegVal (Fval (kacC (mapL ι (bGerm bs))) (mapL ι (HahnSeries.C d))
      (HahnSeries.C (RatFunc.X : RatFunc K)) M) (Frat (kacC bs) d M) := by
    intro M
    rw [Fval_eq, Frat_eq, hnum, hdet]
    have h1 := regVal_ofPowerSeries (numR cp (PowerSeries.C RatFunc.X) (PowerSeries.C (ι d)) M)
    have h2 := regVal_ofPowerSeries (detR cp (PowerSeries.C (RatFunc.X : RatFunc K)) M)
    rw [hnum0] at h1
    rw [hdet0] at h2
    exact h1.div h2 (hdetne M)
  have hdetne' : ∀ M, (gram (kacC (mapL ι (bGerm bs)))
      (HahnSeries.C (RatFunc.X : RatFunc K)) M).det ≠ 0 := by
    intro M h0
    have h2 := regVal_ofPowerSeries (detR cp (PowerSeries.C (RatFunc.X : RatFunc K)) M)
    rw [hdet0, ← hdet] at h2
    have : detR (kacC (mapL ι (bGerm bs))) (HahnSeries.C (RatFunc.X : RatFunc K)) M = 0 := h0
    rw [this] at h2
    exact hdetne M (by simpa using h2.2.symm)
  rw [evalAt_Hrat fun M _ => hdetne' M]
  unfold Hval Hrat
  refine RegVal.sum fun j _ => ?_
  have hη : RegVal (((eta j : ℤ) : (RatFunc K)⸨X⸩)) ((eta j : ℤ) : RatFunc K) := regVal_intCast _
  exact hη.mul (hFreg (N - j))

end Field

end Virasoro
