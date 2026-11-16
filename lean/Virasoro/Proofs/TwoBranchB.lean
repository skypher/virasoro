import Virasoro.Proofs.TwoBranchA

/-!
# Proposition 7.7, second part: `S_{κ,M}(t) = R_τ(t)/ζ(t) + Q + O(t)`

With `U(b,Δ) = (Δ - h_τ(b)) H_M(c(b),Δ,d)` regular at `(b⋆, z)` and `U(b, h_τ(b)) = R_τ(b)` by the
generic recursion at level `M`, the function
`V(b,Δ) = H_M(c(b),Δ,d) - R_τ(b)/(Δ - h_τ(b))` is regular at `(b⋆, z)`; its value there is the
finite part `Q` of `H_M(c⋆,·,d)` at `z`, and its restriction to `Δ = z_κ(t)` is
`S_{κ,M}(t) - R_τ(t)/ζ(t)`.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

variable {K : Type} [Field K] [CharZero K]

/-- The shifted coefficient on a branch of a two-branch collision. -/
theorem shifted_branch (hK : Cited_KacDeterminant) (hrec : GenericRecursionUniform) {bs : K}
    (hbs : bs ≠ 0) (d : K) {κ τ : Label} {M : ℕ} (hκ1 : 0 < κ.1) (hκ2 : 0 < κ.2)
    (hτ : τ ∈ labels M) (hτlvl : τ.lvl = M)
    (huniq : ∀ g ∈ labels M, kacHL g bs = kacHL κ bs + (κ.lvl : K) ↔ g = τ)
    (hRτ : OrdGE (RG bs d τ) 0) (hζ : zG bs κ - hG bs τ ≠ 0) :
    RegVal (SG bs d M κ - RG bs d τ / (zG bs κ - hG bs τ))
      (lcoeff (Hrat (kacC bs) d M) (kacHL κ bs + (κ.lvl : K)) 0) := by
  classical
  have hτz : kacHL τ bs = kacHL κ bs + (κ.lvl : K) := (huniq τ hτ).2 rfl
  rw [← hτz]
  have hbne := bGerm_ne_zero hbs
  have hirr := sqIrrational_bGerm bs
  obtain ⟨ht1, ht2, ht3⟩ := mem_labels.1 hτ
  have hM1 : 1 ≤ M := by
    have := Nat.mul_pos ht1 ht2
    omega
  have hgerm : ∀ M', 1 ≤ M' → GenericRecursionAt K⸨X⸩ (bGerm bs) (HahnSeries.C d) M' := by
    intro M' h1
    obtain ⟨S, hSne, hS⟩ := hrec M' h1
    exact hS K⸨X⸩ _ _ hbne fun P hP => aeval_bGerm_ne_zero bs (hSne P hP)
  -- lifts to power series in `t`
  obtain ⟨cp, hcp, hcp0⟩ := exists_ofPowerSeries (regVal_kacC_germ hbs).1
  rw [(regVal_kacC_germ hbs).2] at hcp0
  obtain ⟨hp, hhp, hhp0⟩ := exists_ofPowerSeries (regVal_hG hbs τ).1
  rw [(regVal_hG hbs τ).2] at hhp0
  obtain ⟨zp, hzp, hzp0⟩ := exists_ofPowerSeries (regVal_zG hbs κ).1
  rw [(regVal_zG hbs κ).2, ← hτz] at hzp0
  obtain ⟨rp, hrp, -⟩ := exists_ofPowerSeries hRτ
  set dp : PowerSeries K := PowerSeries.C d with hdp
  have hdp1 : toLS dp = HahnSeries.C d := HahnSeries.ofPowerSeries_C d
  have hdp0 : red0 dp = d := PowerSeries.constantCoeff_C d
  -- `U` is regular at `(b⋆, z)`
  have hU : Reg2 (kacHL τ bs)
      ((RatFunc.X - RatFunc.C (toLS hp)) * Hrat (toLS cp) (toLS dp) M)
      ((RatFunc.X - RatFunc.C (kacHL τ bs)) * Hrat (red0 cp) (red0 dp) M) := by
    unfold Hrat
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Reg2.sum fun j hj => ?_
    rw [mul_left_comm, mul_left_comm (RatFunc.X - RatFunc.C (kacHL τ bs))]
    refine (reg2_intCast _ _).mul ?_
    by_cases hj0 : j = 0
    · subst hj0
      rw [Nat.sub_zero]
      exact reg2_linear_mul_Frat hK hbs cp dp hp hcp.symm hcp0 hτ hτlvl hhp.symm hhp0
        (fun g hg h => (huniq g hg).1 (h.trans hτz))
    · have hlin := reg2_X_sub_C (kacHL τ bs) hp
      rw [hhp0] at hlin
      refine hlin.mul ?_
      rw [Frat_up, Frat_dn]
      refine reg2_div _ _ ?_
      rw [detR_map_red0, gramPoly_det_eval, hcp0]
      refine gram_det_ne_of_labels hK hbs fun g hg h => ?_
      have hgτ := (huniq g (labels_subset (Nat.sub_le M j) hg)).1 (h.trans hτz)
      obtain ⟨-, -, h3⟩ := mem_labels.1 hg
      rw [hgτ] at h3
      unfold Label.lvl at hτlvl
      omega
  rw [hcp0, hdp0] at hU
  -- the generic recursion at level `M`
  have hrecM := hgerm M hM1
  unfold GenericRecursionAt at hrecM
  set Rest : RatFunc K⸨X⸩ := ∑ a ∈ (labels M).erase τ,
      RatFunc.C (genR a.1 a.2 (bGerm bs) (HahnSeries.C d)) /
          (RatFunc.X - RatFunc.C (kacHL a (bGerm bs))) *
        RatFunc.C (RatFunc.eval (RingHom.id K⸨X⸩) (kacHL a (bGerm bs) + (a.lvl : K⸨X⸩))
          (Hrat (kacC (bGerm bs)) (HahnSeries.C d) (M - a.lvl))) with hRest
  have hH : Hrat (kacC (bGerm bs)) (HahnSeries.C d) M
      = RatFunc.C (RG bs d τ) / (RatFunc.X - RatFunc.C (hG bs τ)) + Rest := by
    rw [hrecM, ← Finset.add_sum_erase _ _ hτ]
    congr 1
    rw [hτlvl, Nat.sub_self, Hrat_zero]
    simp [RG, hG]
  have hRestReg : RegAt (hG bs τ) Rest := by
    refine RegAt.sum fun a ha => ?_
    obtain ⟨hane, haM⟩ := Finset.mem_erase.1 ha
    obtain ⟨ha1, ha2, -⟩ := mem_labels.1 haM
    refine regAt_pole_mul ?_ _ _
    intro h
    refine kacH_ne hbne hirr (τ.1 : ℤ) (τ.2 : ℤ) (a.1 : ℤ) (a.2 : ℤ) (by exact_mod_cast ht1)
      (by exact_mod_cast ht2) (by exact_mod_cast ha1) (by exact_mod_cast ha2) ?_ (sub_eq_zero.2 h)
    intro hpair
    apply hane
    have h1 := (Prod.mk.inj hpair).1
    have h2 := (Prod.mk.inj hpair).2
    exact Prod.ext (by exact_mod_cast h1.symm) (by exact_mod_cast h2.symm)
  have hne := ratFunc_X_sub_C_ne_zero (hG bs τ)
  have hf : (RatFunc.X - RatFunc.C (toLS hp)) * Hrat (toLS cp) (toLS dp) M - RatFunc.C (toLS rp)
      = (RatFunc.X - RatFunc.C (hG bs τ)) * Rest := by
    rw [← hcp, hdp1, ← hhp, ← hrp, hH]
    field_simp
    ring
  have hfzero : evalAt (toLS hp)
      ((RatFunc.X - RatFunc.C (toLS hp)) * Hrat (toLS cp) (toLS dp) M - RatFunc.C (toLS rp))
        = 0 := by
    rw [hf, ← hhp, evalAt_mul (regAt_X_sub_C _ _).1 hRestReg, (regAt_X_sub_C _ _).2, sub_self,
      zero_mul]
  have hV := (hU.sub (reg2_C (kacHL τ bs) rp)).div_linear hp hhp0 hfzero
  have hVeq : ((RatFunc.X - RatFunc.C (toLS hp)) * Hrat (toLS cp) (toLS dp) M
      - RatFunc.C (toLS rp)) / (RatFunc.X - RatFunc.C (toLS hp)) = Rest := by
    rw [hf, ← hhp, mul_div_cancel_left₀ _ hne]
  rw [hVeq] at hV
  -- restriction to the curve `Δ = z_κ(t)`
  obtain ⟨hVreg, hVval⟩ := hV.curve zp hzp0
  rw [← hzp] at hVreg hVval
  have hSG : SG bs d M κ = evalAt (zG bs κ) (Hrat (kacC (bGerm bs)) (HahnSeries.C d) M) := by
    have h := SG_eq_eval (ι := RingHom.id K) bs d M hbs
      (fun M' h1 _ => by simp only [mapL_id]; exact hgerm M' h1) M le_rfl κ hκ1 hκ2
    simp only [mapL_id] at h
    exact h
  have hpole := regAt_pole (sub_ne_zero.1 hζ) (RG bs d τ)
  rw [hSG, hH, evalAt_add hpole.1 hVreg, hpole.2, add_sub_cancel_left]
  -- the value is the finite part of `H_M(c⋆,·,d)` at `z`
  have hlc : lcoeff (Hrat (kacC bs) d M) (kacHL τ bs) 0
      = evalAt (kacHL τ bs) (((RatFunc.X - RatFunc.C (kacHL τ bs)) * Hrat (kacC bs) d M
          - RatFunc.C (red0 rp)) / (RatFunc.X - RatFunc.C (kacHL τ bs))) := by
    have hne0 := ratFunc_X_sub_C_ne_zero (kacHL τ bs)
    have e : Hrat (kacC bs) d M
        = ((RatFunc.X - RatFunc.C (kacHL τ bs)) * Hrat (kacC bs) d M
            - RatFunc.C (red0 rp)) / (RatFunc.X - RatFunc.C (kacHL τ bs))
          + RatFunc.C (red0 rp) / (RatFunc.X - RatFunc.C (kacHL τ bs)) ^ 1 := by
      rw [pow_one]
      field_simp
      ring
    unfold lcoeff
    rw [expandAt_eq]
    conv_lhs => rw [e]
    rw [map_add, expandHom_pole_same, HahnSeries.coeff_add, ← expandAt_eq, hV.expand.2.2,
      HahnSeries.coeff_single_of_ne (by norm_num), add_zero]
  rw [hlc]
  exact hVval

end Virasoro
