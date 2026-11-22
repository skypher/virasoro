import Virasoro.Sphere.Proofs.Sec3GaussShiftSubst
import Virasoro.Sphere.Proofs.Sec3GaussLog
import Virasoro.Sphere.Proofs.Sec3GaussWick

/-!
# Tools for the `λ⁻¹`-expansion of the shifted factor (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.684–702.  `T = S̃⁽¹⁾-part + t T₂` with `T₂|_{t=0} = S⁽²⁾`; a series `V(t x)`
whose constant term vanishes is `t` times a series whose value at `t = 0` is the linear part of
`V` (this is how the order `λ¹` disappears and the order `λ⁰` is linear in the fluctuation
variables); a series evaluated at constants is a constant.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "KK" => RatFunc ℂ
local notation "PP" => PowerSeries ℂ

/-- `T₂ = (S - S⁽⁰⁾ - t S⁽¹⁾)/t² = ∑_{r≥2} t^{r-2} S⁽ʳ⁾`, with coefficients in `ℂ[[t]]`. -/
noncomputable def SPtail2 (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries ℕ+ PP :=
  fun α => PowerSeries.mk fun r => PowerSeries.coeff (r + 2) (coeff α (SP F))

theorem coeff_SPtail2 (F : ℕ → MvPolynomial ℕ+ KK) (α : ℕ+ →₀ ℕ) (r : ℕ) :
    PowerSeries.coeff r (coeff α (SPtail2 F)) = PowerSeries.coeff (r + 2) (coeff α (SP F)) := by
  show PowerSeries.coeff r (PowerSeries.mk fun r => PowerSeries.coeff (r + 2) (coeff α (SP F))) = _
  rw [PowerSeries.coeff_mk]

/-- `T = S⁽¹⁾ + t T₂`. -/
theorem SPtail_split (F : ℕ → MvPolynomial ℕ+ KK) (α : ℕ+ →₀ ℕ) :
    coeff α (SPtail F) =
      PowerSeries.C (coeff α (Sord F 1)) + PowerSeries.X * coeff α (SPtail2 F) := by
  ext r
  cases r with
  | zero =>
    have h0 := congrArg (coeff α) (Sord_eq_cR F 1)
    rw [coeff_cR] at h0
    rw [coeff_SPtail, h0]
    simp
  | succ r =>
    rw [map_add, PowerSeries.coeff_succ_X_mul, coeff_SPtail, coeff_SPtail2, PowerSeries.coeff_C,
      if_neg (Nat.succ_ne_zero r), zero_add]

theorem map_constantCoeff_SPtail2 (F : ℕ → MvPolynomial ℕ+ KK) :
    map (PowerSeries.constantCoeff (R := ℂ)) (SPtail2 F) = Sord F 2 := by
  ext α
  have h0 := congrArg (coeff α) (Sord_eq_cR F 2)
  rw [coeff_cR] at h0
  rw [coeff_map, h0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_SPtail2]

theorem constantCoeff_SPtail2 {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) : constantCoeff (SPtail2 F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  ext r
  rw [coeff_SPtail2]
  show PowerSeries.coeff (r + 2)
    (PowerSeries.mk fun r : ℕ => (coeff 0 (SL F)).coeff (r : ℤ)) = _
  rw [PowerSeries.coeff_mk, coeff_zero_SL F (constantCoeff_wardSeries h)]
  simp

section Dq

variable {τ : Type*} {S : Type*} [CommRing S]

open Classical in
/-- `(V(r x) - V(0))/r`: the coefficient of `x^β` is `r^{|β|-1} V_β` for `β ≠ 0`. -/
noncomputable def dq (r : S) (V : MvPowerSeries τ S) : MvPowerSeries τ S :=
  fun β => if β = 0 then 0 else r ^ (β.degree - 1) * coeff β V

open Classical in
theorem coeff_dq (r : S) (V : MvPowerSeries τ S) (β : τ →₀ ℕ) :
    coeff β (dq r V) = if β = 0 then 0 else r ^ (β.degree - 1) * coeff β V := rfl

theorem constantCoeff_dq (r : S) (V : MvPowerSeries τ S) : constantCoeff (dq r V) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_dq, if_pos rfl]

/-- `V(r x) = V(0) + r · (V(r x) - V(0))/r`. -/
theorem rescale_eq_dq (r : S) (V : MvPowerSeries τ S) :
    rescale (fun _ => r) V = C (constantCoeff V) + C r * dq r V := by
  classical
  ext β
  rw [coeff_rescale, prod_const_pow, map_add, coeff_C_mul, coeff_dq, coeff_C]
  by_cases h : β = 0
  · subst h
    simp
  · rw [if_neg h, if_neg h, zero_add, ← mul_assoc, ← pow_succ']
    have hd : β.degree ≠ 0 := fun h0 => h ((Finsupp.degree_eq_zero_iff β).1 h0)
    rw [show β.degree - 1 + 1 = β.degree by omega]

variable [Fintype τ] [DecidableEq τ]

theorem coeff_linForm (a : τ → S) (β : τ →₀ ℕ) :
    coeff β (linForm a) = ∑ i, if β = Finsupp.single i 1 then a i else 0 := by
  rw [linForm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

/-- At `r = 0`, `(V(r x) - V(0))/r` is the linear part of `V`. -/
theorem map_dq_zero {S' : Type*} [CommRing S'] (ε : S →+* S') (r : S) (hr : ε r = 0)
    (V : MvPowerSeries τ S) :
    map ε (dq r V) = linForm fun x => ε (coeff (Finsupp.single x 1) V) := by
  ext β
  rw [coeff_map, coeff_dq, coeff_linForm]
  by_cases h0 : β = 0
  · subst h0
    rw [if_pos rfl, map_zero]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro h
    have := congrArg Finsupp.degree h
    simp at this
  · rw [if_neg h0]
    by_cases h1 : ∃ x, β = Finsupp.single x 1
    · obtain ⟨x, rfl⟩ := h1
      rw [Finset.sum_eq_single x]
      · rw [if_pos rfl]
        simp
      · intro i _ hi
        rw [if_neg]
        intro h
        exact hi (Finsupp.single_left_injective one_ne_zero h).symm
      · intro h
        exact absurd (Finset.mem_univ x) h
    · have hd : 2 ≤ β.degree := by
        by_contra hlt
        have hd0 : β.degree ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff β).1 h)
        have hd1 : β.degree = 1 := by omega
        rw [Finsupp.degree_eq_sum] at hd1
        apply h1
        obtain ⟨x, hx⟩ : ∃ x, β x ≠ 0 := by
          by_contra hne
          push Not at hne
          exact h0 (Finsupp.ext hne)
        refine ⟨x, Finsupp.ext fun y => ?_⟩
        have hle : β x ≤ ∑ i, β i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ x)
        have hx1 : β x = 1 := by omega
        by_cases hy : y = x
        · subst hy
          rw [hx1, Finsupp.single_eq_same]
        · rw [Finsupp.single_apply, if_neg (Ne.symm hy)]
          have h2 : β x + β y ≤ ∑ i, β i := by
            rw [← Finset.sum_pair (Ne.symm hy)]
            exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          omega
      rw [map_mul, map_pow, hr, zero_pow (by omega), zero_mul]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact h1 ⟨i, h⟩

end Dq

section Const

variable {n : ℕ} {S : Type*} [CommRing S]

/-- A series evaluated at constants is a constant. -/
theorem subst_cS_eq_C (s : Fin n → Modes n) {a : Modes n → S} (ha : ∀ x, IsNilpotent (a x))
    (G : MvPowerSeries ℕ+ S) :
    subst (cS s a) G = C (constantCoeff (subst (cS s a) G)) := by
  classical
  ext e
  by_cases he : e = 0
  · subst he
    simp
  · rw [coeff_C, if_neg he, coeff_subst (hasSubst_cS s ha)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    have hmem : (d.prod fun m k => cS s a m ^ k) ∈ (C : S →+* MvPowerSeries (Modes n) S).range := by
      refine Subring.prod_mem _ fun m _ => Subring.pow_mem _ ?_ _
      rw [cS]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨0, map_zero _⟩
    obtain ⟨x, hx⟩ := hmem
    rw [← hx, coeff_C, if_neg he, smul_zero]

end Const

end Virasoro.Sphere
