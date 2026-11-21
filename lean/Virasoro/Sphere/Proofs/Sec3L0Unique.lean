import Virasoro.Sphere.Proofs.Sec3SaddleLin

/-!
# Sphere paper Lemma 3.3(ii): uniqueness for the operators `L_k^{(0)}`
(`sphere/paper.tex` l.572–584, l.606–611)

A series `D` with `L_k^{(0)} D = 0` for all `k ≥ 1` has no monomial other than the constant: by
induction on the oscillator level and, within a level, on the polynomial degree.  In
`L_k^{(0)}` the terms `-∑ nσ_n∂_n` and `-½∑(∂_nS^{(0)})∂_{k-n}` act on lower levels, and
`∑ nσ_n∂_{n+k}` preserves the degree while `i∂_k` lowers it by one, so the coefficient of
`σ^{α-e_k}` in `L_k^{(0)} D = 0` is `i α_k D_α` modulo coefficients already known to vanish
(injectivity of `𝒟_m(∞)`).

Consumers: Lemma 3.6 (uniqueness of `S_1^{(2)}, S_2^{(2)}`), Lemma 3.3(ii).
-/

namespace Virasoro.Sphere

open Finset

/-- The oscillator level of a monomial. -/
noncomputable abbrev lvl (α : ℕ+ →₀ ℕ) : ℕ := Finsupp.weight fockWeight α

theorem lvl_add (α β : ℕ+ →₀ ℕ) : lvl (α + β) = lvl α + lvl β := map_add _ _ _

theorem lvl_single (k : ℕ+) : lvl (Finsupp.single k 1) = (k : ℕ) := by
  simp [lvl, Finsupp.weight_single, fockWeight]

theorem sub_add_single {α : ℕ+ →₀ ℕ} {k : ℕ+} (hk : k ∈ α.support) :
    α - Finsupp.single k 1 + Finsupp.single k 1 = α := by
  ext j
  have hk' := Finsupp.mem_support_iff.1 hk
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h
    omega
  · omega

theorem add_single_ne_zero (γ : ℕ+ →₀ ℕ) (j : ℕ+) : γ + Finsupp.single j 1 ≠ 0 := fun h0 => by
  have h1 := congrArg (fun f : ℕ+ →₀ ℕ => f j) h0
  simp at h1

/-- Uniqueness for `L_k^{(0)}` (l.606–611): a solution of the homogeneous equations has no
nonconstant monomial. -/
theorem L0_unique (D : MvPowerSeries ℕ+ ℂ) (h : ∀ k : ℕ, 1 ≤ k → L0 k D = 0) :
    ∀ α : ℕ+ →₀ ℕ, α ≠ 0 → MvPowerSeries.coeff α D = 0 := by
  have key : ∀ m d : ℕ, ∀ α : ℕ+ →₀ ℕ, lvl α = m → α.degree = d → α ≠ 0 →
      MvPowerSeries.coeff α D = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ihd =>
        intro α hm hd hα
        obtain ⟨k, hk⟩ : ∃ k, k ∈ α.support := Finsupp.support_nonempty_iff.2 hα
        have hαβ : α - Finsupp.single k 1 + Finsupp.single k 1 = α := sub_add_single hk
        have hlvl : lvl (α - Finsupp.single k 1) + (k : ℕ) = m := by
          rw [← hm, ← lvl_single k, ← lvl_add, hαβ]
        have hdeg : (α - Finsupp.single k 1).degree + 1 = d := by
          have e := congrArg Finsupp.degree hαβ
          rw [map_add, Finsupp.degree_single] at e
          rw [e, hd]
        have hk1 : 1 ≤ (k : ℕ) := k.pos
        generalize α - Finsupp.single k 1 = β at hαβ hlvl hdeg
        have hE := congrArg (MvPowerSeries.coeff β) (h (k : ℕ) hk1)
        rw [L0] at hE
        simp only [map_sub, map_add, map_zero, map_smul, smul_eq_mul, map_sum] at hE
        have hs : MvPowerSeries.coeff β (shiftOp (k : ℕ) D) = 0 := by
          show ∑ n ∈ β.support, ((n : ℕ) : ℂ) *
            MvPowerSeries.coeff (β - Finsupp.single n 1) (pd ((n : ℕ) + (k : ℕ)) D) = 0
          refine Finset.sum_eq_zero fun n hn => ?_
          have hj : ((((n : ℕ) + (k : ℕ)).toPNat' : ℕ+) : ℕ) = (n : ℕ) + (k : ℕ) :=
            PNat.toPNat'_coe (by omega)
          have hβn := sub_add_single hn
          have h1 : lvl (β - Finsupp.single n 1 +
              Finsupp.single ((n : ℕ) + (k : ℕ)).toPNat' 1) = m := by
            have e := congrArg lvl hβn
            rw [lvl_add, lvl_single] at e
            rw [lvl_add, lvl_single, hj]
            omega
          have h2 : (β - Finsupp.single n 1 +
              Finsupp.single ((n : ℕ) + (k : ℕ)).toPNat' 1).degree = d - 1 := by
            have e := congrArg Finsupp.degree hβn
            rw [map_add, Finsupp.degree_single] at e
            rw [map_add, Finsupp.degree_single]
            omega
          rw [pd, MvPowerSeries.coeff_pderiv,
            ihd (d - 1) (by omega) _ h1 h2 (add_single_ne_zero _ _), zero_mul, mul_zero]
        have hl : MvPowerSeries.coeff β (levelOp D) = 0 := by
          show ((lvl β : ℕ) : ℂ) * MvPowerSeries.coeff β D = 0
          by_cases hβ0 : β = 0
          · rw [hβ0]
            simp [lvl]
          · rw [ihm (lvl β) (by omega) β.degree β rfl rfl hβ0, mul_zero]
        have hp : ∀ n ∈ Icc 1 ((k : ℕ) - 1),
            MvPowerSeries.coeff β (pd n S0 * pd ((k : ℕ) - n) D) = 0 := fun n hn => by
          have hn' := Finset.mem_Icc.1 hn
          rw [MvPowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun p hp => ?_
          have hpβ : p.1 + p.2 = β := by simpa using hp
          have hj : (((((k : ℕ) - n).toPNat' : ℕ+)) : ℕ) = (k : ℕ) - n :=
            PNat.toPNat'_coe (by omega)
          have e := congrArg lvl hpβ
          rw [lvl_add] at e
          have h1 : lvl (p.2 + Finsupp.single ((k : ℕ) - n).toPNat' 1) < m := by
            rw [lvl_add, lvl_single, hj]
            omega
          rw [pd, pd, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
            ihm _ h1 _ (p.2 + Finsupp.single ((k : ℕ) - n).toPNat' 1) rfl rfl
              (add_single_ne_zero _ _), zero_mul, mul_zero]
        rw [hs, hl, Finset.sum_eq_zero hp, pd, MvPowerSeries.coeff_pderiv, PNat.coe_toPNat',
          hαβ] at hE
        have hne : ((β k : ℕ) : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
        have h3 : MvPowerSeries.coeff α D * (((β k : ℕ) : ℂ) + 1) = 0 := by
          have h4 : Complex.I * (MvPowerSeries.coeff α D * (((β k : ℕ) : ℂ) + 1)) = 0 := by
            linear_combination hE
          exact (mul_eq_zero.1 h4).resolve_left Complex.I_ne_zero
        exact (mul_eq_zero.1 h3).resolve_right hne
  intro α hα
  exact key (lvl α) α.degree α rfl rfl hα

end Virasoro.Sphere
