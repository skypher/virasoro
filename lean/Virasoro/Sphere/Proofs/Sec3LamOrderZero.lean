import Virasoro.Sphere.Proofs.Sec3LamSeries
import Virasoro.Sphere.Proofs.Sec3SaddlePdeAll

/-!
# Order `λ⁰` of (3.3) and uniqueness for `L_k^{(0)}` (Lemma 3.3(ii))

sphere/paper.tex l.602–612.  Expanding (3.3) in `λ⁻¹` determines each `S^{(r)}_m` by induction
on `m`: in `L_k^{(0)}` the terms `-∑ nσ_n∂_n` and `-½∑(∂_n S^{(0)})∂_{k-n}` act on lower
levels, leaving the injective `𝒟_m(∞)`.  At order `λ⁰` the equation is solved by the quadratic
`S^{(0)}` of (3.4) (Lemma 3.4(i)).
-/

namespace Virasoro.Sphere

open Finset

local notation "KK" => RatFunc ℂ

/-- Uniqueness for `L_k^{(0)}` level by level (l.602–607): if the coefficients of `L_k^{(0)}D`
at level `m - k` vanish whenever `D` vanishes below level `m`, then `D` has no nonconstant
monomial. -/
theorem L0_unique_gen (D : MvPowerSeries ℕ+ ℂ)
    (h : ∀ m : ℕ, (∀ α : ℕ+ →₀ ℕ, α ≠ 0 → lvl α < m → MvPowerSeries.coeff α D = 0) →
      ∀ k : ℕ, 1 ≤ k → ∀ β : ℕ+ →₀ ℕ, lvl β + k = m → MvPowerSeries.coeff β (L0 k D) = 0) :
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
        have hE := h m (fun α' hα' hlt => ihm (lvl α') hlt α'.degree α' rfl rfl hα')
          (k : ℕ) hk1 β hlvl
        rw [L0] at hE
        simp only [map_sub, map_add, map_smul, smul_eq_mul, map_sum] at hE
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

theorem L0_eq (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) :
    L0 k T = Complex.I • pdA k T + shiftA k T - levelA T
      - (1 / 2 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) T := rfl

/-- Reflection `n ↦ k - n` of the sums over `1 ≤ n ≤ k - 1`. -/
theorem sum_reflect {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 (k - 1), f n (k - n) = ∑ n ∈ Icc 1 (k - 1), f (k - n) n := by
  refine Finset.sum_nbij' (fun n => k - n) (fun n => k - n) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    have := Finset.mem_Icc.1 hn
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro n hn
    have := Finset.mem_Icc.1 hn
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro n hn
    have := Finset.mem_Icc.1 hn
    show k - (k - n) = n
    omega
  · intro n hn
    have := Finset.mem_Icc.1 hn
    show k - (k - n) = n
    omega
  · intro n hn
    have := Finset.mem_Icc.1 hn
    have e : k - (k - n) = n := by omega
    show f n (k - n) = f (k - (k - n)) (k - n)
    rw [e]

theorem pdA_add {A : Type*} [CommRing A] (n : ℕ) (T T' : MvPowerSeries ℕ+ A) :
    pdA n (T + T') = pdA n T + pdA n T' := map_add _ _ _

theorem pdA_sub {A : Type*} [CommRing A] (n : ℕ) (T T' : MvPowerSeries ℕ+ A) :
    pdA n (T - T') = pdA n T - pdA n T' := map_sub _ _ _

theorem pdA_smul {A : Type*} [CommRing A] (n : ℕ) (z : A) (T : MvPowerSeries ℕ+ A) :
    pdA n (z • T) = z • pdA n T := Derivation.map_smul _ _ _

theorem pdA_C {A : Type*} [CommRing A] (n : ℕ) (z : A) :
    pdA n (MvPowerSeries.C z : MvPowerSeries ℕ+ A) = 0 := MvPowerSeries.pderiv_C

theorem shiftA_add {A : Type*} [CommRing A] (k : ℕ) (T T' : MvPowerSeries ℕ+ A) :
    shiftA k (T + T') = shiftA k T + shiftA k T' := by
  ext α
  simp only [coeff_shiftA, map_add, pdA_add, mul_add, Finset.sum_add_distrib]

theorem shiftA_smul {A : Type*} [CommRing A] (k : ℕ) (z : A) (T : MvPowerSeries ℕ+ A) :
    shiftA k (z • T) = z • shiftA k T := by
  ext α
  simp only [coeff_shiftA, pdA_smul, MvPowerSeries.coeff_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem levelA_add {A : Type*} [CommRing A] (T T' : MvPowerSeries ℕ+ A) :
    levelA (T + T') = levelA T + levelA T' := by
  ext α
  simp only [coeff_levelA, map_add, mul_add]

theorem levelA_smul {A : Type*} [CommRing A] (z : A) (T : MvPowerSeries ℕ+ A) :
    levelA (z • T) = z • levelA T := by
  ext α
  simp only [coeff_levelA, MvPowerSeries.coeff_smul]
  ring

/-- `L_k^{(0)}` as a linear map. -/
noncomputable def L0lin (k : ℕ) : MvPowerSeries ℕ+ ℂ →ₗ[ℂ] MvPowerSeries ℕ+ ℂ where
  toFun := L0 k
  map_add' T T' := by
    simp only [L0_eq, pdA_add, shiftA_add, levelA_add, mul_add, Finset.sum_add_distrib,
      smul_add]
    abel
  map_smul' z T := by
    simp only [L0_eq, pdA_smul, shiftA_smul, levelA_smul, mul_smul_comm, ← Finset.smul_sum,
      smul_sub, smul_add, RingHom.id_apply, smul_comm z]

theorem L0lin_apply (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) : L0lin k T = L0 k T := rfl

theorem coeff_zero_Sord {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) (r : ℕ) : MvPowerSeries.coeff 0 (Sord F r) = 0 := by
  rw [Sord_eq, coeff_zero_SL F (constantCoeff_wardSeries h)]
  rfl

theorem coeff_zero_S0 : MvPowerSeries.coeff 0 S0 = 0 := by
  show S0 0 = 0
  simp [S0]

section OrderZero

variable {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
  (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)

include h

/-- `S^{(0)}` is the quadratic series of (3.4). -/
theorem Sord_zero_eq : Sord F 0 = S0 := by
  set D := Sord F 0 - S0 with hD
  have hS : Sord F 0 = S0 + D := by rw [hD]; ring
  have hL : ∀ k : ℕ, 1 ≤ k →
      L0 k D = (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pdA n D * pdA (k - n) D := by
    intro k hk
    have e1 := order_zero_eq h k hk
    have e2 := pdeZero_S0 k hk
    rw [pdeZero_eq_pdeLam, pdeLam, zero_smul, sub_zero] at e1 e2
    rw [hS] at e1
    have hsym : ∑ n ∈ Icc 1 (k - 1), pdA n D * pdA (k - n) S0 =
        ∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) D := by
      rw [sum_reflect k fun a b => pdA a D * pdA b S0]
      exact Finset.sum_congr rfl fun n _ => mul_comm _ _
    have hexp : ∑ n ∈ Icc 1 (k - 1), pdA n (S0 + D) * pdA (k - n) (S0 + D) =
        ∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) S0 +
        (∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) D +
          ∑ n ∈ Icc 1 (k - 1), pdA n D * pdA (k - n) S0) +
        ∑ n ∈ Icc 1 (k - 1), pdA n D * pdA (k - n) D := by
      simp only [← Finset.sum_add_distrib, pdA_add]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hexp, hsym, pdA_add, shiftA_add, levelA_add] at e1
    rw [L0_eq]
    simp only [MvPowerSeries.smul_eq_C_mul] at e1 e2 ⊢
    have h4 : (MvPowerSeries.C (1 / 2 : ℂ) : MvPowerSeries ℕ+ ℂ) =
        MvPowerSeries.C (1 / 4 : ℂ) * 2 := by
      rw [show (2 : MvPowerSeries ℕ+ ℂ) = MvPowerSeries.C (2 : ℂ) from (map_ofNat _ 2).symm,
        ← map_mul]
      norm_num
    rw [h4]
    linear_combination e1 - e2
  have hD0 : MvPowerSeries.coeff 0 D = 0 := by
    rw [hD, map_sub, coeff_zero_Sord h, coeff_zero_S0, sub_zero]
  have hz : ∀ α : ℕ+ →₀ ℕ, α ≠ 0 → MvPowerSeries.coeff α D = 0 := by
    refine L0_unique_gen D fun m hm k hk β hβ => ?_
    classical
    rw [hL k hk, MvPowerSeries.coeff_smul, map_sum, Finset.sum_eq_zero, mul_zero]
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpβ : p.1 + p.2 = β := by simpa using hp
    have e := congrArg lvl hpβ
    rw [lvl_add] at e
    have hj1 : ((n.toPNat' : ℕ+) : ℕ) = n := PNat.toPNat'_coe hn'.1
    have l1 : lvl (p.1 + Finsupp.single n.toPNat' 1) < m := by
      rw [lvl_add, lvl_single, hj1]
      omega
    rw [coeff_pdA, hm _ (add_single_ne_zero _ _) l1, zero_mul, zero_mul]
  have hDz : D = 0 := by
    ext α
    by_cases hα : α = 0
    · rw [hα, hD0, map_zero]
    · rw [hz α hα, map_zero]
  rw [hS, hDz, add_zero]

end OrderZero

/-- Step (ii-a) of Lemma 3.3. -/
theorem sub_lam_order_zero : Stmt_sub_lam_order_zero := fun _ _ _ _ _ h => Sord_zero_eq h

end Virasoro.Sphere
