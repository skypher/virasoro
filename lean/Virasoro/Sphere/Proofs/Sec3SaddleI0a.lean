import Virasoro.Sphere.Proofs.Sec3SaddleValC

/-!
# Sphere paper Lemma 3.4(iii): substitution into `S⁽⁰⁾` (`sphere/paper.tex` l.694, l.800–808)

For a family `σ_m ∈ z^m ℂ[[z]]` the coefficient of `z^k` of a quadratic series
`∑ a_m σ_m + ∑ b_{m,n} σ_m σ_n` at `σ(z)` only involves `m, n ≤ k`.  `S⁽⁰⁾` and
`S̃⁽⁰⁾ = conj S⁽⁰⁾` are of this form.

Consumer: the saddle value `𝓘₀` in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

/-- `{μ : ℕ+ | μ ≤ k}`. -/
noncomputable def pIcc (k : ℕ) : Finset ℕ+ := (Icc 1 k).image Nat.toPNat'

theorem mem_pIcc (k : ℕ) (μ : ℕ+) : μ ∈ pIcc k ↔ (μ : ℕ) ≤ k := by
  rw [pIcc, mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have := mem_Icc.1 hn
    rw [Nat.toPNat'_coe, if_pos (by omega)]
    exact this.2
  · intro h
    exact ⟨μ, mem_Icc.2 ⟨μ.pos, h⟩, PNat.coe_toPNat' μ⟩

theorem sum_pIcc {M : Type*} [AddCommMonoid M] (k : ℕ) (g : ℕ+ → M) :
    ∑ μ ∈ pIcc k, g μ = ∑ n ∈ Icc 1 k, g n.toPNat' := by
  rw [pIcc, sum_image]
  intro x hx y hy h
  have hx' := mem_Icc.1 hx
  have hy' := mem_Icc.1 hy
  have := congrArg (fun t : ℕ+ => (t : ℕ)) h
  simp only [Nat.toPNat'_coe] at this
  rw [if_pos (by omega), if_pos (by omega)] at this
  exact this

theorem finsum_pnat (f : ℕ+ → ℂ) (k : ℕ) (hf : ∀ μ : ℕ+, k < (μ : ℕ) → f μ = 0) :
    ∑ᶠ μ, f μ = ∑ μ ∈ pIcc k, f μ := by
  apply finsum_eq_sum_of_support_subset
  intro μ hμ
  rw [Finset.mem_coe, mem_pIcc]
  by_contra h
  exact hμ (hf μ (by omega))

/-- `∑_m a_m σ_m + ∑_{m,n} b_{m,n} σ_m σ_n`. -/
noncomputable def Sq (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) : MvPowerSeries ℕ+ ℂ := fun α =>
  if α.degree = 1 then ∑ m ∈ α.support, a m
  else if α.degree = 2 then
    ∑ m ∈ α.support, ∑ n ∈ α.support,
      if α = Finsupp.single m 1 + Finsupp.single n 1 then b m n else 0
  else 0

theorem S0_eq_Sq : S0 = Sq Acoef (fun m n => (Bcoef m n : ℂ)) := rfl

theorem conj_S0_eq_Sq :
    conjSeries S0 = Sq (fun m => -Acoef m) (fun m n => (Bcoef m n : ℂ)) := by
  ext α
  rw [conjSeries, MvPowerSeries.coeff_map, coeff_eq_apply S0,
    coeff_eq_apply (Sq (fun m => -Acoef m) (fun m n => (Bcoef m n : ℂ))), S0, Sq]
  split_ifs with h1 h2
  · rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Acoef]
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_I, map_ratCast]
    ring
  · rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  · exact map_zero _

theorem coeff_X_mul_X (μ ν : ℕ+) (d : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff d ((MvPowerSeries.X μ : MvPowerSeries ℕ+ ℂ) * MvPowerSeries.X ν) =
      if d = Finsupp.single μ 1 + Finsupp.single ν 1 then 1 else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial,
    MvPowerSeries.coeff_monomial, mul_one]

/-- The coefficient of `z^k` in `∑ a_m σ_m + ∑ b_{m,n} σ_m σ_n`. -/
theorem coeff_subst_Sq (σ : ℕ+ → PowerSeries ℂ)
    (hord : ∀ m : ℕ+, (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σ m)
    (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (k : ℕ) :
    PowerSeries.coeff k (MvPowerSeries.subst σ (Sq a b)) =
      ∑ μ ∈ pIcc k, a μ * PowerSeries.coeff k (σ μ) +
        ∑ μ ∈ pIcc k, ∑ ν ∈ pIcc k, b μ ν * PowerSeries.coeff k (σ μ * σ ν) := by
  have hσ := hasSubst_of_dvd σ hord
  set p : MvPowerSeries ℕ+ ℂ := ∑ μ ∈ pIcc k, a μ • MvPowerSeries.X μ +
    ∑ μ ∈ pIcc k, ∑ ν ∈ pIcc k, b μ ν • (MvPowerSeries.X μ * MvPowerSeries.X ν) with hp
  have hsub : MvPowerSeries.subst σ p = ∑ μ ∈ pIcc k, a μ • σ μ +
      ∑ μ ∈ pIcc k, ∑ ν ∈ pIcc k, b μ ν • (σ μ * σ ν) := by
    rw [hp, ← MvPowerSeries.coe_substAlgHom hσ]
    simp only [map_add, map_sum, map_smul, map_mul, MvPowerSeries.substAlgHom_X]
  have hz : PowerSeries.coeff k (MvPowerSeries.subst σ (Sq a b - p)) = 0 := by
    apply coeff_subst_eq_zero σ hord
    intro d hd
    rw [map_sub, sub_eq_zero, hp, map_add]
    simp only [map_sum, MvPowerSeries.coeff_smul, smul_eq_mul, MvPowerSeries.coeff_X,
      coeff_X_mul_X]
    have hsupp : d.support ⊆ pIcc k := by
      intro s hs
      rw [mem_pIcc]
      calc (s : ℕ) ≤ d s * (s : ℕ) :=
            Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs))
        _ ≤ Finsupp.weight fockWeight d := by
            rw [Finsupp.weight_apply, Finsupp.sum]
            exact Finset.single_le_sum (f := fun i => d i • fockWeight i)
              (fun _ _ => Nat.zero_le _) hs
        _ ≤ k := hd
    rw [coeff_eq_apply, Sq]
    by_cases h1 : d.degree = 1
    · rw [if_pos h1]
      have h2 : ∀ μ ν : ℕ+, d ≠ Finsupp.single μ 1 + Finsupp.single ν 1 := by
        intro μ ν h
        rw [h, map_add, Finsupp.degree_single, Finsupp.degree_single] at h1
        omega
      simp only [if_neg (h2 _ _), mul_zero, sum_const_zero, add_zero]
      obtain ⟨s, rfl⟩ := exists_single_of_degree_one d h1
      rw [Finsupp.support_single _ one_ne_zero, sum_singleton, sum_eq_single s]
      · rw [if_pos rfl, mul_one]
      · intro μ _ hμ
        rw [if_neg (fun h => hμ (Finsupp.single_left_injective one_ne_zero h).symm), mul_zero]
      · intro h
        exact absurd (hsupp (by simp)) h
    · rw [if_neg h1]
      have h2 : ∀ μ : ℕ+, d ≠ Finsupp.single μ 1 := fun μ h =>
        h1 (by rw [h, Finsupp.degree_single])
      simp only [if_neg (h2 _), mul_zero, sum_const_zero, zero_add]
      by_cases h3 : d.degree = 2
      · rw [if_pos h3]
        have hmem : ∀ μ ν : ℕ+, d = Finsupp.single μ 1 + Finsupp.single ν 1 →
            μ ∈ d.support ∧ ν ∈ d.support := by
          intro μ ν h
          rw [h]
          simp [Finsupp.mem_support_iff]
        symm
        rw [← sum_subset hsupp (fun μ _ hμ => sum_eq_zero fun ν _ => by
          rw [if_neg (fun h => hμ (hmem μ ν h).1), mul_zero])]
        refine sum_congr rfl fun μ _ => ?_
        rw [← sum_subset hsupp (fun ν _ hν => by
          rw [if_neg (fun h => hν (hmem μ ν h).2), mul_zero])]
        refine sum_congr rfl fun ν _ => ?_
        split_ifs <;> simp
      · rw [if_neg h3]
        symm
        refine sum_eq_zero fun μ _ => sum_eq_zero fun ν _ => ?_
        rw [if_neg, mul_zero]
        intro h
        apply h3
        rw [h, map_add, Finsupp.degree_single, Finsupp.degree_single]
  have hsplit : Sq a b = p + (Sq a b - p) := by ring
  rw [hsplit, MvPowerSeries.subst_add hσ, map_add, hz, add_zero, hsub]
  simp only [map_add, map_sum, PowerSeries.coeff_smul, smul_eq_mul]

end Virasoro.Sphere
