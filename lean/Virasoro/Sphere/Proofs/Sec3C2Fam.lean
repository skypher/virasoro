import Virasoro.Sphere.Proofs.Sec3C2Stacked
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Lemma 3.7, Step 3: `D_k` on families of coefficients (sphere paper)

sphere/paper.tex l.1111–1127.  A formal series in the variables `W_m` with coefficients in an
additive monoid `E` is the family `β ↦ Φ_β` of its coefficients.  `D_k = ∂_{W_k} + ∑_m m W_m
∂_{W_{m+k}}` acts on families by finitely many terms for each `β`.  For coefficients in a ring
(not necessarily commutative) `D_k` is a derivation of the product of series.  The
degree-triangular uniqueness of l.1123–1127 is `fam_unique`.
-/

namespace Virasoro.Sphere

open Finset MvPolynomial

section Fam

variable {E : Type*} [AddCommMonoid E]

/-- `∂_{W_i}` on families: `(∂_i Φ)_β = (β_i + 1) Φ_{β + e_i}`. -/
noncomputable def pdN (i : ℕ+) (Φ : (ℕ+ →₀ ℕ) → E) : (ℕ+ →₀ ℕ) → E :=
  fun β => (β i + 1) • Φ (β + Finsupp.single i 1)

/-- `D_k = ∂_{W_k} + ∑_{m≥1} m W_m ∂_{W_{m+k}}` on families (sphere/paper.tex l.1075–1076). -/
noncomputable def DkF (k : ℕ) (Φ : (ℕ+ →₀ ℕ) → E) : (ℕ+ →₀ ℕ) → E :=
  fun β => pdN k.toPNat' Φ β +
    ∑ m ∈ β.support, (m : ℕ) • pdN ((m : ℕ) + k).toPNat' Φ (β - Finsupp.single m 1)

theorem DkF_map {E' : Type*} [AddCommMonoid E'] (φ : E →+ E') (k : ℕ) (Φ : (ℕ+ →₀ ℕ) → E)
    (β : ℕ+ →₀ ℕ) : φ (DkF k Φ β) = DkF k (fun β => φ (Φ β)) β := by
  simp only [DkF, pdN, map_add, map_sum, map_nsmul]

theorem DkF_congr (k : ℕ) {Φ Φ' : (ℕ+ →₀ ℕ) → E} (β : ℕ+ →₀ ℕ)
    (h : ∀ δ, lvl δ = lvl β + k → Φ δ = Φ' δ) (hk : 1 ≤ k) : DkF k Φ β = DkF k Φ' β := by
  have hjk : ∀ j : ℕ, 1 ≤ j → ((j.toPNat' : ℕ+) : ℕ) = j := fun j hj => PNat.toPNat'_coe hj
  unfold DkF pdN
  congr 1
  · rw [h _ (by rw [lvl_add, lvl_single, hjk k hk])]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [h _ (by
      have e := congrArg lvl (sub_add_single hm)
      rw [lvl_add, lvl_single] at e
      rw [lvl_add, lvl_single, hjk _ (by omega)]
      omega)]

end Fam

/-- The coefficients of `D_k g` for a polynomial `g` in the `W_m`. -/
theorem coeff_Dop_eq (k : ℕ) (g : Fock) (γ : ℕ+ →₀ ℕ) :
    coeff γ (Dop k g) = DkF k (fun β => coeff β g) γ := by
  rw [coeff_Dop, DkF, add_comm]
  simp only [pdN, coeff_pderiv, nsmul_eq_mul]
  congr 1
  · push_cast
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring

/-! ### Degree-triangular uniqueness -/

/-- The degree-triangular uniqueness of l.1123–1127 for scalar families.  `Z i w` marks the
components (index `i`, `W`-weight `w`) that are claimed to vanish.  If the weight-`0` component
vanishes, and `D_k` of each marked component vanishes as soon as the marked components of lower
weight do, then all marked components vanish: the lowest nonzero positive `W`-weight would lie
in `⋂_k ker D_k`. -/
theorem fam_unique {ι : Type*} (d : ι → (ℕ+ →₀ ℕ) → ℂ) (Z : ι → ℕ → Prop)
    (h0 : ∀ i, Z i 0 → d i 0 = 0)
    (hD : ∀ i w, Z i w → ∀ k : ℕ, 1 ≤ k → ∀ δ : ℕ+ →₀ ℕ, lvl δ + k = w →
      (∀ i' w', w' < w → Z i' w' → ∀ β, lvl β = w' → d i' β = 0) → DkF k (d i) δ = 0) :
    ∀ w i, Z i w → ∀ β, lvl β = w → d i β = 0 := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro i hZ β hβ
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rw [lvl_eq_zero hβ]
      exact h0 i hZ
    set a : Fock := ∑ β' ∈ (finite_level w).toFinset, monomial β' (d i β') with ha
    have hacoeff : ∀ β' : ℕ+ →₀ ℕ, coeff β' a = if lvl β' = w then d i β' else 0 := by
      intro β'
      rw [ha, coeff_sum]
      simp only [coeff_monomial]
      rw [Finset.sum_ite_eq']
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have halev : a ∈ levelSub w := by
      intro β' hβ'
      rw [hacoeff] at hβ'
      by_contra hne
      exact hβ' (if_neg hne)
    have hDa : ∀ k : ℕ, 1 ≤ k → Dop k a = 0 := by
      intro k hk
      ext δ
      rw [coeff_zero]
      by_cases hδ : lvl δ + k = w
      · rw [coeff_Dop_eq, DkF_congr k δ (Φ' := d i) (fun δ' hδ' => by
          show coeff δ' a = d i δ'
          rw [hacoeff, if_pos (by omega)]) hk]
        exact hD i w hZ k hk δ hδ fun i' w' hw' hZ' β' hβ' => ih w' hw' i' hZ' β' hβ'
      · exact coeff_Dop_of_level k hk halev δ hδ
    have ha0 := Dop_injective_level hw halev hDa
    have h1 := hacoeff β
    rw [ha0, coeff_zero, if_pos hβ] at h1
    exact h1.symm

/-! ### `D_k` is a derivation of the product of series -/

section Leibniz

variable {R : Type*} [Semiring R]

theorem sum_antidiagonal_swap' {M : Type*} [AddCommMonoid M] (β : ℕ+ →₀ ℕ)
    (G : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) → M) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, G p = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, G p.swap := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    rw [Prod.fst_swap, Prod.snd_swap, add_comm]
    exact hp
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    rw [Prod.fst_swap, Prod.snd_swap, add_comm]
    exact hp
  · intro p _
    exact Prod.swap_swap p
  · intro p _
    exact Prod.swap_swap p
  · intro p _
    rw [Prod.swap_swap]

/-- The pairs `(a, b)` with `a + b = β + e_i` and `a_i ≥ 1` are the `(a' + e_i, b)` with
`a' + b = β`. -/
theorem sum_antidiagonal_single_left {M : Type*} [AddCommMonoid M] (i : ℕ+) (β : ℕ+ →₀ ℕ)
    (F : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) → M) :
    Finset.sum (Finset.HasAntidiagonal.antidiagonal (β + Finsupp.single i 1))
        (fun p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) =>
          if p.1 i = 0 then 0 else F (p.1 - Finsupp.single i 1, p.2)) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, F q := by
  classical
  have hsub : ∀ a : ℕ+ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a :=
    fun a ha => sub_add_single (Finsupp.mem_support_iff.mpr ha)
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1 - Finsupp.single i 1, p.2)) ?_ ?_ ?_ ?_
  · intro p hp hne
    have hpi : p.1 i ≠ 0 := fun h => hne (if_pos h)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    have e : p.1 - Finsupp.single i 1 + p.2 + Finsupp.single i 1 = β + Finsupp.single i 1 := by
      rw [add_right_comm, hsub _ hpi, hp]
    exact add_right_cancel e
  · intro p _ hne p' _ hne' h
    have hpi : p.1 i ≠ 0 := fun h => hne (if_pos h)
    have hpi' : p'.1 i ≠ 0 := fun h => hne' (if_pos h)
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    refine Prod.ext ?_ h2
    rw [← hsub _ hpi, ← hsub _ hpi', h1]
  · intro q hq hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hqi : (q.1 + Finsupp.single i 1 : ℕ+ →₀ ℕ) i ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    refine ⟨(q.1 + Finsupp.single i 1, q.2), ?_, ?_, ?_⟩
    · rw [Finset.HasAntidiagonal.mem_antidiagonal]
      show q.1 + Finsupp.single i 1 + q.2 = β + Finsupp.single i 1
      rw [add_right_comm, hq]
    · show (if (q.1 + Finsupp.single i 1 : ℕ+ →₀ ℕ) i = 0 then 0
        else F (q.1 + Finsupp.single i 1 - Finsupp.single i 1, q.2)) ≠ 0
      rw [if_neg hqi, add_tsub_cancel_right]
      exact hne
    · show (q.1 + Finsupp.single i 1 - Finsupp.single i 1, q.2) = q
      rw [add_tsub_cancel_right]
  · intro p _ hne
    have hpi : p.1 i ≠ 0 := fun h => hne (if_pos h)
    rw [if_neg hpi]

theorem sum_antidiagonal_single_right {M : Type*} [AddCommMonoid M] (i : ℕ+) (β : ℕ+ →₀ ℕ)
    (F : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) → M) :
    Finset.sum (Finset.HasAntidiagonal.antidiagonal (β + Finsupp.single i 1))
        (fun p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) =>
          if p.2 i = 0 then 0 else F (p.1, p.2 - Finsupp.single i 1)) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, F q := by
  rw [sum_antidiagonal_swap', sum_antidiagonal_swap' β F]
  exact sum_antidiagonal_single_left i β fun q => F q.swap

/-- `∂_{W_i}` on series. -/
noncomputable def pdS (i : ℕ+) (Φ : MvPowerSeries ℕ+ R) : MvPowerSeries ℕ+ R := pdN i Φ

/-- `D_k` on series. -/
noncomputable def DkS (k : ℕ) (Φ : MvPowerSeries ℕ+ R) : MvPowerSeries ℕ+ R := DkF k Φ

theorem coeff_pdN (i : ℕ+) (Φ : MvPowerSeries ℕ+ R) (β : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff β (pdS i Φ) =
      (β i + 1) • MvPowerSeries.coeff (β + Finsupp.single i 1) Φ := rfl

theorem coeff_DkF (k : ℕ) (Φ : MvPowerSeries ℕ+ R) (β : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff β (DkS k Φ) =
      MvPowerSeries.coeff β (pdS k.toPNat' Φ) +
        ∑ m ∈ β.support, (m : ℕ) • MvPowerSeries.coeff (β - Finsupp.single m 1)
          (pdS ((m : ℕ) + k).toPNat' Φ) := rfl

/-- `∂_{W_i}` is a derivation. -/
theorem pdS_mul (i : ℕ+) (Φ Ψ : MvPowerSeries ℕ+ R) :
    (pdS i (Φ * Ψ)) =
      (pdS i Φ) * Ψ + Φ * (pdS i Ψ) := by
  classical
  ext β
  rw [map_add, coeff_pdN, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, Finset.smul_sum]
  simp only [coeff_pdN]
  rw [← sum_antidiagonal_single_left i β fun q =>
      ((q.1 i + 1) • MvPowerSeries.coeff (q.1 + Finsupp.single i 1) Φ) *
        MvPowerSeries.coeff q.2 Ψ,
    ← sum_antidiagonal_single_right i β fun q =>
      MvPowerSeries.coeff q.1 Φ *
        ((q.2 i + 1) • MvPowerSeries.coeff (q.2 + Finsupp.single i 1) Ψ),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hpi : p.1 i + p.2 i = β i + 1 := by
    have h := congrArg (fun f : ℕ+ →₀ ℕ => f i) hp
    simpa using h
  have e1 : (if p.1 i = 0 then (0 : R) else
      ((p.1 - Finsupp.single i 1 : ℕ+ →₀ ℕ) i + 1) •
          MvPowerSeries.coeff (p.1 - Finsupp.single i 1 + Finsupp.single i 1) Φ *
        MvPowerSeries.coeff p.2 Ψ) =
      (p.1 i) • (MvPowerSeries.coeff p.1 Φ * MvPowerSeries.coeff p.2 Ψ) := by
    by_cases h : p.1 i = 0
    · rw [if_pos h, h, zero_smul]
    · rw [if_neg h, sub_add_single (Finsupp.mem_support_iff.mpr h), smul_mul_assoc]
      congr 1
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
  have e2 : (if p.2 i = 0 then (0 : R) else
      MvPowerSeries.coeff p.1 Φ * (((p.2 - Finsupp.single i 1 : ℕ+ →₀ ℕ) i + 1) •
          MvPowerSeries.coeff (p.2 - Finsupp.single i 1 + Finsupp.single i 1) Ψ)) =
      (p.2 i) • (MvPowerSeries.coeff p.1 Φ * MvPowerSeries.coeff p.2 Ψ) := by
    by_cases h : p.2 i = 0
    · rw [if_pos h, h, zero_smul]
    · rw [if_neg h, sub_add_single (Finsupp.mem_support_iff.mpr h), mul_smul_comm]
      congr 1
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
  rw [e1, e2, ← add_smul, hpi]

/-- `D_k` is a derivation of the product of series in the `W_m` (coefficients in a ring that
need not be commutative). -/
theorem DkS_mul (k : ℕ) (Φ Ψ : MvPowerSeries ℕ+ R) :
    (DkS k (Φ * Ψ)) =
      (DkS k Φ) * Ψ + Φ * (DkS k Ψ) := by
  classical
  ext β
  rw [coeff_DkF]
  simp only [pdS_mul, map_add]
  rw [MvPowerSeries.coeff_mul (φ := (DkS k Φ)),
    MvPowerSeries.coeff_mul (ψ := (DkS k Ψ))]
  simp only [coeff_DkF, add_mul, mul_add, Finset.sum_add_distrib, smul_add]
  have hA : ∑ m ∈ β.support, (m : ℕ) • MvPowerSeries.coeff (β - Finsupp.single m 1)
        ((pdS ((m : ℕ) + k).toPNat' Φ) * Ψ) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, (∑ m ∈ p.1.support, (m : ℕ) •
        MvPowerSeries.coeff (p.1 - Finsupp.single m 1)
          (pdS ((m : ℕ) + k).toPNat' Φ)) * MvPowerSeries.coeff p.2 Ψ := by
    have hm : ∀ m ∈ β.support, (m : ℕ) • MvPowerSeries.coeff (β - Finsupp.single m 1)
        ((pdS ((m : ℕ) + k).toPNat' Φ) * Ψ) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, (if p.1 m = 0 then (0 : R) else
          (m : ℕ) • (MvPowerSeries.coeff (p.1 - Finsupp.single m 1)
            (pdS ((m : ℕ) + k).toPNat' Φ) *
              MvPowerSeries.coeff p.2 Ψ)) := by
      intro m hm
      have h := sum_antidiagonal_single_left m (β - Finsupp.single m 1) fun q =>
        (m : ℕ) • (MvPowerSeries.coeff q.1 (pdS ((m : ℕ) + k).toPNat' Φ) *
          MvPowerSeries.coeff q.2 Ψ)
      rw [sub_add_single hm] at h
      rw [h, MvPowerSeries.coeff_mul, Finset.smul_sum]
    rw [Finset.sum_congr rfl hm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hsub : p.1.support ⊆ β.support := support_subset_of_add (by rw [add_comm]; exact hp)
    rw [Finset.sum_mul, ← Finset.sum_subset hsub (fun m _ hm => by
      rw [if_pos (Finsupp.notMem_support_iff.mp hm)])]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_neg (Finsupp.mem_support_iff.mp hm), smul_mul_assoc]
  have hB : ∑ m ∈ β.support, (m : ℕ) • MvPowerSeries.coeff (β - Finsupp.single m 1)
        (Φ * (pdS ((m : ℕ) + k).toPNat' Ψ)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, MvPowerSeries.coeff p.1 Φ * (∑ m ∈ p.2.support, (m : ℕ) •
        MvPowerSeries.coeff (p.2 - Finsupp.single m 1)
          (pdS ((m : ℕ) + k).toPNat' Ψ)) := by
    have hm : ∀ m ∈ β.support, (m : ℕ) • MvPowerSeries.coeff (β - Finsupp.single m 1)
        (Φ * (pdS ((m : ℕ) + k).toPNat' Ψ)) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, (if p.2 m = 0 then (0 : R) else
          (m : ℕ) • (MvPowerSeries.coeff p.1 Φ *
            MvPowerSeries.coeff (p.2 - Finsupp.single m 1)
              (pdS ((m : ℕ) + k).toPNat' Ψ))) := by
      intro m hm
      have h := sum_antidiagonal_single_right m (β - Finsupp.single m 1) fun q =>
        (m : ℕ) • (MvPowerSeries.coeff q.1 Φ *
          MvPowerSeries.coeff q.2 (pdS ((m : ℕ) + k).toPNat' Ψ))
      rw [sub_add_single hm] at h
      rw [h, MvPowerSeries.coeff_mul, Finset.smul_sum]
    rw [Finset.sum_congr rfl hm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hsub : p.2.support ⊆ β.support := support_subset_of_add hp
    rw [Finset.mul_sum, ← Finset.sum_subset hsub (fun m _ hm => by
      rw [if_pos (Finsupp.notMem_support_iff.mp hm)])]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_neg (Finsupp.mem_support_iff.mp hm), mul_smul_comm]
  rw [hA, hB, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  abel

end Leibniz

end Virasoro.Sphere
