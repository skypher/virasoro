import Virasoro.Sphere.Proofs.Sec3C2WickTools
import Virasoro.Sphere.Proofs.Sec3ExtLinear
import Virasoro.Sphere.Proofs.Sec3ExpLog

/-!
# Lemma 3.7, Step 3: specialization at `W = W_*` (sphere paper)

sphere/paper.tex l.1128–1131.  A series in the `W_m` becomes a series in `t = x^{-1}` by
`W_m ↦ W_m t^m`: the coefficient of `t^d` is the sum of the coefficients of weight `d`.  For
`exp(c ∑_m W_{*,m} t^m)` this gives the powers of `f(x;W_*)/x = exp(-∑_m W_{*,m} x^{-m})`.
-/

namespace Virasoro.Sphere

open Finset PowerSeries

theorem mem_level_iff (d : ℕ) (β : ℕ+ →₀ ℕ) : β ∈ (finite_level d).toFinset ↔ lvl β = d := by
  rw [Set.Finite.mem_toFinset]
  rfl

/-- Sums over the pairs `(β₁, β₂)` with `|β₁| + |β₂| = d`, in two ways. -/
theorem sum_level_antidiagonal {M : Type*} [AddCommMonoid M] (d : ℕ)
    (G : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) → M) :
    ∑ β ∈ (finite_level d).toFinset, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, G p =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d, ∑ β1 ∈ (finite_level ab.1).toFinset,
        ∑ β2 ∈ (finite_level ab.2).toFinset, G (β1, β2) := by
  classical
  have h1 : ∑ β ∈ (finite_level d).toFinset, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, G p =
      ∑ p ∈ (finite_level_pair d).toFinset, G p := by
    rw [Finset.sum_comm' (s' := fun p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) => {p.1 + p.2})
      (t' := (finite_level_pair d).toFinset)]
    · exact Finset.sum_congr rfl fun p _ => Finset.sum_singleton _ _
    · intro β p
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.HasAntidiagonal.mem_antidiagonal,
        Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2.symm, ?_⟩
        rw [← h2, lvl_add] at h1
        exact h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1.symm⟩
        rw [h1, lvl_add]
        exact h2
  have h2 : ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d, ∑ β1 ∈ (finite_level ab.1).toFinset,
        ∑ β2 ∈ (finite_level ab.2).toFinset, G (β1, β2) =
      ∑ p ∈ (finite_level_pair d).toFinset, G p := by
    have e : ∀ ab : ℕ × ℕ, ∑ β1 ∈ (finite_level ab.1).toFinset,
        ∑ β2 ∈ (finite_level ab.2).toFinset, G (β1, β2) =
        ∑ p ∈ (finite_level ab.1).toFinset ×ˢ (finite_level ab.2).toFinset, G p := fun ab =>
      (Finset.sum_product _ _ _).symm
    rw [Finset.sum_congr rfl fun ab _ => e ab,
      Finset.sum_comm' (s' := fun p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ) => {(lvl p.1, lvl p.2)})
        (t' := (finite_level_pair d).toFinset)]
    · exact Finset.sum_congr rfl fun p _ => Finset.sum_singleton _ _
    · intro ab p
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.HasAntidiagonal.mem_antidiagonal,
        Finset.mem_singleton, Finset.mem_product]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨Prod.ext h2.symm h3.symm, ?_⟩
        rw [h2, h3]
        exact h1
      · rintro ⟨h1, h2⟩
        subst h1
        exact ⟨h2, rfl, rfl⟩
  rw [h1, h2]

/-- `W_m ↦ W_m t^m`: the coefficient of `t^d` is the sum of the coefficients of weight `d`. -/
noncomputable def levS (Φ : MvPowerSeries ℕ+ ℂ) : PowerSeries ℂ :=
  mk fun d => ∑ β ∈ (finite_level d).toFinset, MvPowerSeries.coeff β Φ

theorem coeff_levS (Φ : MvPowerSeries ℕ+ ℂ) (d : ℕ) :
    coeff d (levS Φ) = ∑ β ∈ (finite_level d).toFinset, MvPowerSeries.coeff β Φ := by
  rw [levS, coeff_mk]

theorem levS_mul (Φ Ψ : MvPowerSeries ℕ+ ℂ) : levS (Φ * Ψ) = levS Φ * levS Ψ := by
  classical
  ext d
  rw [coeff_levS, PowerSeries.coeff_mul]
  simp only [coeff_levS, MvPowerSeries.coeff_mul, Finset.sum_mul_sum]
  exact sum_level_antidiagonal d fun p => MvPowerSeries.coeff p.1 Φ * MvPowerSeries.coeff p.2 Ψ

theorem level_zero_eq : (finite_level 0).toFinset = {(0 : ℕ+ →₀ ℕ)} := by
  ext β
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
  constructor
  · exact lvl_eq_zero
  · rintro rfl
    exact map_zero _

theorem levS_one : levS 1 = 1 := by
  classical
  ext d
  rw [coeff_levS, PowerSeries.coeff_one]
  simp only [MvPowerSeries.coeff_one]
  rw [Finset.sum_ite_eq']
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, if_pos (by rw [level_zero_eq]; exact Finset.mem_singleton_self _)]
  · rw [if_neg hd, if_neg]
    intro h
    apply hd
    have h1 : lvl (0 : ℕ+ →₀ ℕ) = d := (mem_level_iff d 0).mp h
    rw [← h1]
    exact map_zero _

theorem coeff_X_mul_derivative (f : PowerSeries ℂ) (d : ℕ) :
    coeff d (X * derivative ℂ f) = (d : ℂ) * coeff d f := by
  cases d with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem levS_levelA (Φ : MvPowerSeries ℕ+ ℂ) : levS (levelA Φ) = X * derivative ℂ (levS Φ) := by
  ext d
  rw [coeff_X_mul_derivative, coeff_levS, coeff_levS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have h1 : lvl β = d := (mem_level_iff d β).mp hβ
  rw [coeff_levelA, h1]

theorem levS_linSeries (c : ℕ → ℂ) :
    levS (linSeries c) = mk fun d => if d = 0 then 0 else c d := by
  classical
  ext d
  rw [coeff_levS, coeff_mk]
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, level_zero_eq, Finset.sum_singleton]
    exact linSeries_zero c
  · rw [if_neg hd]
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    rw [Finset.sum_eq_single (Finsupp.single d.toPNat' 1)]
    · show linSeries c (Finsupp.single d.toPNat' 1) = c d
      rw [linSeries_single, PNat.toPNat'_coe hd1]
    · intro β hβ hne
      have h1 : lvl β = d := (mem_level_iff d β).mp hβ
      show linSeries c β = 0
      by_cases hdeg : β.degree = 1
      · obtain ⟨m, rfl⟩ := exists_single_of_degree_one β hdeg
        exfalso
        apply hne
        rw [lvl_single] at h1
        congr 1
        apply PNat.eq
        rw [PNat.toPNat'_coe hd1]
        exact h1
      · exact linSeries_of_degree_ne c β hdeg
    · intro hnot
      exfalso
      apply hnot
      rw [mem_level_iff]
      rw [lvl_single, PNat.toPNat'_coe hd1]

/-! ### The powers of `f(x;W_*)/x` -/

/-- `W_{*,m} = binom(2m,m)/(m 4^m)` for a natural number `m ≥ 1`. -/
noncomputable def wN (m : ℕ) : ℂ := (halfBinom m : ℂ) / (m : ℂ)

/-- `exp(c ∑_m W_{*,m} t^m)`; with `t = x^{-1}`, `(f(x;W_*)/x)^p` is `Est (-p)`. -/
noncomputable def Est (c : ℂ) : PowerSeries ℂ := levS (mexp (linSeries fun m => c * wN m))

/-- `∑_m m W_{*,m} t^m = (1-t)^{-1/2} - 1` (sphere/paper.tex l.1128). -/
noncomputable def Hst : PowerSeries ℂ := mk fun m => (m : ℂ) * wN m

theorem constantCoeff_Est (c : ℂ) : constantCoeff (Est c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Est, coeff_levS, level_zero_eq, Finset.sum_singleton,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_mexp (constantCoeff_linSeries _)]

theorem Est_add (c c' : ℂ) : Est (c + c') = Est c * Est c' := by
  have e : (linSeries fun m => (c + c') * wN m) =
      (linSeries fun m => c * wN m) + linSeries fun m => c' * wN m := by
    ext α
    rw [map_add, coeff_eq_apply, coeff_eq_apply, coeff_eq_apply]
    unfold linSeries
    split_ifs
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    · rw [add_zero]
  rw [Est, e, mexp_add (by rw [constantCoeff_linSeries]; exact IsNilpotent.zero)
    (by rw [constantCoeff_linSeries]; exact IsNilpotent.zero), levS_mul]
  rfl

theorem Est_zero : Est 0 = 1 := by
  have e : (linSeries fun m => (0 : ℂ) * wN m) = 0 := by
    ext α
    rw [coeff_eq_apply, map_zero]
    unfold linSeries
    split_ifs
    · exact Finset.sum_eq_zero fun m _ => by ring
    · rfl
  rw [Est, e, mexp_zero, levS_one]

/-- `t ∂_t exp(c L) = c (t L') exp(c L)` for `L = ∑_m W_{*,m} t^m`. -/
theorem Est_deriv (c : ℂ) : X * derivative ℂ (Est c) = C c * Hst * Est c := by
  have hL0 := constantCoeff_linSeries fun m => c * wN m
  have h1 : levelA (mexp (linSeries fun m => c * wN m)) =
      mexp (linSeries fun m => c * wN m) * levelA (linSeries fun m => c * wN m) :=
    levelA_of_pd _ _ _ fun j => pderiv_mexp (by rw [hL0]; exact IsNilpotent.zero) _
  have h2 : levS (levelA (linSeries fun m => c * wN m)) = C c * Hst := by
    rw [levelA_linSeries, levS_linSeries]
    ext d
    rw [coeff_mk, coeff_C_mul, Hst, coeff_mk]
    split_ifs with h
    · subst h
      simp
    · ring
  rw [Est, ← levS_levelA, h1, levS_mul, h2]
  ring

/-- The coefficients of `exp(c L)`. -/
theorem coeff_Est (c : ℂ) (d : ℕ) :
    coeff d (Est c) = ∑ β ∈ (finite_level d).toFinset, linExpCoef (fun m => c * wN m) β := by
  rw [Est, coeff_levS]
  exact Finset.sum_congr rfl fun β _ => coeff_mexp_linSeries _ β

end Virasoro.Sphere
