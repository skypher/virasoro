import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# The exponential of a formal series (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.637–650: the integrand of the algebraic Gaussian expectation is
`exp(λ²S(z^•u/λ) + λ²S̃(ū/λ))`.  For a series `f` in any set of variables over a `ℚ`-algebra,
with nilpotent constant term, `mexp f = ∑_k f^k/k!` is the substitution of `f` into the
exponential series.  Proved here: the chain rule `∂_i e^f = e^f ∂_i f`, `e^{f+g} = e^f e^g`,
`e^c = ∑_k c^k/k!` for a nilpotent constant `c`, and compatibility with substitutions and with
changes of the coefficient ring.
-/

namespace Virasoro.Sphere

open Finset

section Chain

variable {σ : Type*} {A : Type*} [CommRing A]

theorem coeff_subst_truncG {g : MvPowerSeries σ A} (hg : MvPowerSeries.constantCoeff g = 0)
    (f : PowerSeries A) (e : σ →₀ ℕ) (N : ℕ) (hN : e.degree < N) :
    MvPowerSeries.coeff e (f.subst g) =
      MvPowerSeries.coeff e ((↑(PowerSeries.trunc N f) : PowerSeries A).subst g) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun d => ?_
  rcases lt_or_ge d N with hd | hd
  · rw [PowerSeries.coeff_coe_trunc_of_lt hd]
  · have h0 : MvPowerSeries.coeff e (g ^ d) = 0 := by
      refine MvPowerSeries.coeff_of_lt_order ?_
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg)
      exact_mod_cast lt_of_lt_of_le hN hd
    rw [h0, smul_zero, smul_zero]

/-- The chain rule `∂_i (f(g)) = f'(g) ∂_i g` for a series `g` with zero constant term. -/
theorem pderiv_substG {g : MvPowerSeries σ A} (hg : MvPowerSeries.constantCoeff g = 0)
    (f : PowerSeries A) (i : σ) :
    MvPowerSeries.pderiv A i (f.subst g) =
      (PowerSeries.derivative A f).subst g * MvPowerSeries.pderiv A i g := by
  classical
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  ext e
  have h1 : (e + Finsupp.single i 1).degree < e.degree + 2 := by
    rw [map_add, Finsupp.degree_single]
    omega
  rw [MvPowerSeries.coeff_pderiv, coeff_subst_truncG hg f _ (e.degree + 2) h1,
    ← MvPowerSeries.coeff_pderiv, PowerSeries.subst_coe hs, Derivation.comp_aeval_eq,
    smul_eq_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  congr 1
  have hp' : p.1 + p.2 = e := by simpa using hp
  have h2 : p.1.degree < e.degree + 1 := by
    have := congrArg Finsupp.degree hp'
    rw [map_add] at this
    omega
  rw [coeff_subst_truncG hg _ p.1 (e.degree + 1) h2, PowerSeries.trunc_derivative,
    PowerSeries.subst_coe hs]

/-- Substitution into a substituted one-variable series. -/
theorem subst_psubst {τ υ : Type*} {a : MvPowerSeries τ A} (ha : PowerSeries.HasSubst a)
    {b : τ → MvPowerSeries υ A} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries A) :
    MvPowerSeries.subst b (f.subst a) = f.subst (MvPowerSeries.subst b a) :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb f

end Chain

section Exp

variable {σ : Type*} {A : Type*} [CommRing A] [Algebra ℚ A]

/-- A series over a `ℚ`-algebra is determined by its constant term and its logarithmic
derivatives. -/
theorem ext_of_pderiv {Φ Φ' : MvPowerSeries σ A} (h : σ → MvPowerSeries σ A)
    (h0 : MvPowerSeries.constantCoeff Φ = MvPowerSeries.constantCoeff Φ')
    (hΦ : ∀ i, MvPowerSeries.pderiv A i Φ = Φ * h i)
    (hΦ' : ∀ i, MvPowerSeries.pderiv A i Φ' = Φ' * h i) : Φ = Φ' := by
  classical
  have key : ∀ N : ℕ, ∀ e : σ →₀ ℕ, e.degree = N →
      MvPowerSeries.coeff e Φ = MvPowerSeries.coeff e Φ' := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro e he
      by_cases h00 : e = 0
      · rw [h00]
        exact h0
      · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact h00 (Finsupp.ext hcon)
        set e' := e - Finsupp.single i 1 with he'
        have hee : e' + Finsupp.single i 1 = e := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp only [he', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]
            omega
          · simp [he', Finsupp.single_eq_of_ne hj]
        have hdeg : e'.degree < N := by
          have := congrArg Finsupp.degree hee
          rw [map_add, Finsupp.degree_single] at this
          omega
        have k1 := congrArg (MvPowerSeries.coeff e') (hΦ i)
        have k2 := congrArg (MvPowerSeries.coeff e') (hΦ' i)
        rw [MvPowerSeries.coeff_pderiv, hee, MvPowerSeries.coeff_mul] at k1 k2
        have k3 : MvPowerSeries.coeff e Φ * ((e' i : A) + 1) =
            MvPowerSeries.coeff e Φ' * ((e' i : A) + 1) := by
          rw [k1, k2]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp' : p.1 + p.2 = e' := by simpa using hp
          have h2 : p.1.degree < N := by
            have := congrArg Finsupp.degree hp'
            rw [map_add] at this
            omega
          rw [ih _ h2 p.1 rfl]
        have hu : ((e' i : A) + 1) * algebraMap ℚ A (((e' i : ℚ) + 1)⁻¹) = 1 := by
          have h3 : ((e' i : A) + 1) = algebraMap ℚ A ((e' i : ℚ) + 1) := by simp
          rw [h3, ← map_mul, mul_inv_cancel₀ (by positivity), map_one]
        calc MvPowerSeries.coeff e Φ
            = MvPowerSeries.coeff e Φ * ((e' i : A) + 1) *
                algebraMap ℚ A (((e' i : ℚ) + 1)⁻¹) := by rw [mul_assoc, hu, mul_one]
          _ = MvPowerSeries.coeff e Φ' := by rw [k3, mul_assoc, hu, mul_one]
  ext e
  exact key _ e rfl

/-- `e^f`, the substitution of `f` into the exponential series. -/
noncomputable def mexp (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.exp A).subst f

theorem constantCoeff_mexp {g : MvPowerSeries σ A} (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (mexp g) = 1 := by
  rw [mexp, PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    rw [map_pow, hg, zero_pow hd, smul_zero]

theorem pderiv_mexp_zero {g : MvPowerSeries σ A} (hg : MvPowerSeries.constantCoeff g = 0)
    (i : σ) : MvPowerSeries.pderiv A i (mexp g) = mexp g * MvPowerSeries.pderiv A i g := by
  rw [mexp, pderiv_substG hg, PowerSeries.derivative_exp]

theorem mexp_add2 :
    mexp (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) =
      mexp (MvPowerSeries.X 0) * mexp (MvPowerSeries.X 1) := by
  have c0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
  have c1 : ∀ j : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.X j : MvPowerSeries (Fin 2) A) = 0 := fun j => by simp
  refine ext_of_pderiv (fun _ => 1) ?_ (fun i => ?_) (fun i => ?_)
  · rw [constantCoeff_mexp c0, map_mul, constantCoeff_mexp (c1 0), constantCoeff_mexp (c1 1),
      mul_one]
  · rw [pderiv_mexp_zero c0, map_add]
    fin_cases i <;> simp
  · rw [Derivation.leibniz, pderiv_mexp_zero (c1 0), pderiv_mexp_zero (c1 1)]
    fin_cases i <;> simp [mul_comm]

/-- `e^{f+g} = e^f e^g`. -/
theorem mexp_add {f g : MvPowerSeries σ A} (hf : IsNilpotent (MvPowerSeries.constantCoeff f))
    (hg : IsNilpotent (MvPowerSeries.constantCoeff g)) : mexp (f + g) = mexp f * mexp g := by
  have ha : MvPowerSeries.HasSubst (![f, g] : Fin 2 → MvPowerSeries σ A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by
      fin_cases s
      · simpa using hf
      · simpa using hg
  have hX : ∀ j : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X j : MvPowerSeries (Fin 2) A) :=
    fun j => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hs0 : PowerSeries.HasSubst
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h := congrArg (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries σ A))
    (mexp_add2 (A := A))
  rw [mexp, subst_psubst hs0 ha, MvPowerSeries.subst_mul ha, mexp, mexp, subst_psubst (hX 0) ha,
    subst_psubst (hX 1) ha, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha,
    MvPowerSeries.subst_X ha] at h
  simpa [mexp] using h

/-- `e^c = ∑_k c^k/k!` for a nilpotent constant `c`. -/
theorem mexp_C {c : A} (hc : IsNilpotent c) :
    mexp (MvPowerSeries.C c : MvPowerSeries σ A) = MvPowerSeries.C (IsNilpotent.exp c) := by
  classical
  obtain ⟨k, hk⟩ := hc
  have hs : PowerSeries.HasSubst (MvPowerSeries.C c : MvPowerSeries σ A) := by
    rw [PowerSeries.HasSubst, MvPowerSeries.constantCoeff_C]
    exact ⟨k, hk⟩
  ext e
  rw [mexp, PowerSeries.coeff_subst hs, MvPowerSeries.coeff_C, IsNilpotent.exp_eq_sum hk]
  have hsupp : (Function.support fun d : ℕ => PowerSeries.coeff d (PowerSeries.exp A) •
      MvPowerSeries.coeff e ((MvPowerSeries.C c : MvPowerSeries σ A) ^ d)) ⊆
      ((Finset.range k : Finset ℕ) : Set ℕ) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    refine hd ?_
    rw [← map_pow, pow_eq_zero_of_le hcon hk, map_zero, map_zero, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  split_ifs with he
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [← map_pow, MvPowerSeries.coeff_C, if_pos he, PowerSeries.coeff_exp, smul_eq_mul,
      Algebra.smul_def]
    congr 2
    simp
  · refine Finset.sum_eq_zero fun d _ => ?_
    rw [← map_pow, MvPowerSeries.coeff_C, if_neg he, smul_zero]

theorem mexp_zero : mexp (0 : MvPowerSeries σ A) = 1 := by
  have h := mexp_C (σ := σ) (A := A) (c := 0) IsNilpotent.zero
  rwa [map_zero, IsNilpotent.exp_zero, map_one] at h

/-- The chain rule `∂_i e^f = e^f ∂_i f`. -/
theorem pderiv_mexp {f : MvPowerSeries σ A} (hf : IsNilpotent (MvPowerSeries.constantCoeff f))
    (i : σ) : MvPowerSeries.pderiv A i (mexp f) = mexp f * MvPowerSeries.pderiv A i f := by
  set c := MvPowerSeries.constantCoeff f with hc
  set g := f - MvPowerSeries.C c with hg
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by simp [hg, hc]
  have hfg : f = MvPowerSeries.C c + g := by rw [hg]; ring
  have hC : IsNilpotent (MvPowerSeries.constantCoeff (MvPowerSeries.C c : MvPowerSeries σ A)) := by
    rwa [MvPowerSeries.constantCoeff_C]
  have e1 : mexp f = MvPowerSeries.C (IsNilpotent.exp c) * mexp g := by
    conv_lhs => rw [hfg]
    rw [mexp_add hC (by rw [hg0]; exact IsNilpotent.zero), mexp_C hf]
  have e2 : MvPowerSeries.pderiv A i f = MvPowerSeries.pderiv A i g := by
    conv_lhs => rw [hfg]
    rw [map_add, MvPowerSeries.pderiv_C, zero_add]
  rw [e2, e1, Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero,
    pderiv_mexp_zero hg0, smul_eq_mul, mul_assoc]

/-- Substitutions commute with the exponential. -/
theorem subst_mexp {τ : Type*} {f : MvPowerSeries σ A}
    (hf : IsNilpotent (MvPowerSeries.constantCoeff f)) {b : σ → MvPowerSeries τ A}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (mexp f) = mexp (MvPowerSeries.subst b f) :=
  subst_psubst hf hb _

/-- Changes of the coefficient ring commute with the exponential. -/
theorem map_mexp {B : Type*} [CommRing B] [Algebra ℚ B] (φ : A →+* B) {f : MvPowerSeries σ A}
    (hf : IsNilpotent (MvPowerSeries.constantCoeff f)) :
    MvPowerSeries.map φ (mexp f) = mexp (MvPowerSeries.map φ f) := by
  rw [mexp, PowerSeries.map_subst hf, PowerSeries.map_exp]
  rfl

theorem mexp_neg_mul {f : MvPowerSeries σ A} (hf : IsNilpotent (MvPowerSeries.constantCoeff f)) :
    mexp (-f) * mexp f = 1 := by
  rw [← mexp_add (by rw [map_neg]; exact hf.neg) hf, neg_add_cancel, mexp_zero]

end Exp

end Virasoro.Sphere
