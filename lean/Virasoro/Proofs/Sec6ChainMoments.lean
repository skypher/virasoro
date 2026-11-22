import Virasoro.Proofs.Sec6Chains
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Proposition 6.7: the partial-fraction moments (paper.tex l.1162–1164)

If `f(w) = ∑_θ C_θ/(w − a_θ)` over `k` slopes is `O(w^{−k})`, its moments of order at most `k − 2`
vanish, and `lim_w w^k f(w) = C_κ ∏_{θ≠κ}(a_κ − a_θ)` for each `κ`
(`ChainEval.moment_limit`).  In polynomial form: the numerator
`P = ∑_θ C_θ ∏_{θ'≠θ}(w − a_θ')` of `f` over `Q = ∏_θ (w − a_θ)` has degree less than `k`, and
`w^k P − a Q` has degree less than `k`, so `P` is the constant `a`; its value at `a_κ` is
`C_κ ∏_{θ≠κ}(a_κ − a_θ)`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {ι : Type*} [DecidableEq ι]

/-- The numerator `∑_θ C_θ ∏_{θ'≠θ}(w − a_θ')`. -/
noncomputable def pfNum (S : Finset ι) (aθ Cθ : ι → ℂ) : ℂ[X] :=
  ∑ θ ∈ S, C (Cθ θ) * ∏ θ' ∈ S.erase θ, (X - C (aθ θ'))

/-- The denominator `∏_θ (w − a_θ)`. -/
noncomputable def pfDen (S : Finset ι) (aθ : ι → ℂ) : ℂ[X] := ∏ θ ∈ S, (X - C (aθ θ))

theorem pfDen_monic (S : Finset ι) (aθ : ι → ℂ) : (pfDen S aθ).Monic :=
  monic_prod_of_monic _ _ fun θ _ => monic_X_sub_C (aθ θ)

theorem pfDen_natDegree (S : Finset ι) (aθ : ι → ℂ) : (pfDen S aθ).natDegree = S.card := by
  rw [pfDen, natDegree_prod_of_monic _ _ fun θ _ => monic_X_sub_C (aθ θ)]
  simp

theorem algebraMap_pfNum (S : Finset ι) (aθ Cθ : ι → ℂ) :
    algebraMap ℂ[X] (RatFunc ℂ) (pfNum S aθ Cθ) =
      (∑ θ ∈ S, RatFunc.C (Cθ θ) * (RatFunc.X - RatFunc.C (aθ θ))⁻¹) *
        algebraMap ℂ[X] (RatFunc ℂ) (pfDen S aθ) := by
  rw [pfNum, map_sum, sum_mul]
  refine sum_congr rfl fun θ hθ => ?_
  have hne : (RatFunc.X - RatFunc.C (aθ θ) : RatFunc ℂ) ≠ 0 := by
    have e : (RatFunc.X - RatFunc.C (aθ θ) : RatFunc ℂ) =
        algebraMap ℂ[X] (RatFunc ℂ) (X - C (aθ θ)) := by
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [e]
    exact fun h0 => X_sub_C_ne_zero (aθ θ)
      (RatFunc.algebraMap_injective ℂ (h0.trans (map_zero _).symm))
  rw [pfDen, ← mul_prod_erase S _ hθ, map_mul, map_mul, map_sub, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, RatFunc.algebraMap_C]
  field_simp

theorem eval_pfNum (S : Finset ι) (aθ Cθ : ι → ℂ) {κ : ι} (hκ : κ ∈ S) :
    (pfNum S aθ Cθ).eval (aθ κ) = Cθ κ * ∏ θ ∈ S.erase κ, (aθ κ - aθ θ) := by
  rw [pfNum, eval_finset_sum, sum_eq_single κ]
  · rw [eval_mul, eval_C, eval_prod]
    simp
  · intro θ _ hθκ
    rw [eval_mul, eval_prod, prod_eq_zero (mem_erase.2 ⟨Ne.symm hθκ, hκ⟩) (by simp), mul_zero]
  · exact fun h => absurd hκ h

/-- `lim_w w^k ∑_θ C_θ/(w − a_θ) = C_κ ∏_{θ≠κ}(a_κ − a_θ)` for each of the `k` slopes `κ`, when
the limit exists (paper.tex l.1162–1164). -/
theorem moment_limit (S : Finset ι) (aθ Cθ : ι → ℂ) (k : ℕ) (hk : S.card = k) (a : ℂ)
    (e : RatFunc ℂ) (he : VanishesAtInfinity e)
    (h : (∑ θ ∈ S, RatFunc.C (Cθ θ) * (RatFunc.X - RatFunc.C (aθ θ))⁻¹) * RatFunc.X ^ k =
      RatFunc.C a + e) :
    ∀ κ ∈ S, a = Cθ κ * ∏ θ ∈ S.erase κ, (aθ κ - aθ θ) := by
  have hQd : (pfDen S aθ).natDegree = k := (pfDen_natDegree S aθ).trans hk
  have hQ0 : algebraMap ℂ[X] (RatFunc ℂ) (pfDen S aθ) ≠ 0 := fun h0 =>
    (pfDen_monic S aθ).ne_zero (RatFunc.algebraMap_injective ℂ (h0.trans (map_zero _).symm))
  have hD : algebraMap ℂ[X] (RatFunc ℂ) (pfNum S aθ Cθ * X ^ k - C a * pfDen S aθ) =
      e * algebraMap ℂ[X] (RatFunc ℂ) (pfDen S aθ) := by
    rw [map_sub, map_mul, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      algebraMap_pfNum]
    linear_combination (algebraMap ℂ[X] (RatFunc ℂ) (pfDen S aθ)) * h
  have hcoef : ∀ n : ℕ, k ≤ n → (pfNum S aθ Cθ * X ^ k - C a * pfDen S aθ).coeff n = 0 := by
    intro n hn
    rcases he with he | he
    · rw [he, zero_mul] at hD
      rw [RatFunc.algebraMap_injective ℂ (hD.trans (map_zero _).symm), coeff_zero]
    · by_cases hD0 : pfNum S aθ Cθ * X ^ k - C a * pfDen S aθ = 0
      · rw [hD0, coeff_zero]
      · have he0 : e ≠ 0 := by
          rintro rfl
          simp at he
        have h1 := congrArg RatFunc.intDegree hD
        rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_mul he0 hQ0,
          RatFunc.intDegree_polynomial, hQd] at h1
        exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hP : pfNum S aθ Cθ = C a := by
    ext j
    have h1 := hcoef (j + k) (Nat.le_add_left k j)
    rw [coeff_sub, coeff_mul_X_pow, coeff_C_mul] at h1
    cases j with
    | zero =>
      have h2 : (pfDen S aθ).coeff (0 + k) = 1 := by
        rw [zero_add, ← hQd]
        exact (pfDen_monic S aθ).coeff_natDegree
      rw [h2, mul_one] at h1
      rw [coeff_C_zero]
      exact sub_eq_zero.1 h1
    | succ j =>
      have h2 : (pfDen S aθ).coeff (j + 1 + k) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h2, mul_zero, sub_zero] at h1
      rw [h1, coeff_C_succ]
  intro κ hκ
  rw [← eval_pfNum S aθ Cθ hκ, hP, eval_C]

end Virasoro.ChainEval
