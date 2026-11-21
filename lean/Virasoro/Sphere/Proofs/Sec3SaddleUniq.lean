import Virasoro.Sphere.Proofs.Sec3SaddleEx

/-!
# Sphere paper Lemma 3.4(iii): uniqueness of the saddle point (`sphere/paper.tex` l.727–728)

The saddle-point equations determine the coefficient of `z^k` of `σ_m`, `σ̄_m` from the
coefficients of `z^{k-m}`, so two saddle points are equal.

Consumer: the uniqueness claim in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem IsSaddle.dvd {σ σb : ℕ+ → PowerSeries ℂ} (h : IsSaddle σ σb) (m : ℕ+) :
    (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σ m ∧
      (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σb m := by
  have hm0 : (2 * ((m : ℕ) : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 m.pos.ne')
  constructor
  · refine ⟨(2 * ((m : ℕ) : ℂ))⁻¹ • (PowerSeries.C (-Acoef m) +
      2 * MvPowerSeries.subst σb (linSeries fun n => (Bcoef m n : ℂ))), ?_⟩
    rw [mul_smul_comm, ← h.eq_bar m, inv_smul_smul₀ hm0]
  · refine ⟨(2 * ((m : ℕ) : ℂ))⁻¹ • (PowerSeries.C (Acoef m) +
      2 * MvPowerSeries.subst σ (linSeries fun n => (Bcoef m n : ℂ))), ?_⟩
    rw [mul_smul_comm, ← h.eq m, inv_smul_smul₀ hm0]

theorem IsSaddle.coeff_bar {σ σb : ℕ+ → PowerSeries ℂ} (h : IsSaddle σ σb) (m : ℕ+) (k : ℕ) :
    (2 * ((m : ℕ) : ℂ)) * PowerSeries.coeff k (σb m) =
      if (m : ℕ) ≤ k then
        (if k - (m : ℕ) = 0 then Acoef m else 0) + 2 * ∑ n ∈ Icc 1 (k - (m : ℕ)),
          (Bcoef m n : ℂ) * PowerSeries.coeff (k - (m : ℕ)) (σ n.toPNat')
      else 0 := by
  have := congrArg (PowerSeries.coeff k) (h.eq m)
  rw [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul'] at this
  by_cases hk : (m : ℕ) ≤ k
  · rw [if_pos hk] at this ⊢
    rw [this, map_add, PowerSeries.coeff_C,
      show (2 : PowerSeries ℂ) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
      PowerSeries.coeff_C_mul, coeff_subst_linSeries _ (fun n => (h.dvd n).1)]
  · rw [if_neg hk] at this ⊢
    exact this

theorem IsSaddle.coeff_self {σ σb : ℕ+ → PowerSeries ℂ} (h : IsSaddle σ σb) (m : ℕ+) (k : ℕ) :
    (2 * ((m : ℕ) : ℂ)) * PowerSeries.coeff k (σ m) =
      if (m : ℕ) ≤ k then
        (if k - (m : ℕ) = 0 then -Acoef m else 0) + 2 * ∑ n ∈ Icc 1 (k - (m : ℕ)),
          (Bcoef m n : ℂ) * PowerSeries.coeff (k - (m : ℕ)) (σb n.toPNat')
      else 0 := by
  have := congrArg (PowerSeries.coeff k) (h.eq_bar m)
  rw [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul'] at this
  by_cases hk : (m : ℕ) ≤ k
  · rw [if_pos hk] at this ⊢
    rw [this, map_add, PowerSeries.coeff_C,
      show (2 : PowerSeries ℂ) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
      PowerSeries.coeff_C_mul, coeff_subst_linSeries _ (fun n => (h.dvd n).2)]
  · rw [if_neg hk] at this ⊢
    exact this

/-- Two saddle points are equal. -/
theorem IsSaddle.unique {σ σb σ' σb' : ℕ+ → PowerSeries ℂ} (h : IsSaddle σ σb)
    (h' : IsSaddle σ' σb') : σ = σ' ∧ σb = σb' := by
  have key : ∀ k : ℕ, ∀ m : ℕ+,
      PowerSeries.coeff k (σ m) = PowerSeries.coeff k (σ' m) ∧
        PowerSeries.coeff k (σb m) = PowerSeries.coeff k (σb' m) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro m
      have hm0 : (2 * ((m : ℕ) : ℂ)) ≠ 0 :=
        mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 m.pos.ne')
      have hpos := m.pos
      constructor
      · apply mul_left_cancel₀ hm0
        rw [h.coeff_self m k, h'.coeff_self m k]
        by_cases hk : (m : ℕ) ≤ k
        · rw [if_pos hk, if_pos hk,
            sum_congr rfl (fun n _ => by rw [(ih (k - (m : ℕ)) (by omega) n.toPNat').2])]
        · rw [if_neg hk, if_neg hk]
      · apply mul_left_cancel₀ hm0
        rw [h.coeff_bar m k, h'.coeff_bar m k]
        by_cases hk : (m : ℕ) ≤ k
        · rw [if_pos hk, if_pos hk,
            sum_congr rfl (fun n _ => by rw [(ih (k - (m : ℕ)) (by omega) n.toPNat').1])]
        · rw [if_neg hk, if_neg hk]
  exact ⟨funext fun m => PowerSeries.ext fun k => (key k m).1,
    funext fun m => PowerSeries.ext fun k => (key k m).2⟩

/-- Every saddle point is `(σ_*, -σ_*)`. -/
theorem IsSaddle.eq_sigmaStar {σ σb : ℕ+ → PowerSeries ℂ} (h : IsSaddle σ σb) :
    σ = sigmaStar ∧ σb = fun m => -sigmaStar m :=
  h.unique isSaddle_sigmaStar

end Virasoro.Sphere
