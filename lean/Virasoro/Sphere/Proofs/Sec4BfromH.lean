import Virasoro.Sphere.Proofs.FpowBinom
import Virasoro.Sphere.Proofs.Sec3SaddleI0e
import Virasoro.Sphere.Proofs.Sec2HSeries

/-!
# Sphere paper equation (2.8): `ℬ_N` in terms of `H_0, …, H_N`

`sphere/paper.tex` l.386–392.  Substituting `q = q(z)` in `∑ ℬ_m z(q)^m = Φ̃ ∑ H_m (16q)^m`
gives `ℬ_N = ∑_{m ≤ N} H_m [z^N](Φ̃(q(z)) (16 q(z))^m)`, and
`[z^N](Φ̃(c,Δ;q(z)) (16q(z))^m) = ψ_{N-m}(c,Δ+m,Δ_i)` because
`(16q(z))^m = z^m (16q(z)/z)^m`.  With `ψ_i = [z^i] Φ̃(q(z))`,
`[z^N](Φ̃(q(z)) (16 q(z))^m) = ∑_{i+j=N} ψ_i 16^m [z^j] q(z)^m`.
-/

namespace Virasoro.Sphere

open PowerSeries

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `q(z)` over `𝔽(Δ)`. -/
noncomputable def Qr (𝔽 : Type*) [Field 𝔽] [CharZero 𝔽] : PowerSeries (RatFunc 𝔽) :=
  Q0.map (algebraMap ℚ (RatFunc 𝔽))

theorem constantCoeff_Qr : constantCoeff (Qr 𝔽) = 0 := by
  rw [Qr, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_Q0, map_zero]

theorem hasSubst_Qr : HasSubst (Qr 𝔽) := HasSubst.of_constantCoeff_zero' constantCoeff_Qr

theorem zq_subst_Qr : (zq (RatFunc 𝔽)).subst (Qr 𝔽) = X := by
  have h1 := congrArg (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽))) zq_subst_Q0
  rw [PowerSeries.map_X] at h1
  rw [← h1, ← map_zq (algebraMap ℚ (RatFunc 𝔽))]
  exact (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' constantCoeff_Q0)
    (h := algebraMap ℚ (RatFunc 𝔽)) _).symm

/-- `(∑_k b_k z(q)^k)(q(z)) = ∑_k b_k z^k`. -/
theorem compS_zq_subst_Qr (b : ℕ → RatFunc 𝔽) :
    (compS b (zq (RatFunc 𝔽))).subst (Qr 𝔽) = PowerSeries.mk b := by
  rw [compS_eq_subst b constantCoeff_zq,
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' constantCoeff_zq) hasSubst_Qr,
    zq_subst_Qr, subst_X_self']

/-- `ψ_i(c,Δ,Δ_i) = [z^i] Φ̃(c,Δ,Δ_i;q(z))`. -/
noncomputable def psiZ (c : 𝔽) (Δe : Fin 4 → 𝔽) (i : ℕ) : RatFunc 𝔽 :=
  coeff i ((PhiTilde c Δe).subst (Qr 𝔽))

/-- `[z^N](Φ̃(c,Δ,Δ_i;q(z)) (16q(z))^m)`, the coefficient `ψ_{N-m}(c,Δ+m,Δ_i)` of
equation (2.8). -/
noncomputable def wZ (c : 𝔽) (Δe : Fin 4 → 𝔽) (N m : ℕ) : RatFunc 𝔽 :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
    psiZ c Δe p.1 * (16 ^ m * coeff p.2 (Qr 𝔽 ^ m))

theorem PhiTilde_mul_Hseries (c : 𝔽) (Δe : Fin 4 → 𝔽) :
    PhiTilde c Δe * Hseries c Δe = BzSeries c Δe := by
  have h1 : constantCoeff (PhiTilde c Δe) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PhiTilde_coeff_zero]
    exact one_ne_zero
  rw [Hseries, ← mul_assoc, PowerSeries.mul_inv_cancel _ h1, one_mul]

theorem coeff_Hseries (c : 𝔽) (Δe : Fin 4 → 𝔽) (m : ℕ) :
    coeff m (Hseries c Δe) = 16 ^ m * Hsph c Δe m := by
  rw [Hsph, mul_div_cancel₀ _ (pow_ne_zero m (by norm_num : (16 : RatFunc 𝔽) ≠ 0))]

/-- Equation (2.8): `ℬ_N = ∑_{m=0}^N H_m ψ_{N-m}(c,Δ+m,Δ_i)`. -/
theorem B_from_H (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) :
    Bsph c Δe N = ∑ m ∈ Finset.range (N + 1), Hsph c Δe m * wZ c Δe N m := by
  have hB : (BzSeries c Δe).subst (Qr 𝔽) = PowerSeries.mk (Bsph c Δe) :=
    compS_zq_subst_Qr (Bsph c Δe)
  have hH : Hseries c Δe = PowerSeries.mk fun m => coeff m (Hseries c Δe) := by
    ext m
    rw [coeff_mk]
  have hHs : ∀ j ≤ N, coeff j ((Hseries c Δe).subst (Qr 𝔽)) =
      ∑ m ∈ Finset.range (N + 1), 16 ^ m * Hsph c Δe m * coeff j (Qr 𝔽 ^ m) := by
    intro j hj
    rw [hH, ← compS_eq_subst _ constantCoeff_Qr, coeff_compS_le constantCoeff_Qr _ hj]
    exact Finset.sum_congr rfl fun m _ => by rw [coeff_Hseries]
  have h1 := congrArg (coeff N) hB
  rw [coeff_mk, ← PhiTilde_mul_Hseries, subst_mul hasSubst_Qr, coeff_mul] at h1
  rw [← h1]
  have h2 : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      coeff p.1 ((PhiTilde c Δe).subst (Qr 𝔽)) * coeff p.2 ((Hseries c Δe).subst (Qr 𝔽)) =
        ∑ m ∈ Finset.range (N + 1),
          Hsph c Δe m * (psiZ c Δe p.1 * (16 ^ m * coeff p.2 (Qr 𝔽 ^ m))) := by
    intro p hp
    have hp2 : p.2 ≤ N := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega
    rw [hHs p.2 hp2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [psiZ]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [wZ, Finset.mul_sum]

end Virasoro.Sphere
