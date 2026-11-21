import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.ResidueCore2

/-!
# The coefficient of `(Δ-a)^{-k}` in `F_N` when `G_N⁻¹` has pole order at most `k`

Paper.tex l.871–873.  If `G_N(c,a+x) S(x) = x^k`, then
`F_N(c,a+x,d) = x^{-k} ∑_{Y,Y'} S(x)_{Y,Y'} ρ_N(c,a+x,d)_{Y,Y'}`, so
`[x^{-k}] F_N = ∑ S(0)_{Y,Y'} ρ_N(c,a,d)_{Y,Y'}`; `S(0) = [x^{-k}] G_N(c,a+x)⁻¹`.  Over `ℂ(d)`
the matrix `S` is the image of the one over `ℂ`.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- If `G_N(c, a + x) S(x) = x^m`, then `F_N(c,a+x,d) = x^{-m} ∑ S_{Y,Y'} ρ_{Y,Y'}`. -/
theorem expandAt_Frat_of_scaled (c d a : 𝔽) (N : ℕ) (m : ℕ)
    (S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries 𝔽))
    (hS : gramLocal c a N * S = (PowerSeries.X : PowerSeries 𝔽) ^ m • 1) :
    expandAt (Frat c d N) a = HahnSeries.ofPowerSeries ℤ 𝔽 (∑ Y, ∑ Y', S Y Y' *
        torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y') /
      HahnSeries.single (m : ℤ) (1 : 𝔽) := by
  classical
  set G := gramLocal c a N with hG
  set ρ := torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N with hρ
  have hnum : shiftPS a (numR (C c) X (C d) N) = ∑ Y, ∑ Y', G.adjugate Y Y' * ρ Y Y' := by
    rw [map_numR, shiftPS_C, shiftPS_X, shiftPS_C]
    rfl
  have hdet : shiftPS a (detR (C c) X N) = G.det := by
    rw [map_detR, shiftPS_C, shiftPS_X]
    rfl
  have hadj : ∀ Y Y', (PowerSeries.X : PowerSeries 𝔽) ^ m * G.adjugate Y Y'
      = G.det * S Y Y' := by
    intro Y Y'
    have h1 : G.adjugate * (G * S) = G.det • S := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [hS, Matrix.mul_smul, Matrix.mul_one] at h1
    have h2 := congrFun (congrFun h1 Y) Y'
    simpa [Matrix.smul_apply, smul_eq_mul] using h2
  set Q : PowerSeries 𝔽 := ∑ Y, ∑ Y', S Y Y' * ρ Y Y' with hQ
  have hmain : (PowerSeries.X : PowerSeries 𝔽) ^ m * shiftPS a (numR (C c) X (C d) N)
      = G.det * Q := by
    rw [hnum, hQ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [← mul_assoc, hadj, mul_assoc]
  have hdet0 : (HahnSeries.ofPowerSeries ℤ 𝔽 G.det) ≠ 0 := by
    intro h0
    exact gramLocal_det_ne_zero c a N
      (HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero]))
  have hX0 : (HahnSeries.single (m : ℤ) (1 : 𝔽) : 𝔽⸨X⸩) ≠ 0 := by
    simp
  rw [expandAt_eq, Frat_eq, map_div₀, expandHom_algebraMap, expandHom_algebraMap, hdet,
    div_eq_div_iff hdet0 hX0]
  have h3 := congrArg (HahnSeries.ofPowerSeries ℤ 𝔽) hmain
  rw [map_mul, map_mul, HahnSeries.ofPowerSeries_X_pow] at h3
  rw [mul_comm, h3, mul_comm]

/-- If `G_N(c, a + x) S(x) = x^k`, then `[x^{-k}] F_N(c,a+x,d) = ∑ S(0)_{Y,Y'} ρ_N(c,a,d)_{Y,Y'}`. -/
theorem ppCoeff_Frat_of_scaled (c d a : 𝔽) (N : ℕ) (k : ℕ)
    (S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries 𝔽))
    (hS : gramLocal c a N * S = (PowerSeries.X : PowerSeries 𝔽) ^ k • 1) :
    ppCoeff (Frat c d N) a k =
      ∑ Y, ∑ Y', PowerSeries.constantCoeff (S Y Y') * torus c a d N Y Y' := by
  unfold ppCoeff lcoeff
  rw [expandAt_Frat_of_scaled c d a N k S hS]
  have hX0 : (HahnSeries.single (k : ℤ) (1 : 𝔽) : 𝔽⸨X⸩) ≠ 0 := by
    simp
  obtain ⟨Q, hQ⟩ : ∃ Q : PowerSeries 𝔽, Q = ∑ Y, ∑ Y', S Y Y' *
      torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y' :=
    ⟨_, rfl⟩
  rw [← hQ]
  have h1 : HahnSeries.ofPowerSeries ℤ 𝔽 Q / HahnSeries.single (k : ℤ) (1 : 𝔽) *
      HahnSeries.single (k : ℤ) (1 : 𝔽) = HahnSeries.ofPowerSeries ℤ 𝔽 Q :=
    div_mul_cancel₀ _ hX0
  have h2 := HahnSeries.coeff_mul_single_add
    (x := HahnSeries.ofPowerSeries ℤ 𝔽 Q / HahnSeries.single (k : ℤ) (1 : 𝔽))
    (a := -(k : ℤ)) (b := (k : ℤ)) (r := (1 : 𝔽))
  rw [h1, neg_add_cancel, mul_one] at h2
  rw [← h2]
  have h3 := PowerSeries.coeff_coe (f := Q) 0
  rw [if_neg (by norm_num)] at h3
  have h4 : (HahnSeries.ofPowerSeries ℤ 𝔽 Q).coeff 0 = PowerSeries.constantCoeff Q := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h3
  rw [h4, hQ, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_mul, constantCoeff_torusLocal]

/-- Over `ℂ(d)`: if `G_N(c,Δ)⁻¹` has pole order at most `k` at `Δ = a`, then
`[(Δ-a)^{-k}] F_N(c,Δ,d) = ∑ ([x^{-k}] G_N(c,a+x)⁻¹)_{Y,Y'} ρ_N(c,a,d)_{Y,Y'}`, a polynomial
in `d`. -/
theorem ppCoeff_FN_top (c a : ℂ) (N k : ℕ) (hp : poleOrderInv (gramLocal c a N) ≤ k) :
    ppCoeff (FN c N) (pt a) k = algebraMap ℂ[X] Kd
      (∑ Y, ∑ Y', C (invCoeff (gramLocal c a N) (-(k : ℤ)) Y Y') *
        torus (C c) (C a) (X : ℂ[X]) N Y Y') := by
  classical
  have hord : MatOrdGE (invLaurent (gramLocal c a N)) (-(k : ℤ)) := fun i j =>
    (matOrdGE_inv (gramLocal c a N) i j).mono (by
      have : (poleOrderInv (gramLocal c a N) : ℤ) ≤ k := by exact_mod_cast hp
      omega)
  have h0 := mul_scaledInv (gramLocal_det_ne_zero c a N) hord
  have hS : gramLocal (RatFunc.C c : Kd) (pt a) N *
      (scaledInv (gramLocal c a N) k).map (PowerSeries.map (RatFunc.C : ℂ →+* Kd)) =
      (PowerSeries.X : PowerSeries Kd) ^ k • 1 := by
    rw [gramLocal_ratC, ← Matrix.map_mul, h0]
    refine Matrix.ext fun Y Y' => ?_
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.one_apply, smul_eq_mul, smul_eq_mul, map_mul, map_pow, PowerSeries.map_X]
    by_cases hY : Y = Y'
    · rw [if_pos hY, if_pos hY, map_one]
    · rw [if_neg hY, if_neg hY, map_zero]
  have hc : ∀ Y Y', PowerSeries.constantCoeff (scaledInv (gramLocal c a N) k Y Y') =
      invCoeff (gramLocal c a N) (-(k : ℤ)) Y Y' := by
    intro Y Y'
    have := congrFun (congrFun (coeffMat_scaledInv (gramLocal c a N) k 0) Y) Y'
    simpa [coeffMat, PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
  have ht : torus (RatFunc.C c : Kd) (pt a) dvar N =
      (torus (C c) (C a) (X : ℂ[X]) N).map (algebraMap ℂ[X] Kd) := by
    have := torus_map (algebraMap ℂ[X] Kd) (C c) (C a) (X : ℂ[X]) N
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X] at this
    exact this
  rw [FN, ppCoeff_Frat_of_scaled _ _ _ _ _ _ hS, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_mul, RatFunc.algebraMap_C, ht, Matrix.map_apply, Matrix.map_apply, ← hc Y Y']
  congr 1

end Virasoro
