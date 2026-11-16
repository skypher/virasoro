import Virasoro.Proofs.Sec4Core2
import Virasoro.Proofs.GramDet
import Virasoro.Proofs.Expand

/-!
# The pole order of `F_N` is at most the pole order of the inverse Shapovalov matrix

The Laurent expansion of a quotient of polynomials at `Δ = a` is the quotient of their shifts
`p(a + x)`.  If `G_N(c, a + x) S(x) = x^m` for a matrix `S` of power series, then
`F_N = tr(G_N⁻¹ ρ_Nᵀ)` has a pole of order at most `m` at `Δ = a`.  The matrix `S` for the
field `ℂ(d)` is obtained from the one over `ℂ`.
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- The Laurent expansion at `a` of a polynomial is its shift `p(a + x)`. -/
theorem expandHom_algebraMap (a : 𝔽) (p : 𝔽[X]) :
    expandHom a (algebraMap 𝔽[X] (RatFunc 𝔽) p)
      = HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a p) := by
  have key : (expandHom a).comp (algebraMap 𝔽[X] (RatFunc 𝔽))
      = (HahnSeries.ofPowerSeries ℤ 𝔽).comp (shiftPS a) := by
    apply Polynomial.ringHom_ext
    · intro x
      rw [RingHom.comp_apply, RingHom.comp_apply, shiftPS_C, HahnSeries.ofPowerSeries_C,
        RatFunc.algebraMap_C, expandHom_C]
    · rw [RingHom.comp_apply, RingHom.comp_apply, shiftPS_X, map_add,
        HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, RatFunc.algebraMap_X,
        expandHom_X, add_comm]
  exact congrArg (fun f : 𝔽[X] →+* 𝔽⸨X⸩ => f p) key

omit [CharZero 𝔽] in
theorem poleOrder_le_of_ordGE {f : RatFunc 𝔽} {a : 𝔽} {n : ℕ}
    (hord : OrdGE (expandAt f a) (-(n : ℤ))) : poleOrder f a ≤ n := by
  unfold poleOrder
  by_cases h0 : expandAt f a = 0
  · rw [h0]; simp
  · unfold OrdGE at hord
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at hord
    have : -(n : ℤ) ≤ (expandAt f a).order := by exact_mod_cast hord
    omega

/-- If `G_N(c, a + x) S(x) = x^m`, the expansion of `F_N` at `Δ = a` has order at least `-m`. -/
theorem ordGE_expandAt_Frat (c d a : 𝔽) (N : ℕ) (m : ℕ)
    (S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries 𝔽))
    (hS : gramLocal c a N * S = (PowerSeries.X : PowerSeries 𝔽) ^ m • 1) :
    OrdGE (expandAt (Frat c d N) a) (-(m : ℤ)) := by
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
  have hexp : expandAt (Frat c d N) a
      = HahnSeries.ofPowerSeries ℤ 𝔽 Q / HahnSeries.single (m : ℤ) (1 : 𝔽) := by
    rw [expandAt_eq, Frat_eq, map_div₀, expandHom_algebraMap, expandHom_algebraMap, hdet,
      div_eq_div_iff hdet0 hX0]
    have h3 := congrArg (HahnSeries.ofPowerSeries ℤ 𝔽) hmain
    rw [map_mul, map_mul, HahnSeries.ofPowerSeries_X_pow] at h3
    rw [mul_comm, h3, mul_comm]
  rw [hexp]
  have := (ordGE_ofPowerSeries Q).div (HahnSeries.single (m : ℤ) (1 : 𝔽))
  rwa [HahnSeries.order_single one_ne_zero, zero_sub] at this

/-- The pole order of `F_N(c,Δ,d)` at `Δ = a` is at most that of `G_N(c,Δ)⁻¹`, over one field. -/
theorem ordGE_expandAt_Frat_poleOrderInv (c d a : 𝔽) (N : ℕ) :
    OrdGE (expandAt (Frat c d N) a) (-(poleOrderInv (gramLocal c a N) : ℤ)) :=
  ordGE_expandAt_Frat c d a N _ (scaledInv (gramLocal c a N) (poleOrderInv (gramLocal c a N)))
    (mul_scaledInv (gramLocal_det_ne_zero c a N) (matOrdGE_inv _))

/-- The local Shapovalov matrix over `ℂ(d)` is the image of the one over `ℂ`. -/
theorem gramLocal_ratC (c a : ℂ) (N : ℕ) :
    gramLocal (RatFunc.C c : Kd) (pt a) N
      = (gramLocal c a N).map (PowerSeries.map (RatFunc.C : ℂ →+* Kd)) := by
  have := gram_map (PowerSeries.map (RatFunc.C : ℂ →+* Kd)) (PowerSeries.C c)
    (PowerSeries.C a + PowerSeries.X) N
  rw [map_add, PowerSeries.map_C, PowerSeries.map_C, PowerSeries.map_X] at this
  exact this

/-- The pole order of `F_N(c,Δ,d)` over `ℂ(d)` at `Δ = a` is at most the pole order of
`G_N(c,Δ)⁻¹` over `ℂ`. -/
theorem ordGE_expandAt_FN (c a : ℂ) (N : ℕ) :
    OrdGE (expandAt (FN c N) (pt a)) (-(poleOrderInv (gramLocal c a N) : ℤ)) := by
  classical
  have h0 := mul_scaledInv (gramLocal_det_ne_zero c a N) (matOrdGE_inv (gramLocal c a N))
  refine ordGE_expandAt_Frat (RatFunc.C c : Kd) dvar (pt a) N
    (poleOrderInv (gramLocal c a N))
    ((scaledInv (gramLocal c a N) (poleOrderInv (gramLocal c a N))).map
      (PowerSeries.map (RatFunc.C : ℂ →+* Kd))) ?_
  rw [gramLocal_ratC, ← Matrix.map_mul, h0]
  refine Matrix.ext fun Y Y' => ?_
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.one_apply, smul_eq_mul, smul_eq_mul, map_mul, map_pow, PowerSeries.map_X]
  by_cases hY : Y = Y'
  · rw [if_pos hY, if_pos hY, map_one]
  · rw [if_neg hY, if_neg hY, map_zero]

theorem poleOrder_FN_le (c a : ℂ) (N : ℕ) :
    poleOrder (FN c N) (pt a) ≤ poleOrderInv (gramLocal c a N) :=
  poleOrder_le_of_ordGE (ordGE_expandAt_FN c a N)

/-- If the pole orders of `G_M(c,Δ)⁻¹`, `M ≤ N`, at `Δ = a` are at most `B`, then `H_N(c,Δ,d)`
has a pole of order at most `B` at `Δ = a`. -/
theorem poleOrder_HN_le (c a : ℂ) (N B : ℕ)
    (hB : ∀ M ≤ N, poleOrderInv (gramLocal c a M) ≤ B) :
    poleOrder (HN c N) (pt a) ≤ B := by
  refine poleOrder_le_of_ordGE ?_
  rw [expandAt_eq, HN, Hrat, map_sum]
  refine OrdGE.sum fun j _ => ?_
  rw [map_mul, map_intCast]
  have h1 : OrdGE (((eta j : ℤ) : Kd⸨X⸩)) 0 := (regVal_intCast (eta j)).1
  have h2 := (ordGE_expandAt_FN c a (N - j)).mono
    (show -(B : ℤ) ≤ -(poleOrderInv (gramLocal c a (N - j)) : ℤ) by
      have := hB (N - j) (Nat.sub_le N j)
      omega)
  have h3 := h1.mul h2
  rw [zero_add] at h3
  exact h3

end Virasoro
