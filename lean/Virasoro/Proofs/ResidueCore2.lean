import Virasoro.Proofs.ResidueCore1
import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.Sec7Pole
import Virasoro.Proofs.Sec5Det
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The residue of `F_N` at a singular weight

Continuation of `ResidueCore1`: the residue of `G_{ℓ+M}(c,Δ)⁻¹` at `Δ = h` is
`ι (β_χ G_M(c,h+ℓ))⁻¹ ιᵀ`, and with the factorization of the pulled-back torus form,
`Res_{Δ=h} F_{ℓ+M}(c,Δ,d) = ⟨χ|V_d(1)|χ⟩ / β_χ · F_M(c,h+ℓ,d)`.
-/

namespace Virasoro

open Polynomial Module
open scoped LaurentSeries

variable {K : Type*} [Field K] [CharZero K]

theorem multiset_filter_pos_card_le_sum (s : Multiset ℕ) :
    (s.filter fun e => 0 < e).card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.filter_cons, Multiset.sum_cons]
    split_ifs with ha
    · simp only [Multiset.singleton_add, Multiset.card_cons]
      omega
    · simp only [zero_add]
      omega

theorem coeff_neg_one_mul {x y : K⸨X⸩} (hx : OrdGE x (-1)) (hy : OrdGE y 0) :
    (x * y).coeff (-1) = x.coeff (-1) * y.coeff 0 := by
  have h1 := coeff_mul_congr (A := x) (A' := x) (S := HahnSeries.C (y.coeff 0)) (S' := y)
    (a := -1) (s := 0) (U := -1) hx hy (fun _ _ => rfl) (fun n hn => by
      have hC : (HahnSeries.C (y.coeff 0) : K⸨X⸩) = HahnSeries.single 0 (y.coeff 0) := rfl
      by_cases h0 : n = 0
      · subst h0
        rw [hC, HahnSeries.coeff_single_same]
      · rw [hC, HahnSeries.coeff_single_of_ne h0]
        exact hy.coeff_eq_zero (by omega)) (-1) le_rfl
  rw [h1, coeff_mul_C]

/-- The Laurent expansion of `F_N` at `Δ = a` through the inverse of the local Shapovalov
matrix. -/
theorem expandAt_Frat_eq (c d a : K) (N : ℕ) :
    expandAt (Frat c d N) a = ∑ Y, ∑ Y', invLaurent (gramLocal c a N) Y Y' *
      HahnSeries.ofPowerSeries ℤ K
        (torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y') := by
  classical
  set G := gramLocal c a N with hG
  have hnum : shiftPS a (numR (C c) X (C d) N) = ∑ Y, ∑ Y', G.adjugate Y Y' *
      torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y' := by
    rw [map_numR, shiftPS_C, shiftPS_X, shiftPS_C]
    rfl
  have hdet : shiftPS a (detR (C c) X N) = G.det := by
    rw [map_detR, shiftPS_C, shiftPS_X]
    rfl
  have hinv : ∀ Y Y', invLaurent G Y Y'
      = (HahnSeries.ofPowerSeries ℤ K G.det)⁻¹ * HahnSeries.ofPowerSeries ℤ K (G.adjugate Y Y') := by
    intro Y Y'
    have h1 : invLaurent G = (toL G)⁻¹ := rfl
    have h2 : (toL G).adjugate = toL G.adjugate :=
      (RingHom.map_adjugate (HahnSeries.ofPowerSeries ℤ K) G).symm
    rw [h1, Matrix.inv_def, Ring.inverse_eq_inv', det_toL, h2]
    rfl
  rw [expandAt_eq, Frat_eq, map_div₀, expandHom_algebraMap, expandHom_algebraMap, hnum, hdet,
    div_eq_inv_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_mul, hinv, mul_assoc]

theorem constantCoeff_torusLocal (c d a : K) (N : ℕ) (Y Y' : Nat.Partition N) :
    PowerSeries.constantCoeff
        (torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y')
      = torus c a d N Y Y' := by
  have := torus_map (PowerSeries.constantCoeff (R := K)) (PowerSeries.C c)
    (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N
  simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero] at this
  rw [this]
  rfl

/-- If `G_N(c,Δ)⁻¹` has at most a simple pole at `Δ = a`, so does `F_N`, with residue
`∑ (Res G_N⁻¹)_{Y,Y'} ρ_N(c,a,d)_{Y,Y'}`. -/
theorem ppCoeff_Frat_of_simple (c d a : K) (N : ℕ)
    (hp : poleOrderInv (gramLocal c a N) ≤ 1) :
    poleOrder (Frat c d N) a ≤ 1 ∧
      ppCoeff (Frat c d N) a 1
        = ∑ Y, ∑ Y', invCoeff (gramLocal c a N) (-1) Y Y' * torus c a d N Y Y' := by
  have hord : ∀ Y Y', OrdGE (invLaurent (gramLocal c a N) Y Y') (-1) := by
    intro Y Y'
    refine (matOrdGE_inv (gramLocal c a N) Y Y').mono ?_
    have : (poleOrderInv (gramLocal c a N) : ℤ) ≤ 1 := by exact_mod_cast hp
    omega
  have hρ : ∀ Y Y', OrdGE (HahnSeries.ofPowerSeries ℤ K
      (torus (PowerSeries.C c) (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y')) 0 :=
    fun Y Y' => ordGE_ofPowerSeries _
  constructor
  · refine poleOrder_le_of_ordGE ?_
    rw [expandAt_Frat_eq]
    refine OrdGE.sum fun Y _ => OrdGE.sum fun Y' _ => ?_
    have := (hord Y Y').mul (hρ Y Y')
    simpa using this
  · unfold ppCoeff lcoeff
    rw [expandAt_Frat_eq, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun Y' _ => ?_
    have h1 := coeff_neg_one_mul (hord Y Y') (hρ Y Y')
    have h2 : (HahnSeries.ofPowerSeries ℤ K (torus (PowerSeries.C c)
        (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y')).coeff 0
        = torus c a d N Y Y' := by
      have := PowerSeries.coeff_coe (f := torus (PowerSeries.C c)
        (PowerSeries.C a + PowerSeries.X) (PowerSeries.C d) N Y Y') 0
      rw [if_neg (by norm_num)] at this
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_torusLocal] using this
    simp only [Nat.cast_one]
    rw [h1, h2]
    rfl

end Virasoro
