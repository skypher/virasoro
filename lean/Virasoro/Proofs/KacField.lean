import Virasoro.Proofs.Specialize
import Virasoro.Proofs.Sec4Core2
import Virasoro.Proofs.GramDet
import Virasoro.Cited

/-!
# The Kac determinant over every field of characteristic zero

The Kac determinant formula, cited for complex `b`, is an identity of polynomials in `Δ` whose
coefficients are rational functions of `b` over `ℚ`.  It therefore holds over `ℚ(b)` (a rational
function vanishing at all positive integers is zero) and specializes to every `b ≠ 0` of every
field of characteristic zero.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

theorem PolyEv.pow {b : 𝔽} {P : (RatFunc ℚ)[X]} {P' : 𝔽[X]} (hP : PolyEv b P P') (n : ℕ) :
    PolyEv b (P ^ n) (P' ^ n) := by
  induction n with
  | zero => simpa using polyEv_one (b := b)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hP

/-- The Shapovalov determinant over `ℚ(b)` specializes coefficientwise. -/
theorem polyEv_gramDet {b : 𝔽} (hb : b ≠ 0) (N : ℕ) :
    PolyEv b (gramPoly (kacC (RatFunc.X : RatFunc ℚ)) N).det (gramPoly (kacC b) N).det := by
  intro n
  set cR : regSub b := ⟨kacC RatFunc.X, (evTo_kacC hb).1⟩ with hcR
  set incl : regSub b →+* RatFunc ℚ := ((regSub b).val : regSub b →+* RatFunc ℚ) with hincl
  have h1 : (gramPoly (kacC (RatFunc.X : RatFunc ℚ)) N).det
      = (detR (C cR) (X : (regSub b)[X]) N).map incl := by
    have := map_detR (Polynomial.mapRingHom incl) (C cR) (X : (regSub b)[X]) N
    simp only [coe_mapRingHom, map_C, map_X] at this
    rw [this]
    rfl
  have h2 : (gramPoly (kacC b) N).det = (detR (C cR) (X : (regSub b)[X]) N).map (evReg b) := by
    have := map_detR (Polynomial.mapRingHom (evReg b)) (C cR) (X : (regSub b)[X]) N
    simp only [coe_mapRingHom, map_C, map_X] at this
    rw [this, show evReg b cR = kacC b from (evTo_kacC hb).2]
    rfl
  rw [h1, h2, coeff_map, coeff_map]
  exact ⟨((detR (C cR) (X : (regSub b)[X]) N).coeff n).2, rfl⟩

/-- The product `∏_{rs ≤ N} (Δ - h_{r,s}(b))^{p(N-rs)}` of the Kac determinant formula. -/
noncomputable def kacProd {K : Type*} [Field K] (b : K) (N : ℕ) : K[X] :=
  ∏ a ∈ labels N, (X - C (kacHL a b)) ^ Fintype.card (Nat.Partition (N - a.lvl))

/-- The degree of the product of the Kac determinant formula. -/
def kacDeg (N : ℕ) : ℕ := ∑ a ∈ labels N, Fintype.card (Nat.Partition (N - a.lvl))

theorem kacProd_monic {K : Type*} [Field K] (b : K) (N : ℕ) : (kacProd b N).Monic :=
  monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow _

theorem kacProd_natDegree {K : Type*} [Field K] (b : K) (N : ℕ) :
    (kacProd b N).natDegree = kacDeg N := by
  unfold kacProd kacDeg
  rw [natDegree_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem polyEv_kacProd {b : 𝔽} (hb : b ≠ 0) (N : ℕ) :
    PolyEv b (kacProd (RatFunc.X : RatFunc ℚ) N) (kacProd b N) := by
  unfold kacProd
  refine PolyEv.prod _ fun a _ => PolyEv.pow (PolyEv.sub polyEv_X (polyEv_C ?_)) _
  exact evTo_kacH hb (a.1 : ℤ) (a.2 : ℤ)

/-- A rational function over `ℚ` that vanishes at every positive integer is zero. -/
theorem eq_zero_of_evTo_nat (x : RatFunc ℚ)
    (h : ∀ m : ℕ, 1 ≤ m → EvTo ((m : ℕ) : ℂ) x 0) : x = 0 := by
  rw [← RatFunc.num_eq_zero_iff]
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + 1 : ℕ) : ℚ)) ?_ ?_
  · intro m m' hmm
    have h1 : ((m + 1 : ℕ) : ℚ) = ((m' + 1 : ℕ) : ℚ) := hmm
    have : (m + 1 : ℕ) = m' + 1 := Nat.cast_injective h1
    omega
  · intro m
    have hm := h (m + 1) (by omega)
    have h1 : Polynomial.eval₂ (algebraMap ℚ ℂ) (((m + 1 : ℕ) : ℕ) : ℂ) (RatFunc.num x) = 0 := by
      have h2 := hm.2
      rw [RatFunc.eval, div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2 hm.1
    have h3 : (((m + 1 : ℕ) : ℕ) : ℂ) = algebraMap ℚ ℂ ((m + 1 : ℕ) : ℚ) := by
      rw [map_natCast]
    rw [h3, Polynomial.eval₂_at_apply] at h1
    exact (map_eq_zero_iff _ (algebraMap ℚ ℂ).injective).1 h1

/-- The Kac determinant formula over `ℚ(b)`. -/
theorem kac_det_ratQ (hK : Cited_KacDeterminant) (N : ℕ) :
    (gramPoly (kacC (RatFunc.X : RatFunc ℚ)) N).det
      = C ((gramPoly (kacC (RatFunc.X : RatFunc ℚ)) N).det.coeff (kacDeg N))
        * kacProd (RatFunc.X : RatFunc ℚ) N := by
  rw [← sub_eq_zero]
  refine Polynomial.ext fun n => ?_
  rw [coeff_zero]
  refine eq_zero_of_evTo_nat _ fun m hm => ?_
  have hb : ((m : ℕ) : ℂ) ≠ 0 := by
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact this
  have hdet := polyEv_gramDet (b := ((m : ℕ) : ℂ)) hb N
  have hprod := polyEv_kacProd (b := ((m : ℕ) : ℂ)) hb N
  have h1 := (hdet.sub ((polyEv_C (hdet (kacDeg N))).mul hprod)) n
  obtain ⟨C₀, -, hC₀⟩ := hK ((m : ℕ) : ℂ) hb N
  have hcoeff : (gramPoly (kacC ((m : ℕ) : ℂ)) N).det.coeff (kacDeg N) = C₀ := by
    rw [hC₀, coeff_C_mul]
    have := (kacProd_monic ((m : ℕ) : ℂ) N).coeff_natDegree
    rw [kacProd_natDegree] at this
    rw [show (∏ a ∈ labels N, (X - C (kacHL a ((m : ℕ) : ℂ))) ^
        Fintype.card (Nat.Partition (N - a.lvl))) = kacProd ((m : ℕ) : ℂ) N from rfl, this,
      mul_one]
  have hz : (gramPoly (kacC ((m : ℕ) : ℂ)) N).det
      - C ((gramPoly (kacC ((m : ℕ) : ℂ)) N).det.coeff (kacDeg N)) * kacProd ((m : ℕ) : ℂ) N
      = 0 := by
    rw [hcoeff, sub_eq_zero]
    exact hC₀
  rw [hz, coeff_zero] at h1
  exact h1

/-- The Kac determinant formula at every `b ≠ 0` of every field of characteristic zero. -/
theorem kac_det_field (hK : Cited_KacDeterminant) {b : 𝔽} (hb : b ≠ 0) (N : ℕ) :
    ∃ C₀ : 𝔽, C₀ ≠ 0 ∧ (gramPoly (kacC b) N).det = C C₀ * kacProd b N := by
  have hdet := polyEv_gramDet hb N
  have hprod := polyEv_kacProd hb N
  have h1 := (polyEv_C (hdet (kacDeg N))).mul hprod
  rw [← kac_det_ratQ hK N] at h1
  have heq := hdet.unique h1
  refine ⟨(gramPoly (kacC b) N).det.coeff (kacDeg N), ?_, heq⟩
  intro h0
  rw [h0, map_zero, zero_mul] at heq
  exact gramPoly_det_ne_zero (kacC b) N heq

end Virasoro
