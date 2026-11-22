import Virasoro.Proofs.Sec6LimGr2
import Virasoro.Proofs.Sec4Core2
import Virasoro.Proofs.EvalLemmas

/-!
# Proposition 6.7, the chain limit (b): the common denominator of `H_N` (paper.tex l.1141–1144)

`H_N = P/D` with `D = ∏_{M ≤ N} det G_M` and `P = ∑_j η_j num_{N−j} ∏_{M ≠ N−j} det G_M`, both
natural in ring homomorphisms.  Over the graded power series both are graded, and `D` does not
involve `Y` (it does not involve `d`).
-/

namespace Virasoro.ChainLim

open Finset PowerSeries

section Common

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `D = ∏_{M ≤ N} det G_M(c,h)`. -/
noncomputable def denH (c h : R) (N : ℕ) : R := ∏ M ∈ range (N + 1), detR c h M

/-- `P = ∑_j η_j num_{N−j} ∏_{M ≠ N−j} det G_M`. -/
noncomputable def numH (c h d : R) (N : ℕ) : R :=
  ∑ j ∈ range (N + 1), (eta j : R) * numR c h d (N - j) *
    ∏ M ∈ (range (N + 1)).erase (N - j), detR c h M

variable {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S)

theorem map_denH (c h : R) (N : ℕ) : f (denH c h N) = denH (f c) (f h) N := by
  simp only [denH, map_prod, map_detR]

theorem map_numH (c h d : R) (N : ℕ) : f (numH c h d N) = numH (f c) (f h) (f d) N := by
  simp only [numH, map_sum, map_mul, map_prod, map_intCast, map_numR, map_detR]

end Common

theorem Hval_eq_numH {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽] {c d z : 𝔽} {N : ℕ}
    (h : ∀ M ≤ N, (gram c z M).det ≠ 0) : Hval c d z N = numH c z d N / denH c z N := by
  have hD : ∀ M ∈ range (N + 1), detR c z M ≠ 0 := fun M hM =>
    h M (Nat.lt_succ_iff.1 (mem_range.1 hM))
  have hDen : denH c z N ≠ 0 := prod_ne_zero_iff.2 hD
  rw [eq_div_iff hDen, Hval, sum_mul, numH]
  refine sum_congr rfl fun j hj => ?_
  have hmem : N - j ∈ range (N + 1) := mem_range.2 (by omega)
  have hd := hD _ hmem
  have hF : Fval c d z (N - j) = numR c z d (N - j) / detR c z (N - j) := rfl
  rw [hF, denH, ← mul_prod_erase _ _ hmem]
  field_simp

theorem denH_ne_zero {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽] {c z : 𝔽} {N : ℕ}
    (h : ∀ M ≤ N, (gram c z M).det ≠ 0) : denH c z N ≠ 0 :=
  prod_ne_zero_iff.2 fun M hM => h M (Nat.lt_succ_iff.1 (mem_range.1 hM))

/-! ### Membership in subalgebras of `PS` -/

theorem denH_mem (A : Subalgebra ℚ PS) {c h : PS} (hc : c ∈ A) (hh : h ∈ A) (N : ℕ) :
    denH c h N ∈ A :=
  prod_mem fun M _ => det_mem' A hc hh M

theorem numH_mem (A : Subalgebra ℚ PS) {c h d : PS} (hc : c ∈ A) (hh : h ∈ A) (hd : d ∈ A)
    (N : ℕ) : numH c h d N ∈ A :=
  sum_mem fun j _ => A.mul_mem (A.mul_mem (intCast_mem A _) (fnum_mem A hc hh hd _))
    (prod_mem fun M _ => det_mem' A hc hh M)

/-- The power series whose coefficients do not involve `Y`. -/
def noY : Subalgebra ℚ PS where
  carrier := {f | ∀ i, coeff i f ∈ MvPolynomial.supported ℂ ({0, 1} : Set (Fin 3))}
  mul_mem' := by
    intro f g hf hg i
    rw [coeff_mul]
    exact sum_mem fun ab _ => Subalgebra.mul_mem _ (hf ab.1) (hg ab.2)
  one_mem' := by
    intro i
    rw [coeff_one]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  add_mem' := by
    intro f g hf hg i
    rw [map_add]
    exact Subalgebra.add_mem _ (hf i) (hg i)
  zero_mem' := fun i => by rw [map_zero]; exact Subalgebra.zero_mem _
  algebraMap_mem' := by
    intro q i
    have : algebraMap ℚ PS q = PowerSeries.C (MvPolynomial.C (q : ℂ)) := by
      rw [IsScalarTower.algebraMap_apply ℚ R3 PS]
      simp [PowerSeries.algebraMap_apply', MvPolynomial.algebraMap_eq]
    rw [this, coeff_C]
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _

theorem mem_noY {f : PS} :
    f ∈ noY ↔ ∀ i, coeff i f ∈ MvPolynomial.supported ℂ ({0, 1} : Set (Fin 3)) := Iff.rfl

theorem Cc_mem_noY (c : ℂ) : PowerSeries.C (MvPolynomial.C c) ∈ noY := by
  intro i
  rw [coeff_C]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem var_mem_noY {k : Fin 3} (hk : k ∈ ({0, 1} : Set (Fin 3))) :
    PowerSeries.C (MvPolynomial.X k) * PowerSeries.X ∈ noY := by
  intro i
  have e : (PowerSeries.C (MvPolynomial.X k) * PowerSeries.X : PS) =
      PowerSeries.C (MvPolynomial.X k) * PowerSeries.X ^ 1 := by rw [pow_one]
  rw [e, coeff_C_mul_X_pow]
  split_ifs
  · exact MvPolynomial.X_mem_supported.2 hk
  · exact Subalgebra.zero_mem _

theorem Bb_mem_noY (bs : ℂ) : Bb bs ∈ noY :=
  noY.add_mem (Cc_mem_noY bs) (var_mem_noY (by simp))

theorem Binv_mem_noY (bs : ℂ) : Binv bs ∈ noY := by
  intro i
  rw [Binv, coeff_mk]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (MvPolynomial.X_mem_supported.2 (by simp)) _)

theorem DR_mem_noY (lam : ℂ) : DR lam ∈ noY :=
  noY.add_mem (Cc_mem_noY lam) (var_mem_noY (by simp))

theorem cR_mem_noY (bs : ℂ) : cR bs ∈ noY := by
  unfold cR
  have h6 : (6 : PS) ∈ noY := by
    have := noY.algebraMap_mem (6 : ℚ)
    simpa using this
  exact noY.add_mem noY.one_mem
    (noY.mul_mem h6 (noY.pow_mem (noY.add_mem (Bb_mem_noY bs) (Binv_mem_noY bs)) 2))

/-- The graded numerator and denominator along `(b⋆ + S t, λ + W t, Y t)`. -/
noncomputable def NumG (bs lam : ℂ) (N : ℕ) : PS := numH (cR bs) (DR lam) dR N

noncomputable def DenG (bs lam : ℂ) (N : ℕ) : PS := denH (cR bs) (DR lam) N

theorem NumG_mem (bs lam : ℂ) (N : ℕ) : NumG bs lam N ∈ grSub :=
  numH_mem grSub (cR_mem bs) (DR_mem lam) dR_mem N

theorem DenG_mem (bs lam : ℂ) (N : ℕ) : DenG bs lam N ∈ grSub :=
  denH_mem grSub (cR_mem bs) (DR_mem lam) N

theorem DenG_mem_noY (bs lam : ℂ) (N : ℕ) : DenG bs lam N ∈ noY :=
  denH_mem noY (cR_mem_noY bs) (DR_mem_noY lam) N

end Virasoro.ChainLim
