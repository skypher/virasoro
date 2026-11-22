import Virasoro.Proofs.Sec6LimChain
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Proposition 6.7, the chain limit (b): graded power series (paper.tex l.1141–1146)

Over `R = ℂ[S,W,Y]`, the power series in `X` whose coefficient of `X^i` is homogeneous of degree
`i` form a `ℚ`-subalgebra.  It contains `b = b⋆ + S X`, its inverse, `Δ = λ + W X` and `d = Y X`:
along the line `(b⋆ + S t, λ + W t, Y t)` each power of `t` comes with one of `S, W, Y`.  This is
the lowest-homogeneous-part bookkeeping of l.1141–1144.
-/

namespace Virasoro.ChainLim

open PowerSeries

/-- `ℂ[S,W,Y]`. -/
abbrev R3 : Type := MvPolynomial (Fin 3) ℂ

/-- `ℂ[S,W,Y][[X]]`. -/
abbrev PS : Type := PowerSeries R3

/-- The coefficient of `X^i` is homogeneous of degree `i`. -/
def IsGr (f : PS) : Prop := ∀ i : ℕ, (coeff i f).IsHomogeneous i

theorem isGr_zero : IsGr 0 := fun i => by simpa using MvPolynomial.isHomogeneous_zero (Fin 3) ℂ i

theorem isGr_one : IsGr 1 := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h
    exact MvPolynomial.isHomogeneous_one (Fin 3) ℂ
  · exact MvPolynomial.isHomogeneous_zero (Fin 3) ℂ i

theorem IsGr.add {f g : PS} (hf : IsGr f) (hg : IsGr g) : IsGr (f + g) := fun i => by
  rw [map_add]
  exact (hf i).add (hg i)

theorem IsGr.neg {f : PS} (hf : IsGr f) : IsGr (-f) := fun i => by
  rw [map_neg]
  exact (hf i).neg

theorem IsGr.mul {f g : PS} (hf : IsGr f) (hg : IsGr g) : IsGr (f * g) := by
  intro i
  rw [coeff_mul]
  apply MvPolynomial.IsHomogeneous.sum
  intro ab hab
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
  rw [← hab]
  exact (hf ab.1).mul (hg ab.2)

theorem isGr_C (x : R3) (hx : x.IsHomogeneous 0) : IsGr (PowerSeries.C x) := by
  intro i
  rw [coeff_C]
  split_ifs with h
  · subst h
    exact hx
  · exact MvPolynomial.isHomogeneous_zero (Fin 3) ℂ i

theorem isGr_algebraMap (q : ℚ) : IsGr (algebraMap ℚ PS q) := by
  have : algebraMap ℚ PS q = PowerSeries.C (MvPolynomial.C (q : ℂ)) := by
    rw [IsScalarTower.algebraMap_apply ℚ R3 PS]
    simp [PowerSeries.algebraMap_apply', MvPolynomial.algebraMap_eq]
  rw [this]
  exact isGr_C _ (MvPolynomial.isHomogeneous_C _ _)

/-- The graded power series as a `ℚ`-subalgebra. -/
def grSub : Subalgebra ℚ PS where
  carrier := {f | IsGr f}
  mul_mem' := fun ha hb => IsGr.mul ha hb
  one_mem' := isGr_one
  add_mem' := fun ha hb => IsGr.add ha hb
  zero_mem' := isGr_zero
  algebraMap_mem' := isGr_algebraMap

theorem mem_grSub {f : PS} : f ∈ grSub ↔ IsGr f := Iff.rfl

theorem isGr_Cc (c : ℂ) : IsGr (PowerSeries.C (MvPolynomial.C c)) :=
  isGr_C _ (MvPolynomial.isHomogeneous_C _ _)

/-- `C(X k) · X`: degree one in `X`, of degree one in `S, W, Y`. -/
theorem isGr_var (k : Fin 3) : IsGr (PowerSeries.C (MvPolynomial.X k) * PowerSeries.X) := by
  intro i
  have e : (PowerSeries.C (MvPolynomial.X k) * PowerSeries.X : PS) =
      PowerSeries.C (MvPolynomial.X k) * PowerSeries.X ^ 1 := by rw [pow_one]
  rw [e, coeff_C_mul_X_pow]
  split_ifs with h
  · subst h
    exact MvPolynomial.isHomogeneous_X ℂ k
  · exact MvPolynomial.isHomogeneous_zero (Fin 3) ℂ i

end Virasoro.ChainLim
