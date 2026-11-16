import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.Germs
import Virasoro.Proofs.Sec4Core2
import Virasoro.Proofs.PoleBound

/-!
# Rational functions of `Δ` over `K((t))` regular at a point `(t, Δ) = (0, z)`

A rational function `f ∈ K((t))(Δ)` is regular at `(0, z)` if it is a quotient `P/E` of
polynomials in `Δ` with coefficients in `K[[t]]` such that `E(0, z) ≠ 0`.  Such a function
restricts to `t = 0` (a rational function of `Δ` over `K` regular at `z`) and to every curve
`Δ = w(t)` with `w(0) = z` (a power series in `t`); the two restrictions have the same value at
the point.  A regular function vanishing on a curve `Δ = h(t)` through the point is divisible by
`Δ - h(t)` with regular quotient.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

variable {K : Type*} [Field K]

/-- The inclusion `K[[t]] → K((t))`. -/
noncomputable abbrev toLS : PowerSeries K →+* K⸨X⸩ := HahnSeries.ofPowerSeries ℤ K

/-- The reduction `t ↦ 0`. -/
noncomputable abbrev red0 : PowerSeries K →+* K := PowerSeries.constantCoeff

/-- A polynomial in `Δ` over `K[[t]]` as a rational function of `Δ` over `K((t))`. -/
noncomputable def upHom : (PowerSeries K)[X] →+* RatFunc K⸨X⸩ :=
  (algebraMap K⸨X⸩[X] (RatFunc K⸨X⸩)).comp (mapRingHom toLS)

/-- The restriction to `t = 0` of a polynomial in `Δ` over `K[[t]]`. -/
noncomputable def dnHom : (PowerSeries K)[X] →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp (mapRingHom red0)

theorem upHom_apply (P : (PowerSeries K)[X]) :
    upHom P = algebraMap K⸨X⸩[X] (RatFunc K⸨X⸩) (P.map toLS) := rfl

theorem dnHom_apply (P : (PowerSeries K)[X]) :
    dnHom P = algebraMap K[X] (RatFunc K) (P.map red0) := rfl

theorem toLS_injective : Function.Injective (toLS : PowerSeries K →+* K⸨X⸩) :=
  HahnSeries.ofPowerSeries_injective

theorem upHom_injective : Function.Injective (upHom : (PowerSeries K)[X] →+* RatFunc K⸨X⸩) := by
  intro P Q h
  have h1 := IsFractionRing.injective K⸨X⸩[X] (RatFunc K⸨X⸩) h
  exact Polynomial.map_injective toLS toLS_injective h1

theorem upHom_C (p : PowerSeries K) : upHom (C p) = RatFunc.C (toLS p) := by
  rw [upHom_apply, Polynomial.map_C, RatFunc.algebraMap_C]

theorem dnHom_C (p : PowerSeries K) : dnHom (C p) = RatFunc.C (red0 p) := by
  rw [dnHom_apply, Polynomial.map_C, RatFunc.algebraMap_C]

theorem upHom_X : upHom (X : (PowerSeries K)[X]) = RatFunc.X := by
  rw [upHom_apply, Polynomial.map_X, RatFunc.algebraMap_X]

theorem dnHom_X : dnHom (X : (PowerSeries K)[X]) = RatFunc.X := by
  rw [dnHom_apply, Polynomial.map_X, RatFunc.algebraMap_X]

/-- `f` is regular at `(t, Δ) = (0, z)`, with restriction `f₀` to `t = 0`. -/
def Reg2 (z : K) (f : RatFunc K⸨X⸩) (f₀ : RatFunc K) : Prop :=
  ∃ P E : (PowerSeries K)[X], (E.map red0).eval z ≠ 0 ∧ f = upHom P / upHom E ∧
    f₀ = dnHom P / dnHom E

theorem dnHom_ne_zero {z : K} {E : (PowerSeries K)[X]} (h : (E.map red0).eval z ≠ 0) :
    dnHom E ≠ 0 := by
  rw [dnHom_apply]
  refine (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 ?_
  intro h0
  rw [h0, eval_zero] at h
  exact h rfl

theorem upHom_ne_zero {z : K} {E : (PowerSeries K)[X]} (h : (E.map red0).eval z ≠ 0) :
    upHom E ≠ 0 := by
  refine (map_ne_zero_iff _ upHom_injective).2 ?_
  intro h0
  rw [h0, Polynomial.map_zero, eval_zero] at h
  exact h rfl

theorem reg2_poly (z : K) (P : (PowerSeries K)[X]) : Reg2 z (upHom P) (dnHom P) :=
  ⟨P, 1, by simp, by simp, by simp⟩

theorem reg2_C (z : K) (p : PowerSeries K) : Reg2 z (RatFunc.C (toLS p)) (RatFunc.C (red0 p)) := by
  have := reg2_poly z (C p)
  rwa [upHom_C, dnHom_C] at this

theorem reg2_X_sub_C (z : K) (p : PowerSeries K) :
    Reg2 z (RatFunc.X - RatFunc.C (toLS p)) (RatFunc.X - RatFunc.C (red0 p)) := by
  have := reg2_poly z (X - C p)
  rwa [map_sub, map_sub, upHom_C, dnHom_C, upHom_X, dnHom_X] at this

theorem reg2_intCast (z : K) (n : ℤ) : Reg2 z (n : RatFunc K⸨X⸩) (n : RatFunc K) := by
  have := reg2_poly z ((n : (PowerSeries K)[X]))
  rwa [map_intCast, map_intCast] at this

theorem reg2_div (z : K) (P : (PowerSeries K)[X]) {E : (PowerSeries K)[X]}
    (hE : (E.map red0).eval z ≠ 0) : Reg2 z (upHom P / upHom E) (dnHom P / dnHom E) :=
  ⟨P, E, hE, rfl, rfl⟩

theorem Reg2.add {z : K} {f g : RatFunc K⸨X⸩} {f₀ g₀ : RatFunc K} (hf : Reg2 z f f₀)
    (hg : Reg2 z g g₀) : Reg2 z (f + g) (f₀ + g₀) := by
  obtain ⟨P, E, hE, rfl, rfl⟩ := hf
  obtain ⟨P', E', hE', rfl, rfl⟩ := hg
  refine ⟨P * E' + E * P', E * E', ?_, ?_, ?_⟩
  · rw [Polynomial.map_mul, eval_mul]
    exact mul_ne_zero hE hE'
  · rw [div_add_div _ _ (upHom_ne_zero hE) (upHom_ne_zero hE'), map_add, map_mul, map_mul,
      map_mul]
  · rw [div_add_div _ _ (dnHom_ne_zero hE) (dnHom_ne_zero hE'), map_add, map_mul, map_mul,
      map_mul]

theorem Reg2.mul {z : K} {f g : RatFunc K⸨X⸩} {f₀ g₀ : RatFunc K} (hf : Reg2 z f f₀)
    (hg : Reg2 z g g₀) : Reg2 z (f * g) (f₀ * g₀) := by
  obtain ⟨P, E, hE, rfl, rfl⟩ := hf
  obtain ⟨P', E', hE', rfl, rfl⟩ := hg
  refine ⟨P * P', E * E', ?_, ?_, ?_⟩
  · rw [Polynomial.map_mul, eval_mul]
    exact mul_ne_zero hE hE'
  · rw [div_mul_div_comm, map_mul, map_mul]
  · rw [div_mul_div_comm, map_mul, map_mul]

theorem Reg2.sub {z : K} {f g : RatFunc K⸨X⸩} {f₀ g₀ : RatFunc K} (hf : Reg2 z f f₀)
    (hg : Reg2 z g g₀) : Reg2 z (f - g) (f₀ - g₀) := by
  have h1 : Reg2 z (-1 : RatFunc K⸨X⸩) (-1 : RatFunc K) := by
    have := reg2_intCast (K := K) z (-1)
    simpa using this
  have := hf.add (h1.mul hg)
  simpa [sub_eq_add_neg] using this

theorem Reg2.sum {α : Type*} {z : K} {s : Finset α} {f : α → RatFunc K⸨X⸩}
    {f₀ : α → RatFunc K} (h : ∀ i ∈ s, Reg2 z (f i) (f₀ i)) :
    Reg2 z (∑ i ∈ s, f i) (∑ i ∈ s, f₀ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := reg2_intCast (K := K) z 0
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The restriction to `t = 0` is regular at `z`, and its Laurent expansion at `z` is a power
series with constant term its value. -/
theorem Reg2.expand [CharZero K] {z : K} {f : RatFunc K⸨X⸩} {f₀ : RatFunc K} (hf : Reg2 z f f₀) :
    RegAt z f₀ ∧ RegVal (expandAt f₀ z) (evalAt z f₀) := by
  obtain ⟨P, E, hE, rfl, rfl⟩ := hf
  rw [dnHom_apply, dnHom_apply]
  refine ⟨regAt_div z _ hE, ?_⟩
  rw [evalAt_div z _ hE, expandAt_eq, map_div₀, expandHom_algebraMap, expandHom_algebraMap]
  have h1 := regVal_ofPowerSeries (shiftPS z (P.map red0))
  have h2 := regVal_ofPowerSeries (shiftPS z (E.map red0))
  rw [constantCoeff_shiftPS] at h1 h2
  exact h1.div h2 hE

theorem eval_map_toLS (P : (PowerSeries K)[X]) (w : PowerSeries K) :
    (P.map toLS).eval (toLS w) = toLS (P.eval w) := by
  rw [eval_map, eval₂_at_apply]

theorem eval_map_red0 (P : (PowerSeries K)[X]) (w : PowerSeries K) :
    (P.map red0).eval (red0 w) = red0 (P.eval w) := by
  rw [eval_map, eval₂_at_apply]

/-- The restriction of a regular function to a curve `Δ = w(t)` through the point is a power
series whose constant term is the value at `z` of the restriction to `t = 0`. -/
theorem Reg2.curve [CharZero K] {z : K} {f : RatFunc K⸨X⸩} {f₀ : RatFunc K} (hf : Reg2 z f f₀)
    (w : PowerSeries K) (hw : red0 w = z) :
    RegAt (toLS w) f ∧ RegVal (evalAt (toLS w) f) (evalAt z f₀) := by
  obtain ⟨P, E, hE, rfl, rfl⟩ := hf
  have hE2 : red0 (E.eval w) ≠ 0 := by
    rw [← eval_map_red0, hw]
    exact hE
  have hE1 : (E.map toLS).eval (toLS w) ≠ 0 := by
    rw [eval_map_toLS]
    intro h0
    apply hE2
    rw [toLS_injective (h0.trans (map_zero _).symm), map_zero]
  rw [upHom_apply, upHom_apply, dnHom_apply, dnHom_apply]
  refine ⟨regAt_div _ _ hE1, ?_⟩
  rw [evalAt_div _ _ hE1, evalAt_div z _ hE, eval_map_toLS, eval_map_toLS, ← hw, eval_map_red0,
    eval_map_red0]
  exact (regVal_ofPowerSeries _).div (regVal_ofPowerSeries _) hE2

/-- A regular function vanishing on the curve `Δ = h(t)` through the point is divisible by
`Δ - h(t)`, with regular quotient. -/
theorem Reg2.div_linear {z : K} {f : RatFunc K⸨X⸩} {f₀ : RatFunc K} (hf : Reg2 z f f₀)
    (h : PowerSeries K) (hh : red0 h = z) (hzero : evalAt (toLS h) f = 0) :
    Reg2 z (f / (RatFunc.X - RatFunc.C (toLS h))) (f₀ / (RatFunc.X - RatFunc.C z)) := by
  obtain ⟨P, E, hE, rfl, rfl⟩ := hf
  have hE2 : red0 (E.eval h) ≠ 0 := by
    rw [← eval_map_red0, hh]
    exact hE
  have hE1 : (E.map toLS).eval (toLS h) ≠ 0 := by
    rw [eval_map_toLS]
    intro h0
    apply hE2
    rw [toLS_injective (h0.trans (map_zero _).symm), map_zero]
  rw [upHom_apply, upHom_apply, evalAt_div _ _ hE1, div_eq_zero_iff, eval_map_toLS] at hzero
  have hP : P.eval h = 0 := toLS_injective ((hzero.resolve_right hE1).trans (map_zero _).symm)
  obtain ⟨W, rfl⟩ := dvd_iff_isRoot.2 hP
  have hup : upHom (X - C h : (PowerSeries K)[X]) = RatFunc.X - RatFunc.C (toLS h) := by
    rw [map_sub, upHom_X, upHom_C]
  have hdn : dnHom (X - C h : (PowerSeries K)[X]) = RatFunc.X - RatFunc.C z := by
    rw [map_sub, dnHom_X, dnHom_C, hh]
  have hne1 : (RatFunc.X - RatFunc.C (toLS h) : RatFunc K⸨X⸩) ≠ 0 := by
    rw [← hup]
    refine (map_ne_zero_iff _ upHom_injective).2 (X_sub_C_ne_zero h)
  have hne2 : (RatFunc.X - RatFunc.C z : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 (X_sub_C_ne_zero z)
  refine ⟨W, E, hE, ?_, ?_⟩
  · have hE0 := upHom_ne_zero hE
    rw [map_mul, hup]
    field_simp
  · have hE0 := dnHom_ne_zero hE
    rw [map_mul, hdn]
    field_simp

end Virasoro
