import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

/-!
# The ring `A[[z]]/(z^{N+1})` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.637–638: "Fix `N ≥ 0` and work algebraically in the formal ring
`ℂ[[z]]/(z^{N+1})`."  The coefficient ring `A` is `ℂ((t))`, `ℂ[[t]]` or `ℂ` (`t = 1/λ`).
-/

namespace Virasoro.Sphere

open PowerSeries

section Trunc

variable (N : ℕ) (A : Type*) [CommRing A]

/-- `A[[z]]/(z^{N+1})`. -/
def TR : Type _ := PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)}

noncomputable instance : CommRing (TR N A) :=
  inferInstanceAs (CommRing (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)}))

noncomputable instance [Algebra ℚ A] : Algebra ℚ (TR N A) :=
  inferInstanceAs (Algebra ℚ (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)}))

/-- The reduction `A[[z]] → A[[z]]/(z^{N+1})`. -/
noncomputable def mkT : PowerSeries A →+* TR N A :=
  Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)})

variable {N A}

theorem mkT_surjective : Function.Surjective (mkT N A) :=
  Ideal.Quotient.mk_surjective (I := Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)})

theorem algebraMap_TR [Algebra ℚ A] (q : ℚ) :
    algebraMap ℚ (TR N A) q = mkT N A (PowerSeries.C (algebraMap ℚ A q)) := by
  show algebraMap ℚ (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)}) q = _
  rw [IsScalarTower.algebraMap_apply ℚ (PowerSeries A)
    (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)}),
    PowerSeries.algebraMap_apply]
  rfl

theorem mkT_eq_zero_iff (f : PowerSeries A) : mkT N A f = 0 ↔ ∀ j ≤ N, coeff j f = 0 := by
  have h : mkT N A f = 0 ↔ f ∈ Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)} :=
    Ideal.Quotient.eq_zero_iff_mem
  rw [h, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  exact forall_congr' fun j => by rw [Nat.lt_succ_iff]

theorem mkT_eq_iff (f g : PowerSeries A) :
    mkT N A f = mkT N A g ↔ ∀ j ≤ N, coeff j f = coeff j g := by
  rw [← sub_eq_zero, ← map_sub, mkT_eq_zero_iff]
  exact forall₂_congr fun j _ => by rw [map_sub, sub_eq_zero]

theorem mkT_X_pow : (mkT N A PowerSeries.X) ^ (N + 1) = 0 := by
  rw [← map_pow, mkT_eq_zero_iff]
  intro j hj
  rw [PowerSeries.coeff_X_pow, if_neg (by omega)]

/-- The coefficient of `z^j`, `j ≤ N`, of an element of `A[[z]]/(z^{N+1})`. -/
noncomputable def cfT (j : ℕ) (x : TR N A) : A := coeff j (Classical.choose (mkT_surjective x))

theorem mkT_out (x : TR N A) : mkT N A (Classical.choose (mkT_surjective x)) = x :=
  Classical.choose_spec (mkT_surjective x)

theorem cf_mkT {j : ℕ} (hj : j ≤ N) (f : PowerSeries A) : cfT j (mkT N A f) = coeff j f :=
  (mkT_eq_iff _ _).1 (mkT_out (mkT N A f)) j hj

theorem cf_add {j : ℕ} (hj : j ≤ N) (x y : TR N A) : cfT j (x + y) = cfT j x + cfT j y := by
  obtain ⟨f, rfl⟩ := mkT_surjective x
  obtain ⟨g, rfl⟩ := mkT_surjective y
  rw [← map_add, cf_mkT hj, cf_mkT hj, cf_mkT hj, map_add]

theorem cf_zero (j : ℕ) (hj : j ≤ N) : cfT j (0 : TR N A) = 0 := by
  rw [← map_zero (mkT N A), cf_mkT hj, map_zero]

theorem cf_sum {ι : Type*} (s : Finset ι) (f : ι → TR N A) {j : ℕ} (hj : j ≤ N) :
    cfT j (∑ i ∈ s, f i) = ∑ i ∈ s, cfT j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf_zero j hj]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cf_add hj, ih]

theorem ext_cf {x y : TR N A} (h : ∀ j ≤ N, cfT j x = cfT j y) : x = y := by
  obtain ⟨f, rfl⟩ := mkT_surjective x
  obtain ⟨g, rfl⟩ := mkT_surjective y
  rw [mkT_eq_iff]
  intro j hj
  have := h j hj
  rwa [cf_mkT hj, cf_mkT hj] at this

/-- `cfT j (c z^k x) = c · cfT (j - k) x` for `k ≤ j`, and `0` for `j < k`. -/
theorem cf_C_mul_X_pow_mul {j : ℕ} (hj : j ≤ N) (c : A) (k : ℕ) (x : TR N A) :
    cfT j (mkT N A (PowerSeries.C c) * mkT N A PowerSeries.X ^ k * x) =
      if k ≤ j then c * cfT (j - k) x else 0 := by
  obtain ⟨f, rfl⟩ := mkT_surjective x
  rw [← map_pow, ← map_mul, ← map_mul, cf_mkT hj, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [cf_mkT (by omega)]
  · rw [mul_zero]

variable {B : Type*} [CommRing B]

/-- Base change of the coefficients. -/
noncomputable def mapT (ψ : A →+* B) : TR N A →+* TR N B :=
  Ideal.quotientMap (Ideal.span {(PowerSeries.X : PowerSeries B) ^ (N + 1)}) (PowerSeries.map ψ)
    (I := Ideal.span {(PowerSeries.X : PowerSeries A) ^ (N + 1)}) (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, PowerSeries.map_X]
    exact Ideal.mem_span_singleton_self _)

theorem mapT_mkT (ψ : A →+* B) (f : PowerSeries A) :
    mapT ψ (mkT N A f) = mkT N B (PowerSeries.map ψ f) :=
  Ideal.quotientMap_mk

theorem cf_mapT (ψ : A →+* B) {j : ℕ} (hj : j ≤ N) (x : TR N A) :
    cfT j (mapT ψ x) = ψ (cfT j x) := by
  obtain ⟨f, rfl⟩ := mkT_surjective x
  rw [mapT_mkT, cf_mkT hj, cf_mkT hj, PowerSeries.coeff_map]

end Trunc

end Virasoro.Sphere
