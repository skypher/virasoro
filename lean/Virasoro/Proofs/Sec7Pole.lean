import Virasoro.Statements.Sec7
import Virasoro.Proofs.LaurentLemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Proofs: Lemma 7.5 (coefficientwise pole support of a collision germ)
-/

namespace Virasoro

open scoped LaurentSeries

variable {K L : Type*} [Field K] [Field L]

/-- Coefficientwise extension of a field homomorphism to Laurent series. -/
noncomputable def mapL (ι : K →+* L) : K⸨X⸩ →+* L⸨X⸩ where
  toFun x := x.map ι
  map_one' := by
    ext n
    simp [HahnSeries.coeff_one]
  map_mul' x y := HahnSeries.map_mul (ι : K →ₙ+* L)
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

@[simp] theorem mapL_apply (ι : K →+* L) (x : K⸨X⸩) : mapL ι x = x.map ι := rfl

theorem mapL_coeff (ι : K →+* L) (x : K⸨X⸩) (n : ℤ) : (mapL ι x).coeff n = ι (x.coeff n) := rfl

theorem OrdGE.mapL {ι : K →+* L} {x : K⸨X⸩} {n : ℤ} (h : OrdGE x n) : OrdGE (mapL ι x) n :=
  ordGE_iff.2 fun m hm => by rw [mapL_coeff, h.coeff_eq_zero hm, map_zero]

theorem coeff_mul_C (x : L⸨X⸩) (c : L) (m : ℤ) : (x * HahnSeries.C c).coeff m = x.coeff m * c := by
  have : (HahnSeries.C c : L⸨X⸩) = HahnSeries.single 0 c := rfl
  rw [this, HahnSeries.coeff_mul_single_zero]

/-- The geometric expansion of Lemma 7.5 with remainder: for `x ≠ 0` and `ord_t δ ≥ 1`, the
coefficient of `t^m` in `B/(x - δ)` is `∑_{j<n} [t^m](B δ^j) / x^{j+1}` as soon as
`m < v + n`, where `ord_t B ≥ v`. -/
theorem pole_support (ι : K →+* L) (x : L) (hx : x ≠ 0) (B δ : K⸨X⸩) (hδ : OrdGE δ 1)
    {v : ℤ} (hB : OrdGE B v) (m : ℤ) (n : ℕ) (hn : m < v + n) :
    (mapL ι B / (HahnSeries.C x - mapL ι δ)).coeff m =
      ∑ j ∈ Finset.range n, ι ((B * δ ^ j).coeff m) / x ^ (j + 1) := by
  set u : L⸨X⸩ := HahnSeries.C x - mapL ι δ with hu
  set c : L⸨X⸩ := HahnSeries.C x⁻¹ with hc
  have hCx : (HahnSeries.C x : L⸨X⸩) * c = 1 := by
    rw [hc, ← map_mul, mul_inv_cancel₀ hx, map_one]
  have hu0 : OrdGE u 0 := (ordGE_C x).sub (hδ.mapL.mono (by norm_num))
  have hucoeff : u.coeff 0 = x := by
    rw [hu, HahnSeries.coeff_sub, (hδ.mapL (ι := ι)).coeff_eq_zero (by norm_num : (0 : ℤ) < 1)]
    simp [HahnSeries.C]
  have huord : u.order = 0 := order_eq_zero_of hu0 (by rw [hucoeff]; exact hx)
  have hune : u ≠ 0 := by
    intro h
    rw [h] at hucoeff
    exact hx (by simpa using hucoeff.symm)
  -- geometric identity
  have hgeo : (∑ j ∈ Finset.range n, (mapL ι δ * c) ^ j) * c * u = 1 - (mapL ι δ * c) ^ n := by
    have h1 : c * u = 1 - mapL ι δ * c := by
      rw [hu, mul_sub, mul_comm c (HahnSeries.C x), hCx, mul_comm]
    rw [mul_assoc, h1, mul_comm, mul_neg_geom_sum]
  have hsplit : mapL ι B / u =
      (∑ j ∈ Finset.range n, mapL ι (B * δ ^ j) * c ^ (j + 1)) +
        mapL ι B * (mapL ι δ * c) ^ n / u := by
    have hsum : (∑ j ∈ Finset.range n, mapL ι (B * δ ^ j) * c ^ (j + 1)) =
        mapL ι B * ((∑ j ∈ Finset.range n, (mapL ι δ * c) ^ j) * c) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow]
      ring
    rw [div_eq_iff hune, add_mul, div_mul_cancel₀ _ hune, hsum, mul_assoc, hgeo]
    ring
  rw [hsplit, HahnSeries.coeff_add, HahnSeries.coeff_sum]
  have hrem : (mapL ι B * (mapL ι δ * c) ^ n / u).coeff m = 0 := by
    have h1 : OrdGE ((mapL ι δ * c) ^ n) (n : ℤ) := by
      exact (((hδ.mapL (ι := ι)).mul (ordGE_C x⁻¹)).pow n).mono (le_of_eq (by ring))
    have h2 := ((hB.mapL (ι := ι)).mul h1).div u
    rw [huord, sub_zero] at h2
    exact h2.coeff_eq_zero hn
  rw [hrem, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : c ^ (j + 1) = HahnSeries.C ((x ^ (j + 1))⁻¹) := by
    rw [hc, ← map_pow, inv_pow]
  rw [this, coeff_mul_C, mapL_coeff, div_eq_mul_inv]

/-- Paper label: lem:collision-pole-support -/
theorem lem_collision_pole_support : Stmt_lem_collision_pole_support := by
  intro B δ hδ m
  have hδ1 : OrdGE δ 1 := by
    refine ordGE_iff.2 fun k hk => ?_
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have : ((k : ℤ) : WithTop ℤ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
    exact lt_of_le_of_lt this hδ
  refine ⟨(m - B.order + 1).toNat, fun n' hn' => ?_⟩
  have hlt : m < B.order + n' := by
    have h1 := Int.self_le_toNat (m - B.order + 1)
    have h2 : ((m - B.order + 1).toNat : ℤ) ≤ n' := by exact_mod_cast hn'
    linarith
  have key := pole_support (algebraMap Kd (RatFunc Kd)) (RatFunc.X : RatFunc Kd)
    RatFunc.X_ne_zero B δ hδ1 (ordGE_order B) m n' hlt
  simp only [mapL_apply] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RatFunc.algebraMap_eq_C]

example : Stmt_lem_collision_pole_support := lem_collision_pole_support

end Virasoro
