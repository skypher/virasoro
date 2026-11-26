import Virasoro.Proofs.Sec8DiagBridge
import Virasoro.Proofs.Sec8Jets

/-!
# Lemma 8.4: pole orders of the residues between nodes

`R_g = 𝒜_g 𝒩_g`; `𝒜_g = ½ ∏_{(a,e)} (a b + e b⁻¹)⁻¹`.  At `b⋆² = -p'/p` a factor vanishes exactly
for `(a,e) = i(p,p')`, and then with slope `2ip`; so its germ has order `0` or `1`.  For the label
from `ν` to `ν'` (`Δ = L_{ν'} - L_ν` odd) the box `[1-u,u] × [1-v,v]` contains exactly the points
`i(p,p')` with `1 ≤ |i| ≤ (Δ-1)/2`, and `𝒩_g(b⋆,d) ≠ 0`; so `R_g` has order exactly `1 - Δ`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

section Orders

variable {K : Type*} [Field K]

theorem dgOrderTop_inv {x : K⸨X⸩} (hx : x ≠ 0) : x⁻¹.orderTop = -x.orderTop := by
  have h := HahnSeries.orderTop_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, HahnSeries.orderTop_one] at h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (HahnSeries.orderTop_ne_top.2 hx)
  have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (HahnSeries.orderTop_ne_top.2 hx')
  rw [← hn, ← hm] at h ⊢
  have : (0 : ℤ) = n + m := by exact_mod_cast h
  rw [show m = -n by omega]
  rfl

/-- A germ regular at `0` with nonzero value has order `0`. -/
theorem dgOrderTop_zero {x : K⸨X⸩} (hx : (0 : WithTop ℤ) ≤ x.orderTop) (h0 : x.coeff 0 ≠ 0) :
    x.orderTop = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h0
  apply le_antisymm _ hx
  exact HahnSeries.orderTop_le_of_coeff_ne_zero h0

/-- A germ regular at `0` with value `0` and nonzero slope has order `1`. -/
theorem dgOrderTop_one {x : K⸨X⸩} (hx : (0 : WithTop ℤ) ≤ x.orderTop) (h0 : x.coeff 0 = 0)
    (h1 : x.coeff 1 ≠ 0) : x.orderTop = 1 := by
  apply le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero h1)
  rw [HahnSeries.le_orderTop_iff_forall] at hx ⊢
  intro m hm
  have hm' : m < 1 := by exact_mod_cast hm
  rcases lt_or_eq_of_le (show m ≤ 0 by omega) with h | h
  · exact hx m (by exact_mod_cast h)
  · rw [h]; exact h0

end Orders

section Products

variable {K : Type*} [Field K]

theorem dgOrderTop_prod {α : Type*} (t : Finset α) (f : α → K⸨X⸩) :
    (∏ i ∈ t, f i).orderTop = ∑ i ∈ t, (f i).orderTop := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [HahnSeries.orderTop_one]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, HahnSeries.orderTop_mul, ih]

end Products

/-- The fusion polynomial `𝒩_{u,v}(b⋆, d)` is nonzero in `ℂ(d)`. -/
theorem genP_ratC_ne {b : ℂ} (hb : b ≠ 0) (u v : ℕ) : genP u v (RatFunc.C b : Kd) dvar ≠ 0 := by
  have key : ∀ w : ℂ, RatFunc.C w - (dvar : Kd) ≠ 0 := by
    intro w h
    have h1 := congrArg RatFunc.intDegree (sub_eq_zero.1 h)
    rw [RatFunc.intDegree_C, dvar, RatFunc.intDegree_X] at h1
    exact absurd h1 (by norm_num)
  have hfac : ∀ (k l : ℕ) (σ : ℂ),
      (lamSq (RatFunc.C b : Kd) dvar - ((k : Kd) * RatFunc.C b + RatFunc.C σ * (l : Kd) *
        (RatFunc.C b)⁻¹) ^ 2) / 4 ≠ 0 := by
    intro k l σ
    have e : (lamSq (RatFunc.C b : Kd) dvar - ((k : Kd) * RatFunc.C b + RatFunc.C σ * (l : Kd) *
        (RatFunc.C b)⁻¹) ^ 2) / 4 =
        RatFunc.C (((b + b⁻¹) ^ 2 - ((k : ℂ) * b + σ * l * b⁻¹) ^ 2) / 4) - dvar := by
      unfold lamSq
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_inv₀, map_natCast, map_ofNat]
      ring
    rw [e]
    exact key _
  unfold genP
  refine Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2 fun l _ => ?_
  refine mul_ne_zero ?_ ?_
  · have := hfac k l 1
    simpa using this
  · have := hfac k l (-1)
    have e2 : ((k : Kd) * RatFunc.C b + RatFunc.C (-1 : ℂ) * (l : Kd) * (RatFunc.C b)⁻¹) =
        (k : Kd) * RatFunc.C b - (l : Kd) * (RatFunc.C b)⁻¹ := by simp; ring
    rwa [e2] at this

/-- The value and slope of a factor `a b + e b⁻¹` of `𝒜` along `b = b⋆ + t`. -/
theorem j1_Afac {bs : Kd} (hbs : bs ≠ 0) (a e : ℤ) :
    J1 ((a : Kd⸨X⸩) * bGerm bs + (e : Kd⸨X⸩) * (bGerm bs)⁻¹) ((a : Kd) * bs + (e : Kd) * bs⁻¹)
      ((a : Kd) - (e : Kd) / bs ^ 2) := by
  have h := (((j2_intCast (K := Kd) a).mul (j2_bGerm bs)).add
    ((j2_intCast (K := Kd) e).mul (j2_bGerm_inv hbs))).toJ1
  refine h.congr (by ring) (by ring)

/-- At `b⋆² = -p'/p`: `a b⋆ + e b⋆⁻¹ = 0` iff `p e = p' a`. -/
theorem Afac_zero_iff {p p' : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p)
    (a e : ℤ) : (a : ℂ) * b + (e : ℂ) * b⁻¹ = 0 ↔ (p : ℤ) * e = p' * a := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    have h0 : -(p' : ℂ) / p ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
    exact h0 (by simpa using hb.symm)
  have e1 : (a : ℂ) * b + (e : ℂ) * b⁻¹ = ((p : ℂ) * e - p' * a) / (p * b) := by
    calc (a : ℂ) * b + (e : ℂ) * b⁻¹ = ((a : ℂ) * b ^ 2 + e) / b := by field_simp
      _ = ((a : ℂ) * (-(p' : ℂ) / p) + e) / b := by rw [hb]
      _ = ((p : ℂ) * e - p' * a) / (p * b) := by field_simp; ring
  rw [e1, div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h (mul_ne_zero hpc hb0)
  · intro h; left; exact_mod_cast h

end Virasoro
