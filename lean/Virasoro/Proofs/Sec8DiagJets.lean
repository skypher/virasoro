import Virasoro.Statements.Sec8Diagonal
import Virasoro.Proofs.Jets
import Virasoro.Proofs.Sec8Jets
import Virasoro.Proofs.P2Sec10OrbitArith

/-!
# Section 8.1: slopes of the Kac weights (Lemma 8.3(i))

`h_{u,v}(b) = ((b + b⁻¹)² - (u b + v b⁻¹)²)/4` has `h'_{u,v}(b) = ((1 - u²) b - (1 - v²) b⁻³)/2`;
at `b⋆² = -p'/p` this is `b⋆/(2p'²) (p'²(1 - u²) - p²(1 - v²)) = b⋆/(2p'²)(p'² - p² - x y)`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- The value and the slope of `h_a(b⋆ + t)` at a general base point `bs ≠ 0`. -/
theorem j1_hG_gen {K : Type*} [Field K] [CharZero K] {bs : K} (hbs : bs ≠ 0) (a : Label) :
    J1 (hG bs a) (kacHL a bs)
      (((1 - (a.1 : K) ^ 2) * bs - (1 - (a.2 : K) ^ 2) / bs ^ 3) / 2) := by
  have hs := (j2_bGerm bs).add (j2_bGerm_inv hbs)
  have hsq := hs.mul hs
  have hu := ((j2_intCast (K := K) (a.1 : ℤ)).mul (j2_bGerm bs)).add
    ((j2_intCast (K := K) (a.2 : ℤ)).mul (j2_bGerm_inv hbs))
  have husq := hu.mul hu
  have h := (hsq.sub husq).div (j2_ofNat (K := K) 4) (by norm_num)
  have h1 := h.toJ1
  unfold hG kacHL kacH
  rw [pow_two, pow_two]
  refine h1.congr ?_ ?_
  · push_cast
    ring
  · push_cast
    field_simp
    ring

/-- The slope of `δ_g` is the slope of `h_g`. -/
theorem delG_coeff_one {K : Type*} [Field K] [CharZero K] {bs : K} (hbs : bs ≠ 0) (g : Label) :
    (delG bs g).coeff 1 = ((1 - (g.1 : K) ^ 2) * bs - (1 - (g.2 : K) ^ 2) / bs ^ 3) / 2 := by
  unfold delG deltaG
  rw [HahnSeries.coeff_sub, (j1_hG_gen hbs g).2.2, (j2_C (kacHL g bs)).2.2.1, sub_zero]

/-- Lemma 8.3(i): `h'_g(b⋆) = b⋆/(2p'²)(p'² - p² - x_g y_g)` at `b⋆² = -p'/p`. -/
theorem node_slope {p p' : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p)
    (g : Label) :
    (delG (bsC b) g).coeff 1 =
      pt (varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) -
        (((p' : ℤ) * g.1 - p * g.2 : ℤ) : ℂ) * (((p' : ℤ) * g.1 + p * g.2 : ℤ) : ℂ))) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
    exact h0 (by simpa using hb.symm)
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  rw [delG_coeff_one hbs g]
  have h4 : b ^ 4 = (p' : ℂ) ^ 2 / (p : ℂ) ^ 2 := by
    rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, hb]
    field_simp
  have hb3 : (1 : ℂ) / b ^ 3 = b * (p : ℂ) ^ 2 / (p' : ℂ) ^ 2 := by
    rw [div_eq_iff (pow_ne_zero 3 hb0)]
    have e : b * (p : ℂ) ^ 2 / (p' : ℂ) ^ 2 * b ^ 3 = b ^ 4 * ((p : ℂ) ^ 2 / (p' : ℂ) ^ 2) := by
      ring
    rw [e, h4]
    field_simp
  have hL : ((1 - (g.1 : Kd) ^ 2) * RatFunc.C b - (1 - (g.2 : Kd) ^ 2) / RatFunc.C b ^ 3) / 2 =
      RatFunc.C (((1 - (g.1 : ℂ) ^ 2) * b - (1 - (g.2 : ℂ) ^ 2) * (1 / b ^ 3)) / 2) := by
    simp only [map_div₀, map_sub, map_mul, map_pow, map_one, map_natCast, map_ofNat]
    ring
  simp only [bsC, pt, varsig]
  rw [hL]
  congr 1
  rw [hb3]
  push_cast
  field_simp
  ring

end Virasoro
