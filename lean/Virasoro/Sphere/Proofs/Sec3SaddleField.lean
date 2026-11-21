import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

/-!
# Sphere paper Lemma 3.4(i): the rational identities in `(s₁,s₂,s₃)`
(`sphere/paper.tex` l.737–747)

The `σ¹` and `σ²` components of the order-`λ⁰` equation are rational identities in
`a = √(1-p)`, `b = √(1-q)`, `c = √(1-r)`.  They are stated here in a field, with the
`q`- and `r`-derivatives of the series entering through their differentiated defining relations.

Consumer: `Sec3SaddlePde1.lean`, `Sec3SaddlePde2.lean` (part (i) of `Stmt_lem_saddle`).
-/

namespace Virasoro.Sphere

/-- The second identity of l.739–741: `(1-p)^{-1/2} B(p,q) = q∂_q(D - V)` with
`D = (p/a - q/b)/(p-q)`, `V = (1/b)/(1-p)`. -/
theorem alg_sigma1 {K : Type*} [Field K] [CharZero K]
    (a b u0 u1 p q D V B db du1 dD dV : K)
    (ha : a ^ 2 = 1 - p) (hb : b ^ 2 = 1 - q) (hpq : p - q ≠ 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h1 : u0 * a = 1) (h2 : u1 * b = 1)
    (hD : (p - q) * D = p * u0 - q * u1) (hV : (1 - p) * V = u1)
    (hB : B * (2 * a * b * (a + b) ^ 2) = -(p * q))
    (hdb : 2 * b * db = -1) (hdu : du1 * b + u1 * db = 0)
    (hdD : (p - q) * dD - D = -u1 - q * du1) (hdV : (1 - p) * dV = du1) :
    u0 * B = q * (dD - dV) := by
  obtain rfl : p = 1 - a ^ 2 := by linear_combination ha
  obtain rfl : q = 1 - b ^ 2 := by linear_combination hb
  have hfac : (b - a) * (a + b) ≠ 0 := by
    intro h
    apply hpq
    linear_combination h
  have hba : b - a ≠ 0 := left_ne_zero_of_mul hfac
  have hab : a + b ≠ 0 := right_ne_zero_of_mul hfac
  have h2' : (2 : K) ≠ 0 := by norm_num
  obtain rfl : du1 = 1 / (2 * b ^ 3) :=
    eq_div_of_mul_eq (mul_ne_zero h2' (pow_ne_zero 3 hb0))
      (by linear_combination 2 * b ^ 2 * hdu - (2 * b * db) * h2 - hdb)
  obtain rfl : u0 = 1 / a := eq_div_of_mul_eq ha0 h1
  obtain rfl : u1 = 1 / b := eq_div_of_mul_eq hb0 h2
  obtain rfl : db = -1 / (2 * b) :=
    eq_div_of_mul_eq (mul_ne_zero h2' hb0) (by linear_combination hdb)
  have hD' : D = ((1 - a ^ 2) * (1 / a) - (1 - b ^ 2) * (1 / b)) / ((b - a) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hD)
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  have hV' : V = (1 / b) / a ^ 2 :=
    eq_div_of_mul_eq ha2 (by linear_combination hV)
  have hdV' : dV = (1 / (2 * b ^ 3)) / a ^ 2 :=
    eq_div_of_mul_eq ha2 (by linear_combination hdV)
  have hden : (2 * a * b * (a + b) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2' ha0) hb0) (pow_ne_zero 2 hab)
  have hB' : B = -((1 - a ^ 2) * (1 - b ^ 2)) / (2 * a * b * (a + b) ^ 2) :=
    eq_div_of_mul_eq hden hB
  have hdD' : dD = (D - 1 / b - (1 - b ^ 2) * (1 / (2 * b ^ 3))) / ((b - a) * (a + b)) :=
    eq_div_of_mul_eq hfac (by linear_combination hdD)
  rw [hdD', hD', hdV', hB']
  field_simp
  ring

/-- The third identity of l.742–745:
`q∂_q(T₁ - U) + r∂_r(T₂ - U) = B(p,q)B(p,r)` with `T₁ = p(B(q,r) - B(p,r))/(q-p)`,
`T₂ = p(B(q,r) - B(p,q))/(r-p)`, `U = pB(q,r)/(1-p)`. -/
theorem alg_sigma2 {K : Type*} [Field K] [CharZero K]
    (a b c p q r B1 B2 B3 T1 T2 U db dc dqB3 drB3 dqT1 drT2 dqU drU : K)
    (ha : a ^ 2 = 1 - p) (hb : b ^ 2 = 1 - q) (hc : c ^ 2 = 1 - r)
    (hqp : q - p ≠ 0) (hrp : r - p ≠ 0) (hqr : q - r ≠ 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hB1 : B1 * (2 * a * b * (a + b) ^ 2) = -(p * q))
    (hB2 : B2 * (2 * a * c * (a + c) ^ 2) = -(p * r))
    (hB3 : B3 * (2 * b * c * (b + c) ^ 2) = -(q * r))
    (hT1 : (q - p) * T1 = p * B3 - p * B2) (hT2 : (r - p) * T2 = p * B3 - p * B1)
    (hU : (1 - p) * U = p * B3)
    (hdb : 2 * b * db = -1) (hdc : 2 * c * dc = -1)
    (hdqB3 : dqB3 * (2 * b * c * (b + c) ^ 2) +
      B3 * (2 * db * c * (b + c) ^ 2 + 2 * b * c * (2 * (b + c) * db)) = -r)
    (hdrB3 : drB3 * (2 * b * c * (b + c) ^ 2) +
      B3 * (2 * b * dc * (b + c) ^ 2 + 2 * b * c * (2 * (b + c) * dc)) = -q)
    (hdqT1 : T1 + (q - p) * dqT1 = p * dqB3) (hdrT2 : T2 + (r - p) * drT2 = p * drB3)
    (hdqU : (1 - p) * dqU = p * dqB3) (hdrU : (1 - p) * drU = p * drB3) :
    q * (dqT1 - dqU) + r * (drT2 - drU) = B1 * B2 := by
  obtain rfl : p = 1 - a ^ 2 := by linear_combination ha
  obtain rfl : q = 1 - b ^ 2 := by linear_combination hb
  obtain rfl : r = 1 - c ^ 2 := by linear_combination hc
  have hfab : (a - b) * (a + b) ≠ 0 := by
    intro h
    apply hqp
    linear_combination h
  have hfac : (a - c) * (a + c) ≠ 0 := by
    intro h
    apply hrp
    linear_combination h
  have hfbc : (c - b) * (b + c) ≠ 0 := by
    intro h
    apply hqr
    linear_combination h
  have hamb : a - b ≠ 0 := left_ne_zero_of_mul hfab
  have hab : a + b ≠ 0 := right_ne_zero_of_mul hfab
  have hamc : a - c ≠ 0 := left_ne_zero_of_mul hfac
  have hac : a + c ≠ 0 := right_ne_zero_of_mul hfac
  have hbc : b + c ≠ 0 := right_ne_zero_of_mul hfbc
  have h2' : (2 : K) ≠ 0 := by norm_num
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  obtain rfl : db = -1 / (2 * b) :=
    eq_div_of_mul_eq (mul_ne_zero h2' hb0) (by linear_combination hdb)
  obtain rfl : dc = -1 / (2 * c) :=
    eq_div_of_mul_eq (mul_ne_zero h2' hc0) (by linear_combination hdc)
  have hB1' : B1 = -((1 - a ^ 2) * (1 - b ^ 2)) / (2 * a * b * (a + b) ^ 2) :=
    eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero (mul_ne_zero h2' ha0) hb0) (pow_ne_zero 2 hab)) hB1
  have hB2' : B2 = -((1 - a ^ 2) * (1 - c ^ 2)) / (2 * a * c * (a + c) ^ 2) :=
    eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero (mul_ne_zero h2' ha0) hc0) (pow_ne_zero 2 hac)) hB2
  have hden3 : (2 * b * c * (b + c) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2' hb0) hc0) (pow_ne_zero 2 hbc)
  have hB3' : B3 = -((1 - b ^ 2) * (1 - c ^ 2)) / (2 * b * c * (b + c) ^ 2) :=
    eq_div_of_mul_eq hden3 hB3
  have hT1' : T1 = ((1 - a ^ 2) * B3 - (1 - a ^ 2) * B2) / ((a - b) * (a + b)) :=
    eq_div_of_mul_eq hfab (by linear_combination hT1)
  have hT2' : T2 = ((1 - a ^ 2) * B3 - (1 - a ^ 2) * B1) / ((a - c) * (a + c)) :=
    eq_div_of_mul_eq hfac (by linear_combination hT2)
  have hdq : dqB3 = (-(1 - c ^ 2) - B3 *
      (2 * (-1 / (2 * b)) * c * (b + c) ^ 2 + 2 * b * c * (2 * (b + c) * (-1 / (2 * b))))) /
      (2 * b * c * (b + c) ^ 2) :=
    eq_div_of_mul_eq hden3 (by linear_combination hdqB3)
  have hdr : drB3 = (-(1 - b ^ 2) - B3 *
      (2 * b * (-1 / (2 * c)) * (b + c) ^ 2 + 2 * b * c * (2 * (b + c) * (-1 / (2 * c))))) /
      (2 * b * c * (b + c) ^ 2) :=
    eq_div_of_mul_eq hden3 (by linear_combination hdrB3)
  have hdqT1' : dqT1 = ((1 - a ^ 2) * dqB3 - T1) / ((a - b) * (a + b)) :=
    eq_div_of_mul_eq hfab (by linear_combination hdqT1)
  have hdrT2' : drT2 = ((1 - a ^ 2) * drB3 - T2) / ((a - c) * (a + c)) :=
    eq_div_of_mul_eq hfac (by linear_combination hdrT2)
  have hdqU' : dqU = ((1 - a ^ 2) * dqB3) / a ^ 2 :=
    eq_div_of_mul_eq ha2 (by linear_combination hdqU)
  have hdrU' : drU = ((1 - a ^ 2) * drB3) / a ^ 2 :=
    eq_div_of_mul_eq ha2 (by linear_combination hdrU)
  rw [hdqT1', hdrT2', hdqU', hdrU', hT1', hT2', hdq, hdr, hB3', hB1', hB2']
  field_simp
  ring

end Virasoro.Sphere
