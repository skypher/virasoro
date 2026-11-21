import Virasoro.Sphere.Proofs.Sec2HSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The exponent law for the binomial power `fpow`

`fpow f a = ∑_k binom(a,k) (f-1)^k` and `∑_m ℬ_m z(q)^m` are both series `∑_k b_k u^k` in a
series `u` without constant term.  Multiplying by `u^ℓ` shifts the coefficient sequence, and
Pascal's rule `binom(a+1,k+1) = binom(a,k+1) + binom(a,k)` gives
`fpow f (a+ℓ) = fpow f a * f^ℓ`.  With `(16q/z(q)) · z(q) = 16q` this is the identity
`Φ̃(λ+ℓ;q) z(q)^ℓ = (16q)^ℓ Φ̃(λ;q)` used in sphere/paper.tex l.1596–1597.
-/

namespace Virasoro.Sphere

open PowerSeries

section Comp

variable {A : Type*} [Field A]

/-- The series `∑_k b_k u^k` for a series `u` without constant term; the coefficient of `q^n`
only involves `k ≤ n`. -/
noncomputable def compS (b : ℕ → A) (u : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), b k * PowerSeries.coeff n (u ^ k)

theorem fpow_eq_compS (f : PowerSeries A) (a : A) : fpow f a = compS (gbinom a) (f - 1) := rfl

theorem coeff_pow_of_lt {u : PowerSeries A} (hu : constantCoeff u = 0) {i k : ℕ} (h : i < k) :
    coeff i (u ^ k) = 0 := by
  obtain ⟨v, rfl⟩ := X_dvd_iff.2 hu
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_compS_le {u : PowerSeries A} (hu : constantCoeff u = 0) (b : ℕ → A) {n M : ℕ}
    (h : n ≤ M) :
    coeff n (compS b u) = ∑ k ∈ Finset.range (M + 1), b k * coeff n (u ^ k) := by
  simp only [compS, coeff_mk]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
  rw [coeff_pow_of_lt hu (by simpa using hk), mul_zero]

theorem coeff_compS_congr {b b' : ℕ → A} (u : PowerSeries A) {n : ℕ}
    (h : ∀ m ≤ n, b m = b' m) : coeff n (compS b u) = coeff n (compS b' u) := by
  simp only [compS, coeff_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h k (by have := Finset.mem_range.1 hk; omega)]

theorem coeff_mul_compS_congr {b b' : ℕ → A} (F u : PowerSeries A) {n : ℕ}
    (h : ∀ m ≤ n, b m = b' m) : coeff n (F * compS b u) = coeff n (F * compS b' u) := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_compS_congr u fun m hm =>
    h m (le_trans hm (Finset.HasAntidiagonal.antidiagonal.snd_le hp))]

theorem compS_add (b b' : ℕ → A) (u : PowerSeries A) :
    compS (fun k => b k + b' k) u = compS b u + compS b' u := by
  ext n
  simp [compS, add_mul, Finset.sum_add_distrib]

theorem compS_smul (t : A) (b : ℕ → A) (u : PowerSeries A) :
    compS (fun k => t * b k) u = C t * compS b u := by
  ext n
  simp [compS, Finset.mul_sum, mul_assoc]

/-- The coefficient sequence shifted by `ℓ`. -/
def shiftSeq (ℓ : ℕ) (b : ℕ → A) : ℕ → A := fun k => if ℓ ≤ k then b (k - ℓ) else 0

/-- `(∑_k b_k u^k) u^ℓ = ∑_k b_{k-ℓ} u^k`. -/
theorem compS_mul_pow {u : PowerSeries A} (hu : constantCoeff u = 0) (b : ℕ → A) (ℓ : ℕ) :
    compS b u * u ^ ℓ = compS (shiftSeq ℓ b) u := by
  ext n
  have hL : coeff n (compS b u * u ^ ℓ) =
      ∑ k ∈ Finset.range (n + 1), b k * coeff n (u ^ k * u ^ ℓ) := by
    have e : ∀ k, coeff n (u ^ k * u ^ ℓ) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 (u ^ k) * coeff p.2 (u ^ ℓ) :=
      fun k => coeff_mul n _ _
    simp only [e, Finset.mul_sum]
    rw [Finset.sum_comm, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [coeff_compS_le hu b (Finset.HasAntidiagonal.antidiagonal.fst_le hp), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : coeff n (compS (shiftSeq ℓ b) u) =
      ∑ k ∈ Finset.range (ℓ + (n + 1)), shiftSeq ℓ b k * coeff n (u ^ k) := by
    simp only [compS, coeff_mk]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
    rw [coeff_pow_of_lt hu (by simpa using hk), mul_zero]
  rw [hL, hR, Finset.sum_range_add (fun k => shiftSeq ℓ b k * coeff n (u ^ k))]
  have h0 : ∑ k ∈ Finset.range ℓ, shiftSeq ℓ b k * coeff n (u ^ k) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [shiftSeq, if_neg (by have := Finset.mem_range.1 hk; omega), zero_mul]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shiftSeq, if_pos (Nat.le_add_right ℓ k), Nat.add_sub_cancel_left, ← pow_add, add_comm]

end Comp

section Law

variable {A : Type*} [Field A] [CharZero A]

/-- Pascal's rule for the generalized binomial coefficients. -/
theorem gbinom_succ (a : A) (k : ℕ) :
    gbinom (a + 1) (k + 1) = gbinom a (k + 1) + gbinom a k := by
  unfold gbinom
  have h1 : ∏ i ∈ Finset.range (k + 1), (a + 1 - (i : A)) =
      (∏ i ∈ Finset.range k, (a - (i : A))) * (a + 1) := by
    rw [Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      push_cast
      ring
    · simp
  have h2 : ∏ i ∈ Finset.range (k + 1), (a - (i : A)) =
      (∏ i ∈ Finset.range k, (a - (i : A))) * (a - (k : A)) := Finset.prod_range_succ _ _
  have hk : ((k.factorial : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hk1 : ((k : A) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [h1, h2, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem gbinom_zero (a : A) : gbinom a 0 = 1 := by simp [gbinom]

theorem gbinom_add_one (a : A) :
    gbinom (a + 1) = fun k => gbinom a k + shiftSeq 1 (gbinom a) k := by
  funext k
  cases k with
  | zero => simp [gbinom_zero, shiftSeq]
  | succ k =>
    rw [gbinom_succ, shiftSeq, if_pos (by omega), Nat.add_sub_cancel]

theorem fpow_add_one {f : PowerSeries A} (hf : constantCoeff f = 1) (a : A) :
    fpow f (a + 1) = fpow f a * f := by
  have hu : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have e : fpow f a * f = fpow f a + fpow f a * (f - 1) ^ 1 := by ring
  rw [e, fpow_eq_compS, fpow_eq_compS, compS_mul_pow hu, ← compS_add, gbinom_add_one]

/-- The exponent law `f^{a+ℓ} = f^a f^ℓ` for the binomial power of a series with constant
term `1`. -/
theorem fpow_add_nat {f : PowerSeries A} (hf : constantCoeff f = 1) (a : A) (ℓ : ℕ) :
    fpow f (a + (ℓ : A)) = fpow f a * f ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [Nat.cast_succ, ← add_assoc, fpow_add_one hf, ih, pow_succ, mul_assoc]

theorem constantCoeff_nomeRatio : constantCoeff (nomeRatio A) = 1 := by
  unfold nomeRatio
  rw [map_mul, map_pow, constantCoeff_th3, PowerSeries.constantCoeff_inv, map_pow,
    constantCoeff_thPsi]
  norm_num

/-- `(16q/z(q)) · z(q) = 16q`. -/
theorem nomeRatio_mul_zq : nomeRatio A * zq A = 16 * X := by
  have h3 : constantCoeff (th3 A ^ 4) ≠ 0 := by
    rw [map_pow, constantCoeff_th3]
    norm_num
  have hp : constantCoeff (thPsi A ^ 4) ≠ 0 := by
    rw [map_pow, constantCoeff_thPsi]
    norm_num
  unfold nomeRatio zq
  calc th3 A ^ 4 * (thPsi A ^ 4)⁻¹ * (16 * X * thPsi A ^ 4 * (th3 A ^ 4)⁻¹)
      = 16 * X * (th3 A ^ 4 * (th3 A ^ 4)⁻¹) * (thPsi A ^ 4 * (thPsi A ^ 4)⁻¹) := by ring
    _ = 16 * X := by
      rw [PowerSeries.mul_inv_cancel _ h3, PowerSeries.mul_inv_cancel _ hp, mul_one, mul_one]

theorem constantCoeff_zq : constantCoeff (zq A) = 0 := by
  unfold zq
  simp

end Law

end Virasoro.Sphere
