import Virasoro.Sphere.Proofs.Sec3SaddleDiag
import Virasoro.Sphere.Proofs.Sec3SaddlePde0
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Series in one of several variables (`sphere/paper.tex` l.737–747)

`one i f` is the one-variable series `f` in the variable `x_i`; `aS i = √(1 - x_i)` and
`uS i = (1 - x_i)^{-1/2}`.  The coefficient of a product with a one-variable series is a
convolution in that variable.

Consumers: `Sec3SaddlePde1.lean`, `Sec3SaddlePde2.lean` (part (i) of `Stmt_lem_saddle`).
-/

namespace Virasoro.Sphere

open Finset

section Tools

variable {σ : Type*} [DecidableEq σ]

noncomputable instance : IsDomain (MvPowerSeries σ ℚ) := NoZeroDivisors.to_isDomain _

theorem coeff_X_mul' (i : σ) (φ : MvPowerSeries σ ℚ) (x : σ →₀ ℕ) :
    MvPowerSeries.coeff x (MvPowerSeries.X i * φ) =
      if 1 ≤ x i then MvPowerSeries.coeff (x - Finsupp.single i 1) φ else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
  by_cases h : 1 ≤ x i
  · rw [if_pos h, if_pos (Finsupp.single_le_iff.2 h)]
  · rw [if_neg h, if_neg (mt Finsupp.single_le_iff.1 h)]

/-- `x_i ∂_{x_i}` multiplies the coefficient of `x^α` by `α_i`. -/
theorem coeff_X_mul_pderiv (i : σ) (f : MvPowerSeries σ ℚ) (x : σ →₀ ℕ) :
    MvPowerSeries.coeff x (MvPowerSeries.X i * MvPowerSeries.pderiv ℚ i f) =
      (x i : ℚ) * MvPowerSeries.coeff x f := by
  rw [coeff_X_mul']
  by_cases h : 1 ≤ x i
  · rw [if_pos h, MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h),
      Finsupp.tsub_apply, Finsupp.single_eq_same]
    have : (((x i - 1 : ℕ) : ℚ) + 1) = (x i : ℚ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℚ)) (Nat.sub_add_cancel h)
    rw [this, mul_comm]
  · rw [if_neg h]
    have : x i = 0 := by omega
    rw [this]
    simp

/-- The one-variable series `f` in the variable `x_i`. -/
noncomputable def one (i : σ) : PowerSeries ℚ →ₐ[ℚ] MvPowerSeries σ ℚ :=
  MvPowerSeries.rename (fun _ : Unit => i)

theorem coeff_one_single (i : σ) (f : PowerSeries ℚ) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i k) (one i f) = PowerSeries.coeff k f := by
  let e : Unit ↪ σ := ⟨fun _ => i, fun _ _ _ => rfl⟩
  have := MvPowerSeries.coeff_embDomain_rename e f (Finsupp.single () k)
  rw [Finsupp.embDomain_single] at this
  exact this

theorem coeff_one_ne (i : σ) (f : PowerSeries ℚ) (x : σ →₀ ℕ)
    (hx : x ≠ Finsupp.single i (x i)) : MvPowerSeries.coeff x (one i f) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨y, rfl⟩
  apply hx
  obtain ⟨n, rfl⟩ : ∃ n, y = Finsupp.single () n := ⟨y (), by ext u; simp⟩
  rw [Finsupp.mapDomain_single]
  simp

theorem coeff_one (i : σ) (f : PowerSeries ℚ) (x : σ →₀ ℕ) :
    MvPowerSeries.coeff x (one i f) =
      if x = Finsupp.single i (x i) then PowerSeries.coeff (x i) f else 0 := by
  by_cases hx : x = Finsupp.single i (x i)
  · rw [if_pos hx]
    conv_lhs => rw [hx]
    exact coeff_one_single i f (x i)
  · rw [if_neg hx, coeff_one_ne i f x hx]

theorem one_X (i : σ) : one i PowerSeries.X = (MvPowerSeries.X i : MvPowerSeries σ ℚ) :=
  MvPowerSeries.rename_X _ ()

theorem constantCoeff_one (i : σ) (f : PowerSeries ℚ) :
    MvPowerSeries.constantCoeff (one i f) = PowerSeries.constantCoeff f :=
  MvPowerSeries.constantCoeff_rename _ f

theorem pderiv_one_ne (i j : σ) (hji : j ≠ i) (f : PowerSeries ℚ) :
    MvPowerSeries.pderiv ℚ j (one i f) = 0 := by
  ext x
  rw [MvPowerSeries.coeff_pderiv, coeff_one_ne, zero_mul, map_zero]
  intro h
  have := DFunLike.congr_fun h j
  simp [Finsupp.single_apply, hji, Ne.symm hji] at this

/-- Uniqueness of the square root with constant term `1`. -/
theorem sqrt_unique {y y' : MvPowerSeries σ ℚ} (h : y ^ 2 = y' ^ 2)
    (hc : MvPowerSeries.constantCoeff y = 1) (hc' : MvPowerSeries.constantCoeff y' = 1) :
    y = y' := by
  have h0 : (y - y') * (y + y') = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have := congrArg MvPowerSeries.constantCoeff h1
    rw [map_add, hc, hc', map_zero] at this
    norm_num at this

theorem ne_zero_of_constantCoeff {y : MvPowerSeries σ ℚ}
    (hc : MvPowerSeries.constantCoeff y ≠ 0) : y ≠ 0 := by
  rintro rfl
  exact hc (map_zero _)

/-- A sum over the antidiagonal of `x` supported on a chain `φ 0, …, φ N`. -/
theorem sum_antidiagonal_eq_range (x : σ →₀ ℕ) (N : ℕ) (φ : ℕ → (σ →₀ ℕ))
    (hinj : Function.Injective φ) (hle : ∀ n ≤ N, φ n ≤ x)
    (F : (σ →₀ ℕ) → (σ →₀ ℕ) → ℚ)
    (h0 : ∀ a b, a + b = x → (∀ n ≤ N, a ≠ φ n) → F a b = 0) :
    ∑ ab ∈ antidiagonal x, F ab.1 ab.2 = ∑ n ∈ range (N + 1), F (φ n) (x - φ n) := by
  have himg : ∑ n ∈ range (N + 1), F (φ n) (x - φ n) =
      ∑ ab ∈ (range (N + 1)).image (fun n => (φ n, x - φ n)), F ab.1 ab.2 :=
    (sum_image (f := fun ab : (σ →₀ ℕ) × (σ →₀ ℕ) => F ab.1 ab.2)
      (g := fun n => (φ n, x - φ n)) (s := range (N + 1))
      (fun n _ n' _ h => hinj (congrArg Prod.fst h))).symm
  rw [himg]
  symm
  apply sum_subset
  · intro ab hab
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hab
    rw [HasAntidiagonal.mem_antidiagonal]
    exact add_tsub_cancel_of_le (hle n (by have := mem_range.1 hn; omega))
  · intro ab hab hnot
    have hsum := HasAntidiagonal.mem_antidiagonal.1 hab
    apply h0 _ _ hsum
    intro n hn h
    apply hnot
    rw [mem_image]
    refine ⟨n, mem_range.2 (by omega), ?_⟩
    refine Prod.ext h.symm ?_
    show x - φ n = ab.2
    rw [← h, ← hsum, add_tsub_cancel_left]

/-- The coefficient of `f(x_i) g`: a convolution in the variable `x_i`. -/
theorem coeff_one_mul (i : σ) (f : PowerSeries ℚ) (g : MvPowerSeries σ ℚ) (x : σ →₀ ℕ) :
    MvPowerSeries.coeff x (one i f * g) =
      ∑ n ∈ range (x i + 1),
        PowerSeries.coeff n f * MvPowerSeries.coeff (x - Finsupp.single i n) g := by
  rw [MvPowerSeries.coeff_mul]
  refine (sum_antidiagonal_eq_range x (x i) (fun n => Finsupp.single i n)
    (Finsupp.single_injective i) (fun n hn => Finsupp.single_le_iff.2 hn)
    (fun a b => MvPowerSeries.coeff a (one i f) * MvPowerSeries.coeff b g) ?_).trans
    (sum_congr rfl fun n _ => by rw [coeff_one_single])
  intro a b hab hne
  rw [coeff_one_ne, zero_mul]
  intro ha
  refine hne (a i) ?_ ha
  have := DFunLike.congr_fun hab i
  rw [Finsupp.add_apply] at this
  omega

/-! ### The square roots -/

/-- `(1-x)^{-1/2}` in one variable. -/
noncomputable def hser : PowerSeries ℚ := PowerSeries.mk halfBinom

theorem hser_sq : hser ^ 2 * (1 - PowerSeries.X) = 1 := by
  have h : hser ^ 2 = PowerSeries.mk 1 := by
    ext k
    rw [pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    simp only [hser, PowerSeries.coeff_mk]
    exact sum_halfBinom_mul k
  rw [h, PowerSeries.mk_one_mul_one_sub_eq_one]

theorem constantCoeff_sOne : PowerSeries.constantCoeff sOne = 1 := by
  rw [← diag_sqrtOneSub 0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_diag]
  simpa using constantCoeff_sqrtOneSub 0

/-- `√(1 - x_i)`. -/
noncomputable def aS (i : σ) : MvPowerSeries σ ℚ := one i sOne

/-- `(1 - x_i)^{-1/2}`. -/
noncomputable def uS (i : σ) : MvPowerSeries σ ℚ := one i hser

theorem aS_sq (i : σ) : aS i ^ 2 = 1 - MvPowerSeries.X i := by
  rw [aS, ← map_pow, sOne_sq, map_sub, map_one, one_X]

theorem constantCoeff_aS (i : σ) : MvPowerSeries.constantCoeff (aS i) = 1 := by
  rw [aS, constantCoeff_one, constantCoeff_sOne]

theorem constantCoeff_uS (i : σ) : MvPowerSeries.constantCoeff (uS i) = 1 := by
  rw [uS, constantCoeff_one, hser, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_mk]
  simp [halfBinom, gbinom]

theorem uS_mul_aS (i : σ) : uS i * aS i = 1 := by
  apply sqrt_unique
  · rw [mul_pow, aS_sq, one_pow, uS, ← map_pow, ← one_X, ← map_one (one i), ← map_sub, ← map_mul,
      hser_sq]
  · rw [map_mul, constantCoeff_aS, constantCoeff_uS, mul_one]
  · exact map_one _

theorem aS_ne_zero (i : σ) : aS i ≠ 0 :=
  ne_zero_of_constantCoeff (by rw [constantCoeff_aS]; exact one_ne_zero)

theorem coeff_uS_single (i : σ) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i k) (uS i) = halfBinom k := by
  rw [uS, coeff_one_single, hser, PowerSeries.coeff_mk]

end Tools

theorem sqrtOneSub_eq_aS (i : Fin 2) : sqrtOneSub i = aS i :=
  sqrt_unique ((sqrtOneSub_sq i).trans (aS_sq i).symm) (constantCoeff_sqrtOneSub i)
    (constantCoeff_aS i)

end Virasoro.Sphere
