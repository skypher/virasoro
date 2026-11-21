import Virasoro.Sphere.Proofs.Sec3BergmanW
import Virasoro.Sphere.Proofs.Sec3SaddleDiag

/-!
# Sphere paper Lemma 3.5: finite-support facts (`sphere/paper.tex` l.840–844, l.878)

`(M₁)_{m,n} = O(z^{m+n})`, so for each `j` the coefficient `[z^j]` of
* `K₁₂ - I` vanishes in the rows `m ≥ j` (finite row support);
* `K₂₁ - I` vanishes in the columns `n ≥ j` (finite column support);
* `A₊₊` vanishes for `m + n > j`; `A₋₊` for `n ≥ j`; `A₊₋` for `m ≥ j`;
* `A₋₋ + B` vanishes for `j ≤ 1`.

Consumer: the convergence of `[z^j] W_no(x₁,x₂)` in `Stmt_sub_bergman_liouville`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

theorem dvd_imul {A B : IMat} {m n d : ℕ}
    (h : ∀ k, (X : PowerSeries ℚ) ^ d ∣ A m k * B k n) : (X : PowerSeries ℚ) ^ d ∣ imul A B m n := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [imul, coeff_mk]
  exact Finset.sum_eq_zero fun k _ => X_pow_dvd_iff.1 (h k) j hj

theorem dvd_ineumann_sub {A : IMat} {m n d : ℕ}
    (h : ∀ r, (X : PowerSeries ℚ) ^ d ∣ ipow A (r + 1) m n) :
    (X : PowerSeries ℚ) ^ d ∣ ineumann A m n - ione m n := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [map_sub, ineumann, coeff_mk, Finset.sum_range_succ', ipow,
    Finset.sum_eq_zero fun r _ => X_pow_dvd_iff.1 (h r) j hj, zero_add, sub_self]

theorem M1inf_zero_left (n : ℕ) : M1inf 0 n = 0 := by
  rw [M1inf, Bcoef_zero_left, zero_div, map_zero, zero_mul]

theorem M1inf_zero_right (m : ℕ) : M1inf m 0 = 0 := by
  rw [M1inf, Bcoef_zero_right, zero_div, map_zero, zero_mul]

theorem M2inf_zero_left (n : ℕ) : M2inf 0 n = 0 := by
  rw [M2inf, Bcoef_zero_left, zero_div, map_zero]

theorem Bzinf_zero_right (m : ℕ) : Bzinf m 0 = 0 := by
  rw [Bzinf, Bcoef_zero_right, map_zero, zero_mul]

theorem dvd_M1inf (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + n) ∣ M1inf m n :=
  Dvd.intro_left _ rfl

theorem dvd_Bzinf (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + n) ∣ Bzinf m n :=
  Dvd.intro_left _ rfl

/-- `(M₁M₂)_{m,n} = O(z^{m+1})`. -/
theorem dvd_M1M2 (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + 1) ∣ imul M1inf M2inf m n := by
  refine dvd_imul fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [M1inf_zero_right, zero_mul]
    exact dvd_zero _
  · exact ((pow_dvd_pow X (by omega)).trans (dvd_M1inf m k)).mul_right _

/-- `(M₂M₁)_{m,n} = O(z^{n+1})`. -/
theorem dvd_M2M1 (m n : ℕ) : (X : PowerSeries ℚ) ^ (n + 1) ∣ imul M2inf M1inf m n := by
  refine dvd_imul fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [M1inf_zero_left, mul_zero]
    exact dvd_zero _
  · exact ((pow_dvd_pow X (by omega)).trans (dvd_M1inf k n)).mul_left _

theorem dvd_ipow_M1M2 (r m n : ℕ) :
    (X : PowerSeries ℚ) ^ (m + 1) ∣ ipow (imul M1inf M2inf) (r + 1) m n := by
  induction r generalizing n with
  | zero =>
    refine dvd_imul fun k => ?_
    by_cases hk : m = k
    · subst hk
      exact (dvd_M1M2 m n).mul_left _
    · rw [ipow, ione, if_neg hk, zero_mul]
      exact dvd_zero _
  | succ r ih => exact dvd_imul fun k => (ih k).mul_right _

theorem dvd_ipow_M2M1 (r m n : ℕ) :
    (X : PowerSeries ℚ) ^ (n + 1) ∣ ipow (imul M2inf M1inf) (r + 1) m n :=
  dvd_imul fun k => (dvd_M2M1 k n).mul_left _

/-- `[z^j](K₁₂ - I)` has finite row support (sphere/paper.tex l.842). -/
theorem dvd_K12_sub (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + 1) ∣ K12 m n - ione m n :=
  dvd_ineumann_sub fun r => dvd_ipow_M1M2 r m n

/-- `[z^j](K₂₁ - I)` has finite column support (sphere/paper.tex l.843). -/
theorem dvd_K21_sub (m n : ℕ) : (X : PowerSeries ℚ) ^ (n + 1) ∣ K21 m n - ione m n :=
  dvd_ineumann_sub fun r => dvd_ipow_M2M1 r m n

/-- `(B^{(z)} K₂₁)_{m,n} = O(z^{m+n})`. -/
theorem dvd_BzK21 (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + n) ∣ imul Bzinf K21 m n := by
  refine dvd_imul fun k => ?_
  have e : Bzinf m k * K21 k n = Bzinf m k * ione k n + Bzinf m k * (K21 k n - ione k n) := by
    ring
  rw [e]
  refine dvd_add ?_ ?_
  · by_cases hk : k = n
    · subst hk
      exact (dvd_Bzinf m k).mul_right _
    · rw [ione, if_neg hk, mul_zero]
      exact dvd_zero _
  · exact (pow_dvd_pow X (by omega)).trans
      ((pow_add (X : PowerSeries ℚ) (m + k) (n + 1)).symm ▸
        mul_dvd_mul (dvd_Bzinf m k) (dvd_K21_sub k n))

/-- `[z^j] A₊₊` vanishes for `m + n > j`. -/
theorem dvd_App (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + n) ∣ App m n :=
  (dvd_BzK21 m n).neg_right

/-- `[z^j] A₋₊` vanishes for `n ≥ j`: finite column support. -/
theorem dvd_Amp (m n : ℕ) : (X : PowerSeries ℚ) ^ (n + 1) ∣ Amp m n := by
  refine dvd_imul fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [M1inf_zero_left, mul_zero]
    exact dvd_zero _
  · exact ((pow_dvd_pow X (by omega)).trans (dvd_M1inf k n)).mul_left _

/-- `[z^j] A₊₋` vanishes for `m ≥ j`: finite row support. -/
theorem dvd_Apm (m n : ℕ) : (X : PowerSeries ℚ) ^ (m + 1) ∣ Apm m n := by
  refine dvd_imul fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [M2inf_zero_left, mul_zero]
    exact dvd_zero _
  · exact ((pow_dvd_pow X (by omega)).trans (dvd_BzK21 m k)).mul_right _

/-- `[z^j](A₋₋ + B) = 0` for `j ≤ 1`. -/
theorem dvd_Amm_add (m n : ℕ) : (X : PowerSeries ℚ) ^ 2 ∣ Amm m n + Binf m n := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [Amm, map_add, map_neg, imul, coeff_mk]
  have h1 : ∀ k ∈ range (m + n + j + 1),
      coeff j (Binf m k * K12 k n) = if k = n then coeff j (Binf m n) else 0 := by
    intro k _
    have e : Binf m k * K12 k n = Binf m k * ione k n + Binf m k * (K12 k n - ione k n) := by
      ring
    have h2 : coeff j (Binf m k * (K12 k n - ione k n)) = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Binf, Bcoef_zero_right, map_zero, zero_mul, map_zero]
      · exact X_pow_dvd_iff.1
          (((pow_dvd_pow X (by omega)).trans (dvd_K12_sub k n)).mul_left _) j hj
    rw [e, map_add, h2, add_zero, ione]
    by_cases hk : k = n
    · rw [if_pos hk, if_pos hk, mul_one, hk]
    · rw [if_neg hk, if_neg hk, mul_zero, map_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (range (m + n + j + 1)) n,
    if_pos (Finset.mem_range.2 (by omega))]
  ring

end Virasoro.Sphere
