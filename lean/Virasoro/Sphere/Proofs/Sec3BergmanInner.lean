import Virasoro.Sphere.Proofs.Sec3BergmanInnerAlg

/-!
# Sphere paper Lemma 3.5, Step 2, inner patch (`sphere/paper.tex` l.892–905)

On `0 < |x₁| < |x₂|`: `W = -∑_n v_n(x₂) z^{n-1} f_n(x₁/z)` and
`√(x₁(x₁-z)) W = -∑_n v_n(x₂) z^n P_n(x₁/z)`, here in the form
`[z^j](x₁√(1-z/x₁) W) = ∑_l x₁^{l+1}/(2(l+1)) [z^j](R_{l+1}(z/x₁) · (Dv)_{l+1})`
(`inner_formula`; `R_n(p) = -2p^nP_n(1/p)`, `(Dv)_{l+1} = (l+1) v_{l+1}`).  Only the powers
`x₁^{l+1-k}`, `0 ≤ k ≤ j`, occur, with coefficients `O(poly(l)|x₂|^{-l})`, so the series is
bounded on `|x₁| ≤ |x₂|/2`.

Consumer: `sub_bergman_const_of_patches`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- `(D v)_{l+1}` as a power series in `z`. -/
noncomputable def Bs (x2 : ℂ) (l : ℕ) : PowerSeries ℂ := PowerSeries.mk fun i => bt x2 i l

/-- The principal part of `[z^i] W(x,x₂)` at `x = 0`. -/
noncomputable def aA (x2 x : ℂ) (i : ℕ) : ℂ := ∑ m ∈ range i, aR x2 i m * x⁻¹ ^ (m + 2)

/-- `x^{l+1} [z^j](√(1-z/x) (Dv)_{l+1})`. -/
noncomputable def tin1 (j : ℕ) (x x2 : ℂ) (l : ℕ) : ℂ :=
  x ^ (l + 1) * coeff j (sqrtZ x * Bs x2 l)

/-- `x^{l+1}/(2(l+1)) [z^j](R_{l+1}(z/x) (Dv)_{l+1})`. -/
noncomputable def tin2 (j : ℕ) (x x2 : ℂ) (l : ℕ) : ℂ :=
  x ^ (l + 1) * (2 * ((l + 1 : ℕ) : ℂ))⁻¹ * coeff j (rescale x⁻¹ (RrevC (l + 1)) * Bs x2 l)

/-- `[z^i] W(x,x₂)` on `|x| < |x₂|` (l.892): principal part and the power series `∑ (Dv) x^m`. -/
theorem coeff_Wser_inner (i : ℕ) {x x2 : ℂ} (hx : ‖x‖ < ‖x2‖) (h2 : ‖x2‖ < 1) :
    coeff i (Wser x x2) = aA x2 x i + ∑' l : ℕ, bt x2 i l * x ^ l := by
  have h1 : ‖x‖ < 1 := lt_trans hx h2
  obtain ⟨hsnd, hW⟩ := Wnos_split i h1 h2
  obtain ⟨hsp, hP⟩ := pole_outer hx
  have hite : Summable fun l : ℕ =>
      (if i = 0 then x ^ l * (((l + 1 : ℕ) : ℂ) * x2⁻¹ ^ (l + 2)) else 0) := by
    by_cases hi : i = 0
    · simp only [if_pos hi]
      exact hsp
    · simp only [if_neg hi]
      exact summable_zero
  have e : ∀ l, bt x2 i l * x ^ l = bR x2 i l * x ^ l +
      (if i = 0 then x ^ l * (((l + 1 : ℕ) : ℂ) * x2⁻¹ ^ (l + 2)) else 0) := fun l => by
    rw [bt, add_mul]
    congr 1
    split_ifs <;> ring
  have hT : ∑' l : ℕ, (if i = 0 then x ^ l * (((l + 1 : ℕ) : ℂ) * x2⁻¹ ^ (l + 2)) else 0) =
      if i = 0 then ((x - x2) ^ 2)⁻¹ else 0 := by
    by_cases hi : i = 0
    · simp only [if_pos hi]
      rw [hP]
      congr 1
      ring
    · simp only [if_neg hi, tsum_zero]
  simp only [e]
  rw [Summable.tsum_add hsnd hite, Wser_eq, map_add, coeff_C, hW, aA, hT]
  ring

/-- The principal part through `a = -B^{(z)} v` (l.892–894). -/
theorem aA_eq (i : ℕ) (x : ℂ) {x2 : ℂ} (h2 : ‖x2‖ < 1) :
    aA x2 x i = -∑ l ∈ range i, ((l + 1 : ℕ) : ℂ)⁻¹ *
      coeff i (X ^ (l + 2) * (Psi x l * Bs x2 l)) := by
  have e : ∀ m, aR x2 i m * x⁻¹ ^ (m + 2) = -∑ l ∈ range i,
      (if m + l + 2 ≤ i then x⁻¹ ^ (m + 2) * bet m l * bt x2 (i - (m + l + 2)) l else 0) :=
    fun m => by
      rw [aR_inner h2, neg_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by split_ifs <;> ring
  rw [aA]
  simp only [e]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sum_guard i l (fun m p => x⁻¹ ^ (m + 2) * bet m l * bt x2 p l), coeff_X_pow_mul']
  by_cases h : l + 2 ≤ i
  · rw [if_pos h, if_pos h, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only
    rw [Psi, Bs, coeff_mk, coeff_mk, bet_eq]
    ring
  · rw [if_neg h, if_neg h, mul_zero]

theorem tin1_term (j : ℕ) (x x2 : ℂ) (l : ℕ) :
    ∑ p ∈ antidiagonal j, coeff p.1 (C x * sqrtZ x) * (bt x2 p.2 l * x ^ l) = tin1 j x x2 l := by
  have h1 : ∑ p ∈ antidiagonal j, coeff p.1 (C x * sqrtZ x) * (bt x2 p.2 l * x ^ l) =
      x ^ l * coeff j (C x * sqrtZ x * Bs x2 l) := by
    rw [coeff_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by
      rw [Bs, coeff_mk]
      ring
  rw [h1, mul_assoc, coeff_C_mul, tin1]
  ring

/-- The inner patch at order `z^j` (l.892–896). -/
theorem inner_formula (j : ℕ) {x x2 : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < ‖x2‖) (h2 : ‖x2‖ < 1) :
    coeff j (C x * sqrtZ x * Wser x x2) = ∑' l : ℕ, tin2 j x x2 l := by
  have hWc : ∀ i, coeff i (Wser x x2) = aA x2 x i + ∑' l : ℕ, bt x2 i l * x ^ l :=
    fun i => coeff_Wser_inner i hx h2
  have hsB : ∀ p ∈ antidiagonal j,
      Summable fun l : ℕ => coeff p.1 (C x * sqrtZ x) * (bt x2 p.2 l * x ^ l) :=
    fun p _ => ((summable_norm_bt h2 hx p.2).of_norm).mul_left _
  have hs1 : Summable (tin1 j x x2) := (summable_sum hsB).congr fun l => tin1_term j x x2 l
  have hB : ∑ p ∈ antidiagonal j, coeff p.1 (C x * sqrtZ x) * ∑' l : ℕ, bt x2 p.2 l * x ^ l =
      ∑' l : ℕ, tin1 j x x2 l := by
    simp only [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hsB]
    exact tsum_congr fun l => tin1_term j x x2 l
  have hA : ∑ p ∈ antidiagonal j, coeff p.1 (C x * sqrtZ x) * aA x2 x p.2 =
      -∑ l ∈ range j, (tin1 j x x2 l - tin2 j x x2 l) := by
    have hS : ∀ i ≤ j, coeff i (PowerSeries.mk (aA x2 x)) =
        coeff i (-∑ l ∈ range j, C (((l + 1 : ℕ) : ℂ)⁻¹) *
          (X ^ (l + 2) * (Psi x l * Bs x2 l))) := fun i hi => by
      rw [coeff_mk, aA_eq i x h2, map_neg, map_sum]
      congr 1
      rw [← Finset.sum_subset (Finset.range_mono hi) (fun l _ hl => by
        rw [coeff_C_mul, coeff_X_pow_mul',
          if_neg (by have := Finset.mem_range.not.1 hl; omega), mul_zero])]
      exact Finset.sum_congr rfl fun l _ => by rw [coeff_C_mul]
    have h1 : ∑ p ∈ antidiagonal j, coeff p.1 (C x * sqrtZ x) * aA x2 x p.2 =
        coeff j (C x * sqrtZ x * PowerSeries.mk (aA x2 x)) := by
      rw [coeff_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [coeff_mk]
    rw [h1, coeff_mul_congr hS, mul_neg, Finset.mul_sum, map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have hc : ((l + 1 : ℕ) : ℂ)⁻¹ * ((l + 1 : ℕ) : ℂ) = 1 :=
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero l))
    have e : C x * sqrtZ x * (C (((l + 1 : ℕ) : ℂ)⁻¹) * (X ^ (l + 2) * (Psi x l * Bs x2 l))) =
        C (((l + 1 : ℕ) : ℂ)⁻¹ * x ^ (l + 1)) *
          (C (((l + 1 : ℕ)) : ℂ) * (sqrtZ x * Bs x2 l) -
            C (1 / 2 : ℂ) * (rescale x⁻¹ (RrevC (l + 1)) * Bs x2 l)) := by
      have hK := inner_K hx0 l
      rw [map_mul]
      linear_combination (C (((l + 1 : ℕ) : ℂ)⁻¹) * Bs x2 l) * hK
    rw [e, coeff_C_mul, map_sub, coeff_C_mul, coeff_C_mul, tin1, tin2, mul_inv]
    linear_combination (x ^ (l + 1) * coeff j (sqrtZ x * Bs x2 l)) * hc
  have hv : ∀ l, j ≤ l → tin1 j x x2 l = tin2 j x x2 l := fun l hl => by
    have h0 := inner_vanish x (Bs x2 l) hl
    rw [sub_mul, map_sub, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul] at h0
    have hc : ((l + 1 : ℕ) : ℂ)⁻¹ * ((l + 1 : ℕ) : ℂ) = 1 :=
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero l))
    rw [tin1, tin2, mul_inv]
    linear_combination (x ^ (l + 1) * ((l + 1 : ℕ) : ℂ)⁻¹) * h0 -
      (x ^ (l + 1) * coeff j (sqrtZ x * Bs x2 l)) * hc
  have hs2 : Summable (tin2 j x x2) :=
    (summable_nat_add_iff j).1 (((summable_nat_add_iff j).2 hs1).congr fun l =>
      hv (l + j) (Nat.le_add_left j l))
  have ht : ∑' l : ℕ, tin1 j x x2 (l + j) = ∑' l : ℕ, tin2 j x x2 (l + j) :=
    tsum_congr fun l => hv (l + j) (Nat.le_add_left j l)
  rw [coeff_mul]
  simp only [hWc, mul_add]
  rw [Finset.sum_add_distrib, hA, hB, ← hs1.sum_add_tsum_nat_add j,
    ← hs2.sum_add_tsum_nat_add j, Finset.sum_sub_distrib, ht]
  ring

theorem norm_tin2_le (j : ℕ) {x x2 : ℂ} {r0 : ℝ} (hx0 : x ≠ 0) (hxr : ‖x‖ ≤ r0) (hr1 : r0 ≤ 1)
    (l : ℕ) :
    ‖tin2 j x x2 l‖ ≤
      2 * r0 * r0⁻¹ ^ j * ∑ p ∈ antidiagonal j, ‖bt x2 p.2 l * ((r0 : ℝ) : ℂ) ^ l‖ := by
  have hr0 : 0 < r0 := lt_of_lt_of_le (norm_pos_iff.2 hx0) hxr
  have hLpos : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.succ_pos l)
  have key : ∀ k : ℕ, k ≤ j →
      ‖x ^ (l + 1) * x⁻¹ ^ k * ((coeff k (Rrev (l + 1)) : ℚ) : ℂ)‖ ≤
        4 * ((l + 1 : ℕ) : ℝ) * (r0 ^ (l + 1) * r0⁻¹ ^ j) := fun k hkj => by
    by_cases hk : k ≤ l + 1
    · have e0 : x ^ (l + 1) * x⁻¹ ^ k = x ^ (l + 1 - k) := by
        have e1 : x ^ (l + 1) = x ^ (l + 1 - k) * x ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        have e2 : x ^ k * x⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx0, one_pow]
        rw [e1, mul_assoc, e2, mul_one]
      have hρ : ‖((coeff k (Rrev (l + 1)) : ℚ) : ℂ)‖ ≤ 4 * ((l + 1 : ℕ) : ℝ) := by
        refine (norm_ratCast_le (abs_coeff_Rrev_le (l + 1) k)).trans (le_of_eq ?_)
        push_cast
        ring
      have e1 : r0 ^ (l + 1) = r0 ^ (l + 1 - k) * r0 ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      have e2 : r0⁻¹ ^ j = r0⁻¹ ^ k * r0⁻¹ ^ (j - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hkj]
      have e3 : r0 ^ k * r0⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow]
      have e4 : 1 ≤ r0⁻¹ ^ (j - k) := one_le_pow₀ ((one_le_inv₀ hr0).2 hr1)
      have e5 : r0 ^ (l + 1 - k) ≤ r0 ^ (l + 1) * r0⁻¹ ^ j := by
        have e6 : r0 ^ (l + 1 - k) * r0 ^ k * (r0⁻¹ ^ k * r0⁻¹ ^ (j - k)) =
            r0 ^ (l + 1 - k) * r0⁻¹ ^ (j - k) * (r0 ^ k * r0⁻¹ ^ k) := by ring
        rw [e1, e2, e6, e3, mul_one]
        exact le_mul_of_one_le_right (pow_nonneg hr0.le _) e4
      rw [e0, norm_mul, norm_pow, mul_comm]
      exact mul_le_mul hρ ((pow_le_pow_left₀ (norm_nonneg x) hxr _).trans e5)
        (pow_nonneg (norm_nonneg x) _) (by positivity)
    · rw [coeff_Rrev_of_lt (by omega), Rat.cast_zero, mul_zero, norm_zero]
      have := pow_pos hr0 (l + 1)
      have := pow_pos (inv_pos.2 hr0) j
      positivity
  have hn2 : ‖(2 * ((l + 1 : ℕ) : ℂ))⁻¹‖ = (2 * ((l + 1 : ℕ) : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_ofNat]
  rw [tin2, coeff_mul, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpj : p.1 ≤ j := by
    have : p.1 + p.2 = j := by simpa using hp
    omega
  have hk := key p.1 hpj
  rw [coeff_rescale, RrevC, coeff_map, eq_ratCast, Bs, coeff_mk]
  have e : x ^ (l + 1) * (2 * ((l + 1 : ℕ) : ℂ))⁻¹ *
      (x⁻¹ ^ p.1 * ((coeff p.1 (Rrev (l + 1)) : ℚ) : ℂ) * bt x2 p.2 l) =
      (2 * ((l + 1 : ℕ) : ℂ))⁻¹ *
        (x ^ (l + 1) * x⁻¹ ^ p.1 * ((coeff p.1 (Rrev (l + 1)) : ℚ) : ℂ)) * bt x2 p.2 l := by
    ring
  rw [e, norm_mul, norm_mul, hn2, norm_mul (bt x2 p.2 l), norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hr0.le]
  calc (2 * ((l + 1 : ℕ) : ℝ))⁻¹ *
        ‖x ^ (l + 1) * x⁻¹ ^ p.1 * ((coeff p.1 (Rrev (l + 1)) : ℚ) : ℂ)‖ * ‖bt x2 p.2 l‖
      ≤ (2 * ((l + 1 : ℕ) : ℝ))⁻¹ * (4 * ((l + 1 : ℕ) : ℝ) * (r0 ^ (l + 1) * r0⁻¹ ^ j)) *
          ‖bt x2 p.2 l‖ := by gcongr
    _ = 2 * r0 * r0⁻¹ ^ j * (‖bt x2 p.2 l‖ * r0 ^ l) := by
        field_simp
        ring

/-- Lemma 3.5, Step 2, inner patch (sphere/paper.tex l.892–905). -/
theorem sub_bergman_inner : Stmt_sub_bergman_inner := by
  intro x2 h20 h21 j
  have hr0 : 0 < ‖x2‖ / 2 := by positivity
  have hr0x : ‖x2‖ / 2 < ‖x2‖ := half_lt_self h20
  have hy : ‖((‖x2‖ / 2 : ℝ) : ℂ)‖ < ‖x2‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact hr0x
  have hg : Summable fun l : ℕ => 2 * (‖x2‖ / 2) * (‖x2‖ / 2)⁻¹ ^ j *
      ∑ p ∈ antidiagonal j, ‖bt x2 p.2 l * ((‖x2‖ / 2 : ℝ) : ℂ) ^ l‖ :=
    (summable_sum fun p _ => summable_norm_bt h21 hy p.2).mul_left _
  refine ⟨‖x2‖ / 2, hr0, ∑' l : ℕ, 2 * (‖x2‖ / 2) * (‖x2‖ / 2)⁻¹ ^ j *
    ∑ p ∈ antidiagonal j, ‖bt x2 p.2 l * ((‖x2‖ / 2 : ℝ) : ℂ) ^ l‖, fun x hx0 hx => ?_⟩
  rw [sub_zero] at hx
  show ‖coeff j (C x * sqrtZ x * Wser x x2)‖ ≤ _
  rw [inner_formula j hx0 (lt_trans hx hr0x) h21]
  exact tsum_of_norm_bounded hg.hasSum fun l =>
    norm_tin2_le j hx0 hx.le (by linarith) l

end Virasoro.Sphere
