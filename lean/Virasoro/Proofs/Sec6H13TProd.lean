import Virasoro.Proofs.Sec6H13TGood

/-!
# Proposition 6.8(ii): products over ranges of length growing with `M` (paper.tex l.1366–1369)

`∏_{u < M + n₀} (1 + (A + Bu) x)` for a monomial `x = r t^e Y^f` with `e ≥ 1`, `e + f = 1`
(`x = t` or `x = t²/(2Y)`): its `[t^{ke} Y^{kf}]` coefficient is `r^k e_k(A + Bu : u < M + n₀)`, a
polynomial in `M` of degree at most `2k` (Faulhaber, through `e_{k+1}(n) = ∑_{u<n} a_u e_k(u)`).
"Expanding `k` factors … produces an elementary symmetric polynomial in `M` of degree at most `2k`
… while increasing `2i + 2j` by `2k`" (l.1366–1369).
-/

namespace Virasoro.H13T

open Virasoro.H13D Finset

/-- `e_k(a_0, …, a_{n−1})`. -/
noncomputable def esym (a : ℕ → ℚ) (k n : ℕ) : ℚ := ∑ S ∈ (range n).powersetCard k, ∏ u ∈ S, a u

theorem esym_zero (a : ℕ → ℚ) (n : ℕ) : esym a 0 n = 1 := by
  simp [esym]

theorem esym_succ_zero (a : ℕ → ℚ) (k : ℕ) : esym a (k + 1) 0 = 0 := by
  unfold esym
  rw [powersetCard_eq_empty.2 (by simp), sum_empty]

theorem esym_succ (a : ℕ → ℚ) (k n : ℕ) :
    esym a (k + 1) (n + 1) = esym a (k + 1) n + a n * esym a k n := by
  unfold esym
  rw [range_add_one, powersetCard_succ_insert (notMem_range_self), sum_union, mul_sum]
  · congr 1
    rw [sum_image]
    · refine sum_congr rfl fun S hS => ?_
      have hn : n ∉ S := fun h => by
        have := (mem_powersetCard.1 hS).1 h
        simp at this
      rw [prod_insert hn]
    · intro S hS T hT hST
      have hnS : n ∉ S := fun h => by
        have := (mem_powersetCard.1 hS).1 h
        simp at this
      have hnT : n ∉ T := fun h => by
        have := (mem_powersetCard.1 hT).1 h
        simp at this
      have := congrArg (fun U : Finset ℕ => U.erase n) hST
      simpa [erase_insert hnS, erase_insert hnT] using this
  · rw [disjoint_left]
    intro S hS hS'
    obtain ⟨T, _, rfl⟩ := mem_image.1 hS'
    have := (mem_powersetCard.1 hS).1 (mem_insert_self n T)
    simp at this

theorem esym_eq_sum (a : ℕ → ℚ) (k n : ℕ) :
    esym a (k + 1) n = ∑ u ∈ range n, a u * esym a k u := by
  induction n with
  | zero => rw [esym_succ_zero, range_zero, sum_empty]
  | succ n ih => rw [esym_succ, ih, sum_range_succ]

/-- `e_k(A + Bu : u < n)` is a polynomial in `n` of degree at most `2k`, for all `n ≥ 0`. -/
theorem polyDeg_esym (A B : ℚ) (k : ℕ) :
    PolyDeg (fun n => esym (fun u => A + B * (u : ℚ)) k n) (2 * k) := by
  induction k with
  | zero =>
    exact ((polyDeg_const 1).mono (by norm_num)).congr fun n => esym_zero _ n
  | succ k ih =>
    have hlin : PolyDeg (fun u : ℕ => A + B * (u : ℚ)) 1 :=
      ⟨Polynomial.C A + Polynomial.C B * Polynomial.X, fun m hm => by
        rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
        rw [if_neg (by omega), if_neg (by omega), mul_zero, add_zero], fun u => by simp⟩
    have h1 := (hlin.mul ih).sum_range
    refine (h1.mono (by push_cast; omega)).congr fun n => ?_
    exact esym_eq_sum _ k n

theorem prod_one_add_eq (a : ℕ → ℚ) (x : LL) (n : ℕ) :
    ∏ u ∈ range n, (1 + cL (a u) * x) = ∑ k ∈ range (n + 1), cL (esym a k n) * x ^ k := by
  classical
  rw [prod_one_add,
    ← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))
      (fun S hS => mem_range.2 (Nat.lt_succ_of_le ((card_le_card (mem_powerset.1 hS)).trans
        (card_range n).le)))]
  refine sum_congr rfl fun k _ => ?_
  rw [esym, map_sum, sum_mul]
  have e1 : (filter (fun S => S.card = k) (range n).powerset) = (range n).powersetCard k := by
    rw [powersetCard_eq_filter]
  rw [e1]
  refine sum_congr rfl fun S hS => ?_
  rw [prod_mul_distrib, prod_const, (mem_powersetCard.1 hS).2, map_prod]

/-- A monomial `r t^e Y^f`. -/
noncomputable def mono (e f : ℤ) (r : ℚ) : LL :=
  HahnSeries.single e (LaurentPolynomial.C r * LaurentPolynomial.T f)

theorem mono_pow (e f : ℤ) (r : ℚ) (k : ℕ) : mono e f r ^ k = mono (k * e) (k * f) (r ^ k) := by
  rw [mono, HahnSeries.single_pow, mono, mul_pow, ← map_pow, LaurentPolynomial.T_pow, nsmul_eq_mul]

theorem cfL_mono (e f : ℤ) (r : ℚ) (i j : ℤ) :
    cfL (mono e f r) i j = if i = e ∧ j = f then r else 0 := by
  rw [cfL, mono, HahnSeries.coeff_single]
  by_cases hi : i = e
  · rw [if_pos hi, lq_coeff_C_mul, ← mul_one (LaurentPolynomial.T f : LQ), lq_coeff_T_mul]
    rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    by_cases hj : j = f
    · rw [if_pos (by omega), if_pos ⟨hi, hj⟩, mul_one]
    · rw [if_neg (by omega), if_neg fun hh => hj hh.2, mul_zero]
  · rw [if_neg hi, if_neg fun hh => hi hh.1]
    rfl

theorem mono_coeff_low (e f : ℤ) (r : ℚ) (n : ℤ) (hn : n < e) : (mono e f r).coeff n = 0 := by
  rw [mono, HahnSeries.coeff_single, if_neg (by omega)]

/-- An `M`-independent monomial `r t^e Y^f`: `Good (2e+2f) (2e+2f)`. -/
theorem good_mono (e f : ℤ) (r : ℚ) : Good (fun _ => mono e f r) (2 * e + 2 * f) (2 * e + 2 * f) :=
  good_const _ (fun i j h => by
    rw [cfL_mono] at h
    split_ifs at h with hh
    · obtain ⟨rfl, rfl⟩ := hh
      exact ⟨le_rfl, le_rfl⟩
    · exact absurd rfl h) ⟨e, fun n hn => mono_coeff_low e f r n hn⟩

/-- `∏_{u < M + n₀}(1 + (A + Bu) r t^e Y^f)` with `e ≥ 1`, `e + f = 1`: `Good 0 0`. -/
theorem good_prod (A B : ℚ) (n₀ : ℕ) (e : ℕ) (he : 1 ≤ e) (f : ℤ) (hef : (e : ℤ) + f = 1)
    (r : ℚ) :
    Good (fun M => ∏ u ∈ range (M + n₀), (1 + cL (A + B * (u : ℚ)) * mono e f r)) 0 0 := by
  set a : ℕ → ℚ := fun u => A + B * (u : ℚ) with ha
  -- the coefficient formula
  have key : ∀ (M : ℕ) (i j : ℤ),
      cfL (∏ u ∈ range (M + n₀), (1 + cL (a u) * mono e f r)) i j =
        if 0 ≤ i ∧ (e : ℤ) ∣ i ∧ j = (i / e) * f then
          esym a (i / e).toNat (M + n₀) * r ^ (i / e).toNat else 0 := by
    intro M i j
    rw [prod_one_add_eq, cfL_sum]
    simp_rw [mono_pow, cfL_cL_mul, cfL_mono]
    split_ifs with h
    · obtain ⟨h0, ⟨c, hc⟩, hj⟩ := h
      have hc0 : 0 ≤ c := by
        rcases lt_or_ge c 0 with hlt | hge
        · nlinarith
        · exact hge
      have hdiv : i / e = c := by
        rw [hc]
        exact Int.mul_ediv_cancel_left c (by exact_mod_cast (by omega : e ≠ 0))
      rw [hdiv]
      by_cases hk : c.toNat < M + n₀ + 1
      · rw [sum_eq_single c.toNat]
        · rw [if_pos ⟨by rw [Int.toNat_of_nonneg hc0, hc]; ring,
            by rw [hj, hdiv, Int.toNat_of_nonneg hc0]⟩]
        · intro k _ hk2
          rw [if_neg, mul_zero]
          rintro ⟨h1, _⟩
          apply hk2
          have : (k : ℤ) = c := by
            have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
            have : (k : ℤ) * e = c * e := by rw [← h1, hc]; ring
            exact mul_right_cancel₀ he0 this
          omega
        · intro hk2
          exact absurd (mem_range.2 hk) hk2
      · have hz : esym a c.toNat (M + n₀) = 0 := by
          unfold esym
          rw [powersetCard_eq_empty.2 (by rw [card_range]; omega), sum_empty]
        rw [hz, zero_mul]
        refine sum_eq_zero fun k hk2 => ?_
        rw [if_neg, mul_zero]
        rintro ⟨h1, _⟩
        have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
        have : (k : ℤ) = c := mul_right_cancel₀ he0 (by rw [← h1, hc]; ring)
        have := mem_range.1 hk2
        omega
    · refine sum_eq_zero fun k _ => ?_
      rw [if_neg, mul_zero]
      rintro ⟨h1, h2⟩
      apply h
      refine ⟨by rw [h1]; positivity, ⟨k, by rw [h1]; ring⟩, ?_⟩
      have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
      rw [h2, h1, Int.mul_ediv_cancel _ he0]
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ⟨0, fun M n hn => ?_⟩⟩
  · refine PolyDeg.congr ?_ (key · i j)
    split_ifs with h
    · obtain ⟨h0, ⟨c, hc⟩, hj⟩ := h
      have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
      have hdiv : i / e = c := by rw [hc]; exact Int.mul_ediv_cancel_left c he0
      have hc0 : 0 ≤ c := by
        rcases lt_or_ge c 0 with hlt | hge
        · nlinarith
        · exact hge
      have h1 := (PolyDeg.comp_add (polyDeg_esym A B (i / e).toNat) n₀).mul
        (polyDeg_const (r ^ (i / e).toNat))
      refine (h1.mono ?_).congr fun M => by beta_reduce; rw [mul_comm]
      rw [hdiv, Int.toNat_of_nonneg hc0, hj, hdiv, hc]
      have : (2 : ℤ) * (e * c) + 2 * (c * f) = 2 * c * ((e : ℤ) + f) := by ring
      rw [this, hef]
      omega
    · exact polyDeg_zero _
  · rw [key]
    split_ifs with h
    · exfalso
      obtain ⟨h0, ⟨c, hc⟩, hj⟩ := h
      have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
      have hdiv : i / e = c := by rw [hc]; exact Int.mul_ediv_cancel_left c he0
      rw [hdiv] at hj
      have hc0 : 0 ≤ c := by
        rcases lt_or_ge c 0 with hlt | hge
        · nlinarith
        · exact hge
      have : 2 * i + 2 * j = 2 * c * ((e : ℤ) + f) := by rw [hc, hj]; ring
      rw [this, hef] at hij
      omega
    · rfl
  · have : ∀ k : ℕ, (mono e f r ^ k).coeff n = 0 := fun k => by
      rw [mono_pow]
      have : (0 : ℤ) ≤ (k : ℤ) * (e : ℤ) := by positivity
      exact mono_coeff_low _ _ _ n (by omega)
    rw [prod_one_add_eq, HahnSeries.coeff_sum]
    refine sum_eq_zero fun k _ => ?_
    rw [cL, RingHom.comp_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, this, smul_zero]

end Virasoro.H13T
