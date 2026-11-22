import Virasoro.Proofs.Sec6FockVir
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The Virasoro relations on the Fock module `𝓕(α)` (paper.tex l.1261–1264)

"`L_n = ½∑_k :a_k a_{n-k}: − q₀(n+1)a_n` gives a Virasoro action of charge `c(b)` and weight
`Δ`": the relations hold with `c = 1 − 12 q₀²`, and `|α⟩ = 1` is a highest-weight vector of
weight `Δ = ½ α (α − 2 q₀)`.

The operator `T = [L_m, L_n] − (m−n) L_{m+n} − (c/12)(m³−m) δ_{m+n,0}` commutes with every
`a_j` (from `[L_n, a_m]`), so `T·1` is annihilated by all `∂/∂x_j` and is a constant; its
constant term is computed from `L_m L_{-m} |α⟩`.
-/

namespace Virasoro.TFock

open MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The weight `Δ = ½ α (α − 2 q₀)` of `|α⟩`. -/
noncomputable def wt (al q : R) : R := half R * al ^ 2 - q * al

theorem LOp_one_pos (al q : R) {n : ℤ} (hn : 0 < n) :
    LOp al q n (1 : MvPolynomial ℕ+ R) = 0 := by
  rw [LOp_apply, Derivation.map_one_eq_zero, zero_add]
  have hz : zOp al q n (1 : MvPolynomial ℕ+ R) = 0 := by
    unfold zOp
    rw [if_neg (by omega)]
    simp only [LinearMap.smul_apply, hOp_one_pos al hn, smul_zero]
  have hq : qOp al n (1 : MvPolynomial ℕ+ R) = 0 := by
    rw [qOp_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ioo] at hk
    rw [hOp_one_pos al (by omega), map_zero]
  rw [hz, hq, smul_zero, add_zero]

theorem LOp_one_zero (al q : R) : LOp al q 0 (1 : MvPolynomial ℕ+ R) = wt al q • 1 := by
  rw [LOp_apply, Derivation.map_one_eq_zero, zero_add]
  have hq : qOp al 0 (1 : MvPolynomial ℕ+ R) = 0 := by
    rw [qOp_apply]
    simp
  rw [hq, smul_zero, add_zero]
  unfold zOp wt
  rw [if_pos rfl]
  rfl

theorem LOp_one_neg (al q : R) {n : ℤ} (hn : n < 0) :
    LOp al q n (1 : MvPolynomial ℕ+ R) =
      (al - q * ((n : R) + 1)) • (X (pn (-n)) * 1) +
        half R • ∑ k ∈ Finset.Ioo n 0, X (pn (-k)) * (X (pn (k - n)) * 1) := by
  rw [LOp_apply, Derivation.map_one_eq_zero, zero_add]
  congr 1
  · unfold zOp
    rw [if_neg (by omega)]
    simp only [LinearMap.smul_apply, hOp_neg al hn]
  · rw [qOp_apply, min_eq_left hn.le, max_eq_right hn.le]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ioo] at hk
    rw [hOp_neg al hk.2, hOp_neg al (by omega : n - k < 0), neg_sub]

/-! ### The constant term -/

omit [Algebra ℚ R] in
theorem cc_smul (a : R) (f : MvPolynomial ℕ+ R) :
    constantCoeff (a • f) = a * constantCoeff f := by
  rw [smul_eq_C_mul, map_mul, constantCoeff_C]

omit [Algebra ℚ R] in
theorem cc_dOp (n : ℤ) (f : MvPolynomial ℕ+ R) : constantCoeff (dOp n f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [← algebraMap_eq, Derivation.map_algebraMap, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    have h1 : constantCoeff (dOp n (X i : MvPolynomial ℕ+ R)) = 0 := by
      rw [dOp, mkDerivation_X]
      split_ifs <;> simp [smul_eq_C_mul]
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hp, h1, mul_zero,
      mul_zero, add_zero]

omit [Algebra ℚ R] in
theorem cc_hOp_neg (al : R) {k : ℤ} (hk : k < 0) (f : MvPolynomial ℕ+ R) :
    constantCoeff (hOp al k f) = 0 := by
  rw [hOp_neg al hk, map_mul, constantCoeff_X, zero_mul]

omit [Algebra ℚ R] in
theorem cc_hOp_one (al : R) (j : ℤ) :
    constantCoeff (hOp al j (1 : MvPolynomial ℕ+ R)) = if j = 0 then al else 0 := by
  rcases lt_trichotomy j 0 with h | h | h
  · rw [cc_hOp_neg al h, if_neg (by omega)]
  · subst h
    rw [hOp_zero, cc_smul, map_one, mul_one, if_pos rfl]
  · rw [hOp_one_pos al h, map_zero, if_neg (by omega)]

theorem cc_LOp_neg (al q : R) {n : ℤ} (hn : n < 0) (f : MvPolynomial ℕ+ R) :
    constantCoeff (LOp al q n f) = 0 := by
  rw [LOp_apply, map_add, map_add, cc_dOp, cc_smul, zero_add]
  have hz : constantCoeff (zOp al q n f) = 0 := by
    unfold zOp
    rw [if_neg (by omega)]
    simp only [LinearMap.smul_apply, cc_smul, cc_hOp_neg al hn, mul_zero]
  have hq : constantCoeff (qOp al n f) = 0 := by
    rw [qOp_apply, map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ioo] at hk
    exact cc_hOp_neg al (by omega) _
  rw [hz, hq, mul_zero, add_zero]

theorem cc_LOp_zero (al q : R) (f : MvPolynomial ℕ+ R) :
    constantCoeff (LOp al q 0 f) = wt al q * constantCoeff f := by
  rw [LOp_apply, map_add, map_add, cc_dOp, cc_smul, zero_add]
  have hq : qOp al 0 f = 0 := by
    rw [qOp_apply]
    simp
  rw [hq, map_zero, mul_zero, add_zero]
  unfold zOp wt
  rw [if_pos rfl]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, cc_smul]

theorem cc_LOp_one (al q : R) (m : ℤ) :
    constantCoeff (LOp al q m (1 : MvPolynomial ℕ+ R)) = if m = 0 then wt al q else 0 := by
  rcases lt_trichotomy m 0 with h | h | h
  · rw [cc_LOp_neg al q h, if_neg (by omega)]
  · subst h
    rw [cc_LOp_zero, map_one, mul_one, if_pos rfl]
  · rw [LOp_one_pos al q h, map_zero, if_neg (by omega)]

theorem cc_LOp_X (al q : R) (m : ℤ) (i : ℕ+) (g : MvPolynomial ℕ+ R) :
    constantCoeff (LOp al q m (X i * g)) =
      ((i : ℕ) : R) * constantCoeff (hOp al (m - ((i : ℕ) : ℤ)) g) -
        (if m = ((i : ℕ) : ℤ) then q * (m : R) * ((m : R) + 1) * constantCoeff g else 0) := by
  rw [LOp_X, map_sub, map_add, map_mul, constantCoeff_X, zero_mul, zero_add, cc_smul]
  congr 1
  split_ifs
  · rw [cc_smul]
  · rw [map_zero]

theorem cc_LX1 (al q : R) (m : ℤ) (i : ℕ+) :
    constantCoeff (LOp al q m (X i * (1 : MvPolynomial ℕ+ R))) =
      if m = ((i : ℕ) : ℤ) then ((i : ℕ) : R) * al - q * (m : R) * ((m : R) + 1) else 0 := by
  rw [cc_LOp_X, cc_hOp_one, map_one, mul_one]
  have : (m - ((i : ℕ) : ℤ) = 0) ↔ (m = ((i : ℕ) : ℤ)) := by omega
  rw [if_congr this rfl rfl]
  split_ifs
  · rfl
  · ring

theorem cc_LX2 (al q : R) (m : ℤ) (i j : ℕ+) :
    constantCoeff (LOp al q m (X i * (X j * (1 : MvPolynomial ℕ+ R)))) =
      if m = ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) then ((i : ℕ) : R) * ((j : ℕ) : R) else 0 := by
  rw [cc_LOp_X, hOp_X, map_add, map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul, mul_zero,
    zero_add]
  have : (m - ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ)) ↔ (m = ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by omega
  rw [if_congr this rfl rfl]
  split_ifs <;> simp [cc_smul]

/-- `∑_{k=1}^{m-1} k(m−k) = (m³−m)/6`, over integers. -/
theorem sum_Ioo_int (M : ℕ) (hM : 1 ≤ M) (a : ℤ) :
    6 * ∑ k ∈ Finset.Ioo (-(M : ℤ)) 0, -k * (k + a) =
      3 * a * M * (M - 1) - (M - 1) * M * (2 * M - 1) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : Finset.Ioo (-((1 : ℕ) : ℤ)) 0 = ∅ := by
      ext k
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [this]
    simp
  | succ M hM ih =>
    have e : Finset.Ioo (-((M + 1 : ℕ) : ℤ)) 0 = insert (-(M : ℤ)) (Finset.Ioo (-(M : ℤ)) 0) := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    rw [e, Finset.sum_insert (by simp), mul_add, ih]
    push_cast
    ring

theorem sum_Ioo_R {m : ℤ} (hm : 0 < m) :
    ∑ k ∈ Finset.Ioo (-m) 0, -(k : R) * ((k : R) + (m : R)) =
      algebraMap ℚ R (((m ^ 3 - m : ℤ) : ℚ) / 6) := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = M := ⟨m.toNat, by omega⟩
  have hz := sum_Ioo_int M (by omega) (M : ℤ)
  have h1 : ∑ k ∈ Finset.Ioo (-(M : ℤ)) 0, -(k : R) * ((k : R) + ((M : ℤ) : R)) =
      algebraMap ℚ R ((∑ k ∈ Finset.Ioo (-(M : ℤ)) 0, -k * (k + (M : ℤ)) : ℤ) : ℚ) := by
    rw [map_intCast]
    push_cast
    rfl
  rw [h1]
  congr 1
  rw [eq_div_iff (by norm_num)]
  have h2 := congrArg (Int.cast : ℤ → ℚ) hz
  push_cast at h2 ⊢
  linarith

theorem centralTerm_neg (c : R) (m : ℤ) : centralTerm c (-m) = -centralTerm c m := by
  unfold centralTerm
  have : (((-m) ^ 3 - -m : ℤ) : ℚ) = -((m ^ 3 - m : ℤ) : ℚ) := by push_cast; ring
  rw [this, neg_div, map_neg, neg_mul]

/-- `⟨α| L_m L_n |α⟩` for `m > 0 > n`. -/
theorem cc_LL_main (al q : R) {m n : ℤ} (hm : 0 < m) (hn : n < 0) :
    constantCoeff (LOp al q m (LOp al q n (1 : MvPolynomial ℕ+ R))) =
      if m + n = 0 then 2 * (m : R) * wt al q + centralTerm (1 - 12 * q ^ 2) m else 0 := by
  have h2 := two_mul_half (R := R)
  rw [LOp_one_neg al q hn, map_add, map_smul, map_smul, map_sum, map_add, cc_smul, cc_smul,
    map_sum, cc_LX1]
  have hs : ∀ k ∈ Finset.Ioo n 0,
      constantCoeff (LOp al q m (X (pn (-k)) * (X (pn (k - n)) * (1 : MvPolynomial ℕ+ R)))) =
        if m + n = 0 then -(k : R) * ((k : R) - (n : R)) else 0 := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have e1 : (((pn (-k) : ℕ+) : ℕ) : ℤ) = -k := coe_pn (by omega)
    have e2 : (((pn (k - n) : ℕ+) : ℕ) : ℤ) = k - n := coe_pn (by omega)
    have c1 : (((pn (-k) : ℕ+) : ℕ) : R) = -(k : R) := by
      have := congrArg (Int.cast : ℤ → R) e1
      push_cast at this
      exact this
    have c2 : (((pn (k - n) : ℕ+) : ℕ) : R) = (k : R) - (n : R) := by
      have := congrArg (Int.cast : ℤ → R) e2
      push_cast at this
      exact this
    rw [cc_LX2, e1, e2, c1, c2]
    have : (m = -k + (k - n)) ↔ (m + n = 0) := by omega
    rw [if_congr this rfl rfl]
  rw [Finset.sum_congr rfl hs]
  have e0 : (((pn (-n) : ℕ+) : ℕ) : ℤ) = -n := coe_pn (by omega)
  have c0 : (((pn (-n) : ℕ+) : ℕ) : R) = -(n : R) := by
    have := congrArg (Int.cast : ℤ → R) e0
    push_cast at this
    exact this
  rw [e0, c0]
  have : (m = -n) ↔ (m + n = 0) := by omega
  rw [if_congr this rfl rfl]
  by_cases h : m + n = 0
  · have hnm : n = -m := by omega
    subst hnm
    simp only [if_pos h]
    have hsum := sum_Ioo_R (R := R) hm
    have hsum' : ∑ k ∈ Finset.Ioo (-m) 0, -(k : R) * ((k : R) - ((-m : ℤ) : R)) =
        algebraMap ℚ R (((m ^ 3 - m : ℤ) : ℚ) / 6) := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [hsum']
    have he : half R * algebraMap ℚ R (((m ^ 3 - m : ℤ) : ℚ) / 6) =
        algebraMap ℚ R (((m ^ 3 - m : ℤ) : ℚ) / 12) := by
      unfold half
      rw [← map_mul]
      congr 1
      ring
    have hA : algebraMap ℚ R (((m ^ 3 - m : ℤ) : ℚ) / 12) * 12 = (m : R) ^ 3 - (m : R) := by
      rw [← map_ofNat (algebraMap ℚ R) 12, ← map_mul, div_mul_cancel₀ _ (by norm_num), map_intCast]
      push_cast
      rfl
    rw [he]
    unfold centralTerm wt
    generalize algebraMap ℚ R (((m ^ 3 - m : ℤ) : ℚ) / 12) = A at hA ⊢
    push_cast
    linear_combination (-(m : R) * al ^ 2) * h2 + q ^ 2 * hA
  · simp only [if_neg h, Finset.sum_const_zero, mul_zero, add_zero]

/-! ### The Virasoro relations -/

/-- `[L_m, L_n] − (m−n) L_{m+n} − (c/12)(m³−m) δ_{m+n,0}`, `c = 1 − 12 q₀²`. -/
noncomputable def Tvir (al q : R) (m n : ℤ) : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R :=
  LOp al q m ∘ₗ LOp al q n - LOp al q n ∘ₗ LOp al q m - ((m - n : ℤ) : R) • LOp al q (m + n)
    - (if m + n = 0 then centralTerm (1 - 12 * q ^ 2) m • LinearMap.id else 0)

theorem Tvir_apply (al q : R) (m n : ℤ) (f : MvPolynomial ℕ+ R) :
    Tvir al q m n f = LOp al q m (LOp al q n f) - LOp al q n (LOp al q m f)
      - ((m - n : ℤ) : R) • LOp al q (m + n) f
      - (if m + n = 0 then centralTerm (1 - 12 * q ^ 2) m • f else 0) := by
  unfold Tvir
  split_ifs <;> simp

theorem Tvir_h (al q : R) (m n j : ℤ) (f : MvPolynomial ℕ+ R) :
    Tvir al q m n (hOp al j f) = hOp al j (Tvir al q m n f) := by
  have i1 : m + (n + j) = m + n + j := by ring
  have i2 : n + (m + j) = m + n + j := by ring
  simp only [Tvir_apply, LOp_h, map_sub, map_smul, lin_ite, i1, i2]
  by_cases hP : m + n + j = 0
  · have hc : (j : R) = -(m : R) - (n : R) := by
      have := congrArg (Int.cast : ℤ → R) hP
      push_cast at this
      linear_combination this
    simp only [if_pos hP]
    split_ifs <;> push_cast <;> simp only [hc] <;> module
  · simp only [if_neg hP]
    split_ifs <;> push_cast <;> module

theorem int_smul_cancel {k : ℤ} (hk : k ≠ 0) {v : MvPolynomial ℕ+ R} (h : (k : R) • v = 0) :
    v = 0 := by
  have h1 : algebraMap ℚ R (1 / (k : ℚ)) * (k : R) = 1 := by
    rw [← map_intCast (algebraMap ℚ R) k, ← map_mul,
      one_div_mul_cancel (by exact_mod_cast hk), map_one]
  calc v = (algebraMap ℚ R (1 / (k : ℚ)) * (k : R)) • v := by rw [h1, one_smul]
    _ = 0 := by rw [mul_smul, h, smul_zero]

theorem nat_mul_cancel {k : ℕ} (hk : k ≠ 0) {x : R} (h : x * (k : R) = 0) : x = 0 := by
  have h1 : (k : R) * algebraMap ℚ R (1 / (k : ℚ)) = 1 := by
    rw [← map_natCast (algebraMap ℚ R) k, ← map_mul,
      mul_one_div_cancel (by exact_mod_cast hk), map_one]
  calc x = x * ((k : R) * algebraMap ℚ R (1 / (k : ℚ))) := by rw [h1, mul_one]
    _ = 0 := by rw [← mul_assoc, h, zero_mul]

/-- A polynomial all of whose partial derivatives vanish is constant. -/
theorem eq_C_of_pderiv (f : MvPolynomial ℕ+ R) (h : ∀ i, pderiv i f = 0) :
    f = C (constantCoeff f) := by
  ext e
  rw [coeff_C]
  by_cases he : e = 0
  · subst he
    rw [if_pos rfl, constantCoeff_eq]
  · rw [if_neg (Ne.symm he)]
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact he (Finsupp.ext hne)
    have h1 := coeff_pderiv (i := i) f (e - Finsupp.single i 1)
    have hle : Finsupp.single i 1 ≤ e := by
      intro k
      rw [Finsupp.single_apply]
      split_ifs with hk
      · subst hk
        omega
      · omega
    have h2 : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
    have h3 : ((((e - Finsupp.single i 1 : ℕ+ →₀ ℕ) i : ℕ) : R)) + 1 = ((e i : ℕ) : R) := by
      have : (e - Finsupp.single i 1 : ℕ+ →₀ ℕ) i + 1 = e i := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      exact_mod_cast congrArg (Nat.cast : ℕ → R) this
    rw [h i, coeff_zero, h2, h3] at h1
    exact nat_mul_cancel hi h1.symm

theorem cc_Tvir_one (al q : R) (m n : ℤ) :
    constantCoeff (Tvir al q m n (1 : MvPolynomial ℕ+ R)) = 0 := by
  rw [Tvir_apply, map_sub, map_sub, map_sub, cc_smul]
  have hite : constantCoeff (if m + n = 0 then
      centralTerm (1 - 12 * q ^ 2) m • (1 : MvPolynomial ℕ+ R) else 0) =
      if m + n = 0 then centralTerm (1 - 12 * q ^ 2) m else 0 := by
    split_ifs <;> simp [cc_smul]
  rw [hite, cc_LOp_one]
  rcases lt_trichotomy n 0 with hn | hn | hn <;> rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [cc_LOp_neg al q hm, cc_LOp_neg al q hn, if_neg (by omega), if_neg (by omega)]
    ring
  · subst hm
    rw [cc_LOp_zero, cc_LOp_neg al q hn, cc_LOp_neg al q hn, if_neg (by omega), if_neg (by omega)]
    ring
  · rw [cc_LL_main al q hm hn, cc_LOp_neg al q hn]
    by_cases h : m + n = 0
    · have hc : ((m - n : ℤ) : R) = 2 * (m : R) := by
        have : m - n = 2 * m := by omega
        rw [this]
        push_cast
        rfl
      simp only [if_pos h, hc]
      ring
    · simp only [if_neg h]
      ring
  · subst hn
    rw [cc_LOp_neg al q hm, cc_LOp_zero, cc_LOp_neg al q hm, if_neg (by omega),
      if_neg (by omega)]
    ring
  · subst hn
    subst hm
    simp only [add_zero, if_true, sub_self, Int.cast_zero, zero_mul, centralTerm_zero]
  · subst hn
    rw [LOp_one_zero, map_smul, LOp_one_pos al q hm, smul_zero]
    simp [show m ≠ 0 by omega]
  · rw [LOp_one_pos al q hn, map_zero, map_zero, cc_LL_main al q hn hm]
    by_cases h : m + n = 0
    · have h' : n + m = 0 := by omega
      have hmn : m = -n := by omega
      have hc : ((m - n : ℤ) : R) = -(2 * (n : R)) := by
        have : m - n = -(2 * n) := by omega
        rw [this]
        push_cast
        rfl
      simp only [if_pos h, if_pos h', hc]
      rw [hmn, centralTerm_neg]
      ring
    · have h' : ¬ (n + m = 0) := by omega
      simp only [if_neg h, if_neg h']
      ring
  · subst hm
    rw [LOp_one_pos al q hn, LOp_one_zero, map_smul, LOp_one_pos al q hn, smul_zero]
    simp [show n ≠ 0 by omega]
  · rw [LOp_one_pos al q hn, LOp_one_pos al q hm, map_zero, map_zero, if_neg (by omega),
      if_neg (by omega)]
    simp

theorem Tvir_one (al q : R) (m n : ℤ) : Tvir al q m n (1 : MvPolynomial ℕ+ R) = 0 := by
  have hp : ∀ i : ℕ+, pderiv i (Tvir al q m n (1 : MvPolynomial ℕ+ R)) = 0 := by
    intro i
    have hi : (0 : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast i.pos
    have h1 := Tvir_h al q m n ((i : ℕ) : ℤ) 1
    rw [hOp_one_pos al hi, map_zero, hOp_pos al hi, pn_coe] at h1
    exact int_smul_cancel (by omega) h1.symm
  rw [eq_C_of_pderiv _ hp, cc_Tvir_one, map_zero]

/-- The Virasoro relations on `𝓕(α)` with `c = 1 − 12 q₀²` (paper.tex l.1263–1264). -/
theorem LOp_vir (al q : R) (m n : ℤ) (f : MvPolynomial ℕ+ R) :
    LOp al q m (LOp al q n f) = LOp al q n (LOp al q m f) +
      ((m - n : ℤ) : R) • LOp al q (m + n) f +
      (if m + n = 0 then centralTerm (1 - 12 * q ^ 2) m • f else 0) := by
  have key := op_ext (Tvir al q m n) (fun j g => by
    have := Tvir_h al q m n (-((j : ℕ) : ℤ)) g
    rwa [hOp_neg_coe, hOp_neg_coe] at this) (Tvir_one al q m n) f
  rw [Tvir_apply] at key
  linear_combination key

end Virasoro.TFock
