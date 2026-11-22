import Virasoro.Proofs.Sec6LimGr4

/-!
# Proposition 6.7, the chain limit (b): coefficients of homogeneous polynomials (l.1141–1146)

For `Q ∈ ℂ[S,W,Y]`:
* `S = 0`: `ev0 Q ∈ ℂ[d][u]` has `[u^a d^n] = [W^a Y^n] Q`;
* `S = 1`: `deh Q = Q(1, 2b⋆w, 2b⋆y) ∈ ℂ[w][y]` (outer `y`); for `Q` homogeneous of degree `e`,
  `[y^k w^j] deh Q = (2b⋆)^{j+k} [S^{e−j−k} W^j Y^k] Q`, so `deh` is injective on homogeneous
  polynomials, and `[y^k] deh Q` has degree at most `e − k` in `w` with top coefficient
  `(2b⋆)^e [W^{e−k} Y^k] Q`.
-/

namespace Virasoro.ChainLim

open Polynomial Finset

/-- The exponent `S^a W^b Y^c`. -/
noncomputable def tri (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

theorem tri_apply0 (a b c : ℕ) : tri a b c 0 = a := by simp [tri]
theorem tri_apply1 (a b c : ℕ) : tri a b c 1 = b := by simp [tri]
theorem tri_apply2 (a b c : ℕ) : tri a b c 2 = c := by simp [tri]

theorem eq_tri (m : Fin 3 →₀ ℕ) : m = tri (m 0) (m 1) (m 2) := by
  ext i
  fin_cases i <;> simp [tri]

theorem deg3 {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e) {m : Fin 3 →₀ ℕ} (hm : Q.coeff m ≠ 0) :
    m 0 + m 1 + m 2 = e := by
  have h := hQ hm
  have e1 : Finsupp.weight 1 m = m.degree := by rw [Finsupp.degree_eq_weight_one]; rfl
  rw [e1, Finsupp.degree_eq_sum, Fin.sum_univ_three] at h
  exact h

/-! ### `S = 1` -/

theorem aeval_monomial_y (α β γ : ℂ) (m : Fin 3 →₀ ℕ) (c : ℂ) :
    (MvPolynomial.aeval ![C (C α), C (C β * X), C (C γ) * X] (MvPolynomial.monomial m c) : P2) =
      C (C (c * α ^ m 0 * β ^ m 1 * γ ^ m 2) * X ^ m 1) * X ^ m 2 := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Polynomial.algebraMap_apply, algebraMap_eq,
    mul_pow, map_mul, map_pow]
  ring

theorem coeff_aeval_y (α β γ : ℂ) (Q : R3) (k j : ℕ) :
    ((MvPolynomial.aeval ![C (C α), C (C β * X), C (C γ) * X] Q : P2).coeff k).coeff j =
      ∑ m ∈ Q.support, if m 1 = j ∧ m 2 = k then Q.coeff m * α ^ m 0 * β ^ j * γ ^ k else 0 := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  refine sum_congr rfl fun m _ => ?_
  rw [aeval_monomial_y, coeff_C_mul_X_pow, apply_ite (fun p : ℂ[X] => p.coeff j),
    coeff_C_mul_X_pow, Polynomial.coeff_zero]
  by_cases h2 : m 2 = k
  · by_cases h1 : m 1 = j
    · subst h1 h2
      simp
    · simp [h1, Ne.symm h1]
  · simp [h2, Ne.symm h2]

/-- `Q(1, 2b⋆w, 2b⋆y)` with `y` the outer variable. -/
noncomputable def deh (bs : ℂ) : R3 →+* P2 :=
  (MvPolynomial.aeval (![C (C 1), C (C (2 * bs) * X), C (C (2 * bs)) * X] : Fin 3 → P2)).toRingHom

theorem deh_apply (bs : ℂ) (Q : R3) : deh bs Q =
    MvPolynomial.aeval (![C (C 1), C (C (2 * bs) * X), C (C (2 * bs)) * X] : Fin 3 → P2) Q := rfl

theorem coeff_deh_hom (bs : ℂ) {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e) (k j : ℕ) :
    ((deh bs Q).coeff k).coeff j =
      if j + k ≤ e then Q.coeff (tri (e - j - k) j k) * (2 * bs) ^ (j + k) else 0 := by
  have h := coeff_aeval_y 1 (2 * bs) (2 * bs) Q k j
  rw [deh_apply, h]
  split_ifs with hjk
  · rw [sum_eq_single (tri (e - j - k) j k)]
    · rw [tri_apply1, tri_apply2, if_pos ⟨rfl, rfl⟩, one_pow, mul_one, mul_assoc, ← pow_add]
    · intro m hm hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hne
      have hd := deg3 hQ (MvPolynomial.mem_support_iff.1 hm)
      rw [eq_tri m, h1, h2]
      congr 1
      omega
    · intro hm
      rw [MvPolynomial.notMem_support_iff.1 hm]
      simp
  · refine sum_eq_zero fun m hm => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hd := deg3 hQ (MvPolynomial.mem_support_iff.1 hm)
    omega

theorem deh_injective_hom {bs : ℂ} (hbs : bs ≠ 0) {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e)
    (h0 : deh bs Q = 0) : Q = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  by_contra hm
  have hd := deg3 hQ hm
  have h := coeff_deh_hom bs hQ (m 2) (m 1)
  rw [h0, Polynomial.coeff_zero, Polynomial.coeff_zero, if_pos (by omega)] at h
  have hm' : tri (e - m 1 - m 2) (m 1) (m 2) = m := by
    rw [eq_tri m]
    simp only [tri_apply0, tri_apply1, tri_apply2]
    congr 1
    omega
  rw [hm'] at h
  have h2 : (2 * bs) ^ (m 1 + m 2) ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hbs)
  exact mul_ne_zero hm h2 h.symm

/-- A polynomial without `Y` has `deh Q` constant in `y`. -/
theorem deh_noY (bs : ℂ) {Q : R3} (hQ : Q ∈ MvPolynomial.supported ℂ ({0, 1} : Set (Fin 3))) :
    deh bs Q = C ((deh bs Q).coeff 0) := by
  ext k j
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_zero]
    rw [deh_apply, coeff_aeval_y]
    refine sum_eq_zero fun m hm => ?_
    rw [if_neg]
    rintro ⟨_, h2⟩
    have hv : (2 : Fin 3) ∉ Q.vars := by
      intro h
      have := (MvPolynomial.mem_supported.1 hQ) h
      simp at this
    have := MvPolynomial.mem_support_notMem_vars_zero hm hv
    omega

/-- `[y^k] deh Q` has degree at most `e − k` in `w`. -/
theorem deh_coeff_natDegree_le (bs : ℂ) {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e) (k : ℕ) :
    ((deh bs Q).coeff k).natDegree ≤ e - k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_deh_hom bs hQ, if_neg]
  have : e - k < j := by exact_mod_cast hj
  omega

theorem deh_coeff_top (bs : ℂ) {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e) {k : ℕ} (hk : k ≤ e) :
    ((deh bs Q).coeff k).coeff (e - k) = Q.coeff (tri 0 (e - k) k) * (2 * bs) ^ e := by
  rw [coeff_deh_hom bs hQ, if_pos (by omega)]
  congr 2
  · congr 1; omega
  · omega

theorem deh_coeff_eq_zero (bs : ℂ) {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e) {k : ℕ} (hk : e < k) :
    (deh bs Q).coeff k = 0 := by
  ext j
  rw [coeff_deh_hom bs hQ, if_neg (by omega), Polynomial.coeff_zero]

/-! ### `S = 0` -/

theorem coeff_ev0 (Q : R3) (a n : ℕ) : ((ev0 Q).coeff a).coeff n = Q.coeff (tri 0 a n) := by
  have hmono : ∀ (m : Fin 3 →₀ ℕ) (c : ℂ), ev0 (MvPolynomial.monomial m c) =
      (0 : P2) ^ m 0 * C (C c * X ^ m 2) * X ^ m 1 := by
    intro m c
    rw [show ev0 (MvPolynomial.monomial m c) = MvPolynomial.aeval
      ![(0 : P2), Polynomial.X, Polynomial.C Polynomial.X] (MvPolynomial.monomial m c) from rfl,
      MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      Fin.prod_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Polynomial.algebraMap_apply, algebraMap_eq,
      map_mul, map_pow]
    ring
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  have hterm : ∀ m : Fin 3 →₀ ℕ, (((ev0 (MvPolynomial.monomial m (Q.coeff m))).coeff a).coeff n) =
      if m = tri 0 a n then Q.coeff m else 0 := by
    intro m
    rw [hmono]
    rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
    · rw [h0, pow_zero, one_mul, coeff_C_mul_X_pow, apply_ite (fun p : ℂ[X] => p.coeff n),
        coeff_C_mul_X_pow, Polynomial.coeff_zero]
      by_cases h1 : a = m 1
      · by_cases h2 : n = m 2
        · rw [if_pos h1, if_pos h2, if_pos]
          rw [eq_tri m, h0, ← h1, ← h2]
        · rw [if_pos h1, if_neg h2, if_neg]
          intro he
          apply h2
          rw [he, tri_apply2]
      · rw [if_neg h1, if_neg]
        intro he
        apply h1
        rw [he, tri_apply1]
    · rw [zero_pow (by omega), zero_mul, zero_mul, Polynomial.coeff_zero, Polynomial.coeff_zero,
        if_neg]
      intro he
      rw [he, tri_apply0] at h0
      omega
  simp_rw [hterm]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.1 h).symm

end Virasoro.ChainLim
