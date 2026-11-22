import Virasoro.Proofs.Sec6FockOps

/-!
# The Virasoro action on the Fock module `𝓕(α)` (paper.tex l.1261–1264)

`L_n = ½ ∑_k :a_k a_{n-k}: − q₀ (n+1) a_n` satisfies
`[L_n, a_m] = −m a_{n+m} − q₀ n(n+1) δ_{n+m,0}` and the Virasoro relations with
`c = 1 − 12 q₀²`; the vector `|α⟩ = 1` is annihilated by `L_n`, `n > 0`, and
`L_0 |α⟩ = ½ α (α − 2 q₀) |α⟩`.
-/

namespace Virasoro.TFock

open MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem lin_ite (T : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R) (P : Prop) [Decidable P]
    (g : MvPolynomial ℕ+ R) : T (if P then g else 0) = if P then T g else 0 := by
  split_ifs <;> simp

/-- `[L_n, x_j] = j a_{n-j} − q₀ n(n+1) δ_{n,j}`. -/
theorem LOp_X (al q : R) (n : ℤ) (j : ℕ+) (f : MvPolynomial ℕ+ R) :
    LOp al q n (X j * f) = X j * LOp al q n f + ((j : ℕ) : R) • hOp al (n - ((j : ℕ) : ℤ)) f
      - (if n = ((j : ℕ) : ℤ) then (q * (n : R) * ((n : R) + 1)) • f else 0) := by
  have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
  have h2 := two_mul_half (R := R)
  rw [LOp_apply, LOp_apply, dOp_X_mul, zOp_X, qOp_X]
  rcases lt_trichotomy n ((j : ℕ) : ℤ) with h | h | h
  · simp only [if_pos h, if_neg (ne_of_lt h), if_neg (not_lt.2 h.le)]
    rw [hOp_neg al (by omega : n - ((j : ℕ) : ℤ) < 0), neg_sub]
    simp only [smul_eq_C_mul, add_zero, sub_zero]
    ring
  · subst h
    simp only [if_neg (lt_irrefl _), if_true, sub_self, hOp_zero, Int.cast_natCast]
    simp only [smul_eq_C_mul, add_zero, map_mul, map_sub, map_add, map_one]
    ring
  · simp only [if_neg (not_lt.2 h.le), if_neg (ne_of_gt h), if_pos h]
    have e : half R * ((2 : R) * ((j : ℕ) : R)) = ((j : ℕ) : R) := by
      linear_combination ((j : ℕ) : R) * h2
    rw [smul_add, smul_smul, e]
    simp only [smul_eq_C_mul, add_zero, sub_zero]
    ring

theorem hOp_dOp_one (al : R) (m n : ℤ) : hOp al m (dOp n (1 : MvPolynomial ℕ+ R)) = 0 := by
  rw [Derivation.map_one_eq_zero, map_zero]

theorem hOp_zOp_one (al q : R) {m : ℤ} (hm : 0 < m) (n : ℤ) :
    hOp al m (zOp al q n (1 : MvPolynomial ℕ+ R)) =
      if n + m = 0 then ((al - q * ((n : R) + 1)) * (m : R)) • (1 : MvPolynomial ℕ+ R)
      else 0 := by
  unfold zOp
  by_cases h0 : n = 0
  · rw [if_pos h0, if_neg (by omega)]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, hOp_one_pos al hm, smul_zero]
  · rw [if_neg h0]
    simp only [LinearMap.smul_apply, map_smul]
    rw [hOp_comm, hOp_one_pos al hm, map_zero, zero_add]
    have : (m + n = 0) ↔ (n + m = 0) := by omega
    rw [if_congr this rfl rfl]
    split_ifs
    · rw [smul_smul]
    · rw [smul_zero]

theorem hOp_qOp_one (al : R) {m : ℤ} (hm : 0 < m) (n : ℤ) :
    hOp al m (qOp al n (1 : MvPolynomial ℕ+ R)) =
      if n + m < 0 then ((2 : R) * (m : R)) • hOp al (n + m) (1 : MvPolynomial ℕ+ R)
      else 0 := by
  rw [qOp_apply, map_sum]
  have h1 : ∀ k ∈ Finset.Ioo (min n 0) (max n 0),
      hOp al m (hOp al k (hOp al (n - k) (1 : MvPolynomial ℕ+ R))) =
        (if k = n + m then (m : R) • hOp al k (1 : MvPolynomial ℕ+ R) else 0) +
        (if k = -m then (m : R) • hOp al (n - k) (1 : MvPolynomial ℕ+ R) else 0) := by
    intro k _
    rw [hOp_comm al m k, hOp_comm al m (n - k), hOp_one_pos al hm, map_zero, zero_add, hOp_ite,
      map_smul]
    have e1 : (m + (n - k) = 0) ↔ (k = n + m) := by omega
    have e2 : (m + k = 0) ↔ (k = -m) := by omega
    rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  by_cases h : n + m < 0
  · rw [if_pos h, if_pos (by rw [Finset.mem_Ioo]; omega), if_pos (by rw [Finset.mem_Ioo]; omega),
      sub_neg_eq_add, ← add_smul]
    congr 1
    ring
  · rw [if_neg h, if_neg (by rw [Finset.mem_Ioo]; omega), if_neg (by rw [Finset.mem_Ioo]; omega),
      add_zero]

/-- `a_m L_n |α⟩` for `m > 0`. -/
theorem hOp_LOp_one (al q : R) {m : ℤ} (hm : 0 < m) (n : ℤ) :
    hOp al m (LOp al q n (1 : MvPolynomial ℕ+ R)) =
      (m : R) • hOp al (n + m) (1 : MvPolynomial ℕ+ R) +
        (if n + m = 0 then (q * (n : R) * ((n : R) + 1)) • (1 : MvPolynomial ℕ+ R) else 0) := by
  have h2 := two_mul_half (R := R)
  rw [LOp_apply, map_add, map_add, map_smul, hOp_dOp_one, hOp_zOp_one al q hm, hOp_qOp_one al hm,
    zero_add]
  rcases lt_trichotomy (n + m) 0 with h | h | h
  · simp only [if_neg (ne_of_lt h), if_pos h, zero_add, add_zero, smul_smul]
    congr 1
    linear_combination (m : R) * h2
  · have hc : (n : R) = -(m : R) := by
      have := congrArg (Int.cast : ℤ → R) h
      push_cast at this
      linear_combination this
    rw [h]
    simp only [eq_self_iff_true, if_true, lt_self_iff_false, if_false, hOp_zero, smul_zero,
      add_zero, smul_smul, ← add_smul, hc]
    congr 1
    ring
  · simp only [if_neg (ne_of_gt h), if_neg (not_lt.2 h.le), hOp_one_pos al h, smul_zero,
      add_zero]

/-- `[L_n, a_m] = −m a_{n+m} − q₀ n(n+1) δ_{n+m,0}`. -/
theorem LOp_h (al q : R) (n m : ℤ) (f : MvPolynomial ℕ+ R) :
    LOp al q n (hOp al m f) = hOp al m (LOp al q n f) - (m : R) • hOp al (n + m) f
      - (if n + m = 0 then (q * (n : R) * ((n : R) + 1)) • f else 0) := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hjm : (((pn (-m) : ℕ+) : ℕ) : ℤ) = -m := coe_pn (by omega)
    have hc : (((pn (-m) : ℕ+) : ℕ) : R) = -(m : R) := by
      have := congrArg (Int.cast : ℤ → R) hjm
      push_cast at this
      exact this
    rw [hOp_neg al hm, hOp_neg al hm, LOp_X, hjm, hc, sub_neg_eq_add]
    have : (n = -m) ↔ (n + m = 0) := by omega
    rw [if_congr this rfl rfl, neg_smul]
    ring
  · subst hm
    rw [hOp_zero, hOp_zero, map_smul, Int.cast_zero, zero_smul, sub_zero, add_zero]
    split_ifs with h
    · subst h; simp
    · rw [sub_zero]
  · have key := op_ext (LOp al q n ∘ₗ hOp al m - hOp al m ∘ₗ LOp al q n +
        (m : R) • hOp al (n + m) +
        (if n + m = 0 then (q * (n : R) * ((n : R) + 1)) • LinearMap.id else 0))
      (fun j g => by
        have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
        have e3 : ∀ g' : MvPolynomial ℕ+ R,
            (if n + m = 0 then (q * (n : R) * ((n : R) + 1)) •
              (LinearMap.id : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R) else 0) g' =
            if n + m = 0 then (q * (n : R) * ((n : R) + 1)) • g' else 0 := by
          intro g'
          split_ifs <;> simp
        simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smul_apply, e3, hOp_X, LOp_X, map_add, map_sub, lin_ite, map_smul]
        rw [hOp_comm al (n - ((j : ℕ) : ℤ)) m g]
        have e1 : (n - ((j : ℕ) : ℤ) + m = 0) ↔ (n + m = ((j : ℕ) : ℤ)) := by omega
        rw [if_congr e1 rfl rfl]
        by_cases hD : n + m = ((j : ℕ) : ℤ)
        · have hc : (n : R) = ((j : ℕ) : R) - (m : R) := by
            have := congrArg (Int.cast : ℤ → R) hD
            push_cast at this
            linear_combination this
          have hne : n + m ≠ 0 := by omega
          simp only [if_pos hD, if_neg hne]
          push_cast
          rw [hc]
          split_ifs <;> simp only [smul_eq_C_mul, map_sub, map_mul, map_add, map_one] <;> ring
        · simp only [if_neg hD]
          split_ifs <;> simp only [smul_eq_C_mul, map_sub, map_mul, map_add, map_one] <;> ring)
      (by
        have e3 : (if n + m = 0 then (q * (n : R) * ((n : R) + 1)) •
              (LinearMap.id : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R) else 0) 1 =
            if n + m = 0 then (q * (n : R) * ((n : R) + 1)) • (1 : MvPolynomial ℕ+ R) else 0 := by
          split_ifs <;> simp
        simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smul_apply, e3, hOp_one_pos al hm, map_zero, hOp_LOp_one al q hm]
        ring) f
    have e3 : (if n + m = 0 then (q * (n : R) * ((n : R) + 1)) •
          (LinearMap.id : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R) else 0) f =
        if n + m = 0 then (q * (n : R) * ((n : R) + 1)) • f else 0 := by
      split_ifs <;> simp
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, e3] at key
    linear_combination key

end Virasoro.TFock
