import Virasoro.Sphere.CitedSchur
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Theorem 5.5, step (4): `H_M(α) ≠ 0` (sphere/paper.tex l.1758–1781)

The leading coefficient `[v^M] H_M(v)` is a nonzero multiple of `k_M = M! [t^M] exp(-bt - gt²)`
with `b = 2X/(pp')`, `g = 1/(pp')` (rational).  The sequence `k` satisfies the Hermite
recurrence; with `r = b²/(4g)` (`= α²`), `k_{2m} = g^m E_m(r)` and `k_{2m+1} = -(b/2) g^m O_m(r)`,
where `H_{2m}(x) = E_m(x²)` and `H_{2m+1}(x) = x O_m(x²)`.  For `m ≤ 1` the values are explicit
(`E₁ = 4t - 2`, `O₁ = 8t - 12`); for `m ≥ 2` Schur's theorems exclude a rational root: a root
`r` of `E_m` gives the factor `x² - r` of the irreducible `H_{2m}` of degree `2m ≥ 4`
(l.1775–1781).
-/

namespace Virasoro.Sphere

open Polynomial

/-- Check of the definition: `H₂ = 4x² - 2` (DLMF Table 18.3.1). -/
theorem hermH_two : hermH 2 = C 4 * X ^ 2 - C 2 := by
  rw [hermH.eq_3, hermH.eq_2, hermH.eq_1]
  simp only [map_ofNat, Nat.cast_zero, zero_add, mul_one]
  ring

/-- Check of the definition: `H₃ = 8x³ - 12x` (DLMF Table 18.3.1). -/
theorem hermH_three : hermH 3 = C 8 * X ^ 3 - C 12 * X := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, hermH.eq_3, show (1 + 1 : ℕ) = 2 from rfl, hermH_two,
    hermH.eq_2, show (2 * (((1 : ℕ) : ℚ) + 1)) = 4 by norm_num]
  simp only [map_ofNat]
  ring

/-- The parts `(E_m, O_m)` of the Hermite polynomials in `t = x²`. -/
noncomputable def hermEO : ℕ → ℚ[X] × ℚ[X]
  | 0 => (1, C 2)
  | m + 1 =>
    (C 2 * X * (hermEO m).2 - C (2 * (2 * (m : ℚ) + 1)) * (hermEO m).1,
      C 2 * (C 2 * X * (hermEO m).2 - C (2 * (2 * (m : ℚ) + 1)) * (hermEO m).1) -
        C (4 * ((m : ℚ) + 1)) * (hermEO m).2)

/-- `E_m`, with `H_{2m}(x) = E_m(x²)`. -/
noncomputable def hermE (m : ℕ) : ℚ[X] := (hermEO m).1

/-- `O_m`, with `H_{2m+1}(x) = x O_m(x²)`. -/
noncomputable def hermO (m : ℕ) : ℚ[X] := (hermEO m).2

theorem hermE_zero : hermE 0 = 1 := rfl

theorem hermO_zero : hermO 0 = C 2 := rfl

theorem hermE_succ (m : ℕ) :
    hermE (m + 1) = C 2 * X * hermO m - C (2 * (2 * (m : ℚ) + 1)) * hermE m := rfl

theorem hermO_succ (m : ℕ) :
    hermO (m + 1) = C 2 * hermE (m + 1) - C (4 * ((m : ℚ) + 1)) * hermO m := rfl

/-- `H_{2m} = E_m(x²)` and `H_{2m+1} = x O_m(x²)`. -/
theorem hermH_eo (m : ℕ) :
    hermH (2 * m) = expand ℚ 2 (hermE m) ∧ hermH (2 * m + 1) = X * expand ℚ 2 (hermO m) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [hermE_zero, map_one]; rfl
    · rw [hermO_zero, expand_C, Nat.mul_zero, Nat.zero_add, hermH.eq_2, mul_comm]
  | succ m ih =>
    have e1 : hermH (2 * (m + 1)) = C 2 * X * hermH (2 * m + 1) -
        C (2 * (((2 * m : ℕ) : ℚ) + 1)) * hermH (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, hermH.eq_3]
    have e2 : hermH (2 * (m + 1) + 1) = C 2 * X * hermH (2 * (m + 1)) -
        C (2 * (((2 * m + 1 : ℕ) : ℚ) + 1)) * hermH (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, hermH.eq_3,
        show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    have c1 : (2 * (((2 * m : ℕ) : ℚ) + 1)) = 2 * (2 * (m : ℚ) + 1) := by push_cast; ring
    have c2 : (2 * (((2 * m + 1 : ℕ) : ℚ) + 1)) = 4 * ((m : ℚ) + 1) := by push_cast; ring
    have hE : hermH (2 * (m + 1)) = expand ℚ 2 (hermE (m + 1)) := by
      rw [e1, c1, ih.1, ih.2, hermE_succ]
      simp only [map_sub, map_mul, expand_C, expand_X]
      ring
    refine ⟨hE, ?_⟩
    rw [e2, c2, hE, ih.2, hermO_succ]
    simp only [map_sub, map_mul, expand_C]
    ring

/-- `deg E_m ≤ m`, `[t^m]E_m = 4^m`, `deg O_m ≤ m`, `[t^m]O_m = 2·4^m`. -/
theorem hermEO_deg (m : ℕ) :
    (hermE m).natDegree ≤ m ∧ (hermE m).coeff m = 4 ^ m ∧
      (hermO m).natDegree ≤ m ∧ (hermO m).coeff m = 2 * 4 ^ m := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hermE_zero, natDegree_one]
    · rw [hermE_zero, coeff_one_zero, pow_zero]
    · rw [hermO_zero, natDegree_C]
    · rw [hermO_zero, coeff_C_zero, pow_zero, mul_one]
  | succ m ih =>
    obtain ⟨hE1, hE2, hO1, hO2⟩ := ih
    have hEd : (hermE (m + 1)).natDegree ≤ m + 1 := by
      rw [hermE_succ]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (C (2 : ℚ) * X).natDegree ≤ 1 :=
          (natDegree_C_mul_le _ _).trans natDegree_X_le
        omega
      · exact (natDegree_C_mul_le _ _).trans (hE1.trans (Nat.le_succ m))
    have hEc : (hermE (m + 1)).coeff (m + 1) = 4 ^ (m + 1) := by
      rw [hermE_succ, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul, hO2, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : (hermE m).natDegree < m + 1)]
      ring
    refine ⟨hEd, hEc, ?_, ?_⟩
    · rw [hermO_succ]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans hEd
      · exact (natDegree_C_mul_le _ _).trans (hO1.trans (Nat.le_succ m))
    · rw [hermO_succ, coeff_sub, coeff_C_mul, hEc, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : (hermO m).natDegree < m + 1)]
      ring

theorem natDegree_hermE (m : ℕ) : (hermE m).natDegree = m :=
  natDegree_eq_of_le_of_coeff_ne_zero (hermEO_deg m).1
    (by rw [(hermEO_deg m).2.1]; positivity)

theorem natDegree_hermO (m : ℕ) : (hermO m).natDegree = m :=
  natDegree_eq_of_le_of_coeff_ne_zero (hermEO_deg m).2.2.1
    (by rw [(hermEO_deg m).2.2.2]; positivity)

theorem natDegree_zero_of_isUnit {p : ℚ[X]} (hp : IsUnit p) : p.natDegree = 0 :=
  natDegree_eq_of_degree_eq_some (isUnit_iff_degree_eq_zero.1 hp)

/-- An irreducible `F = G(x²)` with `deg G ≥ 2` gives `G` no rational root (l.1778–1781). -/
theorem no_root_of_irreducible {F G : ℚ[X]} (hirr : Irreducible F) (hF : F = expand ℚ 2 G)
    (hdeg : 2 ≤ G.natDegree) (r : ℚ) : G.eval r ≠ 0 := by
  intro h0
  obtain ⟨d, hd⟩ := dvd_iff_isRoot.2 h0
  have hq : expand ℚ 2 (X - C r) = X ^ 2 - C r := by rw [map_sub, expand_X, expand_C]
  have hFq : F = (X ^ 2 - C r) * expand ℚ 2 d := by rw [hF, hd, map_mul, hq]
  have hFdeg : F.natDegree = G.natDegree * 2 := by rw [hF, natDegree_expand]
  have hq2 : (X ^ 2 - C r : ℚ[X]).natDegree = 2 := natDegree_X_pow_sub_C
  rcases hirr.isUnit_or_isUnit hFq with hu | hu
  · have := natDegree_zero_of_isUnit hu
    omega
  · have hF0 : F ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hFdeg
      omega
    have hq0 : (X ^ 2 - C r : ℚ[X]) ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hq2
      omega
    have he0 : expand ℚ 2 d ≠ 0 := by
      intro h
      rw [h, mul_zero] at hFq
      exact hF0 hFq
    have := natDegree_mul hq0 he0
    rw [← hFq, hq2, natDegree_zero_of_isUnit hu] at this
    omega

/-- Schur: for `m ≥ 2`, neither `E_m` nor `O_m` has a rational root. -/
theorem hermEO_no_root (hS : Cited_SchurHermite) {m : ℕ} (hm : 2 ≤ m) (r : ℚ) :
    (hermE m).eval r ≠ 0 ∧ (hermO m).eval r ≠ 0 := by
  obtain ⟨hE, hO⟩ := hS m (by omega)
  have h := hermH_eo m
  refine ⟨no_root_of_irreducible hE h.1 (by rw [natDegree_hermE]; exact hm) r, ?_⟩
  have hdiv : hermH (2 * m + 1) /ₘ X = expand ℚ 2 (hermO m) := by
    rw [h.2, mul_divByMonic_cancel_left _ monic_X]
  exact no_root_of_irreducible (hdiv ▸ hO) rfl (by rw [natDegree_hermO]; exact hm) r

/-! ### The sequence `k_n = n! [t^n] exp(-bt - gt²)` -/

/-- `k₀ = 1`, `k₁ = -b`, `k_{n+2} = -b k_{n+1} - 2(n+1) g k_n`. -/
def kseq (b g : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => -b
  | n + 2 => -b * kseq b g (n + 1) - 2 * ((n : ℚ) + 1) * g * kseq b g n

theorem kseq_eo (b g : ℚ) (hg : g ≠ 0) (m : ℕ) :
    kseq b g (2 * m) = g ^ m * (hermE m).eval (b ^ 2 / (4 * g)) ∧
      kseq b g (2 * m + 1) = -(b / 2) * g ^ m * (hermO m).eval (b ^ 2 / (4 * g)) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [kseq, hermE_zero]
    · simp only [kseq, hermO_zero, eval_C, pow_zero, mul_one]
      ring
  | succ m ih =>
    have k1 : kseq b g (2 * (m + 1)) = -b * kseq b g (2 * m + 1) -
        2 * (((2 * m : ℕ) : ℚ) + 1) * g * kseq b g (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, kseq.eq_3]
    have k2 : kseq b g (2 * (m + 1) + 1) = -b * kseq b g (2 * (m + 1)) -
        2 * (((2 * m + 1 : ℕ) : ℚ) + 1) * g * kseq b g (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, kseq.eq_3,
        show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    have hE : kseq b g (2 * (m + 1)) = g ^ (m + 1) * (hermE (m + 1)).eval (b ^ 2 / (4 * g)) := by
      rw [k1, ih.1, ih.2, hermE_succ]
      simp only [eval_sub, eval_mul, eval_C, eval_X]
      push_cast
      field_simp
      ring
    refine ⟨hE, ?_⟩
    rw [k2, hE, ih.2, hermO_succ]
    simp only [eval_sub, eval_mul, eval_C]
    push_cast
    ring

theorem hermE_one_eval (r : ℚ) : (hermE 1).eval r = 4 * r - 2 := by
  rw [hermE_succ, hermO_zero, hermE_zero]
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_one]
  ring

theorem hermO_one_eval (r : ℚ) : (hermO 1).eval r = 8 * r - 12 := by
  rw [hermO_succ, hermE_succ, hermO_zero, hermE_zero]
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_one]
  ring

/-- `k_n ≠ 0` when `b, g ≠ 0` and `r = b²/(4g) ∉ {1/2, 3/2}` (l.1762–1781). -/
theorem kseq_ne_zero (hS : Cited_SchurHermite) {b g : ℚ} (hb : b ≠ 0) (hg : g ≠ 0)
    (h2 : b ^ 2 / (4 * g) ≠ 1 / 2) (h3 : b ^ 2 / (4 * g) ≠ 3 / 2) (n : ℕ) : kseq b g n ≠ 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [(kseq_eo b g hg m).1]
    refine mul_ne_zero (pow_ne_zero _ hg) ?_
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · rw [hermE_zero, eval_one]; exact one_ne_zero
      · rw [hermE_one_eval]
        intro h
        apply h2
        linarith
    · exact (hermEO_no_root hS hm _).1
  · rw [(kseq_eo b g hg m).2]
    refine mul_ne_zero (mul_ne_zero (by simpa using hb) (pow_ne_zero _ hg)) ?_
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · rw [hermO_zero, eval_C]; norm_num
      · rw [hermO_one_eval]
        intro h
        apply h3
        linarith
    · exact (hermEO_no_root hS hm _).2

end Virasoro.Sphere
