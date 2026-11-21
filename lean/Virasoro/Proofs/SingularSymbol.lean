import Virasoro.Proofs.PBWIndep
import Virasoro.Proofs.VermaBasic
import Mathlib.Tactic.Abel

/-!
# The length-`K` part of `L_j w` (proof of Lemma 5.7, paper.tex l.719–733)

In the polynomial realization `Φ` of the Verma module (`Verma.polyMap`), the vector
`L_{-y_1} ⋯ L_{-y_K}|h⟩` is `x_{y_1} ⋯ x_{y_K}` plus terms of degree less than `K`.  Moving a
positive mode `L_j` to the right through such a word replaces a factor `L_{-m}`, `m > j`, by
`(m + j) L_{-(m-j)}`; for `m = j` the commutator acts by a scalar and for `m < j` it is a
positive mode, and both lower the length.  Hence
`Φ(L_j L_{-Y}|h⟩) = D_j (x_{y_1} ⋯ x_{y_K}) + (terms of degree < K)` with
`D_j = ∑_{m > j} (m + j) x_{m-j} ∂/∂x_m`.

Consumer: `sub_singular_ones_coeff` in `Virasoro/Proofs/SingularOnes.lean`.
-/

namespace Virasoro

open MvPolynomial

section Poly

variable {R : Type*} [CommRing R]

/-- The derivation `D_j = ∑_{m > j} (m + j) x_{m-j} ∂/∂x_m`. -/
noncomputable def symD (j : ℕ) : Derivation R (MvPolynomial ℕ R) (MvPolynomial ℕ R) :=
  mkDerivation R fun m => if j < m then ((m + j : ℕ) : R) • X (m - j) else 0

theorem symD_X (j m : ℕ) :
    symD (R := R) j (X m) = if j < m then ((m + j : ℕ) : R) • X (m - j) else 0 :=
  mkDerivation_X _ _ _

theorem isHomogeneous_symD_monomial (j : ℕ) (s : ℕ →₀ ℕ) (a : R) :
    IsHomogeneous (symD j (monomial s a)) s.degree := by
  rw [symD, mkDerivation_monomial]
  refine (homogeneousSubmodule ℕ R s.degree).smul_mem a ?_
  refine (homogeneousSubmodule ℕ R s.degree).sum_mem fun i hi => ?_
  have hle : Finsupp.single i 1 ≤ s := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
  have hdeg : (s - Finsupp.single i 1).degree + 1 = s.degree := by
    conv_rhs => rw [← tsub_add_cancel_of_le hle, map_add, Finsupp.degree_single]
  rw [mem_homogeneousSubmodule]
  show IsHomogeneous (monomial (s - Finsupp.single i 1) ((s i : ℕ) : R)
    • (if j < i then ((i + j : ℕ) : R) • (X (i - j) : MvPolynomial ℕ R) else 0)) s.degree
  rw [smul_eq_mul, ← hdeg]
  refine (isHomogeneous_monomial _ rfl).mul ?_
  split_ifs
  · exact (homogeneousSubmodule ℕ R 1).smul_mem _ (isHomogeneous_X R _)
  · exact (homogeneousSubmodule ℕ R 1).zero_mem

theorem LowDeg.smul {q : MvPolynomial ℕ R} {r : ℕ} (hq : LowDeg q r) (a : R) :
    LowDeg (a • q) r := by
  intro d hd
  rw [coeff_smul] at hd
  exact hq d fun h0 => hd (by rw [h0, smul_zero])

theorem lowDeg_of_isHomogeneous {q : MvPolynomial ℕ R} {n r : ℕ} (hq : IsHomogeneous q n)
    (h : n < r) : LowDeg q r := by
  intro d hd
  by_contra hcon
  exact hd (hq.coeff_eq_zero fun e => hcon (by rw [e]; exact h))

theorem wordExp_cons (y : ℕ) (w : List ℕ) :
    wordExp (y :: w) = Finsupp.single y 1 + wordExp w := by simp [wordExp]

theorem monomial_wordExp_cons (y : ℕ) (w : List ℕ) :
    monomial (wordExp (y :: w)) (1 : R) = X y * monomial (wordExp w) 1 := by
  rw [wordExp_cons, X, monomial_mul, one_mul]

theorem lowDeg_symD_wordExp (j : ℕ) (w : List ℕ) :
    LowDeg (symD j (monomial (wordExp w) (1 : R))) (w.length + 1) := by
  have := isHomogeneous_symD_monomial j (wordExp w) (1 : R)
  rw [wordExp_degree] at this
  exact lowDeg_of_isHomogeneous this (Nat.lt_succ_self _)

/-- On a monomial in `x_1, …, x_{j+1}` only the term `m = j + 1` of `D_j` acts:
`D_j x^e = (2j + 1) e_{j+1} x_1 x^e / x_{j+1}`. -/
theorem symD_monomial_top (j : ℕ) (e : ℕ →₀ ℕ) (he : ∀ i, e i ≠ 0 → i ≤ j + 1) :
    symD (R := R) j (monomial e 1) =
      monomial (e - Finsupp.single (j + 1) 1 + Finsupp.single 1 1)
        (((e (j + 1) : ℕ) : R) * ((2 * j + 1 : ℕ) : R)) := by
  rw [symD, mkDerivation_monomial, one_smul, Finsupp.sum, Finset.sum_eq_single (j + 1)]
  · rw [if_pos (Nat.lt_succ_self j), show j + 1 - j = 1 by omega,
      show j + 1 + j = 2 * j + 1 by omega, smul_eq_mul, MvPolynomial.smul_eq_C_mul, X,
      C_mul_monomial, monomial_mul, mul_one]
  · intro i hi hne
    have := he i (Finsupp.mem_support_iff.1 hi)
    rw [if_neg (by omega), smul_zero]
  · intro hn
    rw [Finsupp.notMem_support_iff.1 hn]
    simp

end Poly

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

theorem polyMap_neg_lowDeg (w : List ℕ) (hw : PosWord w) :
    LowDeg (polyMap c h (neg w)) (w.length + 1) := by
  obtain ⟨q, hq, hlow⟩ := polyMap_neg (c := c) (h := h) w hw
  rw [hq]
  refine LowDeg.add ?_ (hlow.mono (Nat.le_succ _))
  exact lowDeg_of_isHomogeneous (isHomogeneous_monomial _ (wordExp_degree w)) (Nat.lt_succ_self _)

/-- `Φ(L_j L_{-w}|h⟩) = D_j (x_{w_1} ⋯ x_{w_r}) + (terms of degree < r)` for `j ≥ 1`. -/
theorem polyMap_L_pos_neg : ∀ w : List ℕ, PosWord w → ∀ j : ℕ, 0 < j →
    ∃ q : MvPolynomial ℕ R,
      polyMap c h (L (j : ℤ) (neg w)) = symD j (monomial (wordExp w) 1) + q ∧
        LowDeg q w.length
  | [], _, j, hj => by
    refine ⟨0, ?_, lowDeg_zero _⟩
    have h0 : wordExp [] = 0 := by simp [wordExp]
    have h1 : (monomial (0 : ℕ →₀ ℕ) (1 : R)) = C 1 := rfl
    rw [neg_nil, L_hw_pos (by exact_mod_cast hj), map_zero, add_zero, h0, h1]
    exact (Derivation.map_algebraMap _ _).symm
  | y :: w, hw, j, hj => by
    have hy : 0 < y := hw y List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    obtain ⟨q, hq, hlow⟩ := polyMap_L_pos_neg w hw' j hj
    have hB := polyMap_neg_lowDeg (c := c) (h := h) w hw'
    have hD : symD j (monomial (wordExp (y :: w)) (1 : R)) =
        X y * symD j (monomial (wordExp w) 1) + monomial (wordExp w) 1 * symD j (X y) := by
      rw [monomial_wordExp_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hLL := L_L (c := c) (h := h) (j : ℤ) (-(y : ℤ)) (neg w)
    have hhom := lowDeg_symD_wordExp (R := R) j w
    have hyZ : (0 : ℤ) < (y : ℤ) := by exact_mod_cast hy
    have h1 : polyMap c h (L (-(y : ℤ)) (L (j : ℤ) (neg w))) =
        X y * symD j (monomial (wordExp w) 1) +
          (X y * q + polyD y (symD j (monomial (wordExp w) 1)) + polyD y q) := by
      rw [polyMap_L_neg hyZ, Int.toNat_natCast, hq, polyG_apply, map_add]
      ring
    have h1low : LowDeg (X y * q + polyD y (symD j (monomial (wordExp w) (1 : R))) + polyD y q)
        (w.length + 1) :=
      ((hlow.X_mul y).add (hhom.deriv y)).add ((hlow.deriv y).mono (Nat.le_succ _))
    have hcast : (((j : ℤ) - -(y : ℤ) : ℤ) : R) = ((y + j : ℕ) : R) := by
      push_cast
      ring
    rw [neg_cons, hLL, map_add, map_add, h1, hD, symD_X, map_smul, hcast]
    rcases lt_trichotomy j y with hjy | hjy | hjy
    · have e : ((j : ℤ) + -(y : ℤ)) = -(((y - j : ℕ) : ℕ) : ℤ) := by omega
      obtain ⟨q1, hq1, hlow1⟩ := polyMap_neg (c := c) (h := h) ((y - j) :: w)
        (fun z hz => by
          rcases List.mem_cons.1 hz with rfl | hz
          · omega
          · exact hw' z hz)
      rw [if_neg (by omega), map_zero, if_pos hjy, e, ← neg_cons, hq1, monomial_wordExp_cons]
      refine ⟨X y * q + polyD y (symD j (monomial (wordExp w) 1)) + polyD y q +
        ((y + j : ℕ) : R) • q1, ?_, h1low.add (hlow1.smul _)⟩
      simp only [MvPolynomial.smul_eq_C_mul]
      ring
    · subst hjy
      rw [add_neg_cancel, if_pos rfl, if_neg (lt_irrefl _), L_zero_neg, map_smul, map_smul,
        mul_zero, add_zero]
      refine ⟨X j * q + polyD j (symD j (monomial (wordExp w) 1)) + polyD j q +
        ((j + j : ℕ) : R) • (h + ((w.sum : ℕ) : R)) • polyMap c h (neg w) +
        centralTerm c (j : ℤ) • polyMap c h (neg w), ?_,
        (h1low.add ((hB.smul _).smul _)).add (hB.smul _)⟩
      abel
    · have e : ((j : ℤ) + -(y : ℤ)) = (((j - y : ℕ) : ℕ) : ℤ) := by omega
      obtain ⟨q2, hq2, hlow2⟩ := polyMap_L_pos_neg w hw' (j - y) (by omega)
      rw [if_neg (by omega), map_zero, if_neg (by omega), e, hq2, mul_zero, add_zero, add_zero]
      refine ⟨X y * q + polyD y (symD j (monomial (wordExp w) 1)) + polyD y q +
        ((y + j : ℕ) : R) • (symD (j - y) (monomial (wordExp w) 1) + q2), ?_,
        h1low.add (((lowDeg_symD_wordExp (j - y) w).add (hlow2.mono (Nat.le_succ _))).smul _)⟩
      abel

end Verma

end Virasoro
