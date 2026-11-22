import Virasoro.Proofs.Sec6FockRel
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The contravariant pairing between `𝓕(2q₀ − α)` and `𝓕(α)` (paper.tex l.1264–1268)

The bilinear form with
`⟨a_{-λ}, a_{-μ}⟩ = δ_{λ,μ} (−1)^{ℓ(λ)} ∏_n m_n! n^{m_n}` satisfies `a_n† = −a_{-n}` (`n ≠ 0`),
`a_0† = 2q₀ − a_0`, and `L_n† = L_{-n}`.
-/

namespace Virasoro.TFock

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- `(−1)^{ℓ(λ)} ∏_n m_n! n^{m_n}` for the monomial with exponents `m_n` (paper.tex l.1267). -/
def wgt (e : ℕ+ →₀ ℕ) : ℤ :=
  e.prod fun n a => (-1) ^ a * (a.factorial : ℤ) * ((n : ℕ) : ℤ) ^ a

theorem wgt_zero : wgt 0 = 1 := by simp [wgt]

theorem wgt_add_single (e : ℕ+ →₀ ℕ) (n : ℕ+) :
    wgt (e + Finsupp.single n 1) = -((e n : ℤ) + 1) * ((n : ℕ) : ℤ) * wgt e := by
  classical
  set g : ℕ+ → ℕ → ℤ := fun n a => (-1) ^ a * (a.factorial : ℤ) * ((n : ℕ) : ℤ) ^ a with hg
  have hg0 : ∀ a, g a 0 = 1 := fun a => by simp [hg]
  set s : Finset ℕ+ := insert n e.support with hs
  have h1 : wgt (e + Finsupp.single n 1) = ∏ a ∈ s, g a ((e + Finsupp.single n 1 : ℕ+ →₀ ℕ) a) := by
    refine Finsupp.prod_of_support_subset _ ?_ _ fun a _ => hg0 a
    intro a ha
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at ha
    rw [hs, Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases h : n = a
    · left; exact h.symm
    · right
      rw [if_neg h, add_zero] at ha
      exact ha
  have h2 : wgt e = ∏ a ∈ s, g a (e a) :=
    Finsupp.prod_of_support_subset _ (Finset.subset_insert _ _) _ fun a _ => hg0 a
  have hn : n ∈ s := Finset.mem_insert_self _ _
  rw [h1, h2, ← Finset.mul_prod_erase s _ hn, ← Finset.mul_prod_erase s _ hn]
  have h3 : ∏ a ∈ s.erase n, g a ((e + Finsupp.single n 1 : ℕ+ →₀ ℕ) a) = ∏ a ∈ s.erase n, g a (e a) := by
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase ha).symm,
      add_zero]
  rw [h3, Finsupp.add_apply, Finsupp.single_eq_same]
  simp only [hg, pow_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The pairing (paper.tex l.1264–1268), bilinear over `R`. -/
noncomputable def pair : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R →ₗ[R] R :=
  (basisMonomials ℕ+ R).constr R fun e => ((wgt e : ℤ) : R) • lcoeff R e

theorem pair_monomial (e : ℕ+ →₀ ℕ) (c : R) (g : MvPolynomial ℕ+ R) :
    pair (monomial e c) g = c * (wgt e : R) * coeff e g := by
  have h1 : (monomial e c : MvPolynomial ℕ+ R) = c • basisMonomials ℕ+ R e := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, LinearMap.smul_apply, pair, Module.Basis.constr_basis]
  simp [mul_assoc]

theorem pair_one_left (g : MvPolynomial ℕ+ R) : pair 1 g = constantCoeff g := by
  have : (1 : MvPolynomial ℕ+ R) = monomial 0 1 := rfl
  rw [this, pair_monomial, wgt_zero, constantCoeff_eq]
  simp

theorem pair_symm (f g : MvPolynomial ℕ+ R) : pair f g = pair g f := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, map_add, hp, hq]
  | monomial e c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => rw [map_add, LinearMap.map_add₂, hp, hq]
    | monomial e' c' =>
      classical
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases h : e = e'
      · subst h
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg h, if_neg (Ne.symm h)]
        ring

theorem pair_one_right (f : MvPolynomial ℕ+ R) : pair f 1 = constantCoeff f := by
  rw [pair_symm, pair_one_left]

/-- `⟨x_j f, g⟩ = −⟨f, j ∂_j g⟩`: `a_{-j}† = −a_j`. -/
theorem pair_X (j : ℕ+) (f g : MvPolynomial ℕ+ R) :
    pair (X j * f) g = -pair f (((j : ℕ) : R) • pderiv j g) := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, map_add, LinearMap.add_apply, hp, hq, map_add, LinearMap.add_apply, neg_add]
  | monomial e c =>
    have h1 : (X j : MvPolynomial ℕ+ R) * monomial e c = monomial (e + Finsupp.single j 1) c := by
      rw [X, monomial_mul, one_mul, add_comm]
    rw [h1, pair_monomial, pair_monomial, coeff_smul, coeff_pderiv, wgt_add_single, smul_eq_mul]
    push_cast
    ring

/-- `⟨j ∂_j f, g⟩ = −⟨f, x_j g⟩`: `a_j† = −a_{-j}`. -/
theorem pair_D (j : ℕ+) (f g : MvPolynomial ℕ+ R) :
    pair (((j : ℕ) : R) • pderiv j f) g = -pair f (X j * g) := by
  rw [pair_symm, pair_symm f, pair_X, neg_neg]

/-- `a_k† = −a_{-k}` for `k ≠ 0`, `a_0† = 2q₀ − a_0` (paper.tex l.1266). -/
theorem pair_h (al q : R) (k : ℤ) (f g : MvPolynomial ℕ+ R) :
    pair (hOp (2 * q - al) k f) g =
      if k = 0 then (2 * q - al) * pair f g else -pair f (hOp al (-k) g) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hjm : (((pn (-k) : ℕ+) : ℕ) : ℤ) = -k := coe_pn (by omega)
    have hc : (((pn (-k) : ℕ+) : ℕ) : R) = ((-k : ℤ) : R) := by
      rw [← hjm]
      push_cast
      rfl
    rw [if_neg (by omega), hOp_neg _ hk, hOp_pos al (by omega : 0 < -k), pair_X, hc]
  · subst hk
    rw [if_pos rfl, hOp_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]
  · have hjm : (((pn k : ℕ+) : ℕ) : ℤ) = k := coe_pn hk
    have hc : (((pn k : ℕ+) : ℕ) : R) = (k : R) := by
      rw [← hjm]
      push_cast
      rfl
    rw [if_neg (by omega), hOp_pos _ hk, hOp_neg al (by omega : -k < 0), neg_neg, ← hc, pair_D]

variable [Algebra ℚ R]

theorem wt_dual (al q : R) : wt (2 * q - al) q = wt al q := by
  have h2 := two_mul_half (R := R)
  unfold wt
  linear_combination (2 * q ^ 2 - 2 * q * al) * h2

/-- `⟨L_n |2q₀−α⟩, g⟩ = ⟨2q₀−α| L_{-n} g⟩`. -/
theorem pair_L_one (al q : R) (n : ℤ) (g : MvPolynomial ℕ+ R) :
    pair (LOp (2 * q - al) q n 1) g = pair 1 (LOp al q (-n) g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    have : (C a : MvPolynomial ℕ+ R) = a • (1 : MvPolynomial ℕ+ R) := by
      rw [smul_eq_C_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, pair_one_right, pair_one_left, cc_LOp_one, cc_LOp_one,
      wt_dual]
    have : (-n = 0) ↔ (n = 0) := by omega
    rw [if_congr this rfl rfl]
  | add p q' hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
    have hL : ((j : ℕ) : R) • pderiv j (LOp (2 * q - al) q n (1 : MvPolynomial ℕ+ R)) =
        ((j : ℕ) : R) • hOp (2 * q - al) (n + ((j : ℕ) : ℤ)) (1 : MvPolynomial ℕ+ R) +
          (if n + ((j : ℕ) : ℤ) = 0 then (q * (n : R) * ((n : R) + 1)) • (1 : MvPolynomial ℕ+ R)
            else 0) := by
      have := hOp_LOp_one (2 * q - al) q hj n
      rw [hOp_pos _ hj, pn_coe, Int.cast_natCast] at this
      exact this
    rw [mul_comm p (X j), pair_symm, pair_X, hL, map_add, map_smul, pair_symm p, pair_h]
    simp only [pair_one_left]
    rw [cc_LOp_X, smul_eq_mul]
    have e1 : (-n = ((j : ℕ) : ℤ)) ↔ (n + ((j : ℕ) : ℤ) = 0) := by omega
    rw [if_congr e1 rfl rfl]
    by_cases h : n + ((j : ℕ) : ℤ) = 0
    · have hc : ((j : ℕ) : R) = -(n : R) := by
        have := congrArg (Int.cast : ℤ → R) h
        push_cast at this
        linear_combination this
      have h0 : -n - ((j : ℕ) : ℤ) = 0 := by omega
      simp only [if_pos h, h0, hOp_zero, cc_smul, map_smul, pair_one_right, pair_one_left,
        smul_eq_mul, map_one, mul_one]
      push_cast
      rw [hc]
      ring
    · have e2 : -(n + ((j : ℕ) : ℤ)) = -n - ((j : ℕ) : ℤ) := by ring
      simp only [if_neg h, e2, pair_one_left, map_zero, mul_neg, neg_neg, add_zero, sub_zero]

/-- `L_n† = L_{-n}` (paper.tex l.1266–1267). -/
theorem pair_L (al q : R) (n : ℤ) (f g : MvPolynomial ℕ+ R) :
    pair (LOp (2 * q - al) q n f) g = pair f (LOp al q (-n) g) := by
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    have : (C a : MvPolynomial ℕ+ R) = a • (1 : MvPolynomial ℕ+ R) := by
      rw [smul_eq_C_mul, mul_one]
    rw [this, map_smul, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
      pair_L_one]
  | add p q' hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hp, hq]
  | mul_X p j hp =>
    have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
    have hh : ∀ x : MvPolynomial ℕ+ R, ((j : ℕ) : R) • pderiv j x = hOp al ((j : ℕ) : ℤ) x :=
      fun x => by rw [hOp_pos al hj, pn_coe, Int.cast_natCast]
    rw [mul_comm p (X j), LOp_X, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      pair_X, hh, hp, pair_X, hh, LOp_h]
    by_cases h : n = ((j : ℕ) : ℤ)
    · subst h
      simp only [sub_self, neg_add_cancel, if_true, hOp_zero, map_sub, map_smul, smul_eq_mul,
        LinearMap.smul_apply]
      push_cast
      ring
    · have h1 : ¬ (n - ((j : ℕ) : ℤ) = 0) := by omega
      have h2 : ¬ (-n + ((j : ℕ) : ℤ) = 0) := by omega
      have h3 : ¬ (((j : ℕ) : ℤ) - n = 0) := by omega
      simp only [if_neg h, if_neg h3, map_smul, LinearMap.smul_apply, pair_h, if_neg h1, neg_sub,
        neg_add_eq_sub, map_sub, smul_eq_mul, map_zero, LinearMap.zero_apply, sub_zero]
      push_cast
      ring

omit [Algebra ℚ R] in
theorem pair_one_one : pair (1 : MvPolynomial ℕ+ R) 1 = 1 := by
  rw [pair_one_left, map_one]

end Virasoro.TFock
