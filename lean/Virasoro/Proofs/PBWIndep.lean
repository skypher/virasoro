import Virasoro.Proofs.VermaFree
import Virasoro.Proofs.VermaSpan
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The Poincaré–Birkhoff–Witt vectors are linearly independent

The operators `G_m = x_m + ∑_k k x_{k+m} ∂_k` on the polynomial ring `R[x_1, x_2, …]` satisfy
`[G_m, G_n] = (n - m) G_{m+n}`, so by the freeness of the Verma module over `U(Vir_-)` there is
a linear map `Φ` from the Verma module with `Φ L_{-m} = G_m Φ` and `Φ|h⟩ = 1`.  The image of
`L_{-w₁} ⋯ L_{-w_r}|h⟩` is `x_{w₁} ⋯ x_{w_r}` plus terms of lower degree, which gives the linear
independence of the vectors `L_{-Y}|h⟩` over all partitions `Y`.
-/

namespace Virasoro

open MvPolynomial

section Poly

variable {R : Type*} [CommRing R]

/-- The derivation `D_m = ∑_k k x_{k+m} ∂_k`. -/
noncomputable def polyD (m : ℕ) : Derivation R (MvPolynomial ℕ R) (MvPolynomial ℕ R) :=
  mkDerivation R fun k => (k : R) • X (k + m)

theorem polyD_X (m k : ℕ) : polyD (R := R) m (X k) = (k : R) • X (k + m) :=
  mkDerivation_X _ _ _

theorem polyD_comm (m n : ℕ) (p : MvPolynomial ℕ R) :
    polyD m (polyD n p) - polyD n (polyD m p) = ((n : R) - (m : R)) • polyD (m + n) p := by
  have key : ⁅polyD (R := R) m, polyD (R := R) n⁆
      = ((n : R) - (m : R)) • polyD (R := R) (m + n) := by
    refine derivation_ext fun k => ?_
    rw [Derivation.commutator_apply, Derivation.smul_apply, polyD_X, polyD_X, polyD_X,
      Derivation.map_smul, Derivation.map_smul, polyD_X, polyD_X, show k + n + m = k + (m + n) by omega,
      show k + m + n = k + (m + n) by omega]
    push_cast
    module
  have := congrArg (fun D : Derivation R (MvPolynomial ℕ R) (MvPolynomial ℕ R) => D p) key
  simpa [Derivation.commutator_apply] using this

/-- The operator `G_m = x_m + D_m`. -/
noncomputable def polyG (m : ℕ) : Module.End R (MvPolynomial ℕ R) :=
  LinearMap.mulLeft R (X m) + (polyD (R := R) m).toLinearMap

theorem polyG_apply (m : ℕ) (p : MvPolynomial ℕ R) : polyG m p = X m * p + polyD m p := rfl

theorem polyG_comm (m n : ℕ) (p : MvPolynomial ℕ R) :
    polyG m (polyG n p) = polyG n (polyG m p) + ((n : R) - (m : R)) • polyG (m + n) p := by
  have h := polyD_comm m n p
  simp only [polyG_apply, map_add, Derivation.leibniz, polyD_X, smul_eq_mul,
    MvPolynomial.smul_eq_C_mul] at h ⊢
  rw [show n + m = m + n by omega]
  simp only [map_sub] at h ⊢
  linear_combination h

/-- Polynomials all of whose monomials have degree less than `r`. -/
def LowDeg (q : MvPolynomial ℕ R) (r : ℕ) : Prop := ∀ d : ℕ →₀ ℕ, coeff d q ≠ 0 → d.degree < r

theorem lowDeg_zero (r : ℕ) : LowDeg (0 : MvPolynomial ℕ R) r := by
  intro d hd
  simp at hd

theorem LowDeg.add {p q : MvPolynomial ℕ R} {r : ℕ} (hp : LowDeg p r) (hq : LowDeg q r) :
    LowDeg (p + q) r := by
  intro d hd
  rw [coeff_add] at hd
  by_cases h0 : coeff d p = 0
  · rw [h0, zero_add] at hd
    exact hq d hd
  · exact hp d h0

theorem LowDeg.mono {p : MvPolynomial ℕ R} {r r' : ℕ} (hp : LowDeg p r) (h : r ≤ r') :
    LowDeg p r' := fun d hd => lt_of_lt_of_le (hp d hd) h

theorem LowDeg.X_mul {q : MvPolynomial ℕ R} {r : ℕ} (hq : LowDeg q r) (y : ℕ) :
    LowDeg (X y * q) (r + 1) := by
  classical
  intro d hd
  rw [coeff_X_mul'] at hd
  split_ifs at hd with hy
  · have h1 := hq _ hd
    have hle : Finsupp.single y 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hy)
    have h2 : d = (d - Finsupp.single y 1) + Finsupp.single y 1 := (tsub_add_cancel_of_le hle).symm
    rw [h2, map_add, Finsupp.degree_single]
    omega
  · exact absurd rfl hd

theorem isHomogeneous_polyD_monomial (m : ℕ) (s : ℕ →₀ ℕ) (a : R) :
    IsHomogeneous (polyD m (monomial s a)) s.degree := by
  rw [polyD, mkDerivation_monomial]
  refine (homogeneousSubmodule ℕ R s.degree).smul_mem a ?_
  refine (homogeneousSubmodule ℕ R s.degree).sum_mem fun i hi => ?_
  have hle : Finsupp.single i 1 ≤ s := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
  have hdeg : (s - Finsupp.single i 1).degree + 1 = s.degree := by
    conv_rhs => rw [← tsub_add_cancel_of_le hle, map_add, Finsupp.degree_single]
  rw [mem_homogeneousSubmodule]
  show IsHomogeneous (monomial (s - Finsupp.single i 1) ((s i : ℕ) : R)
    • ((i : R) • (X (i + m) : MvPolynomial ℕ R))) s.degree
  rw [smul_eq_mul, ← hdeg]
  refine (isHomogeneous_monomial _ rfl).mul ?_
  exact (homogeneousSubmodule ℕ R 1).smul_mem _ (isHomogeneous_X R (i + m))

theorem LowDeg.deriv {q : MvPolynomial ℕ R} {r : ℕ} (hq : LowDeg q r) (m : ℕ) :
    LowDeg (polyD m q) r := by
  classical
  intro d hd
  have e : polyD m q = ∑ v ∈ q.support, polyD m (monomial v (coeff v q)) := by
    conv_lhs => rw [← support_sum_monomial_coeff q]
    rw [map_sum]
  rw [e, coeff_sum] at hd
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have hdv : d.degree = v.degree := by
    by_contra hcon
    exact hne ((isHomogeneous_polyD_monomial m v (coeff v q)).coeff_eq_zero hcon)
  rw [hdv]
  exact hq v (mem_support_iff.1 hv)

/-- The exponent vector of the monomial `x_{w₁} ⋯ x_{w_r}`. -/
noncomputable def wordExp (w : List ℕ) : ℕ →₀ ℕ := (w.map fun y => Finsupp.single y 1).sum

theorem wordExp_apply (w : List ℕ) (y : ℕ) : wordExp w y = w.count y := by
  induction w with
  | nil => simp [wordExp]
  | cons a w ih =>
    have e : wordExp (a :: w) = Finsupp.single a 1 + wordExp w := by simp [wordExp]
    rw [e, Finsupp.add_apply, ih, List.count_cons, Finsupp.single_apply]
    by_cases hay : a = y
    · simp [hay]; omega
    · simp [hay]

theorem wordExp_degree (w : List ℕ) : (wordExp w).degree = w.length := by
  induction w with
  | nil => simp [wordExp]
  | cons a w ih =>
    have e : wordExp (a :: w) = Finsupp.single a 1 + wordExp w := by simp [wordExp]
    rw [e, map_add, Finsupp.degree_single, ih, List.length_cons]
    omega

theorem wordExp_perm {w w' : List ℕ} (h : wordExp w = wordExp w') : w.Perm w' := by
  rw [List.perm_iff_count]
  intro y
  rw [← wordExp_apply, ← wordExp_apply, h]

/-- The monomial `x_{w₁} ⋯ x_{w_r}`. -/
theorem wordMon_eq (w : List ℕ) :
    (w.map (X : ℕ → MvPolynomial ℕ R)).prod = monomial (wordExp w) 1 := by
  induction w with
  | nil => simp [wordExp]
  | cons a w ih =>
    have e : wordExp (a :: w) = Finsupp.single a 1 + wordExp w := by simp [wordExp]
    rw [List.map_cons, List.prod_cons, ih, e, X, monomial_mul, one_mul]

end Poly

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

omit [Algebra ℚ R] in
theorem polyG_rep (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    (polyG (R := R) m.toNat) * polyG n.toNat
      = polyG n.toNat * polyG m.toNat + ((n - m : ℤ) : R) • polyG (m + n).toNat := by
  refine LinearMap.ext fun p => ?_
  rw [Module.End.mul_apply, polyG_comm, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, show (m + n).toNat = m.toNat + n.toNat by omega]
  congr 2
  have h1 : ((n.toNat : ℕ) : R) = ((n : ℤ) : R) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn.le]
  have h2 : ((m.toNat : ℕ) : R) = ((m : ℤ) : R) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm.le]
  rw [h1, h2]
  push_cast
  rfl

variable (c h)

/-- The polynomial realization `Φ` of the Verma module: `Φ|h⟩ = 1`, `Φ L_{-m} = G_m Φ`. -/
noncomputable def polyMap : Verma R c h →ₗ[R] MvPolynomial ℕ R :=
  Classical.choose (exists_negHom (c := c) (h := h) (fun m : ℤ => polyG (R := R) m.toNat)
    polyG_rep (1 : MvPolynomial ℕ R))

variable {c h}

theorem polyMap_hw : polyMap c h hw = 1 :=
  (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => polyG (R := R) m.toNat) polyG_rep (1 : MvPolynomial ℕ R))).1

theorem polyMap_neg_cons (y : ℕ) (hy : 0 < y) (w : List ℕ) :
    polyMap c h (neg (y :: w)) = polyG y (polyMap c h (neg w)) := by
  have := (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => polyG (R := R) m.toNat) polyG_rep (1 : MvPolynomial ℕ R))).2 (y : ℤ)
      (by exact_mod_cast hy) (neg w)
  rw [neg_cons, polyMap, this]
  simp

/-- `Φ(L_{-w}|h⟩) = x_{w₁} ⋯ x_{w_r} + (terms of degree < r)`. -/
theorem polyMap_neg (w : List ℕ) (hw : PosWord w) :
    ∃ q : MvPolynomial ℕ R, polyMap c h (neg w) = monomial (wordExp w) 1 + q ∧
      LowDeg q w.length := by
  induction w with
  | nil =>
    refine ⟨0, ?_, lowDeg_zero _⟩
    rw [neg_nil, polyMap_hw, add_zero]
    simp [wordExp]
  | cons y w ih =>
    have hy : 0 < y := hw y List.mem_cons_self
    obtain ⟨q, hq, hlow⟩ := ih fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have hmon : LowDeg (monomial (wordExp w) (1 : R)) (w.length + 1) := by
      classical
      intro d hd
      rw [coeff_monomial] at hd
      split_ifs at hd with he
      · rw [← he, wordExp_degree]
        omega
      · exact absurd rfl hd
    refine ⟨X y * q + polyD y (monomial (wordExp w) 1) + polyD y q, ?_, ?_⟩
    · rw [polyMap_neg_cons y hy, hq, polyG_apply, map_add, ← wordMon_eq, ← wordMon_eq,
        List.map_cons, List.prod_cons]
      ring
    · rw [List.length_cons]
      exact ((hlow.X_mul y).add (hmon.deriv y)).add ((hlow.deriv y).mono (Nat.le_succ _))

theorem word_coe {N : ℕ} (Y : Nat.Partition N) : ((Y.word : List ℕ) : Multiset ℕ) = Y.parts := by
  rw [Nat.Partition.word, Multiset.sort_eq]

theorem posWord_word {N : ℕ} (Y : Nat.Partition N) : PosWord Y.word := by
  intro y hy
  have : y ∈ ((Y.word : List ℕ) : Multiset ℕ) := Multiset.mem_coe.2 hy
  rw [word_coe] at this
  exact Y.parts_pos this

theorem sigma_eq_of_word_perm {Y Y' : Σ N : ℕ, Nat.Partition N}
    (hp : Y.2.word.Perm Y'.2.word) : Y = Y' := by
  obtain ⟨N, Y⟩ := Y
  obtain ⟨N', Y'⟩ := Y'
  have hparts : Y.parts = Y'.parts := by
    rw [← word_coe, ← word_coe]
    exact Multiset.coe_eq_coe.2 hp
  have hN : N = N' := by rw [← Y.parts_sum, ← Y'.parts_sum, hparts]
  subst hN
  rw [Nat.Partition.ext hparts]

/-- The images under `Φ` of the vectors `L_{-Y}|h⟩`, over all partitions `Y`, are linearly
independent. -/
theorem polyMap_neg_word_linearIndependent :
    LinearIndependent R
      (fun Y : (Σ N : ℕ, Nat.Partition N) => polyMap c h (neg (c := c) (h := h) Y.2.word)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁, hg₁⟩ := hcon
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (s.filter fun i => g i ≠ 0)
    (fun i => i.2.word.length) ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hg₁⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.1 hi₀).1
  have hg₀ : g i₀ ≠ 0 := (Finset.mem_filter.1 hi₀).2
  have h1 := congrArg (fun p => coeff (wordExp i₀.2.word) p) hsum
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_zero] at h1
  rw [Finset.sum_eq_single i₀] at h1
  · obtain ⟨q, hq, hlow⟩ := polyMap_neg (c := c) (h := h) i₀.2.word (posWord_word i₀.2)
    rw [hq, coeff_add, coeff_monomial, if_pos rfl] at h1
    have hq0 : coeff (wordExp i₀.2.word) q = 0 := by
      by_contra hne
      have := hlow _ hne
      rw [wordExp_degree] at this
      omega
    rw [hq0, add_zero, mul_one] at h1
    exact hg₀ h1
  · intro i hi hne
    by_cases hgi : g i = 0
    · rw [hgi, zero_mul]
    · have hlen : i.2.word.length ≤ i₀.2.word.length :=
        hmax i (Finset.mem_filter.2 ⟨hi, hgi⟩)
      obtain ⟨q, hq, hlow⟩ := polyMap_neg (c := c) (h := h) i.2.word (posWord_word i.2)
      rw [hq, coeff_add, coeff_monomial]
      have hexp : ¬ wordExp i.2.word = wordExp i₀.2.word :=
        fun he => hne (sigma_eq_of_word_perm (wordExp_perm he))
      have hq0 : coeff (wordExp i₀.2.word) q = 0 := by
        by_contra hne'
        have := hlow _ hne'
        rw [wordExp_degree] at this
        omega
      rw [if_neg hexp, hq0, add_zero, mul_zero]
  · intro hni
    exact absurd hi₀s hni

/-- The vectors `L_{-Y}|h⟩`, over all partitions `Y` of all integers, are linearly
independent. -/
theorem neg_word_linearIndependent :
    LinearIndependent R
      (fun Y : (Σ N : ℕ, Nat.Partition N) => neg (c := c) (h := h) Y.2.word) :=
  LinearIndependent.of_comp (polyMap c h) polyMap_neg_word_linearIndependent

theorem polyMap_L_neg {m : ℤ} (hm : 0 < m) (v : Verma R c h) :
    polyMap c h (L (-m) v) = polyG m.toNat (polyMap c h v) :=
  (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => polyG (R := R) m.toNat) polyG_rep (1 : MvPolynomial ℕ R))).2 m hm v

end Verma

omit [Algebra ℚ R] in
/-- The operator `G_y` is injective: the monomials of top degree of `G_y q` are `x_y` times
those of `q`. -/
theorem polyG_injective (y : ℕ) : Function.Injective (polyG (R := R) y) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hne
  have hsupp : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image q.support (fun d => d.degree) hsupp
  have hlow : LowDeg q (d.degree + 1) := by
    intro d' hd'
    have := hmax d' (MvPolynomial.mem_support_iff.2 hd')
    omega
  have h1 := congrArg (coeff (Finsupp.single y 1 + d)) hq
  rw [polyG_apply, coeff_add, coeff_X_mul, coeff_zero] at h1
  have h2 : coeff (Finsupp.single y 1 + d) (polyD y q) = 0 := by
    by_contra hcon
    have := hlow.deriv y _ hcon
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [h2, add_zero] at h1
  exact (MvPolynomial.mem_support_iff.1 hd) h1

end Virasoro
