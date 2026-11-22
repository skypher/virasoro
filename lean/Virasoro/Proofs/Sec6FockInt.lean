import Virasoro.Proofs.Sec6FockGram
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Integrality of `B_M`, `ρ_M` (paper.tex l.1232–1235, l.1268–1269)

`B_M(q₀,α) ∈ Mat(ℤ[1/2][q₀,α])`: every entry lies in each subring of the coefficient ring that
contains `1/2`, `q₀` and `α`.  "Since `6 ∣ (m³−m)` and `c/2 ∈ ℤ[1/2][t,t⁻¹]`", the entries of
`ρ_M` lie in each subring containing `1/2`, `c`, `Δ` and `d`.
-/

namespace Virasoro.TFock

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The polynomials all of whose coefficients lie in the subring `S`. -/
def cring (S : Subring R) : Subring (MvPolynomial ℕ+ R) where
  carrier := {f | ∀ e, coeff e f ∈ S}
  mul_mem' := by
    intro f g hf hg e
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => S.mul_mem (hf _) (hg _)
  one_mem' := by
    intro e
    rw [coeff_one]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  add_mem' := by
    intro f g hf hg e
    rw [coeff_add]
    exact S.add_mem (hf e) (hg e)
  zero_mem' := by
    intro e
    rw [coeff_zero]
    exact S.zero_mem
  neg_mem' := by
    intro f hf e
    rw [coeff_neg]
    exact S.neg_mem (hf e)

theorem mem_cring {S : Subring R} {f : MvPolynomial ℕ+ R} :
    f ∈ cring S ↔ ∀ e, coeff e f ∈ S := Iff.rfl

theorem X_mem_cring (S : Subring R) (i : ℕ+) : (X i : MvPolynomial ℕ+ R) ∈ cring S := by
  intro e
  rw [coeff_X']
  split_ifs
  exacts [S.one_mem, S.zero_mem]

theorem monomial_mem_cring (S : Subring R) (e : ℕ+ →₀ ℕ) :
    (monomial e 1 : MvPolynomial ℕ+ R) ∈ cring S := by
  intro e'
  rw [coeff_monomial]
  split_ifs
  exacts [S.one_mem, S.zero_mem]

theorem smul_mem_cring {S : Subring R} {a : R} (ha : a ∈ S) {f : MvPolynomial ℕ+ R}
    (hf : f ∈ cring S) : a • f ∈ cring S := by
  intro e
  rw [coeff_smul]
  exact S.mul_mem ha (hf e)

theorem deriv_monomial_mem (S : Subring R)
    (D : Derivation R (MvPolynomial ℕ+ R) (MvPolynomial ℕ+ R))
    (hD : ∀ i, D (X i) ∈ cring S) (e : ℕ+ →₀ ℕ) : D (monomial e 1) ∈ cring S := by
  induction e using Finsupp.induction with
  | zero =>
    have : (monomial 0 1 : MvPolynomial ℕ+ R) = 1 := rfl
    rw [this, Derivation.map_one_eq_zero]
    exact (cring S).zero_mem
  | single_add a b f _ _ ih =>
    have h1 : (monomial (Finsupp.single a b + f) 1 : MvPolynomial ℕ+ R) =
        X a ^ b * monomial f 1 := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [h1, Derivation.leibniz, Derivation.leibniz_pow]
    refine (cring S).add_mem ?_ ?_
    · exact (cring S).mul_mem ((cring S).pow_mem (X_mem_cring S a) b) ih
    · refine (cring S).mul_mem (monomial_mem_cring S f) ?_
      exact (cring S).nsmul_mem
        ((cring S).mul_mem ((cring S).pow_mem (X_mem_cring S a) _) (hD a)) b

/-- A derivation whose values on the variables have coefficients in `S` preserves the
polynomials with coefficients in `S`. -/
theorem deriv_mem (S : Subring R) (D : Derivation R (MvPolynomial ℕ+ R) (MvPolynomial ℕ+ R))
    (hD : ∀ i, D (X i) ∈ cring S) {f : MvPolynomial ℕ+ R} (hf : f ∈ cring S) :
    D f ∈ cring S := by
  rw [← support_sum_monomial_coeff f, map_sum]
  refine (cring S).sum_mem fun e _ => ?_
  have : (monomial e (coeff e f) : MvPolynomial ℕ+ R) = coeff e f • monomial e 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, Derivation.map_smul]
  exact smul_mem_cring (hf e) (deriv_monomial_mem S D hD e)

theorem hOp_mem {S : Subring R} {al : R} (hal : al ∈ S) (n : ℤ) {f : MvPolynomial ℕ+ R}
    (hf : f ∈ cring S) : hOp al n f ∈ cring S := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [hOp_neg al h]
    exact (cring S).mul_mem (X_mem_cring S _) hf
  · subst h
    rw [hOp_zero]
    exact smul_mem_cring hal hf
  · rw [hOp_pos al h]
    refine smul_mem_cring (intCast_mem S n) (deriv_mem S _ (fun i => ?_) hf)
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    exacts [(cring S).one_mem, (cring S).zero_mem]

theorem dOp_mem (S : Subring R) (n : ℤ) {f : MvPolynomial ℕ+ R} (hf : f ∈ cring S) :
    dOp n f ∈ cring S := by
  refine deriv_mem S _ (fun i => ?_) hf
  rw [dOp, mkDerivation_X]
  split_ifs
  · exact smul_mem_cring (natCast_mem S _) (X_mem_cring S _)
  · exact (cring S).zero_mem

variable [Algebra ℚ R]

theorem LOp_mem {S : Subring R} (hh : half R ∈ S) {al q : R} (hal : al ∈ S) (hq : q ∈ S)
    (n : ℤ) {f : MvPolynomial ℕ+ R} (hf : f ∈ cring S) : LOp al q n f ∈ cring S := by
  rw [LOp_apply]
  refine (cring S).add_mem ((cring S).add_mem (dOp_mem S n hf) ?_) (smul_mem_cring hh ?_)
  · unfold zOp
    split_ifs
    · exact smul_mem_cring
        (S.sub_mem (S.mul_mem hh (S.pow_mem hal 2)) (S.mul_mem hq hal)) hf
    · exact smul_mem_cring
        (S.sub_mem hal (S.mul_mem hq (S.add_mem (intCast_mem S n) S.one_mem)))
        (hOp_mem hal n hf)
  · rw [qOp_apply]
    exact (cring S).sum_mem fun k _ => hOp_mem hal k (hOp_mem hal _ hf)

theorem wordF_mem {S : Subring R} (hh : half R ∈ S) {al q : R} (hal : al ∈ S) (hq : q ∈ S) :
    ∀ w : List ℕ, wordF al q w ∈ cring S
  | [] => (cring S).one_mem
  | y :: w => LOp_mem hh hal hq _ (wordF_mem hh hal hq w)

/-- `B_M(q₀,α) ∈ Mat(ℤ[1/2][q₀,α])` (paper.tex l.1268–1269). -/
theorem Bm_mem {S : Subring R} (hh : half R ∈ S) {al q : R} (hal : al ∈ S) (hq : q ∈ S)
    {N : ℕ} (Y Z : Nat.Partition N) : Bm al q N Y Z ∈ S :=
  wordF_mem hh hal hq Y.word (expOf Z)

/-! ### `ρ_M` -/

theorem six_dvd (k : ℤ) : (6 : ℤ) ∣ k ^ 3 - k := by
  have hn : ∀ n : ℕ, (6 : ℤ) ∣ (n : ℤ) ^ 3 - n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨r, hr⟩ := Nat.even_mul_succ_self n
      obtain ⟨j, hj⟩ := ih
      refine ⟨j + r, ?_⟩
      have hr' : (n : ℤ) * (n + 1) = r + r := by exact_mod_cast hr
      push_cast
      linear_combination hj + 3 * hr'
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · exact hn n
  · obtain ⟨j, hj⟩ := hn n
    exact ⟨-j, by linear_combination -hj⟩

theorem centralTerm_mem {S : Subring R} (hh : half R ∈ S) {c : R} (hc : c ∈ S) (k : ℤ) :
    centralTerm c k ∈ S := by
  obtain ⟨j, hj⟩ := six_dvd k
  have h1 : algebraMap ℚ R (((k ^ 3 - k : ℤ) : ℚ) / 12) = (j : R) * half R := by
    unfold half
    rw [← map_intCast (algebraMap ℚ R) j, ← map_mul, hj]
    congr 1
    push_cast
    ring
  unfold centralTerm
  rw [h1]
  exact S.mul_mem (S.mul_mem (intCast_mem S j) hh) hc

theorem actWord_mem {S : Subring R} (hh : half R ∈ S) {c h : R} (hc : c ∈ S) (hh' : h ∈ S) :
    ∀ (w : List ℕ) (k : ℤ), ∀ t ∈ actWord c h k w, t.2 ∈ S
  | [], k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht
    · rw [List.mem_singleton] at ht
      rw [ht]
      exact S.one_mem
    · rw [List.mem_singleton] at ht
      rw [ht]
      exact hh'
    · simp at ht
  | y :: w, k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2 h3
    · rw [List.mem_singleton] at ht
      rw [ht]
      exact S.one_mem
    · rw [List.mem_singleton] at ht
      rw [ht]
      exact S.add_mem hh' (natCast_mem S _)
    · rw [List.mem_append, List.mem_append, List.mem_map, List.mem_map] at ht
      rcases ht with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ht
      · exact actWord_mem hh hc hh' w k u hu
      · exact S.mul_mem (intCast_mem S _) (actWord_mem hh hc hh' w (k - y) u hu)
      · rw [List.mem_singleton] at ht
        rw [ht]
        exact centralTerm_mem hh hc k
    · rw [List.append_nil, List.mem_append, List.mem_map, List.mem_map] at ht
      rcases ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact actWord_mem hh hc hh' w k u hu
      · exact S.mul_mem (intCast_mem S _) (actWord_mem hh hc hh' w (k - y) u hu)

omit [Algebra ℚ R] in
theorem phi_mem {S : Subring R} {d : R} (hd : d ∈ S) : ∀ w : List ℕ, phi d w ∈ S
  | [] => S.one_mem
  | m :: w => by
    unfold phi
    exact S.mul_mem (S.add_mem (natCast_mem S _) (S.mul_mem (natCast_mem S _) hd)) (phi_mem hd w)

/-- The entries of `ρ_M` lie in every subring containing `1/2`, `c`, `Δ`, `d`
(paper.tex l.1232–1235). -/
theorem torusWord_mem {S : Subring R} (hh : half R ∈ S) {c h d : R} (hc : c ∈ S) (hh' : h ∈ S)
    (hd : d ∈ S) : ∀ (Y w : List ℕ), torusWord c h d Y w ∈ S
  | [], w => by
    unfold torusWord
    exact phi_mem hd w
  | y :: Y, w => by
    unfold torusWord
    refine S.add_mem (Subring.list_sum_mem _ fun x hx => ?_) (S.mul_mem ?_ (torusWord_mem hh hc hh' hd Y w))
    · rw [List.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact S.mul_mem (actWord_mem hh hc hh' w _ t ht) (torusWord_mem hh hc hh' hd Y t.1)
    · exact S.add_mem (S.sub_mem (natCast_mem S _) (natCast_mem S _))
        (S.mul_mem (natCast_mem S _) hd)

end Virasoro.TFock
