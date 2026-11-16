import Virasoro.Proofs.PartEnum
import Virasoro.Proofs.PBWBasis
import Virasoro.Proofs.Levels
import Virasoro.Proofs.Specialize
import Virasoro.Proofs.ResidueCore1

/-!
# Explicit vectors: coordinates, forms and singular vectors

A list `s` of (word, coefficient) pairs whose words are partition words of level `N` has
coordinates `St.coords N s`.  The Shapovalov and torus forms of two such vectors are finite sums
of normal-ordered matrix elements of their words, and the vector is singular as soon as the
modes `L_1, …, L_N` annihilate it.
-/

namespace Virasoro

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- All words of `s` are partition words of level `N`. -/
def IsLevelSt (N : ℕ) (s : St R) : Prop :=
  ∀ t ∈ s, PosWord t.1 ∧ t.1.sum = N ∧ t.1.Pairwise (· ≥ ·)

omit [Algebra ℚ R] in
theorem coords_nil (N : ℕ) (Y : Nat.Partition N) : St.coords N ([] : St R) Y = 0 := rfl

omit [Algebra ℚ R] in
theorem coords_cons (N : ℕ) (t : List ℕ × R) (s : St R) (Y : Nat.Partition N) :
    St.coords N (t :: s) Y = (if t.1 = Y.word then t.2 else 0) + St.coords N s Y := by
  unfold St.coords
  by_cases h : t.1 = Y.word
  · simp [h]
  · simp [h]

omit [Algebra ℚ R] in
/-- Sums against the coordinates of an explicit vector. -/
theorem sum_coords_smul {M : Type*} [AddCommGroup M] [Module R M] {N : ℕ} (s : St R)
    (hs : IsLevelSt N s) (f : List ℕ → M) :
    ∑ Y : Nat.Partition N, St.coords N s Y • f Y.word = (s.map fun t => t.2 • f t.1).sum := by
  classical
  induction s with
  | nil => simp [coords_nil]
  | cons t s ih =>
    obtain ⟨hp, hsum, hsort⟩ := hs t (List.mem_cons_self)
    have ih' := ih fun u hu => hs u (List.mem_cons_of_mem _ hu)
    simp only [coords_cons, add_smul, Finset.sum_add_distrib, ih', List.map_cons, List.sum_cons]
    congr 1
    rw [Finset.sum_eq_single (partOf t.1 hp hsum)]
    · rw [partOf_word hp hsum hsort, if_pos rfl]
    · intro Y _ hY
      rw [if_neg, zero_smul]
      intro h
      apply hY
      apply Nat.Partition.ext
      rw [← Verma.word_coe, ← h]
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h

omit [Algebra ℚ R] in
theorem sum_coords_mul {N : ℕ} (s : St R) (hs : IsLevelSt N s) (f : List ℕ → R) :
    ∑ Y : Nat.Partition N, St.coords N s Y * f Y.word = (s.map fun t => t.2 * f t.1).sum := by
  have := sum_coords_smul (M := R) s hs f
  simpa [smul_eq_mul] using this

/-- The Shapovalov form of two explicit vectors. -/
theorem gramForm_coords (c h : R) {N : ℕ} (s s' : St R) (hs : IsLevelSt N s)
    (hs' : IsLevelSt N s') :
    gramForm c h N (St.coords N s) (St.coords N s')
      = (s.map fun t => t.2 * (s'.map fun t' => t'.2 * gramWord c h t.1 t'.1).sum).sum := by
  unfold gramForm
  simp only [dotProduct, Matrix.mulVec, gram, Matrix.of_apply]
  rw [← sum_coords_mul s hs fun w => (s'.map fun t' => t'.2 * gramWord c h w t'.1).sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [← sum_coords_mul s' hs' fun w' => gramWord c h Y.word w']
  congr 1
  exact Finset.sum_congr rfl fun Y' _ => mul_comm _ _

/-- The torus form of two explicit vectors. -/
theorem torusForm_coords (c h d : R) {N : ℕ} (s s' : St R) (hs : IsLevelSt N s)
    (hs' : IsLevelSt N s') :
    torusForm c h d N (St.coords N s) (St.coords N s')
      = (s.map fun t => t.2 * (s'.map fun t' => t'.2 * torusWord c h d t.1 t'.1).sum).sum := by
  unfold torusForm
  simp only [dotProduct, Matrix.mulVec, torus, Matrix.of_apply]
  rw [← sum_coords_mul s hs fun w => (s'.map fun t' => t'.2 * torusWord c h d w t'.1).sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [← sum_coords_mul s' hs' fun w' => torusWord c h d Y.word w']
  congr 1
  exact Finset.sum_congr rfl fun Y' _ => mul_comm _ _

/-- An explicit vector in Poincaré–Birkhoff–Witt coordinates. -/
theorem toVerma_eq_pbwCoord {c h : R} {N : ℕ} (s : St R) (hs : IsLevelSt N s) :
    St.toVerma (c := c) (h := h) s = Verma.pbwCoord N (St.coords N s) := by
  rw [Verma.pbwCoord_apply, sum_coords_smul s hs fun w => Verma.neg (c := c) (h := h) w]
  rfl

/-- An explicit vector of level `N` is singular if its coordinates are not all zero and the
modes `L_1, …, L_N` annihilate it. -/
theorem isSingular_of_actSt {c h : R} {N : ℕ} (s : St R) (hs : IsLevelSt N s)
    (hne : St.coords N s ≠ 0)
    (hL : ∀ n : ℕ, 1 ≤ n → n ≤ N → St.toVerma (c := c) (h := h) (actSt c h (n : ℤ) s) = 0) :
    Verma.IsSingular (St.toVerma (c := c) (h := h) s) N := by
  have hlev : St.toVerma (c := c) (h := h) s ∈ Verma.level N :=
    Verma.toVerma_mem_level (fun t ht => (hs t ht).1) fun t ht => (hs t ht).2.1
  refine ⟨?_, Verma.L_zero_of_mem_level hlev, fun n hn => ?_⟩
  · rw [toVerma_eq_pbwCoord s hs]
    intro h0
    exact hne (Verma.pbwCoord_injective N (h0.trans (map_zero _).symm))
  · by_cases hnN : (N : ℤ) < n
    · exact Verma.L_eq_zero_of_level hnN hlev
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      rw [← St.toVerma_actSt]
      exact hL m (by omega) (by omega)

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- A Shapovalov form with polynomial dependence on the weight is determined by its values. -/
theorem gramForm_poly_eq [Infinite K] {c : K} {N : ℕ} {u v : Nat.Partition N → K} {Q : K[X]}
    (h : ∀ x : K, gramForm c x N u v = Q.eval x) :
    gramForm (C c) (X : K[X]) N (fun Y => C (u Y)) (fun Y => C (v Y)) = Q := by
  refine Polynomial.funext fun x => ?_
  have := map_gramForm (Polynomial.evalRingHom x) (C c) (X : K[X]) N
    (fun Y => C (u Y)) (fun Y => C (v Y))
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  rw [this, h x]

/-- A torus form with polynomial dependence on the external weight is determined by its
values. -/
theorem torusForm_poly_eq [Infinite K] {c h : K} {N : ℕ} {u v : Nat.Partition N → K}
    {Q : K[X]} (hd : ∀ d : K, torusForm c h d N u v = Q.eval d) :
    torusForm (C c) (C h) (X : K[X]) N (fun Y => C (u Y)) (fun Y => C (v Y)) = Q := by
  refine Polynomial.funext fun x => ?_
  have := map_torusForm (Polynomial.evalRingHom x) (C c) (C h) (X : K[X]) N
    (fun Y => C (u Y)) (fun Y => C (v Y))
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  rw [this, hd x]

/-- The first crossing form of the local Shapovalov matrix as a derivative. -/
theorem cross1_gramLocal_eq [Infinite K] {c h₀ : K} {N : ℕ} {u v : Nat.Partition N → K}
    {Q : K[X]} (h : ∀ x : K, gramForm c x N u v = Q.eval x) :
    cross1 (gramLocal c h₀ N) u v = (derivative Q).eval h₀ := by
  rw [← dAt_gramForm, gramForm_poly_eq h]
  rfl

/-- The crossing scalar as a derivative. -/
theorem crossScalar_eq [Infinite K] {c h₀ : K} {N : ℕ} {p : Nat.Partition N → K} {Q : K[X]}
    (h : ∀ x : K, gramForm c x N p p = Q.eval x) :
    crossScalar c h₀ p = (derivative Q).eval h₀ := by
  unfold crossScalar
  rw [gramForm_poly_eq h]

end Field

end Virasoro
