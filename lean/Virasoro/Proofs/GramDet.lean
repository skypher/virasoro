import Virasoro.Proofs.GramDegree
import Virasoro.Jantzen
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.PowerSeries.Order

/-!
# The Shapovalov determinant is a nonzero polynomial in the internal weight
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- The top coefficient of a product of polynomials with prescribed degree bounds. -/
theorem coeff_prod_top {ι : Type*} (s : Finset ι) (f : ι → 𝔽[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hfa := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨natDegree_mul_le_of_le hfa hs.1,
      by rw [coeff_mul_add_eq_of_natDegree_le hfa hs.1, hs.2]⟩

/-- Leading coefficient of a determinant whose entries have degree at most `min(a i, a j)`, and
whose off-diagonal entries with `a i = a j` have vanishing coefficient of `X^{a i}`. -/
theorem det_coeff_top {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι 𝔽[X]) (a : ι → ℕ)
    (h1 : ∀ i j, (M i j).natDegree ≤ min (a i) (a j))
    (h2 : ∀ i j, i ≠ j → a i = a j → (M i j).coeff (a i) = 0) :
    M.det.coeff (∑ i, a i) = ∏ i, (M i i).coeff (a i) := by
  rw [Matrix.det_apply', finsetSum_coeff]
  have hprod : ∀ σ : Equiv.Perm ι,
      (∏ i, M (σ i) i).coeff (∑ i, a i) = ∏ i, (M (σ i) i).coeff (a i) := fun σ =>
    (coeff_prod_top Finset.univ (fun i => M (σ i) i) a
      fun i _ => le_trans (h1 (σ i) i) (min_le_right _ _)).2
  rw [Finset.sum_eq_single 1]
  · rw [Equiv.Perm.sign_one]
    simp only [Units.val_one, Int.cast_one, one_mul]
    exact hprod 1
  · intro σ _ hσ
    rw [← C_eq_intCast, coeff_C_mul, hprod σ]
    have hex : ∃ i, (M (σ i) i).coeff (a i) = 0 := by
      by_cases hall : ∀ i, a i ≤ a (σ i)
      · have hsum : ∑ i, a i = ∑ i, a (σ i) := (Equiv.sum_comp σ a).symm
        have heq : ∀ i, a i = a (σ i) := by
          have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun i _ => hall i).1 hsum
          exact fun i => this i (Finset.mem_univ i)
        obtain ⟨i₀, hi₀⟩ : ∃ i, σ i ≠ i := by
          by_contra hcon
          push Not at hcon
          exact hσ (Equiv.ext hcon)
        refine ⟨i₀, ?_⟩
        rw [heq i₀]
        exact h2 (σ i₀) i₀ hi₀ (heq i₀).symm
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        refine ⟨i, coeff_eq_zero_of_natDegree_lt ?_⟩
        exact lt_of_le_of_lt (le_trans (h1 (σ i) i) (min_le_left _ _)) hi
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem word_pos {N : ℕ} (Y : Nat.Partition N) : ∀ y ∈ Y.word, 0 < y := by
  intro y hy
  rw [Nat.Partition.word, Multiset.mem_sort] at hy
  exact Y.parts_pos hy

theorem word_injective {N : ℕ} {Y Y' : Nat.Partition N} (h : List.Perm Y'.word Y.word) :
    Y' = Y := by
  apply Nat.Partition.ext
  have h1 : ((Y'.word : List ℕ) : Multiset ℕ) = (Y.word : Multiset ℕ) := Multiset.coe_eq_coe.2 h
  rwa [Nat.Partition.word, Nat.Partition.word, Multiset.sort_eq, Multiset.sort_eq] at h1

/-- The coefficient of `Δ^{∑ ℓ(Y)}` in `det G_N(c,Δ)` is nonzero. -/
theorem gramPoly_det_coeff_ne_zero (c : 𝔽) (N : ℕ) :
    (gramPoly c N).det.coeff (∑ Y : Nat.Partition N, Y.word.length) ≠ 0 := by
  rw [det_coeff_top (gramPoly c N) (fun Y => Y.word.length)]
  · rw [Finset.prod_ne_zero_iff]
    intro Y _
    have h := coeff_gramWord_top c Y.word Y.word (word_pos Y) rfl
    simp only [gramPoly, gram, Matrix.of_apply]
    rw [h, topFun_eq_topNat]
    exact Nat.cast_ne_zero.mpr (topNat_self_pos Y.word (word_pos Y)).ne'
  · intro Y Y'
    exact natDegree_gramWord_le c Y.word Y'.word (word_pos Y)
  · intro Y Y' hne hlen
    have h := coeff_gramWord_top c Y.word Y'.word (word_pos Y) hlen
    simp only [gramPoly, gram, Matrix.of_apply]
    rw [h, topFun_eq_topNat, topNat_eq_zero_of_not_perm hlen, Nat.cast_zero]
    intro hperm
    exact hne (word_injective hperm).symm

/-- `det G_N(c,Δ)` is a nonzero polynomial in `Δ`. -/
theorem gramPoly_det_ne_zero (c : 𝔽) (N : ℕ) : (gramPoly c N).det ≠ 0 := by
  intro h
  have := gramPoly_det_coeff_ne_zero c N
  rw [h, coeff_zero] at this
  exact this rfl

/-- The substitution `Δ ↦ h + x` from polynomials to power series. -/
noncomputable def shiftPS (h : 𝔽) : 𝔽[X] →+* PowerSeries 𝔽 :=
  eval₂RingHom (PowerSeries.C) (PowerSeries.C h + PowerSeries.X)

theorem shiftPS_C (h a : 𝔽) : shiftPS h (C a) = PowerSeries.C a := by
  simp [shiftPS]

theorem shiftPS_X (h : 𝔽) : shiftPS h X = PowerSeries.C h + PowerSeries.X := by
  simp [shiftPS]

theorem constantCoeff_shiftPS (h : 𝔽) (p : 𝔽[X]) :
    PowerSeries.constantCoeff (shiftPS h p) = p.eval h := by
  have : (PowerSeries.constantCoeff (R := 𝔽)).comp (shiftPS h) = evalRingHom h := by
    apply ringHom_ext
    · intro a; simp [shiftPS_C]
    · simp [shiftPS_X]
  exact congrArg (fun f : 𝔽[X] →+* 𝔽 => f p) this

/-- The order at `x = 0` of `p(h + x)` is the multiplicity of the root `h` of `p`. -/
theorem order_shiftPS (h : 𝔽) {p : 𝔽[X]} (hp : p ≠ 0) :
    (shiftPS h p).order = (p.rootMultiplicity h : ℕ∞) := by
  obtain ⟨q, hq, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp h
  have hX : shiftPS h (X - C h) = PowerSeries.X := by
    rw [map_sub, shiftPS_X, shiftPS_C]; ring
  have hq0 : PowerSeries.constantCoeff (shiftPS h q) ≠ 0 := by
    rw [constantCoeff_shiftPS]
    intro h0
    exact hndvd (dvd_iff_isRoot.2 h0)
  have hunit : IsUnit (shiftPS h q) := PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hq0)
  conv_lhs => rw [hq]
  rw [map_mul, map_pow, hX, PowerSeries.order_mul, PowerSeries.order_X_pow,
    PowerSeries.order_zero_of_unit hunit, add_zero]

theorem shiftPS_ne_zero (h : 𝔽) {p : 𝔽[X]} (hp : p ≠ 0) : shiftPS h p ≠ 0 := by
  intro h0
  have := order_shiftPS h hp
  rw [h0, PowerSeries.order_zero] at this
  exact ENat.natCast_ne_top _ this.symm

theorem gramLocal_eq_map (c h : 𝔽) (N : ℕ) :
    gramLocal c h N = (gramPoly c N).map (shiftPS h) := by
  have := gram_map (shiftPS h) (C c) (X : 𝔽[X]) N
  rw [shiftPS_C, shiftPS_X] at this
  exact this

theorem gramLocal_det (c h : 𝔽) (N : ℕ) :
    (gramLocal c h N).det = shiftPS h (gramPoly c N).det := by
  rw [gramLocal_eq_map]
  exact (RingHom.map_det (shiftPS h) (gramPoly c N)).symm

/-- `det G_N(c, h + x)` is a nonzero power series. -/
theorem gramLocal_det_ne_zero (c h : 𝔽) (N : ℕ) : (gramLocal c h N).det ≠ 0 := by
  rw [gramLocal_det]
  exact shiftPS_ne_zero h (gramPoly_det_ne_zero c N)

/-- `ord_x det G_N(c, h + x)` is the multiplicity of the factor `Δ - h` in `det G_N(c,Δ)`. -/
theorem gramLocal_det_order (c h : 𝔽) (N : ℕ) :
    (gramLocal c h N).det.order = ((gramPoly c N).det.rootMultiplicity h : ℕ∞) := by
  rw [gramLocal_det]
  exact order_shiftPS h (gramPoly_det_ne_zero c N)

end Virasoro
