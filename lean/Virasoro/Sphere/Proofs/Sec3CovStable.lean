import Virasoro.Sphere.Proofs.Sec3CovAlg
import Virasoro.Sphere.Proofs.Sec3GaussSaddleCov
import Virasoro.Sphere.Proofs.Sec3GaussExpect
import Virasoro.Sphere.Proofs.Sec3SaddlePde2

/-!
# The Neumann covariance: symmetry, stabilization, block form (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.652–675.  The covariance of the perturbed Gaussian is the finite Neumann sum
`covN = (∑_r N^r) C₀`.  Proved here: it is symmetric; modulo `z^{k+1}` only the modes `≤ k`
contribute and the entries do not depend on the number of modes (row `m` of `M(z)` is `O(z^m)`,
`Cov(U_m, ·) = O(z^m)`, `Cov(V_m, ·) = O(z^m)`); and in `ℂ[[z]]/(z^{k+1})` its blocks are the
reductions of `covUU`, `covUV`, `covVV` (the Neumann block inverse of l.656–661).
-/

namespace Virasoro.Sphere

open Finset Matrix

section Nat

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

theorem map_MR (ψ : R →+* S) (φ : PowerSeries ℚ →+* R) (n : ℕ) :
    (MR n φ).map ψ = MR n (ψ.comp φ) := by
  rw [MR, MR, Matrix.map_map]
  rfl

theorem map_ER (ψ : R →+* S) (φ : PowerSeries ℚ →+* R) (n : ℕ) :
    (ER n φ).map ψ = ER n (ψ.comp φ) := by
  rw [ER, ER, Matrix.diagonal_map (map_zero ψ)]
  congr 1
  funext i
  rw [map_mul, map_pow, map_algebraMap_rat, RingHom.comp_apply]

theorem map_NR (ψ : R →+* S) (φ : PowerSeries ℚ →+* R) (n : ℕ) :
    ψ.mapMatrix (NR n φ) = NR n (ψ.comp φ) := by
  rw [RingHom.mapMatrix_apply, NR, NR, Matrix.fromBlocks_map, map_MR]
  simp

theorem map_C0 (ψ : R →+* S) (φ : PowerSeries ℚ →+* R) (n : ℕ) :
    ψ.mapMatrix (Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 : Matrix (Modes n) (Modes n) R) =
      Matrix.fromBlocks 0 (ER n (ψ.comp φ)) (ER n (ψ.comp φ)) 0 := by
  rw [RingHom.mapMatrix_apply, Matrix.fromBlocks_map, map_ER]
  simp

/-- The Neumann covariance commutes with changes of the ring. -/
theorem map_covN (ψ : R →+* S) (φ : PowerSeries ℚ →+* R) (n K : ℕ) (a b : Modes n) :
    ψ (covN n φ K a b) = covN n (ψ.comp φ) K a b := by
  have h : ψ.mapMatrix (covN n φ K) = covN n (ψ.comp φ) K := by
    rw [covN, covN, map_mul, map_sum, map_C0]
    simp only [map_pow, map_NR]
  rw [← h]
  rfl

end Nat

section Symm

variable {R : Type*} [CommRing R] [Algebra ℚ R] (φ : PowerSeries ℚ →+* R) (n K : ℕ)

theorem MR_mul_ER : MR n φ * ER n φ = ER n φ * (MR n φ)ᵀ := by
  ext i j
  rw [ER, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, MR_apply, MR_apply,
    Bcoef_symm ((j : ℕ) + 1) ((i : ℕ) + 1)]
  have h : algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((i : ℕ) + 1 : ℕ) : ℚ)) *
        algebraMap ℚ R (1 / (2 * (((j : ℕ) + 1 : ℕ) : ℚ))) =
      algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) *
        algebraMap ℚ R (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1) / (((j : ℕ) + 1 : ℕ) : ℚ)) := by
    rw [← map_mul, ← map_mul]
    congr 1
    have h1 : ((((i : ℕ) + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    have h2 : ((((j : ℕ) + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    field_simp
  linear_combination (φ PowerSeries.X ^ ((i : ℕ) + 1) * φ PowerSeries.X ^ ((j : ℕ) + 1)) * h

/-- The Neumann covariance is symmetric. -/
theorem covN_symm (a b : Modes n) : covN n φ K a b = covN n φ K b a := by
  have h1 : NR n φ * Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 =
      Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 * (NR n φ)ᵀ := by
    rw [NR, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.transpose_zero,
      MR_mul_ER]
  have h2 : ∀ r : ℕ, NR n φ ^ r * Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 =
      Matrix.fromBlocks 0 (ER n φ) (ER n φ) 0 * ((NR n φ)ᵀ) ^ r := by
    intro r
    induction r with
    | zero => rw [pow_zero, pow_zero, one_mul, mul_one]
    | succ r ih => rw [pow_succ, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        ← pow_succ]
  have h3 : (covN n φ K)ᵀ = covN n φ K := by
    rw [covN, Matrix.transpose_mul, Matrix.transpose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.transpose_pow, h2, Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_zero, ER, Matrix.diagonal_transpose]
  exact congrFun (congrFun h3 b) a

end Symm

section Stable

variable {R : Type*} [CommRing R] [Algebra ℚ R] (φ : PowerSeries ℚ →+* R)

/-- The mode index of a variable. -/
def idxM {n : ℕ} : Modes n → ℕ := Sum.elim (fun i => (i : ℕ)) (fun i => (i : ℕ))

/-- `Cov(u_m, ū_m)` of `Q₀` as a function of the variable. -/
noncomputable def eeM {n : ℕ} : Modes n → R := Sum.elim (e0 φ) (e0 φ)

/-- The modes `≤ k` among the modes `≤ n`. -/
def embM {k n : ℕ} (h : k ≤ n) : Modes k → Modes n := Sum.map (Fin.castLE h) (Fin.castLE h)

theorem embM_injective {k n : ℕ} (h : k ≤ n) : Function.Injective (embM h) :=
  Sum.map_injective.2 ⟨Fin.castLE_injective h, Fin.castLE_injective h⟩

theorem idxM_of_not_range {k n : ℕ} (h : k ≤ n) (c : Modes n) (hc : c ∉ Set.range (embM h)) :
    k ≤ idxM c := by
  by_contra hlt
  push Not at hlt
  refine hc ?_
  rcases c with i | i
  · exact ⟨Sum.inl ⟨(i : ℕ), hlt⟩, by simp [embM, Fin.ext_iff]⟩
  · exact ⟨Sum.inr ⟨(i : ℕ), hlt⟩, by simp [embM, Fin.ext_iff]⟩

theorem idxM_embM {k n : ℕ} (h : k ≤ n) (a : Modes k) : idxM (embM h a) = idxM a := by
  rcases a with i | i <;> rfl

theorem idxM_lt {k : ℕ} (a : Modes k) : idxM a < k := by
  rcases a with i | i <;> exact i.isLt

theorem idxM_swap {n : ℕ} (a : Modes n) : idxM (Sum.swap a) = idxM a := by
  rcases a with i | i <;> rfl

theorem swap_embM {k n : ℕ} (h : k ≤ n) (a : Modes k) :
    Sum.swap (embM h a) = embM h (Sum.swap a) := by
  rcases a with i | i <;> rfl

theorem eeM_embM {k n : ℕ} (h : k ≤ n) (a : Modes k) : eeM φ (embM h a) = eeM φ a := by
  rcases a with i | i <;> simp [eeM, embM, e0]

variable {φ}

theorem eeM_eq_zero {k n : ℕ} (hz : φ PowerSeries.X ^ (k + 1) = 0) (a : Modes n)
    (ha : k ≤ idxM a) : eeM φ a = 0 := by
  rcases a with i | i <;>
  · have ha' : k ≤ (i : ℕ) := ha
    simp only [eeM, Sum.elim_inl, Sum.elim_inr, e0]
    rw [pow_eq_zero_of_le (Nat.succ_le_succ ha') hz, mul_zero]

variable (φ)

/-- The entries of the Neumann covariance. -/
theorem covN_apply {n : ℕ} (K : ℕ) (a b : Modes n) :
    covN n φ K a b = (∑ r ∈ range (K + 1), NR n φ ^ r) a (Sum.swap b) * eeM φ b := by
  rw [covN, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases b with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, ER, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, eeM, Sum.elim_inl, e0, Sum.swap_inl]
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, ER, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, eeM, Sum.elim_inr, e0, Sum.swap_inr]

variable {φ}

theorem NR_row_zero {k n : ℕ} (hz : φ PowerSeries.X ^ (k + 1) = 0) (a c : Modes n)
    (ha : k ≤ idxM a) : NR n φ a c = 0 := by
  have hM : ∀ i j : Fin n, k ≤ (i : ℕ) → MR n φ i j = 0 := fun i j hi => by
    rw [MR_apply, pow_eq_zero_of_le (Nat.succ_le_succ hi) hz, mul_zero]
  rcases a with i | i <;> rcases c with j | j <;> simp [NR, hM _ _ ha]

theorem NR_pow_row_zero {k n : ℕ} (hz : φ PowerSeries.X ^ (k + 1) = 0) (a b : Modes n)
    (ha : k ≤ idxM a) (r : ℕ) : (NR n φ ^ (r + 1)) a b = 0 := by
  rw [pow_succ', Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => by rw [NR_row_zero hz a c ha, zero_mul]

variable (φ)

theorem NR_embM {k n : ℕ} (h : k ≤ n) (a b : Modes k) :
    NR n φ (embM h a) (embM h b) = NR k φ a b := by
  rcases a with i | i <;> rcases b with j | j <;> simp [NR, embM, MR_apply]

variable {φ}

theorem NR_pow_embM {k n : ℕ} (h : k ≤ n) (hz : φ PowerSeries.X ^ (k + 1) = 0) (r : ℕ) :
    ∀ a b : Modes k, (NR n φ ^ r) (embM h a) (embM h b) = (NR k φ ^ r) a b := by
  induction r with
  | zero =>
    intro a b
    rw [pow_zero, pow_zero, Matrix.one_apply, Matrix.one_apply]
    simp only [(embM_injective h).eq_iff]
  | succ r ih =>
    intro a b
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (embM h) (embM_injective h) _ _ (fun c hc => ?_) fun c => ?_
    · have hk := idxM_of_not_range h c hc
      rcases r with _ | r
      · rw [pow_zero, Matrix.one_apply, if_neg, mul_zero]
        rintro rfl
        exact hc ⟨b, rfl⟩
      · rw [NR_pow_row_zero hz c _ hk, mul_zero]
    · rw [NR_embM, ih]

/-- Modulo `z^{k+1}`, the entries of the Neumann covariance at the modes `≤ k` do not depend on
the number of modes. -/
theorem covN_embM {k n K : ℕ} (h : k ≤ n) (hK : k ≤ K) (hz : φ PowerSeries.X ^ (k + 1) = 0)
    (a b : Modes k) : covN n φ K (embM h a) (embM h b) = covN k φ k a b := by
  rw [covN_apply, covN_apply, swap_embM, eeM_embM, Matrix.sum_apply, Matrix.sum_apply]
  congr 1
  simp only [NR_pow_embM h hz]
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hK)) fun r _ hr => ?_
  rw [Finset.mem_range, not_lt] at hr
  rw [pow_eq_zero_of_le hr (NR_pow_eq_zero hz), Matrix.zero_apply]

/-- Modulo `z^{k+1}`, the entries of the Neumann covariance at a mode `> k` vanish
(`Cov(U_m, ·)` and `Cov(V_m, ·)` are `O(z^m)`). -/
theorem covN_eq_zero {k n : ℕ} (K : ℕ) (hz : φ PowerSeries.X ^ (k + 1) = 0) (a b : Modes n)
    (hab : k ≤ idxM a ∨ k ≤ idxM b) : covN n φ K a b = 0 := by
  rw [covN_apply]
  by_cases hb : k ≤ idxM b
  · rw [eeM_eq_zero hz b hb, mul_zero]
  · have ha : k ≤ idxM a := hab.resolve_right hb
    rw [Matrix.sum_apply, Finset.sum_eq_zero, zero_mul]
    intro r _
    rcases r with _ | r
    · rw [pow_zero, Matrix.one_apply, if_neg]
      intro hc
      rw [hc, idxM_swap] at ha
      exact hb ha
    · exact NR_pow_row_zero hz a _ ha r

/-- Stabilization of the covariance contraction in the number of modes, modulo `z^{k+1}`. -/
theorem covN_stable {k n K : ℕ} (h : k ≤ n) (hK : k ≤ K) (hz : φ PowerSeries.X ^ (k + 1) = 0)
    (x : Modes n → R) :
    ∑ a, ∑ b, x a * covN n φ K a b * x b =
      ∑ a : Modes k, ∑ b : Modes k, x (embM h a) * covN k φ k a b * x (embM h b) := by
  symm
  refine Fintype.sum_of_injective (embM h) (embM_injective h) _ _ (fun a ha => ?_) fun a => ?_
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [covN_eq_zero K hz a b (Or.inl (idxM_of_not_range h a ha)), mul_zero, zero_mul]
  · refine Fintype.sum_of_injective (embM h) (embM_injective h) _ _ (fun b hb => ?_) fun b => ?_
    · rw [covN_eq_zero K hz _ b (Or.inr (idxM_of_not_range h b hb)), mul_zero, zero_mul]
    · rw [covN_embM h hK hz]

end Stable

section Cand

/-- In `ℂ[[z]]/(z^{k+1})` the Neumann covariance is the reduction of the block inverse
(sphere/paper.tex l.656–661). -/
theorem covN_eq_cand (k : ℕ) :
    covN k (phiA k ℂ) k =
      (mkT k ℂ).mapMatrix (Matrix.fromBlocks (covUU k) (covUV k) (covUV k) (covVV k)) := by
  have hz : phiA k ℂ PowerSeries.X ^ (k + 1) = 0 := phiA_X_pow k ℂ
  have hφ : (mkT k ℂ).comp phiP = phiA k ℂ := rfl
  have h1 := congrArg (mkT k ℂ).mapMatrix (cand_eq k)
  rw [map_mul, map_sub, map_one, map_NR, map_C0, hφ] at h1
  have h2 : (∑ r ∈ range (k + 1), NR k (phiA k ℂ) ^ r) * (1 - NR k (phiA k ℂ)) = 1 := by
    rw [geom_sum_mul_neg, NR_pow_eq_zero hz, sub_zero]
  rw [covN, ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem covN_inl_inl (k : ℕ) (i j : Fin k) :
    covN k (phiA k ℂ) k (Sum.inl i) (Sum.inl j) = mkT k ℂ (covUU k i j) := by
  rw [covN_eq_cand]
  rfl

theorem covN_inl_inr (k : ℕ) (i j : Fin k) :
    covN k (phiA k ℂ) k (Sum.inl i) (Sum.inr j) = mkT k ℂ (covUV k i j) := by
  rw [covN_eq_cand]
  rfl

theorem covN_inr_inl (k : ℕ) (i j : Fin k) :
    covN k (phiA k ℂ) k (Sum.inr i) (Sum.inl j) = mkT k ℂ (covUV k j i) := by
  rw [covN_symm, covN_inl_inr]

theorem covN_inr_inr (k : ℕ) (i j : Fin k) :
    covN k (phiA k ℂ) k (Sum.inr i) (Sum.inr j) = mkT k ℂ (covVV k i j) := by
  rw [covN_eq_cand]
  rfl

end Cand

end Virasoro.Sphere
