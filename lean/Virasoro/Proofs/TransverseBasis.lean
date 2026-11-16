import Virasoro.Proofs.ResidueCore4

/-!
# The transverse residue in a basis of the kernel

Let `G(x)` be symmetric with nonzero determinant, and let the columns of `U` lie in
`ker G(0)`.  If the crossing matrix `B = Uᵀ G₁ U` is invertible and `ord_x det G` is the number
of columns, then the columns form a basis of the kernel, `G(x)⁻¹` has at most a simple pole and
`Res_{x=0} G(x)⁻¹ = U B⁻¹ Uᵀ` (Proposition 5.2 in coordinates).  For the Shapovalov matrix this
gives `Res_{Δ=h} F_N = ∑_{a,b} (B⁻¹)_{ab} ⟨u_a|V_d(1)|u_b⟩`.
-/

namespace Virasoro

open Polynomial Module

variable {K : Type*} [Field K] [CharZero K]

section General

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CharZero K] in
theorem residue_inverse_of_basis {G : Matrix ι ι (PowerSeries K)} (hsymm : G.IsSymm)
    (hdet : G.det ≠ 0) (U : Matrix ι κ K) (hU : coeffMat 0 G * U = 0)
    (hB : (U.transpose * coeffMat 1 G * U).det ≠ 0)
    (hord : G.det.order = ((Fintype.card κ : ℕ) : ℕ∞)) :
    poleOrderInv G ≤ 1 ∧
      invCoeff G (-1) = U * (U.transpose * coeffMat 1 G * U)⁻¹ * U.transpose := by
  classical
  set B := U.transpose * coeffMat 1 G * U with hBdef
  have hcross : ∀ (a : κ) (v : ι → K),
      cross1 G (fun Y => U Y a) v = (U.transpose.mulVec ((coeffMat 1 G).mulVec v)) a := by
    intro a v
    rfl
  have hinj : Function.Injective U.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : U.mulVec y = 0 := hy
    have h1 : B.mulVec y = 0 := by
      rw [hBdef, ← Matrix.mulVec_mulVec, hy', Matrix.mulVec_zero]
    exact Matrix.mulVec_injective_of_det_ne_zero hB (by rw [h1, Matrix.mulVec_zero])
  have hcol : ∀ a : κ, (fun Y => U Y a) ∈ ker0 G := by
    intro a
    rw [mem_ker0]
    funext Y
    have := congrFun (congrFun hU Y) a
    rw [Matrix.mul_apply] at this
    exact this
  have hle : LinearMap.range U.mulVecLin ≤ ker0 G := by
    rintro _ ⟨y, rfl⟩
    rw [mem_ker0]
    show (coeffMat 0 G).mulVec (U.mulVec y) = 0
    rw [Matrix.mulVec_mulVec, hU, Matrix.zero_mulVec]
  have hrange : finrank K (LinearMap.range U.mulVecLin) = Fintype.card κ := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  obtain ⟨s, hs⟩ := exists_isSmith hdet
  obtain ⟨h1, h2, -⟩ := smith_main hs
  have hsum : s.sum = Fintype.card κ := by
    rw [h1] at hord
    exact_mod_cast hord
  have hker : finrank K (ker0 G) = Fintype.card κ := by
    apply le_antisymm
    · rw [h2, ← hsum]
      exact multiset_filter_pos_card_le_sum s
    · rw [← hrange]
      exact Submodule.finrank_mono hle
  have heq : LinearMap.range U.mulVecLin = ker0 G :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrange, hker])
  have hnd : Cross1NondegK G := (cross1_main hsymm hdet).2.2 (by rw [hord, hker])
  obtain ⟨hpole, hres⟩ := (cross1_main hsymm hdet).1 hnd
  refine ⟨hpole, ?_⟩
  apply Matrix.mulVec_injective
  funext w
  obtain ⟨hmem, hcr⟩ := hres w
  rw [← heq] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hy' : U.mulVec y = (invCoeff G (-1)).mulVec w := hy
  have h3 : B.mulVec y = U.transpose.mulVec w := by
    funext a
    have h4 := hcr _ (hcol a)
    rw [hcross, ← hy'] at h4
    rw [hBdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h4]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have h5 : y = B⁻¹.mulVec (U.transpose.mulVec w) := by
    rw [← h3, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  rw [← hy', h5, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end General

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The residue of `F_N` at a weight where the kernel of the Shapovalov matrix has a basis with
invertible crossing matrix. -/
theorem ppCoeff_Frat_of_basis (c h d : K) (N : ℕ) (U : Matrix (Nat.Partition N) κ K)
    (hU : ∀ a, (gram c h N).mulVec (fun Y => U Y a) = 0)
    (B : Matrix κ κ K)
    (hBdef : ∀ a b, B a b = cross1 (gramLocal c h N) (fun Y => U Y a) (fun Y => U Y b))
    (hB : B.det ≠ 0)
    (hord : (gramLocal c h N).det.order = ((Fintype.card κ : ℕ) : ℕ∞)) :
    poleOrderInv (gramLocal c h N) ≤ 1 ∧ poleOrder (Frat c d N) h ≤ 1 ∧
      ppCoeff (Frat c d N) h 1
        = ∑ a, ∑ b, B⁻¹ a b * torusForm c h d N (fun Y => U Y a) (fun Y => U Y b) := by
  classical
  have hBeq : B = U.transpose * coeffMat 1 (gramLocal c h N) * U := by
    refine Matrix.ext fun a b => ?_
    rw [hBdef]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cross1, dotProduct, Matrix.mulVec,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => by ring
  have hU' : coeffMat 0 (gramLocal c h N) * U = 0 := by
    rw [coeffMat_zero_gramLocal]
    refine Matrix.ext fun Y a => ?_
    have := congrFun (hU a) Y
    rw [Matrix.mul_apply]
    exact this
  obtain ⟨hpole, hR⟩ := residue_inverse_of_basis (gramLocal_isSymm c h N)
    (gramLocal_det_ne_zero c h N) U hU' (by rw [← hBeq]; exact hB) hord
  obtain ⟨h1, h2⟩ := ppCoeff_Frat_of_simple c d h N hpole
  refine ⟨hpole, h1, ?_⟩
  rw [h2, hR, ← hBeq, sum_mul_eq_trace, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc]
  have e1 : U.transpose * ((torus c h d N).transpose * U)
      = (U.transpose * torus c h d N * U).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e1, ← sum_mul_eq_trace]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, torusForm, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => by ring

end Virasoro
