import Virasoro.Proofs.ResidueCore2
import Virasoro.Proofs.EvalLemmas

/-!
# The residue of `F_{ℓ+M}` at a singular weight of level `ℓ`

With `χ = P|h⟩` singular of level `ℓ ≥ 1`, `G_M(c,h+ℓ)` invertible, `β_χ ≠ 0` and
`ord_x det G_{ℓ+M}(c,h+x) = p(M)`:
`Res_{Δ=h} F_{ℓ+M}(c,Δ,d) = ⟨χ|V_d(1)|χ⟩ / β_χ · F_M(c,h+ℓ,d)`, and the pole is simple.
-/

namespace Virasoro

open Polynomial Module

variable {K : Type*} [Field K] [CharZero K] (c h : K) (ℓ M : ℕ) (p : Nat.Partition ℓ → K)

section Singular

variable (hℓ : 1 ≤ ℓ) (hχ : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) ℓ p) ℓ)

include hℓ hχ

/-- `ιᵀ G₁ ι = β_χ G_M(c,h+ℓ)`. -/
theorem iota_cross_matrix :
    (iotaMat c h ℓ M p).transpose * coeffMat 1 (gramLocal c h (ℓ + M)) * iotaMat c h ℓ M p
      = crossScalar c h p • gram c (h + (ℓ : K)) M := by
  refine Matrix.ext fun Z Z' => ?_
  rw [Matrix.smul_apply, smul_eq_mul, ← cross1_iotaMat c h ℓ M p hℓ hχ Z Z']
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cross1, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => by ring

theorem cross1_iota_mulVec (Z : Nat.Partition M) (y : Nat.Partition M → K) :
    cross1 (gramLocal c h (ℓ + M)) (fun Y => iotaMat c h ℓ M p Y Z)
        ((iotaMat c h ℓ M p).mulVec y)
      = ((crossScalar c h p • gram c (h + (ℓ : K)) M).mulVec y) Z := by
  rw [← iota_cross_matrix c h ℓ M p hℓ hχ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rfl

theorem gram_mul_iotaMat : gram c h (ℓ + M) * iotaMat c h ℓ M p = 0 := by
  refine Matrix.ext fun Y Z => ?_
  have := congrFun (gram_mulVec_iotaMat_col c h ℓ M p hℓ hχ Z) Y
  rw [Matrix.zero_apply]
  exact this

variable (hβ : crossScalar c h p ≠ 0) (hg : (gram c (h + (ℓ : K)) M).det ≠ 0)

include hβ hg

omit hℓ hχ in
theorem det_cross_ne_zero : (crossScalar c h p • gram c (h + (ℓ : K)) M).det ≠ 0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hβ) hg

/-- `ι` is injective. -/
theorem iotaMat_injective : Function.Injective (iotaMat c h ℓ M p).mulVecLin := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hy' : (iotaMat c h ℓ M p).mulVec y = 0 := hy
  have h1 : (crossScalar c h p • gram c (h + (ℓ : K)) M).mulVec y = 0 := by
    funext Z
    rw [← cross1_iota_mulVec c h ℓ M p hℓ hχ Z y, hy']
    simp [cross1]
  have hinj := Matrix.mulVec_injective_of_det_ne_zero (det_cross_ne_zero c h ℓ M p hβ hg)
  exact hinj (by rw [h1, Matrix.mulVec_zero])

variable (hord : (gramLocal c h (ℓ + M)).det.order = ((Fintype.card (Nat.Partition M) : ℕ) : ℕ∞))

include hord

/-- The kernel of `G_{ℓ+M}(c,h)` is the image of `ι`, the inverse has a simple pole, and its
residue is `ι (β_χ G_M(c,h+ℓ))⁻¹ ιᵀ`. -/
theorem residue_inverse :
    poleOrderInv (gramLocal c h (ℓ + M)) ≤ 1 ∧
      invCoeff (gramLocal c h (ℓ + M)) (-1)
        = iotaMat c h ℓ M p * (crossScalar c h p • gram c (h + (ℓ : K)) M)⁻¹
          * (iotaMat c h ℓ M p).transpose := by
  classical
  set G := gramLocal c h (ℓ + M) with hG
  set ι := iotaMat c h ℓ M p with hι
  have hdet := gramLocal_det_ne_zero c h (ℓ + M)
  have hsymm := gramLocal_isSymm c h (ℓ + M)
  have hle : LinearMap.range ι.mulVecLin ≤ ker0 G := by
    rintro _ ⟨y, rfl⟩
    rw [mem_ker0, coeffMat_zero_gramLocal]
    show (gram c h (ℓ + M)).mulVec (ι.mulVec y) = 0
    rw [Matrix.mulVec_mulVec, gram_mul_iotaMat c h ℓ M p hℓ hχ, Matrix.zero_mulVec]
  have hrange : finrank K (LinearMap.range ι.mulVecLin) = Fintype.card (Nat.Partition M) := by
    rw [LinearMap.finrank_range_of_inj (iotaMat_injective c h ℓ M p hℓ hχ hβ hg),
      Module.finrank_fintype_fun_eq_card]
  obtain ⟨s, hs⟩ := exists_isSmith hdet
  obtain ⟨h1, h2, -⟩ := smith_main hs
  have hsum : s.sum = Fintype.card (Nat.Partition M) := by
    rw [h1] at hord
    exact_mod_cast hord
  have hker : finrank K (ker0 G) = Fintype.card (Nat.Partition M) := by
    apply le_antisymm
    · rw [h2, ← hsum]
      exact multiset_filter_pos_card_le_sum s
    · rw [← hrange]
      exact Submodule.finrank_mono hle
  have heq : LinearMap.range ι.mulVecLin = ker0 G :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrange, hker])
  have hnd : Cross1NondegK G := (cross1_main hsymm hdet).2.2 (by rw [hord, hker])
  obtain ⟨hpole, hres⟩ := (cross1_main hsymm hdet).1 hnd
  refine ⟨hpole, ?_⟩
  apply Matrix.mulVec_injective
  funext w
  obtain ⟨hmem, hcross⟩ := hres w
  rw [← heq] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hy' : ι.mulVec y = (invCoeff G (-1)).mulVec w := hy
  have h3 : (crossScalar c h p • gram c (h + (ℓ : K)) M).mulVec y = ι.transpose.mulVec w := by
    funext Z
    rw [← cross1_iota_mulVec c h ℓ M p hℓ hχ Z y, hy',
      hcross _ (iotaMat_col_mem_ker0 c h ℓ M p hℓ hχ Z)]
    rfl
  have hunit : IsUnit (crossScalar c h p • gram c (h + (ℓ : K)) M).det :=
    isUnit_iff_ne_zero.2 (det_cross_ne_zero c h ℓ M p hβ hg)
  have h4 : y = (crossScalar c h p • gram c (h + (ℓ : K)) M)⁻¹.mulVec (ι.transpose.mulVec w) := by
    rw [← h3, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  rw [← hy', h4, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Singular

end Virasoro
