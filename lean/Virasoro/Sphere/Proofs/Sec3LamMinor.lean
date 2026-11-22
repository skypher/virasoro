import Virasoro.Sphere.Proofs.Sec3LamInfty
import Virasoro.Proofs.SmithBasic
import Virasoro.Proofs.Sec4Core2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Sphere paper Lemma 3.3(i): an invertible square minor at `λ⁻¹ = 0` (proof of Lemma 3.3(i))

The paper concludes regularity at `λ = ∞` from the injectivity of `𝒟_m(∞)`: the rectangular
system `𝒟_m(λ)S_m = R_m` then has an invertible `p(m) × p(m)` square minor at `λ⁻¹ = 0`, which
gives a left inverse regular in `λ⁻¹`.  This file proves the two linear-algebra steps in the
variable `t = 1/λ` (Laurent series `ℂ⸨X⸩`):
- `exists_square_minor`: an injective rectangular matrix over a field has a square submatrix
  (a choice of rows) with nonzero determinant;
- `regular_of_rect_system`: if `M x = r` with `M` regular at `t = 0`, `M(0)` injective and `r`
  regular, then `x` is regular.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

/-- An injective rectangular matrix over a field has an invertible square minor. -/
theorem exists_square_minor {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Field K]
    (N : Matrix ι κ K) (hN : ∀ v : κ → K, N.mulVec v = 0 → v = 0) :
    ∃ e : κ → ι, (N.submatrix e id).det ≠ 0 := by
  classical
  -- the rows of `N` span `K^κ`
  have hspan : Submodule.span K (Set.range N) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set v : κ → K := fun j => f (Pi.single j 1) with hv
    have hfv : ∀ w : κ → K, f w = ∑ j, w j * v j := by
      intro w
      conv_lhs => rw [show w = ∑ j, w j • Pi.single j (1 : K) from by
        ext i; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul, hv]
    have hNv : N.mulVec v = 0 := by
      ext i
      have hi : N i ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, hfv] at hi
      simpa [Matrix.mulVec, dotProduct] using hi
    apply hf0
    refine LinearMap.ext fun w => ?_
    rw [hfv, hN v hNv]
    simp
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range N)
  have hbfin : b.Finite := (Set.finite_range N).subset hbsub
  haveI : Fintype b := hbfin.fintype
  let B : Module.Basis b K (κ → K) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  have hcard : Fintype.card κ = Fintype.card b := by
    have h1 : Module.finrank K (κ → K) = Fintype.card κ := by simp
    rw [Module.finrank_eq_card_basis B] at h1
    exact h1.symm
  let eqv : κ ≃ b := Fintype.equivOfCardEq hcard
  have hpre : ∀ j : κ, ∃ i : ι, N i = (eqv j : κ → K) := fun j => hbsub (eqv j).2
  choose e he using hpre
  refine ⟨e, ?_⟩
  have hli : LinearIndependent K fun j => (N.submatrix e id) j := by
    have : (fun j => (N.submatrix e id) j) = fun j => ((eqv j : b) : κ → K) := by
      funext j
      ext l
      simp [Matrix.submatrix, he j]
    rw [this]
    exact hbli.comp eqv eqv.injective
  have hu := (Matrix.linearIndependent_rows_iff_isUnit).1 hli
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

/-- A rectangular system over Laurent series in `t` whose matrix is regular at `t = 0` with an
injective value there, and whose right side is regular, has a regular solution: an invertible
square minor of the value gives a left inverse regular in `t`. -/
theorem regular_of_rect_system {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℂ⸨X⸩) (N : Matrix ι κ ℂ) (hM : ∀ i j, RegVal (M i j) (N i j))
    (hN : ∀ v : κ → ℂ, N.mulVec v = 0 → v = 0) (x : κ → ℂ⸨X⸩) (r : ι → ℂ⸨X⸩)
    (hr : ∀ i, OrdGE (r i) 0) (h : M.mulVec x = r) : ∀ j, OrdGE (x j) 0 := by
  classical
  obtain ⟨e, he⟩ := exists_square_minor N hN
  -- the entries of `M` are power series
  have hP : ∀ i j, ∃ p : PowerSeries ℂ, M i j = HahnSeries.ofPowerSeries ℤ ℂ p ∧
      PowerSeries.constantCoeff p = (M i j).coeff 0 :=
    fun i j => exists_ofPowerSeries (hM i j).1
  choose P hPe hPc using hP
  set φ := HahnSeries.ofPowerSeries ℤ ℂ with hφ
  let P' : Matrix κ κ (PowerSeries ℂ) := (Matrix.of P).submatrix e id
  have hP'0 : P'.map PowerSeries.constantCoeff = N.submatrix e id := by
    ext j l
    simp only [P', Matrix.map_apply, Matrix.submatrix_apply, Matrix.of_apply, id]
    rw [hPc, (hM (e j) l).2]
  have hdet : IsUnit P'.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, hP'0]
    exact he.isUnit
  have hinv : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul P' hdet
  have hMe : (M.submatrix e id) = P'.map φ := by
    ext j l
    simp [P', hPe]
  have hsys : (M.submatrix e id).mulVec x = fun j => r (e j) := by
    funext j
    rw [← h]
    rfl
  have hx : x = (P'⁻¹.map φ).mulVec (fun j => r (e j)) := by
    rw [← hsys, hMe, Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv, Matrix.map_one φ (map_zero φ)
      (map_one φ), Matrix.one_mulVec]
  intro j
  rw [hx]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact OrdGE.sum fun l _ => (ordGE_ofPowerSeries _).mul (hr (e l)) |>.mono (by norm_num)

end Virasoro.Sphere
