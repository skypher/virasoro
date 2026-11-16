import Virasoro.Statements.Sec5a
import Virasoro.Proofs.SmithBasic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Proofs: Lemma 5.1 (pole order from local invariant factors)
-/

namespace Virasoro

open scoped LaurentSeries
open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coeffMat_zero_eq (G : Matrix ι ι K⟦X⟧) :
    coeffMat 0 G = (PowerSeries.constantCoeff (R := K)).mapMatrix G := by
  ext i j
  simp [coeffMat]

theorem det_coeffMat_zero (G : Matrix ι ι K⟦X⟧) :
    (coeffMat 0 G).det = PowerSeries.constantCoeff G.det := by
  rw [coeffMat_zero_eq, ← RingHom.map_det]

theorem det_coeffMat_zero_ne_zero {U : Matrix ι ι K⟦X⟧} (hU : IsUnit U.det) :
    (coeffMat 0 U).det ≠ 0 := by
  rw [det_coeffMat_zero]
  exact (PowerSeries.isUnit_iff_constantCoeff.mp hU).ne_zero

theorem coeffMat_zero_diagonal (e : ι → ℕ) :
    coeffMat 0 (Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) =
      Matrix.diagonal fun i => if e i = 0 then (1 : K) else 0 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [coeffMat, Matrix.map_apply, Matrix.diagonal_apply_eq, PowerSeries.coeff_X_pow]
    by_cases h0 : e i = 0 <;> simp [h0, eq_comm]
  · simp [coeffMat, Matrix.diagonal_apply_ne _ h]

/-- The multiset of exponents attached to an exponent function. -/
theorem multiset_sum_eq (e : ι → ℕ) : (Finset.univ.val.map e).sum = ∑ i, e i := rfl

theorem multiset_filter_card (e : ι → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.univ.val.map e).filter p).card = (Finset.univ.filter fun i => p (e i)).card := by
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

theorem multiset_sup_eq (e : ι → ℕ) : (Finset.univ.val.map e).sup = Finset.univ.sup e :=
  (Finset.sup_def ..).symm

section Smith

variable {G : Matrix ι ι K⟦X⟧} {e : ι → ℕ} {U V : Matrix ι ι K⟦X⟧}

/-- `ord_x det G = ∑ e_i`. -/
theorem smith_order_det (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hD : U * G * V = Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) :
    G.det.order = ((∑ i, e i : ℕ) : ℕ∞) := by
  have h := congrArg Matrix.det hD
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum] at h
  have h2 := congrArg PowerSeries.order h
  rw [PowerSeries.order_mul, PowerSeries.order_mul, PowerSeries.order_zero_of_unit hU,
    PowerSeries.order_zero_of_unit hV, PowerSeries.order_X_pow, zero_add, add_zero] at h2
  exact h2

/-- `dim ker G(0) = #{i : e_i > 0}`. -/
theorem smith_finrank_ker (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hD : U * G * V = Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) :
    finrank K (ker0 G) = (Finset.univ.filter fun i => 0 < e i).card := by
  classical
  have h0 : coeffMat 0 U * coeffMat 0 G * coeffMat 0 V =
      Matrix.diagonal fun i => if e i = 0 then (1 : K) else 0 := by
    rw [← coeffMat_zero_mul, ← coeffMat_zero_mul, hD, coeffMat_zero_diagonal]
  have hrank : (coeffMat 0 G).rank = Fintype.card {i // e i = 0} := by
    have h1 := congrArg Matrix.rank h0
    rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (det_coeffMat_zero_ne_zero hV),
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (det_coeffMat_zero_ne_zero hU),
      Matrix.rank_diagonal] at h1
    rw [h1]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_)
    by_cases h : e i = 0 <;> simp [h]
  have hrn := LinearMap.finrank_range_add_finrank_ker (coeffMat 0 G).mulVecLin
  rw [Module.finrank_pi K] at hrn
  have hr : finrank K (LinearMap.range (coeffMat 0 G).mulVecLin) = (coeffMat 0 G).rank := rfl
  have hk : finrank K (LinearMap.ker (coeffMat 0 G).mulVecLin) = finrank K (ker0 G) := rfl
  rw [hr, hrank, hk] at hrn
  have hsplit : Fintype.card {i // e i = 0} + (Finset.univ.filter fun i => 0 < e i).card =
      Fintype.card ι := by
    rw [Fintype.card_subtype]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun i => e i = 0)
    rw [Finset.card_univ] at this
    rw [← this]
    congr 2
    ext i
    simp [Nat.pos_iff_ne_zero]
  omega

/-- The diagonal Laurent matrix `diag(x^{-e_i})`. -/
noncomputable def diagInv (e : ι → ℕ) : Matrix ι ι K⸨X⸩ :=
  Matrix.diagonal fun i => HahnSeries.single (-(e i : ℤ)) (1 : K)

theorem toL_diagonal_mul_diagInv (e : ι → ℕ) :
    toL (Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) * diagInv e = 1 := by
  have : toL (Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) =
      Matrix.diagonal fun i => (HahnSeries.single (e i : ℤ) (1 : K) : K⸨X⸩) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [toL, HahnSeries.ofPowerSeries_X_pow]
    · simp [toL, Matrix.diagonal_apply_ne _ h]
  rw [this, diagInv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem matOrdGE_diagInv (e : ι → ℕ) :
    MatOrdGE (diagInv (K := K) e) (-((Finset.univ.sup e : ℕ) : ℤ)) := by
  intro i j
  by_cases h : i = j
  · subst h
    rw [diagInv, Matrix.diagonal_apply_eq]
    refine ordGE_iff.2 fun m hm => HahnSeries.coeff_single_of_ne ?_
    have : e i ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ i)
    have : (e i : ℤ) ≤ (Finset.univ.sup e : ℕ) := by exact_mod_cast this
    omega
  · rw [diagInv, Matrix.diagonal_apply_ne _ h]
    exact OrdGE.zero _

theorem isUnit_det_toL {U : Matrix ι ι K⟦X⟧} (hU : IsUnit U.det) : IsUnit (toL U).det := by
  rw [det_toL]
  exact hU.map _

/-- `G(x)⁻¹ = V diag(x^{-e_i}) U`. -/
theorem smith_inv (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hD : U * G * V = Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) :
    invLaurent G = toL V * diagInv e * toL U := by
  have hD' : toL U * toL G * toL V = toL (Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) := by
    rw [← toL_mul, ← toL_mul, hD]
  have hUL := isUnit_det_toL hU
  have key : toL U * (toL G * (toL V * diagInv e * toL U)) = toL U := by
    calc toL U * (toL G * (toL V * diagInv e * toL U))
        = (toL U * toL G * toL V) * diagInv e * toL U := by simp only [Matrix.mul_assoc]
      _ = toL U := by rw [hD', toL_diagonal_mul_diagInv, Matrix.one_mul]
  have h1 : toL G * (toL V * diagInv e * toL U) = 1 := by
    have := congrArg (fun M => (toL U)⁻¹ * M) key
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUL, Matrix.one_mul] at this
  exact Matrix.inv_eq_right_inv h1

/-- The pole order of `G(x)⁻¹` is the largest Smith exponent. -/
theorem smith_poleOrderInv (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hD : U * G * V = Matrix.diagonal fun i => (PowerSeries.X : K⟦X⟧) ^ e i) :
    poleOrderInv G = Finset.univ.sup e := by
  apply le_antisymm
  · apply poleOrderInv_le
    rw [smith_inv hU hV hD]
    have := ((matOrdGE_toL V).mul (matOrdGE_diagInv (K := K) e)).mul (matOrdGE_toL U)
    simpa using this
  · refine Finset.sup_le fun k _ => ?_
    -- `diag(x^{-e}) = V⁻¹ G⁻¹ U⁻¹` has entries of valuation at least `-p`
    have hinv := smith_inv hU hV hD
    have hUL := isUnit_det_toL hU
    have hVL := isUnit_det_toL hV
    have hdiag : diagInv e = toL V⁻¹ * invLaurent G * toL U⁻¹ := by
      rw [hinv]
      have hV1 : toL V⁻¹ * toL V = 1 := by
        rw [← toL_mul, Matrix.nonsing_inv_mul _ hV, toL_one]
      have hU1 : toL U * toL U⁻¹ = 1 := by
        rw [← toL_mul, Matrix.mul_nonsing_inv _ hU, toL_one]
      calc diagInv e = (toL V⁻¹ * toL V) * diagInv e * (toL U * toL U⁻¹) := by
            rw [hV1, hU1, Matrix.one_mul, Matrix.mul_one]
        _ = toL V⁻¹ * (toL V * diagInv e * toL U) * toL U⁻¹ := by
            simp only [Matrix.mul_assoc]
    have hord : MatOrdGE (diagInv (K := K) e) (-(poleOrderInv G : ℤ)) := by
      rw [hdiag]
      have := ((matOrdGE_toL V⁻¹).mul (matOrdGE_inv G)).mul (matOrdGE_toL U⁻¹)
      simpa using this
    by_contra hlt
    push Not at hlt
    have hc := (hord k k).coeff_eq_zero (m := -(e k : ℤ)) (by
      have : (poleOrderInv G : ℤ) < e k := by exact_mod_cast hlt
      linarith)
    rw [diagInv, Matrix.diagonal_apply_eq, HahnSeries.coeff_single_same] at hc
    exact one_ne_zero hc

end Smith

/-- If a multiset of natural numbers has sum equal to the number of its nonzero members, then
every nonzero member is `1`. -/
theorem multiset_pos_eq_one (s : Multiset ℕ) (h : s.sum = s.countP fun e => e ≠ 0) :
    ∀ e ∈ s, e ≠ 0 → e = 1 := by
  have hle : ∀ u : Multiset ℕ, (u.countP fun e => e ≠ 0) ≤ u.sum := by
    intro u
    induction u using Multiset.induction_on with
    | empty => simp
    | cons b v ihv =>
      by_cases hb : b ≠ 0
      · rw [Multiset.countP_cons_of_pos (p := fun e : ℕ => e ≠ 0) v hb, Multiset.sum_cons]; omega
      · rw [Multiset.countP_cons_of_neg (p := fun e : ℕ => e ≠ 0) v hb, Multiset.sum_cons]; omega
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    intro e he hpos
    have h1 := hle t
    by_cases ha : a ≠ 0
    · rw [Multiset.countP_cons_of_pos (p := fun e : ℕ => e ≠ 0) t ha, Multiset.sum_cons] at h
      have ha1 : a = 1 := by omega
      rcases Multiset.mem_cons.1 he with rfl | het
      · exact ha1
      · exact ih (by omega) e het hpos
    · rw [Multiset.countP_cons_of_neg (p := fun e : ℕ => e ≠ 0) t ha, Multiset.sum_cons] at h
      rcases Multiset.mem_cons.1 he with rfl | het
      · exact absurd hpos ha
      · exact ih (by omega) e het hpos

/-- Lemma 5.1 for an arbitrary coefficient field and index type. -/
theorem smith_main {G : Matrix ι ι K⟦X⟧} {s : Multiset ℕ} (hs : IsSmith G s) :
    G.det.order = ((s.sum : ℕ) : ℕ∞) ∧
    finrank K (ker0 G) = (s.filter fun e => 0 < e).card ∧
    poleOrderInv G = s.sup := by
  obtain ⟨e, U, V, hU, hV, hD, rfl⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · rw [multiset_sum_eq]; exact smith_order_det hU hV hD
  · rw [multiset_filter_card]; exact smith_finrank_ker hU hV hD
  · rw [multiset_sup_eq]; exact smith_poleOrderInv hU hV hD

/-- Paper label: lem:smith -/
theorem lem_smith : Stmt_lem_smith := by
  intro m G s _ hs
  obtain ⟨h1, h2, h3⟩ := smith_main hs
  refine ⟨h1, h2, h3, ?_⟩
  intro k hk1 hk2
  have hfilt : (s.filter fun e => 0 < e) = s.filter fun e => e ≠ 0 :=
    Multiset.filter_congr fun e _ => Nat.pos_iff_ne_zero
  have hsum : s.sum = s.countP fun e => e ≠ 0 := by
    rw [h1] at hk1
    have : s.sum = k := by exact_mod_cast hk1
    rw [this, Multiset.countP_eq_card_filter, ← hfilt, ← h2, hk2]
  have hone := multiset_pos_eq_one s hsum
  refine ⟨fun e he hpos => hone e he hpos.ne', ?_⟩
  rw [h3]
  refine Multiset.sup_le.2 fun e he => ?_
  by_cases hpos : e ≠ 0
  · exact (hone e he hpos).le
  · have : e = 0 := by omega
    simp [this]

example : Stmt_lem_smith := lem_smith

end Virasoro
