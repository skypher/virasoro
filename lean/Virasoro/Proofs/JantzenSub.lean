import Virasoro.Proofs.Levels
import Virasoro.Proofs.JantzenDim

/-!
# Lemma 5.6: the Jantzen layers are submodules, and the first layer is the radical
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K] [CharZero K] (c h : K)

theorem gramShift_eval (N : ℕ) : (gramShift c h N).map (Polynomial.eval 0) = gram c h N := by
  have := gram_map (Polynomial.evalRingHom (0 : K)) (C c) (C h + X) N
  simp only [coe_evalRingHom, eval_C, eval_add, eval_X, add_zero] at this
  rw [gramShift, this]

theorem eval_mulVec_gramShift (N : ℕ) (w : Nat.Partition N → K[X]) (Y : Nat.Partition N) :
    ((gramShift c h N).mulVec w Y).eval 0
      = (gram c h N).mulVec (fun Z => (w Z).eval 0) Y := by
  rw [← gramShift_eval]
  exact RingHom.map_mulVec (Polynomial.evalRingHom (0 : K)) (gramShift c h N) w Y

/-- Each Jantzen layer is stable under all modes. -/
theorem L_mem_jantzen (i : ℕ) (n : ℤ) {v : Verma K c h} (hv : v ∈ jantzen c h i) :
    Verma.L n v ∈ jantzen c h i := by
  unfold jantzen at hv ⊢
  refine Submodule.iSup_induction (motive := fun v => Verma.L n v ∈
      ⨆ N : ℕ, (jantzenLayer c h N i).map (Verma.pbwCoord N)) _ hv ?_ ?_ ?_
  · rintro N _ ⟨v₀, ⟨w, hw0, hdvd⟩, rfl⟩
    by_cases hlt : (N : ℤ) < n
    · rw [Verma.L_eq_zero_of_level hlt ⟨v₀, rfl⟩]
      exact Submodule.zero_mem _
    · have hM : (((N : ℤ) - n).toNat : ℤ) = (N : ℤ) - n := Int.toNat_of_nonneg (by omega)
      set M := ((N : ℤ) - n).toNat with hMdef
      have hc : (evalRingHom (0 : K)) (C c) = c := by simp
      have hh : (evalRingHom (0 : K)) (C h + X) = h := by simp
      have hBX := Verma.isShapovalov_shap (c := C c) (h := C h + (X : K[X]))
      obtain ⟨w₁, hw₁⟩ := Verma.L_mem_level (c := C c) (h := C h + (X : K[X])) hM
        (v := Verma.pbwCoord N w) ⟨w, rfl⟩
      have e1 : Verma.L n (Verma.pbwCoord (c := c) (h := h) N v₀)
          = Verma.pbwCoord M fun Y => (w₁ Y).eval 0 := by
        have h1 := congrArg (Verma.baseChange (evalRingHom (0 : K)) hc hh) hw₁
        rw [Verma.baseChange_pbwCoord, Verma.baseChange_L, Verma.baseChange_pbwCoord] at h1
        have h2 : (fun Y => (evalRingHom (0 : K)) (w Y)) = v₀ := funext hw0
        rw [h2] at h1
        exact h1.symm
      rw [e1]
      refine Submodule.mem_iSup_of_mem M ⟨fun Y => (w₁ Y).eval 0, ⟨w₁, fun Y => rfl, ?_⟩, rfl⟩
      intro Y
      have h3 := Verma.shap_neg_pbwCoord (c := C c) (h := C h + (X : K[X])) Y w₁
      rw [hw₁, ← neg_neg n, ← hBX.2] at h3
      rw [show gramShift c h M = gram (C c) (C h + (X : K[X])) M from rfl, ← h3]
      have hN : ((N : ℕ) : ℤ) = ((Y.word.sum : ℕ) : ℤ) - (-n) := by
        rw [Verma.word_sum']
        omega
      obtain ⟨a, ha⟩ := Verma.L_neg_mem_level (c := C c) (h := C h + (X : K[X]))
        (Verma.posWord_word Y) hN
      rw [← ha, Verma.pbwCoord_apply, map_sum, LinearMap.sum_apply]
      refine Finset.dvd_sum fun Z _ => ?_
      rw [map_smul, LinearMap.smul_apply, Verma.shap_neg_pbwCoord, smul_eq_mul]
      exact Dvd.dvd.mul_left (hdvd Z) _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The first Jantzen layer is the radical of the Shapovalov form. -/
theorem jantzen_one_eq_radical :
    (jantzen c h 1 : Set (Verma K c h)) = {v | ∀ u, Verma.shap c h u v = 0} := by
  classical
  ext v
  constructor
  · intro hv
    rw [SetLike.mem_coe] at hv
    unfold jantzen at hv
    refine Submodule.iSup_induction (motive := fun v => ∀ u, Verma.shap c h u v = 0) _ hv
      ?_ ?_ ?_
    · rintro N _ ⟨v₀, ⟨w, hw0, hdvd⟩, rfl⟩
      have hG : (gram c h N).mulVec v₀ = 0 := by
        funext Y
        have h1 := eval_mulVec_gramShift c h N w Y
        rw [show (fun Z => (w Z).eval 0) = v₀ from funext hw0] at h1
        rw [← h1]
        obtain ⟨q, hq⟩ := hdvd Y
        rw [hq]
        simp
      intro u
      refine Verma.induction_neg (P := fun u => Verma.shap c h u (Verma.pbwCoord N v₀) = 0)
        ?_ ?_ ?_ u
      · intro w' hw'
        have hlev := Verma.neg_mem_level (c := c) (h := h) w'.length w' hw' le_rfl
        by_cases hs : w'.sum = N
        · rw [hs] at hlev
          obtain ⟨a, ha⟩ := hlev
          rw [← ha, Verma.pbwCoord_apply, map_sum, LinearMap.sum_apply]
          refine Finset.sum_eq_zero fun Z _ => ?_
          rw [map_smul, LinearMap.smul_apply, Verma.shap_neg_pbwCoord, hG, Pi.zero_apply,
            smul_zero]
        · exact Verma.shap_level_ne hs hlev ⟨v₀, rfl⟩
      · intro a b ha hb
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      · intro r a ha
        rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
    · intro u
      rw [map_zero]
    · intro x y hx hy u
      rw [map_add, hx u, hy u, add_zero]
  · intro hrad
    have hrad : ∀ u, Verma.shap c h u v = 0 := hrad
    have hmem : v ∈ Submodule.span K (Set.range fun Y : (Σ N : ℕ, Nat.Partition N) =>
        Verma.neg (c := c) (h := h) Y.2.word) := by
      rw [Verma.span_neg_word_eq_top]; trivial
    obtain ⟨a, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hmem
    set T : Finset ℕ := a.support.image Sigma.fst with hT
    have hsum : (a.sum fun i x => x • Verma.neg (c := c) (h := h) i.2.word)
        = ∑ N ∈ T, Verma.pbwCoord N fun Y => a ⟨N, Y⟩ := by
      have h1 : ∑ N ∈ T, Verma.pbwCoord (c := c) (h := h) N (fun Y => a ⟨N, Y⟩)
          = ∑ i ∈ T.sigma fun _ => Finset.univ, a i • Verma.neg i.2.word := by
        rw [Finset.sum_sigma]
        exact Finset.sum_congr rfl fun N _ => Verma.pbwCoord_apply N _
      rw [h1, Finsupp.sum]
      refine Finset.sum_subset ?_ ?_
      · intro i hi
        rw [Finset.mem_sigma]
        exact ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ _⟩
      · intro i _ hi
        rw [Finsupp.notMem_support_iff.1 hi, zero_smul]
    have hG : ∀ N : ℕ, (gram c h N).mulVec (fun Y => a ⟨N, Y⟩) = 0 := by
      intro N
      by_cases hN : N ∈ T
      · funext Y
        have h1 := hrad (Verma.neg Y.word)
        rw [hsum, map_sum, Finset.sum_eq_single N] at h1
        · rw [← Verma.shap_neg_pbwCoord, h1, Pi.zero_apply]
        · intro N' _ hne
          exact Verma.shap_level_ne (Ne.symm hne) (Verma.neg_word_mem_level Y) ⟨_, rfl⟩
        · intro hN'
          exact absurd hN hN'
      · have hz : (fun Y : Nat.Partition N => a ⟨N, Y⟩) = 0 := by
          funext Y
          by_contra hne
          exact hN (Finset.mem_image_of_mem Sigma.fst (Finsupp.mem_support_iff.2 hne))
        rw [hz, Matrix.mulVec_zero]
    rw [hsum, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun N _ => ?_
    unfold jantzen
    refine Submodule.mem_iSup_of_mem N ⟨fun Y => a ⟨N, Y⟩,
      ⟨fun Y => C (a ⟨N, Y⟩), fun Y => eval_C, fun Y => ?_⟩, rfl⟩
    rw [pow_one, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero,
      eval_mulVec_gramShift]
    simp only [eval_C]
    rw [hG N, Pi.zero_apply]

/-- If `det G_N(c,h+x) ≢ 0` with local Smith exponents `e_j`, then
`dim J^i_N = #{j : e_j ≥ i}` and `∑_{i≥1} dim J^i_N = ord_x det G_N(c,h+x)`; each `J^i(c,h)` is
a submodule of `M(c,h)`, and `J^1(c,h)` is the radical of the Shapovalov form.

Paper label: lem:jantzen-smith -/
theorem lem_jantzen_smith : Stmt_lem_jantzen_smith := by
  intro c h
  refine ⟨fun N s _ hs => ⟨fun i _ => (jantzen_dim c h N s hs).1 i, (jantzen_dim c h N s hs).2⟩,
    fun _ => ⟨fun i n v hv => L_mem_jantzen c h i n hv, fun B hB => ?_⟩⟩
  rw [Verma.shapovalov_unique hB Verma.isShapovalov_shap]
  exact jantzen_one_eq_radical c h

example : Stmt_lem_jantzen_smith := lem_jantzen_smith

end Virasoro
