import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Sphere paper Lemma 3.5, Step 2: removable singularities and Liouville's theorem
(`sphere/paper.tex` l.914–929)

A function on the unit disc that is holomorphic off `0` and `b`, bounded near both points, and
agrees on an annulus `ρ < |x| < 1` with a function holomorphic on `|x| > ρ` and bounded on
`|x| ≥ 1`, extends to a bounded entire function; by Liouville's theorem it is constant.

Consumer: `sub_bergman_const_of_patches`.
-/

namespace Virasoro.Sphere

open Filter Topology Metric Set

/-- Riemann's removable singularity theorem on an open set, for a function bounded near `c`. -/
theorem removable_step {s : Set ℂ} (hs : IsOpen s) {f : ℂ → ℂ} {c : ℂ} (hc : c ∈ s)
    (hd : DifferentiableOn ℂ f (s \ {c}))
    (hb : ∃ ε > 0, ∃ M : ℝ, ∀ x, x ≠ c → ‖x - c‖ < ε → ‖f x‖ ≤ M) :
    DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠] c) f)) s := by
  obtain ⟨ε, hε, M, hM⟩ := hb
  have hto : IsOpen (s ∩ ball c ε) := hs.inter isOpen_ball
  have hct : c ∈ s ∩ ball c ε := ⟨hc, mem_ball_self hε⟩
  have h1 : DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠] c) f)) (s ∩ ball c ε) := by
    refine Complex.differentiableOn_update_limUnder_of_bddAbove (hto.mem_nhds hct)
      (hd.mono fun x hx => ⟨hx.1.1, hx.2⟩) ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hM x hx.2 (by simpa [dist_eq_norm] using hx.1.2)
  intro x hx
  by_cases hxc : x = c
  · rw [hxc]
    exact (h1.differentiableAt (hto.mem_nhds hct)).differentiableWithinAt
  · have hmem : s \ {c} ∈ 𝓝 x := (hs.sdiff isClosed_singleton).mem_nhds ⟨hx, hxc⟩
    have heq : Function.update f c (limUnder (𝓝[≠] c) f) =ᶠ[𝓝 x] f := by
      filter_upwards [hmem] with y hy
      exact Function.update_of_ne hy.2 _ _
    exact ((hd.differentiableAt hmem).congr_of_eventuallyEq heq).differentiableWithinAt

/-- Liouville's theorem on `ℙ¹` for a function given on two patches (l.914–929). -/
theorem liouville_glue {G Go : ℂ → ℂ} {b : ℂ} {ρ : ℝ} (hb0 : b ≠ 0) (hbρ : ‖b‖ ≤ ρ) (hρ : ρ < 1)
    (hd : DifferentiableOn ℂ G ((ball (0 : ℂ) 1 \ {b}) \ {0}))
    (h0 : ∃ ε > 0, ∃ M : ℝ, ∀ x, x ≠ 0 → ‖x - 0‖ < ε → ‖G x‖ ≤ M)
    (hbb : ∃ ε > 0, ∃ M : ℝ, ∀ x, x ≠ b → ‖x - b‖ < ε → ‖G x‖ ≤ M)
    (ho : DifferentiableOn ℂ Go {x | ρ < ‖x‖})
    (hbo : ∃ M : ℝ, ∀ x, 1 ≤ ‖x‖ → ‖Go x‖ ≤ M)
    (heq : ∀ x, ρ < ‖x‖ → ‖x‖ < 1 → G x = Go x) :
    ∀ x y, 0 < ‖x‖ → ‖x‖ < 1 → x ≠ b → 0 < ‖y‖ → ‖y‖ < 1 → y ≠ b → G x = G y := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb0
  set G1 := Function.update G 0 (limUnder (𝓝[≠] (0 : ℂ)) G) with hG1def
  have hG1 : DifferentiableOn ℂ G1 (ball (0 : ℂ) 1 \ {b}) :=
    removable_step (isOpen_ball.sdiff isClosed_singleton)
      ⟨mem_ball_self one_pos, fun h => hb0 (mem_singleton_iff.1 h).symm⟩ hd h0
  have hG1eq : ∀ x, x ≠ 0 → G1 x = G x := fun x hx => Function.update_of_ne hx _ _
  set G2 := Function.update G1 b (limUnder (𝓝[≠] b) G1) with hG2def
  have hG2 : DifferentiableOn ℂ G2 (ball (0 : ℂ) 1) := by
    refine removable_step isOpen_ball (by simpa using lt_of_le_of_lt hbρ hρ) hG1 ?_
    obtain ⟨ε, hε, M, hM⟩ := hbb
    refine ⟨min ε ‖b‖, lt_min hε hbpos, M, fun x hxb hx => ?_⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := lt_of_lt_of_le hx (min_le_right _ _)
      simp at this
    rw [hG1eq x hx0]
    exact hM x hxb (lt_of_lt_of_le hx (min_le_left _ _))
  have hG2eq : ∀ x, x ≠ 0 → x ≠ b → G2 x = G x := fun x hx hxb => by
    rw [hG2def, Function.update_of_ne hxb, hG1eq x hx]
  set Φ : ℂ → ℂ := fun x => if ‖x‖ < 1 then G2 x else Go x with hΦ
  have hΦd : Differentiable ℂ Φ := by
    intro x
    by_cases hx : ‖x‖ < 1
    · have hmem : ball (0 : ℂ) 1 ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa using hx)
      have he : Φ =ᶠ[𝓝 x] G2 := by
        filter_upwards [hmem] with y hy
        have hy' : ‖y‖ < 1 := by simpa using hy
        simp only [hΦ, if_pos hy']
      exact (hG2.differentiableAt hmem).congr_of_eventuallyEq he
    · have hxρ : ρ < ‖x‖ := lt_of_lt_of_le hρ (not_lt.1 hx)
      have hmem : {y : ℂ | ρ < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hxρ
      have he : Φ =ᶠ[𝓝 x] Go := by
        filter_upwards [hmem] with y hy
        have hy' : ρ < ‖y‖ := hy
        by_cases h1 : ‖y‖ < 1
        · have hy0 : y ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (le_trans hbpos.le hbρ) hy')
          have hyb : y ≠ b := fun h => by rw [h] at hy'; linarith
          simp only [hΦ, if_pos h1]
          rw [hG2eq y hy0 hyb, heq y hy' h1]
        · simp only [hΦ, if_neg h1]
      exact (ho.differentiableAt hmem).congr_of_eventuallyEq he
  have hΦb : Bornology.IsBounded (range Φ) := by
    obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      hΦd.continuous.continuousOn
    obtain ⟨M, hM⟩ := hbo
    refine isBounded_iff_forall_norm_le.2 ⟨max C1 M, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : ‖x‖ ≤ 1
    · exact (hC1 x (by simpa using hx)).trans (le_max_left _ _)
    · have h1 : ¬ ‖x‖ < 1 := fun h => hx h.le
      simp only [hΦ, if_neg h1]
      exact (hM x (not_le.1 hx).le).trans (le_max_right _ _)
  intro x y hx0 hx1 hxb hy0 hy1 hyb
  have e := hΦd.apply_eq_apply_of_bounded hΦb x y
  simp only [hΦ, if_pos hx1, if_pos hy1] at e
  rwa [hG2eq x (norm_pos_iff.1 hx0) hxb, hG2eq y (norm_pos_iff.1 hy0) hyb] at e

end Virasoro.Sphere
