import Virasoro.Cited
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.Sec4Irr
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Irreducibility at `c = 1 + 24μ²`, `Δ = λ² + μ²` (sphere paper Lemma 3.2(i))

sphere/paper.tex l.471–480: with `c = 1 + 6Q²`, `Q = b + b⁻¹ = 2μ > 0`, no Kac weight
`h_{r,s} = (Q² - (rb + sb⁻¹)²)/4` equals `λ² + μ²`: for `c ≥ 25`, `b > 0` and `h_{r,s} ≤ 0`; for
`1 < c < 25`, `b = e^{iθ}`, `h_{r,r} ≤ 0` and `h_{r,s} ∉ ℝ` for `r ≠ s`.  Hence `det G_N ≠ 0`.
-/

namespace Virasoro.Sphere

open Polynomial

/-- The parameter `b` with `b + b⁻¹ = 2μ`: `(rb + sb⁻¹)²` is never a negative real number. -/
theorem exists_kac_param (μ : ℝ) (hμ : 0 < μ) :
    ∃ b binv : ℂ, b * binv = 1 ∧ b + binv = 2 * (μ : ℂ) ∧
      ∀ r s : ℕ, 0 < r → 0 < s → ∀ lam : ℝ, 0 < lam →
        ((r : ℂ) * b + (s : ℂ) * binv) ^ 2 ≠ -4 * (lam : ℂ) ^ 2 := by
  by_cases h1 : 1 ≤ μ
  · -- `c ≥ 25`: `b > 0` is real
    have hw : Real.sqrt (μ ^ 2 - 1) ^ 2 = μ ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    refine ⟨((μ + Real.sqrt (μ ^ 2 - 1) : ℝ) : ℂ), ((μ - Real.sqrt (μ ^ 2 - 1) : ℝ) : ℂ),
      ?_, ?_, ?_⟩
    · rw [← Complex.ofReal_mul]
      have : (μ + Real.sqrt (μ ^ 2 - 1)) * (μ - Real.sqrt (μ ^ 2 - 1)) = 1 := by nlinarith
      rw [this, Complex.ofReal_one]
    · push_cast
      ring
    · intro r s _ _ lam hlam heq
      have h2 : (((r : ℝ) * (μ + Real.sqrt (μ ^ 2 - 1)) + (s : ℝ) * (μ - Real.sqrt (μ ^ 2 - 1))) ^ 2
          : ℝ) = -4 * lam ^ 2 := by
        exact_mod_cast heq
      nlinarith [sq_nonneg ((r : ℝ) * (μ + Real.sqrt (μ ^ 2 - 1)) +
        (s : ℝ) * (μ - Real.sqrt (μ ^ 2 - 1))), sq_pos_of_pos hlam]
  · -- `1 < c < 25`: `b = e^{iθ}`
    have hμ1 : μ < 1 := lt_of_not_ge h1
    have hpos : 0 < 1 - μ ^ 2 := by nlinarith
    have hw : Real.sqrt (1 - μ ^ 2) ^ 2 = 1 - μ ^ 2 := Real.sq_sqrt hpos.le
    have hw0 : 0 < Real.sqrt (1 - μ ^ 2) := Real.sqrt_pos.mpr hpos
    refine ⟨⟨μ, Real.sqrt (1 - μ ^ 2)⟩, ⟨μ, -Real.sqrt (1 - μ ^ 2)⟩, ?_, ?_, ?_⟩
    · apply Complex.ext
      · simp only [Complex.mul_re, Complex.one_re]
        nlinarith
      · simp only [Complex.mul_im, Complex.one_im]
        ring
    · apply Complex.ext <;> simp <;> ring
    · intro r s hr hs lam hlam heq
      have hxy : (r : ℂ) * (⟨μ, Real.sqrt (1 - μ ^ 2)⟩ : ℂ) + (s : ℂ) * ⟨μ, -Real.sqrt (1 - μ ^ 2)⟩
          = ⟨((r : ℝ) + s) * μ, ((r : ℝ) - s) * Real.sqrt (1 - μ ^ 2)⟩ := by
        apply Complex.ext <;> simp <;> ring
      have hrhs : -4 * (lam : ℂ) ^ 2 = ((-4 * lam ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hxy, sq, hrhs] at heq
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr
      have hs' : (0 : ℝ) < s := by exact_mod_cast hs
      have hrs : ((r : ℝ) - s) = 0 := by
        have h3 : ((r : ℝ) + s) * μ * (((r : ℝ) - s) * Real.sqrt (1 - μ ^ 2)) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 (by positivity)
        · rcases mul_eq_zero.mp h4 with h5 | h5
          · exact h5
          · exact absurd h5 hw0.ne'
      rw [hrs] at hre
      nlinarith [sq_pos_of_pos hlam, sq_nonneg (((r : ℝ) + s) * μ)]

/-- Lemma 3.2(i), irreducibility: `det G_N(1 + 24μ², λ² + μ²) ≠ 0` for all `N`. -/
theorem gram_det_ne_zero_fock (hK : Cited_KacDeterminant) (μ lam : ℝ) (hμ : 0 < μ)
    (hlam : 0 < lam) (N : ℕ) :
    (gram (1 + 24 * (μ : ℂ) ^ 2) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) N).det ≠ 0 := by
  obtain ⟨b, binv, hb1, hb2, hb3⟩ := exists_kac_param μ hμ
  have hb : b ≠ 0 := left_ne_zero_of_mul_eq_one hb1
  have hinv : b⁻¹ = binv := (eq_inv_of_mul_eq_one_right hb1).symm
  have hc : kacC b = 1 + 24 * (μ : ℂ) ^ 2 := by
    rw [kacC, hinv, hb2]
    ring
  obtain ⟨C₀, hC, hdet⟩ := hK b hb N
  rw [← gramPoly_det_eval, ← hc, hdet, eval_mul, eval_C, eval_prod]
  refine mul_ne_zero hC (Finset.prod_ne_zero_iff.mpr fun a ha => ?_)
  rw [eval_pow, eval_sub, eval_X, eval_C]
  refine pow_ne_zero _ fun h0 => ?_
  obtain ⟨hr, hs⟩ := labels_pos ha
  refine hb3 a.1 a.2 hr hs lam hlam ?_
  have h1 : kacHL a b = ((2 * (μ : ℂ)) ^ 2 - ((a.1 : ℂ) * b + (a.2 : ℂ) * binv) ^ 2) / 4 := by
    rw [kacHL, kacH, hinv, hb2]
    push_cast
    rfl
  rw [h1] at h0
  linear_combination (4 : ℂ) * h0

end Virasoro.Sphere
