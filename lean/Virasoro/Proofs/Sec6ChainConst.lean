import Virasoro.Proofs.Sec6ChainMoments

/-!
# Proposition 6.7: `[y^k] T_N` as a sum over the first steps (paper.tex l.1139–1141, l.1161–1162)

After the first step `g` of a chain the slopes `ζ_i = ḣ_{g_i}` are constants, so
`T_N(w,y) = ∑_g (w − ḣ_g)⁻¹ · ρ_g y ∏_j(1 − y/(jκ₀)) · (tail of g)` with tails in `ℂ[y]`
(`ChainEval.chainTc`, `ChainEval.chainT_C`), and
`[y^k] T_N = ∑_θ C_θ/(w − ḣ_θ)` over the first steps `θ` (`ChainEval.coeff_chainTN`).
-/

namespace Virasoro.ChainEval

open Polynomial Finset

/-- The sum over the colliding chains of total level `N` from squared momentum `m2` and a
constant slope `ζ` (the recursion of `chainT` over `ℂ`). -/
noncomputable def chainTc (p p' : ℕ) : ℕ → ℕ → ℤ → ℂ → ℂ[X]
  | 0, N, _, _ => if N = 0 then 1 else 0
  | fuel + 1, N, m2, ζ =>
      if N = 0 then 1
      else ∑ g ∈ labels N,
        if ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = m2 then
          C ((ζ - hdotNu p p' g)⁻¹) * resLimit p p' g *
            chainTc p p' fuel (N - g.lvl) (((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2) (hdotNu p p' g)
        else 0

theorem chainT_C (p p' : ℕ) : ∀ (fuel N : ℕ) (m2 : ℤ) (ζ : ℂ),
    chainT p p' fuel N m2 (RatFunc.C ζ) =
      (chainTc p p' fuel N m2 ζ).map (algebraMap ℂ (RatFunc ℂ))
  | 0, N, m2, ζ => by
    rw [chainT, chainTc]
    split_ifs <;> simp
  | fuel + 1, N, m2, ζ => by
    rw [chainT, chainTc]
    split_ifs with hN
    · simp
    · rw [Polynomial.map_sum]
      refine sum_congr rfl fun g _ => ?_
      split_ifs
      · have e : (RatFunc.C ζ - RatFunc.C (hdotNu p p' g))⁻¹ =
            algebraMap ℂ (RatFunc ℂ) ((ζ - hdotNu p p' g)⁻¹) := by
          rw [RatFunc.algebraMap_eq_C, map_inv₀, map_sub]
        rw [chainT_C p p' fuel, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, e]
      · rw [Polynomial.map_zero]

/-- The first steps from squared momentum `m2` at total level `N`. -/
def firstSteps (p p' : ℕ) (N : ℕ) (m2 : ℤ) : Finset Label :=
  (labels N).filter fun g => ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = m2

/-- The tail of the chains after the step `g`, at remaining level `N − ℓ_g`. -/
noncomputable def tailOf (p p' fuel N : ℕ) (g : Label) : ℂ[X] :=
  chainTc p p' fuel (N - g.lvl) (((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2) (hdotNu p p' g)

/-- `C_θ = [y^k](ρ_θ y ∏_j(1 − y/(jκ₀)) · tail)`. -/
noncomputable def pfCoef (p p' n k : ℕ) (g : Label) : ℂ :=
  (resLimit p p' g * tailOf p p' n (n + 1) g).coeff k

/-- `[y^k] T_N = ∑_θ C_θ/(w − ḣ_θ)` over the first steps (paper.tex l.1161–1162). -/
theorem coeff_chainTN (p p' r s n k : ℕ) :
    (chainTN p p' r s (n + 1)).coeff k =
      ∑ g ∈ firstSteps p p' (n + 1) (((p' : ℤ) * r - (p : ℤ) * s) ^ 2),
        RatFunc.C (pfCoef p p' n k g) * (RatFunc.X - RatFunc.C (hdotNu p p' g))⁻¹ := by
  rw [chainTN, chainT, if_neg (Nat.succ_ne_zero n), finset_sum_coeff, firstSteps, sum_filter]
  refine sum_congr rfl fun g _ => ?_
  split_ifs
  · rw [chainT_C, mul_assoc, ← Polynomial.map_mul, coeff_C_mul, coeff_map, pfCoef, tailOf,
      RatFunc.algebraMap_eq_C, mul_comm]
  · rw [coeff_zero]

/-- A chain sum at positive level with no first step vanishes. -/
theorem chainTc_eq_zero (p p' fuel N : ℕ) (m2 : ℤ) (ζ : ℂ) (hN : N ≠ 0)
    (h : ∀ g ∈ labels N, ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 ≠ m2) :
    chainTc p p' fuel N m2 ζ = 0 := by
  cases fuel with
  | zero => rw [chainTc, if_neg hN]
  | succ fuel =>
    rw [chainTc, if_neg hN]
    exact sum_eq_zero fun g hg => if_neg (h g hg)

theorem chainTc_zero_level (p p' fuel : ℕ) (m2 : ℤ) (ζ : ℂ) : chainTc p p' fuel 0 m2 ζ = 1 := by
  cases fuel <;> rw [chainTc, if_pos rfl]

end Virasoro.ChainEval
