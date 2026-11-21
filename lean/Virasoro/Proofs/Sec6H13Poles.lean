import Virasoro.Proofs.Sec6DDeriv
import Virasoro.Statements.Sec6c

/-!
# Proposition 6.8 of `paper.tex` at 70bac53: the first step of part (i)

Paper.tex l.1215–1223: at `d₁ = h_{1,3}(b)` and `d₂ = h_{1,-3}(b)` one has `Λ² = (b ± 3b⁻¹)²`, so
the factor `(k,l) = (1,3)` of `𝒫_{u,v}(b,d_ν)` vanishes for every `v ≥ 2` and `ℛ_{u,v}(b,d_ν) = 0`;
by the generic recursion, `H_M(c(b),Δ,d_ν)` has at most simple poles in `Δ`, all at `h_{u,1}(b)`,
`1 ≤ u ≤ M`: `∏_{u=1}^M (Δ - h_{u,1}(b)) · H_M` is a polynomial in `Δ` of degree at most `M - 1`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `𝒫_{u,v}(b, h_{1,±3}(b)) = 0` for `v ≥ 2`. -/
theorem genP_h13_zero {u v : ℕ} (hu : 1 ≤ u) (hv : 2 ≤ v) (b : 𝔽) :
    genP u v b (kacH 1 3 b) = 0 ∧ genP u v b (kacH 1 (-3) b) = 0 := by
  have h1 : 1 ∈ oddsBelow u :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by norm_num⟩
  have h3 : 3 ∈ oddsBelow v :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by norm_num⟩
  constructor
  · unfold genP
    refine Finset.prod_eq_zero h1 (Finset.prod_eq_zero h3 ?_)
    simp only [lamSq, kacH]
    push_cast
    ring
  · unfold genP
    refine Finset.prod_eq_zero h1 (Finset.prod_eq_zero h3 ?_)
    simp only [lamSq, kacH]
    push_cast
    ring

/-- If `𝒫_{u,v}(b,d) = 0` for all `v ≥ 2`, the generic recursion at level `M ≥ 1` leaves only the
simple poles at `h_{u,1}(b)`, `1 ≤ u ≤ M`. -/
theorem Hrat_simple_poles_of_recursion {b d : 𝔽} {M : ℕ} (hM : 1 ≤ M)
    (hrec : GenericRecursionAt 𝔽 b d M)
    (hP : ∀ u v : ℕ, 1 ≤ u → 2 ≤ v → genP u v b d = 0) :
    ∃ Q : 𝔽[X], Q.natDegree ≤ M - 1 ∧
      algebraMap 𝔽[X] (RatFunc 𝔽) (∏ u ∈ Finset.Icc 1 M, (X - C (kacH (u : ℤ) 1 b))) *
        Hrat (kacC b) d M = algebraMap 𝔽[X] (RatFunc 𝔽) Q := by
  classical
  let cf : Label → 𝔽 := fun a => genR a.1 a.2 b d *
    RatFunc.eval (RingHom.id 𝔽) (kacHL a b + (a.lvl : 𝔽)) (Hrat (kacC b) d (M - a.lvl))
  refine ⟨∑ a ∈ labels M, if a.2 = 1 then
      C (cf a) * ∏ u ∈ (Finset.Icc 1 M).erase a.1, (X - C (kacH (u : ℤ) 1 b)) else 0, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
    obtain ⟨h1, h2, h3⟩ := label_pos ha
    split_ifs with h21
    · have hmem : a.1 ∈ Finset.Icc 1 M := by
        rw [Finset.mem_Icc]
        rw [h21, mul_one] at h3
        omega
      refine le_trans (natDegree_C_mul_le _ _) (le_trans (natDegree_prod_le _ _) ?_)
      refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun u _ => natDegree_X_sub_C_le _) ?_
      rw [Finset.card_erase_of_mem hmem, Nat.card_Icc, smul_eq_mul, mul_one]
      omega
    · simp
  · rw [hrec, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨h1, h2, h3⟩ := label_pos ha
    split_ifs with h21
    · have hmem : a.1 ∈ Finset.Icc 1 M := by
        rw [Finset.mem_Icc]
        rw [h21, mul_one] at h3
        omega
      have hh : kacHL a b = kacH (a.1 : ℤ) 1 b := by
        rw [kacHL, h21]
        rfl
      have hne : (RatFunc.X : RatFunc 𝔽) - RatFunc.C (kacH (a.1 : ℤ) 1 b) ≠ 0 := by
        intro h0
        have h4 : algebraMap 𝔽[X] (RatFunc 𝔽) (X - C (kacH (a.1 : ℤ) 1 b)) = 0 := by
          rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
          exact h0
        exact X_sub_C_ne_zero _ ((map_eq_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).1 h4)
      rw [← Finset.mul_prod_erase _ _ hmem, map_mul, map_mul, map_sub, RatFunc.algebraMap_X,
        RatFunc.algebraMap_C, RatFunc.algebraMap_C, hh]
      show _ = RatFunc.C (genR a.1 a.2 b d * RatFunc.eval (RingHom.id 𝔽)
        (kacHL a b + (a.lvl : 𝔽)) (Hrat (kacC b) d (M - a.lvl))) * _
      rw [map_mul, hh]
      field_simp
    · have hz : genR a.1 a.2 b d = 0 := by
        rw [genR, hP a.1 a.2 h1 (by omega), mul_zero]
      rw [hz, map_zero, zero_div, zero_mul, mul_zero, map_zero]

/-- Frozen sub-statement of Proposition 6.8 (paper.tex l.1181–1183 and l.1218–1265): for
`ν ∈ {1,2}` and `M ≥ 0` the function `P_M^{(ν)}` is a polynomial in `(t, Y)` over `ℚ`.
Demand sheet: the first clause of `Stmt_prop_h13_nonvanishing`, word for word (`ν = 0, 1` stand
for `ν = 1, 2`; variables `0 ↦ t`, `1 ↦ Y`; `P(t, t²Δ) = clearedH ν M` in `ℚ(t)(Δ)`). -/
def Stmt_sub_h13_polynomial : Prop :=
  ∃ P : Fin 2 → ℕ → MvPolynomial (Fin 2) ℚ,
    ∀ ν M, MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (P ν M) = clearedH ν M

end Virasoro
