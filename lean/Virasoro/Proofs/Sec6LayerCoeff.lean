import Virasoro.Proofs.Sec5TopNondeg
import Virasoro.Statements.Sec6b

/-!
# Proposition 6.7 of `paper.tex` at 70bac53: reduction to the expansion

The clause "`τ^±_k` vanishes to order exactly `k` at `d = 0`" (paper.tex l.1121) follows from the
expansion `τ^±_k/γ^±_k = c_k (±ρ)^k d^k + O(d^{k+1})` (l.1120) because `γ^±_k ≠ 0`
(Theorem 5.9 at `N = max(ℓ⁺_k, ℓ⁻_k)`), `c_k ≠ 0` and `ρ ≠ 0` (`n₀ ≠ 0` since `p ∤ r`).  The
expansion itself (proof l.1125–1173) is the frozen sub-statement `Stmt_sub_layer_expansion`.
-/

namespace Virasoro

open Verma

/-- Frozen sub-statement of Proposition 6.7 (paper.tex l.1120, proof l.1125–1173): the
coefficients of `d^n`, `n < k`, of `τ^±_k` vanish and the coefficient of `d^k` is
`γ^±_k c_k (±ρ)^k`.
Demand sheet: the hypotheses and the first two clauses for each sign are those of
`Stmt_prop_layer_coefficients`, word for word; the third clause (the coefficient of `d^k` is
nonzero) is omitted. -/
def Stmt_sub_layer_expansion : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k : ℕ, 1 ≤ k →
        let ρ : ℂ := -((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p))
        (∀ xp : Nat.Partition (ellPlus p p' r s k) → ℂ,
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
            (∀ n : ℕ, n < k → (torusPolyForm (kacC b) (kacH r s b) xp).coeff n = 0) ∧
            (torusPolyForm (kacC b) (kacH r s b) xp).coeff k =
              jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp *
                (layerConst k : ℂ) * ρ ^ k) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s k) → ℂ,
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            (∀ n : ℕ, n < k → (torusPolyForm (kacC b) (kacH r s b) xm).coeff n = 0) ∧
            (torusPolyForm (kacC b) (kacH r s b) xm).coeff k =
              jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm *
                (layerConst k : ℂ) * (-ρ) ^ k)

theorem layerConst_ne_zero (k : ℕ) : (layerConst k : ℂ) ≠ 0 := by
  unfold layerConst
  have h1 : 0 < Nat.choose (k - 1) ((k - 1) / 2) := Nat.choose_pos (Nat.div_le_self _ _)
  push_cast
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast h1.ne')

/-- Proposition 6.7 from the expansion and the cited injectivity of the singular embedding
(used through Theorem 5.9 for `γ^±_k ≠ 0`). -/
theorem prop_layer_coefficients_of_sub (hI : Cited_VermaHomInjective)
    (h : Stmt_sub_layer_expansion) : Stmt_prop_layer_coefficients := by
  intro p p' r s b hset wp wm hT k hk
  have hsub := h p p' r s b hset wp wm hT k hk
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hnum : (p' : ℂ) * r - (p : ℂ) * s ≠ 0 := by
    intro h0
    have h1 : p' * r = p * s := by exact_mod_cast sub_eq_zero.1 h0
    have h2 : p ∣ r := (Nat.Coprime.dvd_mul_left hcop).1 ⟨s, h1⟩
    have h3 := Nat.le_of_dvd hr h2
    omega
  have hden : (2 : ℂ) * ((p' : ℂ) - p) ≠ 0 := by
    refine mul_ne_zero two_ne_zero (sub_ne_zero.2 fun h0 => ?_)
    have h1 : p' = p := by exact_mod_cast h0
    rw [h1, Nat.coprime_self] at hcop
    omega
  have hρ : -((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 hnum) hden
  obtain ⟨hnp, hnm⟩ := sub_top_layer_nondeg_of_cited hI p p' r s b hset' wp wm hT k
    (max (ellPlus p p' r s k) (ellMinus p p' r s k)) hk
    (le_trans (min_le_left _ _) (le_max_left _ _)) (ell_max_lt_succ hr hrp hs hsp hk)
  refine ⟨fun xp hxp => ?_, fun xm hxm => ?_⟩
  · obtain ⟨h1, h2⟩ := hsub.1 xp hxp
    refine ⟨h1, h2, ?_⟩
    rw [h2]
    exact mul_ne_zero (mul_ne_zero (hnp xp hxp (le_max_left _ _)).1 (layerConst_ne_zero k))
      (pow_ne_zero k hρ)
  · obtain ⟨h1, h2⟩ := hsub.2 xm hxm
    refine ⟨h1, h2, ?_⟩
    rw [h2]
    exact mul_ne_zero (mul_ne_zero (hnm xm hxm (le_max_right _ _)).1 (layerConst_ne_zero k))
      (pow_ne_zero k (neg_ne_zero.2 hρ))

end Virasoro
