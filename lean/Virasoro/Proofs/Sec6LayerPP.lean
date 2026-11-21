import Virasoro.Proofs.Sec6LayerCoeff
import Virasoro.Proofs.Sec5TopLayerFinal
import Virasoro.Proofs.TopTermPoly
import Virasoro.Proofs.LevelComp

/-!
# Proposition 6.7 of `paper.tex` at 70bac53: from the top pole coefficient to `τ^±_k`

Paper.tex l.1146–1148: "with Theorems 5.8, 5.9 and Lemma 6.5 this gives
`[d^k](τ^±_k/γ^±_k) = lim_w w^k [y^k] T_{ℓ^±_k}`".  At `N = ℓ^±_k` the right side of (5.1) is
`τ^±_k/γ^±_k` plus, when `ℓ^∓_k < ℓ^±_k`, the summand `τ^∓_k/γ^∓_k · H_{N-ℓ^∓_k}(c⋆, μ^∓_k, d)`,
which is `O(d^{k+1})` because `H_M(c⋆, μ, 0) = 0` for `M ≥ 1` (Lemma 6.5) and `τ^∓_k = O(d^k)` (the
statement at the smaller of the two levels).  So the expansion of `τ^±_k` follows from the
expansion of the coefficient of `(Δ-λ)^{-k}` of `H_{ℓ^±_k}(c⋆,Δ,d)` in powers of `d`, which is
the frozen sub-statement `Stmt_sub_layer_pp`.
-/

namespace Virasoro

open Verma Polynomial

/-- Frozen sub-statement of Proposition 6.7 (paper.tex l.1125–1173, without the last sentence of
the first paragraph of the proof): for `N = ℓ^±_k`, the coefficient of `(Δ-λ)^{-k}` of
`H_N(c⋆,Δ,d)` is a polynomial in `d` whose coefficients of `d^n`, `n < k`, vanish and whose
coefficient of `d^k` is `c_k (±ρ)^k`.

Demand sheet.
- `MinimalSetting`, every `k ≥ 1`, both signs, `N = ℓ^±_k` exactly (l.1147–1148 uses
  `T_{ℓ^±_k}` only);
- the coefficient of `(Δ-λ)^{-k}` over `ℂ(d)` is `ppCoeff`; "polynomial in `d`": it is the image
  of some `A ∈ ℂ[d]` (used to read off coefficients of `d^n`);
- `[d^n]A = 0` for `n < k`: used for `τ^±_k = O(d^k)` (l.1120);
- `[d^k]A = c_k (±ρ)^k`, `ρ = -n₀/(2(p'-p))`: identity (l.1120, l.1171–1173);
- no singular vector appears: the statement concerns `H_N` at `c⋆` only. -/
def Stmt_sub_layer_pp : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ k : ℕ, 1 ≤ k →
    let ρ : ℂ := -((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p))
    (∃ A : ℂ[X],
      ppCoeff (HN (kacC b) (ellPlus p p' r s k)) (pt (kacH r s b)) k = algebraMap ℂ[X] Kd A ∧
      (∀ n : ℕ, n < k → A.coeff n = 0) ∧ A.coeff k = (layerConst k : ℂ) * ρ ^ k) ∧
    (∃ A : ℂ[X],
      ppCoeff (HN (kacC b) (ellMinus p p' r s k)) (pt (kacH r s b)) k = algebraMap ℂ[X] Kd A ∧
      (∀ n : ℕ, n < k → A.coeff n = 0) ∧ A.coeff k = (layerConst k : ℂ) * (-ρ) ^ k)

set_option maxHeartbeats 800000 in
/-- The expansion of `τ^±_k` from the expansion of the top pole coefficient of `H_{ℓ^±_k}`, by
Theorem 5.9 (through the cited injectivity of the singular embedding) and Lemma 6.5 at
`(c⋆, μ^∓_k)`. -/
theorem sub_layer_expansion_of_pp (hI : Cited_VermaHomInjective) (h : Stmt_sub_layer_pp) :
    Stmt_sub_layer_expansion := by
  intro p p' r s b hset wp wm hT k hk
  obtain ⟨⟨Ap, hAp, hAp0, hApk⟩, ⟨Am, hAm, hAm0, hAmk⟩⟩ := h p p' r s b hset k hk
  have top := thm_top_layer_of_cited hI p p' r s b hset wp wm hT k
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  have hmax := ell_max_lt_succ hr hrp hs hsp hk
  have hsing := hT.1 k hk
  have tP := top (ellPlus p p' r s k) hk (min_le_left _ _)
    (lt_of_le_of_lt (le_max_left _ _) hmax)
  have tM := top (ellMinus p p' r s k) hk (min_le_right _ _)
    (lt_of_le_of_lt (le_max_right _ _) hmax)
  have hcp : pbwCoord (ellPlus p p' r s k) (comp (ellPlus p p' r s k) (wp k)) = wp k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero hsing.1.2.1)
  have hcm : pbwCoord (ellMinus p p' r s k) (comp (ellMinus p p' r s k) (wm k)) = wm k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero hsing.2.2.1)
  have plus : ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
      (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
      pbwCoord (ellPlus p p' r s k) xp = wp k → pbwCoord (ellMinus p p' r s k) xm = wm k →
      (ellMinus p p' r s k < ellPlus p p' r s k →
        ∀ n < k, (torusPolyForm (kacC b) (kacH r s b) xm).coeff n = 0) →
      (∀ n < k, (torusPolyForm (kacC b) (kacH r s b) xp).coeff n = 0) ∧
        (torusPolyForm (kacC b) (kacH r s b) xp).coeff k =
          jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp * Ap.coeff k := by
    intro xp xm hxp hxm hτ
    refine tau_coeffs_of_pp _ _ k hne xp xm (tP.2.1 xp hxp le_rfl).1
      (fun hle => (tP.2.2.1 xm hxm hle).2.1) hτ Ap ?_ hAp0
    rw [← hAp]
    exact (tP.2.2.2 xp xm hxp hxm).2
  have minus : ∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
      (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
      pbwCoord (ellPlus p p' r s k) xp = wp k → pbwCoord (ellMinus p p' r s k) xm = wm k →
      (ellPlus p p' r s k < ellMinus p p' r s k →
        ∀ n < k, (torusPolyForm (kacC b) (kacH r s b) xp).coeff n = 0) →
      (∀ n < k, (torusPolyForm (kacC b) (kacH r s b) xm).coeff n = 0) ∧
        (torusPolyForm (kacC b) (kacH r s b) xm).coeff k =
          jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm * Am.coeff k := by
    intro xp xm hxp hxm hτ
    refine tau_coeffs_of_pp _ _ k hne.symm xm xp (tM.2.2.1 xm hxm le_rfl).1
      (fun hle => (tM.2.1 xp hxp hle).2.1) hτ Am ?_ hAm0
    rw [← hAm, add_comm]
    exact (tM.2.2.2 xp xm hxp hxm).2
  have mS : ellMinus p p' r s k < ellPlus p p' r s k → ∀ n < k,
      (torusPolyForm (kacC b) (kacH r s b)
        (comp (ellMinus p p' r s k) (wm k))).coeff n = 0 := fun hlt' =>
    (minus _ _ hcp hcm fun h2 => absurd h2 (lt_asymm hlt')).1
  have pS : ellPlus p p' r s k < ellMinus p p' r s k → ∀ n < k,
      (torusPolyForm (kacC b) (kacH r s b)
        (comp (ellPlus p p' r s k) (wp k))).coeff n = 0 := fun hlt' =>
    (plus _ _ hcp hcm fun h2 => absurd h2 (lt_asymm hlt')).1
  refine ⟨fun xp hxp => ?_, fun xm hxm => ?_⟩
  · have h1 := plus xp _ hxp hcm mS
    refine ⟨h1.1, ?_⟩
    rw [h1.2, hApk, mul_assoc]
  · have h1 := minus _ xm hcp hxm pS
    refine ⟨h1.1, ?_⟩
    rw [h1.2, hAmk, mul_assoc]

/-- Proposition 6.7 from the expansion of the top pole coefficient. -/
theorem prop_layer_coefficients_of_pp (hI : Cited_VermaHomInjective) (h : Stmt_sub_layer_pp) :
    Stmt_prop_layer_coefficients :=
  prop_layer_coefficients_of_sub hI (sub_layer_expansion_of_pp hI h)

end Virasoro
