import Virasoro.Proofs.P2Sec13Laurent
import Virasoro.Proofs.P2Sec10Arrows

/-!
# Lemma 13.1, Step 3: the transverse slope along `b = b⋆ + X` (paper.tex l.2966–2970)

`Δ₁(τ) - Δ₂(τ) = ατ + O(τ²)` with `α ≠ 0`.  In the local parameter `X = b - b⋆` the difference
`h_{R₁,S₁}(b⋆+X) - h_{R₂,S₂}(b⋆+X)` vanishes at `X = 0` and its coefficient of `X` is
`((R₂²-R₁²) b⋆² + (R₂S₂-R₁S₁))/b⋆`, which is `2b⋆α` (`τ = X(2b⋆+X)`); it is nonzero by
Lemma 10.3(iv).
-/

namespace Virasoro.P2

open Virasoro PowerSeries

/-- `[X¹](A B) = [X¹]A · B(0)` when `A(0) = 0`. -/
theorem coeff_one_mul_of_constantCoeff_zero {A B : ℂ⟦X⟧} (hA : constantCoeff A = 0) :
    coeff 1 (A * B) = coeff 1 A * constantCoeff B := by
  obtain ⟨A', rfl⟩ := X_dvd_iff.2 hA
  rw [mul_assoc, coeff_succ_X_mul, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    coeff_zero_eq_constantCoeff_apply, map_mul]

/-- The coefficient of `X` in `h_{u₁,v₁}(b+X) - h_{u₂,v₂}(b+X)` at a point where the two weights
agree. -/
theorem coeff_one_hLoc_sub {b : ℂ} (hb : b ≠ 0) (u₁ v₁ u₂ v₂ : ℤ)
    (h0 : kacH u₁ v₁ b = kacH u₂ v₂ b) :
    b * coeff 1 (hLoc u₁ v₁ b - hLoc u₂ v₂ b) =
      ((u₂ : ℂ) ^ 2 - (u₁ : ℂ) ^ 2) * b ^ 2 + ((u₂ : ℂ) * v₂ - (u₁ : ℂ) * v₁) := by
  set B : ℂ⟦X⟧ := bLoc b with hB
  set Bi : ℂ⟦X⟧ := (bLoc b)⁻¹ with hBi
  have hBBi : B * Bi = 1 := bLoc_mul_inv hb
  have h4 : (4 : ℂ⟦X⟧) * C (1 / 4 : ℂ) = 1 := by
    rw [← map_ofNat (C : ℂ →+* ℂ⟦X⟧) 4, ← map_mul]
    norm_num
  have hh : ∀ u v : ℤ, 4 * B ^ 2 * hLoc u v b =
      (B ^ 2 + 1) ^ 2 - ((u : ℂ⟦X⟧) * B ^ 2 + (v : ℂ⟦X⟧)) ^ 2 := by
    intro u v
    have e1 : B * (B + Bi) = B ^ 2 + 1 := by linear_combination hBBi
    have e2 : B * ((u : ℂ⟦X⟧) * B + (v : ℂ⟦X⟧) * Bi) = (u : ℂ⟦X⟧) * B ^ 2 + (v : ℂ⟦X⟧) := by
      linear_combination (v : ℂ⟦X⟧) * hBBi
    rw [← e1, ← e2, hLoc]
    linear_combination
      (B ^ 2 * ((B + Bi) ^ 2 - ((u : ℂ⟦X⟧) * B + (v : ℂ⟦X⟧) * Bi) ^ 2)) * h4
  have hsq : ∀ u v : ℤ, ((u : ℂ⟦X⟧) * B ^ 2 + (v : ℂ⟦X⟧)) ^ 2 =
      C (((u : ℂ) * b ^ 2 + v) ^ 2) + C (4 * (u : ℂ) * b * ((u : ℂ) * b ^ 2 + v)) * X +
        X ^ 2 * (4 * (u : ℂ⟦X⟧) ^ 2 * C b ^ 2 + 2 * (u : ℂ⟦X⟧) * ((u : ℂ⟦X⟧) * C b ^ 2 + (v : ℂ⟦X⟧)) +
          4 * (u : ℂ⟦X⟧) ^ 2 * C b * X + (u : ℂ⟦X⟧) ^ 2 * X ^ 2) := by
    intro u v
    simp only [hB, bLoc, map_add, map_mul, map_pow, map_intCast, map_ofNat]
    ring
  have hc : ∀ (k0 k1 : ℂ) (r : ℂ⟦X⟧), coeff 1 (C k0 + C k1 * X + X ^ 2 * r) = k1 := by
    intro k0 k1 r
    rw [map_add, map_add, coeff_C, coeff_C_mul, coeff_one_X, coeff_X_pow_mul']
    norm_num
  set Dm : ℂ⟦X⟧ := hLoc u₁ v₁ b - hLoc u₂ v₂ b with hDm
  have hD0 : constantCoeff Dm = 0 := by
    rw [hDm, map_sub, constantCoeff_hLoc, constantCoeff_hLoc, h0, sub_self]
  have hE : 4 * B ^ 2 * Dm =
      ((u₂ : ℂ⟦X⟧) * B ^ 2 + (v₂ : ℂ⟦X⟧)) ^ 2 - ((u₁ : ℂ⟦X⟧) * B ^ 2 + (v₁ : ℂ⟦X⟧)) ^ 2 := by
    rw [hDm, mul_sub, hh, hh]
    ring
  have hl : coeff 1 (4 * B ^ 2 * Dm) = 4 * b ^ 2 * coeff 1 Dm := by
    rw [mul_comm, coeff_one_mul_of_constantCoeff_zero hD0, map_mul, map_pow, hB,
      constantCoeff_bLoc, map_ofNat]
    ring
  have hr : coeff 1 (((u₂ : ℂ⟦X⟧) * B ^ 2 + (v₂ : ℂ⟦X⟧)) ^ 2 -
      ((u₁ : ℂ⟦X⟧) * B ^ 2 + (v₁ : ℂ⟦X⟧)) ^ 2) =
      4 * (u₂ : ℂ) * b * ((u₂ : ℂ) * b ^ 2 + v₂) - 4 * (u₁ : ℂ) * b * ((u₁ : ℂ) * b ^ 2 + v₁) := by
    rw [map_sub, hsq u₂ v₂, hsq u₁ v₁, hc, hc]
  rw [hE, hr] at hl
  have hb2 : (4 * b : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hb
  refine mul_left_cancel₀ hb2 ?_
  linear_combination -hl

/-- Lemma 10.3(iv) for the two arrows out of a node, in the form used along `b = b⋆ + X`:
the coefficient of `X` in `Δ₁ - Δ₂` is nonzero (l.2966–2970). -/
theorem slope_ne_zero (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) (k₀ : ℕ) (ε₁ : Bool)
    {R₁ S₁ R₂ S₂ : ℕ}
    (hlab₁ : arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1)) =
      ((R₁ : ℤ), (S₁ : ℤ)))
    (hlab₂ : arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s (!ε₁) (k₀ + 1)) =
      ((R₂ : ℤ), (S₂ : ℤ))) :
    coeff 1 (hLoc R₁ S₁ b - hLoc R₂ S₂ b) ≠ 0 := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 := minimalSetting_b_ne_zero hset
  obtain ⟨-, -, hμ₁, -⟩ := arrow_facts hset ε k₀ ε₁ hlab₁
  obtain ⟨-, -, hμ₂, -⟩ := arrow_facts hset ε k₀ (!ε₁) hlab₂
  -- the squares of `m_i = p'R_i - pS_i` agree
  have hm : ∀ (ε' : Bool) {R S : ℕ},
      arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε' (k₀ + 1)) = ((R : ℤ), (S : ℤ)) →
      ((p' : ℤ) * R - p * S) ^ 2 = nOrb p p' r s ε k₀ ^ 2 := by
    intro ε' R S hlab
    obtain ⟨R', S', -, -, hsum, hdiff, -, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ ε'
    have hL := arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)
    rw [hlab, Prod.mk.injEq] at hL
    obtain ⟨e1, e2⟩ := hL
    rw [e1, e2]
    rcases hdiff with h | h <;> rw [h] <;> ring
  have hm₁ := hm ε₁ hlab₁
  have hm₂ := hm (!ε₁) hlab₂
  -- Lemma 10.3(iv)
  have hiv : ((p' : ℤ) * R₂ - p * S₂) * ((p' : ℤ) * R₂ + p * S₂) -
      ((p' : ℤ) * R₁ - p * S₁) * ((p' : ℤ) * R₁ + p * S₁) ≠ 0 := by
    have h4 := ((lem_bgg_arrows_of_cited hJ hH p p' r s b hset).2 ε k₀).2.2
    cases ε₁
    · have h5 : ((p' : ℤ) * R₁ - p * S₁) * ((p' : ℤ) * R₁ + p * S₁) -
          ((p' : ℤ) * R₂ - p * S₂) * ((p' : ℤ) * R₂ + p * S₂) ≠ 0 :=
        (h4 R₂ S₂ R₁ S₁ hlab₂ hlab₁).2.2.2.1
      intro h6
      exact h5 (by linear_combination -h6)
    · exact (h4 R₁ S₁ R₂ S₂ hlab₁ hlab₂).2.2.2.1
  -- the integer form of the slope
  have hint : (p : ℤ) * ((R₂ : ℤ) * S₂ - (R₁ : ℤ) * S₁) - (p' : ℤ) * ((R₂ : ℤ) ^ 2 - (R₁ : ℤ) ^ 2)
      ≠ 0 := by
    intro h7
    apply hiv
    have : (2 * (p' : ℤ)) * ((p : ℤ) * ((R₂ : ℤ) * S₂ - (R₁ : ℤ) * S₁) -
        (p' : ℤ) * ((R₂ : ℤ) ^ 2 - (R₁ : ℤ) ^ 2)) = 0 := by rw [h7, mul_zero]
    linear_combination -this - hm₂ + hm₁
  intro hs0'
  have hkey := coeff_one_hLoc_sub hb0 R₁ S₁ R₂ S₂ (hμ₁.trans hμ₂.symm)
  rw [hs0', mul_zero] at hkey
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hcast : (((p : ℤ) * ((R₂ : ℤ) * S₂ - (R₁ : ℤ) * S₁) -
      (p' : ℤ) * ((R₂ : ℤ) ^ 2 - (R₁ : ℤ) ^ 2) : ℤ) : ℂ) = 0 := by
    have hb' : b ^ 2 * p = -(p' : ℂ) := by rw [hb]; field_simp
    push_cast
    linear_combination -(p : ℂ) * hkey - (((R₂ : ℂ)) ^ 2 - ((R₁ : ℂ)) ^ 2) * hb'
  exact hint (by exact_mod_cast hcast)

end Virasoro.P2
