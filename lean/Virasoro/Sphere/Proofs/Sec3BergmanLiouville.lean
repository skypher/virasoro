import Virasoro.Sphere.Proofs.Sec3BergmanLiouConst
import Virasoro.Sphere.Proofs.Sec3BergmanSymm

/-!
# Sphere paper Lemma 3.5, Step 2: the formula for `W` (`sphere/paper.tex` l.921–929)

Symmetry `W(x₁,x₂) = W(x₂,x₁)` (from `A₊₊ᵀ = A₊₊`, `A₋₋ᵀ = A₋₋`, `A₊₋ = A₋₊ᵀ`) turns the
`x₁`-independent series of `Stmt_sub_bergman_const` into `2C(z)/Y(x₂)`.

Consumer: `Stmt_sub_bergman_liouville`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

theorem WnoTerm_symm (j : ℕ) (x1 x2 : ℂ) (m n : ℕ) :
    WnoTerm j x1 x2 m n = WnoTerm j x2 x1 n m := by
  unfold WnoTerm
  rw [App_symm m n, Amm_symm m n, ← Apm_eq_Amp_transpose m n, Apm_eq_Amp_transpose n m]
  ring

/-- `W(x₁,x₂) = W(x₂,x₁)` (l.924). -/
theorem Wser_symm (x1 x2 : ℂ) : Wser x1 x2 = Wser x2 x1 := by
  ext j
  rw [Wser, Wser, coeff_mk, coeff_mk, show (x1 - x2) ^ 2 = (x2 - x1) ^ 2 by ring]
  congr 1
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq (fun mn : ℕ × ℕ => WnoTerm j x2 x1 mn.1 mn.2)]
  exact tsum_congr fun mn => WnoTerm_symm j x1 x2 mn.1 mn.2

theorem Sser_symm (x1 x2 : ℂ) : Sser x2 x1 = Sser x1 x2 := by
  unfold Sser
  rw [show x2 * x1 * (x2 + x1) / 2 - x2 * x1 = x1 * x2 * (x1 + x2) / 2 - x1 * x2 by ring,
    show (x2 + x1) / 2 - x2 * x1 = (x1 + x2) / 2 - x1 * x2 by ring]

/-- Step 2 of Lemma 3.5 (l.921–929): the formula for `W` with a series `C(z)`. -/
theorem sub_bergman_liouville_of_const (hC : Stmt_sub_bergman_const) :
    Stmt_sub_bergman_liouville := by
  have hC' : ∀ x2 : ℂ, ∃ c : PowerSeries ℂ, 0 < ‖x2‖ → ‖x2‖ < 1 →
      ∀ x1 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → x1 ≠ x2 →
        Yser x1 * Wser x1 x2 + gser x2 * Sser x1 x2 * C (((x1 - x2) ^ 2)⁻¹) = c := by
    intro x2
    by_cases h : 0 < ‖x2‖ ∧ ‖x2‖ < 1
    · obtain ⟨c, hc⟩ := hC x2 h.1 h.2
      exact ⟨c, fun _ _ => hc⟩
    · exact ⟨0, fun h0 h1 => absurd ⟨h0, h1⟩ h⟩
  choose c hc using hC'
  have hW : ∀ x1 x2 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → 0 < ‖x2‖ → ‖x2‖ < 1 → x1 ≠ x2 →
      Wser x1 x2 = gser x1 * c x2 - gser x1 * gser x2 * Sser x1 x2 * C (((x1 - x2) ^ 2)⁻¹) := by
    intro x1 x2 h10 h11 h20 h21 hne
    have h := hc x2 h20 h21 x1 h10 h11 hne
    have hgY := gser_mul_Yser (norm_pos_iff.1 h10) h11
    linear_combination gser x1 * h - Wser x1 x2 * hgY
  have hK : ∀ x1 x2 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → 0 < ‖x2‖ → ‖x2‖ < 1 → x1 ≠ x2 →
      Yser x2 * c x2 = Yser x1 * c x1 := by
    intro x1 x2 h10 h11 h20 h21 hne
    have e1 := hW x1 x2 h10 h11 h20 h21 hne
    have e2 := hW x2 x1 h20 h21 h10 h11 hne.symm
    rw [Sser_symm, show (x2 - x1) ^ 2 = (x1 - x2) ^ 2 by ring] at e2
    have hs := Wser_symm x1 x2
    have hgY1 := gser_mul_Yser (norm_pos_iff.1 h10) h11
    have hgY2 := gser_mul_Yser (norm_pos_iff.1 h20) h21
    linear_combination Yser x1 * Yser x2 * (-e1 + e2 + hs) - Yser x2 * c x2 * hgY1 +
      Yser x1 * c x1 * hgY2
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have hKall : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → Yser x * c x = Yser (1 / 2) * c (1 / 2) := by
    intro x h0 h1
    by_cases hx : x = 1 / 2
    · rw [hx]
    · exact hK (1 / 2) x (by rw [hn]; norm_num) (by rw [hn]; norm_num) h0 h1 (Ne.symm hx)
  have h2 : (2 : PowerSeries ℂ) * C (-1 / 2 : ℂ) = -1 := by
    rw [← map_ofNat (C (R := ℂ)) 2, ← map_mul]
    norm_num
  refine ⟨C (-1 / 2 : ℂ) * (Yser (1 / 2) * c (1 / 2)), isWFormula_of_eq ?_⟩
  intro x1 x2 h10 h11 h20 h21 hne
  have e1 := hW x1 x2 h10 h11 h20 h21 hne
  have hKx2 := hKall x2 h20 h21
  have hgY2 := gser_mul_Yser (norm_pos_iff.1 h20) h21
  rw [YYinv_eq]
  linear_combination e1 - gser x1 * c x2 * hgY2 + gser x1 * gser x2 * hKx2 +
    gser x1 * gser x2 * (Yser (1 / 2) * c (1 / 2)) * h2

/-- Step 2 of Lemma 3.5 from the three analytic sub-statements. -/
theorem sub_bergman_liouville_of_patches (hH : Stmt_sub_bergman_holo)
    (hI : Stmt_sub_bergman_inner) (hO : Stmt_sub_bergman_outer) : Stmt_sub_bergman_liouville :=
  sub_bergman_liouville_of_const (sub_bergman_const_of_patches hH hI hO)

end Virasoro.Sphere
