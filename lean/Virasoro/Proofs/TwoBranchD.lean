import Virasoro.Proofs.TwoBranchC
import Virasoro.Proofs.Sec7Class
import Virasoro.Proofs.GenericH

/-!
# Proposition 7.7: closure of a two-branch collision

The coefficient of `t⁻¹ (Δ-λ)⁻¹` in the class sum is `∑_i f_i(0)/ζ̇_i`, which vanishes by
Corollary 7.6.  The collision moments are
`Ã_1 = ∑_i (R_{κ_i}(0) Q_i + T_i)`, `Ã_2 = ∑_i ḣ_{κ_i} f_i(0)/ζ̇_i` and `Ã_k = 0` for `k ≥ 3`;
Theorem 4.3 identifies them with the principal part.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

theorem poleTerm_zero (lam : ℂ) (k : ℕ) : poleTerm 0 lam k = 0 := by
  unfold poleTerm
  simp

/-- The expansion of `B_{κ,N}(t)` on a branch at a complex base point. -/
theorem branch_dataC (hK : Cited_KacDeterminant) (hrec : GenericRecursionUniform) {b : ℂ}
    (hb : b ≠ 0) {N : ℕ} {lam : ℂ} {κ τ : Label} (hκ : κ ∈ collClass N b lam)
    (h : TwoBranchHyp b N κ τ) :
    OrdGE (BG (RatFunc.C b : Kd) dvar N κ) (-1) ∧
      (BG (RatFunc.C b : Kd) dvar N κ).coeff (-1)
        = germ0 (RG (RatFunc.C b : Kd) dvar κ) * germ0 (RG (RatFunc.C b : Kd) dvar τ)
            / germDot (zetaG b κ τ) ∧
      (BG (RatFunc.C b : Kd) dvar N κ).coeff 0
        = germ0 (RG (RatFunc.C b : Kd) dvar κ)
            * finitePart (kacC b) (N - κ.lvl) (kacHL κ b + (κ.lvl : ℂ))
          + Tterm b κ τ := by
  obtain ⟨hτlvl, hτmem, huniq, hRκ, hRτ, hζ⟩ := h
  obtain ⟨hκL, -⟩ := mem_collClass.1 hκ
  obtain ⟨hκ1, hκ2, -⟩ := mem_labels.1 hκL
  have hbs : (RatFunc.C b : Kd) ≠ 0 := (_root_.map_ne_zero _).2 hb
  have hcast : ((κ.lvl : ℕ) : Kd) = RatFunc.C ((κ.lvl : ℕ) : ℂ) := (map_natCast _ _).symm
  have huniq' : ∀ g ∈ labels (N - κ.lvl),
      kacHL g (RatFunc.C b : Kd) = kacHL κ (RatFunc.C b : Kd) + ((κ.lvl : ℕ) : Kd) ↔ g = τ := by
    intro g hg
    rw [← huniq g hg, kacHL_ratC, kacHL_ratC, hcast, ← map_add]
    exact RatFunc.C_injective.eq_iff
  have key := branch_data hK hrec hbs dvar hκ1 hκ2 hτmem hτlvl huniq' hRκ hRτ hζ
  rw [kacC_ratC, kacHL_ratC, hcast, ← map_add] at key
  exact key

/-- Proposition 7.7 (`prop:two-branch`), from the Kac determinant formula and the imported
normalization identities. -/
theorem prop_two_branch (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_two_branch := by
  classical
  have hrec := genericRecursionUniform hK hH
  intro b hb N hN lam hlam κ₁ κ₂ τ₁ τ₂ hκ hclass h₁ h₂
  dsimp only
  have hbs : (RatFunc.C b : Kd) ≠ 0 := (_root_.map_ne_zero _).2 hb
  have hκ₁ : κ₁ ∈ collClass N b lam := by rw [hclass]; simp
  have hκ₂ : κ₂ ∈ collClass N b lam := by rw [hclass]; simp
  obtain ⟨hB₁, hB₁m, hB₁0⟩ := branch_dataC hK hrec hb hκ₁ h₁
  obtain ⟨hB₂, hB₂m, hB₂0⟩ := branch_dataC hK hrec hb hκ₂ h₂
  -- the germs `δ_κ`
  have hδ : ∀ κ ∈ collClass N b lam, OrdGE (deltaG (RatFunc.C b : Kd) (pt lam) κ) 1 ∧
      (deltaG (RatFunc.C b : Kd) (pt lam) κ).coeff 1 = germDot (hG (RatFunc.C b : Kd) κ) := by
    intro κ hκ'
    obtain ⟨-, hκlam⟩ := mem_collClass.1 hκ'
    have h1 : pt lam = kacHL κ (RatFunc.C b : Kd) := by rw [kacHL_ratC, hκlam]
    refine ⟨by rw [h1]; exact ordGE_deltaG_one hbs κ, ?_⟩
    unfold deltaG germDot
    rw [HahnSeries.coeff_sub]
    have h2 : (HahnSeries.C (pt lam) : Kd⸨X⸩).coeff 1 = 0 := by
      show (HahnSeries.single (0 : ℤ) (pt lam)).coeff 1 = 0
      exact HahnSeries.coeff_single_of_ne (by norm_num)
    rw [h2, sub_zero]
  have hBall : ∀ a ∈ collClass N b lam, OrdGE (BG (RatFunc.C b : Kd) dvar N a) (-1) := by
    intro a ha
    rw [hclass] at ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hB₁
    · rw [Finset.mem_singleton.1 ha]
      exact hB₂
  -- the moments
  have hA : ∀ k, AtildeC b N lam k
      = (BG (RatFunc.C b : Kd) dvar N κ₁ * deltaG (RatFunc.C b : Kd) (pt lam) κ₁ ^ (k - 1)).coeff 0
        + (BG (RatFunc.C b : Kd) dvar N κ₂
            * deltaG (RatFunc.C b : Kd) (pt lam) κ₂ ^ (k - 1)).coeff 0 := by
    intro k
    unfold AtildeC Atilde
    rw [collClass_ratC, hclass, Finset.sum_pair hκ, HahnSeries.coeff_add]
  have hA1 : AtildeC b N lam 1
      = (BG (RatFunc.C b : Kd) dvar N κ₁).coeff 0 + (BG (RatFunc.C b : Kd) dvar N κ₂).coeff 0 := by
    rw [hA 1]
    simp
  have hA2 : AtildeC b N lam 2
      = (BG (RatFunc.C b : Kd) dvar N κ₁).coeff (-1) * germDot (hG (RatFunc.C b : Kd) κ₁)
        + (BG (RatFunc.C b : Kd) dvar N κ₂).coeff (-1) * germDot (hG (RatFunc.C b : Kd) κ₂) := by
    have e1 := (coeff_mul_two hB₁ (hδ κ₁ hκ₁).1).1
    have e2 := (coeff_mul_two hB₂ (hδ κ₂ hκ₂).1).1
    norm_num at e1 e2
    rw [hA 2]
    simp only [Nat.add_one_sub_one, pow_one]
    rw [e1, e2, (hδ κ₁ hκ₁).2, (hδ κ₂ hκ₂).2]
  have hA3 : ∀ k, 3 ≤ k → AtildeC b N lam k = 0 := by
    intro k hk
    have e : ∀ a ∈ collClass N b lam, (BG (RatFunc.C b : Kd) dvar N a
        * deltaG (RatFunc.C b : Kd) (pt lam) a ^ (k - 1)).coeff 0 = 0 := by
      intro a ha
      refine ((hBall a ha).mul ((hδ a ha).1.pow (k - 1))).coeff_eq_zero ?_
      omega
    rw [hA k, e κ₁ hκ₁, e κ₂ hκ₂, add_zero]
  -- the coefficient of `t⁻¹` of the class sum
  have hcancel : (BG (RatFunc.C b : Kd) dvar N κ₁).coeff (-1)
      + (BG (RatFunc.C b : Kd) dvar N κ₂).coeff (-1) = 0 := by
    set n₀ : ℕ := (labels N).sup (fun a => vhat (RatFunc.C b : Kd) dvar N a) + 1 with hn₀
    have hn : ∀ a ∈ labels N, vhat (RatFunc.C b : Kd) dvar N a < n₀ := by
      intro a ha
      have := Finset.le_sup (f := fun a => vhat (RatFunc.C b : Kd) dvar N a) ha
      omega
    have h1 := class_coeff hbs dvar N (pt lam) (m := -1) (by norm_num) hn
    have h0 := cor_class_regular hrec b hb N hN lam hlam (-1) (by norm_num)
    rw [collClass_ratC] at h1
    have h2 := h1.symm.trans h0
    rw [Finset.sum_eq_single 1] at h2
    · rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · have h3 := RatFunc.C_injective (h2.trans (map_zero _).symm)
        rw [hclass, Finset.sum_pair hκ] at h3
        simpa using h3
      · exact absurd h2 (pow_ne_zero _ (ratFunc_X_sub_C_ne_zero _))
    · intro k hk hk1
      have hk2 : 2 ≤ k := by
        have := (Finset.mem_Icc.1 hk).1
        omega
      rw [Finset.sum_eq_zero, map_zero, zero_div]
      intro a ha
      refine ((hBall a ha).mul ((hδ a ha).1.pow (k - 1))).coeff_eq_zero ?_
      omega
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h
  have hcancel' : germ0 (RG (RatFunc.C b : Kd) dvar κ₁) * germ0 (RG (RatFunc.C b : Kd) dvar τ₁)
        / germDot (zetaG b κ₁ τ₁)
      + germ0 (RG (RatFunc.C b : Kd) dvar κ₂) * germ0 (RG (RatFunc.C b : Kd) dvar τ₂)
        / germDot (zetaG b κ₂ τ₂) = 0 := by
    rw [← hB₁m, ← hB₂m]
    exact hcancel
  refine ⟨hcancel', ?_⟩
  -- Theorem 4.3 identifies the moments with the principal part
  obtain ⟨hmom, -⟩ := confluence_moments hrec hb hN hlam
  have hPP : PP (HN (kacC b) N) (pt lam)
      = ∑ k ∈ Finset.Icc 1 (mstar b N lam), poleTerm (Astar b N lam k) lam k := rfl
  have hstep1 : ∑ k ∈ Finset.Icc 1 (mstar b N lam), poleTerm (Astar b N lam k) lam k
      = ∑ k ∈ Finset.Icc 1 (mstar b N lam + 2), poleTerm (Astar b N lam k) lam k := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) fun k hk hk' => ?_
    have hk1 := Finset.mem_Icc.1 hk
    have hgt : mstar b N lam < k := by
      by_contra hcon
      exact hk' (Finset.mem_Icc.2 ⟨hk1.1, by omega⟩)
    have : Astar b N lam k = 0 := ppCoeff_eq_zero_of_gt _ _ hgt
    rw [this, poleTerm_zero]
  have hstep2 : ∑ k ∈ Finset.Icc 1 (mstar b N lam + 2), poleTerm (Astar b N lam k) lam k
      = ∑ k ∈ ({1, 2} : Finset ℕ), poleTerm (Astar b N lam k) lam k := by
    symm
    refine Finset.sum_subset ?_ fun k hk hk' => ?_
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      exact Finset.mem_Icc.2 (by omega)
    · have hk1 := Finset.mem_Icc.1 hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
      rw [← hmom k hk1.1, hA3 k (by omega), poleTerm_zero]
  rw [hPP, hstep1, hstep2, Finset.sum_pair (by norm_num), ← hmom 1 le_rfl, ← hmom 2 (by norm_num),
    hA1, hA2, hB₁m, hB₂m, hB₁0, hB₂0, add_comm]
  congr 2
  · linear_combination (germDot (hG (RatFunc.C b : Kd) κ₂)) * hcancel'
  · ring

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) : Stmt_prop_two_branch :=
  prop_two_branch hK hH

end Virasoro
