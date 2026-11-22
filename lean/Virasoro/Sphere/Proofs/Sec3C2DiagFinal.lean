import Virasoro.Sphere.Proofs.Sec3C2Step3Parts

/-!
# Lemma 3.7, Step 3: `U(W_*)^† F_2 = exp(-∑_m (m/16^m) u_m²)` (sphere paper)

sphere/paper.tex l.1140–1149.  The Laurent polynomials `x(X)^{k-1}(X - 1/(16X))`, `k ≥ 1`, span
the `X^m - 16^{-m}X^{-m}`: `(α_m - 16^{-m}α_{-m})(U(W_*)^†F_2) = 0`, that is
`∂_{u_m} Y = -(2m/16^m) u_m Y`.  With `Y_0 = 1` this determines `Y` level by level.
-/

namespace Virasoro.Sphere

open MvPolynomial Finset

section Modes

variable {U : Fock →ₗ[ℂ] HH} (hU : IsDiffeoU U) (hF : Cited_FeiginFuchsOperators)

include hU hF

/-- `(α_m - 16^{-m} α_{-m})(U(W_*)^† F_2) = 0` (sphere/paper.tex l.1140–1143): triangular
induction on `m`, the expansion of `x(X)^{m-1}(X - 1/(16X))` having leading coefficient `1`. -/
theorem modes_rel : ∀ m : ℕ, 1 ≤ m → ∀ n : ℤ,
    alphaOp m (Yz U (n + m)) = (1 / 16 : ℂ) ^ m • alphaOp (-(m : ℤ)) (Yz U (n - m)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm n
    have h := rel hU hF m hm n
    rw [Finset.sum_range_succ, cst_self m hm, one_smul, Finset.sum_eq_zero, zero_add] at h
    · exact sub_eq_zero.mp h
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [cst_zero_right, zero_smul]
      · rw [ih j hj' hj0 n, sub_self, smul_zero]

end Modes

theorem sub_c2_modes (hF : Cited_FeiginFuchsOperators) : Stmt_sub_c2_modes := by
  intro U hU m hm n
  have h := modes_rel hU hF m hm n
  have hA : alphaOp (m : ℤ) = (Complex.I / sqrt2) • dVar m := by
    rw [alphaOp, if_pos (by omega)]
    simp
  have hA' : alphaOp (-(m : ℤ)) = (-(Complex.I * sqrt2 * (m : ℂ))) • uMul m := by
    rw [alphaOp, if_neg (by omega), if_pos (by omega)]
    simp
  rw [hA, hA', LinearMap.smul_apply, LinearMap.smul_apply, uMul_apply, smul_smul] at h
  have hc : Complex.I / sqrt2 ≠ 0 := div_ne_zero Complex.I_ne_zero sqrt2_ne
  have h1 := congrArg (fun z : Fock => (Complex.I / sqrt2)⁻¹ • z) h
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  rw [h1]
  congr 1
  have h2 : sqrt2 / Complex.I * (Complex.I * sqrt2) = 2 := by
    rw [div_mul_eq_mul_div, mul_comm Complex.I, ← mul_assoc, mul_div_assoc,
      div_self Complex.I_ne_zero, mul_one, sqrt2_mul]
  rw [inv_div]
  linear_combination (-((1 / 16 : ℂ) ^ m) * (m : ℂ)) * h2

/-! ### The Gaussian `exp(-∑_m (m/16^m) u_m²)` -/

/-- `exp(-∑_m (m/16^m) u_m²)` as a series. -/
noncomputable def Dgs : MvPowerSeries ℕ+ ℂ := mexp diagExpo

theorem constantCoeff_diagExpo : MvPowerSeries.constantCoeff diagExpo = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show diagExpo 0 = 0
  simp [diagExpo]

theorem diagF_eq_lp (n : ℕ) : diagF n = lp Dgs n := by
  simp [diagF, lp, Dgs]

theorem pdA_diagExpo (m : ℕ) (hm : 1 ≤ m) :
    pdA m diagExpo =
      MvPowerSeries.C (-(2 * (m : ℂ) * (1 / 16 : ℂ) ^ m)) * MvPowerSeries.X m.toPNat' := by
  classical
  ext α
  rw [coeff_pdA, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases h : α = Finsupp.single m.toPNat' 1
  · subst h
    have e : (Finsupp.single m.toPNat' 1 + Finsupp.single m.toPNat' 1 : ℕ+ →₀ ℕ) =
        Finsupp.single m.toPNat' 2 := by
      rw [← Finsupp.single_add]
    rw [if_pos rfl, e, coeff_eq_apply, diagExpo, Finsupp.support_single_ne_zero _ two_ne_zero,
      Finset.sum_singleton, if_pos rfl, Finsupp.single_eq_same, PNat.toPNat'_coe hm]
    push_cast
    rw [one_div, inv_pow]
    ring
  · have h0 : diagExpo (α + Finsupp.single m.toPNat' 1) = 0 := by
      refine Finset.sum_eq_zero fun i _ => if_neg fun h' => h ?_
      have hi : i = m.toPNat' := by
        by_contra hne
        have h1 := congrArg (fun f : ℕ+ →₀ ℕ => f m.toPNat') h'
        simp only [Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_apply, if_neg hne] at h1
        omega
      subst hi
      have h2 : α + Finsupp.single m.toPNat' 1 =
          Finsupp.single m.toPNat' 1 + Finsupp.single m.toPNat' 1 := by
        rw [h', ← Finsupp.single_add]
      exact add_right_cancel h2
    rw [if_neg h, mul_zero, coeff_eq_apply, h0, zero_mul]

theorem dVar_Dgs (m : ℕ) (hm : 1 ≤ m) (i : ℤ) :
    dVar m (lp Dgs (i + m)) =
      (-(2 * (m : ℂ) * (1 / 16 : ℂ) ^ m)) • ((uVar m : Fock) * lp Dgs (i - m)) := by
  have h0 : IsNilpotent (MvPowerSeries.constantCoeff diagExpo) := by
    rw [constantCoeff_diagExpo]
    exact IsNilpotent.zero
  have h1 : pdA m Dgs = MvPowerSeries.C (-(2 * (m : ℂ) * (1 / 16 : ℂ) ^ m)) *
      (MvPowerSeries.X m.toPNat' * Dgs) := by
    rw [Dgs, pdA, pderiv_mexp h0, ← pdA, pdA_diagExpo m hm]
    ring
  rw [dVar_lp m hm, h1, lp_C_mul, uVar_lp m hm]

theorem lp_mem_level (Φ : MvPowerSeries ℕ+ ℂ) (n : ℕ) : lp Φ n ∈ levelSub n := by
  intro γ hγ
  rw [coeff_lp] at hγ
  by_contra hne
  apply hγ
  rw [if_neg]
  intro h
  apply hne
  show lvl γ = n
  omega

/-- A sequence `(Y_n)` with `Y_n` of level `n` is determined by `Y_0` and the equations
`∂_{u_m} Y = c_m u_m Y` (sphere/paper.tex l.1143–1149). -/
theorem gauss_unique (c : ℕ → ℂ) (Y Z : ℤ → Fock)
    (hYl : ∀ n : ℕ, Y n ∈ levelSub n) (hZl : ∀ n : ℕ, Z n ∈ levelSub n)
    (hYn : ∀ i : ℤ, i < 0 → Y i = 0) (hZn : ∀ i : ℤ, i < 0 → Z i = 0) (h0 : Y 0 = Z 0)
    (hY : ∀ m : ℕ, 1 ≤ m → ∀ i : ℤ, dVar m (Y (i + m)) = c m • ((uVar m : Fock) * Y (i - m)))
    (hZ : ∀ m : ℕ, 1 ≤ m → ∀ i : ℤ, dVar m (Z (i + m)) = c m • ((uVar m : Fock) * Z (i - m))) :
    ∀ n : ℕ, Y n = Z n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact_mod_cast h0
    ext γ
    by_cases hγ : γ = 0
    · subst hγ
      have hl : lvl (0 : ℕ+ →₀ ℕ) ≠ n := by
        rw [show lvl (0 : ℕ+ →₀ ℕ) = 0 from map_zero _]
        omega
      rw [coeff_eq_zero_of_level (hYl n) 0 hl, coeff_eq_zero_of_level (hZl n) 0 hl]
    · obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hγ
      have hm1 : 1 ≤ (m : ℕ) := m.pos
      have hprev : Y ((n : ℤ) - (m : ℕ) - (m : ℕ)) = Z ((n : ℤ) - (m : ℕ) - (m : ℕ)) := by
        by_cases hneg : (n : ℤ) - (m : ℕ) - (m : ℕ) < 0
        · rw [hYn _ hneg, hZn _ hneg]
        · obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (n : ℤ) - (m : ℕ) - (m : ℕ) = n' :=
            ⟨((n : ℤ) - (m : ℕ) - (m : ℕ)).toNat, by omega⟩
          rw [hn']
          exact ih n' (by omega)
      have e1 := hY (m : ℕ) hm1 ((n : ℤ) - (m : ℕ))
      have e2 := hZ (m : ℕ) hm1 ((n : ℤ) - (m : ℕ))
      rw [sub_add_cancel] at e1 e2
      rw [hprev, ← e2] at e1
      have e3 := congrArg (coeff (γ - Finsupp.single m 1)) e1
      have e4 : ((m : ℕ)).toPNat' = m := PNat.coe_toPNat' m
      change coeff (γ - Finsupp.single m 1) (pderiv ((m : ℕ)).toPNat' (Y n)) =
        coeff (γ - Finsupp.single m 1) (pderiv ((m : ℕ)).toPNat' (Z n)) at e3
      rw [e4, coeff_pderiv, coeff_pderiv, sub_add_single hm] at e3
      exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) e3

/-- Lemma 3.7, Step 3, first part (sphere/paper.tex l.1111–1149):
`U(W_*)^† F_2(u) = exp(-∑_{m≥1} (m/16^m) u_m²)`. -/
theorem sub_c2_diag (hF : Cited_FeiginFuchsOperators) : Stmt_sub_c2_diag := by
  intro U hU n
  have hY0 : Yz U 0 = 1 := by
    have hT : Tst U 0 = LinearMap.id := by
      rw [Tst, level_zero_eq, Finset.sum_singleton, wpow_zero, one_smul, Udg_zero hU]
    rw [Yz, if_pos le_rfl, Int.toNat_zero, UdagF_eq hU 0, Finset.sum_range_one, hT,
      LinearMap.id_apply, (gaussF_ward 0).1]
  have hZ0 : lp Dgs 0 = 1 := by
    ext γ
    rw [coeff_lp, MvPolynomial.coeff_one]
    by_cases hγ : γ = 0
    · subst hγ
      rw [if_pos (by rw [show lvl (0 : ℕ+ →₀ ℕ) = 0 from map_zero _]; rfl), if_pos rfl, Dgs,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_mexp constantCoeff_diagExpo]
    · rw [if_neg (fun h => hγ (lvl_eq_zero (by exact_mod_cast h))), if_neg (Ne.symm hγ)]
  have key := gauss_unique (fun m => -(2 * (m : ℂ) * (1 / 16 : ℂ) ^ m)) (Yz U) (lp Dgs)
    (fun n => by
      rw [Yz, if_pos (by omega), Int.toNat_natCast]
      exact UdagF_mem_level n)
    (lp_mem_level Dgs)
    (fun i hi => by rw [Yz, if_neg (by omega)])
    (fun i hi => lp_neg_index _ _ hi)
    (by rw [hY0, hZ0])
    (fun m hm i => sub_c2_modes hF U hU m hm i)
    (fun m hm i => dVar_Dgs m hm i) n
  rw [Yz, if_pos (by omega), Int.toNat_natCast] at key
  rw [key, diagF_eq_lp]

end Virasoro.Sphere
