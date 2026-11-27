import Virasoro.Proofs.Sec8BRec
import Virasoro.Proofs.Sec8BSpec
import Virasoro.Proofs.Sec8DiagLambda
import Virasoro.Proofs.Sec5Sharp
import Virasoro.Proofs.TwoBranchA
import Virasoro.Proofs.Sec6H13Label

/-!
# Section 8.2: Theorem 8.11(iii), and Theorem 8.11

(7.8) at the weight `μ_i`, which lies in `Kac_N(b⋆)` as the weight of the label to `μ_{i+1}`.  By
Lemma 8.10 the chains from `μ_i` end at nodes `μ_{i+m}`, and `c^{(k')}_{μ_i→μ_{i+m},j}(b⋆) = 0`
when `k' + j > m`; only `m ≤ D` occurs, and for `k' = D` only `μ_{i+D}` with `j = 0` remains.  If
`N = Δ_D` this is the first term of (7.8) and `H_0 = 1`.  Otherwise the zeros of the Kac
determinant at the level `M = N - Δ_D` and the weight `μ_{i+D}` are labels from `μ_{i+D}`, of level
at least `Δ_{D+1} - Δ_D > M`, so `H_M(c⋆,·)` is regular at `μ_{i+D}` with value
`H_M(c⋆, μ_{i+D}, d)`; as `det G_M(c⋆, μ_{i+D}) ≠ 0` and `μ_{i+D}` has integer momentum, it is a
nonzero polynomial in `d` by Proposition 9.2(iii).  At a specialized `d` the Laurent coefficients of
`H_N(c⋆,·,d₀)` at `μ_i` are the values at `d₀` of the polynomials whose images are those over
`ℂ(d)` (`ChainLim.ppCoeff_HN`, `ChainLim.ppCoeff_Hrat`).
-/

namespace Virasoro

open scoped LaurentSeries Polynomial
open Polynomial

variable {p p' x₀ : ℕ} {b : ℂ}

/-- `H_M(c⋆, d_m, d) ≢ 0` at a weight of momentum form, from Proposition 9.2(iii) (the momentum
version of `HpolyD_ne_zero_min`). -/
theorem HpolyD_ne_zero_mom (h68 : Stmt_prop_h13_nonvanishing) {p p' : ℕ} {b : ℂ} (hp : 2 ≤ p)
    (hp' : 2 ≤ p') (hcop : Nat.Coprime p p') (hb : b ^ 2 = -(p' : ℂ) / p) (m : ℤ) {M : ℕ}
    (hdet : (gram (kacC b) (momWt p p' m) M).det ≠ 0) :
    HpolyD (kacC b) (momWt p p' m) M ≠ 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · intro h0
    have h1 := eval_HpolyD (kacC b) (momWt p p' m) 0 0
    rw [h0, Hval_level_zero] at h1
    simp at h1
  · obtain ⟨P, -, -, -, h3, -⟩ := h68
    have h4 := h3 p p' hp hp' hcop M m hM
    have hmw : momWt p p' m =
        (((((m : ℚ)) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p') : ℚ) : ℂ) := by
      unfold momWt
      push_cast
      rfl
    rw [kacC_min (by omega) (by omega) hb, hmw] at hdet ⊢
    have hg := gram_map (Rat.castHom ℂ) (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M
    have hd := (RingHom.map_det (Rat.castHom ℂ) (gram (1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p'))
      (((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')) M)).symm
    have hq := (h4 fun h0 => hdet (by
      change (gram (Rat.castHom ℂ _) (Rat.castHom ℂ _) M).det = 0
      rw [hg]
      exact hd.trans (by rw [h0, map_zero]))).1
    change HpolyD (Rat.castHom ℂ _) (Rat.castHom ℂ _) M ≠ 0
    rw [HpolyD_map]
    exact (Polynomial.map_ne_zero_iff (Rat.castHom ℂ).injective).2 hq

section Pole

variable (hB : BoundarySetting p p' x₀ b)
include hB

/-- The chain values from `μ_i` to a point of level `n` vanish at `b⋆` unless the point is a node
`μ_m` with `m - i ≥ k' + j`. -/
theorem b_cval_zero {i n k' j : ℕ} (hk : 1 ≤ k')
    (hno : ∀ m : ℕ, i < m → bLev p p' x₀ m = bLev p p' x₀ i + n → m - i < k' + j) :
    (chainFnC b (bWt p p' x₀ i) n k' j).coeff 0 = 0 := by
  by_cases hex : ∃ m : ℕ, i < m ∧ bLev p p' x₀ m = bLev p p' x₀ i + n
  · obtain ⟨m, him, hml⟩ := hex
    have hz := b_chain_coeff_zero hB him k' j hk (hno m him hml)
    unfold bChain at hz
    rwa [show bLev p p' x₀ m - bLev p p' x₀ i = n by omega] at hz
  · push_neg at hex
    rw [b_chainFn_dead hB i n k' j (fun m hm => hex m hm), HahnSeries.coeff_zero]

theorem b_le_of_lev {i m D n : ℕ} (hml : bLev p p' x₀ m = bLev p p' x₀ i + n)
    (hn : n < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ i) : m ≤ i + D := by
  by_contra hc
  have := (bLev_strictMono hB).monotone (show i + D + 1 ≤ m by omega)
  omega

/-- The right side of (7.8) at `μ_i` for `k' ≥ D`, below the level of `μ_{i+D+1}`. -/
theorem b_fc_rhs {i D N J k' : ℕ} (hD : 1 ≤ D) (hJ : 1 ≤ J) (hk : D ≤ k')
    (hN2 : N < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ i) :
    fixedChargeRHS b N (bWt p p' x₀ i) k' J =
      (if k' = D ∧ bLev p p' x₀ (i + D) - bLev p p' x₀ i = N then bTop p p' x₀ b i (i + D)
        else 0) +
      (if k' = D ∧ bLev p p' x₀ (i + D) - bLev p p' x₀ i < N then
        bTop p p' x₀ b i (i + D) *
          lcoeff (HN (kacC b) (N - (bLev p p' x₀ (i + D) - bLev p p' x₀ i)))
            (pt (bWt p p' x₀ (i + D))) 0
      else 0) := by
  have hmono := bLev_strictMono hB
  have hlt : bLev p p' x₀ i < bLev p p' x₀ (i + D) := hmono (by omega)
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, bLev p p' x₀ (i + D) - bLev p p' x₀ i = Δ := ⟨_, rfl⟩
  rw [hΔ]
  have hw : bWt p p' x₀ i + (Δ : ℂ) = bWt p p' x₀ (i + D) := by
    rw [bWt_add_lev hB (i + D), bWt_add_lev hB i, ← hΔ, Nat.cast_sub hlt.le]; ring
  have htop : bTop p p' x₀ b i (i + D) = (chainFnC b (bWt p p' x₀ i) Δ D 0).coeff 0 := by
    simp only [bTop, bChain, Nat.add_sub_cancel_left, hΔ]
  unfold fixedChargeRHS
  congr 1
  · split_ifs with h
    · rw [htop, h.1, h.2]
    · refine b_cval_zero hB (by omega) fun m him hml => ?_
      have hm := b_le_of_lev hB hml hN2
      by_contra hc
      have hmD : m = i + D := by omega
      subst hmD
      exact h ⟨by omega, by omega⟩
  · have hF : ∀ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
        (chainFnC b (bWt p p' x₀ i) n k' j).coeff 0 *
          ((j.factorial : Kd) * lcoeff (HN (kacC b) (N - n)) (pt (bWt p p' x₀ i + n)) j) =
        if n = Δ then (if k' = D then bTop p p' x₀ b i (i + D) *
          lcoeff (HN (kacC b) (N - Δ)) (pt (bWt p p' x₀ (i + D))) 0 else 0) else 0 := by
      intro n hn
      rw [Finset.mem_Ioo] at hn
      by_cases hnΔ : n = Δ
      · rw [if_pos hnΔ, hnΔ]
        by_cases hkD : k' = D
        · rw [if_pos hkD, Finset.sum_eq_single 0]
          · rw [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, hw, hkD, ← htop]
          · intro j _ hj0
            have hz : (chainFnC b (bWt p p' x₀ i) Δ k' j).coeff 0 = 0 :=
              b_cval_zero hB (by omega) fun m him hml => by
                have : m = i + D := hmono.injective (by omega)
                omega
            rw [hz, zero_mul]
          · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
        · rw [if_neg hkD]
          refine Finset.sum_eq_zero fun j _ => ?_
          have hz : (chainFnC b (bWt p p' x₀ i) Δ k' j).coeff 0 = 0 :=
            b_cval_zero hB (by omega) fun m him hml => by
              have : m = i + D := hmono.injective (by omega)
              omega
          rw [hz, zero_mul]
      · rw [if_neg hnΔ]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hz : (chainFnC b (bWt p p' x₀ i) n k' j).coeff 0 = 0 :=
          b_cval_zero hB (by omega) fun m him hml => by
            have hm := b_le_of_lev hB hml (show n < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ i by omega)
            have : m ≠ i + D := by rintro rfl; exact hnΔ (by omega)
            omega
        rw [hz, zero_mul]
    rw [Finset.sum_congr rfl hF, Finset.sum_ite_eq' (Finset.Ioo 0 N) Δ]
    by_cases h1 : k' = D ∧ Δ < N
    · rw [if_pos (Finset.mem_Ioo.2 ⟨by omega, h1.2⟩), if_pos h1.1, if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : Δ ∈ Finset.Ioo 0 N
      · rw [if_pos h2, if_neg (fun hk => h1 ⟨hk, (Finset.mem_Ioo.1 h2).2⟩)]
      · rw [if_neg h2]

/-- `μ_i ∈ Kac_N(b⋆)` as the weight of the label to `μ_{i+1}`. -/
theorem b_lam_mem {i N : ℕ} (hN : bLev p p' x₀ (i + 1) - bLev p p' x₀ i ≤ N) :
    bWt p p' x₀ i ∈ Lam N b := by
  obtain ⟨h1, h2, -, -⟩ := bLabel_xy hB (show i < i + 1 by omega)
  obtain ⟨hw, -⟩ := (label_iff hB (show i < i + 1 by omega) _ h1 h2).2 rfl
  have hl := lvl_bLabel hB (show i < i + 1 by omega)
  exact Finset.mem_image.2 ⟨bLabel p p' x₀ i (i + 1), mem_labels_iff.2 ⟨h1, h2, by omega⟩, hw⟩

/-- No label of level at most `M < Δ_{D+1} - Δ_D` has the weight `μ_{i+D}`. -/
theorem b_no_label {i D M : ℕ}
    (hM : M < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ (i + D)) :
    ∀ g ∈ labels M, kacHL g b ≠ bWt p p' x₀ (i + D) := by
  intro g hg hw
  rw [mem_labels_iff] at hg
  obtain ⟨m, hm, hw'⟩ := label_leads hB (i + D) g (by omega) (by omega) hw
  have e1 := bWt_add_lev hB m
  have e2 := bWt_add_lev hB (i + D)
  have hc : (bLev p p' x₀ m : ℂ) = bLev p p' x₀ (i + D) + g.lvl := by
    linear_combination -e1 + e2 - hw' + hw
  have hnat : bLev p p' x₀ m = bLev p p' x₀ (i + D) + g.lvl := by exact_mod_cast hc
  have := (bLev_strictMono hB).monotone (show i + D + 1 ≤ m by omega)
  omega

/-- `H_M(c⋆,·)` is regular at `μ_{i+D}` for `M < Δ_{D+1} - Δ_D`: the coefficient of `(Δ - μ)⁰`
is the value. -/
theorem b_reg_lcoeff (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i D M : ℕ}
    (hM1 : 1 ≤ M) (hM : M < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ (i + D)) :
    lcoeff (HN (kacC b) M) (pt (bWt p p' x₀ (i + D))) 0 =
      evalAt (pt (bWt p p' x₀ (i + D))) (HN (kacC b) M) := by
  have hb0 := b_ne_zero_of (bSetting_minimal hB)
  have hpf := ((thm_fixed_charge_of_cited hK hH) b hb0 M hM1).2.1
  have hz : ∀ lam' ∈ Lam M b, pt (bWt p p' x₀ (i + D)) ≠ pt lam' := by
    intro lam' hlam' heq
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hlam'
    exact b_no_label hB hM g hg (RatFunc.C_injective heq).symm
  rw [hpf]
  unfold PP
  exact (evalAt_eq_lcoeff_zero (Lam M b) (fun lam' => pt lam')
    (fun lam' => poleOrder (HN (kacC b) M) (pt lam'))
    (fun lam' k => ppCoeff (HN (kacC b) M) (pt lam') k) hz).symm

/-- `H_M(c⋆, μ_{i+D}, d)` is the image of the nonzero polynomial `HpolyD` for
`M < Δ_{D+1} - Δ_D`. -/
theorem b_val_ne (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i D M : ℕ}
    (hM : M < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ (i + D)) :
    evalAt (pt (bWt p p' x₀ (i + D))) (HN (kacC b) M) =
        algebraMap ℂ[X] Kd (HpolyD (kacC b) (bWt p p' x₀ (i + D)) M) ∧
      HpolyD (kacC b) (bWt p p' x₀ (i + D)) M ≠ 0 := by
  have hb0 := b_ne_zero_of (bSetting_minimal hB)
  have hdet : ∀ M' ≤ M, (gram (kacC b) (bWt p p' x₀ (i + D)) M').det ≠ 0 := fun M' hM' =>
    gram_det_ne_of_labels hK hb0 fun g hg => b_no_label hB (show M' < _ by omega) g hg
  have hdetK : ∀ M' ≤ M, (gram (RatFunc.C (kacC b) : Kd) (pt (bWt p p' x₀ (i + D))) M').det ≠ 0 := by
    intro M' hM'
    have hg : gram (RatFunc.C (kacC b) : Kd) (pt (bWt p p' x₀ (i + D))) M' =
        (gram (kacC b) (bWt p p' x₀ (i + D)) M').map (RatFunc.C : ℂ →+* Kd) :=
      gram_map (RatFunc.C : ℂ →+* Kd) (kacC b) (bWt p p' x₀ (i + D)) M'
    have hd : ((gram (kacC b) (bWt p p' x₀ (i + D)) M').map (RatFunc.C : ℂ →+* Kd)).det =
        (RatFunc.C : ℂ →+* Kd) (gram (kacC b) (bWt p p' x₀ (i + D)) M').det :=
      (RingHom.map_det (RatFunc.C : ℂ →+* Kd) (gram (kacC b) (bWt p p' x₀ (i + D)) M')).symm
    rw [hg, hd]
    exact (map_ne_zero (RatFunc.C : ℂ →+* Kd)).2 (hdet M' hM')
  refine ⟨?_, ?_⟩
  · have hev : evalAt (pt (bWt p p' x₀ (i + D))) (HN (kacC b) M) =
        Hval (RatFunc.C (kacC b) : Kd) dvar (pt (bWt p p' x₀ (i + D))) M :=
      evalAt_Hrat hdetK
    rw [hev, Hval_Kd]
  · obtain ⟨hp, hp', hcop, -, -, -, hb⟩ := hB
    exact HpolyD_ne_zero_mom (prop_h13_nonvanishing_of_cited hK hH) hp hp' hcop hb _
      (hdet M le_rfl)

end Pole

/-- Theorem 8.11(iii). -/
theorem b_thm_iii (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hB : BoundarySetting p p' x₀ b) {i D N : ℕ} (hD : 1 ≤ D)
    (hN1 : bLev p p' x₀ (i + D) - bLev p p' x₀ i ≤ N)
    (hN2 : N < bLev p p' x₀ (i + D + 1) - bLev p p' x₀ i) :
    (∀ k' : ℕ, D < k' → Astar b N (bWt p p' x₀ i) k' = 0) ∧
      Astar b N (bWt p p' x₀ i) D =
        bTop p p' x₀ b i (i + D) *
          RatFunc.eval (RingHom.id Kd) (pt (bWt p p' x₀ (i + D)))
            (HN (kacC b) (N - (bLev p p' x₀ (i + D) - bLev p p' x₀ i))) ∧
      Astar b N (bWt p p' x₀ i) D ≠ 0 ∧
      poleOrder (HN (kacC b) N) (pt (bWt p p' x₀ i)) = D ∧
      ∃ P : ℂ[X], algebraMap ℂ[X] Kd P = Astar b N (bWt p p' x₀ i) D ∧
        ∀ d₀ : ℂ, poleOrder (Hrat (kacC b) d₀ N) (bWt p p' x₀ i) ≤ D ∧
          (poleOrder (Hrat (kacC b) d₀ N) (bWt p p' x₀ i) = D ↔ P.eval d₀ ≠ 0) := by
  have hb0 := b_ne_zero_of (bSetting_minimal hB)
  have hmono := bLev_strictMono hB
  have h01 : bLev p p' x₀ i < bLev p p' x₀ (i + 1) := hmono (by omega)
  have h1D : bLev p p' x₀ (i + 1) ≤ bLev p p' x₀ (i + D) := hmono.monotone (by omega)
  have hDD : bLev p p' x₀ (i + D) < bLev p p' x₀ (i + D + 1) := hmono (by omega)
  have hN : 1 ≤ N := by omega
  have hlam : bWt p p' x₀ i ∈ Lam N b := b_lam_mem hB (by omega)
  have hfc := (thm_fixed_charge_of_cited hK hH) b hb0 N hN
  have hA : ∀ k' : ℕ, D ≤ k' → Astar b N (bWt p p' x₀ i) k' =
      (if k' = D ∧ bLev p p' x₀ (i + D) - bLev p p' x₀ i = N then bTop p p' x₀ b i (i + D)
        else 0) +
      (if k' = D ∧ bLev p p' x₀ (i + D) - bLev p p' x₀ i < N then
        bTop p p' x₀ b i (i + D) *
          lcoeff (HN (kacC b) (N - (bLev p p' x₀ (i + D) - bLev p p' x₀ i)))
            (pt (bWt p p' x₀ (i + D))) 0
      else 0) := by
    intro k' hk
    obtain ⟨J₀, hJ₀⟩ := (hfc.1 (bWt p p' x₀ i) hlam k' (by omega)).2
    rw [hJ₀ (max J₀ 1) (le_max_left _ _), b_fc_rhs hB hD (le_max_right _ _) hk hN2]
  have hTop := (b_thm_i hB hK hH (show i < i + D by omega)).2.2
  have hvan : ∀ k' : ℕ, D < k' → Astar b N (bWt p p' x₀ i) k' = 0 := by
    intro k' hk
    rw [hA k' hk.le, if_neg (fun h => absurd h.1 (by omega)),
      if_neg (fun h => absurd h.1 (by omega)), add_zero]
  have hval : Astar b N (bWt p p' x₀ i) D =
      bTop p p' x₀ b i (i + D) *
        RatFunc.eval (RingHom.id Kd) (pt (bWt p p' x₀ (i + D)))
          (HN (kacC b) (N - (bLev p p' x₀ (i + D) - bLev p p' x₀ i))) := by
    rw [hA D le_rfl]
    rcases eq_or_lt_of_le hN1 with hEq | hLt
    · rw [if_pos ⟨rfl, hEq⟩, if_neg (fun h => absurd h.2 (by omega)), add_zero, hEq,
        Nat.sub_self, HN_zero]
      simp
    · rw [if_neg (fun h => absurd h.2 (by omega)), if_pos ⟨rfl, hLt⟩, zero_add]
      congr 1
      exact b_reg_lcoeff hB hK hH (by omega) (by omega)
  have hne : Astar b N (bWt p p' x₀ i) D ≠ 0 := by
    rw [hval]
    refine mul_ne_zero hTop ?_
    have hv := b_val_ne hB hK hH (i := i) (D := D)
      (M := N - (bLev p p' x₀ (i + D) - bLev p p' x₀ i)) (by omega)
    change evalAt _ _ ≠ 0
    rw [hv.1]
    exact (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] Kd)).2 hv.2
  have hle : poleOrder (HN (kacC b) N) (pt (bWt p p' x₀ i)) ≤ D :=
    poleOrder_le_of_ppCoeff fun k hk => hvan k hk
  have hpo : poleOrder (HN (kacC b) N) (pt (bWt p p' x₀ i)) = D :=
    poleOrder_eq_of_ppCoeff_ne hle hne
  -- the specialized `d`
  obtain ⟨T₁, hT, hT0⟩ := ChainLim.kac_taylor hK hb0 (bWt p p' x₀ i) N
  obtain ⟨Pk, hPk⟩ : ∃ Pk : ℕ → ℂ[X], Pk = fun k =>
      if k ≤ ChainLim.eRes b (bWt p p' x₀ i) N then
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (ChainLim.eRes b (bWt p p' x₀ i) N - k),
          (ChainLim.numP (kacC b) (bWt p p' x₀ i) N).coeff x.1 *
            C (PowerSeries.coeff x.2 ((T₁ : PowerSeries ℂ)⁻¹))
      else 0 := ⟨_, rfl⟩
  have hKd : ∀ k, Astar b N (bWt p p' x₀ i) k = algebraMap ℂ[X] Kd (Pk k) := by
    intro k
    rw [hPk]
    exact ChainLim.ppCoeff_HN (kacC b) (bWt p p' x₀ i) N k _ T₁ hT hT0
  have hCd : ∀ (d₀ : ℂ) (k : ℕ), ppCoeff (Hrat (kacC b) d₀ N) (bWt p p' x₀ i) k = (Pk k).eval d₀ := by
    intro d₀ k
    rw [hPk]
    exact ChainLim.ppCoeff_Hrat (kacC b) d₀ (bWt p p' x₀ i) N k _ T₁ hT hT0
  have hPz : ∀ k, D < k → Pk k = 0 := fun k hk =>
    IsFractionRing.injective ℂ[X] Kd ((hKd k).symm.trans ((hvan k hk).trans (map_zero _).symm))
  refine ⟨hvan, hval, hne, hpo, Pk D, (hKd D).symm, fun d₀ => ?_⟩
  have hle0 : poleOrder (Hrat (kacC b) d₀ N) (bWt p p' x₀ i) ≤ D :=
    poleOrder_le_of_ppCoeff fun k hk => by rw [hCd, hPz k hk, Polynomial.eval_zero]
  refine ⟨hle0, fun h => ?_, fun h => poleOrder_eq_of_ppCoeff_ne hle0 (by rw [hCd]; exact h)⟩
  have h1 := ppCoeff_poleOrder_ne (f := Hrat (kacC b) d₀ N) (a := bWt p p' x₀ i) (by omega)
  rw [h, hCd] at h1
  exact h1

/-- Theorem 8.11 (`thm:boundary`), from the two cited results (through Theorem 7.14, Lemma 7.13,
Lemma 8.10, Proposition 8.6 and Lemma 8.7 at the boundary, and Proposition 9.2(iii)).

Paper label: thm:boundary -/
theorem thm_boundary_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_thm_boundary :=
  fun _ _ _ _ hB => ⟨fun _ _ hik => b_thm_i hB hK hH hik,
    fun _ _ _ hik hj => b_thm_ii hK hH hB hik hj,
    fun _ _ _ hD hN1 hN2 => b_thm_iii hK hH hB hD hN1 hN2⟩

end Virasoro
