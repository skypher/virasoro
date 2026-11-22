import Virasoro.Sphere.Proofs.Sec3C2Primaries

/-!
# Lemma 3.7, Step 2: tools for the Wick evaluation (sphere paper)

sphere/paper.tex l.1095–1102: the coefficients of the charged Gaussian
`F_1(v) = exp(λ∑A_m v_m + ∑B_{m,n}v_m v_n)` are polynomials in `λ`; the coefficient of `v^β` is
`λ^{|β|} ∏_m A_m^{β_m}/β_m!` plus lower powers of `λ` (the quadratic contractions).
-/

namespace Virasoro.Sphere

open Filter Topology

theorem tendsto_matrix_inv {ι T : Type*} [Fintype ι] [DecidableEq ι] {l : Filter T}
    (G : T → Matrix ι ι ℂ) (D : Matrix ι ι ℂ) (hD : D.det ≠ 0)
    (h : ∀ i j, Tendsto (fun t => G t i j) l (𝓝 (D i j))) :
    ∀ i j, Tendsto (fun t => (G t)⁻¹ i j) l (𝓝 (D⁻¹ i j)) := by
  have hG : Tendsto G l (𝓝 D) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => h i j
  have hc : ContinuousAt (fun M : Matrix ι ι ℂ => (M.det)⁻¹ • M.adjugate) D :=
    (continuous_id.matrix_det.continuousAt.inv₀ hD).smul continuous_id.matrix_adjugate.continuousAt
  have h2 := hc.tendsto.comp hG
  intro i j
  have h3 := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h2 i)) j
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine h3.congr fun t => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

/-! ### The exponential of a linear series -/

/-- `∏_m c_m^{β_m}/β_m!`, the coefficient of `σ^β` in `exp(∑_m c_m σ_m)`. -/
noncomputable def linExpCoef (c : ℕ → ℂ) (β : ℕ+ →₀ ℕ) : ℂ :=
  β.prod fun m e => c m ^ e / (e.factorial : ℂ)

theorem linExpCoef_add_single (c : ℕ → ℂ) (β : ℕ+ →₀ ℕ) (i : ℕ+) :
    linExpCoef c (β + Finsupp.single i 1) * ((β i : ℂ) + 1) = linExpCoef c β * c i := by
  classical
  have hg : ∀ m : ℕ+, c m ^ 0 / ((Nat.factorial 0 : ℕ) : ℂ) = 1 := fun m => by simp
  have h1 : linExpCoef c β =
      ∏ m ∈ insert i β.support, c m ^ β m / ((β m).factorial : ℂ) :=
    Finsupp.prod_of_support_subset β (Finset.subset_insert _ _) _ (fun m _ => hg m)
  have h2 : linExpCoef c (β + Finsupp.single i 1) =
      ∏ m ∈ insert i β.support, c m ^ (β + Finsupp.single i 1 : ℕ+ →₀ ℕ) m /
        (((β + Finsupp.single i 1 : ℕ+ →₀ ℕ) m).factorial : ℂ) :=
    Finsupp.prod_of_support_subset _ (by
      intro m hm
      rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hm
      rw [Finset.mem_insert, Finsupp.mem_support_iff]
      by_cases hmi : m = i
      · exact Or.inl hmi
      · right
        rw [Finsupp.single_apply, if_neg (Ne.symm hmi), add_zero] at hm
        exact hm) _ (fun m _ => hg m)
  have h3 : ∏ m ∈ (insert i β.support).erase i, c m ^ (β + Finsupp.single i 1 : ℕ+ →₀ ℕ) m /
        (((β + Finsupp.single i 1 : ℕ+ →₀ ℕ) m).factorial : ℂ) =
      ∏ m ∈ (insert i β.support).erase i, c m ^ β m / ((β m).factorial : ℂ) :=
    Finset.prod_congr rfl fun m hm => by
      rw [Finsupp.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm (Finset.ne_of_mem_erase hm)), add_zero]
  rw [h1, h2, ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i _), h3, Finsupp.add_apply,
    Finsupp.single_eq_same, Nat.factorial_succ, pow_succ]
  have hf : ((β i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : ((β i : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  push_cast
  field_simp

/-- The series with the coefficients `linExpCoef c`. -/
noncomputable def linExpSer (c : ℕ → ℂ) : MvPowerSeries ℕ+ ℂ := fun β => linExpCoef c β

theorem coeff_linExpSer (c : ℕ → ℂ) (β : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff β (linExpSer c) = linExpCoef c β := rfl

theorem coeff_mexp_linSeries (c : ℕ → ℂ) (β : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff β (mexp (linSeries c)) = linExpCoef c β := by
  have hL0 : MvPowerSeries.constantCoeff (linSeries c) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show linSeries c 0 = 0
    simp [linSeries]
  have key : mexp (linSeries c) = linExpSer c := by
    refine ext_of_pderiv (fun i => MvPowerSeries.C (c i)) ?_ ?_ ?_
    · rw [constantCoeff_mexp hL0, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_linExpSer]
      simp [linExpCoef]
    · intro i
      rw [pderiv_mexp_zero hL0, pderiv_linSeries]
    · intro i
      ext β
      rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_mul_C, coeff_linExpSer,
        coeff_linExpSer]
      exact linExpCoef_add_single c β i
  rw [key, coeff_linExpSer]

theorem linExpCoef_smul (lam : ℂ) (c : ℕ → ℂ) (β : ℕ+ →₀ ℕ) :
    linExpCoef (fun m => lam * c m) β = lam ^ β.degree * linExpCoef c β := by
  unfold linExpCoef Finsupp.prod
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => by
    dsimp only
    rw [mul_pow, mul_div_assoc]

/-! ### The coefficients of the charged Gaussian -/

theorem constantCoeff_S0Q : MvPowerSeries.constantCoeff S0Q = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show S0 0 - S0L 0 = 0
  simp [S0, S0L, linSeries]

theorem gaussExpo_split (lam : ℂ) :
    gaussExpo lam = linSeries (fun m => lam * Acoef m) + S0Q := by
  rw [gaussExpo_eq]
  congr 1
  ext α
  rw [MvPowerSeries.coeff_C_mul]
  show lam * linSeries Acoef α = linSeries (fun m => lam * Acoef m) α
  unfold linSeries
  split_ifs
  · rw [Finset.mul_sum]
  · rw [mul_zero]

theorem coeff_mexp_gaussExpo (lam : ℂ) (β : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff β (mexp (gaussExpo lam)) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, lam ^ q.1.degree * linExpCoef Acoef q.1 *
        MvPowerSeries.coeff q.2 (mexp S0Q) := by
  have hL0 : MvPowerSeries.constantCoeff (linSeries fun m => lam * Acoef m) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show linSeries (fun m => lam * Acoef m) 0 = 0
    simp [linSeries]
  rw [gaussExpo_split, mexp_add (by rw [hL0]; exact IsNilpotent.zero)
    (by rw [constantCoeff_S0Q]; exact IsNilpotent.zero), MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_mexp_linSeries, linExpCoef_smul]

theorem tendsto_ofReal_inv : Tendsto (fun lam : ℝ => ((lam : ℂ))⁻¹) atTop (𝓝 0) := by
  have h2 : Tendsto (fun lam : ℝ => ((lam⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  rw [Complex.ofReal_zero] at h2
  exact h2.congr fun lam => by push_cast; rfl

/-- `λ^{-|β|} [v^β] F_1 → ∏_m A_m^{β_m}/β_m!` as `λ → ∞`. -/
theorem tendsto_gauss_coeff (β : ℕ+ →₀ ℕ) :
    Tendsto (fun lam : ℝ => ((lam : ℂ))⁻¹ ^ β.degree *
        MvPowerSeries.coeff β (mexp (gaussExpo (lam : ℂ)))) atTop
      (𝓝 (linExpCoef Acoef β)) := by
  classical
  have h1 : Tendsto (fun lam : ℝ => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
      ((lam : ℂ))⁻¹ ^ q.2.degree * (linExpCoef Acoef q.1 *
        MvPowerSeries.coeff q.2 (mexp S0Q))) atTop
      (𝓝 (∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, (0 : ℂ) ^ q.2.degree * (linExpCoef Acoef q.1 *
        MvPowerSeries.coeff q.2 (mexp S0Q)))) :=
    tendsto_finsetSum _ fun q _ => (tendsto_ofReal_inv.pow _).mul tendsto_const_nhds
  have h2 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, (0 : ℂ) ^ q.2.degree * (linExpCoef Acoef q.1 *
      MvPowerSeries.coeff q.2 (mexp S0Q))) = linExpCoef Acoef β := by
    rw [Finset.sum_eq_single (β, 0)]
    · rw [map_zero, pow_zero, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_mexp constantCoeff_S0Q, mul_one]
    · rintro ⟨q1, q2⟩ hq hne
      have hq' : q1 + q2 = β := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have hq2 : q2 ≠ 0 := by
        rintro rfl
        exact hne (by rw [add_zero] at hq'; rw [hq'])
      have hd : q2.degree ≠ 0 := fun h => hq2 ((Finsupp.degree_eq_zero_iff _).mp h)
      rw [zero_pow hd, zero_mul]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero β)) h
  rw [h2] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  rw [coeff_mexp_gaussExpo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = β := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  rw [← hq', map_add, pow_add]
  have e : ((lam : ℂ))⁻¹ ^ q.1.degree * (lam : ℂ) ^ q.1.degree = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hl, one_pow]
  linear_combination (-(((lam : ℂ))⁻¹ ^ q.2.degree * linExpCoef Acoef q.1 *
    MvPowerSeries.coeff q.2 (mexp S0Q))) * e

end Virasoro.Sphere
