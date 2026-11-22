import Virasoro.Sphere.Proofs.Sec3C2WickTools
import Virasoro.Sphere.Proofs.Sec3SaddleOmega

/-!
# Lemma 3.7, Step 2: the Gram matrix, the Wick evaluation and `c_n^∞` (sphere paper)

sphere/paper.tex l.1095–1109.  Because every `v_m` in `P_w` carries `λ^{-1}`, the Gram matrix
tends to that of the `w`; in `⟨P_w, F_1F_2⟩` each monomial in `W̄_m = i v̄_m/λ` paired against
the charged Gaussian tends to the product of the saddle means
`W_{*,m} = iA_m/(2m) = binom(2m,m)/(m 4^m)`; hence `c_n(λ²) → ‖(U(W_*)^† F_2)_n‖²`.
-/

namespace Virasoro.Sphere

open MvPolynomial TensorProduct Filter Topology

theorem hhForm_level_sum {n : ℕ} (x : HH) {y : HH} (hy : y ∈ hhLevel n) :
    hhForm x y = ∑ p ∈ (finite_level_pair n).toFinset,
      (starRingEnd ℂ) (hhBasis.repr x p) * hhBasis.repr y p * (fockNorm p.1 * fockNorm p.2) := by
  rw [hhLevel, Module.Basis.mem_span_image] at hy
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [Set.Finite.mem_toFinset]
    exact hy (Finset.mem_coe.mpr hp)
  · intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    ring

theorem repr_of_rescH (lam : ℂ) (hl : lam ≠ 0) (x : HH) (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) :
    hhBasis.repr x p = ((Complex.I * lam) ^ p.1.degree)⁻¹ * hhBasis.repr (rescH lam x) p := by
  rw [repr_rescH, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero hl)), one_mul]

theorem repr_Ftot (lam : ℂ) (n : ℕ) (β γ : ℕ+ →₀ ℕ) (h : lvl β + lvl γ = n) :
    hhBasis.repr (Ftot lam n) (β, γ) =
      MvPowerSeries.coeff β (mexp (gaussExpo lam)) *
        MvPowerSeries.coeff γ (mexp (gaussExpo 0)) := by
  classical
  rw [Ftot, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp only [hhBasis_repr_tmul, coeff_gaussF]
  rw [Finset.sum_eq_single (lvl β, lvl γ)]
  · rw [if_pos rfl, if_pos rfl]
  · rintro ⟨q1, q2⟩ _ hne
    by_cases h1 : lvl β = q1
    · by_cases h2 : lvl γ = q2
      · exact absurd (by rw [h1, h2]) hne
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro hnot
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr h) hnot

theorem fockForm_monomial_left (γ : ℕ+ →₀ ℕ) (G : Fock) :
    fockForm (monomial γ 1) G = coeff γ G * fockNorm γ := by
  classical
  unfold fockForm
  by_cases hγ : γ ∈ G.support
  · rw [Finset.sum_eq_single γ]
    · rw [coeff_monomial, if_pos rfl, map_one, one_mul]
    · intro α _ hne
      rw [coeff_monomial, if_neg (Ne.symm hne), map_zero, zero_mul, zero_mul]
    · intro h
      exact absurd hγ h
  · rw [notMem_support_iff.mp hγ, zero_mul]
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [coeff_monomial, if_neg (fun h => hγ (by rw [h]; exact hα)), map_zero, zero_mul, zero_mul]

/-- `⟨P(c, ·), G⟩` for `P` a polynomial in `(W, u)` evaluated at `W = c`. -/
theorem fockForm_evAt (c : ℕ+ → ℂ) (y : HH) (G : Fock) :
    fockForm (evAt c y) G = ∑ p ∈ (hhBasis.repr y).support,
      (starRingEnd ℂ) (hhBasis.repr y p) *
        (starRingEnd ℂ) (p.1.prod fun m e => c m ^ e) * (coeff p.2 G * fockNorm p.2) := by
  have hy := hhBasis.linearCombination_repr y
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hy
  conv_lhs => rw [← hy]
  rw [map_sum, fockForm_sum_left]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, hhBasis_apply, evAt_tmul, aeval_monomial, map_one, one_mul, smul_smul,
    fockForm_smul_left, fockForm_monomial_left, map_mul]

theorem conj_Wstar_prod (β : ℕ+ →₀ ℕ) :
    (starRingEnd ℂ) (β.prod fun m e => Wstar m ^ e) = β.prod fun m e => Wstar m ^ e := by
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [map_pow]
  congr 1
  rw [Wstar]
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_ofNat]

theorem Wstar_eq (m : ℕ+) : Wstar m = Complex.I * Acoef m / (2 * ((m : ℕ) : ℂ)) := by
  have hm : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.pos.ne'
  rw [Wstar, Acoef, halfBinom_eq, Nat.centralBinom]
  push_cast
  field_simp
  linear_combination ((Nat.choose (2 * (m : ℕ)) (m : ℕ) : ℂ)) * Complex.I_sq

/-- The saddle means: `i^{|β|} ∏_m A_m^{β_m}/β_m! · ∏_m β_m!/(2m)^{β_m} = ∏_m W_{*,m}^{β_m}`
(sphere/paper.tex l.1100–1101). -/
theorem Wstar_prod (β : ℕ+ →₀ ℕ) :
    Complex.I ^ β.degree * linExpCoef Acoef β * fockNorm β = β.prod fun m e => Wstar m ^ e := by
  unfold linExpCoef fockNorm Finsupp.prod
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  have hf : ((β m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm : (2 * ((m : ℕ) : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr m.pos.ne')
  dsimp only
  rw [Wstar_eq, div_pow, mul_pow]
  field_simp
  ring

theorem coeff_sum_gaussF (n : ℕ) (γ : ℕ+ →₀ ℕ) (h : lvl γ ≤ n) :
    coeff γ (∑ j ∈ Finset.range (n + 1), gaussF 0 j) =
      MvPowerSeries.coeff γ (mexp (gaussExpo 0)) := by
  classical
  rw [coeff_sum]
  simp only [coeff_gaussF]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]

theorem fockNorm_ne_zero (α : ℕ+ →₀ ℕ) : fockNorm α ≠ 0 := by
  rw [fockNorm_eq]
  exact_mod_cast (fockNormQ_pos α).ne'

theorem conj_fockNorm (α : ℕ+ →₀ ℕ) : (starRingEnd ℂ) (fockNorm α) = fockNorm α := by
  rw [fockNorm_eq]
  simp

theorem fockNorm_zero : fockNorm 0 = 1 := by
  simp [fockNorm]

theorem tendsto_ofReal_sq_inv : Tendsto (fun lam : ℝ => (((lam : ℂ)) ^ 2)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_ofReal_inv.pow 2
  rw [zero_pow two_ne_zero] at h
  exact h.congr fun lam => by rw [inv_pow]

theorem coeff_UdagF (U : Fock →ₗ[ℂ] HH) (n : ℕ) (α : ℕ+ →₀ ℕ)
    (hα : α ∈ (finite_level n).toFinset) :
    coeff α (UdagF U n) =
      fockForm (evAt Wstar (U (monomial α 1))) (∑ j ∈ Finset.range (n + 1), gaussF 0 j) /
        fockNorm α := by
  classical
  rw [UdagF, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', if_pos hα]

/-- `‖(U(W_*)^† F_2)_n‖² = ∑_α |⟨U(W_*)u^α, F_2⟩|² / ‖u^α‖²`. -/
theorem fockForm_UdagF (U : Fock →ₗ[ℂ] HH) (n : ℕ) :
    fockForm (UdagF U n) (UdagF U n) = ∑ a : (finite_level n).toFinset,
      (starRingEnd ℂ) (fockForm (evAt Wstar (U (monomial a.1 1)))
          (∑ j ∈ Finset.range (n + 1), gaussF 0 j)) * (fockNorm a.1)⁻¹ *
        fockForm (evAt Wstar (U (monomial a.1 1))) (∑ j ∈ Finset.range (n + 1), gaussF 0 j) := by
  rw [Finset.sum_coe_sort (finite_level n).toFinset (fun α =>
    (starRingEnd ℂ) (fockForm (evAt Wstar (U (monomial α 1)))
        (∑ j ∈ Finset.range (n + 1), gaussF 0 j)) * (fockNorm α)⁻¹ *
      fockForm (evAt Wstar (U (monomial α 1))) (∑ j ∈ Finset.range (n + 1), gaussF 0 j))]
  conv_lhs =>
    arg 1
    rw [UdagF]
  rw [fockForm_sum_left]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [fockForm_smul_left, fockForm_monomial_left, coeff_UdagF U n α hα, map_div₀,
    conj_fockNorm]
  have hN := fockNorm_ne_zero α
  field_simp

set_option maxHeartbeats 3200000 in
/-- Lemma 3.7, Step 2, second half (sphere/paper.tex l.1095–1109). -/
theorem sub_c2_wick : Stmt_sub_c2_wick := by
  intro U hU n P hb hconv
  classical
  have hmemP : ∀ᶠ lam : ℝ in atTop, ∀ a : (finite_level n).toFinset, P lam a ∈ hhLevel n := by
    filter_upwards [hb] with lam hb' a
    obtain ⟨b, hbP⟩ := hb'
    rw [← hbP a]
    exact (mem_primSpace.mp (b a).2).1
  have hsuppU : ∀ (a : (finite_level n).toFinset) (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)),
      p ∉ (finite_level_pair n).toFinset → hhBasis.repr (U (monomial a.1 1)) p = 0 := by
    intro a p hp
    refine tendsto_nhds_unique (hconv a p) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hmemP] with lam h
    have h1 := rescH_mem_level (lam : ℂ) (h a)
    rw [hhLevel, Module.Basis.mem_span_image] at h1
    by_contra hne
    exact hp ((Set.Finite.mem_toFinset _).mpr
      (h1 (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (Ne.symm hne)))))
  have hU0 : ∀ (a : (finite_level n).toFinset) (γ : ℕ+ →₀ ℕ),
      hhBasis.repr (U (monomial a.1 1)) (0, γ) = if a.1 = γ then 1 else 0 := by
    intro a γ
    rw [← coeff_evAt_zero, hU.2, coeff_monomial]
  have hlvl : ∀ a : (finite_level n).toFinset, lvl a.1 = n := fun a => by
    have h := a.2
    rwa [Set.Finite.mem_toFinset] at h
  -- the Gram matrix (l.1095–1097)
  have hG : ∀ a b : (finite_level n).toFinset,
      Tendsto (fun lam : ℝ => hhForm (P lam a) (P lam b)) atTop
        (𝓝 (Matrix.diagonal (fun a : (finite_level n).toFinset => fockNorm a.1) a b)) := by
    intro a b
    have h1 : Tendsto (fun lam : ℝ => ∑ p ∈ (finite_level_pair n).toFinset,
        (((lam : ℂ)) ^ 2)⁻¹ ^ p.1.degree *
          ((starRingEnd ℂ) (hhBasis.repr (rescH (lam : ℂ) (P lam a)) p) *
            hhBasis.repr (rescH (lam : ℂ) (P lam b)) p * (fockNorm p.1 * fockNorm p.2))) atTop
        (𝓝 (∑ p ∈ (finite_level_pair n).toFinset, (0 : ℂ) ^ p.1.degree *
          ((starRingEnd ℂ) (hhBasis.repr (U (monomial a.1 1)) p) *
            hhBasis.repr (U (monomial b.1 1)) p * (fockNorm p.1 * fockNorm p.2)))) :=
      tendsto_finsetSum _ fun p _ => (tendsto_ofReal_sq_inv.pow _).mul
        ((((Complex.continuous_conj.tendsto _).comp (hconv a p)).mul (hconv b p)).mul
          tendsto_const_nhds)
    have h2 : (∑ p ∈ (finite_level_pair n).toFinset, (0 : ℂ) ^ p.1.degree *
          ((starRingEnd ℂ) (hhBasis.repr (U (monomial a.1 1)) p) *
            hhBasis.repr (U (monomial b.1 1)) p * (fockNorm p.1 * fockNorm p.2))) =
        Matrix.diagonal (fun a : (finite_level n).toFinset => fockNorm a.1) a b := by
      rw [Finset.sum_eq_single ((0 : ℕ+ →₀ ℕ), a.1)]
      · rw [hU0, hU0, if_pos rfl, map_zero, pow_zero, map_one, fockNorm_zero,
          Matrix.diagonal_apply]
        by_cases hab : a = b
        · rw [if_pos hab, if_pos (by rw [hab])]
          ring
        · rw [if_neg hab, if_neg (fun h => hab (Subtype.ext h.symm))]
          ring
      · rintro ⟨p1, p2⟩ _ hne
        by_cases hp1 : p1 = 0
        · subst hp1
          rw [hU0, if_neg (fun h => hne (by rw [h]))]
          simp
        · rw [zero_pow (fun h => hp1 ((Finsupp.degree_eq_zero_iff _).mp h)), zero_mul]
      · intro hnot
        exfalso
        apply hnot
        rw [Set.Finite.mem_toFinset]
        show lvl (0 : ℕ+ →₀ ℕ) + lvl a.1 = n
        rw [hlvl a]
        simp [lvl]
    rw [h2] at h1
    refine h1.congr' ?_
    filter_upwards [hmemP, eventually_gt_atTop 0] with lam h hlam
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    rw [hhForm_level_sum (P lam a) (h b)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [repr_of_rescH (lam : ℂ) hl (P lam a) p, repr_of_rescH (lam : ℂ) hl (P lam b) p, map_mul,
      map_inv₀, map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal]
    have e : ((-Complex.I * (lam : ℂ)) ^ p.1.degree)⁻¹ *
        ((Complex.I * (lam : ℂ)) ^ p.1.degree)⁻¹ = (((lam : ℂ)) ^ 2)⁻¹ ^ p.1.degree := by
      rw [← mul_inv, ← mul_pow, inv_pow]
      congr 2
      linear_combination -(lam : ℂ) ^ 2 * Complex.I_mul_I
    linear_combination (-((starRingEnd ℂ) (hhBasis.repr (rescH (lam : ℂ) (P lam a)) p) *
      hhBasis.repr (rescH (lam : ℂ) (P lam b)) p * (fockNorm p.1 * fockNorm p.2))) * e
  -- the pairing with `F_1F_2` (l.1098–1102)
  have hFl : ∀ a : (finite_level n).toFinset,
      Tendsto (fun lam : ℝ => hhForm (P lam a) (Ftot (lam : ℂ) n)) atTop
        (𝓝 (fockForm (evAt Wstar (U (monomial a.1 1)))
          (∑ j ∈ Finset.range (n + 1), gaussF 0 j))) := by
    intro a
    have h1 : Tendsto (fun lam : ℝ => ∑ p ∈ (finite_level_pair n).toFinset,
        (starRingEnd ℂ) (hhBasis.repr (rescH (lam : ℂ) (P lam a)) p) *
          (Complex.I ^ p.1.degree * (((lam : ℂ))⁻¹ ^ p.1.degree *
            MvPowerSeries.coeff p.1 (mexp (gaussExpo (lam : ℂ))))) *
          (MvPowerSeries.coeff p.2 (mexp (gaussExpo 0)) * (fockNorm p.1 * fockNorm p.2))) atTop
        (𝓝 (∑ p ∈ (finite_level_pair n).toFinset,
          (starRingEnd ℂ) (hhBasis.repr (U (monomial a.1 1)) p) *
            (Complex.I ^ p.1.degree * linExpCoef Acoef p.1) *
            (MvPowerSeries.coeff p.2 (mexp (gaussExpo 0)) * (fockNorm p.1 * fockNorm p.2)))) :=
      tendsto_finsetSum _ fun p _ =>
        ((((Complex.continuous_conj.tendsto _).comp (hconv a p)).mul
          (tendsto_const_nhds.mul (tendsto_gauss_coeff p.1))).mul tendsto_const_nhds)
    have h2 : (∑ p ∈ (finite_level_pair n).toFinset,
          (starRingEnd ℂ) (hhBasis.repr (U (monomial a.1 1)) p) *
            (Complex.I ^ p.1.degree * linExpCoef Acoef p.1) *
            (MvPowerSeries.coeff p.2 (mexp (gaussExpo 0)) * (fockNorm p.1 * fockNorm p.2))) =
        fockForm (evAt Wstar (U (monomial a.1 1)))
          (∑ j ∈ Finset.range (n + 1), gaussF 0 j) := by
      rw [fockForm_evAt]
      refine Eq.trans ?_ (Finset.sum_subset
        (s₁ := (hhBasis.repr (U (monomial a.1 1))).support)
        (s₂ := (finite_level_pair n).toFinset)
        (fun p hp => by
          by_contra hnot
          exact (Finsupp.mem_support_iff.mp hp) (hsuppU a p hnot))
        (fun p _ hp => by
          rw [Finsupp.notMem_support_iff.mp hp, map_zero, zero_mul, zero_mul])).symm
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : lvl p.1 + lvl p.2 = n := by
        rwa [Set.Finite.mem_toFinset] at hp
      rw [conj_Wstar_prod, ← Wstar_prod p.1, coeff_sum_gaussF n p.2 (by omega)]
      ring
    rw [h2] at h1
    refine h1.congr' ?_
    filter_upwards [hmemP, eventually_gt_atTop 0] with lam h hlam
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    rw [hhForm_level_sum (P lam a) (Ftot_mem_level (lam : ℂ) n)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : lvl p.1 + lvl p.2 = n := by
      rwa [Set.Finite.mem_toFinset] at hp
    have hF : hhBasis.repr (Ftot (lam : ℂ) n) p =
        MvPowerSeries.coeff p.1 (mexp (gaussExpo (lam : ℂ))) *
          MvPowerSeries.coeff p.2 (mexp (gaussExpo 0)) := repr_Ftot (lam : ℂ) n p.1 p.2 hp'
    rw [hF, repr_of_rescH (lam : ℂ) hl (P lam a) p, map_mul, map_inv₀, map_pow, map_mul,
      Complex.conj_I, Complex.conj_ofReal]
    have e : ((-Complex.I * (lam : ℂ)) ^ p.1.degree)⁻¹ =
        Complex.I ^ p.1.degree * ((lam : ℂ))⁻¹ ^ p.1.degree := by
      rw [← mul_pow, ← inv_pow]
      congr 1
      rw [mul_inv, inv_neg, Complex.inv_I, neg_neg]
    linear_combination (-((starRingEnd ℂ) (hhBasis.repr (rescH (lam : ℂ) (P lam a)) p) *
      MvPowerSeries.coeff p.1 (mexp (gaussExpo (lam : ℂ))) *
      (MvPowerSeries.coeff p.2 (mexp (gaussExpo 0)) * (fockNorm p.1 * fockNorm p.2)))) * e
  -- the limit of `c_n(λ²)` (l.1102–1109)
  have hD : (Matrix.diagonal (fun a : (finite_level n).toFinset => fockNorm a.1)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => fockNorm_ne_zero a.1
  have hGinv := tendsto_matrix_inv (fun lam : ℝ => primGram (P lam)) _ hD (fun i j => hG i j)
  have hDinv : (Matrix.diagonal (fun a : (finite_level n).toFinset => fockNorm a.1))⁻¹ =
      Matrix.diagonal (fun a : (finite_level n).toFinset => (fockNorm a.1)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (fockNorm_ne_zero a.1)
  have hmain : Tendsto (fun lam : ℝ => ∑ a : (finite_level n).toFinset,
      ∑ b : (finite_level n).toFinset,
        (starRingEnd ℂ) (hhForm (P lam a) (Ftot (lam : ℂ) n)) * (primGram (P lam))⁻¹ a b *
          hhForm (P lam b) (Ftot (lam : ℂ) n)) atTop
      (𝓝 (∑ a : (finite_level n).toFinset, ∑ b : (finite_level n).toFinset,
        (starRingEnd ℂ) (fockForm (evAt Wstar (U (monomial a.1 1)))
            (∑ j ∈ Finset.range (n + 1), gaussF 0 j)) *
          (Matrix.diagonal (fun a : (finite_level n).toFinset => fockNorm a.1))⁻¹ a b *
          fockForm (evAt Wstar (U (monomial b.1 1)))
            (∑ j ∈ Finset.range (n + 1), gaussF 0 j))) :=
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      (((Complex.continuous_conj.tendsto _).comp (hFl a)).mul (hGinv a b)).mul (hFl b)
  have hval : (∑ a : (finite_level n).toFinset, ∑ b : (finite_level n).toFinset,
        (starRingEnd ℂ) (fockForm (evAt Wstar (U (monomial a.1 1)))
            (∑ j ∈ Finset.range (n + 1), gaussF 0 j)) *
          (Matrix.diagonal (fun a : (finite_level n).toFinset => fockNorm a.1))⁻¹ a b *
          fockForm (evAt Wstar (U (monomial b.1 1)))
            (∑ j ∈ Finset.range (n + 1), gaussF 0 j)) =
      fockForm (UdagF U n) (UdagF U n) := by
    rw [fockForm_UdagF, hDinv]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.diagonal_apply, if_pos rfl]
    · intro b _ hne
      rw [Matrix.diagonal_apply, if_neg (Ne.symm hne), mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hval] at hmain
  exact hmain

end Virasoro.Sphere
