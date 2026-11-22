import Virasoro.Sphere.Proofs.Sec3FpowExp
import Virasoro.Sphere.Proofs.Sec3CentralSubs
import Virasoro.Sphere.Proofs.Sec3BergmanZero

/-!
# Lemma 3.7 from the `c = 2` decomposition (sphere paper, Step 4)

sphere/paper.tex l.1158–1180.  With the limit of (3.8) at each order in `z` (`c2_limit`),
`(Φ₁ + Φ₂)/8 = -½ log(θ₃θ₄) = -⅛ log(1 - z) - log θ₃` cancels `det(I - M²)^{-1/2}`
(Lemmas 3.5, 3.6 and (2.3)), leaving `exp((Φ_c^raw - 𝓘₀)/24) = ∏(1 - q^{2m})^{1/2}`; raising to
the 24th power and (2.5) give the claim.
-/

namespace Virasoro.Sphere

open PowerSeries

theorem fpow_pow {f : PowerSeries ℚ} (hf : constantCoeff f = 1) (a : ℚ) (k : ℕ) :
    fpow f a ^ k = fpow f ((k : ℚ) * a) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, fpow_zero hf]
  | succ k ih =>
    rw [pow_succ, ih, ← fpow_add hf]
    congr 1
    push_cast
    ring

/-- `exp(-k log θ) θ^k = 1`. -/
theorem exp_neg_log_mul_pow (θ : PowerSeries ℂ) (hθ : constantCoeff θ = 1) (k : ℕ) :
    (exp ℂ).subst ((-(k : ℂ)) • (log ℂ).subst (θ - 1)) * θ ^ k = 1 := by
  have h1 : constantCoeff (θ - 1) = 0 := by rw [map_sub, hθ, map_one, sub_self]
  have hL : constantCoeff ((log ℂ).subst (θ - 1)) = 0 :=
    constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  have hk : ∀ a : ℂ, constantCoeff (a • (log ℂ).subst (θ - 1)) = 0 := fun a => by
    rw [smul_eq_C_mul, map_mul, hL, mul_zero]
  nth_rewrite 2 [← exp_log_subst θ hθ]
  rw [exp_subst_pow _ hL, ← exp_subst_add _ _ (hk _) (hk _), neg_smul, neg_add_cancel,
    exp_subst_zero]

theorem subst_sixteen (cinf : ℕ → ℂ) {Q : PowerSeries ℂ} (hQ0 : constantCoeff Q = 0) :
    (mk cinf).subst ((16 : ℂ) • Q) = (mk fun n => (16 : ℂ) ^ n * cinf n).subst Q := by
  have hs := HasSubst.of_constantCoeff_zero' hQ0
  have hs1 : HasSubst ((16 : ℂ) • Q) := HasSubst.of_constantCoeff_zero' (by
    rw [smul_eq_C_mul, map_mul, hQ0, mul_zero])
  ext N
  rw [coeff_subst' hs1, coeff_subst' hs]
  refine finsum_congr fun d => ?_
  rw [coeff_mk, coeff_mk, smul_pow, coeff_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

section Central

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

theorem hQ0c : constantCoeff (Q0.map (algebraMap ℚ ℂ)) = 0 :=
  constantCoeff_map_zero _ constantCoeff_Q0

theorem hQc : (zq ℂ).subst (Q0.map (algebraMap ℚ ℂ)) = X := by
  have h1 := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) zq_subst_Q0
  rw [PowerSeries.map_X] at h1
  rw [← h1, ← map_zq (algebraMap ℚ ℂ)]
  exact (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' constantCoeff_Q0)
    (h := algebraMap ℚ ℂ) _).symm

/-- `q(z)` is unique. -/
theorem Q_eq_Q0 {Q : PowerSeries ℂ} (hQ0 : constantCoeff Q = 0) (hQ : (zq ℂ).subst Q = X) :
    Q = Q0.map (algebraMap ℚ ℂ) := by
  have hQs := HasSubst.of_constantCoeff_zero' hQ0
  have hzsQ : HasSubst (zq ℚ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
  have hS : (Q0.map (algebraMap ℚ ℂ)).subst (zq ℂ) = X := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) Q0_subst_zq
    rw [PowerSeries.map_X] at h
    rw [← h, ← map_zq (algebraMap ℚ ℂ)]
    exact (PowerSeries.map_subst hzsQ _).symm
  have hzs : HasSubst (zq ℂ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
  have h := congrArg (PowerSeries.subst Q) hS
  rw [subst_comp_subst_apply hzs hQs, hQ, subst_X_self', subst_X hQs] at h
  exact h.symm

/-- `log(fg) = log f + log g` for series with constant term `1`. -/
theorem logMulPS (f g : PowerSeries ℂ) (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    (log ℂ).subst (f * g - 1) = (log ℂ).subst (f - 1) + (log ℂ).subst (g - 1) := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have h2 : constantCoeff (g - 1) = 0 := by rw [map_sub, hg, map_one, sub_self]
  have hL1 : constantCoeff ((log ℂ).subst (f - 1)) = 0 :=
    constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  have hL2 : constantCoeff ((log ℂ).subst (g - 1)) = 0 :=
    constantCoeff_subst_eq_zero h2 _ constantCoeff_log
  have e : f * g = (exp ℂ).subst ((log ℂ).subst (f - 1) + (log ℂ).subst (g - 1)) := by
    rw [exp_subst_add _ _ hL1 hL2, exp_log_subst f hf, exp_log_subst g hg]
  rw [e, log_exp_subst _ (by rw [map_add, hL1, hL2, add_zero])]

/-- `log(f^k) = k log f` for a series with constant term `1`. -/
theorem logPowPS (f : PowerSeries ℂ) (hf : constantCoeff f = 1) (k : ℕ) :
    (log ℂ).subst (f ^ k - 1) = (k : ℂ) • (log ℂ).subst (f - 1) := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hL : constantCoeff ((log ℂ).subst (f - 1)) = 0 :=
    constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  have e : f ^ k = (exp ℂ).subst ((k : ℂ) • (log ℂ).subst (f - 1)) := by
    rw [← exp_subst_pow _ hL, exp_log_subst f hf]
  rw [e, log_exp_subst _ (by rw [smul_eq_C_mul, map_mul, hL, mul_zero])]

/-- The binomial power commutes with `ℚ → ℂ`. -/
theorem fpowMapPS (f : PowerSeries ℚ) (a : ℚ) :
    PowerSeries.map (algebraMap ℚ ℂ) (fpow f a) =
      fpow (PowerSeries.map (algebraMap ℚ ℂ) f) (algebraMap ℚ ℂ a) := by
  ext n
  simp only [fpow, coeff_map, coeff_mk, map_sum, map_mul, gbinom, map_div₀, map_prod, map_sub,
    map_natCast]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← coeff_map, map_pow, map_sub, map_one]

include hF hK in
/-- `exp((Φ₁ + Φ₂)/8) = det(I - M²)^{-1/2}` (sphere/paper.tex l.1176). -/
theorem exp_Phi_eighth (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ} (hE : IsExpansionData S1t S2c S21 S22) :
    constantCoeff ((1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
        (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22) = 0 ∧
    (exp ℂ).subst ((1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
        (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22) =
      detInvSqrt.map (algebraMap ℚ ℂ) := by
  obtain ⟨-, -, h⟩ := lem_ext_exponents_of_cited hF hK hJ1 hJ2 S1t S2c S21 S22 hE
  obtain ⟨h22, h21⟩ := h _ _ isSaddle_sigmaStar _ hQ0c hQc
  have hQs := HasSubst.of_constantCoeff_zero' constantCoeff_Q0
  set θ3c := (th3 ℂ).subst (Q0.map (algebraMap ℚ ℂ)) with hθ3
  set θ4c := (th4 ℂ).subst (Q0.map (algebraMap ℚ ℂ)) with hθ4
  have h3 : constantCoeff θ3c = 1 := constantCoeff_subst_of_one hQ0c _ constantCoeff_th3
  have h4 : constantCoeff θ4c = 1 := constantCoeff_subst_of_one hQ0c _ constantCoeff_th4
  have hl : ∀ θ : PowerSeries ℂ, constantCoeff θ = 1 → ∀ a : ℂ,
      constantCoeff (a • (log ℂ).subst (θ - 1)) = 0 := by
    intro θ hθ a
    have h1 : constantCoeff (θ - 1) = 0 := by rw [map_sub, hθ, map_one, sub_self]
    have h2 : constantCoeff ((log ℂ).subst (θ - 1)) = 0 :=
      constantCoeff_subst_eq_zero h1 _ constantCoeff_log
    rw [smul_eq_C_mul, map_mul, h2, mul_zero]
  have hsum : (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
      (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22 =
      (-(1 / 2) : ℂ) • (log ℂ).subst (θ3c - 1) + (-(1 / 2) : ℂ) • (log ℂ).subst (θ4c - 1) := by
    rw [h21, h22, smul_smul, smul_smul]
    norm_num
  have hc : constantCoeff ((1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
      (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22) = 0 := by
    rw [hsum, map_add, hl θ3c h3, hl θ4c h4, add_zero]
  refine ⟨hc, ?_⟩
  -- the paper's log form (l.1174–1176): `(Φ₁+Φ₂)/8 = -½ log(θ₃θ₄) = -⅛ log(1-z) - log θ₃`
  have hz1 : constantCoeff (1 - X : PowerSeries ℂ) = 1 := by
    rw [map_sub, map_one, constantCoeff_X, sub_zero]
  have hJ := one_sub_mul_th3 hJ1 hQ0c hQc
  have hlog4 : (4 : ℂ) • (log ℂ).subst (θ4c - 1) =
      (log ℂ).subst ((1 - X : PowerSeries ℂ) - 1) + (4 : ℂ) • (log ℂ).subst (θ3c - 1) := by
    have e := congrArg (fun f => (log ℂ).subst (f - 1)) hJ
    rw [logMulPS _ _ hz1 (by rw [map_pow, h3, one_pow]), logPowPS _ h3,
      logPowPS _ h4] at e
    simp only [Nat.cast_ofNat] at e
    exact e.symm
  have hS : (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
      (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22 =
      (-(1 / 8) : ℂ) • (log ℂ).subst ((1 - X : PowerSeries ℂ) - 1) +
        (-1 : ℂ) • (log ℂ).subst (θ3c - 1) := by
    have e4 : (log ℂ).subst (θ4c - 1) = (1 / 4 : ℂ) • (log ℂ).subst ((1 - X : PowerSeries ℂ) - 1) +
        (log ℂ).subst (θ3c - 1) := by
      have h := congrArg (fun f => (1 / 4 : ℂ) • f) hlog4
      simp only [smul_add, smul_smul] at h
      rwa [show (1 / 4 : ℂ) * 4 = 1 by norm_num, one_smul, one_smul] at h
    have key : ∀ A B C : PowerSeries ℂ, B = (1 / 4 : ℂ) • C + A →
        (-(1 / 2) : ℂ) • A + (-(1 / 2) : ℂ) • B = (-(1 / 8) : ℂ) • C + (-1 : ℂ) • A := by
      intro A B C h
      rw [h]
      module
    rw [hsum]
    exact key _ _ _ e4
  have hcz := hl (1 - X) hz1 (-(1 / 8))
  have hc3 := hl θ3c h3 (-1)
  have hinv3 : (exp ℂ).subst ((-1 : ℂ) • (log ℂ).subst (θ3c - 1)) = θ3c⁻¹ := by
    have h := exp_neg_log_mul_pow θ3c h3 1
    rw [Nat.cast_one, pow_one] at h
    exact (PowerSeries.eq_inv_iff_mul_eq_one (by rw [h3]; exact one_ne_zero)).2 h
  have hθmap : PowerSeries.map (algebraMap ℚ ℂ) ((th3 ℚ).subst Q0) = θ3c := by
    rw [hθ3, ← map_th3 (algebraMap ℚ ℂ)]
    exact PowerSeries.map_subst hQs (h := algebraMap ℚ ℂ) _
  have hθ0 : PowerSeries.constantCoeff ((th3 ℚ).subst Q0) ≠ 0 := by
    rw [constantCoeff_subst_of_one' constantCoeff_Q0 _ constantCoeff_th3]
    exact one_ne_zero
  -- Lemma 3.5 in its `fpow` form (l.825–833)
  have hD := (lem_bergman_det_of_cited hJ2).2 Q0 constantCoeff_Q0 zq_subst_Q0
  have hq : (algebraMap ℚ ℂ) (-1 / 8 : ℚ) = (-(1 / 8) : ℂ) := by
    rw [map_div₀, map_neg, map_one, map_ofNat]; ring
  rw [hS, exp_subst_add _ _ hcz hc3, exp_smul_log _ hz1, hinv3, hD, map_mul,
    map_inv_of_ne (algebraMap ℚ ℂ) _ hθ0, hθmap, fpowMapPS, map_sub, map_one,
    PowerSeries.map_X, hq]

include hF hK in
theorem constantCoeff_PhiCraw {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) :
    constantCoeff (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m)) = 0 := by
  have ha : MvPowerSeries.constantCoeff (MvPowerSeries.subst sigmaStar S2c) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_sigmaStar
      (fun m => constantCoeff_sigmaStar m) (coeff_zero_S2c_of_data hF hK hE)
  rw [PhiCraw, map_add, map_mul, constantCoeff_Psi1, add_zero]
  exact mul_eq_zero_of_right _ ha

include hF hK in
set_option maxHeartbeats 1600000 in
/-- Lemma 3.7 from Steps 1–3 of its proof (sphere/paper.tex l.1158–1180, Step 4). -/
theorem lem_central_charge_of_c2 (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (h : Stmt_sub_c2_decomp) : Stmt_lem_central_charge := by
  obtain ⟨c, cinf, hdec, hlim, hgen⟩ := h
  intro S1t S2c S21 S22 hE σ σb hs Q hQ0 hQ
  obtain ⟨e1, e2⟩ := hs.eq_sigmaStar
  subst e1 e2
  have hQeq := Q_eq_Q0 hQ0 hQ
  have hQs := HasSubst.of_constantCoeff_zero' hQ0
  have h16 : (16 : ℂ) • Q = X * (nomeRatio ℂ).subst Q := by
    rw [smul_eq_C_mul, map_ofNat]
    exact sixteen_Q hQ0 hQ
  have hI := I0def_sigmaStar hJ2 hQ0 hQ h16
  have hRc : constantCoeff ((nomeRatio ℂ).subst Q) = 1 :=
    constantCoeff_subst_of_one hQ0 _ constantCoeff_nomeRatio
  have hI0 := constantCoeff_I0s hJ2
  have hEI1 : EI 1 = (nomeRatio ℂ).subst Q := by
    rw [EI, map_one, one_mul, hI, exp_log_subst _ hRc]
  have hEIn : ∀ n : ℕ, EI (n : ℂ) = (nomeRatio ℂ).subst Q ^ n := fun n => by
    rw [← hEI1, EI, EI, map_one, one_mul, exp_subst_pow _ hI0, smul_eq_C_mul]
  have hEIs : ∀ n : ℕ, EI ((n : ℂ) - 1 / 24) = (nomeRatio ℂ).subst Q ^ n * EI (-(1 / 24)) :=
    fun n => by rw [sub_eq_add_neg, EI_add hJ2, hEIn]
  have hstar := c2_limit hF hK hJ2 hE c cinf (fun N => (hdec N).mono fun lam h =>
    h.trans (Finset.sum_congr rfl fun n _ => by rw [Bser2, coeff_mk])) hlim
  obtain ⟨hc2, hY⟩ := exp_Phi_eighth hF hK hJ1 hJ2 hE
  have hcΦ := constantCoeff_PhiCraw hF hK hE
  have hc1 : ∀ a : ℂ, constantCoeff
      (a • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m)) = 0 := fun a => by
    rw [smul_eq_C_mul, map_mul, hcΦ, mul_zero]
  have hLinf : detInvSqrt.map (algebraMap ℚ ℂ) * (exp ℂ).subst
        ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
          (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
          (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22) =
      detInvSqrt.map (algebraMap ℚ ℂ) *
        ((exp ℂ).subst ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m)) *
          detInvSqrt.map (algebraMap ℚ ℂ)) := by
    rw [add_assoc, exp_subst_add _ _ (hc1 _) hc2, hY]
  have hser : detInvSqrt.map (algebraMap ℚ ℂ) * detInvSqrt.map (algebraMap ℚ ℂ) =
      (mk cinf).subst (X * (nomeRatio ℂ).subst Q) * (EI (-(1 / 24)) *
        (detInvSqrt.map (algebraMap ℚ ℂ) *
          ((exp ℂ).subst ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m)) *
            detInvSqrt.map (algebraMap ℚ ℂ)))) := by
    ext N
    rw [hstar N, coeff_subst_X_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coeff_mk, hEIs n, hLinf, mul_assoc]
  rw [← h16, subst_sixteen cinf hQ0] at hser
  have hDc : constantCoeff (detInvSqrt.map (algebraMap ℚ ℂ)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_detInvSqrt, map_one]
  have hDne : detInvSqrt.map (algebraMap ℚ ℂ) * detInvSqrt.map (algebraMap ℚ ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg constantCoeff h0
    rw [map_mul, hDc, map_zero] at h1
    norm_num at h1
  have hAV : (mk fun n => (16 : ℂ) ^ n * cinf n).subst Q * (EI (-(1 / 24)) *
      (exp ℂ).subst ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m))) = 1 := by
    refine mul_right_cancel₀ hDne ?_
    rw [one_mul]
    conv_rhs => rw [hser]
    ring
  have hV : EI (-(1 / 24)) *
      (exp ℂ).subst ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m)) =
      (exp ℂ).subst ((1 / 24 : ℂ) • (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
        I0def sigmaStar (fun m => -sigmaStar m))) := by
    rw [EI, ← exp_subst_add _ _ (by rw [map_mul, hI0, mul_zero]) (hc1 _)]
    congr 1
    rw [smul_sub, smul_eq_C_mul, smul_eq_C_mul, map_neg]
    ring
  have hd0 : constantCoeff ((1 / 24 : ℂ) • (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
      I0def sigmaStar (fun m => -sigmaStar m))) = 0 := by
    rw [smul_eq_C_mul, map_mul, map_sub, hcΦ, hI0, sub_zero, mul_zero]
  have hV24 : (exp ℂ).subst ((1 / 24 : ℂ) • (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
        I0def sigmaStar (fun m => -sigmaStar m))) ^ 24 =
      (exp ℂ).subst (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
        I0def sigmaStar (fun m => -sigmaStar m)) := by
    rw [exp_subst_pow _ hd0 24, smul_smul, show ((24 : ℕ) : ℂ) * (1 / 24) = 1 by norm_num,
      one_smul]
  have hAB : (mk fun n => (16 : ℂ) ^ n * cinf n).subst Q ^ 2 *
      ((etaSqPow 1).map (algebraMap ℚ ℂ)).subst Q = 1 := by
    have h1 := congrArg (PowerSeries.subst Q) hgen
    rwa [subst_mul hQs, subst_pow hQs, subst_one' hQs] at h1
  rw [hV] at hAV
  have hfirst : (exp ℂ).subst (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
        I0def sigmaStar (fun m => -sigmaStar m)) =
      ((etaSqPow 12).map (algebraMap ℚ ℂ)).subst Q := by
    rw [etaSqPow_pow 12, map_pow, subst_pow hQs, ← hV24]
    calc (exp ℂ).subst ((1 / 24 : ℂ) • (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
          I0def sigmaStar (fun m => -sigmaStar m))) ^ 24
        = (exp ℂ).subst ((1 / 24 : ℂ) • (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
            I0def sigmaStar (fun m => -sigmaStar m))) ^ 24 *
            ((mk fun n => (16 : ℂ) ^ n * cinf n).subst Q ^ 2 *
              ((etaSqPow 1).map (algebraMap ℚ ℂ)).subst Q) ^ 12 := by
          rw [hAB, one_pow, mul_one]
      _ = ((mk fun n => (16 : ℂ) ^ n * cinf n).subst Q *
            (exp ℂ).subst ((1 / 24 : ℂ) • (PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) -
              I0def sigmaStar (fun m => -sigmaStar m)))) ^ 24 *
            ((etaSqPow 1).map (algebraMap ℚ ℂ)).subst Q ^ 12 := by ring
      _ = ((etaSqPow 1).map (algebraMap ℚ ℂ)).subst Q ^ 12 := by rw [hAV, one_pow, one_mul]
  refine ⟨hfirst, fun R hR => ?_⟩
  rw [hfirst]
  have hJ := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hJ1.2.2
  rw [map_mul, map_mul, map_mul, map_mul, map_sub, map_one, map_pow, map_zq, map_th3, map_ofNat,
    PowerSeries.map_X] at hJ
  have hJ' := congrArg (PowerSeries.subst Q) hJ
  rw [← coe_substAlgHom hQs] at hJ'
  simp only [map_mul, map_sub, map_one, map_pow, map_ofNat] at hJ'
  rw [coe_substAlgHom hQs, subst_X hQs, hQ] at hJ'
  have h16' : (16 : PowerSeries ℂ) * Q = X * R := by
    rw [← hR, smul_eq_C_mul, map_ofNat]
  rw [h16', mul_assoc, mul_assoc] at hJ'
  have hprod := mul_left_cancel₀ (X_ne_zero (R := ℂ)) hJ'
  have hη : constantCoeff (((etaSqPow 12).map (algebraMap ℚ ℂ)).subst Q) = 1 :=
    constantCoeff_subst_of_one hQ0 _ (by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_etaSqPow, map_one])
  have hθ : constantCoeff ((th3 ℂ).subst Q) = 1 :=
    constantCoeff_subst_of_one hQ0 _ constantCoeff_th3
  have hR0 : constantCoeff R ≠ 0 := by
    intro h0
    have h1 := congrArg constantCoeff hprod
    rw [map_mul, h0, zero_mul, map_mul, map_sub, map_one, constantCoeff_X, map_pow, hθ] at h1
    norm_num at h1
  rw [mul_assoc, ← hprod, ← mul_assoc, PowerSeries.inv_mul_cancel _ hR0, one_mul]

example (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (h : Stmt_sub_c2_decomp) : Stmt_lem_central_charge :=
  lem_central_charge_of_c2 hF hK hJ1 hJ2 h

end Central

end Virasoro.Sphere
