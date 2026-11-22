import Virasoro.Sphere.Proofs.Sec3CentralFinal
import Virasoro.Sphere.Proofs.Sec3FpowExp
import Virasoro.Sphere.Proofs.Sec5TopLayerH
import Virasoro.Sphere.Proofs.Sec3PolyH
import Virasoro.Sphere.Proofs.Sec3LargeDeltaAt

/-!
# Theorem 3.1 from Lemmas 3.2–3.7 (sphere paper)

sphere/paper.tex l.1183–1203.  For `μ > 0` and real `Δ_i`, with `Δ = λ² + μ²`: by
Lemma 3.3(iii), `(16q/z)^{-λ²} ℬ(z)` tends coefficientwise to
`det(I - M²)^{-1/2} exp(μ²Φ_c^raw + (Δ₁+Δ₄-1/8)Φ₁ + (Δ₂+Δ₃-1/8)Φ₂)`, which by Lemmas 3.4–3.7
and `θ₄⁴ = (1-z)θ₃⁴` is `(1-z)^{(c-1)/24-Δ₂-Δ₃} θ₃^{(c-1)/2-4∑Δ_j}`; hence
`lim H(c,Δ,Δ_i;q) = 1` in `ℂ[[q]]`, and Lemma 3.2(iii) extends this to all complex `(c,Δ_i)`.
-/

namespace Virasoro.Sphere

open PowerSeries Filter Topology

/-- `(1-z(q))^{(c-1)/24-Δ₂-Δ₃} θ₃(q)^{(c-1)/2-4∑Δ_j}`: the part of `Φ̃` that does not depend on
`Δ`. -/
noncomputable def P0 (c : ℂ) (Δc : Fin 4 → ℂ) : PowerSeries ℂ :=
  fpow (1 - zq ℂ) ((c - 1) / 24 - Δc 1 - Δc 2) *
    fpow (th3 ℂ) ((c - 1) / 2 - 4 * (Δc 0 + Δc 1 + Δc 2 + Δc 3))

theorem constantCoeff_P0 (c : ℂ) (Δc : Fin 4 → ℂ) : constantCoeff (P0 c Δc) = 1 := by
  rw [P0, map_mul, constantCoeff_fpowC, constantCoeff_fpowC, one_mul]

theorem hasSubst_zq : HasSubst (zq ℂ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq

theorem Qc_subst_zq : PowerSeries.subst (zq ℂ) (Q0.map (algebraMap ℚ ℂ)) = X := by
  have hzsQ : HasSubst (zq ℚ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) Q0_subst_zq
  rw [PowerSeries.map_X] at h
  rw [← h, ← map_zq (algebraMap ℚ ℂ)]
  exact (PowerSeries.map_subst hzsQ _).symm

/-- `f(q(z))` at `z = z(q)` is `f(q)`. -/
theorem subst_zq_subst_Qc (f : PowerSeries ℂ) :
    PowerSeries.subst (zq ℂ) (f.subst (Q0.map (algebraMap ℚ ℂ))) = f := by
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hQ0c) hasSubst_zq, Qc_subst_zq,
    subst_X_self]

theorem coeff_subst_zq (F : PowerSeries ℂ) (m : ℕ) :
    coeff m (PowerSeries.subst (zq ℂ) F) =
      ∑ k ∈ Finset.range (m + 1), coeff k F * coeff m (zq ℂ ^ k) := by
  have h := compS_eq_subst (fun k => coeff k F) (constantCoeff_zq (A := ℂ))
  have hF : PowerSeries.mk (fun k => coeff k F) = F := by
    ext k
    rw [coeff_mk]
  rw [hF] at h
  rw [← h, compS, coeff_mk]

theorem sixteen_Qc : (16 : ℂ) • Q0.map (algebraMap ℚ ℂ) =
    X * (nomeRatio ℂ).subst (Q0.map (algebraMap ℚ ℂ)) := by
  rw [smul_eq_C_mul, map_ofNat]
  exact sixteen_Q hQ0c hQc

/-- `e^{a𝓘₀}` at `z = z(q)` is `(16q/z(q))^a`. -/
theorem EI_subst_zq (hJ2 : Cited_JacobiIdentities2) (a : ℂ) :
    PowerSeries.subst (zq ℂ) (EI a) = fpow (nomeRatio ℂ) a := by
  have hRc : constantCoeff ((nomeRatio ℂ).subst (Q0.map (algebraMap ℚ ℂ))) = 1 :=
    constantCoeff_subst_of_one hQ0c _ constantCoeff_nomeRatio
  rw [EI, I0def_sigmaStar hJ2 hQ0c hQc sixteen_Qc, ← smul_eq_C_mul,
    subst_exp_smul_log _ _ hRc constantCoeff_zq, subst_zq_subst_Qc,
    exp_smul_log _ constantCoeff_nomeRatio]

theorem coeff_P0_inv_mul (c : ℂ) (Δc : Fin 4 → ℂ) (N : ℕ) (L : PowerSeries ℂ)
    (hL : PowerSeries.subst (zq ℂ) L = P0 c Δc) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, coeff p.1 (P0 c Δc)⁻¹ *
        ∑ k ∈ Finset.range (p.2 + 1), coeff k L * coeff p.2 (zq ℂ ^ k)) / 16 ^ N =
      if N = 0 then 1 else 0 := by
  simp only [← coeff_subst_zq]
  rw [← coeff_mul, hL, PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_P0]; exact one_ne_zero)]
  by_cases h : N = 0
  · subst h
    simp
  · simp [PowerSeries.coeff_one, h]

section

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- The value of `H_N` at `Δ = λ² + μ²` (Definition 2.2 with Lemma 3.2(i)). -/
theorem evalAt_Hsph_split (hJ2 : Cited_JacobiIdentities2) (μ : ℝ) (hμ : 0 < μ) (lam : ℝ)
    (hlam : 0 < lam) (Δc : Fin 4 → ℂ) (N : ℕ) :
    evalAt ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) (Hsph (1 + 24 * (μ : ℂ) ^ 2) Δc N) =
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
        coeff p.1 (P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)⁻¹ *
          ∑ k ∈ Finset.range (p.2 + 1), coeff k (EI (-(lam : ℂ) ^ 2) *
            PowerSeries.mk fun j => evalAt ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
              (Bsph (1 + 24 * (μ : ℂ) ^ 2) Δc j)) * coeff p.2 (zq ℂ ^ k)) / 16 ^ N := by
  have hreg : ∀ m ≤ N, RegAt ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
      (Bsph (1 + 24 * (μ : ℂ) ^ 2) Δc m) := fun m _ =>
    regAt_Bsph Δc (((lem_fock_verma_of_cited hF hK).1 μ hμ lam hlam).1.1 m)
  have hP0c := constantCoeff_P0 (1 + 24 * (μ : ℂ) ^ 2) Δc
  have hPhi : PhiAt (1 + 24 * (μ : ℂ) ^ 2) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) Δc =
      fpow (nomeRatio ℂ) ((lam : ℂ) ^ 2) * P0 (1 + 24 * (μ : ℂ) ^ 2) Δc := by
    unfold PhiAt P0
    rw [show (lam : ℂ) ^ 2 + (μ : ℂ) ^ 2 - (1 + 24 * (μ : ℂ) ^ 2 - 1) / 24 = (lam : ℂ) ^ 2 by ring]
    ring
  have hne : constantCoeff (fpow (nomeRatio ℂ) ((lam : ℂ) ^ 2) *
      P0 (1 + 24 * (μ : ℂ) ^ 2) Δc) ≠ 0 := by
    rw [map_mul, constantCoeff_fpowC, hP0c, one_mul]
    exact one_ne_zero
  have hinv : (PhiAt (1 + 24 * (μ : ℂ) ^ 2) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) Δc)⁻¹ =
      fpow (nomeRatio ℂ) (-(lam : ℂ) ^ 2) * (P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)⁻¹ := by
    rw [hPhi]
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one hne]
    calc fpow (nomeRatio ℂ) (-(lam : ℂ) ^ 2) * (P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)⁻¹ *
          (fpow (nomeRatio ℂ) ((lam : ℂ) ^ 2) * P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)
        = (fpow (nomeRatio ℂ) (-(lam : ℂ) ^ 2) * fpow (nomeRatio ℂ) ((lam : ℂ) ^ 2)) *
            ((P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)⁻¹ * P0 (1 + 24 * (μ : ℂ) ^ 2) Δc) := by ring
      _ = 1 := by
        rw [fpow_neg_mul constantCoeff_nomeRatio,
          PowerSeries.inv_mul_cancel _ (by rw [hP0c]; exact one_ne_zero), one_mul]
  rw [evalAt_Hsph _ _ Δc N hreg, compS_eq_subst _ constantCoeff_zq, hinv, ← EI_subst_zq hJ2,
    show PowerSeries.subst (zq ℂ) (EI (-(lam : ℂ) ^ 2)) * (P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)⁻¹ *
        PowerSeries.subst (zq ℂ) (PowerSeries.mk fun j => evalAt ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
          (Bsph (1 + 24 * (μ : ℂ) ^ 2) Δc j)) =
      (P0 (1 + 24 * (μ : ℂ) ^ 2) Δc)⁻¹ * PowerSeries.subst (zq ℂ) (EI (-(lam : ℂ) ^ 2) *
        PowerSeries.mk fun j => evalAt ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
          (Bsph (1 + 24 * (μ : ℂ) ^ 2) Δc j)) by
      rw [subst_mul hasSubst_zq]
      ring, coeff_mul]
  simp only [coeff_subst_zq]

include hF hK in
/-- The limit series at `z = z(q)` (sphere/paper.tex l.1186–1198): with Lemmas 3.4–3.7 and
`θ₄⁴ = (1-z)θ₃⁴`,
`det^{-1/2} exp(m Φ_c^raw + aΦ₁ + bΦ₂) = (1-z)^{m-b-1/8} θ₃^{12m-4a-4b-1}`. -/
theorem Linf_subst (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (h37 : Stmt_lem_central_charge) {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) (m2 a b : ℂ) :
    PowerSeries.subst (zq ℂ) (detInvSqrt.map (algebraMap ℚ ℂ) * (exp ℂ).subst
        (m2 • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
          a • MvPowerSeries.subst sigmaStar S21 + b • MvPowerSeries.subst sigmaStar S22)) =
      fpow (1 - zq ℂ) (m2 - b - 1 / 8) * fpow (th3 ℂ) (12 * m2 - 4 * a - 4 * b - 1) := by
  obtain ⟨-, -, h⟩ := lem_ext_exponents_of_cited hF hK hJ1 hJ2 S1t S2c S21 S22 hE
  obtain ⟨h22, h21⟩ := h _ _ isSaddle_sigmaStar _ hQ0c hQc
  obtain ⟨hc2, hY⟩ := exp_Phi_eighth hF hK hJ1 hJ2 hE
  obtain ⟨-, h37b⟩ := h37 S1t S2c S21 S22 hE _ _ isSaddle_sigmaStar _ hQ0c hQc
  have h37c := h37b _ sixteen_Qc
  have hI := I0def_sigmaStar hJ2 hQ0c hQc sixteen_Qc
  have hI0 := constantCoeff_I0s hJ2
  have hcΦ := constantCoeff_PhiCraw hF hK hE
  set θ3c := (th3 ℂ).subst (Q0.map (algebraMap ℚ ℂ)) with hθ3
  set θ4c := (th4 ℂ).subst (Q0.map (algebraMap ℚ ℂ)) with hθ4
  set Rc := (nomeRatio ℂ).subst (Q0.map (algebraMap ℚ ℂ)) with hRc
  set Φc := PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) with hΦc
  set I0 := I0def sigmaStar (fun m => -sigmaStar m) with hI0def
  have h3 : constantCoeff θ3c = 1 := constantCoeff_subst_of_one hQ0c _ constantCoeff_th3
  have h4 : constantCoeff θ4c = 1 := constantCoeff_subst_of_one hQ0c _ constantCoeff_th4
  have hR1 : constantCoeff Rc = 1 := constantCoeff_subst_of_one hQ0c _ constantCoeff_nomeRatio
  have hx : constantCoeff (1 - X : PowerSeries ℂ) = 1 := by
    rw [map_sub, map_one, constantCoeff_X, sub_zero]
  have hl : ∀ θ : PowerSeries ℂ, constantCoeff θ = 1 →
      constantCoeff ((log ℂ).subst (θ - 1)) = 0 := by
    intro θ hθ
    have h1 : constantCoeff (θ - 1) = 0 := by rw [map_sub, hθ, map_one, sub_self]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  set ℓx := (log ℂ).subst ((1 - X : PowerSeries ℂ) - 1) with hℓx
  set ℓ3 := (log ℂ).subst (θ3c - 1) with hℓ3
  set ℓ4 := (log ℂ).subst (θ4c - 1) with hℓ4
  have hlx : constantCoeff ℓx = 0 := hl _ hx
  have hl3 : constantCoeff ℓ3 = 0 := hl _ h3
  have hl4 : constantCoeff ℓ4 = 0 := hl _ h4
  have hsm : ∀ (s : ℂ) (g : PowerSeries ℂ), constantCoeff g = 0 → constantCoeff (s • g) = 0 :=
    fun s g hg => by rw [smul_eq_C_mul, map_mul, hg, mul_zero]
  -- `4 log θ₄ = log(1 - z) + 4 log θ₃`
  have hfour : (4 : ℂ) • ℓ4 = ℓx + (4 : ℂ) • ℓ3 := by
    have hA := log_exp_subst _ (hsm 4 ℓ4 hl4)
    have hB := log_exp_subst (ℓx + (4 : ℂ) • ℓ3) (by rw [map_add, hlx, hsm 4 ℓ3 hl3, add_zero])
    have e1 : (exp ℂ).subst ((4 : ℂ) • ℓ4) = θ4c ^ 4 := by
      have := exp_subst_pow ℓ4 hl4 4
      rw [exp_log_subst θ4c h4] at this
      rw [this]
      norm_num
    have e2 : (exp ℂ).subst (ℓx + (4 : ℂ) • ℓ3) = (1 - X) * θ3c ^ 4 := by
      have := exp_subst_pow ℓ3 hl3 4
      rw [exp_log_subst θ3c h3] at this
      rw [exp_subst_add _ _ hlx (hsm 4 ℓ3 hl3), exp_log_subst _ hx, this]
      norm_num
    rw [← hA, ← hB, e1, e2, one_sub_mul_th3 hJ1 hQ0c hQc]
  -- `Φ_c^raw = log(1 - z) + 12 log θ₃`
  have hΦ : Φc = ℓx + (12 : ℂ) • ℓ3 := by
    have hd0 : constantCoeff (Φc - I0) = 0 := by rw [map_sub, hcΦ, hI0, sub_zero]
    have hd1 : constantCoeff (ℓx + (12 : ℂ) • ℓ3 + (-1 : ℂ) • I0) = 0 := by
      rw [map_add, map_add, hlx, hsm 12 ℓ3 hl3, hsm (-1) I0 hI0, add_zero, add_zero]
    have hA := log_exp_subst _ hd0
    have hB := log_exp_subst _ hd1
    have e12 : (exp ℂ).subst ((12 : ℂ) • ℓ3) = θ3c ^ 12 := by
      have := exp_subst_pow ℓ3 hl3 12
      rw [exp_log_subst θ3c h3] at this
      rw [this]
      norm_num
    have eI : (exp ℂ).subst ((-1 : ℂ) • I0) = Rc⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [hR1]; exact one_ne_zero)]
      have hRe : (exp ℂ).subst I0 = Rc := by rw [hI, exp_log_subst _ hR1]
      rw [← hRe]
      rw [← exp_subst_add _ _ (hsm (-1) I0 hI0) hI0, neg_one_smul, neg_add_cancel,
        exp_subst_zero]
    have e2 : (exp ℂ).subst (ℓx + (12 : ℂ) • ℓ3 + (-1 : ℂ) • I0) = Rc⁻¹ * (1 - X) * θ3c ^ 12 := by
      rw [exp_subst_add _ _ (by rw [map_add, hlx, hsm 12 ℓ3 hl3, add_zero]) (hsm (-1) I0 hI0),
        exp_subst_add _ _ hlx (hsm 12 ℓ3 hl3), exp_log_subst _ hx, e12, eI]
      ring
    have h5 : Φc - I0 = ℓx + (12 : ℂ) • ℓ3 + (-1 : ℂ) • I0 := by
      rw [← hA, ← hB, h37c, e2]
    rw [neg_one_smul, ← sub_eq_add_neg] at h5
    exact sub_left_injective h5
  have hΦ1 : MvPowerSeries.subst sigmaStar S21 = (-4 : ℂ) • ℓ3 := h21
  have hΦ2 : MvPowerSeries.subst sigmaStar S22 = (-4 : ℂ) • ℓ4 := h22
  have hℓ4' : ℓ4 = (1 / 4 : ℂ) • ℓx + ℓ3 := by
    have : ℓ4 = (1 / 4 : ℂ) • ((4 : ℂ) • ℓ4) := by
      rw [smul_smul]
      norm_num
    rw [this, hfour, smul_add, smul_smul]
    norm_num
  have hexp : (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
        (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22 +
        (m2 • Φc + a • MvPowerSeries.subst sigmaStar S21 +
          b • MvPowerSeries.subst sigmaStar S22) =
      (m2 - b - 1 / 8) • ℓx + (12 * m2 - 4 * a - 4 * b - 1) • ℓ3 := by
    rw [hΦ1, hΦ2, hΦ, hℓ4']
    module
  have hcE : constantCoeff (m2 • Φc + a • MvPowerSeries.subst sigmaStar S21 +
      b • MvPowerSeries.subst sigmaStar S22) = 0 := by
    rw [hΦ1, hΦ2, map_add, map_add, hsm m2 Φc hcΦ, hsm a _ (hsm (-4) ℓ3 hl3),
      hsm b _ (hsm (-4) ℓ4 hl4), add_zero, add_zero]
  rw [← hY, ← exp_subst_add _ _ hc2 hcE, hexp,
    exp_subst_add _ _ (hsm _ ℓx hlx) (hsm _ ℓ3 hl3), subst_mul hasSubst_zq,
    subst_exp_smul_log _ _ hx constantCoeff_zq, subst_exp_smul_log _ _ h3 constantCoeff_zq,
    subst_zq_subst_Qc, subst_sub hasSubst_zq, subst_one' hasSubst_zq, subst_X hasSubst_zq,
    exp_smul_log _ (by rw [map_sub, map_one, constantCoeff_zq, sub_zero]),
    exp_smul_log _ constantCoeff_th3]

include hF hK in
/-- `lim_{λ→∞} H_N(1+24μ², λ²+μ², Δ_i) = δ_{N,0}` for `μ > 0` and real `Δ_i`
(sphere/paper.tex l.1183–1200). -/
theorem tendsto_Hsph_of_central (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (h37 : Stmt_lem_central_charge) (N : ℕ) (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) :
    Tendsto (fun lam : ℝ => RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
        (Hsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) N))
      atTop (𝓝 (if N = 0 then 1 else 0)) := by
  obtain ⟨S1t, S2c, S21, S22, hE, -, -, -⟩ := sub_lam_orders hF hK
  have hL : PowerSeries.subst (zq ℂ) (detInvSqrt.map (algebraMap ℚ ℂ) * (exp ℂ).subst
      (((μ : ℂ) ^ 2) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
        ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S21 +
        ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S22)) =
      P0 (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) := by
    rw [Linf_subst hF hK hJ1 hJ2 h37 hE, P0]
    congr 2 <;> ring
  rw [← coeff_P0_inv_mul _ _ N _ hL]
  refine Tendsto.congr' (f₁ := fun lam : ℝ =>
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
      coeff p.1 (P0 (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)))⁻¹ *
        ∑ k ∈ Finset.range (p.2 + 1), coeff k (EI (-(lam : ℂ) ^ 2) *
          PowerSeries.mk fun j => evalAt ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
            (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) j)) * coeff p.2 (zq ℂ ^ k)) /
      16 ^ N) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact (evalAt_Hsph_split hF hK hJ2 μ hμ lam hlam _ N).symm
  · exact (tendsto_finset_sum _ fun p _ => tendsto_const_nhds.mul
      (tendsto_finset_sum _ fun k _ =>
        (lam_limit hF hK hJ2 hE μ hμ Δe k).mul tendsto_const_nhds)).div_const _

include hF hK in
/-- Theorem 3.1 from Lemma 3.7 (sphere/paper.tex l.1183–1203): Lemmas 3.2–3.6 are proved, so
`lim_{Δ→∞} H_N = δ_{N,0}` follows from the central-charge identity. -/
theorem thm_large_delta_of_central (hJ1 : Cited_JacobiIdentities)
    (hJ2 : Cited_JacobiIdentities2) (h37 : Stmt_lem_central_charge) : Stmt_thm_large_delta :=
  thm_large_delta_iff.2 fun N => (lem_fock_verma_of_cited hF hK).2 N fun μ hμ Δe =>
    tendsto_Hsph_of_central hF hK hJ1 hJ2 h37 N μ hμ Δe

include hF hK in
/-- Theorem 3.1 from Steps 1–3 of the proof of Lemma 3.7. -/
theorem thm_large_delta_of_c2 (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (h : Stmt_sub_c2_decomp) : Stmt_thm_large_delta :=
  thm_large_delta_of_central hF hK hJ1 hJ2 (lem_central_charge_of_c2 hF hK hJ1 hJ2 h)

example (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (h37 : Stmt_lem_central_charge) : Stmt_thm_large_delta :=
  thm_large_delta_of_central hF hK hJ1 hJ2 h37

end

end Virasoro.Sphere
