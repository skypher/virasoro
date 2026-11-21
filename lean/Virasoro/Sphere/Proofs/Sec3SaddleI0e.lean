import Virasoro.Sphere.Proofs.Sec3SaddleI0d
import Virasoro.Sphere.Statements.Sec3d

/-!
# Sphere paper Lemma 3.4 (`lem:saddle`, `sphere/paper.tex` l.713–734)

`𝓘₀ = log(16q(z)/z)` (l.800–808): `z d𝓘₀/dz = 2∑_m a_m² z^m = 1/((1-z)θ₃(q(z))⁴) - 1
= z d/dz log(16q(z)/z)` by the cited identity (2.4), and both sides vanish at `z = 0`.
Then the lemma is assembled from parts (i), (ii), (iii).
-/

namespace Virasoro.Sphere

open Finset PowerSeries

section Generic

variable {A : Type*} [Field A] [CharZero A]

theorem subst_X_self' (f : PowerSeries A) : f.subst (X : PowerSeries A) = f := by
  have h : (fun _ : Unit => (X : PowerSeries A)) = MvPowerSeries.X := by
    funext u
    rfl
  show MvPowerSeries.subst (fun _ : Unit => (X : PowerSeries A)) f = f
  rw [h, MvPowerSeries.subst_self]
  rfl

theorem subst_one'' {Q : PowerSeries A} (hQ : HasSubst Q) :
    (1 : PowerSeries A).subst Q = 1 := by
  rw [← coe_substAlgHom hQ, map_one]

theorem constantCoeff_subst_of_one' {Q : PowerSeries A} (hQ0 : constantCoeff Q = 0)
    (f : PowerSeries A) (hf : constantCoeff f = 1) : constantCoeff (f.subst Q) = 1 := by
  have hQ := HasSubst.of_constantCoeff_zero' hQ0
  have e : f = 1 + (f - 1) := by ring
  have hz : constantCoeff (PowerSeries.subst Q (f - 1)) = 0 :=
    constantCoeff_subst_eq_zero hQ0 _ (by rw [map_sub, hf, map_one, sub_self])
  rw [e, subst_add hQ, subst_one'' hQ, map_add, map_one, hz, add_zero]

/-- `16 q(z) = z · (θ₃⁴/ψ⁴)(q(z))`. -/
theorem sixteen_Q {Q : PowerSeries A} (hQ0 : constantCoeff Q = 0)
    (hQ : (zq A).subst Q = X) : 16 * Q = X * (nomeRatio A).subst Q := by
  have hQs := HasSubst.of_constantCoeff_zero' hQ0
  have h := congrArg (PowerSeries.subst Q) (nomeRatio_mul_zq (A := A))
  have h16 : (16 : PowerSeries A).subst Q = 16 := by
    rw [← coe_substAlgHom hQs, map_ofNat]
  rw [subst_mul hQs, subst_mul hQs, hQ, subst_X hQs, h16] at h
  rw [← h, mul_comm]

end Generic

theorem coeff_one_zq : coeff 1 (zq ℚ) = 16 := by
  rw [zq, show (16 : PowerSeries ℚ) * X * thPsi ℚ ^ 4 * (th3 ℚ ^ 4)⁻¹ =
    X * (16 * thPsi ℚ ^ 4 * (th3 ℚ ^ 4)⁻¹) by ring, show (1 : ℕ) = 0 + 1 from rfl,
    coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, map_pow,
    constantCoeff_inv, map_pow, constantCoeff_thPsi, constantCoeff_th3, map_ofNat]
  norm_num

theorem isUnit_coeff_one_zq : IsUnit (coeff 1 (zq ℚ)) := by
  rw [coeff_one_zq]
  exact isUnit_iff_ne_zero.2 (by norm_num)

/-- `q(z)` over `ℚ`. -/
noncomputable def Q0 : PowerSeries ℚ := (zq ℚ).substInvOfIsUnit isUnit_coeff_one_zq

theorem constantCoeff_Q0 : constantCoeff Q0 = 0 := constantCoeff_substInvOfIsUnit _ _

theorem zq_subst_Q0 : (zq ℚ).subst Q0 = X :=
  subst_substInvOfIsUnit_right (zq ℚ) constantCoeff_zq isUnit_coeff_one_zq

theorem Q0_subst_zq : Q0.subst (zq ℚ) = X :=
  subst_substInvOfIsUnit_left (zq ℚ) constantCoeff_zq isUnit_coeff_one_zq

/-- `16q(z)/z` over `ℚ`. -/
noncomputable def R0 : PowerSeries ℚ := (nomeRatio ℚ).subst Q0

theorem constantCoeff_R0 : constantCoeff R0 = 1 :=
  constantCoeff_subst_of_one' constantCoeff_Q0 _ constantCoeff_nomeRatio

/-- `𝓘₀ = log(16q(z)/z)` over `ℚ`. -/
theorem I0Q_eq (hJ2 : Cited_JacobiIdentities2) : I0Q = (log ℚ).subst (R0 - 1) := by
  have hQs := HasSubst.of_constantCoeff_zero' constantCoeff_Q0
  have hzs : HasSubst (zq ℚ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
  have hF : hyp2F1 = ((th3 ℚ).subst Q0) ^ 2 := by
    have h := congrArg (PowerSeries.subst Q0) hJ2.1
    rw [subst_comp_subst_apply hzs hQs, zq_subst_Q0, subst_X_self', subst_pow hQs] at h
    exact h
  have h16 : (16 : ℚ) • Q0 = X * R0 := by
    rw [R0, ← sixteen_Q constantCoeff_Q0 zq_subst_Q0, smul_eq_C_mul, map_ofNat]
  have hJ := hJ2.2 Q0 constantCoeff_Q0 zq_subst_Q0 R0 h16
  have hd : X * derivative ℚ I0Q = X * derivative ℚ ((log ℚ).subst (R0 - 1)) := by
    rw [X_mul_deriv_I0Q, hJ, hF]
    ring_nf
  refine derivative.ext (mul_left_cancel₀ X_ne_zero hd) ?_
  rw [constantCoeff_I0Q]
  exact (constantCoeff_logOf constantCoeff_R0).symm

/-- `𝓘₀ = log(16q(z)/z)` at the saddle point. -/
theorem I0def_sigmaStar (hJ2 : Cited_JacobiIdentities2) {Q : PowerSeries ℂ}
    (hQ0 : constantCoeff Q = 0) (hQ : (zq ℂ).subst Q = X) {R : PowerSeries ℂ}
    (hR : (16 : ℂ) • Q = X * R) :
    I0def sigmaStar (fun m => -sigmaStar m) = (log ℂ).subst (R - 1) := by
  have hQs := HasSubst.of_constantCoeff_zero' hQ0
  have hzsQ : HasSubst (zq ℚ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
  -- `Q` is the base change of `Q0`
  have hS : (Q0.map (algebraMap ℚ ℂ)).subst (zq ℂ) = X := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) Q0_subst_zq
    rw [PowerSeries.map_X] at h
    rw [← h, ← map_zq (algebraMap ℚ ℂ)]
    exact (PowerSeries.map_subst hzsQ _).symm
  have hQeq : Q = Q0.map (algebraMap ℚ ℂ) := by
    have hzs : HasSubst (zq ℂ) := HasSubst.of_constantCoeff_zero' constantCoeff_zq
    have h := congrArg (PowerSeries.subst Q) hS
    rw [subst_comp_subst_apply hzs hQs, hQ, subst_X_self', subst_X hQs] at h
    exact h.symm
  have hReq : R = R0.map (algebraMap ℚ ℂ) := by
    have h16 : (16 : ℚ) • Q0 = X * R0 := by
      rw [R0, ← sixteen_Q constantCoeff_Q0 zq_subst_Q0, smul_eq_C_mul, map_ofNat]
    have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) h16
    rw [smul_eq_C_mul, map_mul, map_mul, PowerSeries.map_X, PowerSeries.map_C, ← hQeq] at h
    rw [smul_eq_C_mul] at hR
    have h2 : (C ((algebraMap ℚ ℂ) 16) : PowerSeries ℂ) = C 16 := by
      rw [map_ofNat]
    rw [h2, hR] at h
    exact mul_left_cancel₀ X_ne_zero h
  have hI : I0def sigmaStar (fun m => -sigmaStar m) = I0Q.map (algebraMap ℚ ℂ) := by
    ext k
    rw [coeff_I0def_sigmaStar, PowerSeries.coeff_map, I0Q, coeff_mk]
    rfl
  have hR0s : HasSubst (R0 - 1) := HasSubst.of_constantCoeff_zero' (by
    rw [map_sub, constantCoeff_R0, map_one, sub_self])
  rw [hI, I0Q_eq hJ2, hReq]
  have hm := PowerSeries.map_subst (h := algebraMap ℚ ℂ) hR0s (log ℚ)
  rw [map_log] at hm
  have hm' : PowerSeries.map (algebraMap ℚ ℂ) ((log ℚ).subst (R0 - 1)) =
      (log ℂ).subst (PowerSeries.map (algebraMap ℚ ℂ) (R0 - 1)) := hm
  rw [hm', map_sub, map_one]

/-- Lemma 3.4 from the cited Jacobi identities (2.3)–(2.5).

Paper label: lem:saddle -/
theorem lem_saddle_of_cited (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_lem_saddle := by
  refine ⟨fun k hk => ⟨pdeZero_S0 k hk, sum_Bcoef_diag k hk⟩, S0_diag,
    ⟨OmegaCoef_zero, fun m _ => OmegaCoef_neg m⟩, ⟨_, isSaddle_sigmaStar⟩, ?_⟩
  intro σ σb h
  obtain ⟨rfl, rfl⟩ := h.eq_sigmaStar
  refine ⟨rfl, fun Q hQ0 hQ => ⟨fun R hR => I0def_sigmaStar hJ2 hQ0 hQ hR,
    gStar_one hJ1 hJ2 hQ0 hQ, gStar_neg_one hJ2 hQ0 hQ⟩⟩

example (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) : Stmt_lem_saddle :=
  lem_saddle_of_cited hJ1 hJ2

end Virasoro.Sphere
