import Virasoro.Sphere.Proofs.Sec3SaddleVal
import Virasoro.Sphere.CitedJacobi
import Virasoro.Sphere.Cited

/-!
# Sphere paper Lemma 3.4(iii): `1 - g_*(1) = θ₄(q(z))⁻²`, `1 - g_*(-1) = θ₃(q(z))⁻²`
(`sphere/paper.tex` l.729–733)

From `Sec3SaddleVal.lean`: `(1 - g_*(1)) ₂F₁ = (1-z)^{-1/2}` and `(1 - g_*(-1)) ₂F₁ = 1`.  The
cited Jacobi identities `₂F₁(z(q)) = θ₃(q)²` and `1 - z(q) = θ₄(q)⁴/θ₃(q)⁴` then give the
values.

Consumer: the values of `g_*(±1)` in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem aSer_zero : aSer 0 = 1 := by
  rw [aSer, Nat.cast_zero, OmegaCoef_zero]

/-- `1 - ∑_m (i m c_m) σ_{*,m} = ∑_m c_m a_m z^m` for `c_0 = 1`. -/
theorem one_sub_subst_lin (c : ℕ → ℚ) (hc0 : c 0 = 1) (g : ℕ → ℂ)
    (hg : ∀ m, 1 ≤ m → g m = Complex.I * (m : ℂ) * (c m : ℂ)) :
    1 - MvPowerSeries.subst sigmaStar (linSeries g) =
      (ySer c).map (algebraMap ℚ ℂ) := by
  ext k
  rw [map_sub, coeff_subst_linSeries _ (fun m => by simpa using smul_sigmaStar_dvd 1 m),
    PowerSeries.coeff_map, ySer, PowerSeries.coeff_mk, sum_range_succ']
  have e := sum_Icc_one_eq_range
    (fun m => c m * PowerSeries.coeff (k - m) (aSer m)) k
  beta_reduce at e
  rw [← e, hc0, aSer_zero, PowerSeries.coeff_one, Nat.sub_zero, PowerSeries.coeff_one]
  have hsum : ∑ m ∈ Icc 1 k, g m * PowerSeries.coeff k (sigmaStar m.toPNat') =
      -∑ m ∈ Icc 1 k, ((c m : ℂ) * ((PowerSeries.coeff (k - m) (aSer m) : ℚ) : ℂ)) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hm1 := mem_Icc.1 hm
    have hcoe : ((m.toPNat' : ℕ+) : ℕ) = m := by rw [Nat.toPNat'_coe, if_pos (by omega)]
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [hg m hm1.1, coeff_sigmaStar, hcoe, if_pos hm1.2]
    rw [show Complex.I * (m : ℂ) * (c m : ℂ) * (Complex.I * (1 / (m : ℂ)) *
        ((PowerSeries.coeff (k - m) (aSer m) : ℚ) : ℂ)) =
      (Complex.I * Complex.I) * ((m : ℂ) * (1 / (m : ℂ))) *
        ((c m : ℂ) * ((PowerSeries.coeff (k - m) (aSer m) : ℚ) : ℂ)) by ring,
      Complex.I_mul_I, mul_one_div_cancel hm0]
    ring
  rw [hsum]
  simp only [eq_ratCast]
  push_cast
  split_ifs <;> ring

theorem gAt_one_coeff (m : ℕ) :
    2 * Complex.I * ∑ n ∈ Icc 1 m, (n : ℂ) * (1 : ℂ) ^ n * tcoef n m =
      Complex.I * (m : ℂ) * (halfBinom m : ℂ) := by
  have h := sum_n_psi m
  have hc : ∑ n ∈ Icc 1 m, (n : ℂ) * (1 : ℂ) ^ n * tcoef n m =
      (m : ℂ) * (halfBinom m : ℂ) / 2 := by
    simp only [tcoef_eq, one_pow, mul_one]
    exact_mod_cast h
  rw [hc]
  ring

theorem gAt_neg_one_coeff (m : ℕ) (hm : 1 ≤ m) :
    2 * Complex.I * ∑ n ∈ Icc 1 m, (n : ℂ) * (-1 : ℂ) ^ n * tcoef n m =
      Complex.I * (m : ℂ) * ((PowerSeries.coeff m sOne : ℚ) : ℂ) := by
  have h := sum_n_alt_psi m hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h2 := two_mul_coeff_sOne j
  rw [Nat.add_sub_cancel] at h
  have hq : ∑ n ∈ Icc 1 (j + 1), (n : ℚ) * ((-1) ^ n * PowerSeries.coeff (j + 1) (psi n)) =
      ((j : ℚ) + 1) * PowerSeries.coeff (j + 1) sOne / 2 := by
    rw [h]
    linarith
  have hc : ∑ n ∈ Icc 1 (j + 1), (n : ℂ) * (-1 : ℂ) ^ n * tcoef n (j + 1) =
      ((j : ℂ) + 1) * ((PowerSeries.coeff (j + 1) sOne : ℚ) : ℂ) / 2 := by
    simp only [tcoef_eq, mul_assoc]
    exact_mod_cast hq
  rw [hc]
  push_cast
  ring

theorem one_sub_gAt_one :
    1 - MvPowerSeries.subst sigmaStar (gAt 1) = (ySer halfBinom).map (algebraMap ℚ ℂ) :=
  one_sub_subst_lin halfBinom (by simp [halfBinom, gbinom]) _ (fun m _ => gAt_one_coeff m)

theorem one_sub_gAt_neg_one :
    1 - MvPowerSeries.subst sigmaStar (gAt (-1)) =
      (ySer fun m => PowerSeries.coeff m sOne).map (algebraMap ℚ ℂ) :=
  one_sub_subst_lin (fun m => PowerSeries.coeff m sOne)
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_sOne]) _
    (fun m hm => gAt_neg_one_coeff m hm)

/-! ### The Jacobi identities at `q(z)` -/

section Jacobi

variable {A B : Type*} [Field A] [Field B] (f : A →+* B)

theorem map_th4 : PowerSeries.map f (th4 A) = th4 B := by
  ext n
  simp [th4, PowerSeries.coeff_map]

theorem constantCoeff_th4 : PowerSeries.constantCoeff (th4 A) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [th4, theta4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]

end Jacobi

theorem subst_X_self (f : PowerSeries ℂ) : f.subst (PowerSeries.X : PowerSeries ℂ) = f := by
  have h : (fun _ : Unit => (PowerSeries.X : PowerSeries ℂ)) = MvPowerSeries.X := by
    funext u
    rfl
  show MvPowerSeries.subst (fun _ : Unit => (PowerSeries.X : PowerSeries ℂ)) f = f
  rw [h, MvPowerSeries.subst_self]
  rfl

theorem subst_one' {Q : PowerSeries ℂ} (hQ : PowerSeries.HasSubst Q) :
    (1 : PowerSeries ℂ).subst Q = 1 := by
  rw [← PowerSeries.coe_substAlgHom hQ, map_one]

theorem constantCoeff_subst_of_one {Q : PowerSeries ℂ} (hQ0 : PowerSeries.constantCoeff Q = 0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.constantCoeff (f.subst Q) = 1 := by
  have hQ := PowerSeries.HasSubst.of_constantCoeff_zero' hQ0
  have e : f = 1 + (f - 1) := by ring
  have hz : PowerSeries.constantCoeff (PowerSeries.subst Q (f - 1)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hQ0 _ (by rw [map_sub, hf, map_one, sub_self])
  rw [e, PowerSeries.subst_add hQ, subst_one' hQ, map_add, map_one, hz, add_zero]

/-- `₂F₁(1/2,1/2;1;z) = θ₃(q(z))²`. -/
theorem hyp2F1_eq_th3 (hJ2 : Cited_JacobiIdentities2) {Q : PowerSeries ℂ}
    (hQ0 : PowerSeries.constantCoeff Q = 0) (hQ : (zq ℂ).subst Q = PowerSeries.X) :
    hyp2F1.map (algebraMap ℚ ℂ) = ((th3 ℂ).subst Q) ^ 2 := by
  have hQs := PowerSeries.HasSubst.of_constantCoeff_zero' hQ0
  have hzs : PowerSeries.HasSubst (zq ℂ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_zq
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hJ2.1
  have hm : PowerSeries.map (algebraMap ℚ ℂ) (hyp2F1.subst (zq ℚ)) =
      (hyp2F1.map (algebraMap ℚ ℂ)).subst (zq ℂ) := by
    rw [← map_zq (algebraMap ℚ ℂ)]
    exact PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_zq) _
  rw [hm, map_pow, map_th3] at h
  have h2 := congrArg (PowerSeries.subst Q) h
  rw [PowerSeries.subst_comp_subst_apply hzs hQs, hQ, subst_X_self,
    PowerSeries.subst_pow hQs] at h2
  exact h2

/-- `(1 - z) θ₃(q(z))⁴ = θ₄(q(z))⁴`. -/
theorem one_sub_mul_th3 (hJ1 : Cited_JacobiIdentities) {Q : PowerSeries ℂ}
    (hQ0 : PowerSeries.constantCoeff Q = 0) (hQ : (zq ℂ).subst Q = PowerSeries.X) :
    (1 - PowerSeries.X) * ((th3 ℂ).subst Q) ^ 4 = ((th4 ℂ).subst Q) ^ 4 := by
  have hQs := PowerSeries.HasSubst.of_constantCoeff_zero' hQ0
  have h3 : PowerSeries.constantCoeff (th3 ℚ ^ 4) ≠ 0 := by
    rw [map_pow, constantCoeff_th3]
    norm_num
  have h1 : (1 - zq ℚ) * th3 ℚ ^ 4 = th4 ℚ ^ 4 := by
    rw [hJ1.1, mul_assoc, PowerSeries.inv_mul_cancel _ h3, mul_one]
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) h1
  rw [map_mul, map_sub, map_one, map_zq, map_pow, map_pow, map_th3, map_th4] at h
  have h2 := congrArg (PowerSeries.subst Q) h
  rw [PowerSeries.subst_mul hQs, PowerSeries.subst_sub hQs, subst_one' hQs, hQ,
    PowerSeries.subst_pow hQs, PowerSeries.subst_pow hQs] at h2
  exact h2

/-- `1 - g_*(-1) = θ₃(q(z))⁻²`. -/
theorem gStar_neg_one (hJ2 : Cited_JacobiIdentities2) {Q : PowerSeries ℂ}
    (hQ0 : PowerSeries.constantCoeff Q = 0) (hQ : (zq ℂ).subst Q = PowerSeries.X) :
    1 - MvPowerSeries.subst sigmaStar (gAt (-1)) = (((th3 ℂ).subst Q) ^ 2)⁻¹ := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) ySer_two
  rw [map_mul, map_one, hyp2F1_eq_th3 hJ2 hQ0 hQ, ← one_sub_gAt_neg_one] at h
  have hc : PowerSeries.constantCoeff (((th3 ℂ).subst Q) ^ 2) ≠ 0 := by
    rw [map_pow, constantCoeff_subst_of_one hQ0 _ constantCoeff_th3]
    norm_num
  exact (PowerSeries.eq_inv_iff_mul_eq_one hc).2 h

/-- `1 - g_*(1) = θ₄(q(z))⁻²`. -/
theorem gStar_one (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    {Q : PowerSeries ℂ} (hQ0 : PowerSeries.constantCoeff Q = 0)
    (hQ : (zq ℂ).subst Q = PowerSeries.X) :
    1 - MvPowerSeries.subst sigmaStar (gAt 1) = (((th4 ℂ).subst Q) ^ 2)⁻¹ := by
  set Y := 1 - MvPowerSeries.subst sigmaStar (gAt 1) with hY
  set T3 := (th3 ℂ).subst Q with hT3
  set T4 := (th4 ℂ).subst Q with hT4
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) ySer_one
  rw [map_mul, hyp2F1_eq_th3 hJ2 hQ0 hQ, ← one_sub_gAt_one] at h
  have hs := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hser_sq
  rw [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X] at hs
  have h4 := one_sub_mul_th3 hJ1 hQ0 hQ
  have hsq : (Y * T4 ^ 2) ^ 2 = 1 := by
    linear_combination (Y ^ 2) * (-h4) + (1 - PowerSeries.X) *
      (Y * T3 ^ 2 + PowerSeries.map (algebraMap ℚ ℂ) hser) * h + hs
  have hT4c : PowerSeries.constantCoeff T4 = 1 := constantCoeff_subst_of_one hQ0 _ constantCoeff_th4
  have hYc : PowerSeries.constantCoeff Y = 1 := by
    rw [hY, one_sub_gAt_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, ySer, PowerSeries.coeff_mk]
    simp [aSer_zero, halfBinom, gbinom]
  have h0 : (Y * T4 ^ 2 - 1) * (Y * T4 ^ 2 + 1) = 0 := by linear_combination hsq
  have hc : PowerSeries.constantCoeff (T4 ^ 2) ≠ 0 := by
    rw [map_pow, hT4c]
    norm_num
  refine (PowerSeries.eq_inv_iff_mul_eq_one hc).2 ?_
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have := congrArg PowerSeries.constantCoeff h1
    rw [map_add, map_mul, map_pow, hYc, hT4c, map_one, map_zero] at this
    norm_num at this

end Virasoro.Sphere
