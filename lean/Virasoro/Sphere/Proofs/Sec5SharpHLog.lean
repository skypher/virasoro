import Virasoro.Sphere.Proofs.Sec5SharpHSym
import Virasoro.Sphere.Proofs.Sec5SharpHRep

/-!
# Theorem 5.5, step (3) over `ℂ`: `H_M` on the affine line (sphere/paper.tex l.1722–1757)

At `(Δ₁,Δ₂) = (μ,0)` every `γ_Z(μ;μ,0)`, `Z ≠ ∅`, vanishes (the last factor is `μ+0+0-μ`), so
`ℬ_m = δ_{m0}` for `m ≤ M` and `H_M = [q^M] Φ̃(c,μ,Δ_i)⁻¹/16^M` (l.1722–1732).  Over `ℂ`,
`Φ̃⁻¹ = exp(S)` with `S = -(a₁ log(16q/z) + a₂ log(1-z) + a₃ log θ₃)` (`f^a = exp(a log f)`).
On the line `Δ₃ = wt((w+X)/2)`, `Δ₄ = wt((w-X)/2)` the exponent is `s₀ + w s₁ + w² s₂` with
`s₁ = X/(8pp') log(1-z)` and `s₂ = (log(1-z) + 8 log θ₃)/(16pp')`.  From
`z = 16q - 128q² + …` and `θ₃ = 1 + 2q + 0q² + …`: `log(1-z) = -16q + 0q² + …`,
`log θ₃ = 2q - 2q² + …`, so `s₂ = O(q²)`, `[q]s₁ = -2X/(pp')`, `[q²]s₂ = -1/(pp')`
(the paper's `exp(-2αvq - v²q² + …)`, l.1735–1747, with `w = √(pp') v`).
-/

namespace Virasoro.Sphere

open PowerSeries

/-! ### Low coefficients -/

theorem c1_mulPS (f g : PowerSeries ℂ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton]

theorem coeff_zero_one' {f : PowerSeries ℂ} (hf : constantCoeff f = 1) : coeff 0 f = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, hf]

theorem c1_powPS {f : PowerSeries ℂ} (hf : constantCoeff f = 1) (n : ℕ) :
    coeff 1 (f ^ n) = n * coeff 1 f := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, c1_mulPS, ih, coeff_zero_eq_constantCoeff_apply, map_pow, hf, one_pow,
      coeff_zero_one' hf]
    push_cast
    ring

theorem coeff_one_inv' {f : PowerSeries ℂ} (hf : constantCoeff f = 1) :
    coeff 1 f⁻¹ = -coeff 1 f := by
  have h : f⁻¹ * f = 1 := PowerSeries.inv_mul_cancel _ (by rw [hf]; exact one_ne_zero)
  have h1 := congrArg (coeff 1) h
  rw [c1_mulPS, PowerSeries.coeff_one, if_neg one_ne_zero, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_inv, hf, inv_one, coeff_zero_one' hf] at h1
  linear_combination h1

theorem coeff_th3_one : coeff 1 (th3 ℂ) = 2 := by
  simp [th3, theta3Z, coeff_map, coeff_mk, Nat.sqrt_one]

theorem sqrt_two' : Nat.sqrt 2 = 1 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm

theorem coeff_th3_two : coeff 2 (th3 ℂ) = 0 := by
  simp [th3, theta3Z, coeff_map, coeff_mk, sqrt_two']

theorem coeff_thPsi_one : coeff 1 (thPsi ℂ) = 0 := by
  simp [thPsi, thetaPsiZ, coeff_map, coeff_mk, Nat.sqrt_one]

theorem coeff_zq_one' : coeff 1 (zq ℂ) = 16 ∧ coeff 2 (zq ℂ) = -128 := by
  have hz : zq ℂ = X * (C (16 : ℂ) * (thPsi ℂ ^ 4 * (th3 ℂ ^ 4)⁻¹)) := by
    rw [zq, map_ofNat]
    ring
  have hψ : constantCoeff (thPsi ℂ ^ 4) = 1 := by rw [map_pow, constantCoeff_thPsi, one_pow]
  have hθ : constantCoeff (th3 ℂ ^ 4) = 1 := by rw [map_pow, constantCoeff_th3, one_pow]
  have hθi : constantCoeff (th3 ℂ ^ 4)⁻¹ = 1 := by rw [constantCoeff_inv, hθ, inv_one]
  refine ⟨?_, ?_⟩
  · rw [hz, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_C_mul, coeff_zero_eq_constantCoeff_apply,
      map_mul, hψ, hθi]
    norm_num
  · rw [hz, show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, coeff_C_mul, c1_mulPS,
      coeff_one_inv' hθ, c1_powPS (constantCoeff_th3 (A := ℂ)), coeff_th3_one,
      c1_powPS (constantCoeff_thPsi (A := ℂ)), coeff_thPsi_one, coeff_zero_one' hψ,
      coeff_zero_one' hθi]
    norm_num

/-! ### Coefficients of `log f` -/

/-- `log f = log(1 + (f-1))`. -/
noncomputable abbrev logS (f : PowerSeries ℂ) : PowerSeries ℂ := (log ℂ).subst (f - 1)

theorem logS_coeffs {f : PowerSeries ℂ} (hf : constantCoeff f = 1) :
    constantCoeff (logS f) = 0 ∧ coeff 1 (logS f) = coeff 1 f ∧
      coeff 2 (logS f) = coeff 2 f - coeff 1 f ^ 2 / 2 := by
  have h1 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hs1 := HasSubst.of_constantCoeff_zero' h1
  have hL : constantCoeff (logS f) = 0 := constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  have e := deriv_log_subst_mul (τ := Unit) (f - 1) h1
  rw [add_sub_cancel] at e
  have hd : derivative ℂ (logS f) = (derivative ℂ (log ℂ)).subst (f - 1) * derivative ℂ f := by
    rw [logS, derivative_subst hs1, map_sub, Derivation.map_one_eq_zero, sub_zero]
  have key : derivative ℂ (logS f) * f = derivative ℂ f := by
    rw [hd, mul_comm _ (derivative ℂ f), mul_assoc, e, mul_one]
  have k0 := congrArg (coeff 0) key
  have k1 := congrArg (coeff 1) key
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
    ← coeff_zero_eq_constantCoeff_apply, coeff_derivative, coeff_derivative, coeff_zero_one' hf]
    at k0
  rw [c1_mulPS, coeff_derivative, coeff_derivative, coeff_derivative, coeff_zero_one' hf]
    at k1
  refine ⟨hL, ?_, ?_⟩
  · simp only [Nat.cast_zero, zero_add, mul_one] at k0
    exact k0
  · simp only [Nat.cast_zero, zero_add, mul_one, Nat.cast_one] at k0 k1
    rw [k0] at k1
    linear_combination k1 / 2

theorem logS_one_sub_zq :
    constantCoeff (logS (1 - zq ℂ)) = 0 ∧ coeff 1 (logS (1 - zq ℂ)) = -16 ∧
      coeff 2 (logS (1 - zq ℂ)) = 0 := by
  have hf : constantCoeff (1 - zq ℂ) = 1 := by rw [map_sub, map_one, constantCoeff_zq, sub_zero]
  obtain ⟨h0, h1, h2⟩ := logS_coeffs hf
  obtain ⟨z1, z2⟩ := coeff_zq_one'
  rw [map_sub, PowerSeries.coeff_one, if_neg one_ne_zero, z1] at h1
  rw [map_sub, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_one,
    if_neg (by norm_num : (2 : ℕ) ≠ 0), if_neg one_ne_zero, z1, z2] at h2
  refine ⟨h0, by rw [h1]; norm_num, by rw [h2]; norm_num⟩

theorem logS_th3 :
    constantCoeff (logS (th3 ℂ)) = 0 ∧ coeff 1 (logS (th3 ℂ)) = 2 ∧
      coeff 2 (logS (th3 ℂ)) = -2 := by
  obtain ⟨h0, h1, h2⟩ := logS_coeffs (constantCoeff_th3 (A := ℂ))
  rw [coeff_th3_one] at h1
  rw [coeff_th3_one, coeff_th3_two] at h2
  refine ⟨h0, h1, by rw [h2]; norm_num⟩

/-! ### `Φ̃⁻¹ = exp(S)` over `ℂ` -/

/-- The exponent `S = -(a₁ log(16q/z) + a₂ log(1-z) + a₃ log θ₃)` of `Φ̃(c,a,Δ_i)⁻¹`. -/
noncomputable def Sexp (c a : ℂ) (Δe : Fin 4 → ℂ) : PowerSeries ℂ :=
  -((a - (c - 1) / 24) • logS (nomeRatio ℂ) +
    ((c - 1) / 24 - Δe 1 - Δe 2) • logS (1 - zq ℂ) +
    ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3)) • logS (th3 ℂ))

theorem constantCoeff_smul_logS {f : PowerSeries ℂ} (hf : constantCoeff f = 1) (a : ℂ) :
    constantCoeff (a • logS f) = 0 := by
  rw [smul_eq_C_mul, map_mul, (logS_coeffs hf).1, mul_zero]

theorem PhiAt_inv_exp (c a : ℂ) (Δe : Fin 4 → ℂ) :
    (PhiAt c a Δe)⁻¹ = (exp ℂ).subst (Sexp c a Δe) := by
  have f1 : constantCoeff (nomeRatio ℂ) = 1 := constantCoeff_nomeRatio
  have f2 : constantCoeff (1 - zq ℂ) = 1 := by rw [map_sub, map_one, constantCoeff_zq, sub_zero]
  have f3 : constantCoeff (th3 ℂ) = 1 := constantCoeff_th3
  set x₁ := (a - (c - 1) / 24) • logS (nomeRatio ℂ) with hx₁
  set x₂ := ((c - 1) / 24 - Δe 1 - Δe 2) • logS (1 - zq ℂ) with hx₂
  set x₃ := ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3)) • logS (th3 ℂ) with hx₃
  have c₁ : constantCoeff x₁ = 0 := constantCoeff_smul_logS f1 _
  have c₂ : constantCoeff x₂ = 0 := constantCoeff_smul_logS f2 _
  have c₃ : constantCoeff x₃ = 0 := constantCoeff_smul_logS f3 _
  have hPhi : PhiAt c a Δe = (exp ℂ).subst (x₁ + x₂ + x₃) := by
    rw [PhiAt, hx₁, hx₂, hx₃, exp_subst_add _ _ (by rw [map_add, c₁, c₂, add_zero]) c₃,
      exp_subst_add _ _ c₁ c₂, exp_smul_log _ f1, exp_smul_log _ f2, exp_smul_log _ f3]
  have hs : constantCoeff (x₁ + x₂ + x₃) = 0 := by rw [map_add, map_add, c₁, c₂, c₃]; ring
  have hns : constantCoeff (-(x₁ + x₂ + x₃)) = 0 := by rw [map_neg, hs, neg_zero]
  have hS : Sexp c a Δe = -(x₁ + x₂ + x₃) := rfl
  rw [hS]
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [hPhi]; exact (constantCoeff_exp_subst _ hs) ▸ one_ne_zero),
    hPhi, ← exp_subst_add _ _ hns hs, neg_add_cancel, exp_subst_zero]

/-! ### The collapse at `(Δ₁,Δ₂) = (μ,0)` -/

theorem gammaY_self_zero (Δ : ℂ) : ∀ w : List ℕ, w ≠ [] → gammaY Δ Δ 0 w = 0
  | [], h => absurd rfl h
  | [y], _ => by simp [gammaY]
  | y :: z :: w, _ => by
    rw [gammaY, gammaY_self_zero Δ (z :: w) (List.cons_ne_nil _ _), mul_zero]

theorem evalAt_Bsph_collapse {c μ : ℂ} {v : Fin 4 → ℂ} (h0 : v 0 = μ) (h1 : v 1 = 0) {m : ℕ}
    (hm : 1 ≤ m) (hdet : (gram c μ m).det ≠ 0) : evalAt μ (Bsph c v m) = 0 := by
  rw [evalAt_Bsph v hdet]
  refine Finset.sum_eq_zero fun Y _ => Finset.sum_eq_zero fun Z _ => ?_
  have hZ : Z.word ≠ [] := by
    intro h
    have := Verma.word_sum' Z
    rw [h, List.sum_nil] at this
    omega
  rw [h0, h1, gammaY_self_zero μ _ hZ, mul_zero]

theorem compS_delta (u : PowerSeries ℂ) : compS (fun m => if m = 0 then (1 : ℂ) else 0) u = 1 := by
  ext n
  rw [compS, coeff_mk, Finset.sum_eq_single 0 (fun k _ hk => by rw [if_neg hk, zero_mul])
    (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos n)) h), if_pos rfl, one_mul, pow_zero]

/-- `H_M(c,μ,μ,0,Δ₃,Δ₄) = [q^M] exp(S)/16^M` (l.1722–1732). -/
theorem evalAt_Hsph_collapse {c μ : ℂ} {v : Fin 4 → ℂ} (h0 : v 0 = μ) (h1 : v 1 = 0) {M : ℕ}
    (hdet : ∀ m ≤ M, (gram c μ m).det ≠ 0) :
    evalAt μ (Hsph c v M) = coeff M ((exp ℂ).subst (Sexp c μ v)) / 16 ^ M := by
  rw [evalAt_Hsph c μ v M fun m hm => regAt_Bsph v (hdet m hm)]
  congr 1
  rw [coeff_mul_compS_congr (b' := fun m => if m = 0 then (1 : ℂ) else 0) _ _ fun m hm => ?_,
    compS_delta, mul_one, PhiAt_inv_exp]
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · rw [if_pos rfl, Bsph_zero, ← map_one (RatFunc.C : ℂ →+* RatFunc ℂ), evalAt_C]
  · rw [if_neg hm1.ne', evalAt_Bsph_collapse h0 h1 hm1 (hdet m hm)]

/-! ### The exponent on the affine line -/

/-- The point `(μ, 0, wt((w+X)/2), wt((w-X)/2))` of the line of l.1711–1714. -/
noncomputable def ptW (p p' : ℕ) (μ Xc w : ℂ) : Fin 4 → ℂ :=
  ![μ, 0, momC p p' ((w + Xc) / 2), momC p p' ((w - Xc) / 2)]

/-- `s₀`: the part of the exponent independent of `w`. -/
noncomputable def sW0 (p p' : ℕ) (c μ Xc : ℂ) : PowerSeries ℂ :=
  -((μ - (c - 1) / 24) • logS (nomeRatio ℂ) +
    ((c - 1) / 24 - (Xc ^ 2 / 4 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')) • logS (1 - zq ℂ) +
    ((c - 1) / 2 - 4 * (μ + 2 * ((Xc ^ 2 / 4 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')))) •
      logS (th3 ℂ))

/-- `s₁ = X/(8pp') log(1-z)`. -/
noncomputable def sW1 (p p' : ℕ) (Xc : ℂ) : PowerSeries ℂ :=
  (Xc / (8 * p * p')) • logS (1 - zq ℂ)

/-- `s₂ = (log(1-z) + 8 log θ₃)/(16pp')`. -/
noncomputable def sW2 (p p' : ℕ) : PowerSeries ℂ :=
  (1 / (16 * (p : ℂ) * p')) • (logS (1 - zq ℂ) + (8 : ℂ) • logS (th3 ℂ))

theorem Sexp_ptW (p p' : ℕ) (hp : 0 < p) (hp' : 0 < p') (c μ Xc w : ℂ) :
    Sexp c μ (ptW p p' μ Xc w) = sW0 p p' c μ Xc + w • sW1 p p' Xc + w ^ 2 • sW2 p p' := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  ext n
  simp [Sexp, sW0, sW1, sW2, ptW, momC, coeff_smul]
  field_simp
  ring

theorem sOne_sTwo_coeffs (p p' : ℕ) (Xc : ℂ) :
    coeff 0 (sW1 p p' Xc) = 0 ∧ coeff 0 (sW2 p p') = 0 ∧ coeff 1 (sW2 p p') = 0 ∧
      coeff 1 (sW1 p p' Xc) = -(2 * Xc / (p * p')) ∧ coeff 2 (sW2 p p') = -(1 / (p * p')) := by
  obtain ⟨a0, a1, a2⟩ := logS_one_sub_zq
  obtain ⟨b0, b1, b2⟩ := logS_th3
  have a0' : coeff 0 (logS (1 - zq ℂ)) = 0 := by rw [coeff_zero_eq_constantCoeff_apply, a0]
  have b0' : coeff 0 (logS (th3 ℂ)) = 0 := by rw [coeff_zero_eq_constantCoeff_apply, b0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [sW1, coeff_smul, a0, a0']
  · simp [sW2, coeff_smul, a0, b0, a0', b0']
  · simp [sW2, coeff_smul, a1, b1]
    norm_num
  · simp [sW1, coeff_smul, a1]
    ring
  · simp [sW2, coeff_smul, a2, b2]
    ring

theorem coeff_zero_sZero (p p' : ℕ) (c μ Xc : ℂ) : coeff 0 (sW0 p p' c μ Xc) = 0 := by
  have f1 : constantCoeff (nomeRatio ℂ) = 1 := constantCoeff_nomeRatio
  have n0 := (logS_coeffs f1).1
  obtain ⟨a0, -, -⟩ := logS_one_sub_zq
  obtain ⟨b0, -, -⟩ := logS_th3
  simp [sW0, coeff_smul, a0, b0, n0]

end Virasoro.Sphere
