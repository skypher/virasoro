import Virasoro.Sphere.Proofs.Sec3C2Step2Subs

/-!
# Lemma 3.7, Step 2: the rescaling `v_m = iλW_m` (sphere paper)

sphere/paper.tex l.1074–1076: rescaling `v_m = iλW_m` gives
`l_k^{(1)} = D_k + (1/4λ²) ∑_{r=1}^{k-1} ∂_{W_r}∂_{W_{k-r}}`, where
`D_k = ∂_{W_k} + ∑_{m≥1} m W_m ∂_{W_{m+k}}`.
-/

namespace Virasoro.Sphere

open MvPolynomial Finset TensorProduct

/-- `∑_{r=1}^{k-1} ∂_{W_r}∂_{W_{k-r}}`. -/
noncomputable def lapSum (k : ℕ) : Fock →ₗ[ℂ] Fock :=
  ∑ r ∈ Icc 1 (k - 1), dVar r ∘ₗ dVar (k - r)

theorem lapSum_apply (k : ℕ) (f : Fock) :
    lapSum k f = ∑ r ∈ Icc 1 (k - 1), dVar r (dVar (k - r) f) := by
  simp only [lapSum, LinearMap.sum_apply, LinearMap.comp_apply]

theorem Dop_monomial (k : ℕ) (α : ℕ+ →₀ ℕ) : Dop k (monomial α 1) = DopMono k α := by
  have h := (basisMonomials ℕ+ ℂ).constr_basis ℂ (DopMono k) α
  rwa [coe_basisMonomials] at h

theorem rescW_monomial (lam : ℂ) (α : ℕ+ →₀ ℕ) (a : ℂ) :
    rescW lam (monomial α a) = monomial α (a * (Complex.I * lam) ^ α.degree) := by
  unfold rescW
  generalize Complex.I * lam = c
  rw [aeval_monomial, Finsupp.prod]
  simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
    ← Finsupp.degree_apply, algebraMap_eq]
  rw [monomial_eq (s := α), map_mul, Finsupp.prod]
  ring

theorem coeff_rescW (lam : ℂ) (f : Fock) (γ : ℕ+ →₀ ℕ) :
    coeff γ (rescW lam f) = (Complex.I * lam) ^ γ.degree * coeff γ f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial α a =>
    rw [rescW_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · ring
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq]
    ring

theorem pderiv_rescW (lam : ℂ) (i : ℕ+) (f : Fock) :
    pderiv i (rescW lam f) = C (Complex.I * lam) * rescW lam (pderiv i f) := by
  ext γ
  rw [coeff_pderiv, coeff_rescW, coeff_C_mul, coeff_rescW, coeff_pderiv, map_add,
    Finsupp.degree_single]
  ring

theorem dVar_rescW (lam : ℂ) (j : ℕ) (f : Fock) :
    dVar j (rescW lam f) = (Complex.I * lam) • rescW lam (dVar j f) := by
  show pderiv j.toPNat' (rescW lam f) = _
  rw [pderiv_rescW, C_mul']
  rfl

theorem rescW_uVar (lam : ℂ) (n : ℕ) :
    rescW lam (uVar n) = (Complex.I * lam) • (uVar n : Fock) := by
  rw [uVar, rescW, aeval_X, C_mul']

set_option maxHeartbeats 800000 in
/-- `l_k^{(1)} = D_k + (1/4λ²) ∑_{r=1}^{k-1} ∂_{W_r}∂_{W_{k-r}}` in the variables `W = v/(iλ)`
(sphere/paper.tex l.1074–1076). -/
theorem rescW_ffOp (lam : ℂ) (hlam : lam ≠ 0) (k : ℕ) (hk : 1 ≤ k) (f : Fock) :
    rescW lam (ffOp 0 lam (k : ℤ) f) =
      Dop k (rescW lam f) + (1 / (4 * lam ^ 2)) • lapSum k (rescW lam f) := by
  have hc : Complex.I * lam ≠ 0 := mul_ne_zero Complex.I_ne_zero hlam
  have key : (rescW lam).toLinearMap ∘ₗ ffOp 0 lam (k : ℤ) =
      (Dop k + (1 / (4 * lam ^ 2)) • lapSum k) ∘ₗ (rescW lam).toLinearMap := by
    apply (basisMonomials ℕ+ ℂ).ext
    intro α
    rw [coe_basisMonomials]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.add_apply,
      LinearMap.smul_apply]
    have hr : rescW lam (monomial α 1) = (Complex.I * lam) ^ α.degree • monomial α (1 : ℂ) := by
      rw [rescW_monomial, one_mul, smul_monomial, smul_eq_mul, mul_one]
    have hd1 : ∀ (j : ℕ) (g : Fock),
        rescW lam g = (Complex.I * lam) ^ α.degree • g →
        rescW lam (dVar j g) =
          ((Complex.I * lam)⁻¹ * (Complex.I * lam) ^ α.degree) • dVar j g := by
      intro j g hg
      have h1 : (Complex.I * lam) • rescW lam (dVar j g) =
          (Complex.I * lam) ^ α.degree • dVar j g := by
        rw [← dVar_rescW, hg, map_smul]
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hd2 : ∀ i j : ℕ, rescW lam (dVar i (dVar j (monomial α (1 : ℂ)))) =
        (((Complex.I * lam) * (Complex.I * lam))⁻¹ * (Complex.I * lam) ^ α.degree) •
          dVar i (dVar j (monomial α (1 : ℂ))) := by
      intro i j
      have h1 : ((Complex.I * lam) * (Complex.I * lam)) •
          rescW lam (dVar i (dVar j (monomial α (1 : ℂ)))) =
          (Complex.I * lam) ^ α.degree • dVar i (dVar j (monomial α (1 : ℂ))) := by
        rw [mul_smul, ← dVar_rescW, ← map_smul, ← dVar_rescW, hr, map_smul, map_smul]
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
    have hA : ∀ n : ℕ, rescW lam (uVar n * dVar (n + k) (monomial α (1 : ℂ))) =
        (Complex.I * lam) ^ α.degree • (uVar n * dVar (n + k) (monomial α (1 : ℂ))) := by
      intro n
      rw [map_mul, rescW_uVar, hd1 _ _ hr, smul_mul_smul_comm, ← mul_assoc,
        mul_inv_cancel₀ hc, one_mul]
    have hC : rescW lam (C (0 * (k : ℂ) + Complex.I * lam) * dVar k (monomial α (1 : ℂ))) =
        (Complex.I * lam) ^ α.degree • dVar k (monomial α (1 : ℂ)) := by
      rw [C_mul', map_smul, hd1 _ _ hr, smul_smul, zero_mul, zero_add, ← mul_assoc,
        mul_inv_cancel₀ hc, one_mul]
    have hcc : (Complex.I * lam) * (Complex.I * lam) = -lam ^ 2 := by
      linear_combination lam ^ 2 * Complex.I_mul_I
    have e2 : (1 / 4 : ℂ) * (((Complex.I * lam) * (Complex.I * lam))⁻¹ *
        (Complex.I * lam) ^ α.degree) = -(1 / (4 * lam ^ 2)) * (Complex.I * lam) ^ α.degree := by
      rw [hcc]
      field_simp
    have hk0 : ¬ ((k : ℤ) = 0) := by omega
    have hkp : (0 : ℤ) < k := by omega
    rw [ffOp_monomial, hr, map_smul, map_smul, Dop_monomial, lapSum_apply]
    simp only [ffOpMono, DopMono, if_neg hk0, if_pos hkp, Int.toNat_natCast,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [map_add, map_sub, map_smul, map_sum, map_sum, hC,
      Finset.sum_congr rfl fun n _ => by rw [map_smul, hA n, smul_comm],
      Finset.sum_congr (s₁ := Icc 1 (k - 1)) rfl fun n _ => hd2 n (k - n), ← Finset.smul_sum,
      ← Finset.smul_sum, smul_smul, e2]
    module
  exact LinearMap.congr_fun key f

/-- The operator `D_k + s ∑_{r<k} ∂_{W_r}∂_{W_{k-r}} + l_k^{(2)}` on polynomials in `(W, u)`
(the primary condition `L_k^tot P = 0` in the variables `W`, with `s = 1/(4λ²)`). -/
noncomputable def Tk (s : ℂ) (k : ℕ) : HH →ₗ[ℂ] HH :=
  TensorProduct.map (Dop k + s • lapSum k) LinearMap.id +
    TensorProduct.map LinearMap.id (ffOp (0 : ℂ) 0 (k : ℤ))

theorem rescH_tmul (lam : ℂ) (a b : Fock) : rescH lam (a ⊗ₜ[ℂ] b) = rescW lam a ⊗ₜ[ℂ] b := by
  simp only [rescH, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]

theorem rescH_Ltot (lam : ℂ) (hlam : lam ≠ 0) (k : ℕ) (hk : 1 ≤ k) (x : HH) :
    rescH lam (Ltot lam (k : ℤ) x) = Tk (1 / (4 * lam ^ 2)) k (rescH lam x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a b =>
    rw [Ltot_tmul, map_add, rescH_tmul, rescH_tmul, rescH_tmul, rescW_ffOp lam hlam k hk]
    simp only [Tk, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.smul_apply]

end Virasoro.Sphere
