import Virasoro.Sphere.Proofs.Sec3GaussStepThree
import Virasoro.Sphere.Proofs.Sec3CovStable
import Virasoro.Sphere.Proofs.Sec3CovEval

/-!
# Lemma 3.3(iii): the value at `λ = ∞` (sphere paper)

sphere/paper.tex l.703–708.  "Evaluating the finite centered Gaussian expectation of the
linear-in-`(U,V)` exponential yields `exp(μ²Ψ₁(z))` (half the covariance contraction of the
gradient of `S̃⁽¹⁾`).  Using `ι`-evenness of `S⁽²⁾` to identify `S̃⁽²⁾(σ̄_*)` and setting
`Φ_c^raw := 2S_c⁽²⁾(σ_*) + Ψ₁`, `Φ_j := S_j⁽²⁾(σ_*)` yields (3.5) modulo `z^{N+1}`."
This proves `Stmt_sub_gauss_cov`, hence `Stmt_sub_lam_gauss`.
-/

namespace Virasoro.Sphere

open MvPowerSeries

local notation "KK" => RatFunc ℂ

section Psi

/-- The gradient of `S̃⁽¹⁾(σ) + S̃⁽¹⁾_conj(σ̄)` at the saddle point, in the variables `(U, V)`. -/
noncomputable def gradG (S1t : MvPowerSeries ℕ+ ℂ) (n : ℕ) : Modes n → PowerSeries ℂ :=
  Sum.elim (fun i => subst sigmaStar (pd ((i : ℕ) + 1) S1t))
    (fun i => subst (fun m => -sigmaStar m) (pd ((i : ℕ) + 1) (conjSeries S1t)))

theorem gradG_embM (S1t : MvPowerSeries ℕ+ ℂ) {k n : ℕ} (h : k ≤ n) (a : Modes k) :
    gradG S1t n (embM h a) = gradG S1t k a := by
  rcases a with i | i <;> rfl

theorem quad_sum_lemma {R : Type*} [CommRing R] {k : ℕ} (A B Ct D A' B' D' : Fin k → Fin k → R)
    (hA : ∀ i j, A i j = A' i j) (hB : ∀ i j, B i j = B' i j) (hC : ∀ i j, Ct i j = B' j i)
    (hD : ∀ i j, D i j = D' i j) :
    ∑ i, (∑ j, A i j + ∑ j, B i j) + ∑ i, (∑ j, Ct i j + ∑ j, D i j) =
      ∑ i, ∑ j, (A' i j + 2 * B' i j + D' i j) := by
  simp only [hA, hB, hC, hD, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => B' j i)]
  ring

/-- Half the covariance contraction of the gradient of `S̃⁽¹⁾` is `Ψ₁` modulo `z^{n+1}`
(sphere/paper.tex l.703–706), with the stabilization in the number of modes of l.669–675. -/
theorem psi1_eq (S1t : MvPowerSeries ℕ+ ℂ) (n : ℕ) :
    (1 / 2 : ℚ) • ∑ a, ∑ b, mkT n ℂ (gradG S1t n a) * covN n (phiA n ℂ) n a b *
        mkT n ℂ (gradG S1t n b) =
      mkT n ℂ (Psi1 S1t sigmaStar (fun m => -sigmaStar m)) := by
  have hcov : ∀ (k : ℕ) (a b : Modes n),
      mkT k ℂ (covN n phiP n a b) = covN n (phiA k ℂ) n a b :=
    fun k a b => map_covN (mkT k ℂ) phiP n n a b
  have hmap : ∀ k : ℕ, mkT k ℂ (∑ a, ∑ b, gradG S1t n a * covN n phiP n a b * gradG S1t n b) =
      ∑ a, ∑ b, mkT k ℂ (gradG S1t n a) * covN n (phiA k ℂ) n a b * mkT k ℂ (gradG S1t n b) := by
    intro k
    simp only [map_sum, map_mul, hcov]
  have hhalf : (algebraMap ℚ ℂ) (1 / 2) = 1 / 2 := by
    rw [eq_ratCast]
    push_cast
    rfl
  have hL : (1 / 2 : ℚ) • ∑ a, ∑ b, mkT n ℂ (gradG S1t n a) * covN n (phiA n ℂ) n a b *
        mkT n ℂ (gradG S1t n b) =
      mkT n ℂ (PowerSeries.C (1 / 2 : ℂ) *
        ∑ a, ∑ b, gradG S1t n a * covN n phiP n a b * gradG S1t n b) := by
    rw [Algebra.smul_def, algebraMap_TR, hhalf, map_mul, hmap]
  rw [hL]
  refine ext_cf fun k hk => ?_
  rw [cf_mkT hk, cf_mkT hk, Psi1, PowerSeries.coeff_mk]
  refine (mkT_eq_iff _ _).1 ?_ k le_rfl
  rw [map_mul, map_mul, hmap,
    covN_stable hk hk (phiA_X_pow k ℂ) (fun a => mkT k ℂ (gradG S1t n a))]
  congr 1
  simp only [map_sum, map_add, map_mul, map_ofNat, Fintype.sum_sum_type]
  refine quad_sum_lemma _ _ _ _ _ _ _ (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
    (fun i j => ?_)
  · rw [covN_inl_inl, gradG_embM, gradG_embM]
    simp only [gradG, Sum.elim_inl]
    ring
  · rw [covN_inl_inr, gradG_embM, gradG_embM]
    simp only [gradG, Sum.elim_inl, Sum.elim_inr]
    ring
  · rw [covN_inr_inl, gradG_embM, gradG_embM]
    simp only [gradG, Sum.elim_inl, Sum.elim_inr]
    ring
  · rw [covN_inr_inr, gradG_embM, gradG_embM]
    simp only [gradG, Sum.elim_inr]
    ring

theorem constantCoeff_Psi1 (S1t : MvPowerSeries ℕ+ ℂ) (σ σb : ℕ+ → PowerSeries ℂ) :
    PowerSeries.constantCoeff (Psi1 S1t σ σb) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Psi1, PowerSeries.coeff_mk]
  simp

end Psi

section Even

/-- `S̃(σ̄_*) = ι(S)(σ_*)`: conjugating the coefficients and evaluating at `σ̄_* = -σ_*`. -/
theorem subst_neg_conjSeries (T : MvPowerSeries ℕ+ ℂ) :
    subst (fun m => -sigmaStar m) (conjSeries T) = subst sigmaStar (iota T) := by
  have h : iota T = rescale (fun _ => (-1 : ℂ)) (conjSeries T) := by
    ext α
    rw [coeff_iota, coeff_rescale, prod_const_pow]
    rfl
  rw [h, subst_rescale hasSubst_sigmaStar]
  congr 1
  funext m
  rw [map_neg, map_one, neg_one_mul]

theorem conjSeries_real_smul (μ : ℝ) (T : MvPowerSeries ℕ+ ℂ) :
    conjSeries ((μ : ℂ) • T) = (μ : ℂ) • conjSeries T := by
  ext α
  rw [conjSeries, coeff_map, coeff_smul, coeff_smul, map_mul, Complex.conj_ofReal]
  rfl

theorem isNilpotent_mkT_constantCoeff {n : ℕ} {f : PowerSeries ℂ}
    (h : IsNilpotent (mkT n ℂ f)) : PowerSeries.constantCoeff f = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [← map_pow, mkT_eq_zero_iff] at hk
  have h0 := hk 0 (Nat.zero_le _)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] at h0
  by_cases hk0 : k = 0
  · subst hk0
    simp at h0
  · exact (pow_eq_zero_iff hk0).1 h0

end Even

section Final

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- Lemma 3.3(iii), last step (sphere/paper.tex l.703–708). -/
theorem sub_gauss_cov : Stmt_sub_gauss_cov := by
  intro S1t S2c S21 S22 hE μ hμ Δe n
  have hW := wardRat_isWard hF hK μ hμ (Δe 0 : ℂ) (Δe 1 : ℂ)
  have hW' := wardRat_isWard hF hK μ hμ (Δe 3 : ℂ) (Δe 2 : ℂ)
  obtain ⟨h1, h2⟩ := hE μ hμ (Δe 0) (Δe 1) _ hW
  obtain ⟨h1', h2'⟩ := hE μ hμ (Δe 3) (Δe 2) _ hW'
  have heven := iota_Sord_two hF hK hW'
  set F := wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) with hFdef
  set F' := wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ) with hF'def
  have hs := hasSubst_sigmaStar
  -- the constant: `S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*)`
  have hC : constC (n := n) F F' = mkT n ℂ
      (((μ : ℂ) ^ 2 • subst sigmaStar S2c + ((Δe 1 : ℂ) - 1 / 16) • subst sigmaStar S22 +
          ((Δe 0 : ℂ) - 1 / 16) • subst sigmaStar S21) +
        ((μ : ℂ) ^ 2 • subst sigmaStar S2c + ((Δe 2 : ℂ) - 1 / 16) • subst sigmaStar S22 +
          ((Δe 3 : ℂ) - 1 / 16) • subst sigmaStar S21)) := by
    rw [constC_eq, subst_neg_conjSeries, heven, h2, h2', ← map_add]
    simp only [subst_add hs, subst_smul hs]
  -- the gradient
  have hL : ∀ a, gradL (n := n) F F' a =
      mkT n ℂ (PowerSeries.C (μ : ℂ)) * mkT n ℂ (gradG S1t n a) := by
    intro a
    rcases a with i | i
    · rw [gradL_inl, h1, pd, Derivation.map_smul, subst_smul hs, ← map_mul,
        ← PowerSeries.smul_eq_C_mul]
      rfl
    · rw [gradL_inr, h1', conjSeries_real_smul, pd, Derivation.map_smul,
        subst_smul hasSubst_sigmaStar_neg, ← map_mul, ← PowerSeries.smul_eq_C_mul]
      rfl
  have hQ : (1 / 2 : ℚ) • ∑ a, ∑ b, gradL (n := n) F F' a * covN n (phiA n ℂ) n a b *
        gradL (n := n) F F' b =
      mkT n ℂ ((μ : ℂ) ^ 2 • Psi1 S1t sigmaStar (fun m => -sigmaStar m)) := by
    have e : ∑ a, ∑ b, gradL (n := n) F F' a * covN n (phiA n ℂ) n a b *
          gradL (n := n) F F' b =
        mkT n ℂ (PowerSeries.C (μ : ℂ)) ^ 2 * ∑ a, ∑ b, mkT n ℂ (gradG S1t n a) *
          covN n (phiA n ℂ) n a b * mkT n ℂ (gradG S1t n b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hL a, hL b]
      ring
    rw [e, ← mul_smul_comm, psi1_eq, ← map_pow, ← map_mul, ← map_pow,
      ← PowerSeries.smul_eq_C_mul]
  -- nilpotency
  obtain ⟨S1t', S2c', S21', S22', hE', hodd, -, -⟩ := sub_lam_orders hF hK
  have hodd' : iota (Sord F' 1) = -Sord F 1 := by
    rw [(hE' μ hμ (Δe 0) (Δe 1) _ hW).1, (hE' μ hμ (Δe 3) (Δe 2) _ hW').1, iota_smul, hodd,
      Complex.conj_ofReal, smul_neg]
  obtain ⟨EP, -, -, -, hcn⟩ := gauss_lift (n := n) hW hW' hodd'
  have hQn : IsNilpotent ((1 / 2 : ℚ) • ∑ a, ∑ b, gradL (n := n) F F' a *
      covN n (phiA n ℂ) n a b * gradL (n := n) F F' b) := by
    rw [hQ]
    refine isNilpotent_mkT _ ?_
    rw [PowerSeries.smul_eq_C_mul, map_mul, constantCoeff_Psi1, mul_zero]
  have hsum : constC (n := n) F F' + (1 / 2 : ℚ) • ∑ a, ∑ b, gradL (n := n) F F' a *
        covN n (phiA n ℂ) n a b * gradL (n := n) F F' b =
      mkT n ℂ ((μ : ℂ) ^ 2 • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
        ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S21 +
        ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst sigmaStar S22) := by
    rw [hC, hQ, ← map_add, PhiCraw, two_mul]
    congr 1
    module
  have hH0 := isNilpotent_mkT_constantCoeff
    (hsum ▸ Commute.isNilpotent_add (Commute.all _ _) hcn hQn)
  rw [← mul_assoc, ← IsNilpotent.exp_add_of_commute (Commute.all _ _) hcn hQn, hsum,
    ← mkT_exp_subst _ hH0, phiA, RingHom.comp_apply, ← map_mul, cf_mkT le_rfl, mul_comm]

include hF hK in
/-- Lemma 3.3(iii), the Gaussian evaluation in `λ⁻¹` (sphere/paper.tex l.637–711). -/
theorem sub_lam_gauss : Stmt_sub_lam_gauss :=
  sub_lam_gauss_of_cov hF hK (sub_gauss_cov hF hK)

end Final

end Virasoro.Sphere
