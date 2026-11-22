import Virasoro.Sphere.Proofs.Sec3C2GaussWard
import Virasoro.Sphere.Proofs.Sec3GaussSaddleI0
import Virasoro.Sphere.Proofs.Sec3CovStable
import Virasoro.Sphere.Proofs.Sec3GaussStepTwo

/-!
# Lemma 3.7, Step 1: the Fock pairings of the pure Gaussians (sphere paper)

sphere/paper.tex l.1035–1045: direct Gaussian evaluation (the Wick rule of the proof of
Lemma 3.3(iii) and the saddle value of Lemma 3.4(iii)) gives
`G_charged(λ;z) = ⟨F̃_1(v̄), F_1(z^• v)⟩ = det(I - M(z)²)^{-1/2} (16q(z)/z)^{λ²}` and
`G_neutral(z) = ⟨F̃_2(ū), F_2(z^• u)⟩ = det(I - M(z)²)^{-1/2}`, coefficient by coefficient in
`z`: the coefficient of `z^j` is the pairing (3.1) of the level-`j` parts.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset MvPowerSeries

local notation "LL" => ℂ⸨X⸩

/-! ### The exponent in the modes `≤ N` -/

theorem gaussExpo_eq_Sq (lam : ℂ) :
    gaussExpo lam = Sq (fun m => lam * Acoef m) (fun m n => (Bcoef m n : ℂ)) := by
  ext α
  show gaussExpo lam α = Sq (fun m => lam * Acoef m) (fun m n => (Bcoef m n : ℂ)) α
  unfold gaussExpo Sq S0
  split_ifs with h1 h2
  · rw [Finset.mul_sum]
  · rfl
  · rfl

theorem conj_gaussExpo (lam : ℝ) :
    MvPowerSeries.map (starRingEnd ℂ) (gaussExpo (lam : ℂ)) = gaussExpo (-(lam : ℂ)) := by
  ext α
  rw [MvPowerSeries.coeff_map]
  show (starRingEnd ℂ) (gaussExpo (lam : ℂ) α) = gaussExpo (-(lam : ℂ)) α
  have hc : (starRingEnd ℂ) (S0 α) = Sq (fun m => -Acoef m) (fun m n => (Bcoef m n : ℂ)) α := by
    have h := congrFun conj_S0_eq_Sq α
    rw [← h]
    rfl
  unfold gaussExpo
  by_cases h1 : α.degree = 1
  · rw [if_pos h1, if_pos h1, map_mul, Complex.conj_ofReal, hc]
    unfold Sq S0
    rw [if_pos h1, if_pos h1, Finset.sum_neg_distrib]
    ring
  · rw [if_neg h1, if_neg h1, hc]
    unfold Sq S0
    rw [if_neg h1, if_neg h1]

section Modes

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `E_λ(u) + E_{-λ}(ū)` in the modes `≤ N` is `q + J·x` with
`J = λ (A_1,…,A_N,-A_1,…,-A_N)`. -/
theorem subst_gaussExpo_eq (ψ : ℂ →+* R) (lam : ℂ) :
    subst (eS (S := R) Sum.inl) (map ψ (gaussExpo lam)) +
      subst (eS (S := R) Sum.inr) (map ψ (gaussExpo (-lam))) =
    quadB N R + linForm (Sum.elim (fun i : Fin N => ψ lam * ψ (Acoef ((i : ℕ) + 1)))
      (fun i : Fin N => -(ψ lam * ψ (Acoef ((i : ℕ) + 1))))) := by
  have hbN : ∀ (s : Fin N → Modes N) (m : ℕ+), N < (m : ℕ) → eS (S := R) s m = 0 :=
    fun s m h => eS_of_lt s m h
  have hq : ∀ q : ℚ, ψ ((q : ℂ)) = algebraMap ℚ R q := fun q =>
    RingHom.congr_fun (Subsingleton.elim (ψ.comp (algebraMap ℚ ℂ)) (algebraMap ℚ R)) q
  rw [gaussExpo_eq_Sq, gaussExpo_eq_Sq, subst_map_Sq (hasSubst_eS _) (hbN _),
    subst_map_Sq (hasSubst_eS _) (hbN _), quadB, linForm, Fintype.sum_sum_type]
  simp only [eS_modeEmb, Sum.elim_inl, Sum.elim_inr, hq, smul_eq_C_mul, map_neg, map_mul,
    mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The product of the two restricted Gaussians is `e^{q + J·x}`. -/
theorem gauss_prod_eq (ψ : ℂ →+* R) (lam : ℂ) :
    subst (eS (S := R) Sum.inl) (map ψ (mexp (gaussExpo lam))) *
      subst (eS (S := R) Sum.inr) (map ψ (mexp (gaussExpo (-lam)))) =
    mexp (quadB N R + linForm (Sum.elim (fun i : Fin N => ψ lam * ψ (Acoef ((i : ℕ) + 1)))
      (fun i : Fin N => -(ψ lam * ψ (Acoef ((i : ℕ) + 1)))))) := by
  have h0 : ∀ l : ℂ, IsNilpotent (constantCoeff (gaussExpo l)) := fun l => by
    rw [constantCoeff_gaussExpo]
    exact IsNilpotent.zero
  have h1' : ∀ l : ℂ, constantCoeff (map ψ (gaussExpo l)) = 0 := fun l => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_gaussExpo, map_zero]
  have h1 : ∀ l : ℂ, IsNilpotent (constantCoeff (map ψ (gaussExpo l))) := fun l => by
    rw [h1']
    exact IsNilpotent.zero
  have h2 : ∀ (s : Fin N → Modes N) (l : ℂ),
      IsNilpotent (constantCoeff (subst (eS (S := R) s) (map ψ (gaussExpo l)))) := fun s l => by
    rw [constantCoeff_subst_eS _ _ (h1' l)]
    exact IsNilpotent.zero
  rw [map_mexp ψ (h0 _), map_mexp ψ (h0 _), subst_mexp (h1 _) (hasSubst_eS _),
    subst_mexp (h1 _) (hasSubst_eS _), ← mexp_add (h2 _ _) (h2 _ _), subst_gaussExpo_eq]

end Modes

/-! ### The saddle value over `ℂ[[z]]/(z^{N+1})` -/

section Value

variable (N : ℕ)

/-- `ℂ[[z]]/(z^{N+1}) → ℂ((t))[[z]]/(z^{N+1})`. -/
noncomputable def chiT : TR N ℂ →+* TR N LL := mapT (HahnSeries.C : ℂ →+* LL)

theorem chiT_injective : Function.Injective (chiT N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine ext_cf fun j hj => ?_
  have h := congrArg (cfT j) hx
  rw [chiT, cf_mapT _ hj, cf_zero j hj] at h
  rw [cf_zero j hj]
  exact HahnSeries.C_injective (by rw [h, map_zero])

theorem chiT_psiC (a : ℂ) : chiT N (psiC N a) = psiL N (HahnSeries.C a) := by
  rw [chiT, psiC, psiL, RingHom.comp_apply, RingHom.comp_apply, mapT_mkT, PowerSeries.map_C]

theorem chiT_mkT (f : PowerSeries ℂ) : chiT N (mkT N ℂ f) = iotaZ N f := by
  rw [chiT, mapT_mkT]
  rfl

theorem chiT_comp_phiA : (chiT N).comp (phiA N ℂ) = phiL N := by
  ext f : 1
  rw [RingHom.comp_apply, chiT, mapT_phiA]
  rfl

/-- The source `(A_1,…,A_N,-A_1,…,-A_N)`. -/
noncomputable def J0 : Modes N → TR N ℂ :=
  Sum.elim (fun i : Fin N => psiC N (Acoef ((i : ℕ) + 1)))
    (fun i : Fin N => -psiC N (Acoef ((i : ℕ) + 1)))

theorem JL_eq (a : Modes N) : JL N (psiL N) a = psiL N tL⁻¹ * chiT N (J0 N a) := by
  rcases a with i | i
  · simp only [JL, J0, Sum.elim_inl, chiT_psiC]
  · simp only [JL, J0, Sum.elim_inr, map_neg, chiT_psiC, mul_neg]

/-- `½ J₀·CJ₀ = 𝓘₀(z)` modulo `z^{N+1}` (sphere/paper.tex l.684, Lemma 3.4(iii)). -/
theorem J0CJ0_eq :
    (1 / 2 : ℚ) • ∑ a, ∑ b, J0 N a * covN N (phiA N ℂ) N a b * J0 N b =
      mkT N ℂ (I0def sigmaStar (fun m => -sigmaStar m)) := by
  apply chiT_injective N
  have hu : psiL N tL * psiL N tL⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ tL_ne_zero, map_one]
  have h := JCJ_eq N
  have e1 : (1 / 2 : ℚ) • ∑ a, ∑ b, JL N (psiL N) a * covN N (phiL N) N a b * JL N (psiL N) b =
      psiL N tL⁻¹ ^ 2 *
        chiT N ((1 / 2 : ℚ) • ∑ a, ∑ b, J0 N a * covN N (phiA N ℂ) N a b * J0 N b) := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [JL_eq, JL_eq, map_mul, map_mul, map_covN, chiT_comp_phiA,
      RingHom.map_rat_algebraMap]
    ring
  rw [e1] at h
  have h2 : chiT N ((1 / 2 : ℚ) • ∑ a, ∑ b, J0 N a * covN N (phiA N ℂ) N a b * J0 N b) =
      iotaZ N (I0def sigmaStar (fun m => -sigmaStar m)) := by
    linear_combination (psiL N tL ^ 2) * h -
      (chiT N ((1 / 2 : ℚ) • ∑ a, ∑ b, J0 N a * covN N (phiA N ℂ) N a b * J0 N b) -
        iotaZ N (I0def sigmaStar (fun m => -sigmaStar m))) * (psiL N tL * psiL N tL⁻¹ + 1) * hu
  rw [h2, chiT_mkT]

end Value

/-! ### The pairings -/

theorem phiA_X (N : ℕ) : phiA N ℂ PowerSeries.X = mkT N ℂ PowerSeries.X := by
  rw [phiA, RingHom.comp_apply, PowerSeries.map_X]

/-- The Fock pairing of the level-`j` parts of `e^{E_λ}` and its conjugate. -/
theorem gauss_pair (lam : ℂ) {j N : ℕ} (hj : j ≤ N) :
    ∑ α ∈ (finite_level j).toFinset, algebraMap ℚ ℂ (fockNormQ α) *
        (coeff α (mexp (gaussExpo lam)) * coeff α (mexp (gaussExpo (-lam)))) =
      PowerSeries.coeff j (EI (lam ^ 2) * detInvSqrt.map (algebraMap ℚ ℂ)) := by
  have hJ : (1 / 2 : ℚ) • ∑ a, ∑ b,
      (Sum.elim (fun i : Fin N => psiC N lam * psiC N (Acoef ((i : ℕ) + 1)))
          (fun i : Fin N => -(psiC N lam * psiC N (Acoef ((i : ℕ) + 1))))) a *
        covN N (phiA N ℂ) N a b *
        (Sum.elim (fun i : Fin N => psiC N lam * psiC N (Acoef ((i : ℕ) + 1)))
          (fun i : Fin N => -(psiC N lam * psiC N (Acoef ((i : ℕ) + 1))))) b =
      mkT N ℂ (PowerSeries.C (lam ^ 2) * I0def sigmaStar (fun m => -sigmaStar m)) := by
    have hJa : ∀ a : Modes N,
        (Sum.elim (fun i : Fin N => psiC N lam * psiC N (Acoef ((i : ℕ) + 1)))
          (fun i : Fin N => -(psiC N lam * psiC N (Acoef ((i : ℕ) + 1))))) a =
        psiC N lam * J0 N a := by
      intro a
      rcases a with i | i
      · simp only [J0, Sum.elim_inl]
      · simp only [J0, Sum.elim_inr, mul_neg]
    simp only [hJa]
    rw [map_mul, ← J0CJ0_eq, Algebra.smul_def, Algebra.smul_def, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show mkT N ℂ (PowerSeries.C (lam ^ 2)) = psiC N lam ^ 2 by
      rw [psiC, RingHom.comp_apply, ← map_pow, ← map_pow]]
    ring
  have hg : PowerSeries.constantCoeff
      (PowerSeries.C (lam ^ 2) * I0def sigmaStar (fun m => -sigmaStar m)) = 0 := by
    rw [map_mul, constantCoeff_I0def, mul_zero]
  rw [← cf_fockP_pair (N := N) _ _ hj]
  have hprod := gauss_prod_eq (N := N) (psiC N) lam
  rw [psiC] at hprod
  rw [hprod, ← phiA_X, fockP_gauss_linear (phiA N ℂ) le_rfl (phiA_X_pow N ℂ)]
  rw [← psiC, hJ, ← mkT_exp_subst _ hg]
  show cfT j (mkT N ℂ _ * mkT N ℂ (detInvSqrt.map (algebraMap ℚ ℂ))) = _
  rw [← map_mul, cf_mkT hj]
  rfl

/-- `⟨F̃_N, F_N⟩` for the pure Gaussian `F = e^{E_λ}`, `λ` real: the coefficient of `z^N` of
`det(I - M(z)²)^{-1/2} e^{λ²𝓘₀(z)}` (sphere/paper.tex l.1035–1045). -/
theorem gaussF_norm (lam : ℝ) (j : ℕ) :
    fockForm (gaussF (lam : ℂ) j) (gaussF (lam : ℂ) j) =
      PowerSeries.coeff j (EI ((lam : ℂ) ^ 2) * detInvSqrt.map (algebraMap ℚ ℂ)) := by
  rw [← gauss_pair (lam : ℂ) (le_refl j)]
  have hs : (gaussF (lam : ℂ) j).support ⊆ (finite_level j).toFinset := by
    intro α hα
    rw [Set.Finite.mem_toFinset]
    exact gaussF_mem_level (lam : ℂ) j (MvPolynomial.mem_support_iff.mp hα)
  rw [fockForm_eq _ _ _ hs]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hα' : lvl α = j := by
    rw [Set.Finite.mem_toFinset] at hα
    exact hα
  have hc : coeff α (mexp (gaussExpo (-(lam : ℂ)))) =
      (starRingEnd ℂ) (coeff α (mexp (gaussExpo (lam : ℂ)))) := by
    rw [← conj_gaussExpo, ← map_mexp (starRingEnd ℂ) (by
      rw [constantCoeff_gaussExpo]
      exact IsNilpotent.zero), MvPowerSeries.coeff_map]
  rw [coeff_gaussF_of_level (lam : ℂ) hα', hc, fockNorm_eq]
  simp only [eq_ratCast]
  ring

end Virasoro.Sphere
