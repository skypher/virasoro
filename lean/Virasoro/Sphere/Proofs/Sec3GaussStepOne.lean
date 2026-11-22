import Virasoro.Sphere.Proofs.Sec3GaussPair
import Virasoro.Sphere.Proofs.Sec3GaussLog
import Virasoro.Sphere.Proofs.Sec3GaussQuadPart
import Virasoro.Sphere.Proofs.Sec3GaussConj
import Virasoro.Sphere.Proofs.Sec3GaussCharged

/-!
# `ℬ(z) mod z^{N+1}` as a Gaussian expectation (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.637–668.  In `ℂ((t))[[z]]/(z^{N+1})`, `t = 1/λ`:
`ℬ(z) ≡ 𝔼_{Q₀}[exp(λ²S⁽⁰⁾(u/λ) + λ²S̃⁽⁰⁾(ū/λ)) R]`, the exponent of the first factor is `q + J·x`
with `q` the quadratic part and `J = λ(A, -A)`, and completing the square gives
`ℬ(z) ≡ e^{½J·CJ} 𝔼_{Q₀}[e^q R(x + CJ)]` with `C` the Neumann covariance.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

section StepOne

variable {N : ℕ} {R' : Type*} [CommRing R'] [Algebra ℚ R'] (ψ : LL →+* R')

/-- `T(tu)` in the modes `u_1,…,u_N`, with `T = (S - S⁽⁰⁾)/t`: `λ` times it is the logarithm of
the first factor of `R` (sphere/paper.tex l.647–650). -/
noncomputable def remU (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries (Modes N) R' :=
  subst (eS (N := N) (S := R') Sum.inl)
    (rescale (fun _ => ψ tL) (map (ψ.comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F)))

/-- `T̃(tū)` in the modes `ū_1,…,ū_N`. -/
noncomputable def remB (F : ℕ → MvPolynomial ℕ+ KK) : MvPowerSeries (Modes N) R' :=
  subst (eS (N := N) (S := R') Sum.inr)
    (rescale (fun _ => ψ tL) (map ((ψ.comp cL).comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F)))

variable (N) in
/-- The source `J = λ (A_1,…,A_N,-A_1,…,-A_N)`. -/
noncomputable def JL : Modes N → R' :=
  Sum.elim (fun i : Fin N => ψ tL⁻¹ * ψ (HahnSeries.C (Acoef ((i : ℕ) + 1))))
    (fun i : Fin N => -(ψ tL⁻¹ * ψ (HahnSeries.C (Acoef ((i : ℕ) + 1)))))

omit [Algebra ℚ R'] in
theorem constantCoeff_eS (s : Fin N → Modes N) (m : ℕ+) :
    constantCoeff (eS (N := N) (S := R') s m) = 0 := by
  rw [eS]
  split_ifs <;> simp

omit [Algebra ℚ R'] in
theorem constantCoeff_subst_eS (s : Fin N → Modes N) (f : MvPowerSeries ℕ+ R')
    (hf : constantCoeff f = 0) : constantCoeff (subst (eS (N := N) (S := R') s) f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_eS _) (constantCoeff_eS _) hf

theorem coeff_zero_SPtail {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) : constantCoeff (SPtail F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  ext r
  rw [coeff_SPtail]
  show PowerSeries.coeff (r + 1)
    (PowerSeries.mk fun r : ℕ => (coeff 0 (SL F)).coeff (r : ℤ)) = _
  rw [PowerSeries.coeff_mk, coeff_zero_SL F (constantCoeff_wardSeries h)]
  simp

omit [Algebra ℚ R'] in
theorem constantCoeff_rescale_map {A' : Type*} [CommRing A'] (r : R') (χ : A' →+* R')
    (T : MvPowerSeries ℕ+ A') (hT : constantCoeff T = 0) :
    constantCoeff (rescale (fun _ => r) (map χ T)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_map,
    coeff_zero_eq_constantCoeff_apply, hT, map_zero, mul_zero]

omit [Algebra ℚ R'] in
theorem constantCoeff_remU {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) : constantCoeff (remU (N := N) ψ F) = 0 :=
  constantCoeff_subst_eS _ _ (constantCoeff_rescale_map _ _ _ (coeff_zero_SPtail h))

omit [Algebra ℚ R'] in
theorem constantCoeff_remB {μ lam Δa Δb : KK} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries μ lam Δa Δb F) : constantCoeff (remB (N := N) ψ F) = 0 :=
  constantCoeff_subst_eS _ _ (constantCoeff_rescale_map _ _ _ (coeff_zero_SPtail h))

section Factor

variable {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
  (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)

include h

/-- The restricted Ward solution is `exp(λ² S⁽⁰⁾(tu) + λ T(tu))`, for any coefficient map
`ψ` out of `ℂ((t))`. -/
theorem subst_ward_eq (s : Fin N → Modes N) :
    subst (eS (N := N) (S := R') s) (map (ψ.comp EInf) (wardSeries F)) =
      mexp (ψ (tL⁻¹) ^ 2 • subst (eS (N := N) (S := R') s)
          (rescale (fun _ => ψ tL) (map (ψ.comp HahnSeries.C) S0)) +
        ψ (tL⁻¹) • subst (eS (N := N) (S := R') s) (rescale (fun _ => ψ tL)
          (map (ψ.comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F)))) := by
  have h0 : IsNilpotent (constantCoeff (logW F)) := by
    rw [constantCoeff_logW h]
    exact IsNilpotent.zero
  have h1 : IsNilpotent (constantCoeff (map (ψ.comp EInf) (logW F))) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_logW h, map_zero]
    exact IsNilpotent.zero
  rw [wardSeries_eq_mexp h, map_mexp _ h0, subst_mexp h1 (hasSubst_eS s), map_logW h,
    subst_add (hasSubst_eS s), subst_smul (hasSubst_eS s), subst_smul (hasSubst_eS s)]

end Factor

/-- Step 1 of Lemma 3.3(iii), second half (sphere/paper.tex l.641–650): the product of the two
restricted Ward solutions is `e^{q + J·x} R`. -/
theorem ward_prod_eq {μ Δ1 Δ2 Δ3 Δ4 : ℂ} {F F' : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)
    (h' : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ4) (RatFunc.C Δ3) F') :
    subst (eS (N := N) (S := R') Sum.inl) (map (ψ.comp EInf) (wardSeries F)) *
      subst (eS (N := N) (S := R') Sum.inr) (map ((ψ.comp cL).comp EInf) (wardSeries F')) =
    mexp (quadB N R' + linForm (JL N ψ)) *
      mexp (ψ tL⁻¹ • remU ψ F + ψ tL⁻¹ • remB ψ F') := by
  have e3 : map ((ψ.comp cL).comp HahnSeries.C) S0 =
      map (ψ.comp HahnSeries.C) (conjSeries S0) := by
    ext α
    simp only [coeff_map, RingHom.comp_apply, conjSeries, cL_C]
  have e4 : (ψ.comp cL) tL⁻¹ = ψ tL⁻¹ := by
    rw [RingHom.comp_apply, map_inv₀, cL_tL]
  have e5 : (ψ.comp cL) tL = ψ tL := by
    rw [RingHom.comp_apply, cL_tL]
  have hlt : ψ tL⁻¹ * ψ tL = 1 := by
    rw [← map_mul, inv_mul_cancel₀ tL_ne_zero, map_one]
  rw [subst_ward_eq ψ h Sum.inl, subst_ward_eq (ψ.comp cL) h' Sum.inr, e3, e4, e5]
  have hS := subst_S0_eq (N := N) (ψ.comp HahnSeries.C) (ψ tL⁻¹) (ψ tL) hlt
  have hcS : constantCoeff (conjSeries S0) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, conjSeries, coeff_map, coeff_zero_S0, map_zero]
  have hc0 : constantCoeff S0 = 0 := coeff_zero_S0
  have n1 : IsNilpotent (constantCoeff (ψ tL⁻¹ ^ 2 • subst (eS (N := N) (S := R') Sum.inl)
      (rescale (fun _ => ψ tL) (map (ψ.comp HahnSeries.C) S0)) +
      ψ tL⁻¹ • subst (eS (N := N) (S := R') Sum.inl) (rescale (fun _ => ψ tL)
          (map (ψ.comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F))))) := by
    rw [map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul,
      constantCoeff_subst_eS _ _ (constantCoeff_rescale_map _ _ _ hc0),
      constantCoeff_subst_eS _ _ (constantCoeff_rescale_map _ _ _ (coeff_zero_SPtail h)),
      ]
    simp only [mul_zero, add_zero]
    exact IsNilpotent.zero
  have n2 : IsNilpotent (constantCoeff (ψ tL⁻¹ ^ 2 • subst (eS (N := N) (S := R') Sum.inr)
      (rescale (fun _ => ψ tL) (map (ψ.comp HahnSeries.C) (conjSeries S0))) +
      ψ tL⁻¹ • subst (eS (N := N) (S := R') Sum.inr) (rescale (fun _ => ψ tL)
          (map ((ψ.comp cL).comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F'))))) := by
    rw [map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul,
      constantCoeff_subst_eS _ _ (constantCoeff_rescale_map _ _ _ hcS),
      constantCoeff_subst_eS _ _ (constantCoeff_rescale_map _ _ _ (coeff_zero_SPtail h')),
      ]
    simp only [mul_zero, add_zero]
    exact IsNilpotent.zero
  have n3 : IsNilpotent (constantCoeff (quadB N R' + linForm (JL N ψ))) := by
    rw [map_add, constantCoeff_quadB, constantCoeff_linForm, add_zero]
    exact IsNilpotent.zero
  have n4 : IsNilpotent (constantCoeff (ψ tL⁻¹ • remU (N := N) ψ F + ψ tL⁻¹ • remB ψ F')) := by
    rw [map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, constantCoeff_remU ψ h,
      constantCoeff_remB ψ h']
    simp only [mul_zero, add_zero]
    exact IsNilpotent.zero
  rw [← mexp_add n1 n2, ← mexp_add n3 n4]
  congr 1
  have hS' : quadB N R' + linForm (JL N ψ) =
      ψ tL⁻¹ ^ 2 • subst (eS (N := N) (S := R') Sum.inl)
        (rescale (fun _ => ψ tL) (map (ψ.comp HahnSeries.C) S0)) +
      ψ tL⁻¹ ^ 2 • subst (eS (N := N) (S := R') Sum.inr)
        (rescale (fun _ => ψ tL) (map (ψ.comp HahnSeries.C) (conjSeries S0))) := hS.symm
  rw [hS', remU, remB]
  abel

end StepOne

section Shift

variable (N : ℕ)

/-- `ℂ((t)) → ℂ((t))[[z]]/(z^{N+1})`. -/
noncomputable def psiL : LL →+* TR N LL := (mkT N LL).comp PowerSeries.C

/-- `ℚ[[z]] → ℂ((t))[[z]]/(z^{N+1})`. -/
noncomputable def phiL : PowerSeries ℚ →+* TR N LL :=
  (mkT N LL).comp (PowerSeries.map (algebraMap ℚ LL))

theorem phiL_X : phiL N PowerSeries.X = mkT N LL PowerSeries.X := by
  rw [phiL, RingHom.comp_apply, PowerSeries.map_X]

theorem phiL_X_pow : phiL N PowerSeries.X ^ (N + 1) = 0 := by
  rw [phiL_X]
  exact mkT_X_pow

variable {N} (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- Steps 1–2 of Lemma 3.3(iii) (sphere/paper.tex l.637–668): for `j ≤ N`, `ℬ_j` (expanded at
`λ = ∞`) is the coefficient of `z^j` of `e^{½J·CJ} 𝔼_{Q₀}[e^q R(x + CJ)]`, with `C` the Neumann
covariance of the perturbed Hessian and `J = λ(A, -A)`. -/
theorem EInf_pairK_eq_shift (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) {j : ℕ} (hj : j ≤ N) :
    EInf (pairK μ Δe j) =
      cfT j (IsNilpotent.exp ((1 / 2 : ℚ) •
          ∑ a, ∑ b, JL N (psiL N) a * covN N (phiL N) N a b * JL N (psiL N) b) *
        fockP N N (phiL N PowerSeries.X)
          (mexp (quadB N (TR N LL)) *
            trans (fun a => ∑ b, covN N (phiL N) N a b * JL N (psiL N) b)
              (mexp (psiL N tL⁻¹ • remU (psiL N) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
                psiL N tL⁻¹ • remB (psiL N) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ)))))) := by
  have h1 := cf_fockP_ward (N := N) hF hK μ hμ Δe hj
  have e1 : ∀ W : MvPowerSeries ℕ+ KK, map ((mkT N LL).comp PowerSeries.C) (map EInf W) =
      map ((psiL N).comp EInf) W := fun W => by
    ext α
    simp only [coeff_map, RingHom.comp_apply, psiL]
  have e2 : ∀ W : MvPowerSeries ℕ+ KK,
      map ((mkT N LL).comp PowerSeries.C) (map (EInf.comp conjK) W) =
      map (((psiL N).comp cL).comp EInf) W := fun W => by
    ext α
    simp only [coeff_map, RingHom.comp_apply, psiL, EInf_conjK]
  have hp := ward_prod_eq (N := N) (R' := TR N LL) (psiL N)
    (wardRat_isWard hF hK μ hμ (Δe 0 : ℂ) (Δe 1 : ℂ))
    (wardRat_isWard hF hK μ hμ (Δe 3 : ℂ) (Δe 2 : ℂ))
  have hg := fockP_gauss_shift (n := N) (K := N) (phiL N) (phiL_X_pow N) (JL N (psiL N))
    (mexp (psiL N tL⁻¹ • remU (psiL N) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)) +
      psiL N tL⁻¹ • remB (psiL N) (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ))))
  rw [e1, e2, hp, ← phiL_X, hg] at h1
  exact h1.symm

end Shift

end Virasoro.Sphere
