import Virasoro.Sphere.Proofs.Sec3GaussLiftTools
import Virasoro.Sphere.Proofs.Sec3GaussExpect
import Virasoro.Sphere.Proofs.Sec3LamData

/-!
# The `λ⁻¹`-expansion of the shifted factor `R` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.684–702.  After the shift `z^m u_m = λσ_{*,m} + U_m`, `ū_m = λσ̄_{*,m} + V_m`,
the exponent of `R` is `λ T(σ_* + t x) + λ T̃(σ̄_* + t x̄)`, `T = S⁽¹⁾ + t T₂`.  The order `λ¹`,
`λ(S⁽¹⁾(σ_*) + S̃⁽¹⁾(σ̄_*))`, vanishes by `ι`-oddness of `S⁽¹⁾` and `σ̄_* = -σ_*`; the rest has
coefficients in `ℂ[[t]][[z]]/(z^{n+1})`, and at `t = 0` it is the linear form with the
coefficients of the gradient of `S⁽¹⁾` at the saddle point, plus the constant
`S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩
local notation "PP" => PowerSeries ℂ

section Lift

variable (n : ℕ)

/-- `ℂ[[t]] → ℂ[[t]][[z]]/(z^{n+1})`. -/
noncomputable def psiP : PP →+* TR n PP := (mkT n PP).comp PowerSeries.C

/-- `ℂ → ℂ[[z]]/(z^{n+1})`. -/
noncomputable def psiC : ℂ →+* TR n ℂ := (mkT n ℂ).comp PowerSeries.C

/-- `t` in `ℂ[[t]][[z]]/(z^{n+1})`. -/
noncomputable def tP : TR n PP := psiP n PowerSeries.X

/-- Conjugation of the coefficients of a series in `t`. -/
noncomputable def conjP : PP →+* PP := PowerSeries.map (starRingEnd ℂ)

/-- The saddle point `(σ_*, σ̄_*)` in `ℂ[[t]][[z]]/(z^{n+1})`. -/
noncomputable def sgP : Modes n → TR n PP :=
  Sum.elim (fun i => mkT n PP (PowerSeries.map PowerSeries.C (sigmaStar (modeEmb n i))))
    (fun i => -mkT n PP (PowerSeries.map PowerSeries.C (sigmaStar (modeEmb n i))))

/-- The saddle point `(σ_*, σ̄_*)` in `ℂ[[z]]/(z^{n+1})`. -/
noncomputable def sgC : Modes n → TR n ℂ :=
  Sum.elim (fun i => mkT n ℂ (sigmaStar (modeEmb n i)))
    (fun i => -mkT n ℂ (sigmaStar (modeEmb n i)))

variable {n}

theorem isNilpotent_mkT {A : Type*} [CommRing A] (g : PowerSeries A)
    (hg : PowerSeries.constantCoeff g = 0) : IsNilpotent (mkT n A g) := by
  obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
  exact ⟨n + 1, by rw [map_mul, mul_pow, mkT_X_pow, zero_mul]⟩

theorem constantCoeff_sigmaStar (m : ℕ+) : PowerSeries.constantCoeff (sigmaStar m) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_sigmaStar,
    if_neg (by have := m.pos; omega), mul_zero]

theorem isNilpotent_sgP (x : Modes n) : IsNilpotent (sgP n x) := by
  rcases x with i | i
  · exact isNilpotent_mkT _ (constantCoeff_map_zero _ (constantCoeff_sigmaStar _))
  · exact (isNilpotent_mkT _ (constantCoeff_map_zero _ (constantCoeff_sigmaStar _))).neg

theorem isNilpotent_sgC (x : Modes n) : IsNilpotent (sgC n x) := by
  rcases x with i | i
  · exact isNilpotent_mkT _ (constantCoeff_sigmaStar _)
  · exact (isNilpotent_mkT _ (constantCoeff_sigmaStar _)).neg

theorem rhoT_psiP (p : PP) : rhoT n (psiP n p) = psiL n (HahnSeries.ofPowerSeries ℤ ℂ p) := by
  rw [rhoT, psiP, psiL, RingHom.comp_apply, RingHom.comp_apply, mapT_mkT, PowerSeries.map_C]

theorem rhoT_tP : rhoT n (tP n) = psiL n tL := by
  rw [tP, rhoT_psiP, HahnSeries.ofPowerSeries_X]
  rfl

theorem rhoT_sgP (x : Modes n) : rhoT n (sgP n x) = sgT n x := by
  have h : ∀ i : Fin n,
      rhoT n (mkT n PP (PowerSeries.map PowerSeries.C (sigmaStar (modeEmb n i)))) = sgL n i := by
    intro i
    rw [← iotaZ_sigmaStar, rhoT, mapT_mkT, iotaZ, RingHom.comp_apply]
    refine congrArg _ (PowerSeries.ext fun k => ?_)
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map,
      HahnSeries.ofPowerSeries_C]
  rcases x with i | i
  · exact h i
  · show rhoT n (-_) = -sgL n i
    rw [map_neg, h i]

theorem epsT_psiP (p : PP) : epsT n (psiP n p) = psiC n (PowerSeries.constantCoeff p) := by
  rw [epsT, psiP, psiC, RingHom.comp_apply, RingHom.comp_apply, mapT_mkT, PowerSeries.map_C]

theorem epsT_tP : epsT n (tP n) = 0 := by
  rw [tP, epsT_psiP, PowerSeries.constantCoeff_X, map_zero]

theorem epsT_sgP (x : Modes n) : epsT n (sgP n x) = sgC n x := by
  have h : ∀ i : Fin n,
      epsT n (mkT n PP (PowerSeries.map PowerSeries.C (sigmaStar (modeEmb n i)))) =
        mkT n ℂ (sigmaStar (modeEmb n i)) := by
    intro i
    rw [epsT, mapT_mkT]
    refine congrArg _ (PowerSeries.ext fun k => ?_)
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.constantCoeff_C]
  rcases x with i | i
  · exact h i
  · show epsT n (-_) = -_
    rw [map_neg, h i]

theorem sgT_nilpotent (x : Modes n) : IsNilpotent (sgT n x) := by
  rw [← rhoT_sgP]
  exact (isNilpotent_sgP x).map _

theorem cS_inr_sgP (m : ℕ+) :
    cS Sum.inr (sgP n) m = C (-1) * cS Sum.inl (sgP n) m := by
  rw [cS, cS]
  split_ifs
  · rw [← map_mul]
    simp [sgP]
  · rw [mul_zero]

theorem constantCoeff_bS_one (s : Fin n → Modes n) {S : Type*} [CommRing S] (a : Modes n → S)
    (m : ℕ+) : constantCoeff (bS s 1 a m) = constantCoeff (cS s a m) := by
  rw [bS, map_add, map_mul, eS]
  split_ifs <;> simp

section Main

variable {μ Δ1 Δ2 Δ3 Δ4 : ℂ} {F F' : ℕ → MvPolynomial ℕ+ KK}
  (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)
  (h' : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ4) (RatFunc.C Δ3) F')

/-- The order `λ¹` vanishes (sphere/paper.tex l.685–688): `S⁽¹⁾(σ_*) + S̃⁽¹⁾(σ̄_*) = 0`, from
`ι`-oddness and `σ̄_* = -σ_*`. -/
theorem constantCoeff_order_one (hodd : iota (Sord F' 1) = -Sord F 1) :
    constantCoeff
      (subst (bS Sum.inl 1 (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) +
        subst (bS Sum.inr 1 (sgP n))
          (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1))) = 0 := by
  have hl := hasSubst_cS (n := n) Sum.inl (isNilpotent_sgP (n := n))
  have hr := hasSubst_cS (n := n) Sum.inr (isNilpotent_sgP (n := n))
  have e1 : rescale (fun _ => (-1 : TR n PP))
      (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1)) =
      -map ((psiP n).comp PowerSeries.C) (Sord F 1) := by
    ext α
    have h1 := congrArg (coeff α) hodd
    rw [coeff_iota, map_neg] at h1
    rw [coeff_rescale, prod_const_pow, coeff_map, map_neg, coeff_map, RingHom.comp_apply,
      RingHom.comp_apply, RingHom.comp_apply, conjP, PowerSeries.map_C]
    have h2 := congrArg (fun c => psiP n (PowerSeries.C c)) h1
    simp only [map_mul, map_pow, map_neg, map_one] at h2
    exact h2
  have e2 : subst (cS Sum.inr (sgP n))
      (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1)) =
      -subst (cS Sum.inl (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) := by
    rw [show cS Sum.inr (sgP n) = fun m => C (-1) * cS Sum.inl (sgP n) m from
      funext cS_inr_sgP, ← subst_rescale hl, e1, ← coe_substAlgHom hl, map_neg]
  rw [map_add,
    constantCoeff_subst_congr (hasSubst_bS Sum.inl 1 isNilpotent_sgP) hl
      (constantCoeff_bS_one Sum.inl (sgP n)),
    constantCoeff_subst_congr (hasSubst_bS Sum.inr 1 isNilpotent_sgP) hr
      (constantCoeff_bS_one Sum.inr (sgP n)), e2, map_neg, add_neg_cancel]

/-- The gradient of `S⁽¹⁾` at the saddle point: the coefficient of the fluctuation variable `x`
in `S⁽¹⁾(σ_* + x) + S̃⁽¹⁾(σ̄_* + x̄)`, in `ℂ[[z]]/(z^{n+1})`. -/
noncomputable def gradL (F F' : ℕ → MvPolynomial ℕ+ KK) (x : Modes n) : TR n ℂ :=
  coeff (Finsupp.single x 1)
    (subst (bS Sum.inl 1 (sgC n)) (map (psiC n) (Sord F 1)) +
      subst (bS Sum.inr 1 (sgC n)) (map (psiC n) (conjSeries (Sord F' 1))))

/-- `S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*)` in `ℂ[[z]]/(z^{n+1})`. -/
noncomputable def constC (F F' : ℕ → MvPolynomial ℕ+ KK) : TR n ℂ :=
  constantCoeff (subst (cS Sum.inl (sgC n)) (map (psiC n) (Sord F 2))) +
    constantCoeff (subst (cS Sum.inr (sgC n)) (map (psiC n) (conjSeries (Sord F' 2))))

theorem trans_remU (F : ℕ → MvPolynomial ℕ+ KK) :
    trans (fun x => psiL n tL⁻¹ * sgT n x) (remU (psiL n) F) =
      map (rhoT n) (subst (bS Sum.inl (tP n) (sgP n)) (map (psiP n) (SPtail F))) := by
  have htl : psiL n tL * psiL n tL⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ tL_ne_zero, map_one]
  have ea : (fun m => map (rhoT n) (bS Sum.inl (tP n) (sgP n) m)) =
      bS Sum.inl (psiL n tL) (sgT n) := by
    funext m
    rw [map_bS, rhoT_tP, show (fun x => rhoT n (sgP n x)) = sgT n from funext rhoT_sgP]
  have ef : map (rhoT n) (map (psiP n) (SPtail F)) =
      map ((psiL n).comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F) := by
    ext α
    rw [coeff_map, coeff_map, coeff_map, RingHom.comp_apply, rhoT_psiP]
  rw [remU, trans_subst_rescale Sum.inl sgT_nilpotent _ _ htl,
    map_subst (hasSubst_bS Sum.inl (tP n) isNilpotent_sgP), ea, ef]

theorem trans_remB (F : ℕ → MvPolynomial ℕ+ KK) :
    trans (fun x => psiL n tL⁻¹ * sgT n x) (remB (psiL n) F) =
      map (rhoT n) (subst (bS Sum.inr (tP n) (sgP n))
        (map ((psiP n).comp conjP) (SPtail F))) := by
  have htl : psiL n tL * psiL n tL⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ tL_ne_zero, map_one]
  have ea : (fun m => map (rhoT n) (bS Sum.inr (tP n) (sgP n) m)) =
      bS Sum.inr (psiL n tL) (sgT n) := by
    funext m
    rw [map_bS, rhoT_tP, show (fun x => rhoT n (sgP n x)) = sgT n from funext rhoT_sgP]
  have ef : map (rhoT n) (map ((psiP n).comp conjP) (SPtail F)) =
      map (((psiL n).comp cL).comp (HahnSeries.ofPowerSeries ℤ ℂ)) (SPtail F) := by
    ext α
    rw [coeff_map, coeff_map, coeff_map, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, rhoT_psiP, conjP, cL_ofPowerSeries]
  rw [remB, trans_subst_rescale Sum.inr sgT_nilpotent _ _ htl,
    map_subst (hasSubst_bS Sum.inr (tP n) isNilpotent_sgP), ea, ef]

/-- `T(σ_* + t x) = S⁽¹⁾(σ_* + t x) + t T₂(σ_* + t x)`. -/
theorem subst_SPtail (s : Fin n → Modes n) (χ : PP →+* TR n PP)
    (hχ : χ PowerSeries.X = tP n) (F : ℕ → MvPolynomial ℕ+ KK) :
    subst (bS s (tP n) (sgP n)) (map χ (SPtail F)) =
      rescale (fun _ => tP n)
          (subst (bS s 1 (sgP n)) (map (χ.comp PowerSeries.C) (Sord F 1))) +
        tP n • subst (bS s (tP n) (sgP n)) (map χ (SPtail2 F)) := by
  have hb := hasSubst_bS s (tP n) (isNilpotent_sgP (n := n))
  have e : map χ (SPtail F) =
      map (χ.comp PowerSeries.C) (Sord F 1) + tP n • map χ (SPtail2 F) := by
    ext α
    rw [coeff_map, SPtail_split, map_add, map_mul, hχ, map_add, coeff_smul, coeff_map,
      coeff_map, RingHom.comp_apply]
  rw [e, subst_add hb, subst_smul hb, subst_bS_eq_rescale s (tP n) isNilpotent_sgP]

include h h' in
/-- Step 3 of Lemma 3.3(iii) (sphere/paper.tex l.684–702): the exponent of the shifted factor
`R` has coefficients in `ℂ[[t]][[z]]/(z^{n+1})`, and at `t = 0` it is the linear form of the
gradient of `S⁽¹⁾` at the saddle point plus the constant `S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*)`. -/
theorem gauss_lift (hodd : iota (Sord F' 1) = -Sord F 1) :
    ∃ EP : MvPowerSeries (Modes n) (TR n PP), IsNilpotent (constantCoeff EP) ∧
      trans (fun x => psiL n tL⁻¹ * sgT n x)
          (psiL n tL⁻¹ • remU (psiL n) F + psiL n tL⁻¹ • remB (psiL n) F') =
        map (rhoT n) EP ∧
      map (epsT n) EP = linForm (gradL (n := n) F F') + C (constC (n := n) F F') ∧
      IsNilpotent (constC (n := n) F F') := by
  have hbl := fun r : TR n PP => hasSubst_bS Sum.inl r (isNilpotent_sgP (n := n))
  have hbr := fun r : TR n PP => hasSubst_bS Sum.inr r (isNilpotent_sgP (n := n))
  have hχ : ((psiP n).comp conjP) PowerSeries.X = tP n := by
    rw [RingHom.comp_apply, conjP, PowerSeries.map_X, tP]
  have hzero : ∀ (χ : PP →+* TR n PP) (G : ℕ → MvPolynomial ℕ+ KK) {μ' l' a' b' : KK},
      IsWardSeries μ' l' a' b' G → IsNilpotent (constantCoeff (map χ (SPtail2 G))) := by
    intro χ G _ _ _ _ hG
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_SPtail2 hG, map_zero]
    exact IsNilpotent.zero
  have ha' : ∀ x, IsNilpotent (psiL n tL⁻¹ * sgT n x) := fun x => by
    obtain ⟨k, hk⟩ := sgT_nilpotent x
    exact ⟨k, by rw [mul_pow, hk, mul_zero]⟩
  have hlt : psiL n tL⁻¹ * psiL n tL = 1 := by
    rw [← map_mul, inv_mul_cancel₀ tL_ne_zero, map_one]
  refine ⟨dq (tP n) (subst (bS Sum.inl 1 (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) +
      subst (bS Sum.inr 1 (sgP n))
        (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1))) +
    subst (bS Sum.inl (tP n) (sgP n)) (map (psiP n) (SPtail2 F)) +
    subst (bS Sum.inr (tP n) (sgP n)) (map ((psiP n).comp conjP) (SPtail2 F')), ?_, ?_, ?_, ?_⟩
  · rw [map_add, map_add, constantCoeff_dq, zero_add]
    exact Commute.isNilpotent_add (Commute.all _ _) (IsNilpotent_subst (hbl _) (hzero _ F h))
      (IsNilpotent_subst (hbr _) (hzero _ F' h'))
  · have hA : trans (fun x => psiL n tL⁻¹ * sgT n x)
          (psiL n tL⁻¹ • remU (psiL n) F + psiL n tL⁻¹ • remB (psiL n) F') =
        psiL n tL⁻¹ • trans (fun x => psiL n tL⁻¹ * sgT n x) (remU (psiL n) F) +
          psiL n tL⁻¹ • trans (fun x => psiL n tL⁻¹ * sgT n x) (remB (psiL n) F') := by
      unfold trans
      rw [subst_add (hasSubst_trans ha'), subst_smul (hasSubst_trans ha'),
        subst_smul (hasSubst_trans ha')]
    have hD := rescale_eq_dq (tP n)
      (subst (bS Sum.inl 1 (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) +
        subst (bS Sum.inr 1 (sgP n))
          (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1)))
    rw [constantCoeff_order_one hodd, map_zero, zero_add, map_add] at hD
    rw [hA, trans_remU, trans_remB, subst_SPtail Sum.inl (psiP n) rfl,
      subst_SPtail Sum.inr ((psiP n).comp conjP) hχ, ← smul_add, ← map_add]
    have hsum : rescale (fun _ => tP n)
          (subst (bS Sum.inl 1 (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1))) +
        tP n • subst (bS Sum.inl (tP n) (sgP n)) (map (psiP n) (SPtail2 F)) +
        (rescale (fun _ => tP n) (subst (bS Sum.inr 1 (sgP n))
            (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1))) +
          tP n • subst (bS Sum.inr (tP n) (sgP n))
            (map ((psiP n).comp conjP) (SPtail2 F'))) =
        C (tP n) * (dq (tP n)
          (subst (bS Sum.inl 1 (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) +
            subst (bS Sum.inr 1 (sgP n))
              (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1))) +
          subst (bS Sum.inl (tP n) (sgP n)) (map (psiP n) (SPtail2 F)) +
          subst (bS Sum.inr (tP n) (sgP n)) (map ((psiP n).comp conjP) (SPtail2 F'))) := by
      rw [smul_eq_C_mul, smul_eq_C_mul]
      linear_combination hD
    rw [hsum, map_mul, map_C, rhoT_tP, smul_eq_C_mul, ← mul_assoc, ← map_mul, hlt, map_one,
      one_mul]
  · have eaC : ∀ (s : Fin n → Modes n) (r : TR n PP),
        (fun m => map (epsT n) (bS s r (sgP n) m)) = bS s (epsT n r) (sgC n) := by
      intro s r
      funext m
      rw [map_bS, show (fun x => epsT n (sgP n x)) = sgC n from funext epsT_sgP]
    have eb0 : ∀ s : Fin n → Modes n, bS s (0 : TR n ℂ) (sgC n) = cS s (sgC n) := by
      intro s
      funext m
      rw [bS, map_zero, zero_mul, zero_add]
    have ef1 : map (epsT n) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) =
        map (psiC n) (Sord F 1) := by
      ext α
      rw [coeff_map, coeff_map, coeff_map, RingHom.comp_apply, epsT_psiP,
        PowerSeries.constantCoeff_C]
    have ef1b : map (epsT n) (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1)) =
        map (psiC n) (conjSeries (Sord F' 1)) := by
      ext α
      rw [coeff_map, coeff_map, coeff_map, RingHom.comp_apply, RingHom.comp_apply, epsT_psiP,
        conjP, PowerSeries.map_C, PowerSeries.constantCoeff_C, conjSeries, coeff_map]
    have ef2 : map (epsT n) (map (psiP n) (SPtail2 F)) = map (psiC n) (Sord F 2) := by
      ext α
      rw [coeff_map, coeff_map, coeff_map, epsT_psiP, ← map_constantCoeff_SPtail2, coeff_map]
    have ef2b : map (epsT n) (map ((psiP n).comp conjP) (SPtail2 F')) =
        map (psiC n) (conjSeries (Sord F' 2)) := by
      ext α
      rw [coeff_map, coeff_map, coeff_map, RingHom.comp_apply, epsT_psiP, conjSeries, coeff_map,
        ← map_constantCoeff_SPtail2, coeff_map, conjP,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    have hL : (fun x => epsT n (coeff (Finsupp.single x 1)
        (subst (bS Sum.inl 1 (sgP n)) (map ((psiP n).comp PowerSeries.C) (Sord F 1)) +
          subst (bS Sum.inr 1 (sgP n))
            (map (((psiP n).comp conjP).comp PowerSeries.C) (Sord F' 1))))) =
        gradL (n := n) F F' := by
      funext x
      rw [← coeff_map, map_add, map_subst (hbl 1), map_subst (hbr 1), eaC, eaC, map_one, ef1,
        ef1b, gradL]
    rw [map_add, map_add, map_dq_zero (epsT n) (tP n) epsT_tP, hL, map_subst (hbl _),
      map_subst (hbr _), eaC, eaC, epsT_tP, eb0, eb0, ef2, ef2b,
      subst_cS_eq_C Sum.inl isNilpotent_sgC, subst_cS_eq_C Sum.inr isNilpotent_sgC, constC,
      map_add, add_assoc]
  · have hz2 : ∀ (G : ℕ → MvPolynomial ℕ+ KK) {μ' l' a' b' : KK}, IsWardSeries μ' l' a' b' G →
        MvPowerSeries.coeff 0 (Sord G 2) = 0 := fun G _ _ _ _ hG => coeff_zero_Sord hG 2
    refine Commute.isNilpotent_add (Commute.all _ _)
      (IsNilpotent_subst (hasSubst_cS Sum.inl isNilpotent_sgC) ?_)
      (IsNilpotent_subst (hasSubst_cS Sum.inr isNilpotent_sgC) ?_)
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hz2 F h, map_zero]
      exact IsNilpotent.zero
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, conjSeries, coeff_map, hz2 F' h',
        map_zero, map_zero]
      exact IsNilpotent.zero

end Main

end Lift

end Virasoro.Sphere
