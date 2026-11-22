import Virasoro.Sphere.Proofs.Sec3GaussLift

/-!
# Evaluation at the saddle point modulo `z^{n+1}` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.672–675, l.698–702.  "Every saddle factor `σ_{*,m}`, `σ̄_{*,m}` has `z`-order at
least `m`; modulo `z^{N+1}` only finitely many oscillator modes contribute."  For a series `T`
in the `σ_m`, the value `T(σ_*)` modulo `z^{n+1}` is computed with the modes `≤ n` in
`ℂ[[z]]/(z^{n+1})`; the coefficient of the fluctuation variable `x_m` in `T(σ_* + x)` is
`(∂_{σ_m} T)(σ_*)`.  This identifies `constC` and `gradL` of `gauss_lift`.
-/

namespace Virasoro.Sphere

open MvPowerSeries

local notation "KK" => RatFunc ℂ

section PderivTrans

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The translation commutes with the partial derivatives. -/
theorem pderiv_trans {a : ι → R} (ha : ∀ i, IsNilpotent (a i)) (Φ : MvPowerSeries ι R) (j : ι) :
    pderiv R j (trans a Φ) = trans a (pderiv R j Φ) := by
  classical
  choose k hk using ha
  have hk0 : ∀ i, a i ^ (∑ i, k i) = 0 := fun i =>
    pow_eq_zero_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (hk i)
  have ha' : ∀ i, IsNilpotent (a i) := fun i => ⟨_, hk0 i⟩
  ext e
  have l1 : IsLocal (Fintype.card ι * (e.degree + 1 + ∑ i, k i) + 1)
      ((coeff e).comp ((pderiv R j).toLinearMap.comp (transLin ha'))) := by
    intro Φ hΦ
    show coeff e (pderiv R j (transLin ha' Φ)) = 0
    rw [transLin_apply, coeff_pderiv,
      coeff_trans_eq_zero hk0 (e.degree + 1) Φ (fun α hα => hΦ α (hα.trans (Nat.le_succ _))) _
        (by rw [map_add, Finsupp.degree_single]), zero_mul]
  have l2 : IsLocal (Fintype.card ι * (e.degree + 1 + ∑ i, k i) + 1)
      ((coeff e).comp ((transLin ha').comp (pderiv R j).toLinearMap)) := by
    intro Φ hΦ
    show coeff e (transLin ha' (pderiv R j Φ)) = 0
    rw [transLin_apply]
    refine coeff_trans_eq_zero hk0 e.degree _ (fun α hα => ?_) e le_rfl
    rw [coeff_pderiv, hΦ, zero_mul]
    rw [map_add, Finsupp.degree_single]
    have : Fintype.card ι * (e.degree + ∑ i, k i) ≤
        Fintype.card ι * (e.degree + 1 + ∑ i, k i) := Nat.mul_le_mul_left _ (by omega)
    omega
  have key := LinearMap.congr_fun (IsLocal.ext l1 l2 fun α => by
    show coeff e (pderiv R j (transLin ha' (monomial α 1))) =
      coeff e (transLin ha' (pderiv R j (monomial α 1)))
    rw [transLin_apply, transLin_apply, pderiv_trans_monomial]) Φ
  change coeff e (pderiv R j (transLin ha' Φ)) = coeff e (transLin ha' (pderiv R j Φ)) at key
  rwa [transLin_apply, transLin_apply] at key

theorem coeff_single_eq (f : MvPowerSeries ι R) (x : ι) :
    coeff (Finsupp.single x 1) f = constantCoeff (pderiv R x f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

theorem map_pderivG {S : Type*} [CommRing S] (ψ : R →+* S) {τ : Type*} [DecidableEq τ] (x : τ)
    (G : MvPowerSeries τ R) : map ψ (pderiv R x G) = pderiv S x (map ψ G) := by
  ext e
  rw [coeff_map, coeff_pderiv, coeff_pderiv, coeff_map, map_mul]
  simp

end PderivTrans

section Grad

variable {n : ℕ} {S : Type*} [CommRing S]

theorem pderiv_subst_eS {s : Fin n → Modes n} (hs : Function.Injective s)
    (G : MvPowerSeries ℕ+ S) (i : Fin n) :
    pderiv S (s i) (subst (eS (S := S) s) G) =
      subst (eS (S := S) s) (pderiv S (modeEmb n i) G) := by
  classical
  ext γ
  by_cases hγ : γ ∈ Set.range (Finsupp.mapDomain s : (Fin n →₀ ℕ) → _)
  · obtain ⟨g, rfl⟩ := hγ
    rw [coeff_pderiv, coeff_subst_eS_map hs, coeff_pderiv,
      show Finsupp.mapDomain s g + Finsupp.single (s i) 1 =
        Finsupp.mapDomain s (g + Finsupp.single i 1) by
        rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single],
      coeff_subst_eS_map hs, Finsupp.mapDomain_apply hs,
      Finsupp.mapDomain_apply (modeEmb_injective (N := n)), Finsupp.mapDomain_add,
      Finsupp.mapDomain_single]
  · rw [coeff_pderiv, coeff_subst_eS_of_not hs _ γ hγ, coeff_subst_eS_of_not hs, zero_mul]
    rintro ⟨g', hg'⟩
    refine hγ ⟨g' - Finsupp.single i 1, ?_⟩
    have h1 : g' i = γ (s i) + 1 := by
      have := DFunLike.congr_fun hg' (s i)
      rw [Finsupp.mapDomain_apply hs] at this
      simpa using this
    have h2 : g' - Finsupp.single i 1 + Finsupp.single i 1 = g' := by
      ext y
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with hy
      · subst hy
        omega
      · omega
    refine add_right_cancel (b := Finsupp.single (s i) 1) ?_
    rw [← hg', ← Finsupp.mapDomain_single (f := s) (a := i) (b := 1), ← Finsupp.mapDomain_add, h2]

theorem pderiv_subst_eS_zero {s : Fin n → Modes n} (hs : Function.Injective s)
    (G : MvPowerSeries ℕ+ S) (x : Modes n) (hx : x ∉ Set.range s) :
    pderiv S x (subst (eS (S := S) s) G) = 0 := by
  classical
  ext γ
  rw [coeff_pderiv, coeff_subst_eS_of_not hs, zero_mul, map_zero]
  rintro ⟨g', hg'⟩
  have := DFunLike.congr_fun hg' x
  rw [Finsupp.mapDomain_of_notMem_range _ _ hx] at this
  simp at this

theorem subst_bS_one_eq_trans (s : Fin n → Modes n) {a : Modes n → S}
    (ha : ∀ x, IsNilpotent (a x)) (G : MvPowerSeries ℕ+ S) :
    subst (bS s 1 a) G = trans a (subst (eS (S := S) s) G) := by
  have h1 : (fun x => (1 : S) * a x) = a := funext fun x => one_mul _
  have h2 : rescale (fun _ : ℕ+ => (1 : S)) G = G := by
    rw [show (fun _ : ℕ+ => (1 : S)) = 1 from rfl, rescale_one]
    rfl
  have h := trans_subst_rescale s ha 1 1 (one_mul 1) G
  rw [h1, h2] at h
  exact h.symm

/-- The coefficient of the fluctuation variable `x_{s(i)}` in `G(a + x)` is `(∂_{i+1}G)(a)`. -/
theorem coeff_single_subst_bS {s : Fin n → Modes n} (hs : Function.Injective s)
    {a : Modes n → S} (ha : ∀ x, IsNilpotent (a x)) (G : MvPowerSeries ℕ+ S) (i : Fin n) :
    coeff (Finsupp.single (s i) 1) (subst (bS s 1 a) G) =
      constantCoeff (subst (cS s a) (pderiv S (modeEmb n i) G)) := by
  rw [coeff_single_eq, subst_bS_one_eq_trans s ha, pderiv_trans ha, pderiv_subst_eS hs,
    ← subst_bS_one_eq_trans s ha]
  exact constantCoeff_subst_congr (hasSubst_bS s 1 ha) (hasSubst_cS s ha)
    (constantCoeff_bS_one s a) _

theorem coeff_single_subst_bS_zero {s : Fin n → Modes n} (hs : Function.Injective s)
    {a : Modes n → S} (ha : ∀ x, IsNilpotent (a x)) (G : MvPowerSeries ℕ+ S) (x : Modes n)
    (hx : x ∉ Set.range s) : coeff (Finsupp.single x 1) (subst (bS s 1 a) G) = 0 := by
  have ha' : HasSubst (fun i => (X i + C (a i) : MvPowerSeries (Modes n) S)) := hasSubst_trans ha
  rw [coeff_single_eq, subst_bS_one_eq_trans s ha, pderiv_trans ha, pderiv_subst_eS_zero hs _ x hx,
    trans, ← coe_substAlgHom ha', map_zero, map_zero]

end Grad

section Eval

variable {n : ℕ}

/-- Evaluation modulo `z^{n+1}` (sphere/paper.tex l.672–675): if `σ_m ≡ 0` for `m > n`, the value
`T(σ)` modulo `z^{n+1}` is the value of `T` at the constants `σ_m mod z^{n+1}`, `m ≤ n`. -/
theorem eval_cS (s : Fin n → Modes n) {a : Modes n → TR n ℂ} (ha : ∀ x, IsNilpotent (a x))
    {σ : ℕ+ → PowerSeries ℂ} (hσ : HasSubst σ)
    (hcs : ∀ m, cS s a m = C (mkT n ℂ (σ m))) (T : MvPowerSeries ℕ+ ℂ) :
    constantCoeff (subst (cS s a) (map (psiC n) T)) = mkT n ℂ (subst σ T) := by
  classical
  have hc := hasSubst_cS s ha
  have hterm : ∀ d : ℕ+ →₀ ℕ,
      coeff d (map (psiC n) T) • coeff 0 (d.prod fun m e => cS s a m ^ e) =
        mkT n ℂ (PowerSeries.C (coeff d T) * d.prod fun m e => σ m ^ e) := by
    intro d
    have e1 : (d.prod fun m e => cS s a m ^ e) =
        C (mkT n ℂ (d.prod fun m e => σ m ^ e)) := by
      rw [Finsupp.prod, Finsupp.prod, map_prod, map_prod]
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [hcs, map_pow, map_pow]
    rw [e1, coeff_zero_eq_constantCoeff_apply, constantCoeff_C, coeff_map, smul_eq_mul, map_mul]
    rfl
  have hfin : (Function.support fun d : ℕ+ →₀ ℕ =>
      mkT n ℂ (PowerSeries.C (coeff d T) * d.prod fun m e => σ m ^ e)).Finite := by
    rw [← funext hterm]
    exact coeff_subst_finite hc _ 0
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst hc, funext hterm,
    finsum_eq_sum _ hfin, ← map_sum, mkT_eq_iff]
  intro j _
  rw [map_sum]
  show _ = MvPowerSeries.coeff (Finsupp.single () j) (subst σ T)
  rw [coeff_subst hσ, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [PowerSeries.coeff_C_mul, smul_eq_mul]
    rfl
  · intro d hd
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    refine hd ?_
    have h1 := (mkT_eq_zero_iff _).1 h0 j ‹j ≤ n›
    rw [PowerSeries.coeff_C_mul] at h1
    show _ • _ = 0
    rw [smul_eq_mul]
    exact h1

theorem cS_inl_sgC (m : ℕ+) : cS Sum.inl (sgC n) m = C (mkT n ℂ (sigmaStar m)) := by
  rw [cS]
  split_ifs with h
  · have hm : modeEmb n ⟨(m : ℕ) - 1, by have := m.pos; omega⟩ = m := by
      apply PNat.eq
      rw [modeEmb_coe]
      have := m.pos
      simp only
      omega
    rw [sgC, Sum.elim_inl, hm]
  · have h0 : mkT n ℂ (sigmaStar m) = 0 := by
      rw [mkT_eq_zero_iff]
      intro j hj
      have h1 := smul_sigmaStar_dvd 1 m
      rw [one_smul] at h1
      exact PowerSeries.X_pow_dvd_iff.1 h1 j (by omega)
    rw [h0, map_zero]

theorem cS_inr_sgC (m : ℕ+) :
    cS Sum.inr (sgC n) m = C (mkT n ℂ ((fun m => -sigmaStar m) m)) := by
  have h2 : cS Sum.inr (sgC n) m = C (-1) * cS Sum.inl (sgC n) m := by
    rw [cS, cS]
    split_ifs
    · rw [← map_mul]
      simp [sgC]
    · rw [mul_zero]
  rw [h2, cS_inl_sgC, ← map_mul, neg_one_mul]
  simp only [map_neg]

theorem hasSubst_sigmaStar : HasSubst sigmaStar := isSaddle_sigmaStar.hasSubst

theorem hasSubst_sigmaStar_neg : HasSubst (fun m => -sigmaStar m) := isSaddle_sigmaStar.hasSubst_bar

theorem eval_inl (T : MvPowerSeries ℕ+ ℂ) :
    constantCoeff (subst (cS Sum.inl (sgC n)) (map (psiC n) T)) =
      mkT n ℂ (subst sigmaStar T) :=
  eval_cS Sum.inl isNilpotent_sgC hasSubst_sigmaStar cS_inl_sgC T

theorem eval_inr (T : MvPowerSeries ℕ+ ℂ) :
    constantCoeff (subst (cS Sum.inr (sgC n)) (map (psiC n) T)) =
      mkT n ℂ (subst (fun m => -sigmaStar m) T) :=
  eval_cS Sum.inr isNilpotent_sgC hasSubst_sigmaStar_neg cS_inr_sgC T

theorem toPNat_modeEmb (i : Fin n) : ((i : ℕ) + 1).toPNat' = modeEmb n i := by
  apply PNat.eq
  rw [Nat.toPNat'_coe, if_pos (Nat.succ_pos _)]
  rfl

/-- `constC` is `S⁽²⁾(σ_*) + S̃⁽²⁾(σ̄_*)` modulo `z^{n+1}`. -/
theorem constC_eq (F F' : ℕ → MvPolynomial ℕ+ KK) :
    constC (n := n) F F' = mkT n ℂ (subst sigmaStar (Sord F 2)) +
      mkT n ℂ (subst (fun m => -sigmaStar m) (conjSeries (Sord F' 2))) := by
  rw [constC, eval_inl, eval_inr]

/-- `gradL` on the variables `U_m`: `(∂_{σ_m} S⁽¹⁾)(σ_*)` modulo `z^{n+1}`. -/
theorem gradL_inl (F F' : ℕ → MvPolynomial ℕ+ KK) (i : Fin n) :
    gradL (n := n) F F' (Sum.inl i) =
      mkT n ℂ (subst sigmaStar (pd ((i : ℕ) + 1) (Sord F 1))) := by
  rw [gradL, map_add, coeff_single_subst_bS Sum.inl_injective isNilpotent_sgC,
    coeff_single_subst_bS_zero Sum.inr_injective isNilpotent_sgC _ _ (by simp), add_zero,
    ← map_pderivG, eval_inl, pd, toPNat_modeEmb]

/-- `gradL` on the variables `V_m`: `(∂_{σ̄_m} S̃⁽¹⁾)(σ̄_*)` modulo `z^{n+1}`. -/
theorem gradL_inr (F F' : ℕ → MvPolynomial ℕ+ KK) (i : Fin n) :
    gradL (n := n) F F' (Sum.inr i) =
      mkT n ℂ (subst (fun m => -sigmaStar m) (pd ((i : ℕ) + 1) (conjSeries (Sord F' 1)))) := by
  rw [gradL, map_add, coeff_single_subst_bS Sum.inr_injective isNilpotent_sgC,
    coeff_single_subst_bS_zero Sum.inl_injective isNilpotent_sgC _ _ (by simp), zero_add,
    ← map_pderivG, eval_inr, pd, toPNat_modeEmb]

end Eval

end Virasoro.Sphere
