import Virasoro.Proofs.AppAModeCount
import Virasoro.Proofs.AppAOddPrimes
import Virasoro.Proofs.AppALevelPoly

/-!
# Proposition 9.2(i)–(ii) of `paper.tex` from Lemmas A.1–A.3 (l.3104–3161)

The proof of Proposition 9.2(i)–(ii) at the end of Appendix A, consuming the three frozen
statements of Appendix A.
- Lemma A.1 (`Stmt_lem_mode_count`): `G̃(0,Y) = D₀(Y)` and `ρ̃(0,Y;ζ)` does not depend on `ζ`.
  The first makes `P_M^{(ν)}` regular at `t = 0` (with the Kac determinant this gives
  `P_M^{(ν)} ∈ ℚ[t,Y]`) and gives the formula for `P_M^{(ν)}(0,Y)`; the second gives
  `P_M^{(2)}(0,Y) = P_M^{(1)}(0,Y)` (l.3113–3123).  The matrices of the lemma are tied to `GsM`,
  `RsM` through the injectivity of `ℚ[t,Y,ζ] → ℚ(t,Y,ζ)`.
- Lemma A.2 (`Stmt_lem_odd_primes`): in `𝒮_𝔭`, `P_M^{(ν)}(t,Y)` is the prefactor times
  `∑_s η_s Tr(M! G_{M−s}⁻¹ ρ_{M−s})`, which lies in `𝒮_𝔭`; the algebraic independence of `t` and
  `Y` in the residue field gives `𝒮_𝔭 ∩ ℚ[t,Y] = ℤ_(ϖ)[t,Y]` (l.3125–3142).
- Lemma A.3 (`Stmt_lem_level_poly`): the sum over `s` of `η_s M(M−1)⋯(M−s+1)(Y/2)^s R_{M−s}`
  and the normalized prefactor (l.3144–3160).
Parts (iii) and (iv) follow from (i) and (ii) as in the paper (`sub_h13_valuation`,
`sub_h13_lipschitz`).
-/

namespace Virasoro

open Polynomial H13D

/-! ### Part (ii) from Lemma A.3 -/

theorem tyToRat_injective : Function.Injective tyToRat := by
  intro a b hab
  have ha := tyToRat_thetaMv (thetaInv a)
  have hb := tyToRat_thetaMv (thetaInv b)
  rw [thetaMv_thetaInv] at ha hb
  rw [← thetaMv_thetaInv a, ← thetaMv_thetaInv b, psi_injective (ha.symm.trans (hab.trans hb))]

/-- The expansion in `t` is unique. -/
theorem IsTExpansion.unique {x : RatFunc (RatFunc ℚ)} {r r' : SerTY} (h : IsTExpansion x r)
    (h' : IsTExpansion x r') : r = r' := by
  obtain ⟨p, q, -, hp, hu, hr⟩ := h
  obtain ⟨p', q', -, hp', hu', hr'⟩ := h'
  have e : p * q' = p' * q := tyToRat_injective (by rw [map_mul, map_mul, hp, hp']; ring)
  have e2 := congrArg tyToSer e
  rw [map_mul, map_mul, ← hr, ← hr'] at e2
  apply (hu.mul hu').mul_right_cancel
  linear_combination e2

/-- `[t^i Y^j] R_M` is a polynomial in `M` of degree at most `2i + 2j`, from Lemma A.3. -/
theorem degFam_R_of_levelPoly (h : Stmt_lem_level_poly) (ν : Fin 2) : DegFam (Rfam ν) := by
  obtain ⟨R, hR, hdeg⟩ := h ν
  have e : R = Rfam ν := funext fun M => (hR M).unique (isTExpansion_Rfam ν M)
  subst e
  exact hdeg

/-- Proposition 9.2(ii) from Lemma A.3 (paper.tex l.3144–3160). -/
theorem sub_h13_degree_of_levelPoly (h : Stmt_lem_level_poly) : Stmt_sub_h13_degree := by
  intro P hP ν i j
  obtain ⟨f, hf1, hf2⟩ := ((degFam_R_of_levelPoly h ν).S).N_mul i (j : ℤ)
  refine ⟨f, natDegree_le_iff_coeff_eq_zero.2 fun N hN => hf1 N (by omega), fun M => ?_⟩
  have hQ : clearedH ν M = psi (thetaInv (P ν M)) := by
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  have h3 := cf_iM_thetaInv (P ν M) i j
  rw [iM_Q hQ, cf_cQ_mul] at h3
  have h4 : cf (Nfam M * Sfam ν M) i (j : ℤ) = f.eval (M : ℚ) := hf2 M
  rw [← h4, ← h3]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))

/-! ### Integrality in part (i) from Lemma A.2 -/

section OddPrimes

variable {K : Type} [Field K] [CharZero K] {S : Subring K} [IsDiscreteValuationRing S]

omit [IsDiscreteValuationRing S] in
theorem coe_aeval_int (v : Fin 2 → S) (f : MvPolynomial (Fin 2) ℤ) :
    ((MvPolynomial.aeval v f : S) : K) =
      MvPolynomial.aeval (fun i => (v i : K)) (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  change S.subtype (MvPolynomial.eval₂ (algebraMap ℤ S) v f) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

/-- `𝒮_𝔭 ∩ ℚ[t,Y] = ℤ_(ϖ)[t,Y]` (paper.tex l.3139–3141): a rational polynomial whose value at
`(t, Y)` lies in `𝒮_𝔭` has `ϖ`-integral coefficients. -/
theorem coeff_local_of_mem {ϖ : ℕ} (hϖ : ϖ.Prime) (hirr : Irreducible ((ϖ : ℕ) : S))
    (v : Fin 2 → S)
    (hind : ∀ f : MvPolynomial (Fin 2) ℤ, (∃ e, ¬ (ϖ : ℤ) ∣ f.coeff e) →
      MvPolynomial.aeval v f ∉ IsLocalRing.maximalIdeal S)
    (P : MvPolynomial (Fin 2) ℚ) (hP : MvPolynomial.aeval (fun i => (v i : K)) P ∈ S)
    (e : Fin 2 →₀ ℕ) :
    ∃ a c : ℤ, ¬ ((ϖ : ℤ) ∣ c) ∧ MvPolynomial.coeff e P = (a : ℚ) / c := by
  obtain ⟨D, Pt, hD, hPt⟩ := H13Local.exists_clear P
  set xS : S := ⟨_, hP⟩ with hxS
  have hPtS : MvPolynomial.aeval v Pt = (D : S) * xS := by
    apply Subtype.ext
    rw [coe_aeval_int, hPt, map_mul, MvPolynomial.aeval_C, map_natCast]
    rfl
  have hmax : ((ϖ : ℕ) : S) ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hirr.not_isUnit)
  have hϖ0 : ((ϖ : ℕ) : S) ≠ 0 := hirr.ne_zero
  have hCS : ∀ (z : ℤ) (Q : MvPolynomial (Fin 2) ℤ),
      MvPolynomial.aeval v (MvPolynomial.C z * Q) = (z : S) * MvPolynomial.aeval v Q := by
    intro z Q
    rw [map_mul, MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast]
  have key : ∀ j : ℕ, j ≤ D.factorization ϖ → MvPolynomial.C (((ϖ : ℕ) : ℤ) ^ j) ∣ Pt := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [pow_zero, MvPolynomial.C_1]
      exact one_dvd _
    | succ j ih =>
      intro hj
      obtain ⟨Q, hQ⟩ := ih (by omega)
      obtain ⟨D2, hD2⟩ : ϖ ^ (j + 1) ∣ D := (pow_dvd_pow ϖ hj).trans (Nat.ordProj_dvd D ϖ)
      have h3 : ((ϖ : ℕ) : S) ^ j * MvPolynomial.aeval v Q =
          ((ϖ : ℕ) : S) ^ j * (((ϖ : ℕ) : S) * ((D2 : S) * xS)) := by
        have h1 := hCS (((ϖ : ℕ) : ℤ) ^ j) Q
        rw [← hQ, hPtS, hD2] at h1
        push_cast at h1
        rw [← h1]
        ring
      have hQv := mul_left_cancel₀ (pow_ne_zero _ hϖ0) h3
      have hQm : MvPolynomial.aeval v Q ∈ IsLocalRing.maximalIdeal S := by
        rw [hQv]
        exact Ideal.mul_mem_right _ _ hmax
      have hdiv : ∀ e, ((ϖ : ℕ) : ℤ) ∣ Q.coeff e := by
        by_contra hne
        push Not at hne
        exact hind Q hne hQm
      obtain ⟨Q', hQ'⟩ := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).2 hdiv
      exact ⟨Q', by rw [hQ, hQ', ← mul_assoc, ← MvPolynomial.C_mul, pow_succ]⟩
  obtain ⟨Q, hQ⟩ := key _ le_rfl
  have hc : (D : ℚ) * MvPolynomial.coeff e P =
      (ϖ : ℚ) ^ D.factorization ϖ * ((MvPolynomial.coeff e Q : ℤ) : ℚ) := by
    have := congrArg (MvPolynomial.coeff e) hPt
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, hQ, MvPolynomial.coeff_C_mul] at this
    rw [← this, eq_intCast]
    push_cast
    rfl
  have hDv : (D : ℚ) = (ϖ : ℚ) ^ D.factorization ϖ * ((D / ϖ ^ D.factorization ϖ : ℕ) : ℚ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self D ϖ).symm
  have hlq : (ϖ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hϖ.ne_zero
  have hne : ((D / ϖ ^ D.factorization ϖ : ℕ) : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hDv
    exact hD (by exact_mod_cast hDv)
  refine ⟨MvPolynomial.coeff e Q, ((D / ϖ ^ D.factorization ϖ : ℕ) : ℤ), ?_, ?_⟩
  · intro hd
    exact Nat.not_dvd_ordCompl hϖ hD (by exact_mod_cast hd)
  · rw [Int.cast_natCast, eq_div_iff hne]
    apply mul_left_cancel₀ (pow_ne_zero (D.factorization ϖ) hlq)
    rw [← hc, hDv]
    ring

/-- For an odd prime `ϖ`, the coefficients of `P_M^{(ν)}` are `ϖ`-integral, from the data of
Lemma A.2 (paper.tex l.3129–3142). -/
theorem coeff_local_of_dvr {ϖ : ℕ} (hϖ : ϖ.Prime) (h2 : ϖ ≠ 2) {ν : Fin 2} {M : ℕ}
    {P : MvPolynomial (Fin 2) ℚ} (hQ : clearedH ν M = psi (thetaInv P))
    (hirr : Irreducible ((ϖ : ℕ) : S))
    (hloc : ∀ (z : ℤ) (n : ℕ), ¬ ϖ ∣ n → (z : K) / (n : K) ∈ S)
    (b q₀ α Y : S) (hb : IsUnit b)
    (hc : cT ((b : K) ^ 2) = 1 - 12 * (q₀ : K) ^ 2)
    (hY : (Y : K) = (b : K) ^ 4 * (α : K) * ((α : K) - 2 * (q₀ : K)) / 2)
    (hind : ∀ f : MvPolynomial (Fin 2) ℤ, (∃ e, ¬ (ϖ : ℤ) ∣ f.coeff e) →
        MvPolynomial.aeval (![b ^ 2, Y] : Fin 2 → S) f ∉ IsLocalRing.maximalIdeal S)
    (hgram : ∀ M s : ℕ, s ≤ M →
        (gram (cT ((b : K) ^ 2)) ((α : K) * ((α : K) - 2 * (q₀ : K)) / 2) (M - s)).det ≠ 0 ∧
        ∀ Z Z' : Nat.Partition (M - s),
          (M.factorial : K) *
              (gram (cT ((b : K) ^ 2)) ((α : K) * ((α : K) - 2 * (q₀ : K)) / 2) (M - s))⁻¹ Z Z'
            ∈ S)
    (e : Fin 2 →₀ ℕ) :
    ∃ a c : ℤ, ¬ ((ϖ : ℤ) ∣ c) ∧ MvPolynomial.coeff e P = (a : ℚ) / c := by
  -- memberships in `𝒮_𝔭`
  have hhalf : (2 : K)⁻¹ ∈ S := by
    have := hloc 1 2 fun h => h2 ((Nat.prime_dvd_prime_iff_eq hϖ Nat.prime_two).1 h)
    simpa using this
  have htwo : (2 : K) ∈ S := by exact_mod_cast natCast_mem S 2
  obtain ⟨u, hu⟩ := hb
  have h1 : (b : K) * ((↑u⁻¹ : S) : K) = 1 := by
    have := congrArg S.subtype (Units.mul_inv u)
    rwa [map_mul, map_one, hu] at this
  have hbK : (b : K) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hbinv : (b : K)⁻¹ ∈ S := by
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact (↑u⁻¹ : S).2
  set t₀ : K := (b : K) ^ 2 with ht₀
  set μ : K := (α : K) * ((α : K) - 2 * (q₀ : K)) / 2 with hμ
  have ht0 : t₀ ≠ 0 := pow_ne_zero 2 hbK
  have ht0m : t₀ ∈ S := S.pow_mem b.2 2
  have ht0i : t₀⁻¹ ∈ S := by
    rw [ht₀, ← inv_pow]
    exact S.pow_mem hbinv 2
  have hμm : μ ∈ S := by
    rw [hμ, div_eq_mul_inv]
    exact S.mul_mem (S.mul_mem α.2 (S.sub_mem α.2 (S.mul_mem htwo q₀.2))) hhalf
  have hcm : cT t₀ ∈ S := by
    rw [hc]
    exact S.sub_mem S.one_mem (S.mul_mem (by exact_mod_cast natCast_mem S 12) (S.pow_mem q₀.2 2))
  have hdm : dvalK ν t₀ ∈ S := by
    unfold dvalK
    split_ifs
    · rw [div_eq_mul_inv]
      exact S.sub_mem (S.neg_mem S.one_mem) (S.mul_mem htwo ht0i)
    · rw [div_eq_mul_inv]
      exact S.sub_mem htwo (S.mul_mem htwo ht0i)
  have hhT : ∀ u : ℕ, hT (u : ℤ) 1 t₀ ∈ S := by
    intro u
    have e : hT (u : ℤ) 1 t₀ =
        ((t₀ + 1) ^ 2 - ((u : ℤ) * t₀ + ((1 : ℤ) : K)) ^ 2) * 2⁻¹ * 2⁻¹ * t₀⁻¹ := by
      unfold hT
      field_simp
      ring
    rw [e]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.sub_mem (S.pow_mem (S.add_mem ht0m S.one_mem) 2)
      (S.pow_mem (S.add_mem (S.mul_mem (intCast_mem S _) ht0m) (intCast_mem S _)) 2))
      hhalf) hhalf) ht0i
  have hhalfT : TFock.half K ∈ S := by
    unfold TFock.half
    rw [map_div₀, map_one, map_ofNat, one_div]
    exact hhalf
  -- `P(t,Y) = ∏_u t²(2Δ − 2h_{u,1}) ∑_s η_s Tr(M! G_{M−s}⁻¹ ρ_{M−s})` (l.3131–3137)
  let W : ℕ → K := fun j => ∑ Z, ∑ Z', ((M.factorial : K) * (gram (cT t₀) μ (M - j))⁻¹ Z Z') *
    torus (cT t₀) μ (dvalK ν t₀) (M - j) Z Z'
  have hW : ∀ j ∈ Finset.range (M + 1), W j ∈ S := by
    intro j hj
    have hjM : j ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact S.sum_mem fun Z _ => S.sum_mem fun Z' _ => S.mul_mem ((hgram M j hjM).2 Z Z')
      (TFock.torusWord_mem hhalfT hcm hμm hdm _ _)
  have hD : ∀ j ∈ Finset.range (M + 1), (gram (cT t₀) μ (M - j)).det ≠ 0 :=
    fun j hj => (hgram M j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).1
  have hAW : ∀ j ∈ Finset.range (M + 1), (M.factorial : K) * AK ν t₀ μ (M - j) =
      (gram (cT t₀) μ (M - j)).det * W j := by
    intro j hj
    have hd := hD j hj
    simp only [AK, W, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    field_simp
  have hprod : ∏ j ∈ Finset.range (M + 1), (gram (cT t₀) μ (M - j)).det ≠ 0 :=
    Finset.prod_ne_zero_iff.2 hD
  have spec := specK (K := K) hQ ht0 μ
  rw [sigK_thetaInv] at spec
  have hs : (M.factorial : K) * ∑ j ∈ Finset.range (M + 1), (eta j : K) * AK ν t₀ μ (M - j) *
        ∏ i ∈ (Finset.range (M + 1)).erase j, (gram (cT t₀) μ (M - i)).det =
      (∑ j ∈ Finset.range (M + 1), (eta j : K) * W j) *
        ∏ j ∈ Finset.range (M + 1), (gram (cT t₀) μ (M - j)).det := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.mul_prod_erase _ (fun i => (gram (cT t₀) μ (M - i)).det) hj]
    linear_combination ((eta j : K) * ∏ i ∈ (Finset.range (M + 1)).erase j,
      (gram (cT t₀) μ (M - i)).det) * hAW j hj
  have hval : MvPolynomial.aeval ![t₀, t₀ ^ 2 * μ] P =
      (∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀))) *
        ∑ j ∈ Finset.range (M + 1), (eta j : K) * W j := by
    apply mul_right_cancel₀ hprod
    linear_combination spec +
      (∏ u ∈ Finset.Icc 1 M, (t₀ ^ 2 * (2 * μ - 2 * hT (u : ℤ) 1 t₀))) * hs
  have hmem : MvPolynomial.aeval ![t₀, t₀ ^ 2 * μ] P ∈ S := by
    rw [hval]
    refine S.mul_mem (S.prod_mem fun u _ => S.mul_mem (S.pow_mem ht0m 2)
      (S.sub_mem (S.mul_mem htwo hμm) (S.mul_mem htwo (hhT u)))) ?_
    exact S.sum_mem fun j hj => S.mul_mem (intCast_mem S _) (hW j hj)
  have hv : (fun i => (((![b ^ 2, Y] : Fin 2 → S) i : S) : K)) = ![t₀, t₀ ^ 2 * μ] := by
    funext i
    fin_cases i
    · simp [ht₀]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hY, ht₀, hμ]
      ring
  rw [← hv] at hmem
  exact coeff_local_of_mem hϖ hirr _ hind P hmem e

end OddPrimes

/-- Proposition 9.2(i), integrality, from Lemma A.2 (paper.tex l.3125–3142). -/
theorem sub_h13_integral_of_oddPrimes (h : Stmt_lem_odd_primes) : Stmt_sub_h13_integral := by
  intro P hP ν M _ e
  apply H13Local.two_pow_of_odd
  intro ϖ hϖ h2
  have hQ : clearedH ν M = psi (thetaInv (P ν M)) := by
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  obtain ⟨K, _, _, S, _, b, q₀, α, Y, hirr, hloc, hb, -, hc, hY, hind, hgram⟩ := h ϖ hϖ h2
  exact coeff_local_of_dvr hϖ h2 hQ hirr hloc b q₀ α Y hb hc hY hind hgram e

/-! ### The matrices of Lemma A.1 and `G̃`, `ρ̃` in `ℚ[t][Y]` -/

theorem thetaMv_tS : thetaMv tS = MvPolynomial.X 0 := by simp [thetaMv, tS]

theorem thetaMv_X : thetaMv (X : PS) = MvPolynomial.X 1 := by simp [thetaMv]

theorem thetaMv_cS : thetaMv cS = ct2 := by
  simp only [thetaMv, cS, ct2, coe_eval₂RingHom, eval₂_C, map_add, map_mul, map_pow,
    AlgHom.coe_toRingHom, aeval_X]
  rw [map_ofNat (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) 6,
    map_ofNat (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) 13]

theorem thetaMv_GsM (n : ℕ) (Z Z' : Nat.Partition n) : thetaMv (GsM n Z Z') = Gt2 n Z Z' := by
  simp only [GsM, Matrix.of_apply]
  rw [← gramT_map, thetaMv_tS, thetaMv_cS, thetaMv_X]
  rfl

/-- `ζ_ν`: `ζ = −1` for `ν = 0` and `ζ = 2` for `ν = 1`. -/
noncomputable def zetaVal (ν : Fin 2) : ℚ := if ν = 0 then -1 else 2

/-- `t ↦ t`, `Y ↦ Y`, `ζ ↦ ζ_ν`. -/
noncomputable def specZ (ν : Fin 2) : MvPolynomial (Fin 3) ℚ →+* MvPolynomial (Fin 2) ℚ :=
  (MvPolynomial.aeval (R := ℚ) (σ := Fin 3)
    (![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (zetaVal ν)] :
      Fin 3 → MvPolynomial (Fin 2) ℚ)).toRingHom

theorem specZ_X0 (ν : Fin 2) : specZ ν (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [specZ]

theorem specZ_X2 (ν : Fin 2) : specZ ν (MvPolynomial.X 2) = MvPolynomial.C (zetaVal ν) := by
  simp [specZ]

theorem specZ_ct3 (ν : Fin 2) : specZ ν ct3 = ct2 := by
  simp only [ct3, ct2, map_add, map_mul, map_pow, specZ_X0]
  rw [map_ofNat (specZ ν) 6, map_ofNat (specZ ν) 13]

theorem specZ_dt3 (ν : Fin 2) : specZ ν dt3 = thetaMv (dS ν) := by
  have ha : aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) (2 : ℚ[X]) = 2 :=
    map_ofNat (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) 2
  have hC : (MvPolynomial.C (2 : ℚ) : MvPolynomial (Fin 2) ℚ) = 2 := map_ofNat _ 2
  simp only [dt3, map_add, map_mul, map_neg, specZ_X0, specZ_X2]
  rw [map_ofNat (specZ ν) 2]
  unfold dS zetaVal
  split_ifs <;> simp [thetaMv, ha, hC] <;> ring

/-- `ρ̃` at `ζ = ζ_ν` is `RsM ν`. -/
theorem thetaMv_RsM (ν : Fin 2) (n : ℕ) (Z Z' : Nat.Partition n) :
    thetaMv (RsM ν n Z Z') = specZ ν (rhot3 n Z Z') := by
  simp only [RsM, Matrix.of_apply, rhot3]
  rw [← torusWordT_map, ← torusWordT_map, thetaMv_tS, thetaMv_cS, thetaMv_X, specZ_ct3,
    specZ_dt3]
  simp [specZ]

theorem evtYz_rename_injective :
    Function.Injective fun p : MvPolynomial (Fin 2) ℚ =>
      evtYz (MvPolynomial.rename Fin.castSucc p) :=
  (IsFractionRing.injective (MvPolynomial (Fin 3) ℚ) KtYz).comp
    (MvPolynomial.rename_injective _ (Fin.castSucc_injective _))

/-- `G̃(0,Y) = D₀(Y)`, from Lemma A.1. -/
theorem GsM_ev0_of_modeCount (h : Stmt_lem_mode_count) (n : ℕ) :
    (GsM n).map ev0 = Matrix.diagonal fun Y : Nat.Partition n => D0 Y := by
  obtain ⟨G1, ρt, hA⟩ := h n
  dsimp only at hA
  obtain ⟨-, -, hG, -, -⟩ := hA
  ext Z Z'
  have e : Gt2 n Z Z' = (if Z = Z' then MvPolynomial.C (appKZ Z : ℚ) *
      MvPolynomial.X 1 ^ Z.parts.card else 0) + MvPolynomial.X 0 * G1 Z Z' :=
    evtYz_rename_injective ((evtYz_Gt2 n Z Z').trans (hG Z Z').symm)
  rw [Matrix.map_apply, ← aeval0_thetaMv, thetaMv_GsM, e, map_add, map_mul, MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero, zero_mul, add_zero]
  by_cases hZ : Z = Z'
  · subst hZ
    rw [if_pos rfl, Matrix.diagonal_apply_eq, D0, topNat_word_eq_appKZ, word_length_eq_card]
    simp
  · rw [if_neg hZ, Matrix.diagonal_apply_ne _ hZ, map_zero]

/-- `ρ̃(0,Y;ζ)` does not depend on `ζ`, from Lemma A.1: the two values `ζ = −1, 2` agree. -/
theorem RsM_ev0_of_modeCount (h : Stmt_lem_mode_count) (n : ℕ) (Z Z' : Nat.Partition n) :
    ev0 (RsM 1 n Z Z') = ev0 (RsM 0 n Z Z') := by
  obtain ⟨G1, ρt, hA⟩ := h n
  dsimp only at hA
  obtain ⟨-, -, -, hρ, h0⟩ := hA
  have e : ρt Z Z' = rhot3 n Z Z' :=
    IsFractionRing.injective (MvPolynomial (Fin 3) ℚ) KtYz ((hρ Z Z').trans (evtYz_rhot3 n Z Z').symm)
  have key : ∀ ν : Fin 2, ev0 (RsM ν n Z Z') =
      MvPolynomial.aeval (![0, X, 0] : Fin 3 → ℚ[X]) (ρt Z Z') := by
    intro ν
    let φ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] ℚ[X] :=
      MvPolynomial.aeval (![0, X, C (zetaVal ν)] : Fin 3 → ℚ[X])
    have c1 : ((MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X])).comp
        (MvPolynomial.aeval (R := ℚ) (σ := Fin 3)
          (![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (zetaVal ν)] :
            Fin 3 → MvPolynomial (Fin 2) ℚ))) = φ := by
      rw [MvPolynomial.comp_aeval]
      congr 1
      funext i
      fin_cases i <;> simp
    have c2 : φ.comp (MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℚ)) = φ := by
      rw [MvPolynomial.comp_aeval]
      congr 1
      funext i
      fin_cases i <;> simp [φ]
    have c3 : φ.comp (MvPolynomial.aeval (![0, MvPolynomial.X 1, 0] :
        Fin 3 → MvPolynomial (Fin 3) ℚ)) = MvPolynomial.aeval (![0, X, 0] : Fin 3 → ℚ[X]) := by
      rw [MvPolynomial.comp_aeval]
      congr 1
      funext i
      fin_cases i <;> simp [φ]
    rw [← aeval0_thetaMv, thetaMv_RsM, ← e]
    have d1 := AlgHom.congr_fun c1 (ρt Z Z')
    have d2 := AlgHom.congr_fun c2 (ρt Z Z')
    have d3 := AlgHom.congr_fun c3 (ρt Z Z')
    simp only [AlgHom.comp_apply] at d1 d2 d3
    rw [h0 Z Z'] at d2
    exact d1.trans (d2.symm.trans d3)
  rw [key, key]

/-! ### Values at `t = 0` in part (i) from Lemma A.1 -/

section Values

variable (hG : ∀ n : ℕ, (GsM n).map ev0 = Matrix.diagonal fun Y : Nat.Partition n => D0 Y)
include hG

theorem ev0_det_of (n : ℕ) : ev0 (GsM n).det = ∏ Y : Nat.Partition n, D0 Y := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hG, Matrix.det_diagonal]

theorem ev0_det_ne_zero_of (n : ℕ) : ev0 (GsM n).det ≠ 0 := by
  rw [ev0_det_of hG]
  exact Finset.prod_ne_zero_iff.2 fun Y _ => D0_ne_zero Y

theorem ev0_numS_of (ν : Fin 2) (n : ℕ) :
    ev0 (numS ν n) = ∑ Y : Nat.Partition n, (∏ Z ∈ Finset.univ.erase Y, D0 Z) * rr0 n Y := by
  rw [numS, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  have hadj : ∀ Y', ev0 ((GsM n).adjugate Y Y') =
      (Matrix.diagonal fun Z : Nat.Partition n => ∏ W ∈ Finset.univ.erase Z, D0 W) Y Y' := by
    intro Y'
    have h1 := RingHom.map_adjugate ev0 (GsM n)
    have h2 : ev0 ((GsM n).adjugate Y Y') = (ev0.mapMatrix (GsM n).adjugate) Y Y' := rfl
    rw [h2, h1, RingHom.mapMatrix_apply, hG, Matrix.adjugate_diagonal]
  rw [Finset.sum_eq_single Y]
  · rw [map_mul, hadj, Matrix.diagonal_apply_eq]
    congr 1
    simp only [RsM, Matrix.of_apply]
    rw [← torusWordT_map, ev0_tS, ev0_X, ev0_dS]
    rfl
  · intro Y' _ hne
    rw [map_mul, hadj, Matrix.diagonal_apply_ne _ hne.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ Y) h

theorem ev0_Bden_ne_zero_of (M : ℕ) : ev0 (Bden M) ≠ 0 := by
  rw [Bden, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun j _ => ev0_det_ne_zero_of hG (M - j)

theorem ev0_Anum_of (ν : Fin 2) (M : ℕ) :
    ev0 (Anum ν M) = ∑ j ∈ Finset.range (M + 1), (eta j : ℚ[X]) *
      (∑ Y : Nat.Partition (M - j), (∏ Z ∈ Finset.univ.erase Y, D0 Z) * rr0 (M - j) Y) *
      ∏ i ∈ (Finset.range (M + 1)).erase j, ∏ Y : Nat.Partition (M - i), D0 Y := by
  simp only [Anum, map_sum, map_mul, map_prod, map_intCast, ev0_numS_of hG, ev0_det_of hG]

/-- `P_M^{(ν)}(0,Y) = M! 2^M ∑_s η_s ∑_{Z ⊢ M-s} K_Z⁻¹ Y^{M-ℓ(Z)} ρ̃^{(M-s)}(0,Y)_{Z,Z}`
(paper.tex l.3119–3120). -/
theorem ev0_formula_of {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) :
    ev0 Q = (M.factorial : ℚ[X]) * 2 ^ M * ∑ j ∈ Finset.range (M + 1), (eta j : ℚ[X]) *
      ∑ Y : Nat.Partition (M - j), C (1 / (topNat Y.word Y.word : ℚ)) *
        X ^ (M - Y.word.length) * rr0 (M - j) Y := by
  have k := congrArg ev0 (key_PS h)
  rw [map_mul, map_mul, ev0_prefS, ev0_Anum_of hG] at k
  apply mul_right_cancel₀ (ev0_Bden_ne_zero_of hG M)
  rw [k, Bden, map_prod]
  simp only [ev0_det_of hG]
  rw [mul_assoc ((M.factorial : ℚ[X]) * 2 ^ M), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.mul_prod_erase _ (fun i => ∏ Y : Nat.Partition (M - i), D0 Y) hj]
  have := sumY (M - j) M (Nat.sub_le M j)
  linear_combination ((M.factorial : ℚ[X]) * 2 ^ M * (eta j : ℚ[X]) *
    ∏ i ∈ (Finset.range (M + 1)).erase j, ∏ Y : Nat.Partition (M - i), D0 Y) * this.symm

/-- `P_M^{(ν)}(0,0) = 4^M` (paper.tex l.3121–3123). -/
theorem eval_ev0_of {ν : Fin 2} {M : ℕ} {Q : PS} (h : clearedH ν M = psi Q) :
    (ev0 Q).eval 0 = 4 ^ M := by
  rw [ev0_formula_of hG h]
  simp only [eval_mul, eval_finsetSum, eval_pow, eval_X, eval_C, eval_natCast, eval_intCast,
    eval_ofNat]
  have hin : ∀ j ∈ Finset.range (M + 1),
      ((eta j : ℤ) : ℚ) * ∑ Y : Nat.Partition (M - j), 1 / (topNat Y.word Y.word : ℚ) *
        (0 : ℚ) ^ (M - Y.word.length) * (rr0 (M - j) Y).eval 0 =
      if j = 0 then (4 : ℚ) ^ M / ((M.factorial : ℚ) * 2 ^ M) else 0 := by
    intro j hj
    rw [innerEval (M - j) M (Nat.sub_le M j)]
    have hj' := Finset.mem_range.1 hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, if_pos (Nat.sub_zero M), eta_zero]
      simp
    · rw [if_neg hj0, if_neg (by omega), mul_zero]
  rw [Finset.sum_congr rfl hin, Finset.sum_ite_eq' (Finset.range (M + 1)) 0,
    if_pos (Finset.mem_range.2 (Nat.succ_pos M))]
  have h1 : ((M.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
  field_simp

end Values

/-- `P_M^{(2)}(0,Y) = P_M^{(1)}(0,Y)`: the values at `t = 0` of `F_{M−s}`, hence of `H_M`, do not
depend on `ζ` (Lemma A.1; paper.tex l.3113–3118). -/
theorem ev0_nu_indep_of (h : Stmt_lem_mode_count) {M : ℕ} {Q₀ Q₁ : PS}
    (h0 : clearedH 0 M = psi Q₀) (h1 : clearedH 1 M = psi Q₁) : ev0 Q₁ = ev0 Q₀ := by
  have hN : ∀ n, ev0 (numS 1 n) = ev0 (numS 0 n) := by
    intro n
    simp only [numS, map_sum, map_mul, RsM_ev0_of_modeCount h]
  have hA : ev0 (Anum 1 M) = ev0 (Anum 0 M) := by
    simp only [Anum, map_sum, map_mul, map_intCast, hN]
  have k0 := congrArg ev0 (key_PS h0)
  have k1 := congrArg ev0 (key_PS h1)
  rw [map_mul, map_mul] at k0 k1
  apply mul_right_cancel₀ (ev0_Bden_ne_zero_of (GsM_ev0_of_modeCount h) M)
  rw [k0, k1, hA]

/-- The values of `P_M^{(ν)}` at `t = 0`, from Lemma A.1 (paper.tex l.3113–3123). -/
theorem sub_h13_values_of_modeCount (h : Stmt_lem_mode_count) : Stmt_sub_h13_values := by
  intro P hP ν M _
  have hQ : ∀ ν, clearedH ν M = psi (thetaInv (P ν M)) := by
    intro ν
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  have hth : ∀ ν, P ν M = thetaMv (thetaInv (P ν M)) := fun ν => (thetaMv_thetaInv _).symm
  refine ⟨?_, ?_⟩
  · rw [hth 1, hth 0, aeval0_thetaMv, aeval0_thetaMv]
    exact ev0_nu_indep_of h (hQ 0) (hQ 1)
  · rw [hth ν, eval00_thetaMv]
    exact eval_ev0_of (GsM_ev0_of_modeCount h) (hQ ν)

/-! ### `P_M^{(ν)} ∈ ℚ[t,Y]` in part (i), with the regularity at `t = 0` from Lemma A.1 -/

section Poly

variable (hG : ∀ n : ℕ, (GsM n).map ev0 = Matrix.diagonal fun Y : Nat.Partition n => D0 Y)
include hG

theorem not_tS_dvd_det_of (N : ℕ) : ¬ tS ∣ (GsM N).det := by
  rintro ⟨q, hq⟩
  apply ev0_det_ne_zero_of hG N
  rw [hq, map_mul, ev0_tS, zero_mul]

/-- `F_N = Tr(G̃⁻¹ρ̃)` is regular at `t = 0` (paper.tex l.3113–3116). -/
theorem regT_Frat_of (ν : Fin 2) (N : ℕ) :
    RegT (Frat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N) := by
  refine ⟨numS ν N, (GsM N).det, not_tS_dvd_det_of hG N, ?_⟩
  have hdet : algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
      (gramPoly (cT (RatFunc.X : RatFunc ℚ)) N).det ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)))]
    exact gramPoly_det_ne_zero _ N
  simp only [psi, RingHom.comp_apply]
  rw [psi1_det, psi1_numS, map_mul, map_mul, Frat]
  field_simp

theorem regT_Hrat_of (ν : Fin 2) (N : ℕ) :
    RegT (Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N) := by
  unfold Hrat
  refine Finset.sum_induction _ RegT (fun _ _ => RegT.add) ?_ fun j _ => ?_
  · simpa using RegT.psi 0
  · refine RegT.mul ?_ (regT_Frat_of hG ν (N - j))
    have : ((eta j : ℤ) : RatFunc (RatFunc ℚ)) = psi ((eta j : ℤ) : PS) := by
      rw [map_intCast]
    rw [this]
    exact RegT.psi _

/-- `P_M^{(ν)}` is regular at `t = 0` (paper.tex l.3116–3118). -/
theorem regT_clearedH_of (ν : Fin 2) (M : ℕ) : RegT (clearedH ν M) := by
  rw [clearedH_pref]
  exact RegT.mul (RegT.psi _) (regT_Hrat_of hG ν M)

end Poly

/-- `P_M^{(ν)} ∈ ℚ[t,Y]`: regular at `t = 0` (Lemma A.1) and a Laurent polynomial in `t` by the
Kac determinant formula and Cramer's rule (paper.tex l.3113–3118, l.3125–3129). -/
theorem sub_h13_polynomial_of_modeCount (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (h : Stmt_lem_mode_count) : Stmt_sub_h13_polynomial := by
  have hP : ∀ ν M, ∃ P : PS, clearedH ν M = psi P := by
    intro ν M
    obtain ⟨n, P₀, h0⟩ := laurent_clearedH hK hH ν M
    obtain ⟨A, B, hB, hAB⟩ := regT_clearedH_of (GsM_ev0_of_modeCount h) ν M
    have h1 : P₀ * B = tS ^ n * A := by
      apply psi_injective
      rw [map_mul, map_mul, map_pow, psi_tS, ← h0, ← hAB]
      ring
    have h2 : tS ^ n ∣ P₀ := prime_tS.pow_dvd_of_dvd_mul_right n hB (Dvd.intro _ h1.symm)
    obtain ⟨P, rfl⟩ := h2
    refine ⟨P, ?_⟩
    have hne : RatFunc.C (RatFunc.X : RatFunc ℚ) ^ n ≠ (0 : RatFunc (RatFunc ℚ)) :=
      pow_ne_zero _ ((_root_.map_ne_zero _).2 RatFunc.X_ne_zero)
    apply mul_left_cancel₀ hne
    rw [h0, map_mul, map_pow, psi_tS]
  choose P hP using hP
  exact ⟨fun ν M => thetaMv (P ν M), fun ν M => by rw [aeval_thetaMv, hP]⟩

/-! ### Proposition 9.2 -/

/-- Proposition 9.2 from Lemmas A.1–A.3, as in its proof in the paper (l.1616–1694 and
l.3104–3161): parts (i)–(ii) from the three lemmas, the Kac determinant formula and the
normalizations behind Proposition 6.5; parts (iii)–(iv) from (i)–(ii). -/
theorem prop_h13_nonvanishing_of_appA (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (hA1 : Stmt_lem_mode_count) (hA2 : Stmt_lem_odd_primes)
    (hA3 : Stmt_lem_level_poly) : Stmt_prop_h13_nonvanishing := by
  obtain ⟨P, hP⟩ := sub_h13_polynomial_of_modeCount hK hH hA1
  have hdeg := sub_h13_degree_of_levelPoly hA3
  have hi :
      (∀ ν M, 1 ≤ M →
        (∀ e, ∃ (z : ℤ) (n : ℕ), (P ν M).coeff e = (z : ℚ) / 2 ^ n) ∧
        MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 1 M) =
          MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X]) (P 0 M) ∧
        MvPolynomial.eval (![0, 0] : Fin 2 → ℚ) (P ν M) = 4 ^ M) :=
    fun ν M hM => ⟨sub_h13_integral_of_oddPrimes hA2 P hP ν M hM,
      sub_h13_values_of_modeCount hA1 P hP ν M hM⟩
  exact ⟨P, hP, hi, hdeg P hP, sub_h13_valuation hK P hP hi, sub_h13_lipschitz P hP hi (hdeg P hP)⟩

end Virasoro
