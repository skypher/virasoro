import Virasoro.Proofs.Sec6H13DegCalc
import Virasoro.Proofs.Sec6H13Values
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.ComputeDegree

/-!
# Proposition 6.8(ii): the normalized product (paper.tex l.1293–1299)

The ring `ℚ[Y,Y⁻¹][[t]]` (`LS`), the coefficient `[t^i Y^j]` (`cf`), the embedding of `ℚ[t][Y]`,
and the normalized product `∏_{u=1}^M (1 + (u−1)/2 · t²/Y + (u²−1)/4 · t³/Y)` (`Nfam`): each
`[t^a Y^{−b}]` of it is a polynomial in `M` of degree at most `2a − 2b` for all `M ≥ 0`
(`Ek_PD`, by Faulhaber's formula and Newton's identities), so multiplying by it preserves the
class `DegFam` of families whose `[t^i Y^j]` is a polynomial in `M` of degree at most `2i + 2j`.
-/

namespace Virasoro.H13D

open Polynomial

/-- `ℚ[Y, Y⁻¹]`. -/
abbrev LQ : Type := LaurentPolynomial ℚ

/-- `ℚ[Y, Y⁻¹][[t]]`. -/
abbrev LS : Type := PowerSeries LQ

/-- `[t^i Y^j] F`. -/
noncomputable def cf (F : LS) (i : ℕ) (j : ℤ) : ℚ := (PowerSeries.coeff i F).coeff j

/-- The constants. -/
noncomputable def cQ : ℚ →+* LS := (PowerSeries.C : LQ →+* LS).comp LaurentPolynomial.C

/-- `ℚ[[t]] → ℚ[Y,Y⁻¹][[t]]`. -/
noncomputable def iT : PowerSeries ℚ →+* LS := PowerSeries.map (LaurentPolynomial.C : ℚ →+* LQ)

/-- `Y^k`, `k ∈ ℤ`. -/
noncomputable def Yp (k : ℤ) : LS := PowerSeries.C (LaurentPolynomial.T k : LQ)

theorem Yp_add (a b : ℤ) : Yp (a + b) = Yp a * Yp b := by
  rw [Yp, LaurentPolynomial.T_add, map_mul]
  rfl

theorem Yp_zero : Yp 0 = 1 := by rw [Yp, LaurentPolynomial.T_zero, map_one]

theorem Yp_pow (k : ℤ) (n : ℕ) : Yp k ^ n = Yp (n * k) := by
  rw [Yp, ← map_pow, LaurentPolynomial.T_pow]
  rfl

theorem lq_coeff_T_mul (k j : ℤ) (p : LQ) :
    (LaurentPolynomial.T k * p).coeff j = p.coeff (j - k) := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  ring

theorem lq_coeff_C_mul (q : ℚ) (j : ℤ) (p : LQ) :
    (LaurentPolynomial.C q * p).coeff j = q * p.coeff j := by
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply]
  simp

theorem cf_zero (i : ℕ) (j : ℤ) : cf 0 i j = 0 := by simp [cf]

theorem cf_add (F G : LS) (i : ℕ) (j : ℤ) : cf (F + G) i j = cf F i j + cf G i j := by
  simp [cf]

theorem cf_sum {ι : Type*} (S : Finset ι) (F : ι → LS) (i : ℕ) (j : ℤ) :
    cf (∑ a ∈ S, F a) i j = ∑ a ∈ S, cf (F a) i j := by
  simp [cf, map_sum, Finsupp.finsetSum_apply]

theorem cf_cQ_mul (q : ℚ) (F : LS) (i : ℕ) (j : ℤ) : cf (cQ q * F) i j = q * cf F i j := by
  rw [cf, cQ, RingHom.comp_apply, PowerSeries.coeff_C_mul, lq_coeff_C_mul]
  rfl

theorem cf_Yp_mul (k : ℤ) (F : LS) (i : ℕ) (j : ℤ) : cf (Yp k * F) i j = cf F i (j - k) := by
  rw [cf, Yp, PowerSeries.coeff_C_mul, lq_coeff_T_mul]
  rfl

theorem cf_iT_mul (g : PowerSeries ℚ) (F : LS) (i : ℕ) (j : ℤ) :
    cf (iT g * F) i j =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, PowerSeries.coeff p.1 g * cf F p.2 j := by
  rw [cf, PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [iT, PowerSeries.coeff_map, lq_coeff_C_mul]
  rfl

theorem cf_of_dvd {F : LS} {n i : ℕ} (h : (PowerSeries.X : LS) ^ n ∣ F) (hi : i < n) (j : ℤ) :
    cf F i j = 0 := by
  rw [cf, PowerSeries.X_pow_dvd_iff.1 h i hi]
  simp

theorem cf_X_pow (n i : ℕ) (k : ℤ) :
    cf ((PowerSeries.X : LS) ^ n) i k = if i = n ∧ k = 0 then 1 else 0 := by
  rw [cf, PowerSeries.coeff_X_pow]
  by_cases h : i = n
  · rw [if_pos h, ← LaurentPolynomial.T_zero, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    by_cases hk : k = 0
    · rw [if_pos hk.symm, if_pos ⟨h, hk⟩]
    · rw [if_neg (Ne.symm hk), if_neg fun hh => hk hh.2]
  · rw [if_neg h, if_neg fun hh => h hh.1]
    simp

/-! ### The embedding of `ℚ[t][Y]` -/

/-- `ℚ[t][Y] → ℚ[Y,Y⁻¹][[t]]`. -/
noncomputable def iM : PS →+* LS :=
  eval₂RingHom (iT.comp (Polynomial.coeToPowerSeries.ringHom)) (Yp 1)

theorem iM_C (p : ℚ[X]) : iM (C p) = iT (p : PowerSeries ℚ) := by simp [iM]

theorem iM_tS : iM tS = PowerSeries.X := by
  rw [tS, iM_C, Polynomial.coe_X, iT, PowerSeries.map_X]

theorem iM_X : iM X = Yp 1 := by simp [iM]

theorem iM_CC (q : ℚ) : iM (C (C q)) = cQ q := by
  rw [iM_C, Polynomial.coe_C, iT, PowerSeries.map_C]
  rfl

theorem cf_iM_thetaInv (P : MvPolynomial (Fin 2) ℚ) (i j : ℕ) :
    cf (iM (thetaInv P)) i j = P.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
    have h1 : thetaInv (MvPolynomial.monomial e a) = C (C a) * (tS ^ e 0 * X ^ e 1) := by
      change (MvPolynomial.aeval (![tS, X] : Fin 2 → PS)) (MvPolynomial.monomial e a) = _
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
        Fin.prod_univ_two]
      rfl
    rw [h1, map_mul, map_mul, map_pow, map_pow, iM_CC, iM_tS, iM_X, Yp_pow, mul_comm _ (Yp _),
      cf_cQ_mul, cf_Yp_mul, cf_X_pow, MvPolynomial.coeff_monomial]
    have hiff : (i = e 0 ∧ (j : ℤ) - ((e 1 : ℕ) : ℤ) * 1 = 0) ↔
        e = Finsupp.single 0 i + Finsupp.single 1 j := by
      constructor
      · rintro ⟨h0, h1'⟩
        ext x
        fin_cases x
        · simp [h0]
        · simp
          omega
      · rintro rfl
        simp
    by_cases he : e = Finsupp.single 0 i + Finsupp.single 1 j
    · rw [if_pos he, if_pos (hiff.2 he), mul_one]
    · rw [if_neg he, if_neg fun hh => he (hiff.1 hh), mul_zero]
  | add p q hp hq => rw [map_add, map_add, cf_add, hp, hq, MvPolynomial.coeff_add]

/-! ### The normalized product (l.1293–1299) -/

/-- `u/2 · t² + ((u+1)²−1)/4 · t³`: the `u+1`-st factor of the normalized product is
`1 + yN(u)/Y`. -/
noncomputable def yNp (u : ℕ) : ℚ[X] :=
  C ((u : ℚ) / 2) * X ^ 2 + C ((((u : ℚ) + 1) ^ 2 - 1) / 4) * X ^ 3

/-- `yNp` as a power series in `t`. -/
noncomputable def yN (u : ℕ) : PowerSeries ℚ := (yNp u : PowerSeries ℚ)

theorem polH_succ (u : ℕ) : polH (u + 1) = -2 * yNp u := by
  apply Polynomial.funext
  intro r
  simp [polH, yNp]
  ring

/-- `∏_{u=1}^M (1 + (u−1)/2 · t²/Y + (u²−1)/4 · t³/Y)`. -/
noncomputable def Nfam (M : ℕ) : LS := ∏ u ∈ Finset.range M, (1 + Yp (-1) * iT (yN u))

theorem Yp_one_mul_neg : Yp 1 * Yp (-1) = 1 := by
  rw [← Yp_add, show (1 : ℤ) + -1 = 0 from rfl, Yp_zero]

theorem iM_pref_factor (u : ℕ) :
    iM (2 * X - C (polH (u + 1))) = cQ 2 * Yp 1 * (1 + Yp (-1) * iT (yN u)) := by
  have h1 : iM (C (polH (u + 1))) = -(cQ 2 * iT (yN u)) := by
    have e1 : ((-2 : ℚ[X]) : PowerSeries ℚ) = PowerSeries.C (-2) := by
      rw [show (-2 : ℚ[X]) = C (-2) by rw [map_neg, map_ofNat], Polynomial.coe_C]
    have e2 : iT (PowerSeries.C (-2)) = cQ (-2) := by
      rw [iT, PowerSeries.map_C]
      rfl
    rw [polH_succ, iM_C, yN, Polynomial.coe_mul, map_mul, e1, e2, map_neg, neg_mul]
  have h3 : iM 2 = cQ 2 := by rw [map_ofNat, map_ofNat]
  rw [map_sub, map_mul, iM_X, h1, h3]
  linear_combination (-(cQ 2 * iT (yN u))) * Yp_one_mul_neg

theorem iM_prefS (M : ℕ) :
    iM (prefS M) = cQ (M.factorial : ℚ) * (cQ 2 * Yp 1) ^ M * Nfam M := by
  have h : ∀ M : ℕ, iM (∏ u ∈ Finset.Icc 1 M, (2 * X - C (polH u))) =
      (cQ 2 * Yp 1) ^ M * Nfam M := by
    intro M
    induction M with
    | zero => simp [Nfam]
    | succ M ih =>
      rw [Finset.prod_Icc_succ_top (by omega), map_mul, ih, iM_pref_factor, Nfam, Nfam,
        Finset.prod_range_succ, pow_succ]
      ring
  rw [prefS, map_mul, h, map_natCast, map_natCast, mul_assoc]

/-- `e_k(yN(0), …, yN(M−1))`. -/
noncomputable def Ek (k M : ℕ) : PowerSeries ℚ :=
  MvPolynomial.aeval (fun u : Fin M => yN u) (MvPolynomial.esymm (Fin M) ℚ k)

theorem Ek_eq (k M : ℕ) :
    Ek k M = ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin M)), ∏ u ∈ t, yN u := by
  simp [Ek, MvPolynomial.esymm, map_sum, map_prod]

theorem Ek_zero_of_lt {k M : ℕ} (h : M < k) : Ek k M = 0 := by
  rw [Ek_eq, Finset.powersetCard_eq_empty.2 (by simpa using h), Finset.sum_empty]

theorem Nfam_eq (M : ℕ) :
    Nfam M = ∑ k ∈ Finset.range (M + 1), Yp (-(k : ℤ)) * iT (Ek k M) := by
  classical
  rw [Nfam, ← Fin.prod_univ_eq_prod_range (fun u => 1 + Yp (-1) * iT (yN u)) M,
    Finset.prod_one_add,
    ← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (M + 1))
      (fun t _ => Finset.mem_range.2 (Nat.lt_succ_of_le
        ((Finset.card_le_univ t).trans (Fintype.card_fin M).le)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.powersetCard_eq_filter, Ek_eq, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2, map_prod,
    Yp_pow]
  congr 2
  ring

theorem yN_PD : PD yN 1 1 := by
  intro n
  have hc : ∀ u : ℕ, PowerSeries.coeff n (yN u) =
      (if n = 2 then (u : ℚ) / 2 else 0) + (if n = 3 then (((u : ℚ) + 1) ^ 2 - 1) / 4 else 0) := by
    intro u
    rw [yN, Polynomial.coeff_coe, yNp, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow,
      coeff_X_pow]
    simp
  by_cases h2 : n = 2
  · subst h2
    refine ⟨C (1 / 2) * X, fun k hk => ?_, fun u => ?_⟩
    · rw [coeff_C_mul, coeff_X, if_neg (by omega), mul_zero]
    · beta_reduce
      rw [hc]
      simp
      ring
  by_cases h3 : n = 3
  · subst h3
    refine ⟨C (1 / 4) * ((X + 1) ^ 2 - 1), fun k hk => ?_, fun u => ?_⟩
    · apply coeff_eq_zero_of_natDegree_lt
      have hd : (C (1 / 4 : ℚ) * ((X + 1) ^ 2 - 1)).natDegree ≤ 2 := by compute_degree
      omega
    · beta_reduce
      rw [hc]
      simp
      ring
  · refine (polyDeg_zero _).congr fun u => ?_
    rw [hc, if_neg h2, if_neg h3, add_zero]

theorem yN_dvd (u : ℕ) : (PowerSeries.X : PowerSeries ℚ) ^ 2 ∣ yN u := by
  refine ⟨((C ((u : ℚ) / 2) + C ((((u : ℚ) + 1) ^ 2 - 1) / 4) * X : ℚ[X]) : PowerSeries ℚ), ?_⟩
  rw [yN, ← Polynomial.coe_X, ← Polynomial.coe_pow, ← Polynomial.coe_mul, yNp]
  congr 1
  ring

/-- `[tⁿ] e_k` is a polynomial in `M` of degree at most `2n − 2k`. -/
theorem Ek_PD (k : ℕ) : PD (Ek k) 2 (2 * k) :=
  PD_esymm yN (fun m hm => PD_psum yN yN_PD yN_dvd m hm) k

/-- `[t^i Y^j] S_M` is a polynomial in `M` of degree at most `2i + 2j`, for all `M ≥ 0`. -/
def DegFam (S : ℕ → LS) : Prop :=
  ∀ (i : ℕ) (j : ℤ), PolyDeg (fun M => cf (S M) i j) (2 * i + 2 * j)

/-- Multiplication by the normalized product preserves `DegFam` (l.1293–1299). -/
theorem DegFam.N_mul {S : ℕ → LS} (hS : DegFam S) : DegFam (fun M => Nfam M * S M) := by
  intro i j
  have key : ∀ M, cf (Nfam M * S M) i j = ∑ k ∈ Finset.range (i + 1),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, PowerSeries.coeff p.1 (Ek k M) * cf (S M) p.2 (j + k) := by
    intro M
    have term : ∀ k : ℕ, cf (Yp (-(k : ℤ)) * iT (Ek k M) * S M) i j =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, PowerSeries.coeff p.1 (Ek k M) * cf (S M) p.2 (j + k) := by
      intro k
      rw [mul_assoc, cf_Yp_mul, cf_iT_mul]
      simp only [sub_neg_eq_add]
    have hz : ∀ k : ℕ, (M < k ∨ i < k) →
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, PowerSeries.coeff p.1 (Ek k M) * cf (S M) p.2 (j + k) = 0 := by
      intro k hk
      refine Finset.sum_eq_zero fun p hp => ?_
      rcases hk with hk | hk
      · rw [Ek_zero_of_lt hk, map_zero, zero_mul]
      · have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        have hz0 : PowerSeries.coeff p.1 (Ek k M) = 0 := (Ek_PD k p.1).eq_zero (by omega) M
        rw [hz0, zero_mul]
    rw [Nfam_eq, Finset.sum_mul, cf_sum]
    simp only [term]
    exact (Finset.sum_subset (Finset.range_mono (show M + 1 ≤ M + 1 + (i + 1) by omega))
        (fun k _ hk => hz k (Or.inl (by simpa using hk)))).trans
      (Finset.sum_subset (Finset.range_mono (show i + 1 ≤ M + 1 + (i + 1) by omega))
        (fun k _ hk => hz k (Or.inr (by simpa using hk)))).symm
  refine PolyDeg.congr ?_ key
  refine PolyDeg.sum _ fun k _ => PolyDeg.sum _ fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  refine ((Ek_PD k p.1).mul (hS p.2 (j + k))).mono (le_of_eq ?_)
  rw [← hp']
  push_cast
  ring

end Virasoro.H13D
