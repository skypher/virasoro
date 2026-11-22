import Virasoro.Proofs.Sec6LimGr9
import Virasoro.Proofs.Sec6LimGr7

/-!
# Proposition 6.7, the chain limit: `Stmt_sub_layer_chain_limit` (paper.tex l.1135–1148)

For every `N`, the coefficient of `(Δ − λ)^{-k}` of `H_N(c⋆,Δ,d)` is a polynomial `A(d)` with
`[d^n] A = 0` for `n < k`, and `w^k [y^k] T_N(w,y) = [d^k] A + o(1)` as `w → ∞`.

Proof (l.1141–1146).  With `P = ∑ t^i P_i(S,W,Y)` and `D = ∑ t^i D_i(S,W)` the graded numerator and
denominator along `(b⋆ + S t, λ + W t, Y t)`:
* the line `S = 1` (germ computation and Kac): `P_i(1,·,·) = 0` for `i < e`, so `P_i = 0`
  (homogeneity), and `P_e(1, 2b⋆w, 2b⋆y) = T_N(w,y) D_e(1, 2b⋆w)`;
* the line `S = 0`: `[u^a d^n] P(c⋆, λ + u, d) = [W^a Y^n] P_{a+n}`, and
  `D(c⋆, λ + u) = u^e T₁(u)` with `T₁(0) = [W^e] D_e`;
* so `[d^n] A = 0` for `n < k`, `[d^k] A = [W^{e−k} Y^k] P_e / T₁(0)`, and both the numerator
  `w^k [y^k] P_e(1,2b⋆w,·)` and the denominator `D_e(1,2b⋆w)` have degree `e` in `w` with top
  coefficients `(2b⋆)^e [W^{e−k} Y^k] P_e` and `(2b⋆)^e T₁(0)`.
-/

namespace Virasoro.ChainLim

open Polynomial Finset
open scoped LaurentSeries PowerSeries

theorem minimal_facts {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) :
    b ≠ 0 ∧ (p : ℂ) * b ^ 2 + p' = 0 ∧ p ≠ p' ∧ b ^ 2 + 1 ≠ 0 ∧ 0 < p ∧ 0 < p' ∧
      Nat.Coprime p p' := by
  obtain ⟨hp, hp', hcop, -, -, -, -, -, hb⟩ := hset
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'C : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hne : p ≠ p' := by
    intro h
    rw [← h] at hcop
    have := (Nat.coprime_self p).1 hcop
    omega
  refine ⟨?_, ?_, hne, ?_, by omega, by omega, hcop⟩
  · intro h0
    rw [h0, zero_pow two_ne_zero] at hb
    have h2 : -((p' : ℂ) / p) = 0 := by rw [← neg_div]; exact hb.symm
    have : (p' : ℂ) / p = 0 := neg_eq_zero.1 h2
    exact div_ne_zero hp'C hpC this
  · rw [hb]
    field_simp
    ring
  · rw [hb]
    intro h
    have h1 : (p' : ℂ) = p := by
      field_simp at h
      linear_combination -h
    exact hne (Nat.cast_injective h1).symm

/-- The chain limit at a level `N`. -/
theorem chain_limit_N (hrec : GenericRecursionUniform) (hK : Cited_KacDeterminant)
    {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (N k : ℕ) :
    ∃ A : ℂ[X],
      ppCoeff (HN (kacC b) N) (pt (kacH r s b)) k = algebraMap ℂ[X] Kd A ∧
      (∀ n : ℕ, n < k → A.coeff n = 0) ∧
      ∃ e : RatFunc ℂ, VanishesAtInfinity e ∧
        (chainTN p p' r s N).coeff k * RatFunc.X ^ k = RatFunc.C (A.coeff k) + e := by
  obtain ⟨hb0, hrel, hne, hb1, hp0, hp'0, hcop⟩ := minimal_facts hset
  set lam := kacH r s b with hlam
  set e := eRes b lam N with he
  obtain ⟨T₁, hT, hT0⟩ := kac_taylor hK hb0 lam N
  set V₁ : ℂ⟦X⟧ := (T₁ : ℂ⟦X⟧)⁻¹ with hV₁
  set Pc := numP (kacC b) lam N with hPc
  set A : ℂ[X] := if k ≤ e then ∑ x ∈ antidiagonal (e - k),
    Pc.coeff x.1 * C (PowerSeries.coeff x.2 V₁) else 0 with hA
  have hppA := ppCoeff_HN (kacC b) lam N k e T₁ hT hT0
  -- the line `S = 1`
  obtain ⟨hlow, hDe, hval⟩ := transfer (K := KK) hrec hK hp0 hp'0 hne hcop hb0 hrel hb1
    (w := wK) wK_ne yK N
  set Q : ℕ → R3 := fun i => PowerSeries.coeff i (NumG b lam N) with hQ
  set D : ℕ → R3 := fun i => PowerSeries.coeff i (DenG b lam N) with hD
  have hQh : ∀ i, (Q i).IsHomogeneous i := fun i => NumG_mem b lam N i
  have hDh : ∀ i, (D i).IsHomogeneous i := fun i => DenG_mem b lam N i
  have hQ0 : ∀ i < e, Q i = 0 := fun i hi => ev1_KK_injective hb0 (hQh i) (hlow i hi)
  -- the line `S = 0`
  have hsig0N : sig0 (NumG b lam N) = gam Pc := by
    rw [NumG, map_numH, sig0_cR hb0, sig0_DR, sig0_dR, hPc, numP, map_numH, map_add, gam_CC,
      gam_CC, gam_X, gam_CX]
  have hsig0D : sig0 (DenG b lam N) = gam (denH (C (C (kacC b))) (C (C lam) + X) N) := by
    rw [DenG, map_denH, sig0_cR hb0, sig0_DR, map_denH, map_add, gam_CC, gam_CC, gam_X]
  have hcoefP : ∀ a n, (Pc.coeff a).coeff n = (Q (a + n)).coeff (tri 0 a n) := by
    intro a n
    have h1 := coeff_gam Pc (a + n) a n
    rw [if_pos rfl, ← hsig0N, sig0, PowerSeries.coeff_map, coeff_ev0] at h1
    exact h1.symm
  have hP0 : ∀ a n, a + n < e → (Pc.coeff a).coeff n = 0 := by
    intro a n h
    rw [hcoefP, hQ0 _ h, MvPolynomial.coeff_zero]
  have hcoefD : (D e).coeff (tri 0 e 0) = T₁.eval 0 := by
    have h1 := coeff_gam (denH (C (C (kacC b))) (C (C lam) + X) N) e e 0
    rw [if_pos (add_zero e), ← hsig0D, sig0, PowerSeries.coeff_map, coeff_ev0] at h1
    rw [show D e = PowerSeries.coeff e (DenG b lam N) from rfl, h1, denH_shift, hT,
      Polynomial.coeff_map, Polynomial.coeff_C_zero, ← Polynomial.coeff_zero_eq_eval_zero]
    have := Polynomial.coeff_X_pow_mul T₁ e 0
    rw [zero_add] at this
    exact this
  -- the coefficients of `A`
  have hAlow : ∀ n < k, A.coeff n = 0 := by
    intro n hn
    rw [hA]
    split_ifs with hke
    · rw [Polynomial.finset_sum_coeff]
      refine sum_eq_zero fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [Polynomial.coeff_mul_C, hP0 _ _ (by omega), zero_mul]
    · rw [Polynomial.coeff_zero]
  have hAk : A.coeff k = if k ≤ e then (Pc.coeff (e - k)).coeff k * (T₁.eval 0)⁻¹ else 0 := by
    rw [hA]
    split_ifs with hke
    · rw [Polynomial.finset_sum_coeff, sum_eq_single (e - k, 0)]
      · rw [Polynomial.coeff_mul_C, PowerSeries.coeff_zero_eq_constantCoeff_apply, hV₁,
          PowerSeries.constantCoeff_inv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero]
      · intro x hx hx0
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        have hx1 : x.1 < e - k := by
          rcases Nat.lt_or_ge x.1 (e - k) with h | h
          · exact h
          · exfalso
            apply hx0
            ext <;> simp <;> omega
        rw [Polynomial.coeff_mul_C, hP0 _ _ (by omega), zero_mul]
      · intro h
        exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
    · rw [Polynomial.coeff_zero]
  refine ⟨A, hppA, hAlow, ?_⟩
  -- the line `S = 1`, value: `[y^k]`
  set ι := algebraMap ℂ[X] (RatFunc ℂ) with hι
  have hnoY : D e ∈ MvPolynomial.supported ℂ ({0, 1} : Set (Fin 3)) := DenG_mem_noY b lam N e
  set δ : ℂ[X] := (deh b (D e)).coeff 0 with hδ
  have hdehD : deh b (D e) = C δ := deh_noY b hnoY
  set q : ℂ[X] := (deh b (Q e)).coeff k with hq
  have hchain := chainK_eq_chainT hp0 hne hb0 N N (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) RatFunc.X
  have hval' : ev1 b wK yK (Q e) =
      algebraMap (RatFunc ℂ)[X] KK (chainTN p p' r s N) * ev1 b wK yK (D e) := by
    rw [chainTN, ← hchain]
    exact hval
  have hpoly : (deh b (Q e)).map ι = chainTN p p' r s N * C (ι δ) := by
    apply RatFunc.algebraMap_injective (RatFunc ℂ)
    rw [map_mul, ← ev1_KK, hval']
    congr 1
    rw [ev1_KK, hdehD, Polynomial.map_C]
  have hcoef : ι q = (chainTN p p' r s N).coeff k * ι δ := by
    have := congrArg (fun P : (RatFunc ℂ)[X] => P.coeff k) hpoly
    simp only [Polynomial.coeff_map, Polynomial.coeff_mul_C] at this
    exact this
  -- `δ` has degree `e` with top coefficient `(2b⋆)^e T₁(0)`
  have hδdeg : δ.natDegree ≤ e := by
    have := deh_coeff_natDegree_le b (hDh e) 0
    rwa [Nat.sub_zero] at this
  have hδtop : δ.coeff e = T₁.eval 0 * (2 * b) ^ e := by
    have := deh_coeff_top b (hDh e) (Nat.zero_le e)
    rw [Nat.sub_zero, hcoefD] at this
    exact this
  have h2b : (2 * b) ^ e ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hb0)
  have hδ0 : δ ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hδtop
    exact mul_ne_zero hT0 h2b hδtop.symm
  have hιδ : ι δ ≠ 0 := (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).2 hδ0
  -- the remainder
  set R : ℂ[X] := q * X ^ k - C (A.coeff k) * δ with hR
  refine ⟨ι R / ι δ, ?_, ?_⟩
  · by_cases hR0 : R = 0
    · left
      rw [hR0, map_zero, zero_div]
    · right
      have hRdeg : R.natDegree < e := by
        have hle : R.natDegree ≤ e := by
          by_cases hke : k ≤ e
          · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
            · refine natDegree_mul_le.trans ?_
              rw [natDegree_X_pow]
              have : q.natDegree ≤ e - k := deh_coeff_natDegree_le b (hQh e) k
              omega
            · exact natDegree_C_mul_le _ _ |>.trans hδdeg
          · exfalso
            apply hR0
            have hq0 : q = 0 := deh_coeff_eq_zero b (hQh e) (by omega)
            rw [hR, hq0, hAk, if_neg hke]
            simp
        have htop : R.coeff e = 0 := by
          rw [hR, coeff_sub, coeff_C_mul, hδtop, hAk]
          split_ifs with hke
          · have e1 : e = (e - k) + k := by omega
            rw [e1, coeff_mul_X_pow, ← e1, hq, deh_coeff_top b (hQh e) hke, hcoefP,
              Nat.sub_add_cancel hke]
            field_simp
            ring
          · rw [hq, deh_coeff_eq_zero b (hQh e) (by omega), zero_mul, coeff_zero]
            ring
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exfalso
          apply hR0
          have hlc : R.leadingCoeff = 0 := by
            rw [leadingCoeff, h, htop]
          exact leadingCoeff_eq_zero.1 hlc
      have hιR : ι R ≠ 0 := (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).2 hR0
      rw [RatFunc.intDegree_div hιR hιδ, RatFunc.intDegree_polynomial,
        RatFunc.intDegree_polynomial]
      have hδe : δ.natDegree = e := by
        refine le_antisymm hδdeg (le_natDegree_of_ne_zero ?_)
        rw [hδtop]
        exact mul_ne_zero hT0 h2b
      rw [hδe]
      omega
  · have hX : (RatFunc.X : RatFunc ℂ) = ι X := (RatFunc.algebraMap_X).symm
    have hC : RatFunc.C (A.coeff k) = ι (C (A.coeff k)) := (RatFunc.algebraMap_C _).symm
    have hTk : (chainTN p p' r s N).coeff k = ι q / ι δ := by
      rw [hcoef, mul_div_cancel_right₀ _ hιδ]
    rw [hTk, hX, hC, hR, map_sub, map_mul, map_mul, map_pow]
    field_simp
    ring

/-- `Stmt_sub_layer_chain_limit` (paper.tex l.1135–1148). -/
theorem sub_layer_chain_limit (hrec : GenericRecursionUniform) (hK : Cited_KacDeterminant) :
    Stmt_sub_layer_chain_limit := by
  intro p p' r s b hset k _
  exact ⟨chain_limit_N hrec hK hset _ k, chain_limit_N hrec hK hset _ k⟩

end Virasoro.ChainLim
