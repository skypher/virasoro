import Virasoro.Proofs.Sec6H13Laurent

/-!
# Proposition 6.8(i) of `paper.tex` at 70bac53: `P_M^{(ν)} ∈ ℚ[t,Y]` (l.1224–1261)

`P_M^{(ν)}` is a quotient of polynomials in `(t,Y)` whose denominator does not vanish at `t = 0`
(`regT_clearedH`, l.1232–1252), and a power of `t` times `P_M^{(ν)}` is a polynomial in `(t,Y)`
(`laurent_clearedH`, l.1224–1231 and l.1257–1261); hence `P_M^{(ν)} ∈ ℚ[t,Y]` (l.1261).
-/

namespace Virasoro

open Polynomial

/-- `ℚ[t][Y] → ℚ[t,Y]`, with `t` the variable `0` and `Y` the variable `1`. -/
noncomputable def thetaMv : PS →+* MvPolynomial (Fin 2) ℚ :=
  eval₂RingHom
    ((aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) : ℚ[X] →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) :
      ℚ[X] →+* MvPolynomial (Fin 2) ℚ)
    (MvPolynomial.X 1)

theorem psi_tS : psi tS = RatFunc.C (RatFunc.X : RatFunc ℚ) := by
  simp only [psi, RingHom.comp_apply]
  rw [psi1_tS, RatFunc.algebraMap_C]

theorem aeval_thetaMv (P : PS) :
    MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ))
        (thetaMv P) = psi P := by
  set F : MvPolynomial (Fin 2) ℚ →+* RatFunc (RatFunc ℚ) :=
    ((MvPolynomial.aeval
        (![RatFunc.C (RatFunc.X : RatFunc ℚ),
            RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 * RatFunc.X] : Fin 2 → RatFunc (RatFunc ℚ)) :
      MvPolynomial (Fin 2) ℚ →ₐ[ℚ] RatFunc (RatFunc ℚ)) :
      MvPolynomial (Fin 2) ℚ →+* RatFunc (RatFunc ℚ)) with hF
  have h : F.comp thetaMv = psi := by
    refine Polynomial.ringHom_ext (fun p => ?_) ?_
    · have h2 : (F.comp thetaMv).comp C = psi.comp C := by
        refine Polynomial.ringHom_ext (fun r => ?_) ?_
        · exact RingHom.congr_fun
            (RingHom.ext_rat (((F.comp thetaMv).comp C).comp C) ((psi.comp C).comp C)) r
        · show F (thetaMv (C X)) = psi (C X)
          rw [← tS, psi_tS]
          simp [hF, thetaMv, tS]
      exact RingHom.congr_fun h2 p
    · show F (thetaMv X) = psi X
      simp [hF, thetaMv, psi, psi1_X, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  exact RingHom.congr_fun h P

/-- `P_M^{(ν)}` is a polynomial in `(t, Y)` over `ℚ` (paper.tex l.1261). -/
theorem clearedH_psi (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (ν : Fin 2)
    (M : ℕ) : ∃ P : PS, clearedH ν M = psi P := by
  obtain ⟨n, P₀, h0⟩ := laurent_clearedH hK hH ν M
  obtain ⟨A, B, hB, hAB⟩ := regT_clearedH ν M
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

/-- The first clause of Proposition 6.8: `P_M^{(ν)} ∈ ℚ[t,Y]` (paper.tex l.1181–1183 and
l.1218–1261), from the Kac determinant and the normalization identities behind
Proposition 6.5. -/
theorem sub_h13_polynomial (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_h13_polynomial := by
  choose P hP using fun ν M => clearedH_psi hK hH ν M
  exact ⟨fun ν M => thetaMv (P ν M), fun ν M => by rw [aeval_thetaMv, hP]⟩

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) : Stmt_sub_h13_polynomial :=
  sub_h13_polynomial hK hH

end Virasoro
