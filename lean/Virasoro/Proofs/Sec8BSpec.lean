import Virasoro.Proofs.Sec6LimGr8
import Virasoro.Proofs.Sec4PF

/-!
# The Laurent coefficients of `H_N(c, Δ, d₀)` at a specialized `d₀`

With `P(c, λ + u, d) = 𝒫(u, d) ∈ ℂ[d][u]` and `D(c, λ + u) = u^e T₁(u)`, `T₁(0) ≠ 0`, the
coefficient of `(Δ − λ)^{-k}` of `H_N(c, Δ, d)` over `ℂ(d)` is the image of the polynomial
`∑_{a + j = e − k} 𝒫_a(d) [u^j] T₁⁻¹` (`ChainLim.ppCoeff_HN`); the same computation over `ℂ` with
`d ↦ d₀` shows that the coefficient of `H_N(c, Δ, d₀)` is the value of this polynomial at `d₀`.
This is the sense of "at a specialized `d`" in Theorem 8.11(iii).
-/

namespace Virasoro.ChainLim

open Polynomial Finset
open scoped LaurentSeries PowerSeries

/-- `θ_{d₀} : ℂ[d][u] → ℂ⸨u⸩`, `d ↦ d₀`. -/
noncomputable def thetaAt (d₀ : ℂ) : P2 →+* ℂ⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp
    ((Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (Polynomial.evalRingHom d₀)))

theorem thetaAt_apply (d₀ : ℂ) (f : P2) :
    thetaAt d₀ f =
      HahnSeries.ofPowerSeries ℤ ℂ ((f.map (Polynomial.evalRingHom d₀) : ℂ[X]) : ℂ⟦X⟧) := rfl

theorem thetaAt_CC (d₀ z : ℂ) : thetaAt d₀ (C (C z)) = HahnSeries.C z := by
  rw [thetaAt_apply, Polynomial.map_C, Polynomial.coe_C, HahnSeries.ofPowerSeries_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_C]

theorem thetaAt_X (d₀ : ℂ) : thetaAt d₀ X = HahnSeries.single 1 1 := by
  rw [thetaAt_apply, Polynomial.map_X, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]

theorem thetaAt_CX (d₀ : ℂ) : thetaAt d₀ (C X) = HahnSeries.C d₀ := by
  rw [thetaAt_apply, Polynomial.map_C, Polynomial.coe_C, HahnSeries.ofPowerSeries_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_X]

/-- `H_N(c,Δ,d₀) = P/D` over `ℂ`. -/
theorem Hrat_eq (cs d₀ : ℂ) (N : ℕ) :
    Hrat cs d₀ N = algebraMap ℂ[X] (RatFunc ℂ) (numH (C cs) X (C d₀) N) /
      algebraMap ℂ[X] (RatFunc ℂ) (denH (C cs) X N) := by
  set a := algebraMap ℂ[X] (RatFunc ℂ) with ha
  have hF : ∀ M, Frat cs d₀ M = a (numR (C cs) X (C d₀) M) / a (detR (C cs) X M) := fun M => rfl
  have hD : ∀ M ∈ range (N + 1), a (detR (C cs) X M) ≠ 0 := by
    intro M _
    have e : detR (C cs) X M = (gramPoly cs M).det := rfl
    rw [e]
    exact (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).2 (gramPoly_det_ne_zero _ M)
  have h1 : Hrat cs d₀ N = ∑ j ∈ range (N + 1), (eta j : RatFunc ℂ) *
      (a (numR (C cs) X (C d₀) (N - j)) / a (detR (C cs) X (N - j))) := by
    rw [Hrat]
    exact sum_congr rfl fun j _ => by rw [hF]
  have h2 := sum_eta_div (fun M => a (numR (C cs) X (C d₀) M)) (fun M => a (detR (C cs) X M)) N hD
  rw [h1, h2]
  simp only [numH, denH, map_sum, map_mul, map_prod, map_intCast]

theorem expandAt_Hrat (cs d₀ lam : ℂ) (N : ℕ) :
    expandAt (Hrat cs d₀ N) lam =
      thetaAt d₀ (numP cs lam N) / thetaAt d₀ (denH (C (C cs)) (C (C lam) + X) N) := by
  set φ : ℂ[X] →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (shiftPS lam) with hφ
  have hφa : ∀ f : ℂ[X], expandHom lam (algebraMap ℂ[X] (RatFunc ℂ) f) = φ f :=
    fun f => expandHom_algebraMap _ f
  have hφC : ∀ z : ℂ, φ (C z) = HahnSeries.C z := fun z => by
    rw [hφ, RingHom.comp_apply, shiftPS_C, HahnSeries.ofPowerSeries_C]
  have hφX : φ X = HahnSeries.C lam + HahnSeries.single 1 1 := by
    rw [hφ, RingHom.comp_apply, shiftPS_X, map_add, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X]
  rw [Hrat_eq, expandAt_eq, map_div₀, hφa, hφa, map_numH, map_denH, hφC, hφC, hφX, numP,
    map_numH, map_denH, map_add, thetaAt_CC, thetaAt_CC, thetaAt_X, thetaAt_CX]

theorem map_C_evalRingHom (d₀ : ℂ) (q : ℂ[X]) :
    (q.map (C : ℂ →+* ℂ[X])).map (Polynomial.evalRingHom d₀) = q := by
  ext n
  simp [Polynomial.coeff_map]

/-- The coefficient of `(Δ − λ)^{-k}` in `H_N(c,Δ,d₀)`: the value at `d₀` of the polynomial of
`ChainLim.ppCoeff_HN`. -/
theorem ppCoeff_Hrat (cs d₀ lam : ℂ) (N k e : ℕ) (T₁ : ℂ[X])
    (hT : taylor lam (denH (C cs) X N) = X ^ e * T₁) (hT0 : T₁.eval 0 ≠ 0) :
    ppCoeff (Hrat cs d₀ N) lam k =
      (if k ≤ e then ∑ x ∈ antidiagonal (e - k),
        (numP cs lam N).coeff x.1 * C (PowerSeries.coeff x.2 ((T₁ : ℂ⟦X⟧)⁻¹)) else 0).eval d₀ := by
  set V₁ : ℂ⟦X⟧ := (T₁ : ℂ⟦X⟧)⁻¹ with hV₁
  have hc0 : PowerSeries.constantCoeff (T₁ : ℂ⟦X⟧) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero]
    exact hT0
  have hVT : V₁ * (T₁ : ℂ⟦X⟧) = 1 := by rw [hV₁, PowerSeries.inv_mul_cancel _ hc0]
  set Ph : ℂ⟦X⟧ := (((numP cs lam N).map (Polynomial.evalRingHom d₀) : ℂ[X]) : ℂ⟦X⟧) with hPh
  have hden : thetaAt d₀ (denH (C (C cs)) (C (C lam) + X) N) =
      HahnSeries.single (e : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℂ (T₁ : ℂ⟦X⟧) := by
    rw [denH_shift, hT, thetaAt_apply, map_C_evalRingHom, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, map_mul, HahnSeries.ofPowerSeries_X_pow]
  have hThne : HahnSeries.ofPowerSeries ℤ ℂ (T₁ : ℂ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hVT
    rw [map_mul, h0, mul_zero, map_one] at this
    exact zero_ne_one this
  have hdne : thetaAt d₀ (denH (C (C cs)) (C (C lam) + X) N) ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (by simp [HahnSeries.single_eq_zero_iff]) hThne
  have hquot : expandAt (Hrat cs d₀ N) lam =
      HahnSeries.single (-(e : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℂ (Ph * V₁) := by
    rw [expandAt_Hrat, div_eq_iff hdne, hden]
    have hPhθ : thetaAt d₀ (numP cs lam N) = HahnSeries.ofPowerSeries ℤ ℂ Ph := rfl
    rw [hPhθ]
    calc HahnSeries.ofPowerSeries ℤ ℂ Ph
        = HahnSeries.single (-(e : ℤ) + e) (1 * 1) *
            HahnSeries.ofPowerSeries ℤ ℂ (Ph * (V₁ * (T₁ : ℂ⟦X⟧))) := by
          rw [neg_add_cancel, mul_one, HahnSeries.single_zero_one, one_mul, hVT, mul_one]
      _ = _ := by
          rw [← HahnSeries.single_mul_single, map_mul, map_mul, map_mul]
          ring
  unfold ppCoeff lcoeff
  rw [hquot, coeff_single_neg_mul]
  split_ifs with hk
  · have e1 : -(k : ℤ) + e = ((e - k : ℕ) : ℤ) := by push_cast [hk]; ring
    rw [e1, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mul, Polynomial.eval_finset_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hPh, Polynomial.coeff_coe, Polynomial.coeff_map, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.coe_evalRingHom]
  · rw [Polynomial.eval_zero]
    exact (ordGE_ofPowerSeries _).coeff_eq_zero (by omega)

end Virasoro.ChainLim

namespace Virasoro

/-- No coefficient of `(Δ - a)^{-k}` for `k > D`: the pole order is at most `D`. -/
theorem poleOrder_le_of_ppCoeff {K : Type*} [Field K] {f : RatFunc K} {a : K} {D : ℕ}
    (h : ∀ k : ℕ, D < k → ppCoeff f a k = 0) : poleOrder f a ≤ D := by
  by_contra hc
  push_neg at hc
  have hE : expandAt f a ≠ 0 := by
    intro h0
    unfold poleOrder at hc
    rw [h0] at hc
    simp at hc
  have h2 := Int.lt_toNat.1 hc
  have hm : (expandAt f a).order = -((poleOrder f a : ℕ) : ℤ) := by
    unfold poleOrder
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  apply HahnSeries.coeff_order_eq_zero.not.2 hE
  rw [hm]
  exact h _ hc

/-- At a pole the coefficient of `(Δ - a)^{-poleOrder}` is nonzero. -/
theorem ppCoeff_poleOrder_ne {K : Type*} [Field K] {f : RatFunc K} {a : K}
    (h : 1 ≤ poleOrder f a) : ppCoeff f a (poleOrder f a) ≠ 0 := by
  have hE : expandAt f a ≠ 0 := by
    intro h0
    unfold poleOrder at h
    rw [h0] at h
    simp at h
  have h2 := Int.lt_toNat.1 (show 0 < (-(expandAt f a).order).toNat from h)
  have hm : (expandAt f a).order = -((poleOrder f a : ℕ) : ℤ) := by
    unfold poleOrder
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  intro h0
  apply HahnSeries.coeff_order_eq_zero.not.2 hE
  rw [hm]
  exact h0

end Virasoro
