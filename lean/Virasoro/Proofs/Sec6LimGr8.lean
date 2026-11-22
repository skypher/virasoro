import Virasoro.Proofs.Sec6LimGr6
import Virasoro.Proofs.Expand
import Virasoro.Proofs.SubringCoeff
import Virasoro.Proofs.Sec6DDeriv
import Virasoro.Proofs.SmithBasic

/-!
# Proposition 6.7, the chain limit (b): the Laurent coefficients of `H_N(c⋆,Δ,d)` at `λ`

With `P(c⋆, λ + u, d) = 𝒫(u, d) ∈ ℂ[d][u]` and `D(c⋆, λ + u) = u^e T₁(u)`, `T₁(0) ≠ 0`, the
coefficient of `(Δ − λ)^{-k}` is `∑_{a + j = e − k} 𝒫_a(d) [u^j] T₁⁻¹`, a polynomial in `d`
(paper.tex l.1141–1146).
-/

namespace Virasoro.ChainLim

open Polynomial Finset
open scoped LaurentSeries PowerSeries

/-- `𝒫 = P(c⋆, λ + u, d) ∈ ℂ[d][u]`. -/
noncomputable def numP (cs lam : ℂ) (N : ℕ) : P2 := numH (C (C cs)) (C (C lam) + X) (C X) N

/-- `θ : ℂ[d][u] → ℂ(d)⸨u⸩`. -/
noncomputable def theta : P2 →+* Kd⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ Kd).comp
    ((Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom (algebraMap ℂ[X] Kd)))

theorem theta_apply (f : P2) :
    theta f = HahnSeries.ofPowerSeries ℤ Kd ((f.map (algebraMap ℂ[X] Kd) : Kd[X]) : Kd⟦X⟧) := rfl

theorem theta_CC (z : ℂ) : theta (C (C z)) = HahnSeries.C (RatFunc.C z) := by
  rw [theta_apply, Polynomial.map_C, Polynomial.coe_C, HahnSeries.ofPowerSeries_C,
    RatFunc.algebraMap_C]

theorem theta_X : theta X = HahnSeries.single 1 1 := by
  rw [theta_apply, Polynomial.map_X, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]

theorem theta_CX : theta (C X) = HahnSeries.C dvar := by
  rw [theta_apply, Polynomial.map_C, Polynomial.coe_C, HahnSeries.ofPowerSeries_C,
    RatFunc.algebraMap_X]

/-- `∑_j η_j n_{N−j}/D_{N−j}` over the common denominator `∏_{M ≤ N} D_M`. -/
theorem sum_eta_div {F : Type*} [Field F] (n D : ℕ → F) (N : ℕ)
    (hD : ∀ M ∈ range (N + 1), D M ≠ 0) :
    ∑ j ∈ range (N + 1), (eta j : F) * (n (N - j) / D (N - j)) =
      (∑ j ∈ range (N + 1), (eta j : F) * n (N - j) *
        ∏ M ∈ (range (N + 1)).erase (N - j), D M) / ∏ M ∈ range (N + 1), D M := by
  have hDen : ∏ M ∈ range (N + 1), D M ≠ 0 := prod_ne_zero_iff.2 hD
  rw [eq_div_iff hDen, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hmem : N - j ∈ range (N + 1) := mem_range.2 (by omega)
  have hd := hD _ hmem
  rw [← mul_prod_erase _ _ hmem]
  field_simp

/-- `H_N(c⋆,Δ,d) = P/D` over `ℂ(d)`. -/
theorem HN_eq (cs : ℂ) (N : ℕ) :
    HN cs N = algebraMap Kd[X] (RatFunc Kd) (numH (C (RatFunc.C cs)) X (C dvar) N) /
      algebraMap Kd[X] (RatFunc Kd) (denH (C (RatFunc.C cs)) X N) := by
  set a := algebraMap Kd[X] (RatFunc Kd) with ha
  have hF : ∀ M, Frat (RatFunc.C cs) dvar M =
      a (numR (C (RatFunc.C cs)) X (C dvar) M) / a (detR (C (RatFunc.C cs)) X M) := fun M => rfl
  have hD : ∀ M ∈ range (N + 1), a (detR (C (RatFunc.C cs)) X M) ≠ 0 := by
    intro M _
    have e : detR (C (RatFunc.C cs : Kd)) X M = (gramPoly (RatFunc.C cs : Kd) M).det := rfl
    rw [e]
    exact (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective Kd)).2
      (gramPoly_det_ne_zero _ M)
  have h1 : HN cs N = ∑ j ∈ range (N + 1), (eta j : RatFunc Kd) *
      (a (numR (C (RatFunc.C cs)) X (C dvar) (N - j)) / a (detR (C (RatFunc.C cs)) X (N - j))) := by
    rw [HN, Hrat]
    exact sum_congr rfl fun j _ => by rw [hF]
  have h2 := sum_eta_div (fun M => a (numR (C (RatFunc.C cs)) X (C dvar) M))
    (fun M => a (detR (C (RatFunc.C cs)) X M)) N hD
  rw [h1, h2]
  simp only [numH, denH, map_sum, map_mul, map_prod, map_intCast]

theorem expandAt_HN (cs lam : ℂ) (N : ℕ) :
    expandAt (HN cs N) (pt lam) =
      theta (numP cs lam N) / theta (denH (C (C cs)) (C (C lam) + X) N) := by
  set φ : Kd[X] →+* Kd⸨X⸩ := (HahnSeries.ofPowerSeries ℤ Kd).comp (shiftPS (pt lam)) with hφ
  have hφa : ∀ f : Kd[X], expandHom (pt lam) (algebraMap Kd[X] (RatFunc Kd) f) = φ f :=
    fun f => expandHom_algebraMap _ f
  have hφC : ∀ z : Kd, φ (C z) = HahnSeries.C z := fun z => by
    rw [hφ, RingHom.comp_apply, shiftPS_C, HahnSeries.ofPowerSeries_C]
  have hφX : φ X = HahnSeries.C (pt lam) + HahnSeries.single 1 1 := by
    rw [hφ, RingHom.comp_apply, shiftPS_X, map_add, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X]
  rw [HN_eq, expandAt_eq, map_div₀, hφa, hφa, map_numH, map_denH, hφC, hφC, hφX, numP,
    map_numH, map_denH, map_add, theta_CC, theta_CC, theta_X, theta_CX]

/-- `D(c⋆, λ + u) = D♮(λ + u)` with constants in `d`. -/
theorem denH_shift (cs lam : ℂ) (N : ℕ) :
    denH (C (C cs)) (C (C lam) + X) N = (taylor lam (denH (C cs) X N)).map C := by
  let ψ : ℂ[X] →+* P2 := (Polynomial.mapRingHom C).comp (taylorAlgHom lam).toRingHom
  have h := map_denH ψ (C cs) X N
  have e1 : ψ (C cs) = C (C cs) := by simp [ψ]
  have e2 : ψ X = C (C lam) + X := by simp [ψ, add_comm]
  rw [e1, e2] at h
  rw [← h]
  rfl

theorem theta_map_C (q : ℂ[X]) :
    theta (q.map C) = HahnSeries.ofPowerSeries ℤ Kd ((q.map RatFunc.C : Kd[X]) : Kd⟦X⟧) := by
  rw [theta_apply, Polynomial.map_map]
  congr 3

theorem coe_map_RC (q : ℂ[X]) :
    ((q.map RatFunc.C : Kd[X]) : Kd⟦X⟧) = PowerSeries.map RatFunc.C (q : ℂ⟦X⟧) := by
  ext n
  simp [Polynomial.coeff_coe, Polynomial.coeff_map]

/-- The coefficient of `(Δ − λ)^{-k}` in `H_N(c⋆,Δ,d)`. -/
theorem ppCoeff_HN (cs lam : ℂ) (N k e : ℕ) (T₁ : ℂ[X])
    (hT : taylor lam (denH (C cs) X N) = X ^ e * T₁) (hT0 : T₁.eval 0 ≠ 0) :
    ppCoeff (HN cs N) (pt lam) k = algebraMap ℂ[X] Kd
      (if k ≤ e then ∑ x ∈ antidiagonal (e - k),
        (numP cs lam N).coeff x.1 * C (PowerSeries.coeff x.2 ((T₁ : ℂ⟦X⟧)⁻¹)) else 0) := by
  set V₁ : ℂ⟦X⟧ := (T₁ : ℂ⟦X⟧)⁻¹ with hV₁
  have hc0 : PowerSeries.constantCoeff (T₁ : ℂ⟦X⟧) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero]
    exact hT0
  set Th : Kd⟦X⟧ := ((T₁.map RatFunc.C : Kd[X]) : Kd⟦X⟧) with hTh
  set Vh : Kd⟦X⟧ := PowerSeries.map RatFunc.C V₁ with hVh
  have hVT : Vh * Th = 1 := by
    rw [hVh, hTh, coe_map_RC, ← map_mul, hV₁, PowerSeries.inv_mul_cancel _ hc0, map_one]
  set Ph : Kd⟦X⟧ := (((numP cs lam N).map (algebraMap ℂ[X] Kd) : Kd[X]) : Kd⟦X⟧) with hPh
  have hden : theta (denH (C (C cs)) (C (C lam) + X) N) =
      HahnSeries.single (e : ℤ) 1 * HahnSeries.ofPowerSeries ℤ Kd Th := by
    rw [denH_shift, hT, theta_map_C, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, map_mul,
      HahnSeries.ofPowerSeries_X_pow]
  have hThne : HahnSeries.ofPowerSeries ℤ Kd Th ≠ 0 := by
    intro h0
    have := congrArg (HahnSeries.ofPowerSeries ℤ Kd) hVT
    rw [map_mul, h0, mul_zero, map_one] at this
    exact zero_ne_one this
  have hdne : theta (denH (C (C cs)) (C (C lam) + X) N) ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (by simp [HahnSeries.single_eq_zero_iff]) hThne
  have hquot : expandAt (HN cs N) (pt lam) =
      HahnSeries.single (-(e : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ Kd (Ph * Vh) := by
    rw [expandAt_HN, div_eq_iff hdne, hden]
    have hPhθ : theta (numP cs lam N) = HahnSeries.ofPowerSeries ℤ Kd Ph := rfl
    rw [hPhθ]
    calc HahnSeries.ofPowerSeries ℤ Kd Ph
        = HahnSeries.single (-(e : ℤ) + e) (1 * 1) *
            HahnSeries.ofPowerSeries ℤ Kd (Ph * (Vh * Th)) := by
          rw [neg_add_cancel, mul_one, HahnSeries.single_zero_one, one_mul, hVT, mul_one]
      _ = _ := by
          rw [← HahnSeries.single_mul_single, map_mul, map_mul, map_mul]
          ring
  unfold ppCoeff lcoeff
  rw [hquot, coeff_single_neg_mul]
  split_ifs with hk
  · have e1 : -(k : ℤ) + e = ((e - k : ℕ) : ℤ) := by push_cast [hk]; ring
    rw [e1, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mul, map_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hPh, hVh, Polynomial.coeff_coe, Polynomial.coeff_map, PowerSeries.coeff_map, map_mul,
      RatFunc.algebraMap_C]
  · rw [map_zero]
    exact (ordGE_ofPowerSeries _).coeff_eq_zero (by omega)

end Virasoro.ChainLim
