import Virasoro.Proofs.Sec6LimGr8
import Virasoro.Proofs.Sec6Chains

/-!
# Proposition 6.7, the chain limit (c): `K = ℂ(w)(y)`

* `ev1` at `(w, y)` factors through `deh` and the injective maps `ℂ[w][y] → ℂ(w)[y] → ℂ(w)(y)`,
  so it is injective on homogeneous polynomials;
* the chain sum with b-slopes at `(2b⋆w, 2b⋆y)` is the image of `T_N(w,y)` (paper.tex l.1139–1141:
  the b-scaled chain sum is `T_N(W/(2b⋆), Y/(2b⋆))`).
-/

namespace Virasoro.ChainLim

open Polynomial Finset

/-- `K = ℂ(w)(y)`. -/
abbrev KK : Type := RatFunc (RatFunc ℂ)

/-- `w ∈ K`. -/
noncomputable def wK : KK := RatFunc.C RatFunc.X

/-- `y ∈ K`. -/
noncomputable def yK : KK := RatFunc.X

theorem cK_eq (z : ℂ) : algebraMap ℂ KK z = RatFunc.C (RatFunc.C z) := by
  rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ)[X] KK, Polynomial.algebraMap_apply,
    RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

theorem wK_ne (z : ℂ) : wK ≠ algebraMap ℂ KK z := by
  rw [cK_eq, wK]
  intro h
  have h1 := RatFunc.C_injective h
  have h2 : RatFunc.intDegree (RatFunc.X : RatFunc ℂ) = RatFunc.intDegree (RatFunc.C z) := by
    rw [h1]
  rw [RatFunc.intDegree_X, RatFunc.intDegree_C] at h2
  exact one_ne_zero h2

/-- `ev1` at `(w, y)` is `deh` followed by `ℂ[w][y] → ℂ(w)[y] → ℂ(w)(y)`. -/
theorem ev1_KK (bs : ℂ) (Q : R3) : ev1 bs wK yK Q =
    algebraMap (RatFunc ℂ)[X] KK ((deh bs Q).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
  have h : ev1 bs wK yK = (algebraMap (RatFunc ℂ)[X] KK).comp
      ((Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).comp (deh bs)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp only [RingHom.comp_apply, ev1_C, cK_eq, deh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C, Polynomial.algebraMap_apply, coe_mapRingHom, Polynomial.map_C,
        RatFunc.algebraMap_C, algebraMap_eq]
    · have h0 : ev1 bs wK yK (MvPolynomial.X 0) = (algebraMap (RatFunc ℂ)[X] KK)
          ((deh bs (MvPolynomial.X 0)).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
        rw [ev1_X0, deh_apply, MvPolynomial.aeval_X]
        simp [RatFunc.algebraMap_C]
      have h1 : ev1 bs wK yK (MvPolynomial.X 1) = (algebraMap (RatFunc ℂ)[X] KK)
          ((deh bs (MvPolynomial.X 1)).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
        rw [ev1_X1, deh_apply, MvPolynomial.aeval_X, cK_eq, wK]
        change _ = (algebraMap (RatFunc ℂ)[X] KK)
          (Polynomial.map (algebraMap ℂ[X] (RatFunc ℂ)) (C (C (2 * bs) * X)))
        rw [Polynomial.map_C, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
          RatFunc.algebraMap_C, map_mul, map_mul, map_mul, map_ofNat, map_ofNat]
      have h2 : ev1 bs wK yK (MvPolynomial.X 2) = (algebraMap (RatFunc ℂ)[X] KK)
          ((deh bs (MvPolynomial.X 2)).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
        rw [ev1_X2, deh_apply, MvPolynomial.aeval_X, cK_eq, yK]
        change _ = (algebraMap (RatFunc ℂ)[X] KK)
          (Polynomial.map (algebraMap ℂ[X] (RatFunc ℂ)) (C (C (2 * bs)) * X))
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_mul, RatFunc.algebraMap_C,
          RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_mul, map_mul, map_ofNat, map_ofNat]
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
  rw [h]
  rfl

theorem ev1_KK_injective {bs : ℂ} (hbs : bs ≠ 0) {Q : R3} {e : ℕ} (hQ : Q.IsHomogeneous e)
    (h : ev1 bs wK yK Q = 0) : Q = 0 := by
  rw [ev1_KK] at h
  have h1 : (deh bs Q).map (algebraMap ℂ[X] (RatFunc ℂ)) = 0 :=
    RatFunc.algebraMap_injective (RatFunc ℂ) (h.trans (map_zero _).symm)
  have h2 := (Polynomial.map_eq_zero_iff (RatFunc.algebraMap_injective ℂ)).1 h1
  exact deh_injective_hom hbs hQ h2

theorem hdotK_KK (p p' : ℕ) (g : Label) :
    hdotK (K := KK) p p' g = RatFunc.C (RatFunc.C (hdotNu p p' g)) := by
  rw [hdotK_map, cK_eq]
  rfl

theorem inv_mul_cancel_aux {F : Type*} [Field F] (t u ρ y P : F) (ht : t ≠ 0) :
    (t * u)⁻¹ * (ρ * (t * y) * P) = u⁻¹ * (ρ * y * P) := by
  rw [mul_inv]
  calc t⁻¹ * u⁻¹ * (ρ * (t * y) * P) = (t⁻¹ * t) * (u⁻¹ * (ρ * y * P)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ ht, one_mul]

/-- The chain sum with b-slopes at `(2b⋆ζ, 2b⋆y)` is the image of the chain sum `T`. -/
theorem chainK_eq_chainT {p p' : ℕ} (hp0 : 0 < p) (hne : p ≠ p') {bs : ℂ} (hbs : bs ≠ 0) :
    ∀ (fuel M : ℕ) (m2 : ℤ) (ζ : RatFunc ℂ),
      chainK p p' (algebraMap ℂ KK bs) (2 * algebraMap ℂ KK bs * yK) fuel M m2
          (2 * algebraMap ℂ KK bs * RatFunc.C ζ) =
        algebraMap (RatFunc ℂ)[X] KK (chainT p p' fuel M m2 ζ) := by
  set bK := algebraMap ℂ KK bs with hbK
  have hbK0 : bK ≠ 0 := (_root_.map_ne_zero _).2 hbs
  have h2b : (2 * bK) ≠ 0 := by
    rw [hbK, ← map_ofNat (algebraMap ℂ KK) 2, ← map_mul]
    exact (_root_.map_ne_zero _).2 (mul_ne_zero two_ne_zero hbs)
  have hcast : ∀ z : ℂ, RatFunc.C (RatFunc.C z) = algebraMap ℂ KK z := fun z => (cK_eq z).symm
  intro fuel
  induction fuel with
  | zero =>
    intro M m2 ζ
    simp only [chainK, chainT]
    split_ifs <;> simp
  | succ f ih =>
    intro M m2 ζ
    rw [chainK, chainT]
    split_ifs with hM
    · simp
    · rw [map_sum]
      refine sum_congr rfl fun g _ => ?_
      split_ifs with hc
      · have hih := ih (M - g.lvl) (((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2)
          (RatFunc.C (hdotNu p p' g))
        rw [hdotK_KK, map_mul, map_mul, ← hih, RatFunc.algebraMap_C]
        congr 1
        -- the step factor
        set u : KK := RatFunc.C ζ - RatFunc.C (RatFunc.C (hdotNu p p' g)) with hu
        have e1 : 2 * bK * RatFunc.C ζ - 2 * bK * RatFunc.C (RatFunc.C (hdotNu p p' g)) =
            (2 * bK) * u := by rw [hu]; ring
        have e2 : RatFunc.C ((ζ - RatFunc.C (hdotNu p p' g))⁻¹) = u⁻¹ := by
          rw [map_inv₀, map_sub]
        rw [e1, e2]
        have hres : algebraMap (RatFunc ℂ)[X] KK ((resLimit p p' g).map (algebraMap ℂ (RatFunc ℂ)))
            = RatFunc.C (RatFunc.C (rhoG p p' g)) * yK * ∏ j ∈ boxMults p p' g,
                (1 - RatFunc.C (RatFunc.C (((j : ℂ) * kappa0 p p')⁻¹)) * yK) := by
          simp only [resLimit, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
            Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one, map_mul, map_prod,
            map_sub, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X, yK,
            RatFunc.algebraMap_eq_C]
        rw [hres]
        have hprod : ∏ j ∈ boxMults p p' g, (1 - 2 * bK * yK / (2 * bK * (j : KK) * kap p p')) =
            ∏ j ∈ boxMults p p' g, (1 - RatFunc.C (RatFunc.C (((j : ℂ) * kappa0 p p')⁻¹)) * yK) := by
          refine prod_congr rfl fun j hj => ?_
          have hj0 : j ≠ 0 := (mem_filter.1 hj).2.1
          have hk : RatFunc.C (RatFunc.C (((j : ℂ) * kappa0 p p')⁻¹)) =
              ((j : KK) * kap p p')⁻¹ := by
            rw [hcast, map_inv₀, map_mul, map_intCast, kappa0, kap]
            simp only [map_div₀, map_mul, map_sub, map_natCast]
          rw [hk]
          have hj' : (j : KK) ≠ 0 := Int.cast_ne_zero.2 hj0
          field_simp
        have hrho : -((p' : KK) * g.1 - (p : KK) * g.2) / (2 * ((p' : KK) - p)) =
            RatFunc.C (RatFunc.C (rhoG p p' g)) := by
          rw [hcast, rhoG]
          simp only [map_div₀, map_neg, map_sub, map_mul, map_natCast, map_ofNat]
        unfold leadK
        rw [hprod, hrho]
        exact inv_mul_cancel_aux (F := KK) _ _ _ _ _ h2b
      · simp

end Virasoro.ChainLim
