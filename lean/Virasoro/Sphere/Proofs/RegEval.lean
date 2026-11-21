import Virasoro.Sphere.Proofs.Sec5PoleBound
import Virasoro.Sphere.Proofs.FpowLaw
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.Sec4Core2

/-!
# Values at a point of the coefficients of `Φ̃⁻¹`

A rational function is regular at `a` (its Laurent expansion has order `≥ 0`) exactly when its
reduced denominator does not vanish at `a`, and the constant coefficient of the expansion is
its value.  Evaluating the coefficients of `Φ̃(c,Δ,Δ_i;q)⁻¹` at `Δ = a` gives the inverse of the
series `Φ̃(c,a,Δ_i;q)` over the base field, and
`Φ̃(c,a,Δ_i;q)⁻¹ z(q)^ℓ = (16q)^ℓ Φ̃(c,a+ℓ,Δ_i;q)⁻¹` (sphere/paper.tex l.1596–1597).
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

omit [CharZero 𝔽] in
/-- The lowest coefficient of a product with a regular factor. -/
theorem coeff_mul_regVal {f r : 𝔽⸨X⸩} {k : ℤ} {v : 𝔽} (hf : OrdGE f k) (hr : RegVal r v) :
    (f * r).coeff k = f.coeff k * v := by
  have h1 : OrdGE (HahnSeries.single (0 : ℤ) v) 0 :=
    ordGE_iff.2 fun m hm => HahnSeries.coeff_single_of_ne (ne_of_lt hm)
  have h := coeff_mul_congr (A := f) (S := r) (A' := HahnSeries.single k (f.coeff k))
    (S' := HahnSeries.single 0 v) (a := k) (s := 0) (U := k) hf h1
    (fun n hn => by
      rcases lt_or_eq_of_le (show n ≤ k by simpa using hn) with h | h
      · rw [HahnSeries.coeff_single_of_ne (ne_of_lt h), hf.coeff_eq_zero h]
      · rw [h, HahnSeries.coeff_single_same])
    (fun n hn => by
      rcases lt_or_eq_of_le (show n ≤ 0 by simpa using hn) with h | h
      · rw [HahnSeries.coeff_single_of_ne (ne_of_lt h), hr.1.coeff_eq_zero h]
      · rw [h, HahnSeries.coeff_single_same, hr.2]) k le_rfl
  rw [← h, HahnSeries.single_mul_single, add_zero, HahnSeries.coeff_single_same]

theorem expandHom_mul_denom (a : 𝔽) (x : RatFunc 𝔽) :
    expandHom a x * HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a x.denom) =
      HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a x.num) := by
  have hxd : x * algebraMap 𝔽[X] (RatFunc 𝔽) x.denom = algebraMap 𝔽[X] (RatFunc 𝔽) x.num := by
    have h := RatFunc.num_div_denom x
    rw [div_eq_iff ((map_ne_zero_iff _ (RatFunc.algebraMap_injective 𝔽)).2
      (RatFunc.denom_ne_zero x))] at h
    exact h.symm
  have h2 := congrArg (expandHom a) hxd
  rwa [map_mul, expandHom_algebraMap, expandHom_algebraMap] at h2

/-- A rational function whose denominator does not vanish at `a` has a regular expansion at
`a`, with constant coefficient its value. -/
theorem regVal_of_regAt {a : 𝔽} {x : RatFunc 𝔽} (hx : RegAt a x) :
    RegVal (expandHom a x) (evalAt a x) := by
  have hD : PowerSeries.constantCoeff (shiftPS a x.denom) ≠ 0 := by
    rw [constantCoeff_shiftPS]
    exact hx
  have key : expandHom a x =
      HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a x.num * (shiftPS a x.denom)⁻¹) := by
    rw [map_mul, ← expandHom_mul_denom, mul_assoc, ← map_mul, PowerSeries.mul_inv_cancel _ hD,
      map_one, mul_one]
  have hv : PowerSeries.constantCoeff (shiftPS a x.num * (shiftPS a x.denom)⁻¹) =
      evalAt a x := by
    rw [map_mul, PowerSeries.constantCoeff_inv, constantCoeff_shiftPS, constantCoeff_shiftPS]
    simp [evalAt, RatFunc.eval, Polynomial.eval₂_id, div_eq_mul_inv]
  rw [key, ← hv]
  exact regVal_ofPowerSeries _

/-- A rational function with a regular expansion at `a` has nonvanishing denominator at `a`. -/
theorem regAt_of_mem_regRing {a : 𝔽} {x : RatFunc 𝔽} (hx : x ∈ regRing a) : RegAt a x := by
  intro h
  have hx' : RegVal (expandHom a x) ((expandHom a x).coeff 0) := ⟨hx, rfl⟩
  have hm := (hx'.mul (regVal_ofPowerSeries (shiftPS a x.denom))).2
  rw [expandHom_mul_denom, constantCoeff_shiftPS, h, mul_zero,
    (regVal_ofPowerSeries (shiftPS a x.num)).2, constantCoeff_shiftPS] at hm
  obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom x
  have := congrArg (Polynomial.eval a) huv
  rw [eval_add, eval_mul, eval_mul, hm, h, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

theorem regVal_of_mem_regRing {a : 𝔽} {x : RatFunc 𝔽} (hx : x ∈ regRing a) :
    RegVal (expandHom a x) (evalAt a x) :=
  regVal_of_regAt (regAt_of_mem_regRing hx)

/-! ### Evaluation of constants and binomial coefficients -/

omit [CharZero 𝔽] in
theorem regAt_C (a x : 𝔽) : RegAt a (RatFunc.C x) := by
  rw [← RatFunc.algebraMap_C]
  exact regAt_algebraMap a _

omit [CharZero 𝔽] in
theorem evalAt_C (a x : 𝔽) : evalAt a (RatFunc.C x) = x := by
  rw [← RatFunc.algebraMap_C, evalAt_algebraMap, eval_C]

theorem ratCast_eq_C (q : ℚ) : algebraMap ℚ (RatFunc 𝔽) q = RatFunc.C (algebraMap ℚ 𝔽 q) :=
  RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (RatFunc 𝔽))
    ((RatFunc.C : 𝔽 →+* RatFunc 𝔽).comp (algebraMap ℚ 𝔽))) q

theorem regAt_prod_sub {a : 𝔽} {e : RatFunc 𝔽} (he : RegAt a e) (k : ℕ) :
    RegAt a (∏ i ∈ Finset.range k, (e - (i : RatFunc 𝔽))) ∧
      evalAt a (∏ i ∈ Finset.range k, (e - (i : RatFunc 𝔽))) =
        ∏ i ∈ Finset.range k, (evalAt a e - (i : 𝔽)) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty]
    rw [← map_one (RatFunc.C : 𝔽 →+* RatFunc 𝔽)]
    exact ⟨regAt_C a 1, evalAt_C a 1⟩
  | succ k ih =>
    have hk : e - (k : RatFunc 𝔽) = e + RatFunc.C (-(k : 𝔽)) := by
      rw [map_neg, map_natCast, sub_eq_add_neg]
    have h1 : RegAt a (e - (k : RatFunc 𝔽)) := by
      rw [hk]
      exact he.add (regAt_C a _)
    have h2 : evalAt a (e - (k : RatFunc 𝔽)) = evalAt a e - (k : 𝔽) := by
      rw [hk, evalAt_add he (regAt_C a _), evalAt_C, sub_eq_add_neg]
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    exact ⟨ih.1.mul h1, by rw [evalAt_mul ih.1 h1, ih.2, h2]⟩

theorem evalAt_gbinom {a : 𝔽} {e : RatFunc 𝔽} (he : RegAt a e) (k : ℕ) :
    RegAt a (gbinom e k) ∧ evalAt a (gbinom e k) = gbinom (evalAt a e) k := by
  have h : gbinom e k = (∏ i ∈ Finset.range k, (e - (i : RatFunc 𝔽))) *
      RatFunc.C (((k.factorial : ℕ) : 𝔽)⁻¹) := by
    rw [gbinom, div_eq_mul_inv, map_inv₀, map_natCast]
  obtain ⟨h1, h2⟩ := regAt_prod_sub he k
  rw [h]
  exact ⟨h1.mul (regAt_C a _), by
    rw [evalAt_mul h1 (regAt_C a _), h2, evalAt_C, gbinom, div_eq_mul_inv]⟩

/-! ### Coefficientwise evaluation of power series over `𝔽(Δ)` -/

/-- Coefficientwise evaluation at `Δ = a`. -/
noncomputable def evS (a : 𝔽) (f : PowerSeries (RatFunc 𝔽)) : PowerSeries 𝔽 :=
  PowerSeries.mk fun n => evalAt a (PowerSeries.coeff n f)

/-- All coefficients are regular at `a`. -/
def CoeffReg (a : 𝔽) (f : PowerSeries (RatFunc 𝔽)) : Prop :=
  ∀ n, RegAt a (PowerSeries.coeff n f)

theorem CoeffIn.coeffReg {a : 𝔽} {f : PowerSeries (RatFunc 𝔽)} (h : CoeffIn (regRing a) f) :
    CoeffReg a f := fun n => regAt_of_mem_regRing (h n)

omit [CharZero 𝔽] in
theorem evS_mul {a : 𝔽} {f g : PowerSeries (RatFunc 𝔽)} (hf : CoeffReg a f)
    (hg : CoeffReg a g) : evS a (f * g) = evS a f * evS a g := by
  ext n
  simp only [evS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [evalAt_sum fun p _ => (hf p.1).mul (hg p.2)]
  exact Finset.sum_congr rfl fun p _ => evalAt_mul (hf p.1) (hg p.2)

omit [CharZero 𝔽] in
theorem evS_one (a : 𝔽) : evS a (1 : PowerSeries (RatFunc 𝔽)) = 1 := by
  ext n
  simp only [evS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs
  · rw [← map_one (RatFunc.C : 𝔽 →+* RatFunc 𝔽), evalAt_C]
  · rw [← map_zero (RatFunc.C : 𝔽 →+* RatFunc 𝔽), evalAt_C]

/-- Evaluation of a binomial power of a rational series: `(g^e)|_{Δ=a} = g^{e(a)}`. -/
theorem evS_fpow {a : 𝔽} (g : PowerSeries ℚ) {e : RatFunc 𝔽} (he : RegAt a e) :
    evS a (fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g) e) =
      fpow (PowerSeries.map (algebraMap ℚ 𝔽) g) (evalAt a e) := by
  ext n
  have hc : ∀ k, PowerSeries.coeff n ((PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g - 1) ^ k) =
      RatFunc.C (PowerSeries.coeff n ((PowerSeries.map (algebraMap ℚ 𝔽) g - 1) ^ k)) := by
    intro k
    rw [← map_one (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽))), ← map_sub, ← map_pow,
      PowerSeries.coeff_map, ratCast_eq_C,
      ← map_one (PowerSeries.map (algebraMap ℚ 𝔽)), ← map_sub, ← map_pow, PowerSeries.coeff_map]
  simp only [evS, fpow, PowerSeries.coeff_mk, hc]
  rw [evalAt_sum fun k _ => (evalAt_gbinom he k).1.mul (regAt_C a _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [evalAt_mul (evalAt_gbinom he k).1 (regAt_C a _), (evalAt_gbinom he k).2, evalAt_C]

/-! ### The prefactor at a point -/

/-- `Φ̃(c,a,Δ_i;q)` as a power series in `q` over the base field. -/
noncomputable def PhiAt (c a : 𝔽) (Δe : Fin 4 → 𝔽) : PowerSeries 𝔽 :=
  fpow (nomeRatio 𝔽) (a - (c - 1) / 24) *
    fpow (1 - zq 𝔽) ((c - 1) / 24 - Δe 1 - Δe 2) *
    fpow (th3 𝔽) ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3))

theorem constantCoeff_PhiAt (c a : 𝔽) (Δe : Fin 4 → 𝔽) :
    PowerSeries.constantCoeff (PhiAt c a Δe) = 1 := by
  unfold PhiAt
  rw [map_mul, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, fpow_coeff_zero, fpow_coeff_zero,
    fpow_coeff_zero]
  norm_num

theorem evS_PhiTilde (c a : 𝔽) (Δe : Fin 4 → 𝔽) :
    CoeffReg a (PhiTilde c Δe) ∧ evS a (PhiTilde c Δe) = PhiAt c a Δe := by
  have x1 : (RatFunc.X - (RatFunc.C c - 1) / 24 : RatFunc 𝔽) =
      algebraMap 𝔽[X] (RatFunc 𝔽) (X - C ((c - 1) / 24)) := by
    simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, map_div₀, map_ofNat]
  have x2 : ((RatFunc.C c - 1) / 24 - RatFunc.C (Δe 1) - RatFunc.C (Δe 2) : RatFunc 𝔽) =
      RatFunc.C ((c - 1) / 24 - Δe 1 - Δe 2) := by
    simp [map_sub, map_div₀, map_ofNat]
  have x3 : ((RatFunc.C c - 1) / 2 - 4 * RatFunc.C (Δe 0 + Δe 1 + Δe 2 + Δe 3) : RatFunc 𝔽) =
      RatFunc.C ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3)) := by
    simp [map_sub, map_div₀, map_mul, map_add, map_ofNat]
  have r1 : RegAt a (RatFunc.X - (RatFunc.C c - 1) / 24 : RatFunc 𝔽) := by
    rw [x1]
    exact regAt_algebraMap a _
  have v1 : evalAt a (RatFunc.X - (RatFunc.C c - 1) / 24 : RatFunc 𝔽) = a - (c - 1) / 24 := by
    rw [x1, evalAt_algebraMap]
    simp
  have e1 : nomeRatio (RatFunc 𝔽) =
      PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ) := (map_nomeRatio _).symm
  have e2 : (1 - zq (RatFunc 𝔽) : PowerSeries (RatFunc 𝔽)) =
      PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (1 - zq ℚ) := by
    rw [map_sub, map_one, map_zq]
  have e3 : th3 (RatFunc 𝔽) = PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (th3 ℚ) :=
    (map_th3 _).symm
  have f1 : nomeRatio 𝔽 = PowerSeries.map (algebraMap ℚ 𝔽) (nomeRatio ℚ) :=
    (map_nomeRatio _).symm
  have f2 : (1 - zq 𝔽 : PowerSeries 𝔽) = PowerSeries.map (algebraMap ℚ 𝔽) (1 - zq ℚ) := by
    rw [map_sub, map_one, map_zq]
  have f3 : th3 𝔽 = PowerSeries.map (algebraMap ℚ 𝔽) (th3 ℚ) := (map_th3 _).symm
  have c1 := coeffIn_fpow (coeffIn_map_rat a (nomeRatio ℚ)) (mem_regRing.2
    (regVal_of_regAt r1).1)
  have c2 := coeffIn_fpow (coeffIn_map_rat a (1 - zq ℚ)) (mem_regRing.2
    (regVal_of_regAt (regAt_C a ((c - 1) / 24 - Δe 1 - Δe 2))).1)
  have c3 := coeffIn_fpow (coeffIn_map_rat a (th3 ℚ)) (mem_regRing.2
    (regVal_of_regAt (regAt_C a ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3)))).1)
  unfold PhiTilde PhiAt
  rw [e1, e2, e3, x2, x3]
  refine ⟨((c1.mul c2).mul c3).coeffReg, ?_⟩
  rw [evS_mul (c1.mul c2).coeffReg c3.coeffReg,
    evS_mul c1.coeffReg c2.coeffReg, evS_fpow _ r1, evS_fpow _ (regAt_C a _),
    evS_fpow _ (regAt_C a _), v1, evalAt_C, evalAt_C, ← f1, ← f2, ← f3]

theorem evS_PhiTilde_inv (c a : 𝔽) (Δe : Fin 4 → 𝔽) :
    evS a (PhiTilde c Δe)⁻¹ = (PhiAt c a Δe)⁻¹ := by
  have h0 : PowerSeries.constantCoeff (PhiTilde c Δe) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PhiTilde_coeff_zero c Δe
  have hinv := coeffIn_PhiTilde_inv c a Δe
  have hreg : CoeffReg a (PhiTilde c Δe) := (evS_PhiTilde c a Δe).1
  have hm : (PhiTilde c Δe)⁻¹ * PhiTilde c Δe = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [h0]; exact one_ne_zero)
  have h := congrArg (evS a) hm
  rw [evS_mul hinv.coeffReg hreg, evS_one, (evS_PhiTilde c a Δe).2] at h
  exact (PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_PhiAt]; exact one_ne_zero)).2 h

/-- `Φ̃(c,a+ℓ,Δ_i;q) z(q)^ℓ = Φ̃(c,a,Δ_i;q) (16q)^ℓ`. -/
theorem PhiAt_add_nat (c a : 𝔽) (Δe : Fin 4 → 𝔽) (ℓ : ℕ) :
    PhiAt c (a + (ℓ : 𝔽)) Δe * zq 𝔽 ^ ℓ = PhiAt c a Δe * (16 * PowerSeries.X) ^ ℓ := by
  unfold PhiAt
  rw [show a + (ℓ : 𝔽) - (c - 1) / 24 = a - (c - 1) / 24 + (ℓ : 𝔽) by ring,
    fpow_add_nat constantCoeff_nomeRatio, ← nomeRatio_mul_zq, mul_pow]
  ring

/-- `Φ̃(c,a,Δ_i;q)⁻¹ z(q)^ℓ = (16q)^ℓ Φ̃(c,a+ℓ,Δ_i;q)⁻¹` (sphere/paper.tex l.1596–1597). -/
theorem PhiAt_inv_mul_zq_pow (c a : 𝔽) (Δe : Fin 4 → 𝔽) (ℓ : ℕ) :
    (PhiAt c a Δe)⁻¹ * zq 𝔽 ^ ℓ =
      (16 * PowerSeries.X) ^ ℓ * (PhiAt c (a + (ℓ : 𝔽)) Δe)⁻¹ := by
  have h1 : PowerSeries.constantCoeff (PhiAt c a Δe) ≠ 0 := by
    rw [constantCoeff_PhiAt]
    exact one_ne_zero
  have h2 : PowerSeries.constantCoeff (PhiAt c (a + (ℓ : 𝔽)) Δe) ≠ 0 := by
    rw [constantCoeff_PhiAt]
    exact one_ne_zero
  calc (PhiAt c a Δe)⁻¹ * zq 𝔽 ^ ℓ
      = (PhiAt c a Δe)⁻¹ * (PhiAt c (a + (ℓ : 𝔽)) Δe)⁻¹ *
          (PhiAt c (a + (ℓ : 𝔽)) Δe * zq 𝔽 ^ ℓ) := by
        rw [mul_assoc, ← mul_assoc _ (PhiAt c (a + (ℓ : 𝔽)) Δe), PowerSeries.inv_mul_cancel _ h2,
          one_mul]
    _ = (16 * PowerSeries.X) ^ ℓ * (PhiAt c (a + (ℓ : 𝔽)) Δe)⁻¹ *
          ((PhiAt c a Δe)⁻¹ * PhiAt c a Δe) := by
        rw [PhiAt_add_nat]
        ring
    _ = (16 * PowerSeries.X) ^ ℓ * (PhiAt c (a + (ℓ : 𝔽)) Δe)⁻¹ := by
        rw [PowerSeries.inv_mul_cancel _ h1, mul_one]

end Virasoro.Sphere
