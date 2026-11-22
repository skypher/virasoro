import Virasoro.Proofs.P2Sec13TauRatio
import Virasoro.Proofs.P2Sec11LayerSum1

/-!
# Lemma 13.1, Step 4: the trace on `𝒱_N` as a rational function of `b` (paper.tex l.2990–2994)

The trace `Tr_{V_{R,S}(b)_N}(V_{d(b)}(1))`, computed in the basis `E` of the free lattice of
Step 2, is `∑ (G_E^{-1})_{ij} ρ_E(e_j,e_i)` with `G_E`, `ρ_E` matrices over `ℂ[b,b⁻¹]`.  It is the
rational function `trRat = trNum / det G_E` of `b`: at generic `b'` its value is the trace, and
its Laurent expansion at `b⋆` is the quotient of the expansions `b ↦ b⋆ + X` of `trNum` and
`det G_E`.
-/

namespace Virasoro.P2

open Virasoro Polynomial

open scoped PowerSeries LaurentSeries

/-- `ℂ[b,b⁻¹] → ℂ(b)`. -/
noncomputable def lamRat : Lam →+* RatFunc ℂ :=
  IsLocalization.Away.lift (X : ℂ[X]) (g := algebraMap ℂ[X] (RatFunc ℂ))
    (isUnit_iff_ne_zero.2 (RatFunc.algebraMap_ne_zero X_ne_zero))

theorem lamRat_algebraMap (q : ℂ[X]) :
    lamRat (algebraMap ℂ[X] Lam q) = algebraMap ℂ[X] (RatFunc ℂ) q :=
  IsLocalization.Away.lift_eq _ _ q

/-- The Laurent expansion at `b ≠ 0` of a Laurent polynomial in `b` is its expansion
`b ↦ b + X`. -/
theorem expand_lamRat {b : ℂ} (hb : b ≠ 0) (a : Lam) :
    expandHom b (lamRat a) = HahnSeries.ofPowerSeries ℤ ℂ (locLam b hb a) := by
  have h : (expandHom b).comp lamRat =
      (HahnSeries.ofPowerSeries ℤ ℂ).comp (locLam b hb) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (X : ℂ[X])) ?_
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp only [RingHom.comp_apply, lamRat_algebraMap, locLam_algebraMap, expandHom_algebraMap,
        eval₂_C, shiftPS_C]
    · simp only [RingHom.comp_apply, lamRat_algebraMap, locLam_algebraMap, expandHom_algebraMap,
        eval₂_X, shiftPS_X, bLoc]
  exact congrArg (fun f : Lam →+* ℂ⸨X⸩ => f a) h

/-- A rational function whose expansion at `a` is a power series is regular at `a`, with value
the constant coefficient. -/
theorem regAt_of_expand {f : RatFunc ℂ} {a : ℂ} {Φ : ℂ⟦X⟧}
    (h : expandHom a f = HahnSeries.ofPowerSeries ℤ ℂ Φ) :
    RegAt a f ∧ evalAt a f = PowerSeries.constantCoeff Φ := by
  refine ⟨?_, (regular_of_expandAt (by rw [expandAt_eq]; exact h)).2⟩
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hs0 : HahnSeries.ofPowerSeries ℤ ℂ (shiftPS a f.denom) ≠ 0 := fun h0 =>
    shiftPS_ne_zero a hden (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [h0, map_zero]))
  have e : shiftPS a f.num = shiftPS a f.denom * Φ := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    have hf : expandHom a f = HahnSeries.ofPowerSeries ℤ ℂ (shiftPS a f.num) /
        HahnSeries.ofPowerSeries ℤ ℂ (shiftPS a f.denom) := by
      conv_lhs => rw [← RatFunc.num_div_denom f]
      rw [map_div₀, expandHom_algebraMap, expandHom_algebraMap]
    rw [map_mul, ← h, hf, mul_div_cancel₀ _ hs0]
  have e0 := congrArg PowerSeries.constantCoeff e
  rw [map_mul, constantCoeff_shiftPS, constantCoeff_shiftPS] at e0
  intro hz
  rw [hz, zero_mul] at e0
  obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom f
  have := congrArg (Polynomial.eval a) huv
  rw [eval_add, eval_mul, eval_mul, e0, hz, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

section Trace

variable {n N : ℕ} (E : Fin n → (Nat.Partition N → ℂ))

/-- The family `E` over `ℂ[b,b⁻¹]`. -/
noncomputable def ELam : Fin n → Nat.Partition N → Lam := fun i Y => algebraMap ℂ[X] Lam (C (E i Y))

/-- `G_E(b)`: the Gram matrix of `E` in `M(c(b),h_{R,S}(b))`. -/
noncomputable def GLam (R S : ℕ) : Matrix (Fin n) (Fin n) Lam :=
  Matrix.of fun i j => gramForm cLam (hLam R S) N (ELam E i) (ELam E j)

/-- `∑ adj(G_E)_{ij} ρ_E(e_j,e_i)`. -/
noncomputable def trNum (R S : ℕ) (u v : ℤ) : Lam :=
  ∑ i, ∑ j, (GLam E R S).adjugate i j * torusForm cLam (hLam R S) (hLam u v) N (ELam E j) (ELam E i)

/-- The trace on `𝒱_N` as a rational function of `b`. -/
noncomputable def trRat (R S : ℕ) (u v : ℤ) : RatFunc ℂ :=
  lamRat (trNum E R S u v) / lamRat (GLam E R S).det

variable {E}

theorem map_GLam {T : Type*} [CommRing T] [Algebra ℚ T] (f : Lam →+* T) {R S : ℕ} {c h : T}
    (hc : f cLam = c) (hh : f (hLam R S) = h) {e : Fin n → Nat.Partition N → T}
    (he : ∀ i Y, f (ELam E i Y) = e i Y) :
    f.mapMatrix (GLam E R S) = Matrix.of fun i j => gramForm c h N (e i) (e j) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, GLam, Matrix.of_apply, map_gramForm, hc,
    hh, he]

theorem map_trNum {T : Type*} [CommRing T] [Algebra ℚ T] (f : Lam →+* T) {R S : ℕ} {u v : ℤ}
    {c h d : T} (hc : f cLam = c) (hh : f (hLam R S) = h) (hd : f (hLam u v) = d)
    {e : Fin n → Nat.Partition N → T} (he : ∀ i Y, f (ELam E i Y) = e i Y) :
    f (trNum E R S u v) = ∑ i, ∑ j, (Matrix.of fun i j => gramForm c h N (e i) (e j)).adjugate i j *
      torusForm c h d N (e j) (e i) := by
  rw [trNum, map_sum, ← map_GLam f hc hh he, ← RingHom.map_adjugate]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_torusForm, hc, hh, hd]
  simp only [he, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem evLam_ELam {b : ℂ} (hb : b ≠ 0) (i : Fin n) (Y : Nat.Partition N) :
    evLam b hb (ELam E i Y) = E i Y := by
  rw [ELam, evLam_algebraMap, eval_C]

theorem locLam_ELam {b : ℂ} (hb : b ≠ 0) (i : Fin n) (Y : Nat.Partition N) :
    locLam b hb (ELam E i Y) = PowerSeries.C (E i Y) := by
  rw [ELam, locLam_algebraMap, eval₂_C]

/-- The Laurent expansion of `trRat` at `b ≠ 0`. -/
theorem expand_trRat {b : ℂ} (hb : b ≠ 0) (R S : ℕ) (u v : ℤ) :
    expandHom b (trRat E R S u v) =
      HahnSeries.ofPowerSeries ℤ ℂ (locLam b hb (trNum E R S u v)) /
        HahnSeries.ofPowerSeries ℤ ℂ (locLam b hb (GLam E R S).det) := by
  rw [trRat, map_div₀, expand_lamRat hb, expand_lamRat hb]

/-- At `b' ≠ 0` with `det G_E(b') ≠ 0`, `trRat` is regular with value the trace computed in the
basis `E`. -/
theorem trRat_generic {b : ℂ} (hb : b ≠ 0) (R S : ℕ) (u v : ℤ)
    (hdet : (Matrix.of fun i j => gramForm (kacC b) (kacH R S b) N (E i) (E j)).det ≠ 0) :
    RegAt b (trRat E R S u v) ∧
      evalAt b (trRat E R S u v) =
        ∑ i, ∑ j, (Matrix.of fun i j => gramForm (kacC b) (kacH R S b) N (E i) (E j))⁻¹ i j *
          torusForm (kacC b) (kacH R S b) (kacH u v b) N (E j) (E i) := by
  have hG := map_GLam (E := E) (e := E) (evLam b hb) (evLam_cLam hb) (evLam_hLam hb R S)
    (evLam_ELam hb)
  have hT := map_trNum (E := E) (e := E) (evLam b hb) (evLam_cLam hb) (evLam_hLam hb R S)
    (evLam_hLam hb u v) (evLam_ELam hb)
  have hD : evLam b hb (GLam E R S).det =
      (Matrix.of fun i j => gramForm (kacC b) (kacH R S b) N (E i) (E j)).det := by
    rw [RingHom.map_det, hG]
  have hunit : IsUnit (locLam b hb (GLam E R S).det) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_locLam, hD]
    exact isUnit_iff_ne_zero.2 hdet
  have hexp : expandHom b (trRat E R S u v) = HahnSeries.ofPowerSeries ℤ ℂ
      (locLam b hb (trNum E R S u v) * (locLam b hb (GLam E R S).det)⁻¹) := by
    have hne : HahnSeries.ofPowerSeries ℤ ℂ (locLam b hb (GLam E R S).det) ≠ 0 := by
      intro h0
      apply hunit.ne_zero
      exact HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [h0, map_zero])
    rw [expand_trRat hb, div_eq_iff hne, ← map_mul, mul_assoc,
      PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_locLam, hD]; exact hdet), mul_one]
  obtain ⟨hreg, hval⟩ := regAt_of_expand hexp
  refine ⟨hreg, ?_⟩
  rw [hval, map_mul, PowerSeries.constantCoeff_inv, constantCoeff_locLam, constantCoeff_locLam, hT,
    hD, Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Trace

end Virasoro.P2
