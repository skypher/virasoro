import Virasoro.Proofs.Sec5TopLayerFinal
import Virasoro.Proofs.EvalLemmas
import Virasoro.Sphere.Proofs.Sec5PoleBound
import Virasoro.Sphere.Proofs.Sec2Block
import Virasoro.Sphere.Proofs.Sec4Imported

/-!
# Sphere paper Theorem 5.3: the coefficient of `(Δ-λ)^{-k}` of `ℬ_N`

`sphere/paper.tex` l.1571–1582.  For `ℓ_k ≤ N' ≤ N`, `[x^{-k}] ℬ_{N'}(c⋆,λ+x,Δ_i)` is
`[x^{-k}] G_{N'}⁻¹ = ∑_± (γ^±)⁻¹ U^± G(μ^±)⁻¹ (U^±)ᵀ` (proof of the torus Theorem 5.9) contracted
with the vectors `γ_Y(λ;Δ₄,Δ₃)`, `γ_Z(λ;Δ₁,Δ₂)`, and Lemma 4.2 factors
`∑_Y γ_Y(λ) U_{Y,Z} = π γ_Z(μ)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Verma Polynomial

section Coeff

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem constantCoeff_shift_gammaPoly (a Δa Δb : 𝔽) (N : ℕ) (Y : Nat.Partition N) :
    PowerSeries.constantCoeff (shiftPS a (gammaPoly Δa Δb N Y)) = gammaY a Δa Δb Y.word := by
  rw [constantCoeff_shiftPS, gammaPoly, ← coe_evalRingHom, map_gammaY]
  simp

/-- If `G_N(c,a+x) S(x) = x^k`, then
`[(Δ-a)^{-k}] ℬ_N = ∑ γ_Y(a;Δ₄,Δ₃) S(0)_{Y,Z} γ_Z(a;Δ₁,Δ₂)`. -/
theorem ppCoeff_Bsph_of_scaled (c a : 𝔽) (Δe : Fin 4 → 𝔽) (N k : ℕ)
    (S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries 𝔽))
    (hS : gramLocal c a N * S = (PowerSeries.X : PowerSeries 𝔽) ^ k • 1) :
    ppCoeff (Bsph c Δe N) a k =
      ∑ Y, ∑ Z, gammaY a (Δe 3) (Δe 2) Y.word * PowerSeries.constantCoeff (S Y Z) *
        gammaY a (Δe 0) (Δe 1) Z.word := by
  unfold ppCoeff lcoeff
  rw [expandAt_Bsph_of_scaled c a Δe N k S hS]
  have hX0 : (HahnSeries.single (k : ℤ) (1 : 𝔽) : 𝔽⸨X⸩) ≠ 0 := by
    simp
  obtain ⟨Q, hQ⟩ : ∃ Q : PowerSeries 𝔽, Q = ∑ Y, ∑ Z,
      shiftPS a (gammaPoly (Δe 3) (Δe 2) N Y) * S Y Z *
        shiftPS a (gammaPoly (Δe 0) (Δe 1) N Z) := ⟨_, rfl⟩
  rw [← hQ]
  have h1 : HahnSeries.ofPowerSeries ℤ 𝔽 Q / HahnSeries.single (k : ℤ) (1 : 𝔽) *
      HahnSeries.single (k : ℤ) (1 : 𝔽) = HahnSeries.ofPowerSeries ℤ 𝔽 Q :=
    div_mul_cancel₀ _ hX0
  have h2 := HahnSeries.coeff_mul_single_add
    (x := HahnSeries.ofPowerSeries ℤ 𝔽 Q / HahnSeries.single (k : ℤ) (1 : 𝔽))
    (a := -(k : ℤ)) (b := (k : ℤ)) (r := (1 : 𝔽))
  rw [h1, neg_add_cancel, mul_one] at h2
  rw [← h2]
  have h3 := PowerSeries.coeff_coe (f := Q) 0
  rw [if_neg (by norm_num)] at h3
  have h4 : (HahnSeries.ofPowerSeries ℤ 𝔽 Q).coeff 0 = PowerSeries.constantCoeff Q := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h3
  rw [h4, hQ, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [map_mul, map_mul, constantCoeff_shift_gammaPoly, constantCoeff_shift_gammaPoly]

/-- The value of `ℬ_M` at a point `z` with `det G_M(c,z) ≠ 0`. -/
theorem evalAt_Bsph {c z : 𝔽} (Δe : Fin 4 → 𝔽) {M : ℕ} (h : (gram c z M).det ≠ 0) :
    evalAt z (Bsph c Δe M) =
      ∑ Y, ∑ Z, gammaY z (Δe 3) (Δe 2) Y.word * (gram c z M)⁻¹ Y Z *
        gammaY z (Δe 0) (Δe 1) Z.word := by
  have hG : (gramPoly c M).map (evalRingHom z) = gram c z M := by
    have := gram_map (evalRingHom z) (C c) (X : 𝔽[X]) M
    rw [coe_evalRingHom, eval_C, eval_X] at this
    exact this.symm
  have hadj : ∀ Y Z, ((gramPoly c M).adjugate Y Z).eval z = (gram c z M).adjugate Y Z := by
    intro Y Z
    rw [← hG]
    exact congrFun (congrFun (RingHom.map_adjugate (evalRingHom z) (gramPoly c M)) Y) Z
  have hγ : ∀ (Δa Δb : 𝔽) (Y : Nat.Partition M),
      (gammaPoly Δa Δb M Y).eval z = gammaY z Δa Δb Y.word := by
    intro Δa Δb Y
    rw [gammaPoly, ← coe_evalRingHom, map_gammaY]
    simp
  unfold Bsph
  rw [evalAt_div z _ (by rwa [gramPoly_det_eval]), gramPoly_det_eval, Bnum, eval_finsetSum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [eval_mul, eval_mul, hadj, hγ, hγ, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  field_simp

end Coeff

/-- Over `ℂ(Δ₁,…,Δ₄)`: if `G_N(c,Δ)⁻¹` has pole order at most `k` at `Δ = a`, then
`[(Δ-a)^{-k}] ℬ_N = ∑ γ_Y(a;Δ₄,Δ₃) ([x^{-k}] G_N(c,a+x)⁻¹)_{Y,Z} γ_Z(a;Δ₁,Δ₂)`. -/
theorem ppCoeff_BsphK_top (c a : ℂ) (N k : ℕ) (hp : poleOrderInv (gramLocal c a N) ≤ k) :
    ppCoeff (Bsph (cK c) ΔK N) (cK a) k =
      ∑ Y, ∑ Z, gammaY (cK a) (ΔK 3) (ΔK 2) Y.word *
        cK (invCoeff (gramLocal c a N) (-(k : ℤ)) Y Z) * gammaY (cK a) (ΔK 0) (ΔK 1) Z.word := by
  classical
  have hord : MatOrdGE (invLaurent (gramLocal c a N)) (-(k : ℤ)) := fun i j =>
    (matOrdGE_inv (gramLocal c a N) i j).mono (by
      have : (poleOrderInv (gramLocal c a N) : ℤ) ≤ k := by exact_mod_cast hp
      omega)
  have h0 := mul_scaledInv (gramLocal_det_ne_zero c a N) hord
  have hS : gramLocal (cK c) (cK a) N *
      (scaledInv (gramLocal c a N) k).map (PowerSeries.map (algebraMap ℂ K4)) =
      (PowerSeries.X : PowerSeries K4) ^ k • 1 := by
    rw [gramLocal_K4, ← Matrix.map_mul, h0]
    refine Matrix.ext fun Y Y' => ?_
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.one_apply, smul_eq_mul, smul_eq_mul, map_mul, map_pow, PowerSeries.map_X]
    by_cases hY : Y = Y'
    · rw [if_pos hY, if_pos hY, map_one]
    · rw [if_neg hY, if_neg hY, map_zero]
  have hc : ∀ Y Y', PowerSeries.constantCoeff (scaledInv (gramLocal c a N) k Y Y') =
      invCoeff (gramLocal c a N) (-(k : ℤ)) Y Y' := by
    intro Y Y'
    have := congrFun (congrFun (coeffMat_scaledInv (gramLocal c a N) k 0) Y) Y'
    simpa [coeffMat, PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
  rw [ppCoeff_Bsph_of_scaled _ _ _ _ _ _ hS]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Z _ => ?_
  rw [Matrix.map_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]

section Factor

variable {c h : ℂ}

/-- Base change of the Verma module from `ℂ` to `ℂ(Δ₁,…,Δ₄)`. -/
noncomputable def bcK (c h : ℂ) : Verma ℂ c h →ₛₗ[algebraMap ℂ K4] Verma K4 (cK c) (cK h) :=
  Verma.baseChange (algebraMap ℂ K4) rfl rfl

theorem bcK_negOp (w : List ℕ) (v : Verma ℂ c h) :
    bcK c h (VirEnv.negOp c w • v) = VirEnv.negOp (cK c) w • bcK c h v := by
  induction w with
  | nil => rw [negOp_nil_smul, negOp_nil_smul]
  | cons y w ih =>
    rw [negOp_cons_smul, negOp_cons_smul, bcK, Verma.baseChange_L, ← bcK, ih]

/-- The three-point scalar of a level-`N` vector `v` of `M(c,h)`, with weights in
`ℂ(Δ₁,…,Δ₄)`, in coordinates. -/
theorem threePt_bcK (Δa Δb : K4) {N : ℕ} {v : Verma ℂ c h} (hv : v ∈ level N) :
    threePt (cK c) (cK h) Δa Δb (bcK c h v) =
      ∑ Y, cK (comp N v Y) * gammaY (cK h) Δa Δb Y.word := by
  have hφ := isThreePoint_threePt (cK c) (cK h) Δa Δb
  conv_lhs => rw [← pbwCoord_comp_of_mem_level hv]
  rw [bcK, Verma.baseChange_pbwCoord, pbwCoord_apply, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have := threePoint_negOp hφ hw_mem_level_zero Y.word (posWord_word Y)
  rw [hφ.1, mul_one, Nat.cast_zero, add_zero] at this
  rw [map_smul, smul_eq_mul]
  congr 1

/-- Lemma 4.2 in coordinates: `∑_Y γ_Y(h;Δ_a,Δ_b) U_{Y,Z} = π(Δ_a,Δ_b) γ_Z(h+ℓ;Δ_a,Δ_b)` for
the matrix `U` of the vectors `L_{-Z}χ`, `χ` of level `ℓ` with coordinates `p`. -/
theorem gamma_Umat (Δa Δb : K4) (ℓ M : ℕ) (p : Nat.Partition ℓ → ℂ) (Z : Nat.Partition M) :
    ∑ Y, gammaY (cK h) Δa Δb Y.word *
        cK (Umat (pbwCoord (c := c) (h := h) ℓ p) (ℓ + M) M Y Z) =
      piScalar h p Δa Δb * gammaY (cK (h + (ℓ : ℂ))) Δa Δb Z.word := by
  have hχ : pbwCoord (c := c) (h := h) ℓ p ∈ level ℓ := ⟨p, rfl⟩
  have hl := negOp_smul_mem_level hχ Z.word
  rw [word_sum'] at hl
  have h1 := threePt_bcK Δa Δb hl
  have hχK : bcK c h (pbwCoord ℓ p) ∈ level (c := cK c) (h := cK h) ℓ := by
    rw [bcK, Verma.baseChange_pbwCoord]
    exact ⟨_, rfl⟩
  have h2 := threePoint_negOp (isThreePoint_threePt (cK c) (cK h) Δa Δb) hχK Z.word
    (posWord_word Z)
  have h3 := threePt_bcK Δa Δb hχ
  rw [comp_pbwCoord_same] at h3
  rw [bcK_negOp, h2, h3] at h1
  have e : (cK (h + (ℓ : ℂ)) : K4) = cK h + (ℓ : K4) := by
    show algebraMap ℂ K4 (h + (ℓ : ℂ)) = algebraMap ℂ K4 h + (ℓ : K4)
    rw [map_add, map_natCast]
  rw [e]
  calc ∑ Y, gammaY (cK h) Δa Δb Y.word *
          cK (Umat (pbwCoord (c := c) (h := h) ℓ p) (ℓ + M) M Y Z)
      = ∑ Y, cK (comp (ℓ + M) (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h) ℓ p) Y) *
          gammaY (cK h) Δa Δb Y.word := Finset.sum_congr rfl fun Y _ => mul_comm _ _
    _ = gammaY (cK h + (ℓ : K4)) Δa Δb Z.word * ∑ Y, cK (p Y) * gammaY (cK h) Δa Δb Y.word :=
        h1.symm
    _ = piScalar h p Δa Δb * gammaY (cK h + (ℓ : K4)) Δa Δb Z.word := mul_comm _ _

end Factor

end Virasoro.Sphere
