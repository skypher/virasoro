import Virasoro.Proofs.ResidueCore3
import Virasoro.Sphere.Proofs.Sec5TopB

/-!
# Sphere paper Proposition 4.4: the residue of `ℬ_m` at a simple Kac root

`sphere/paper.tex` l.1300–1311.  With `χ = P|h⟩` singular of level `ℓ ≥ 1`, `G_M(c,h+ℓ)`
invertible, `β_χ ≠ 0` and `ord_x det G_{ℓ+M}(c,h+x) = p(M)`, the inverse `G_{ℓ+M}⁻¹` has a simple
pole at `h` with residue `ι (β_χ G_M(c,h+ℓ))⁻¹ ιᵀ` (Smith-form residue extraction); contracting
with `γ_Y(h;Δ₄,Δ₃)`, `γ_Z(h;Δ₁,Δ₂)` and factoring `∑_Y γ_Y(h) ι_{Y,Z} = ⟨χ|Φ|·⟩ γ_Z(h+ℓ)`
(Lemma 4.2) gives
`Res_{Δ=h} ℬ_{ℓ+M} = ⟨χ|Φ_{Δ₃}|Δ₄⟩⟨χ|Φ_{Δ₂}|Δ₁⟩/β_χ · ℬ_M(c,h+ℓ,Δ_i)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Verma Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- If `G_N(c,Δ)⁻¹` has pole order at most `k` at `Δ = a`, so has `ℬ_N`, and
`[(Δ-a)^{-k}] ℬ_N = ∑ γ_Y(a;Δ₄,Δ₃) ([x^{-k}] G_N(c,a+x)⁻¹)_{Y,Z} γ_Z(a;Δ₁,Δ₂)`. -/
theorem ppCoeff_Bsph_top (c a : 𝔽) (Δe : Fin 4 → 𝔽) (N k : ℕ)
    (hp : poleOrderInv (gramLocal c a N) ≤ k) :
    poleOrder (Bsph c Δe N) a ≤ k ∧
      ppCoeff (Bsph c Δe N) a k =
        ∑ Y, ∑ Z, gammaY a (Δe 3) (Δe 2) Y.word *
          invCoeff (gramLocal c a N) (-(k : ℤ)) Y Z * gammaY a (Δe 0) (Δe 1) Z.word := by
  classical
  have hord : MatOrdGE (invLaurent (gramLocal c a N)) (-(k : ℤ)) := fun i j =>
    (matOrdGE_inv (gramLocal c a N) i j).mono (by
      have : (poleOrderInv (gramLocal c a N) : ℤ) ≤ k := by exact_mod_cast hp
      omega)
  have hS := mul_scaledInv (gramLocal_det_ne_zero c a N) hord
  have hc : ∀ Y Y', PowerSeries.constantCoeff (scaledInv (gramLocal c a N) k Y Y') =
      invCoeff (gramLocal c a N) (-(k : ℤ)) Y Y' := by
    intro Y Y'
    have := congrFun (congrFun (coeffMat_scaledInv (gramLocal c a N) k 0) Y) Y'
    simpa [coeffMat, PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
  refine ⟨poleOrder_le_of_ordGE (ordGE_expandAt_Bsph c a Δe N k _ hS), ?_⟩
  rw [ppCoeff_Bsph_of_scaled _ _ _ _ _ _ hS]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Z _ => ?_
  rw [hc]

/-- The three-point scalar of a vector with coordinates `u` is `∑_Y u_Y γ_Y(h;Δ_a,Δ_b)`
(Definition 2.1). -/
theorem threePt_pbwCoord (c h Δa Δb : 𝔽) (N : ℕ) (u : Nat.Partition N → 𝔽) :
    threePt c h Δa Δb (pbwCoord (c := c) (h := h) N u) =
      ∑ Y, u Y * gammaY h Δa Δb Y.word := by
  have hφ := isThreePoint_threePt c h Δa Δb
  rw [pbwCoord_apply, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have := threePoint_negOp hφ hw_mem_level_zero Y.word (posWord_word Y)
  rw [hφ.1, mul_one, Nat.cast_zero, add_zero] at this
  rw [map_smul, smul_eq_mul]
  exact congrArg (u Y * ·) this

/-- Lemma 4.2 in coordinates: `∑_Y γ_Y(h;Δ_a,Δ_b) ι_{Y,Z} = ⟨χ|Φ_b|Δ_a⟩ γ_Z(h+ℓ;Δ_a,Δ_b)`. -/
theorem gamma_iotaMat (c h Δa Δb : 𝔽) (ℓ M : ℕ) (p : Nat.Partition ℓ → 𝔽)
    (Z : Nat.Partition M) :
    ∑ Y, gammaY h Δa Δb Y.word * iotaMat c h ℓ M p Y Z =
      (∑ W, p W * gammaY h Δa Δb W.word) * gammaY (h + (ℓ : 𝔽)) Δa Δb Z.word := by
  have h1 := threePt_pbwCoord c h Δa Δb (ℓ + M) (fun Y => iotaMat c h ℓ M p Y Z)
  rw [pbwCoord_iotaMat_col,
    threePoint_negOp (isThreePoint_threePt c h Δa Δb) ⟨p, rfl⟩ Z.word (posWord_word Z),
    threePt_pbwCoord] at h1
  rw [mul_comm, h1]
  exact Finset.sum_congr rfl fun Y _ => mul_comm _ _

omit [CharZero 𝔽] in
theorem sum_sum_eq_dot {m n : Type*} [Fintype m] [Fintype n] (u : m → 𝔽) (B : Matrix m n 𝔽)
    (v : n → 𝔽) : ∑ Y, ∑ Z, u Y * B Y Z * v Z = u ⬝ᵥ (B.mulVec v) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- `Res_{Δ=h} ℬ_{ℓ+M}(c,Δ,Δ_i) = ⟨χ|Φ_{Δ₃}|Δ₄⟩ ⟨χ|Φ_{Δ₂}|Δ₁⟩ / β_χ · ℬ_M(c,h+ℓ,Δ_i)` for a
singular vector `χ` of level `ℓ ≥ 1` in `M(c,h)`, when `G_M(c,h+ℓ)` is invertible, `β_χ ≠ 0` and
`ord_x det G_{ℓ+M}(c,h+x) = p(M)`; the pole is simple. -/
theorem residue_Bsph (c h : 𝔽) (ℓ M : ℕ) (p : Nat.Partition ℓ → 𝔽) (Δe : Fin 4 → 𝔽)
    (hℓ : 1 ≤ ℓ) (hχ : Verma.IsSingular (pbwCoord (c := c) (h := h) ℓ p) ℓ)
    (hβ : crossScalar c h p ≠ 0) (hg : (gram c (h + (ℓ : 𝔽)) M).det ≠ 0)
    (hord : (gramLocal c h (ℓ + M)).det.order
      = ((Fintype.card (Nat.Partition M) : ℕ) : ℕ∞)) :
    poleOrder (Bsph c Δe (ℓ + M)) h ≤ 1 ∧
      ppCoeff (Bsph c Δe (ℓ + M)) h 1 =
        (∑ W, p W * gammaY h (Δe 3) (Δe 2) W.word) *
            (∑ W, p W * gammaY h (Δe 0) (Δe 1) W.word) / crossScalar c h p *
          evalAt (h + (ℓ : 𝔽)) (Bsph c Δe M) := by
  classical
  obtain ⟨hpole, hR⟩ := residue_inverse c h ℓ M p hℓ hχ hβ hg hord
  obtain ⟨h1, h2⟩ := ppCoeff_Bsph_top c h Δe (ℓ + M) 1 hpole
  refine ⟨h1, ?_⟩
  have e1 : (-((1 : ℕ) : ℤ)) = -1 := by norm_num
  rw [e1, hR] at h2
  set g := gram c (h + (ℓ : 𝔽)) M with hgdef
  set β := crossScalar c h p with hβdef
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have hA : (β • g)⁻¹ = β⁻¹ • g⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hβ, one_smul,
      Matrix.mul_nonsing_inv _ hgu]
  have hu : ∀ Δa Δb : 𝔽, Matrix.vecMul (fun Y : Nat.Partition (ℓ + M) => gammaY h Δa Δb Y.word)
      (iotaMat c h ℓ M p) =
      fun Z => (∑ W, p W * gammaY h Δa Δb W.word) * gammaY (h + (ℓ : 𝔽)) Δa Δb Z.word := by
    intro Δa Δb
    funext Z
    rw [← gamma_iotaMat]
    rfl
  rw [h2, sum_sum_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, hu, hu, hA, evalAt_Bsph Δe hg,
    div_eq_mul_inv]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Z _ =>
    Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun W' _ => ?_
  ring

end Virasoro.Sphere
