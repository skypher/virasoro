import Virasoro.Proofs.Generic

/-!
# The residues of `F_N` at generic `b`
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] {hN : NormalizationIdentities} {N : ℕ} {b : 𝔽}

/-- For generic `b`, `G_M(c(b),Δ)` is invertible at every shifted weight `h_a(b) + ℓ_a`. -/
theorem GenericAt.gram_det_shift_ne (hK : Cited_KacDeterminant) (hgen : GenericAt hN N b)
    {a : Label} (ha : a ∈ labels N) {M : ℕ} (hM : M ≤ N) :
    (gram (kacC b) (kacHL a b + (a.lvl : 𝔽)) M).det ≠ 0 := by
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hgen.ne_zero M
  rw [← gramPoly_det_eval, hdet, eval_mul, eval_C, kacProd, eval_prod]
  refine mul_ne_zero hC₀ (Finset.prod_ne_zero_iff.2 fun g hg => ?_)
  rw [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.2 (hgen.shift_ne ha (labels_subset hM hg)))

/-- For generic `b`, the multiplicity of the root `h_a(b)` of the Kac product is `p(M - ℓ_a)`. -/
theorem GenericAt.rootMultiplicity_kacProd (hgen : GenericAt hN N b) {M : ℕ} (hM : M ≤ N)
    {a : Label} (ha : a ∈ labels M) :
    (kacProd b M).rootMultiplicity (kacHL a b) = Fintype.card (Nat.Partition (M - a.lvl)) := by
  classical
  have hne : kacProd b M ≠ 0 := (kacProd_monic b M).ne_zero
  have hsplit : kacProd b M
      = (X - C (kacHL a b)) ^ Fintype.card (Nat.Partition (M - a.lvl))
        * ∏ g ∈ (labels M).erase a,
            (X - C (kacHL g b)) ^ Fintype.card (Nat.Partition (M - g.lvl)) := by
    unfold kacProd
    rw [Finset.mul_prod_erase (labels M)
      (fun g => (X - C (kacHL g b)) ^ Fintype.card (Nat.Partition (M - g.lvl))) ha]
  have hnr : ¬ IsRoot (∏ g ∈ (labels M).erase a,
      (X - C (kacHL g b)) ^ Fintype.card (Nat.Partition (M - g.lvl))) (kacHL a b) := by
    rw [IsRoot, eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun g hg => ?_
    rw [eval_pow, eval_sub, eval_X, eval_C]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h => ?_)
    have hg' := Finset.mem_erase.1 hg
    exact hg'.1 (hgen.kacHL_inj (labels_subset hM hg'.2) (labels_subset hM ha) h.symm)
  rw [hsplit] at hne ⊢
  rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hnr,
    add_zero]

/-- For generic `b`, `ord_x det G_M(c(b), h_a(b) + x) = p(M - ℓ_a)`. -/
theorem GenericAt.gramLocal_det_order (hK : Cited_KacDeterminant) (hgen : GenericAt hN N b)
    {M : ℕ} (hM : M ≤ N) {a : Label} (ha : a ∈ labels M) :
    (gramLocal (kacC b) (kacHL a b) M).det.order
      = ((Fintype.card (Nat.Partition (M - a.lvl)) : ℕ) : ℕ∞) := by
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hgen.ne_zero M
  have hne : C C₀ * kacProd b M ≠ 0 := by
    rw [← hdet]
    exact gramPoly_det_ne_zero _ _
  rw [Virasoro.gramLocal_det_order, hdet, rootMultiplicity_mul hne, rootMultiplicity_C, zero_add,
    hgen.rootMultiplicity_kacProd hM ha]

/-- For generic `b` and a label `a` of level at most `M ≤ N`: `F_M(c(b),Δ,d)` has at most a
simple pole at `Δ = h_a(b)`, with residue `ℛ_a(b,d) F_{M-ℓ_a}(c(b), h_a(b)+ℓ_a, d)`. -/
theorem GenericAt.residue (hK : Cited_KacDeterminant) (hgen : GenericAt hN N b) {M : ℕ}
    (hM : M ≤ N) {a : Label} (ha : a ∈ labels M) (d : 𝔽) :
    poleOrder (Frat (kacC b) d M) (kacHL a b) ≤ 1 ∧
      ppCoeff (Frat (kacC b) d M) (kacHL a b) 1
        = genR a.1 a.2 b d * Fval (kacC b) d (kacHL a b + (a.lvl : 𝔽)) (M - a.lvl) := by
  obtain ⟨ha1, ha2, ha3⟩ := mem_labels.1 ha
  have haN := labels_subset hM ha
  obtain ⟨M', rfl⟩ : ∃ M', M = a.1 * a.2 + M' := Nat.exists_eq_add_of_le ha3
  obtain ⟨hsing, hcross, htor⟩ := normP_spec hN ha1 ha2 hgen.ne_zero (hgen.reg a haN)
  have hsub : a.1 * a.2 + M' - a.lvl = M' := by
    unfold Label.lvl
    omega
  have hβ : crossScalar (kacC b) (kacH (a.1 : ℤ) (a.2 : ℤ) b)
      (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y)) ≠ 0 := by
    rw [hcross]
    exact hgen.cross_ne haN
  have hg := hgen.gram_det_shift_ne hK haN (M := M') (by omega)
  have hord := hgen.gramLocal_det_order hK hM ha
  rw [hsub] at hord
  have hres := residue_Frat (kacC b) (kacHL a b) (a.1 * a.2) M'
    (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y)) d
    (Nat.mul_pos ha1 ha2) hsing hβ hg hord
  refine ⟨hres.1, ?_⟩
  rw [hres.2, hsub]
  have e1 : (torusForm (kacC b) (kacHL a b) d (a.1 * a.2)
      (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y))
      (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y))) = genP a.1 a.2 b d :=
    htor d
  have e2 : crossScalar (kacC b) (kacHL a b)
      (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN a.1 a.2 Y)) = (genA a.1 a.2 b)⁻¹ := by
    rw [genA_inv]
    exact hcross
  rw [e1, e2, div_inv_eq_mul, genR, mul_comm (genP a.1 a.2 b d)]
  rfl

end Virasoro
