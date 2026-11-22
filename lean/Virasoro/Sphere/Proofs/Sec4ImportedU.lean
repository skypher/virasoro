import Virasoro.Sphere.Proofs.Sec4Imported

/-!
# Proposition 4.3, second identity, at a regular point of any field

`sphere/paper.tex` l.1255–1263: `⟨χ_{r,s}(b)|Φ_b(1)|Δ_a⟩ = P_{r,s}(b,Δ_a,Δ_b)` is an identity of
rational functions of `b`, polynomial in `Δ_a, Δ_b`; it specializes to every `b₁ ≠ 0` of a field
of characteristic zero at which the coordinates of `χ_{r,s}` are regular.  The proof of
Theorem 4.7 uses it at the germ `b = b⋆ + t` (l.1392–1393).
-/

namespace Virasoro.Sphere

open Polynomial

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

theorem eval_gammaY_bU (h a x : 𝔽) (w : List ℕ) :
    eval x (gammaY (C h) (C a) X w) = gammaY h a x w := by
  have := map_gammaY (evalRingHom x) (C h) (C a) X w
  simpa using this

theorem eval_gammaY_aU (h x bb : 𝔽) (w : List ℕ) :
    eval x (gammaY (C h) X (C bb) w) = gammaY h x bb w := by
  have := map_gammaY (evalRingHom x) (C h) X (C bb) w
  simpa using this

theorem evTo_gammaYU {b : 𝔽} {Δ Δa Δb : RatFunc ℚ} {δ δa δb : 𝔽} (h : EvTo b Δ δ)
    (ha : EvTo b Δa δa) (hb : EvTo b Δb δb) :
    ∀ w : List ℕ, EvTo b (gammaY Δ Δa Δb w) (gammaY δ δa δb w) := by
  intro w
  induction w with
  | nil =>
    simp only [gammaY]
    exact evTo_one
  | cons y w ih =>
    simp only [gammaY]
    exact (((h.add (evTo_natCast w.sum)).add ((evTo_natCast y).mul hb)).sub ha).mul ih

theorem evTo_fusPU {b : 𝔽} (hb0 : b ≠ 0) (r s : ℕ) {Δa Δb : RatFunc ℚ} {δa δb : 𝔽}
    (ha : EvTo b Δa δa) (hb : EvTo b Δb δb) :
    EvTo b (fusP r s RatFunc.X Δa Δb) (fusP r s b δa δb) := by
  have hbi : EvTo b (RatFunc.X + RatFunc.X⁻¹ : RatFunc ℚ) (b + b⁻¹) :=
    evTo_X.add (evTo_X.inv hb0)
  have hA : EvTo b ((RatFunc.X + RatFunc.X⁻¹) ^ 2 - 4 * Δa) ((b + b⁻¹) ^ 2 - 4 * δa) :=
    (hbi.pow 2).sub ((evTo_ofNat 4).mul ha)
  have hB : EvTo b ((RatFunc.X + RatFunc.X⁻¹) ^ 2 - 4 * Δb) ((b + b⁻¹) ^ 2 - 4 * δb) :=
    (hbi.pow 2).sub ((evTo_ofNat 4).mul hb)
  simp only [fusP]
  refine EvTo.mul ?_ (EvTo.prod _ fun x _ => ?_)
  · split_ifs
    · exact (hA.sub hB).div (evTo_ofNat 4) (by norm_num)
    · exact evTo_one
  · have hβ : EvTo b ((x.1 : RatFunc ℚ) * RatFunc.X + (x.2 : RatFunc ℚ) * RatFunc.X⁻¹)
        ((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) :=
      ((evTo_intCast x.1).mul evTo_X).add ((evTo_intCast x.2).mul (evTo_X.inv hb0))
    exact ((((hA.sub hB).add (hβ.pow 2)).pow 2).sub
      (((evTo_ofNat 4).mul hA).mul (hβ.pow 2))).div (evTo_ofNat 16) (by norm_num)

/-- `P_{r,s}(b,Δ_a,Δ_b)` as a polynomial in `Δ_a`. -/
noncomputable def fusPaU (r s : ℕ) (b Δb : 𝔽) : 𝔽[X] :=
  (if (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s then
      C (1 / 4) * (C ((b + b⁻¹) ^ 2) - 4 * X - C ((b + b⁻¹) ^ 2 - 4 * Δb)) else 1) *
    ∏ x ∈ (stepRange r ×ˢ stepRange s).filter fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
      C (1 / 16) * ((C ((b + b⁻¹) ^ 2) - 4 * X - C ((b + b⁻¹) ^ 2 - 4 * Δb)
          + C (((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) ^ 2)) ^ 2
        - 4 * (C ((b + b⁻¹) ^ 2) - 4 * X) * C (((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) ^ 2))

/-- `P_{r,s}(b,Δ_a,Δ_b)` as a polynomial in `Δ_b`. -/
noncomputable def fusPbU (r s : ℕ) (b Δa : 𝔽) : 𝔽[X] :=
  (if (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s then
      C (1 / 4) * (C ((b + b⁻¹) ^ 2 - 4 * Δa) - (C ((b + b⁻¹) ^ 2) - 4 * X)) else 1) *
    ∏ x ∈ (stepRange r ×ˢ stepRange s).filter fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
      C (1 / 16) * ((C ((b + b⁻¹) ^ 2 - 4 * Δa) - (C ((b + b⁻¹) ^ 2) - 4 * X)
          + C (((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) ^ 2)) ^ 2
        - 4 * C ((b + b⁻¹) ^ 2 - 4 * Δa) * C (((x.1 : 𝔽) * b + (x.2 : 𝔽) * b⁻¹) ^ 2))

theorem fusPaU_eval (r s : ℕ) (b Δa Δb : 𝔽) : (fusPaU r s b Δb).eval Δa = fusP r s b Δa Δb := by
  simp only [fusPaU, fusP]
  rw [eval_mul, eval_prod]
  congr 1
  · split_ifs
    · simp
      ring
    · simp
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp
    ring

theorem fusPbU_eval (r s : ℕ) (b Δa Δb : 𝔽) : (fusPbU r s b Δa).eval Δb = fusP r s b Δa Δb := by
  simp only [fusPbU, fusP]
  rw [eval_mul, eval_prod]
  congr 1
  · split_ifs
    · simp
      ring
    · simp
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp
    ring

/-- Two complex polynomials that agree at every rational number are equal. -/
theorem poly_ext_ratU {P Q : 𝔽[X]} (h : ∀ q : ℚ, P.eval (q : 𝔽) = Q.eval (q : 𝔽)) : P = Q := by
  refine eq_of_infinite_eval_eq P Q (Set.Infinite.mono ?_
    (Set.infinite_range_of_injective (Rat.cast_injective (α := 𝔽))))
  rintro _ ⟨q, rfl⟩
  exact h q

/-- The second identity of Proposition 4.3 at a point `b₁ ≠ 0` of a field of characteristic
zero where the coordinates `p` of the normalized singular vector are regular. -/
theorem fus_at (hF : Cited_SphereFusionPolynomial) {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (p : Nat.Partition (r * s) → RatFunc ℚ) (hp1 : p (onesPartition (r * s)) = 1)
    (hps : Verma.IsSingular
      (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
        (r * s) p) (r * s))
    {b₁ : 𝔽} (hb₁ : b₁ ≠ 0)
    (hreg : ∀ Y, Polynomial.eval₂ (algebraMap ℚ 𝔽) b₁ (RatFunc.denom (p Y)) ≠ 0) :
    ∀ Δa Δb : 𝔽,
      ∑ Y, RatFunc.eval (algebraMap ℚ 𝔽) b₁ (p Y) * gammaY (kacH r s b₁) Δa Δb Y.word =
        fusP r s b₁ Δa Δb := by
  have hfus := hF r s hr hs p hp1 hps
  have hQ : ∀ qa qb : ℚ,
      ∑ Y, RatFunc.eval (algebraMap ℚ 𝔽) b₁ (p Y) *
          gammaY (kacH r s b₁) (qa : 𝔽) (qb : 𝔽) Y.word = fusP r s b₁ (qa : 𝔽) (qb : 𝔽) := by
    intro qa qb
    have e1 : EvTo b₁
        (∑ Y, p Y * gammaY (kacH r s (RatFunc.X : RatFunc ℚ)) (RatFunc.C qa) (RatFunc.C qb)
          Y.word)
        (∑ Y, RatFunc.eval (algebraMap ℚ 𝔽) b₁ (p Y) *
          gammaY (kacH r s b₁) (algebraMap ℚ 𝔽 qa) (algebraMap ℚ 𝔽 qb) Y.word) :=
      EvTo.sum _ fun Y _ => EvTo.mul ⟨hreg Y, rfl⟩
        (evTo_gammaYU (evTo_kacH hb₁ r s) (evTo_C qa) (evTo_C qb) Y.word)
    have e2 := evTo_fusPU hb₁ r s (evTo_C (b := b₁) qa) (evTo_C (b := b₁) qb)
    rw [hfus] at e1
    have e3 := e1.unique e2
    simpa only [eq_ratCast] using e3
  have h1 : ∀ (qa : ℚ) (Δb : 𝔽),
      ∑ Y, RatFunc.eval (algebraMap ℚ 𝔽) b₁ (p Y) *
          gammaY (kacH r s b₁) (qa : 𝔽) Δb Y.word = fusP r s b₁ (qa : 𝔽) Δb := by
    intro qa Δb
    have hpoly : (∑ Y : Nat.Partition (r * s), C (RatFunc.eval (algebraMap ℚ 𝔽) b₁ (p Y)) *
        gammaY (C (kacH r s b₁)) (C (qa : 𝔽)) X Y.word : 𝔽[X]) = fusPbU r s b₁ (qa : 𝔽) := by
      refine poly_ext_ratU fun qb => ?_
      rw [fusPbU_eval, ← hQ qa qb, eval_finsetSum]
      exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_bU]
    have h2 := congrArg (eval Δb) hpoly
    rw [fusPbU_eval, eval_finsetSum] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_bU]
  intro Δa Δb
  have hpoly : (∑ Y : Nat.Partition (r * s), C (RatFunc.eval (algebraMap ℚ 𝔽) b₁ (p Y)) *
      gammaY (C (kacH r s b₁)) X (C Δb) Y.word : 𝔽[X]) = fusPaU r s b₁ Δb := by
    refine poly_ext_ratU fun qa => ?_
    rw [fusPaU_eval, ← h1 qa Δb, eval_finsetSum]
    exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_aU]
  have h2 := congrArg (eval Δa) hpoly
  rw [fusPaU_eval, eval_finsetSum] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_aU]

end Virasoro.Sphere
