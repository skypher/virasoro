import Virasoro.Sphere.Cited
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.RegEval
import Virasoro.Proofs.Specialize

/-!
# Proposition 4.3 of `sphere/paper.tex`

The normalized singular vector `χ_{r,s}(b)` over `ℚ(b)`, its uniqueness and
`β_χ = 𝒜_{r,s}⁻¹` are those of the torus Proposition 6.2; the fusion polynomial identity over
`ℚ(b)` is the cited input; regularity at every `b⋆ ≠ 0` is the torus Lemma 6.6.  The second
identity at `b⋆` holds first for rational `Δ_a, Δ_b` (evaluate the identity over `ℚ(b)` at
`b⋆`) and then for all complex `Δ_a, Δ_b`, both sides being polynomials in each of them.
-/

namespace Virasoro.Sphere

open Polynomial

theorem map_gammaY {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Δ Δa Δb : R) :
    ∀ w : List ℕ, f (gammaY Δ Δa Δb w) = gammaY (f Δ) (f Δa) (f Δb) w := by
  intro w
  induction w with
  | nil => simp [gammaY]
  | cons y w ih => simp only [gammaY, map_mul, map_sub, map_add, map_natCast, ih]

theorem eval_gammaY_b (h a x : ℂ) (w : List ℕ) :
    eval x (gammaY (C h) (C a) X w) = gammaY h a x w := by
  have := map_gammaY (evalRingHom x) (C h) (C a) X w
  simpa using this

theorem eval_gammaY_a (h x bb : ℂ) (w : List ℕ) :
    eval x (gammaY (C h) X (C bb) w) = gammaY h x bb w := by
  have := map_gammaY (evalRingHom x) (C h) X (C bb) w
  simpa using this

theorem evTo_gammaY {b : ℂ} {Δ Δa Δb : RatFunc ℚ} {δ δa δb : ℂ} (h : EvTo b Δ δ)
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

theorem evTo_fusP {b : ℂ} (hb0 : b ≠ 0) (r s : ℕ) {Δa Δb : RatFunc ℚ} {δa δb : ℂ}
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
        ((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) :=
      ((evTo_intCast x.1).mul evTo_X).add ((evTo_intCast x.2).mul (evTo_X.inv hb0))
    exact ((((hA.sub hB).add (hβ.pow 2)).pow 2).sub
      (((evTo_ofNat 4).mul hA).mul (hβ.pow 2))).div (evTo_ofNat 16) (by norm_num)

/-- `P_{r,s}(b,Δ_a,Δ_b)` as a polynomial in `Δ_a`. -/
noncomputable def fusPa (r s : ℕ) (b Δb : ℂ) : ℂ[X] :=
  (if (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s then
      C (1 / 4) * (C ((b + b⁻¹) ^ 2) - 4 * X - C ((b + b⁻¹) ^ 2 - 4 * Δb)) else 1) *
    ∏ x ∈ (stepRange r ×ˢ stepRange s).filter fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
      C (1 / 16) * ((C ((b + b⁻¹) ^ 2) - 4 * X - C ((b + b⁻¹) ^ 2 - 4 * Δb)
          + C (((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2)) ^ 2
        - 4 * (C ((b + b⁻¹) ^ 2) - 4 * X) * C (((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2))

/-- `P_{r,s}(b,Δ_a,Δ_b)` as a polynomial in `Δ_b`. -/
noncomputable def fusPb (r s : ℕ) (b Δa : ℂ) : ℂ[X] :=
  (if (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s then
      C (1 / 4) * (C ((b + b⁻¹) ^ 2 - 4 * Δa) - (C ((b + b⁻¹) ^ 2) - 4 * X)) else 1) *
    ∏ x ∈ (stepRange r ×ˢ stepRange s).filter fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
      C (1 / 16) * ((C ((b + b⁻¹) ^ 2 - 4 * Δa) - (C ((b + b⁻¹) ^ 2) - 4 * X)
          + C (((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2)) ^ 2
        - 4 * C ((b + b⁻¹) ^ 2 - 4 * Δa) * C (((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2))

theorem fusPa_eval (r s : ℕ) (b Δa Δb : ℂ) : (fusPa r s b Δb).eval Δa = fusP r s b Δa Δb := by
  simp only [fusPa, fusP]
  rw [eval_mul, eval_prod]
  congr 1
  · split_ifs
    · simp
      ring
    · simp
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp
    ring

theorem fusPb_eval (r s : ℕ) (b Δa Δb : ℂ) : (fusPb r s b Δa).eval Δb = fusP r s b Δa Δb := by
  simp only [fusPb, fusP]
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
theorem poly_ext_rat {P Q : ℂ[X]} (h : ∀ q : ℚ, P.eval (q : ℂ) = Q.eval (q : ℂ)) : P = Q := by
  refine eq_of_infinite_eval_eq P Q (Set.Infinite.mono ?_
    (Set.infinite_range_of_injective (Rat.cast_injective (α := ℂ))))
  rintro _ ⟨q, rfl⟩
  exact h q

/-- Proposition 4.3, from the cited normalizations of the torus Proposition 6.2 and the cited
fusion polynomial.

Paper label: prop:imported -/
theorem prop_imported_of_cited (hH : Cited_HJSNormalizations)
    (hF : Cited_SphereFusionPolynomial) : Stmt_prop_imported := by
  intro r s hr hs
  obtain ⟨p, ⟨hp1, hps⟩, huniq, hcross, -, -⟩ := normalization_at hH r s hr hs
  have hfus := hF r s hr hs p hp1 hps
  refine ⟨p, ⟨hp1, hps⟩, huniq, hcross, hfus, fun b₁ hb₁ => ?_⟩
  have hreg := (lem_regular_everywhere_of_cited hH r s hr hs p hp1 hps b₁ hb₁).1
  refine ⟨hreg, ?_⟩
  have hQ : ∀ qa qb : ℚ,
      ∑ Y, RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y) *
          gammaY (kacH r s b₁) (qa : ℂ) (qb : ℂ) Y.word = fusP r s b₁ (qa : ℂ) (qb : ℂ) := by
    intro qa qb
    have e1 : EvTo b₁
        (∑ Y, p Y * gammaY (kacH r s (RatFunc.X : RatFunc ℚ)) (RatFunc.C qa) (RatFunc.C qb)
          Y.word)
        (∑ Y, RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y) *
          gammaY (kacH r s b₁) (algebraMap ℚ ℂ qa) (algebraMap ℚ ℂ qb) Y.word) :=
      EvTo.sum _ fun Y _ => EvTo.mul ⟨hreg Y, rfl⟩
        (evTo_gammaY (evTo_kacH hb₁ r s) (evTo_C qa) (evTo_C qb) Y.word)
    have e2 := evTo_fusP hb₁ r s (evTo_C (b := b₁) qa) (evTo_C (b := b₁) qb)
    rw [hfus] at e1
    have e3 := e1.unique e2
    simpa only [eq_ratCast] using e3
  have h1 : ∀ (qa : ℚ) (Δb : ℂ),
      ∑ Y, RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y) *
          gammaY (kacH r s b₁) (qa : ℂ) Δb Y.word = fusP r s b₁ (qa : ℂ) Δb := by
    intro qa Δb
    have hpoly : (∑ Y : Nat.Partition (r * s), C (RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y)) *
        gammaY (C (kacH r s b₁)) (C (qa : ℂ)) X Y.word : ℂ[X]) = fusPb r s b₁ (qa : ℂ) := by
      refine poly_ext_rat fun qb => ?_
      rw [fusPb_eval, ← hQ qa qb, eval_finsetSum]
      exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_b]
    have h2 := congrArg (eval Δb) hpoly
    rw [fusPb_eval, eval_finsetSum] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_b]
  intro Δa Δb
  have hpoly : (∑ Y : Nat.Partition (r * s), C (RatFunc.eval (algebraMap ℚ ℂ) b₁ (p Y)) *
      gammaY (C (kacH r s b₁)) X (C Δb) Y.word : ℂ[X]) = fusPa r s b₁ Δb := by
    refine poly_ext_rat fun qa => ?_
    rw [fusPa_eval, ← h1 qa Δb, eval_finsetSum]
    exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_a]
  have h2 := congrArg (eval Δa) hpoly
  rw [fusPa_eval, eval_finsetSum] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun Y _ => by rw [eval_mul, eval_C, eval_gammaY_a]

example (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial) :
    Stmt_prop_imported := prop_imported_of_cited hH hF

end Virasoro.Sphere
