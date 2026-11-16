import Virasoro.Proofs.Specialize
import Virasoro.Cited

/-!
# Proposition 6.2: continuation of the normalization identities

The identities (6.1) and (6.2) for the normalized singular vector over `ℚ(b)` specialize to
every point `b ≠ 0` of a field of characteristic zero at which the coordinates of the normalized
singular vector are regular; there the specialized vector is singular.
-/

namespace Virasoro

open Polynomial

theorem genA_inv {𝔽 : Type*} [Field 𝔽] (r s : ℕ) (b : 𝔽) :
    (genA r s b)⁻¹ = 2 * ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹) := by
  unfold genA
  rw [mul_inv, inv_inv, ← Finset.prod_inv_distrib]
  simp only [inv_inv]

theorem evTo_genA_inv {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] {b : 𝔽} (hb : b ≠ 0) (r s : ℕ) :
    EvTo b ((genA r s (RatFunc.X : RatFunc ℚ))⁻¹)
      (2 * ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹)) := by
  rw [genA_inv]
  exact (evTo_ofNat 2).mul (EvTo.prod _ fun pq _ =>
    ((evTo_intCast pq.1).mul evTo_X).add ((evTo_intCast pq.2).mul (evTo_X.inv hb)))

/-- The normalized singular vector over `ℚ(b)` and its specializations: at every point `b ≠ 0`
of a field of characteristic zero where its coordinates are regular, the specialized vector is
singular with `L_{-1}^{rs}`-coefficient `1`, its crossing scalar is `2 ∏ (p b + q b⁻¹)`, and its
torus self-pairing is `𝒫_{r,s}(b,d)`. -/
theorem normalization_at (hN : NormalizationIdentities) (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ p : Nat.Partition (r * s) → RatFunc ℚ,
      (p (onesPartition (r * s)) = 1 ∧
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p) (r * s)) ∧
      (∀ p' : Nat.Partition (r * s) → RatFunc ℚ, p' (onesPartition (r * s)) = 1 →
        Verma.IsSingular
          (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
            (r * s) p') (r * s) → p' = p) ∧
      crossScalar (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) p =
        (genA r s (RatFunc.X : RatFunc ℚ))⁻¹ ∧
      (∀ d : RatFunc ℚ,
        torusForm (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) d (r * s) p p =
          genP r s RatFunc.X d) ∧
      ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (b : 𝔽), b ≠ 0 →
        (∀ Y, Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom (p Y)) ≠ 0) →
        Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) (r * s)
          fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) (r * s) ∧
        RatFunc.eval (algebraMap ℚ 𝔽) b (p (onesPartition (r * s))) = 1 ∧
        crossScalar (kacC b) (kacH r s b) (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) =
          2 * ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹) ∧
        ∀ d : 𝔽, torusForm (kacC b) (kacH r s b) d (r * s)
          (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y))
          (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) = genP r s b d := by
  obtain ⟨p, ⟨hp1, hsing⟩, huniq, hcross, htor⟩ := hN r s hr hs
  refine ⟨p, ⟨hp1, hsing⟩, huniq, hcross, htor, ?_⟩
  intro 𝔽 _ _ b hb hreg
  have hone : RatFunc.eval (algebraMap ℚ 𝔽) b (p (onesPartition (r * s))) = 1 := by
    rw [hp1]
    exact RatFunc.eval_one (f := algebraMap ℚ 𝔽) (a := b)
  obtain ⟨h1, h2, h3⟩ := specialize_singular (evTo_kacC hb) (evTo_kacH hb (r : ℤ) (s : ℤ)) p
    hreg hsing ⟨onesPartition (r * s), by rw [hone]; exact one_ne_zero⟩
  refine ⟨h1, hone, ?_, ?_⟩
  · rw [hcross] at h2
    exact h2.unique (evTo_genA_inv hb r s)
  · haveI : Infinite (RatFunc ℚ) :=
      Infinite.of_injective (fun q : ℚ => RatFunc.C q) RatFunc.C_injective
    have hpoly : torusSelf (kacC (RatFunc.X : RatFunc ℚ)) (kacH r s RatFunc.X) p
        = genPpoly r s (RatFunc.X : RatFunc ℚ) :=
      Polynomial.funext fun d => by rw [torusSelf_eval, htor d, genPpoly_eval]
    rw [hpoly] at h3
    have heq := h3.unique (polyEv_genPpoly hb r s)
    intro d
    rw [← torusSelf_eval, heq, genPpoly_eval]

/-- Proposition 6.2, with the two identities over `ℚ(b)` taken from the literature. -/
theorem prop_imported_normalizations (h : Cited_HJSNormalizations) :
    Stmt_prop_imported_normalizations := by
  intro r s hr hs
  obtain ⟨p, h1, h2, h3, h4, hat⟩ := normalization_at h r s hr hs
  refine ⟨p, h1, h2, h3, h4, fun b₁ hb₁ hreg => ?_⟩
  obtain ⟨-, -, h5, h6⟩ := hat ℂ b₁ hb₁ hreg
  exact ⟨h5, h6⟩

example (h : Cited_HJSNormalizations) : Stmt_prop_imported_normalizations :=
  prop_imported_normalizations h

end Virasoro
