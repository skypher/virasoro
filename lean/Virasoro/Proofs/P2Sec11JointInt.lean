import Virasoro.Proofs.P2Sec11JointRec
import Virasoro.Proofs.KacField
import Virasoro.Proofs.GenericH
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Lemma 11.3 (joint regularity), proof, first step (paper.tex l.2508–2540)

"Work in the Laurent-polynomial ring `ℚ[b,b⁻¹,Δ]`": the ring `ℂ[b,b⁻¹]` is the subalgebra `bLaur`
of `ℂ(b)`.  The entries of `G_N(c(b),Δ)` and `ρ_N(c(b),Δ,d(b))` lie in `bLaur[Δ]`, the Kac
determinant is a unit of `bLaur` times a product of factors monic in `Δ`, and the quotient of an
element of `bLaur[Δ]` by a monic element of `bLaur[Δ]` that is a polynomial over `ℂ(b)` lies in
`bLaur[Δ]`.  With the cancellation of the inactive factors (`Frat_active_poly`) this gives
`Stmt_sub_joint_denominator`.
-/

namespace Virasoro

open Polynomial

/-- The Laurent-polynomial ring `ℂ[b,b⁻¹]` inside `ℂ(b)`. -/
def bLaur : Subalgebra ℚ (RatFunc ℂ) where
  carrier := {x | ∃ (e : ℕ) (P : ℂ[X]), RatFunc.X ^ e * x = algebraMap ℂ[X] (RatFunc ℂ) P}
  mul_mem' := by
    rintro x y ⟨e, P, hP⟩ ⟨e', P', hP'⟩
    exact ⟨e + e', P * P', by rw [map_mul, ← hP, ← hP']; ring⟩
  add_mem' := by
    rintro x y ⟨e, P, hP⟩ ⟨e', P', hP'⟩
    refine ⟨e + e', X ^ e' * P + X ^ e * P', ?_⟩
    rw [map_add, map_mul, map_mul, ← hP, ← hP', map_pow, map_pow, RatFunc.algebraMap_X]
    ring
  algebraMap_mem' := fun q => ⟨0, C (q : ℂ), by
    rw [pow_zero, one_mul, RatFunc.algebraMap_C, eq_ratCast, map_ratCast]⟩

theorem mem_bLaur {x : RatFunc ℂ} :
    x ∈ bLaur ↔ ∃ (e : ℕ) (P : ℂ[X]), RatFunc.X ^ e * x = algebraMap ℂ[X] (RatFunc ℂ) P :=
  Iff.rfl

theorem X_mem_bLaur : (RatFunc.X : RatFunc ℂ) ∈ bLaur := ⟨0, X, by simp⟩

theorem Xinv_mem_bLaur : (RatFunc.X : RatFunc ℂ)⁻¹ ∈ bLaur :=
  ⟨1, 1, by rw [pow_one, mul_inv_cancel₀ RatFunc.X_ne_zero, map_one]⟩

theorem kacC_mem_bLaur : kacC (RatFunc.X : RatFunc ℂ) ∈ bLaur := by
  unfold kacC
  have h6 : (6 : RatFunc ℂ) ∈ bLaur := by exact_mod_cast natCast_mem bLaur 6
  exact add_mem (one_mem _) (mul_mem h6 (pow_mem (add_mem X_mem_bLaur Xinv_mem_bLaur) 2))

theorem kacH_mem_bLaur (u v : ℤ) : kacH u v (RatFunc.X : RatFunc ℂ) ∈ bLaur := by
  unfold kacH
  rw [div_eq_mul_inv]
  have h4 : (4 : RatFunc ℂ)⁻¹ ∈ bLaur := by
    have := bLaur.algebraMap_mem (4⁻¹ : ℚ)
    rwa [map_inv₀, map_ofNat] at this
  exact mul_mem (sub_mem (pow_mem (add_mem X_mem_bLaur Xinv_mem_bLaur) 2)
    (pow_mem (add_mem (mul_mem (intCast_mem _ u) X_mem_bLaur)
      (mul_mem (intCast_mem _ v) Xinv_mem_bLaur)) 2)) h4

/-- A polynomial over `ℚ` with no nonzero complex root is a nonzero constant times a power of
the variable. -/
theorem eq_monomial_of_no_roots {P : ℚ[X]}
    (h : ∀ b : ℂ, b ≠ 0 → eval₂ (algebraMap ℚ ℂ) b P ≠ 0) :
    ∃ (q : ℚ) (n : ℕ), q ≠ 0 ∧ P = C q * X ^ n := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h 1 one_ne_zero (by simp)
  have hPc0 : P.map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 hP0
  have hroots : ∀ a ∈ (P.map (algebraMap ℚ ℂ)).roots, a = 0 := by
    intro a ha
    by_contra ha0
    exact h a ha0 (by rw [eval₂_eq_eval_map]; exact (mem_roots hPc0).1 ha)
  have hs := (IsAlgClosed.splits (P.map (algebraMap ℚ ℂ))).eq_prod_roots
  rw [Multiset.eq_replicate.2 ⟨rfl, hroots⟩] at hs
  simp only [Multiset.map_replicate, Multiset.prod_replicate, map_zero, sub_zero] at hs
  refine ⟨P.leadingCoeff, (P.map (algebraMap ℚ ℂ)).roots.card, leadingCoeff_ne_zero.2 hP0, ?_⟩
  apply Polynomial.map_injective _ (algebraMap ℚ ℂ).injective
  rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, ← leadingCoeff_map]
  exact hs

/-- The value at `b` of a nonzero constant times a power of the variable is a unit of
`ℂ[b,b⁻¹]`. -/
theorem monomial_unit_mem {q : ℚ} (hq : q ≠ 0) (n : ℕ) :
    eval₂ (algebraMap ℚ (RatFunc ℂ)) RatFunc.X (C q * X ^ n) ∈ bLaur ∧
      (eval₂ (algebraMap ℚ (RatFunc ℂ)) RatFunc.X (C q * X ^ n))⁻¹ ∈ bLaur := by
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  refine ⟨mul_mem (bLaur.algebraMap_mem q) (pow_mem X_mem_bLaur n), ?_⟩
  rw [mul_inv, ← map_inv₀, ← inv_pow]
  exact mul_mem (bLaur.algebraMap_mem q⁻¹) (pow_mem Xinv_mem_bLaur n)

theorem kac_lead_coeff {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] (b C₀ : 𝔽) (N : ℕ)
    (h : (gramPoly (kacC b) N).det = C C₀ * kacProd b N) :
    (gramPoly (kacC b) N).det.coeff (kacDeg N) = C₀ := by
  rw [h, coeff_C_mul]
  have := (kacProd_monic b N).coeff_natDegree
  rw [kacProd_natDegree] at this
  rw [this, mul_one]

/-- The constant `C_N` of the Kac determinant formula is a unit of `ℂ[b,b⁻¹]`
(paper.tex l.2510–2515: `C_N ∈ ℚ^×`, so the determinant has unit `Δ`-leading coefficient). -/
theorem kacLead_unit (hK : Cited_KacDeterminant) (N : ℕ) :
    ∃ C₀ : RatFunc ℂ, C₀ ∈ bLaur ∧ C₀⁻¹ ∈ bLaur ∧ C₀ ≠ 0 ∧
      (gramPoly (kacC (RatFunc.X : RatFunc ℂ)) N).det = C C₀ * kacProd RatFunc.X N := by
  have hpt : ∀ b : ℂ, b ≠ 0 →
      eval₂ (algebraMap ℚ ℂ) b (RatFunc.denom
        ((gramPoly (kacC (RatFunc.X : RatFunc ℚ)) N).det.coeff (kacDeg N))) ≠ 0 ∧
      eval₂ (algebraMap ℚ ℂ) b (RatFunc.num
        ((gramPoly (kacC (RatFunc.X : RatFunc ℚ)) N).det.coeff (kacDeg N))) ≠ 0 := by
    intro b hb
    obtain ⟨C₀, hC₀, hdet⟩ := hK b hb N
    have hev := polyEv_gramDet hb N (kacDeg N)
    rw [kac_lead_coeff b C₀ N hdet] at hev
    refine ⟨hev.1, fun h0 => hC₀ ?_⟩
    rw [← hev.2, RatFunc.eval, h0, zero_div]
  obtain ⟨q, n, hq, hnum⟩ := eq_monomial_of_no_roots fun b hb => (hpt b hb).2
  obtain ⟨q', n', hq', hden⟩ := eq_monomial_of_no_roots fun b hb => (hpt b hb).1
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK (b := (RatFunc.X : RatFunc ℂ)) RatFunc.X_ne_zero N
  have hev := polyEv_gramDet (b := (RatFunc.X : RatFunc ℂ)) RatFunc.X_ne_zero N (kacDeg N)
  rw [kac_lead_coeff _ C₀ N hdet] at hev
  have hval : C₀ = eval₂ (algebraMap ℚ (RatFunc ℂ)) RatFunc.X (C q * X ^ n) /
      eval₂ (algebraMap ℚ (RatFunc ℂ)) RatFunc.X (C q' * X ^ n') := by
    rw [← hev.2, RatFunc.eval, hnum, hden]
  refine ⟨C₀, ?_, ?_, hC₀, hdet⟩
  · rw [hval, div_eq_mul_inv]
    exact mul_mem (monomial_unit_mem hq n).1 (monomial_unit_mem hq' n').2
  · rw [hval, inv_div, div_eq_mul_inv]
    exact mul_mem (monomial_unit_mem hq' n').1 (monomial_unit_mem hq n).2

/-- A polynomial in `Δ` over `ℂ[b,b⁻¹]` becomes a polynomial in `(b,Δ)` after multiplication by
a power of `b`. -/
theorem laurent_clear (QA : bLaur[X]) : ∃ (e : ℕ) (P : ℂ[X][X]),
    C ((RatFunc.X : RatFunc ℂ) ^ e) * QA.map bLaur.val.toRingHom =
      P.map (algebraMap ℂ[X] (RatFunc ℂ)) := by
  induction QA using Polynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨e, P, hP⟩ := hf
    obtain ⟨e', P', hP'⟩ := hg
    refine ⟨e + e', C (X ^ e') * P + C (X ^ e) * P', ?_⟩
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← hP,
      ← hP', Polynomial.map_C, Polynomial.map_C]
    simp only [map_pow, RatFunc.algebraMap_X, pow_add, C_mul, C_pow]
    ring
  | monomial n a =>
    obtain ⟨x, e, P₀, h⟩ := a
    refine ⟨e, monomial n P₀, ?_⟩
    rw [Polynomial.map_monomial, Polynomial.map_monomial, C_mul_monomial, ← h]
    rfl

/-- First step of the proof of Lemma 11.3 (paper.tex l.2508–2540), from the Kac determinant
formula and the generic recursion. -/
theorem sub_joint_denominator (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_joint_denominator := by
  classical
  intro k m ε N
  obtain ⟨Q, hQ⟩ := Frat_active_poly (genericRecursionUniform hK hH) k m ε N
  obtain ⟨C₀, -, hC₀im, hC₀, hdet⟩ := kacLead_unit hK N
  let incl : bLaur →+* RatFunc ℂ := bLaur.val.toRingHom
  let cA : bLaur := ⟨_, kacC_mem_bLaur⟩
  let dA : bLaur := ⟨_, kacH_mem_bLaur (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1))⟩
  let hA : Label → bLaur := fun a => ⟨kacHL a RatFunc.X, kacH_mem_bLaur _ _⟩
  let numA : bLaur[X] := numR (C cA) X (C dA) N
  let prodA : bLaur[X] :=
    ∏ a ∈ labels N, (X - C (hA a)) ^ Fintype.card (Nat.Partition (N - a.lvl))
  let actA : bLaur[X] := ∏ a ∈ activeLabels k m N, (X - C (hA a))
  have hnum : Fnum (kacC (RatFunc.X : RatFunc ℂ))
      (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) RatFunc.X) N = numA.map incl := by
    have := map_numR (Polynomial.mapRingHom incl) (C cA) (X : bLaur[X]) (C dA) N
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
    rw [this]
    rfl
  have hprod : kacProd (RatFunc.X : RatFunc ℂ) N = prodA.map incl := by
    simp only [prodA, kacProd, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    rfl
  have hact : ∏ a ∈ activeLabels k m N, (X - C (kacHL a (RatFunc.X : RatFunc ℂ))) =
      actA.map incl := by
    simp only [actA, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hmonic : prodA.Monic := monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow _
  have hdet0 : algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ))
      (gramPoly (kacC (RatFunc.X : RatFunc ℂ)) N).det ≠ 0 := fun h0 =>
    gramPoly_det_ne_zero _ N
      ((map_eq_zero_iff _ (IsFractionRing.injective (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ)))).1 h0)
  have hid : kacProd (RatFunc.X : RatFunc ℂ) N * (Q * C C₀) =
      Fnum (kacC (RatFunc.X : RatFunc ℂ))
        (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) RatFunc.X) N *
      ∏ a ∈ activeLabels k m N, (X - C (kacHL a (RatFunc.X : RatFunc ℂ))) := by
    apply IsFractionRing.injective (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ))
    rw [show kacProd (RatFunc.X : RatFunc ℂ) N * (Q * C C₀) =
      Q * (gramPoly (kacC (RatFunc.X : RatFunc ℂ)) N).det by rw [hdet]; ring, map_mul, map_mul,
      ← hQ, Frat]
    field_simp
  have hQC : Q * C C₀ = ((numA * actA) /ₘ prodA).map incl := by
    rw [map_divByMonic incl hmonic, Polynomial.map_mul, ← hnum, ← hact, ← hprod, ← hid,
      mul_divByMonic_cancel_left _ (kacProd_monic _ N)]
  obtain ⟨e, P, hP⟩ := laurent_clear (C (⟨C₀⁻¹, hC₀im⟩ : bLaur) * ((numA * actA) /ₘ prodA))
  have hQA : (C (⟨C₀⁻¹, hC₀im⟩ : bLaur) * ((numA * actA) /ₘ prodA)).map incl = Q := by
    rw [Polynomial.map_mul, ← hQC, Polynomial.map_C]
    show C C₀⁻¹ * (Q * C C₀) = Q
    rw [mul_comm, mul_assoc, ← C_mul, mul_inv_cancel₀ hC₀, C_1, mul_one]
  refine ⟨e, P, ?_⟩
  rw [← hP]
  show _ = algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ)) (C (RatFunc.X ^ e) *
    (C (⟨C₀⁻¹, hC₀im⟩ : bLaur) * ((numA * actA) /ₘ prodA)).map incl)
  rw [hQA, map_mul, ← hQ, RatFunc.algebraMap_C, map_prod]
  simp only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, activeLabels]
  ring

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_joint_denominator := sub_joint_denominator hK hH

end Virasoro
