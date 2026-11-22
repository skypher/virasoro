import Virasoro.Proofs.Sec6H13Reg
import Virasoro.Proofs.KacField
import Virasoro.Proofs.GenericH
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Proposition 6.8(i) of `paper.tex` at 70bac53: Cramer's rule and monic division (l.1224–1231,
l.1257–1261)

The entries of `G_M` and `ρ_M` at `c = c(b)`, `d = d_ν` lie in `ℚ[t,t⁻¹][Δ]` (l.1232–1235; the
paper records the smaller ring `ℤ[1/2][t,t⁻¹]`, used for the integrality clause).  By the Kac
determinant `det G_M = K_M ∏ (Δ - h_{u,v})^{p(M-uv)}` with `K_M = ∏ K_λ`, Cramer's rule writes
`H_M` with a denominator that is monic in `Δ` over `ℚ[t,t⁻¹]`.  By the generic recursion
`∏_{u ≤ M} (Δ - h_{u,1}) H_M` is a polynomial in `Δ` (l.1224–1231); monic division gives its
coefficients in `ℚ[t,t⁻¹]`.

`Lt` is `ℚ[t,t⁻¹] ⊂ ℚ(t)`; the recursion is applied over `ℚ(b)`, reached by `t ↦ b²`.
-/

namespace Virasoro

open Polynomial

/-! ### The leading coefficient of the Shapovalov determinant -/

section Top

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `K_N = ∏_{λ ⊢ N} K_λ`. -/
def kacK (N : ℕ) : ℕ := ∏ Y : Nat.Partition N, topNat Y.word Y.word

theorem kacK_ne_zero (N : ℕ) : kacK N ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun Y _ => (topNat_self_pos Y.word (word_pos Y)).ne'

/-- `∑_{λ ⊢ N} ℓ(λ)`. -/
def lenSum (N : ℕ) : ℕ := ∑ Y : Nat.Partition N, Y.word.length

omit [CharZero 𝔽] in
theorem det_natDegree_le' {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι 𝔽[X])
    (a : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ a i) : M.det.natDegree ≤ ∑ i, a i := by
  rw [Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine natDegree_mul_le.trans ?_
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : 𝔽[X]).natDegree = 0 := natDegree_intCast _
  rw [h1, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  rw [← Equiv.sum_comp σ a]
  exact Finset.sum_le_sum fun i _ => h (σ i) i

theorem gramPoly_det_natDegree_le (c : 𝔽) (N : ℕ) :
    (gramPoly c N).det.natDegree ≤ lenSum N :=
  det_natDegree_le' _ _ fun Y Y' =>
    (natDegree_gramWord_le c Y.word Y'.word (word_pos Y)).trans (min_le_left _ _)

theorem gramPoly_det_coeff_lenSum (c : 𝔽) (N : ℕ) :
    (gramPoly c N).det.coeff (lenSum N) = (kacK N : 𝔽) := by
  rw [lenSum, det_coeff_top (gramPoly c N) (fun Y => Y.word.length)]
  · rw [kacK, Nat.cast_prod]
    refine Finset.prod_congr rfl fun Y _ => ?_
    have h := coeff_gramWord_top c Y.word Y.word (word_pos Y) rfl
    simp only [gramPoly, gram, Matrix.of_apply]
    rw [h, topFun_eq_topNat]
  · intro Y Y'
    exact natDegree_gramWord_le c Y.word Y'.word (word_pos Y)
  · intro Y Y' hne hlen
    have h := coeff_gramWord_top c Y.word Y'.word (word_pos Y) hlen
    simp only [gramPoly, gram, Matrix.of_apply]
    rw [h, topFun_eq_topNat, topNat_eq_zero_of_not_perm hlen, Nat.cast_zero]
    intro hperm
    exact hne (word_injective hperm).symm

end Top

/-- The Kac determinant with its constant: `det G_N = K_N ∏ (Δ - h_{u,v})^{p(N-uv)}`
(paper.tex l.1257–1258). -/
theorem kac_det_const {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] (hK : Cited_KacDeterminant) {b : 𝔽}
    (hb : b ≠ 0) (N : ℕ) :
    (gramPoly (kacC b) N).det = C (kacK N : 𝔽) * kacProd b N := by
  obtain ⟨C₀, hC₀, h⟩ := kac_det_field hK hb N
  have hdeg : (gramPoly (kacC b) N).det.natDegree = kacDeg N := by
    rw [h, natDegree_C_mul hC₀, kacProd_natDegree]
  have hcoef : (gramPoly (kacC b) N).det.coeff (kacDeg N) = C₀ := by
    have := (kacProd_monic b N).coeff_natDegree
    rw [kacProd_natDegree] at this
    rw [h, coeff_C_mul, this, mul_one]
  have h1 : kacDeg N ≤ lenSum N := hdeg ▸ gramPoly_det_natDegree_le (kacC b) N
  have h2 : lenSum N ≤ kacDeg N := by
    rw [← hdeg]
    apply le_natDegree_of_ne_zero
    rw [gramPoly_det_coeff_lenSum]
    exact Nat.cast_ne_zero.2 (kacK_ne_zero N)
  have h3 : lenSum N = kacDeg N := le_antisymm h2 h1
  rw [← h3, gramPoly_det_coeff_lenSum] at hcoef
  rw [h, ← hcoef]

/-! ### `ℚ[t,t⁻¹]` -/

/-- `ℚ[t,t⁻¹]` as a subalgebra of `ℚ(t)`. -/
noncomputable def Lt : Subalgebra ℚ (RatFunc ℚ) where
  carrier := {x | ∃ (n : ℕ) (p : ℚ[X]),
    (RatFunc.X : RatFunc ℚ) ^ n * x = algebraMap ℚ[X] (RatFunc ℚ) p}
  mul_mem' := by
    rintro x y ⟨n, p, hp⟩ ⟨m, q, hq⟩
    exact ⟨n + m, p * q, by rw [map_mul, ← hp, ← hq]; ring⟩
  add_mem' := by
    rintro x y ⟨n, p, hp⟩ ⟨m, q, hq⟩
    refine ⟨n + m, X ^ m * p + X ^ n * q, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X, ← hp, ← hq]
    ring
  algebraMap_mem' := fun r => ⟨0, C r, by
    rw [pow_zero, one_mul, RatFunc.algebraMap_C]
    exact (eq_ratCast (algebraMap ℚ (RatFunc ℚ)) r).trans (eq_ratCast RatFunc.C r).symm⟩

/-- `t ∈ ℚ[t,t⁻¹]`. -/
noncomputable def tL : Lt := ⟨RatFunc.X, 0, X, by rw [pow_zero, one_mul, RatFunc.algebraMap_X]⟩

/-- `c(b) = 13 + 6t + 6/t ∈ ℚ[t,t⁻¹]`. -/
noncomputable def cL : Lt := ⟨cT RatFunc.X, 1, 13 * X + 6 * X ^ 2 + 6, by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, map_ofNat, cT]
  field_simp⟩

/-- `d_ν ∈ ℚ[t,t⁻¹]`. -/
noncomputable def dL (ν : Fin 2) : Lt := ⟨d13 ν, 1, if ν = 0 then -X - 2 else 2 * X - 2, by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  unfold d13
  split_ifs
  · simp only [map_sub, map_neg, map_ofNat, RatFunc.algebraMap_X]
    field_simp
  · simp only [map_sub, map_mul, map_ofNat, RatFunc.algebraMap_X]
    field_simp⟩

/-- `h_{u,v}(b) ∈ ℚ[t,t⁻¹]`. -/
noncomputable def hL (u v : ℤ) : Lt :=
  ⟨hT u v RatFunc.X, 1, C (1 / 4) * ((X + 1) ^ 2 - (C (u : ℚ) * X + C (v : ℚ)) ^ 2), by
    have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    simp only [map_mul, map_sub, map_add, map_pow, map_one, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, hT, map_div₀, map_ofNat, map_intCast]
    field_simp⟩

/-- The inclusion `ℚ[t,t⁻¹] → ℚ(t)`. -/
noncomputable def phiT1 : Lt →+* RatFunc ℚ := Lt.val.toRingHom

theorem expandAlg_injective : Function.Injective
    ((algebraMap ℚ[X] (RatFunc ℚ)).comp (expand ℚ 2 : ℚ[X] →+* ℚ[X])) :=
  (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp (expand_injective (by norm_num))

/-- `ℚ(t) → ℚ(b)`, `t ↦ b²`. -/
noncomputable def iotaB : RatFunc ℚ →+* RatFunc ℚ := IsFractionRing.lift (K := RatFunc ℚ) expandAlg_injective

theorem iotaB_X : iotaB RatFunc.X = (RatFunc.X : RatFunc ℚ) ^ 2 := by
  have := IsFractionRing.lift_algebraMap (K := RatFunc ℚ) expandAlg_injective (X : ℚ[X])
  rw [RatFunc.algebraMap_X] at this
  rw [iotaB, this]
  simp [RatFunc.algebraMap_X]

/-- `ℚ[t,t⁻¹] → ℚ(b)`, `t ↦ b²`. -/
noncomputable def phiB : Lt →+* RatFunc ℚ := iotaB.comp phiT1

theorem phiB_injective : Function.Injective phiB :=
  iotaB.injective.comp Subtype.val_injective

theorem phiB_cL : phiB cL = kacC (RatFunc.X : RatFunc ℚ) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  show iotaB (cT RatFunc.X) = _
  simp only [cT, kacC, map_add, map_mul, map_div₀, iotaB_X, map_ofNat]
  field_simp
  ring

theorem phiB_hL (u v : ℤ) : phiB (hL u v) = kacH u v (RatFunc.X : RatFunc ℚ) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  show iotaB (hT u v RatFunc.X) = _
  simp only [hT, kacH, map_add, map_sub, map_mul, map_div₀, map_pow, iotaB_X, map_ofNat, map_one,
    map_intCast]
  field_simp

theorem phiB_dL (ν : Fin 2) :
    phiB (dL ν) = if ν = 0 then kacH 1 3 (RatFunc.X : RatFunc ℚ) else kacH 1 (-3) RatFunc.X := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  show iotaB (d13 ν) = _
  unfold d13
  split_ifs
  · simp only [kacH, map_sub, map_neg, map_div₀, map_one, iotaB_X, map_ofNat]
    push_cast
    field_simp
    ring
  · simp only [kacH, map_sub, map_div₀, iotaB_X, map_ofNat]
    push_cast
    field_simp
    ring

/-! ### Cramer's rule over `ℚ[t,t⁻¹][Δ]` -/

/-- `det G_N ∈ ℚ[t,t⁻¹][Δ]`. -/
noncomputable def detL (N : ℕ) : Lt[X] := detR (C cL) X N

/-- The Cramer numerator of `F_N(c(b),Δ,d_ν)` in `ℚ[t,t⁻¹][Δ]`. -/
noncomputable def numL (ν : Fin 2) (N : ℕ) : Lt[X] := numR (C cL) X (C (dL ν)) N

/-- `∏ (Δ - h_{u,v})^{p(N-uv)} ∈ ℚ[t,t⁻¹][Δ]`. -/
noncomputable def kacL (N : ℕ) : Lt[X] :=
  ∏ a ∈ labels N, (X - C (hL (a.1 : ℤ) (a.2 : ℤ))) ^ Fintype.card (Nat.Partition (N - a.lvl))

theorem kacL_monic (N : ℕ) : (kacL N).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

theorem map_detL (φ : Lt →+* RatFunc ℚ) (N : ℕ) :
    (detL N).map φ = (gramPoly (φ cL) N).det := by
  have := map_detR (mapRingHom φ) (C cL) (X : Lt[X]) N
  simp only [coe_mapRingHom, map_C, map_X] at this
  exact this

theorem map_numL (φ : Lt →+* RatFunc ℚ) (ν : Fin 2) (N : ℕ) :
    (numL ν N).map φ = Fnum (φ cL) (φ (dL ν)) N := by
  have := map_numR (mapRingHom φ) (C cL) (X : Lt[X]) (C (dL ν)) N
  simp only [coe_mapRingHom, map_C, map_X] at this
  exact this

theorem map_kacL_phiB (N : ℕ) : (kacL N).map phiB = kacProd (RatFunc.X : RatFunc ℚ) N := by
  unfold kacL kacProd
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, phiB_hL]
  rfl

/-- The Kac determinant in `ℚ[t,t⁻¹][Δ]`. -/
theorem detL_eq (hK : Cited_KacDeterminant) (N : ℕ) : detL N = (kacK N : Lt[X]) * kacL N := by
  apply Polynomial.map_injective phiB phiB_injective
  rw [map_detL, phiB_cL, kac_det_const hK RatFunc.X_ne_zero, Polynomial.map_mul,
    Polynomial.map_natCast, map_kacL_phiB, ← C_eq_natCast]

/-- A family `x(φ) ∈ ℚ(t)(Δ)`, indexed by the homomorphisms `φ` of `ℚ[t,t⁻¹]` into `ℚ(t)`, that
is a quotient of polynomials in `Δ` over `ℚ[t,t⁻¹]` with monic denominator, up to a nonzero
integer factor. -/
def MonL (x : (Lt →+* RatFunc ℚ) → RatFunc (RatFunc ℚ)) : Prop :=
  ∃ (A B : Lt[X]) (k : ℕ), B.Monic ∧ k ≠ 0 ∧ ∀ φ : Lt →+* RatFunc ℚ,
    (k : RatFunc (RatFunc ℚ)) * x φ * algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (B.map φ) =
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (A.map φ)

theorem MonL.zero : MonL fun _ => 0 :=
  ⟨0, 1, 1, monic_one, one_ne_zero, fun φ => by simp⟩

theorem MonL.add {x y : (Lt →+* RatFunc ℚ) → RatFunc (RatFunc ℚ)} (hx : MonL x) (hy : MonL y) :
    MonL fun φ => x φ + y φ := by
  obtain ⟨A, B, k, hB, hk, h1⟩ := hx
  obtain ⟨A', B', k', hB', hk', h2⟩ := hy
  refine ⟨A * B' * (k' : Lt[X]) + A' * B * (k : Lt[X]), B * B', k * k', hB.mul hB',
    mul_ne_zero hk hk', fun φ => ?_⟩
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_natCast, map_add, map_mul,
    map_natCast, Nat.cast_mul]
  rw [← h1 φ, ← h2 φ]
  ring

theorem MonL.int_mul {x : (Lt →+* RatFunc ℚ) → RatFunc (RatFunc ℚ)} (z : ℤ) (hx : MonL x) :
    MonL fun φ => (z : RatFunc (RatFunc ℚ)) * x φ := by
  obtain ⟨A, B, k, hB, hk, h1⟩ := hx
  refine ⟨(z : Lt[X]) * A, B, k, hB, hk, fun φ => ?_⟩
  simp only [Polynomial.map_mul, Polynomial.map_intCast, map_mul, map_intCast]
  rw [← h1 φ]
  ring

/-- Cramer's rule with the Kac determinant (paper.tex l.1257–1259). -/
theorem monL_Frat (hK : Cited_KacDeterminant) (ν : Fin 2) (N : ℕ) :
    MonL fun φ => Frat (φ cL) (φ (dL ν)) N := by
  refine ⟨numL ν N, kacL N, kacK N, kacL_monic N, kacK_ne_zero N, fun φ => ?_⟩
  have hk : ((kacK N : ℕ) : RatFunc (RatFunc ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (kacK_ne_zero N)
  have hB : algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) ((kacL N).map φ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)))]
    exact ((kacL_monic N).map φ).ne_zero
  have hdet : (gramPoly (φ cL) N).det = (kacK N : (RatFunc ℚ)[X]) * (kacL N).map φ := by
    rw [← map_detL, detL_eq hK, Polynomial.map_mul, Polynomial.map_natCast]
  beta_reduce
  rw [map_numL, Frat, hdet, map_mul, map_natCast]
  field_simp

theorem monL_Hrat (hK : Cited_KacDeterminant) (ν : Fin 2) (N : ℕ) :
    MonL fun φ => Hrat (φ cL) (φ (dL ν)) N := by
  unfold Hrat
  generalize Finset.range (N + 1) = s
  induction s using Finset.induction_on with
  | empty => simpa using MonL.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact MonL.add (MonL.int_mul _ (monL_Frat hK ν (N - j))) ih

/-! ### Monic division -/

/-- An element of `ℚ[t,t⁻¹][Δ]`, multiplied by a power of `t`, is a polynomial in `(t, Y)`. -/
theorem laurent_psi (q : Lt[X]) : ∃ (n : ℕ) (P₀ : PS),
    RatFunc.C (RatFunc.X : RatFunc ℚ) ^ n *
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (q.map phiT1) = psi P₀ := by
  have htS : psi tS = RatFunc.C (RatFunc.X : RatFunc ℚ) := by
    simp only [psi, RingHom.comp_apply]
    rw [psi1_tS, RatFunc.algebraMap_C]
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨n, P, hP⟩ := hp
    obtain ⟨m, Q, hQ⟩ := hq
    refine ⟨n + m, tS ^ m * P + tS ^ n * Q, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, htS, ← hP, ← hQ, Polynomial.map_add, map_add]
    ring
  | monomial j a =>
    obtain ⟨n, p, hp⟩ := a.property
    refine ⟨n + 2 * j, C p * X ^ j, ?_⟩
    have h1 : phiT1 a = (a : RatFunc ℚ) := rfl
    simp only [psi, RingHom.comp_apply]
    rw [map_mul, map_pow, psi1_C, psi1_X, ← hp, Polynomial.map_monomial, h1,
      ← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    ring

/-- `P_M^{(ν)}`, multiplied by a power of `t`, is a polynomial in `(t, Y)`: Cramer's rule and
monic division (paper.tex l.1224–1231 and l.1257–1261). -/
theorem laurent_clearedH (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (ν : Fin 2) (M : ℕ) : ∃ (n : ℕ) (P₀ : PS),
      RatFunc.C (RatFunc.X : RatFunc ℚ) ^ n * clearedH ν M = psi P₀ := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    refine ⟨0, 1, ?_⟩
    simp [clearedH, Hrat_zero]
  set alg := algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) with halg
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  obtain ⟨A, B, k, hB, hk, hAB⟩ := monL_Hrat hK ν M
  -- the recursion over `ℚ(b)`
  obtain ⟨S, hS0, hS⟩ := genericRecursionUniform hK hH M hM
  have hrec : GenericRecursionAt (RatFunc ℚ) (RatFunc.X : RatFunc ℚ) (phiB (dL ν)) M := by
    refine hS (RatFunc ℚ) RatFunc.X (phiB (dL ν)) RatFunc.X_ne_zero fun P hP => ?_
    have e : ((aeval (RatFunc.X : RatFunc ℚ) : ℚ[X] →ₐ[ℚ] RatFunc ℚ) : ℚ[X] →+* RatFunc ℚ) =
        algebraMap ℚ[X] (RatFunc ℚ) :=
      Polynomial.ringHom_ext
        (fun a => by
          rw [RingHom.coe_coe, aeval_C, RatFunc.algebraMap_C]
          exact (eq_ratCast (algebraMap ℚ (RatFunc ℚ)) a).trans (eq_ratCast RatFunc.C a).symm)
        (by rw [RingHom.coe_coe, aeval_X, RatFunc.algebraMap_X])
    have e2 : aeval (RatFunc.X : RatFunc ℚ) P = algebraMap ℚ[X] (RatFunc ℚ) P :=
      RingHom.congr_fun e P
    rw [e2, Ne, map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))]
    exact hS0 P hP
  have hP : ∀ u v : ℕ, 1 ≤ u → 2 ≤ v → genP u v (RatFunc.X : RatFunc ℚ) (phiB (dL ν)) = 0 := by
    intro u v hu hv
    rw [phiB_dL]
    split_ifs
    · exact (genP_h13_zero hu hv _).1
    · exact (genP_h13_zero hu hv _).2
  obtain ⟨Q, -, hQ⟩ := Hrat_simple_poles_of_recursion hM hrec hP
  set PiL : Lt[X] := ∏ u ∈ Finset.Icc 1 M, (X - C (hL (u : ℤ) 1)) with hPiL
  have hPiB : PiL.map phiB = ∏ u ∈ Finset.Icc 1 M, (X - C (kacH (u : ℤ) 1 RatFunc.X)) := by
    rw [hPiL, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, phiB_hL]
  have hb := hAB phiB
  beta_reduce at hb
  rw [phiB_cL] at hb
  have h1 : (PiL * A).map phiB = C ((k : ℕ) : RatFunc ℚ) * Q * B.map phiB := by
    apply hinj
    rw [Polynomial.map_mul, hPiB, map_mul, ← hb, map_mul, map_mul, ← hQ, C_eq_natCast,
      map_natCast]
    ring
  have h2 : (PiL * A) %ₘ B = 0 := by
    apply Polynomial.map_injective phiB phiB_injective
    rw [map_modByMonic _ hB, Polynomial.map_zero, modByMonic_eq_zero_iff_dvd (hB.map phiB), h1]
    exact Dvd.intro_left _ rfl
  have h3 : PiL * A = B * ((PiL * A) /ₘ B) := by
    have := modByMonic_add_div (PiL * A) B
    rw [h2, zero_add] at this
    exact this.symm
  set q := (PiL * A) /ₘ B with hq
  -- back over `ℚ(t)`
  have ht := hAB phiT1
  beta_reduce at ht
  have hBne : alg (B.map phiT1) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    exact (hB.map phiT1).ne_zero
  have h4 : (k : RatFunc (RatFunc ℚ)) * alg (PiL.map phiT1) *
      Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M = alg (q.map phiT1) := by
    have h5 : alg ((PiL * A).map phiT1) = alg ((B * q).map phiT1) := by rw [h3]
    rw [Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul, ← ht] at h5
    have h6 : phiT1 cL = cT (RatFunc.X : RatFunc ℚ) := rfl
    have h7 : phiT1 (dL ν) = d13 ν := rfl
    rw [h6, h7] at h5
    apply mul_right_cancel₀ hBne
    linear_combination h5
  have hPiT : alg (PiL.map phiT1) =
      ∏ u ∈ Finset.Icc 1 M, (RatFunc.X - RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))) := by
    rw [hPiL, Polynomial.map_prod, map_prod]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, map_sub, halg, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C]
    rfl
  -- the prefactor
  have hk' : ((k : ℕ) : RatFunc (RatFunc ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hcl : clearedH ν M =
      alg ((C (algebraMap ℚ Lt ((M.factorial : ℚ) * 2 ^ M / k) * tL ^ (2 * M)) * q).map phiT1) := by
    have h8 : phiT1 (algebraMap ℚ Lt ((M.factorial : ℚ) * 2 ^ M / k) * tL ^ (2 * M)) =
        RatFunc.C ((M.factorial : ℚ) * 2 ^ M / k) * (RatFunc.X : RatFunc ℚ) ^ (2 * M) := by
      have e0 : ∀ r : ℚ, algebraMap ℚ (RatFunc ℚ) r = RatFunc.C r := fun r =>
        (eq_ratCast (algebraMap ℚ (RatFunc ℚ)) r).trans (eq_ratCast RatFunc.C r).symm
      rw [map_mul, map_pow, RingHom.map_rat_algebraMap, e0]
      rfl
    have h9 : (∏ u ∈ Finset.Icc 1 M,
        (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ)))) =
        2 ^ M * ∏ u ∈ Finset.Icc 1 M,
          (RatFunc.X - RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))) := by
      have : ∀ u : ℕ, (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))) =
          2 * (RatFunc.X - RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))) := fun u => by ring
      simp only [this]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
      simp
    have hkq : ((k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk
    have e1 : (RatFunc.C (RatFunc.C ((M.factorial : ℚ) * 2 ^ M / k) : RatFunc ℚ) :
          RatFunc (RatFunc ℚ)) * (k : RatFunc (RatFunc ℚ)) =
        (M.factorial : RatFunc (RatFunc ℚ)) * 2 ^ M := by
      have e2 : ((k : ℕ) : RatFunc (RatFunc ℚ)) = RatFunc.C (RatFunc.C ((k : ℕ) : ℚ)) := by
        rw [map_natCast, map_natCast]
      rw [e2, ← map_mul, ← map_mul, div_mul_cancel₀ _ hkq, map_mul, map_mul, map_pow, map_pow,
        map_natCast, map_natCast, map_ofNat, map_ofNat]
    have hc0 : clearedH ν M = (M.factorial : RatFunc (RatFunc ℚ)) *
        RatFunc.C (RatFunc.X : RatFunc ℚ) ^ (2 * M) *
        (∏ u ∈ Finset.Icc 1 M,
          (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ)))) *
        Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M := rfl
    rw [Polynomial.map_mul, map_C, h8, map_mul, ← h4, hPiT, halg, RatFunc.algebraMap_C, map_mul,
      map_pow, hc0, h9]
    linear_combination (-(RatFunc.C (RatFunc.X : RatFunc ℚ) ^ (2 * M) *
      (∏ u ∈ Finset.Icc 1 M, (RatFunc.X - RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ)))) *
      Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M)) * e1
  rw [hcl]
  exact laurent_psi _

end Virasoro
