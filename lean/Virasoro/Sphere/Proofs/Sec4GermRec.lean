import Virasoro.Sphere.Proofs.Sec4PolyU
import Virasoro.Sphere.Proofs.Sec4ImportedU
import Virasoro.Sphere.Proofs.Sec4GenericFinal

/-!
# Sphere paper Proposition 4.4 as an identity of rational functions of `b`

`sphere/paper.tex` l.1392–1393: the proof of Theorem 4.7 applies the generic recursion (4.3) to
the germ `b = b⋆ + t`.  The proof of Proposition 4.4 (l.1297–1319) holds over every field of
characteristic zero at every `b` that is a root of no nonzero polynomial over `ℚ`: the degree
bound `deg_Δ P_N < deg_Δ det G_N` of Theorem 3.1 is a statement about the polynomial
`P_N ∈ ℚ[c,Δ,Δ_i]`, and Proposition 4.3 is an identity of rational functions of `b`.
-/

namespace Virasoro.Sphere

open Polynomial

section Field

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- The point `(c,Δ₁,…,Δ₄)` of `𝔽⁵`. -/
def pt5U (c : 𝔽) (Δe : Fin 4 → 𝔽) : Fin 5 → 𝔽 := ![c, Δe 0, Δe 1, Δe 2, Δe 3]

/-- Evaluation of the parameters at `(c,Δ₁,…,Δ₄)`. -/
noncomputable def ev5U (c : 𝔽) (Δe : Fin 4 → 𝔽) : PA →+* 𝔽 :=
  (MvPolynomial.aeval (pt5U c Δe)).toRingHom

theorem aeval_vec6U (c : 𝔽) (Δe : Fin 4 → 𝔽) (Q : MvPolynomial (Fin 6) ℚ) :
    MvPolynomial.aeval (vec6U c Δe) Q =
      algebraMap 𝔽[X] (RatFunc 𝔽) ((tau Q).map (ev5U c Δe)) := by
  have h : (MvPolynomial.aeval (vec6U c Δe) : MvPolynomial (Fin 6) ℚ →ₐ[ℚ] RatFunc 𝔽).toRingHom =
      (algebraMap 𝔽[X] (RatFunc 𝔽)).comp ((mapRingHom (ev5U c Δe)).comp tau) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tau, ev5U, eq_ratCast, map_ratCast]
    · intro i
      fin_cases i <;>
        simp [vec6U, tau, ev5U, pt5U, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  exact DFunLike.congr_fun h Q

end Field

/-- Theorem 3.1 in its degree form (l.411–414), with one polynomial `P_N ∈ ℚ[c,Δ_i][Δ]` for all
fields of characteristic zero: `H_N det G_N = P_N` and `deg_Δ P_N < d_N`. -/
theorem hsph_poly_deg (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) {N : ℕ} (hN : 1 ≤ N) :
    ∃ U : PA[X], U.degree < (dN N : WithBot ℕ) ∧
      ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (c : 𝔽) (Δe : Fin 4 → 𝔽),
        Hsph c Δe N * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det =
          algebraMap 𝔽[X] (RatFunc 𝔽) (U.map (ev5U c Δe)) := by
  obtain ⟨Q, hQ⟩ := isPolyFamU_Hsph_det hK N
  refine ⟨tau Q, ?_, ?_⟩
  · rw [degree_lt_iff_coeff_zero]
    intro d hd
    refine PA_eq_zero _ fun c Δe => ?_
    obtain ⟨-, Q', hQ'⟩ := thm_large_delta_of_cited hF hK hJ1 hJ2 N
    obtain ⟨P, -, hP, hdeg⟩ := hQ' c Δe
    have h1 := hQ ℂ c Δe
    beta_reduce at h1
    rw [hP, aeval_vec6U] at h1
    have h2 : P = (tau Q).map (ev5U c Δe) := IsFractionRing.injective ℂ[X] (RatFunc ℂ) h1
    have h3 : ev5U c Δe = ev5 c Δe := rfl
    have h4 := hdeg hN
    rw [gramPoly_det_degree] at h4
    rw [← coeff_map, ← h3, ← h2]
    exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h4 (by exact_mod_cast hd))
  · intro 𝔽 _ _ c Δe
    have h1 := hQ 𝔽 c Δe
    beta_reduce at h1
    rw [h1, aeval_vec6U]

section Field

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- `H_N(c(b),Δ,Δ_i)`, `N ≥ 1`, is the sum of its principal parts at `Λ_N(b)`, over every field
of characteristic zero (Theorem 3.1 and the Kac determinant, l.1317–1318). -/
theorem isPoleSum_Hsph_field (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) {b : 𝔽} (hb : b ≠ 0)
    (Δe : Fin 4 → 𝔽) {N : ℕ} (hN : 1 ≤ N) : IsPoleSum (Lam N b) (Hsph (kacC b) Δe N) := by
  obtain ⟨U, hU, hH⟩ := hsph_poly_deg hF hK hJ1 hJ2 hN
  refine isPoleSum_Hsph hK hb Δe N (U.map (ev5U (kacC b) Δe)) (hH 𝔽 _ Δe) ?_
  calc (U.map (ev5U (kacC b) Δe)).degree ≤ U.degree := degree_map_le
    _ < (dN N : WithBot ℕ) := hU
    _ ≤ (gramPoly (kacC b) N).det.degree :=
      le_degree_of_ne_zero (gramPoly_det_coeff_ne_zero (kacC b) N)

/-- Genericity for the sphere recursion from the nonvanishing of the polynomials `m b² + n` and
of the denominators of the normalized singular vectors (Proposition 4.3 over `𝔽`). -/
theorem genericAtSph_of (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial)
    {N : ℕ} {b : 𝔽} (hb : b ≠ 0) (hS : ∀ P ∈ linPolys N, aeval b P ≠ 0)
    (hreg : ∀ a ∈ labels N, ∀ Y,
      Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom (normP hH a.1 a.2 Y)) ≠ 0) :
    GenericAtSph hH N b := by
  classical
  refine ⟨⟨hb, ?_, hreg⟩, ?_⟩
  · intro m n hm hn hmn h0
    have hmem : (C (m : ℚ) * X ^ 2 + C (n : ℚ) : ℚ[X]) ∈ linPolys N := by
      simp only [linPolys, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      rw [abs_le] at hm hn
      exact ⟨(m, n), ⟨⟨⟨hm.1, hm.2⟩, ⟨hn.1, hn.2⟩⟩, hmn⟩, rfl⟩
    apply hS _ hmem
    simp only [map_add, map_mul, map_pow, aeval_X, map_intCast]
    exact h0
  · intro a ha Δa Δb
    obtain ⟨ha1, ha2, -⟩ := mem_labels.1 ha
    obtain ⟨hp1, hps⟩ := normP_normalized hH ha1 ha2
    exact fus_at hFus ha1 ha2 _ hp1 hps hb (hreg a ha) Δa Δb

/-- The generic recursion (4.3) at every `b` of a field of characteristic zero that is a root
of no nonzero polynomial over `ℚ`. -/
theorem sph_recursion_of_transcendental (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) {b : 𝔽}
    (hb : ∀ P : ℚ[X], P ≠ 0 → aeval b P ≠ 0) (Δe : Fin 4 → 𝔽) {N : ℕ} (hN : 1 ≤ N) :
    Hsph (kacC b) Δe N =
      ∑ a ∈ labels N,
        RatFunc.C (Rsph a.1 a.2 b Δe) / (RatFunc.X - RatFunc.C (kacHL a b)) *
          RatFunc.C (evalAt (kacHL a b + (a.lvl : 𝔽)) (Hsph (kacC b) Δe (N - a.lvl))) := by
  have hb0 : b ≠ 0 := by
    intro h0
    refine hb X X_ne_zero ?_
    rw [aeval_X, h0]
  have hgen : GenericAtSph hH N b := genericAtSph_of hH hFus hb0
    (fun P hP => hb P (linPolys_ne_zero hP)) fun a _ Y => by
      rw [← aeval_def]
      exact hb _ (RatFunc.denom_ne_zero _)
  exact hgen.recursion hK Δe (isPoleSum_Hsph_field hF hK hJ1 hJ2 hb0 Δe hN)

end Field

end Virasoro.Sphere
