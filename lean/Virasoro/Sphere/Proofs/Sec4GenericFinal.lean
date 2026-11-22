import Virasoro.Sphere.Proofs.Sec4GenericRec
import Virasoro.Sphere.Proofs.Sec4Imported
import Virasoro.Sphere.Proofs.Sec3Headline

/-!
# Sphere paper Proposition 4.4 (`prop:generic-recursion`)

`sphere/paper.tex` l.1284–1319.  The exceptional set is the set of complex roots of the
polynomials `m b² + n` over `ℚ` with small integer coefficients (the values where some
`h_a(b) - h_g(b)`, `h_a(b) + ℓ_a - h_g(b)` vanishes or `𝒜_a(b)` has a pole); the normalized
singular vectors are regular at every `b ≠ 0` (Proposition 4.3), and Theorem 3.1 gives
`deg_Δ P_N < deg_Δ det G_N`.
-/

namespace Virasoro.Sphere

open Polynomial

theorem linPolys_ne_zero {N : ℕ} {P : ℚ[X]} (hP : P ∈ linPolys N) : P ≠ 0 := by
  classical
  simp only [linPolys, Finset.mem_image, Finset.mem_filter] at hP
  obtain ⟨mn, ⟨-, hmn⟩, rfl⟩ := hP
  intro h0
  have h2 := congrArg (fun P : ℚ[X] => P.coeff 2) h0
  have h3 := congrArg (fun P : ℚ[X] => P.coeff 0) h0
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_zero] at h2 h3
  norm_num at h2 h3
  rcases hmn with h | h
  · exact h h2
  · exact h h3

/-- The normalized singular vector over `ℚ(b)` chosen by `normP`. -/
theorem normP_normalized (hN : NormalizationIdentities) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    normP hN r s (onesPartition (r * s)) = 1 ∧
      Verma.IsSingular
        (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
          (r * s) (normP hN r s)) (r * s) := by
  have hdef : normP hN r s = Classical.choose (normalization_at hN r s hr hs) := by
    unfold normP
    rw [dif_pos ⟨hr, hs⟩]
  rw [hdef]
  exact (Classical.choose_spec (normalization_at hN r s hr hs)).1

/-- Over `ℂ`, a nonzero `b` that is a root of none of the polynomials `m X² + n` is generic for
the sphere recursion (Proposition 4.3 supplies regularity and the fusion polynomial). -/
theorem genericAtSph_complex (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial)
    {N : ℕ} {b : ℂ} (hb : b ≠ 0) (hS : ∀ P ∈ linPolys N, aeval b P ≠ 0) :
    GenericAtSph hH N b := by
  classical
  refine ⟨⟨hb, ?_, ?_⟩, ?_⟩
  · intro m n hm hn hmn h0
    have hmem : (C (m : ℚ) * X ^ 2 + C (n : ℚ) : ℚ[X]) ∈ linPolys N := by
      simp only [linPolys, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      rw [abs_le] at hm hn
      exact ⟨(m, n), ⟨⟨⟨hm.1, hm.2⟩, ⟨hn.1, hn.2⟩⟩, hmn⟩, rfl⟩
    apply hS _ hmem
    simp only [map_add, map_mul, map_pow, aeval_X, map_intCast]
    exact h0
  · intro a ha
    obtain ⟨ha1, ha2, -⟩ := mem_labels.1 ha
    obtain ⟨hp1, hps⟩ := normP_normalized hH ha1 ha2
    exact (lem_regular_everywhere_of_cited hH a.1 a.2 ha1 ha2 _ hp1 hps b hb).1
  · intro a ha Δa Δb
    obtain ⟨ha1, ha2, -⟩ := mem_labels.1 ha
    obtain ⟨hp1, hps⟩ := normP_normalized hH ha1 ha2
    obtain ⟨p, -, huniq, -, -, hev⟩ := prop_imported_of_cited hH hFus a.1 a.2 ha1 ha2
    rw [huniq _ hp1 hps]
    exact (hev b hb).2 Δa Δb

/-- Proposition 4.4, from Theorem 3.1, the Kac determinant formula and Proposition 4.3.

Paper label: prop:generic-recursion -/
theorem prop_generic_recursion_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) :
    Stmt_prop_generic_recursion := by
  classical
  intro N hN1
  have hroot : ∀ (P : ℚ[X]) (x : ℂ), P ∈ linPolys N →
      (x ∈ (P.map (algebraMap ℚ ℂ)).roots.toFinset ↔ aeval x P = 0) := by
    intro P x hP
    have h0 : P.map (algebraMap ℚ ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 (linPolys_ne_zero hP)
    rw [Multiset.mem_toFinset, mem_roots h0, IsRoot.def, eval_map, ← aeval_def]
  refine ⟨(linPolys N).biUnion fun P => (P.map (algebraMap ℚ ℂ)).roots.toFinset, ?_, ?_⟩
  · intro x hx
    obtain ⟨P, hP, hx⟩ := Finset.mem_biUnion.1 hx
    exact ⟨P, linPolys_ne_zero hP, (hroot P x hP).1 hx⟩
  · intro b hb hbE Δe
    have hgen : GenericAtSph hH N b := genericAtSph_complex hH hFus hb fun P hP h0 =>
      hbE (Finset.mem_biUnion.2 ⟨P, hP, (hroot P b hP).2 h0⟩)
    obtain ⟨-, Q, hQ⟩ := thm_large_delta_of_cited hF hK hJ1 hJ2 N
    obtain ⟨P, -, hP, hdeg⟩ := hQ (kacC b) Δe
    exact hgen.recursion hK Δe (isPoleSum_Hsph hK hb Δe N P hP (hdeg hN1))

example (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) :
    Stmt_prop_generic_recursion := prop_generic_recursion_of_cited hF hK hJ1 hJ2 hH hFus

end Virasoro.Sphere
