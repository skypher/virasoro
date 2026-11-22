import Virasoro.Cited2
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.P2Sec10FusRoots

/-!
# Proposition 10.2 (singular vectors and fusion polynomials), paper.tex l.2115–2160

Part (i) and the factorization (10.8) are cited in the paper (l.2149–2155); the root list
(10.10) is `fusP_roots`.
-/

namespace Virasoro

open Polynomial

/-- A coordinate in `ℚ[b²,b⁻²]` is regular at every `b₁ ≠ 0` (l.2120–2122). -/
theorem laurent_regular {x : RatFunc ℚ} {f : ℚ[X]} {n : ℕ}
    (hx : x = Polynomial.aeval ((RatFunc.X : RatFunc ℚ) ^ 2) f / RatFunc.X ^ (2 * n))
    {b₁ : ℂ} (hb : b₁ ≠ 0) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom x) ≠ 0 := by
  have e : x = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.aeval (X ^ 2 : ℚ[X]) f) /
      algebraMap ℚ[X] (RatFunc ℚ) (X ^ (2 * n)) := by
    rw [hx, ← Polynomial.aeval_algebraMap_apply, map_pow, map_pow, RatFunc.algebraMap_X]
  rw [e]
  refine eval₂_ne_of_dvd (RatFunc.denom_div_dvd _ _) ?_
  rw [eval₂_pow, eval₂_X]
  exact pow_ne_zero _ hb

/-- Proposition 10.2 from the cited inputs of its proof: the normalized singular vector over
`ℚ(b)` (Kac, Feigin–Fuchs, Iohara–Koga), its Laurent coefficients (Astashkevich) and
Zamolodchikov's fusion polynomial.
Paper label: prop:fusion-poly -/
theorem prop_fusion_poly_of_cited (hH : Cited_HJSNormalizations)
    (hL : Cited_SingularFamilyLaurent) (hF : Cited_FusionPolynomial) :
    Stmt_prop_fusion_poly := by
  intro R S hR hS
  obtain ⟨p, ⟨hp1, hsing⟩, huniq, -, -⟩ := hH R S hR hS
  have hlaur := hL R S hR hS p hp1 hsing
  refine ⟨p, ⟨hp1, hsing⟩, huniq, hlaur, fun b₁ hb => ?_⟩
  have hreg : ∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (p Y)) ≠ 0 := by
    intro Y
    obtain ⟨f, n, hf⟩ := hlaur Y
    exact laurent_regular hf hb
  have hone : RatFunc.eval (algebraMap ℚ ℂ) b₁ (p (onesPartition (R * S))) = 1 := by
    rw [hp1]; simp
  have hs1 := (specialize_singular (evTo_kacC hb) (evTo_kacH hb R S) p hreg hsing
    ⟨onesPartition (R * S), by rw [hone]; exact one_ne_zero⟩).1
  exact ⟨hreg, hF R S hR hS b₁ hb _ hone hs1, fun d => fusP_roots R S b₁ d⟩

example (hH : Cited_HJSNormalizations) (hL : Cited_SingularFamilyLaurent)
    (hF : Cited_FusionPolynomial) : Stmt_prop_fusion_poly :=
  prop_fusion_poly_of_cited hH hL hF

end Virasoro
