import Virasoro.Proofs.Sec6TTCase3
import Virasoro.Proofs.Sec6H13Label
import Virasoro.Proofs.Sec6LayerFinal

/-!
# Proposition 6.9 and Corollary 5.10 of `paper.tex` at 70bac53

`prop:two-term-criteria` (paper.tex l.1419–1565): `P_N ≢ 0` on every two-vector level and the
pole of order exactly `k`.  The proof (l.1428–1565) is `TT.core_all` (Cases 1–3) through the
rational model `TT.two_term_odd_of_core` and the reduction `b ↦ b⁻¹`.  Inputs: the cited
injectivity of the singular embedding, the Kac determinant formula, the normalizations of the
singular vectors and the uniqueness of singular vectors (Iohara–Koga, Proposition 5.1).

`cor:top-layer-sharp` (paper.tex l.892–917) from Theorem 5.8 (cited Jantzen layers), Theorem 5.9
and Propositions 6.7–6.9.
-/

namespace Virasoro

/-- Proposition 6.9 (paper.tex l.1419–1565).
Paper label: prop:two-term-criteria -/
theorem prop_two_term_criteria_of_cited (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) :
    Stmt_prop_two_term_criteria :=
  prop_two_term_criteria_of_sub hI (sub_two_term_nonzero_of_odd
    (TT.two_term_odd_of_core hI hH hU (prop_layer_coefficients_of_cited hI hK hH)
      (TT.core_all (prop_h13_nonvanishing_of_cited hK hH))))

/-- Corollary 5.10 (paper.tex l.892–917).
Paper label: cor:top-layer-sharp -/
theorem cor_top_layer_sharp_of_cited (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) :
    Stmt_cor_top_layer_sharp :=
  cor_top_layer_sharp_of_props hJ hI (prop_layer_coefficients_of_cited hI hK hH)
    (prop_h13_nonvanishing_of_cited hK hH) (prop_two_term_criteria_of_cited hI hK hH hU)

example (hI : Cited_VermaHomInjective) (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) : Stmt_prop_two_term_criteria :=
  prop_two_term_criteria_of_cited hI hK hH hU

end Virasoro
