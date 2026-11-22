import Virasoro.Proofs.Sec6LimGr10
import Virasoro.Proofs.Sec6ChainEvalFinal
import Virasoro.Proofs.GenericH

/-!
# Proposition 6.7 of `paper.tex` at 70bac53

`prop:layer-coefficients` (paper.tex l.1115–1173) from its two parts: the chain limit
(`ChainLim.sub_layer_chain_limit`, l.1135–1148) and the evaluation of the limit
(`sub_layer_chain_eval`, l.1150–1173).  The inputs are the cited Kac determinant formula, the
cited normalizations of the singular vectors (through the generic recursion of Proposition 6.4) and
the cited injectivity of the singular embedding.
-/

namespace Virasoro

/-- Proposition 6.7 (paper.tex l.1115–1173).
Paper label: prop:layer-coefficients -/
theorem prop_layer_coefficients_of_cited (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_layer_coefficients :=
  prop_layer_coefficients_of_limit hI
    (ChainLim.sub_layer_chain_limit (genericRecursionUniform hK hH) hK)

example (hI : Cited_VermaHomInjective) (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_prop_layer_coefficients :=
  prop_layer_coefficients_of_cited hI hK hH

end Virasoro
