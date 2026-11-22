import Virasoro.Proofs.Sec6H13Assembly
import Virasoro.Proofs.Sec6H13TFinal

/-!
# Proposition 6.8 of `paper.tex` at 70bac53

`prop:h13-nonvanishing` (paper.tex l.1178–1416): clause (i) (`sub_h13_integral`), clause (ii)
from the terms of the expansion of `R_M` (`H13T.sub_h13_degree_chain`, l.1304–1378) and clause
(iii) from (i) and (ii).  The inputs are the cited Kac determinant formula and the cited
normalizations of the singular vectors.
-/

namespace Virasoro

/-- Proposition 6.8 (paper.tex l.1178–1416).
Paper label: prop:h13-nonvanishing -/
theorem prop_h13_nonvanishing_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_chain hK hH H13T.sub_h13_degree_chain

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_cited hK hH

end Virasoro
