import Virasoro.Proofs.Sec6H13Assembly
import Virasoro.Proofs.Sec6H13TFinal
import Virasoro.Proofs.Prop92AppA

/-!
# Proposition 9.2 of `paper.tex` (`prop:h13-nonvanishing`, l.1616–1694)

The proof follows the paper: parts (i)–(ii) from Lemmas A.1–A.3 of Appendix A (l.3104–3161,
`prop_h13_nonvanishing_of_appA`), parts (iii)–(iv) from (i)–(ii).  The inputs are the cited Kac
determinant formula and the cited normalizations of the singular vectors.  The earlier route
through the terms of the expansion of `R_M` (`prop_h13_nonvanishing_of_chain`) stays in the library.
-/

namespace Virasoro

/-- Proposition 9.2 (paper.tex l.1616–1694, proof of (i)–(ii) l.3104–3161).
Paper label: prop:h13-nonvanishing -/
theorem prop_h13_nonvanishing_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_appA hK hH lem_mode_count (AppA2.lem_odd_primes_of_cited hK)
    lem_level_poly

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_cited hK hH

end Virasoro
