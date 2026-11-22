import Virasoro.Proofs.Sec6H13Integral
import Virasoro.Proofs.Sec6H13Comb
import Virasoro.Proofs.Sec6H13DegRed

/-!
# Proposition 6.8: clause (i) and the reduction of clause (ii) (paper.tex l.1178–1416)

Clause (i) is proved (`sub_h13_integral`, with `sub_h13_polynomial`, `sub_h13_values`); clause (iii)
is proved from clauses (i) and (ii) (`sub_h13_valuation`, `sub_h13_lipschitz`); clause (ii) is
reduced to the terms of the expansion of `R_M` (`Stmt_sub_h13_degree_chain`, l.1304–1378).
-/

namespace Virasoro

/-- Proposition 6.8(i), integrality: `P_M^{(ν)} ∈ ℤ[1/2][t,Y]` (paper.tex l.1261–1291). -/
theorem sub_h13_integral (hK : Cited_KacDeterminant) : Stmt_sub_h13_integral :=
  sub_h13_integral_of hK sub_h13_lagrange sub_h13_detD

example (hK : Cited_KacDeterminant) : Stmt_sub_h13_integral := sub_h13_integral hK

/-- Proposition 6.8 from clause (ii) (`Stmt_sub_h13_degree`, l.1293–1378). -/
theorem prop_h13_nonvanishing_of_degree (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (h2 : Stmt_sub_h13_degree) : Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_comb hK hH sub_h13_lagrange sub_h13_detD h2

/-- Proposition 6.8 from the terms of the expansion of `R_M` (`Stmt_sub_h13_degree_chain`,
l.1304–1378). -/
theorem prop_h13_nonvanishing_of_chain (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (h : Stmt_sub_h13_degree_chain) :
    Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_degree hK hH (sub_h13_degree_of_chain h)

end Virasoro
