import Virasoro.Proofs.P2Sec13VermaLimit
import Virasoro.Proofs.P2Sec13BoxLimit

/-!
# Lemma 13.1 from Steps 2–4 (paper.tex l.2869–3037)

Step 1 (equation (13.2)), the limits of the Verma terms and of the box ratio are proved; the
lemma is reduced to `Stmt_sub_tau_trace_limit` (Steps 2–4, l.2906–3028).
-/

namespace Virasoro.P2

open Virasoro

/-- Lemma 13.1 from the limit of the trace on the generic irreducible quotient (Steps 2–4). -/
theorem lem_degenerate_quotient_t_of_trace (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective)
    (hT : Stmt_sub_tau_trace_limit) : Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_limits hK hE hH hU hF hI (sub_tau_verma_limit_of_cited hK hH)
    sub_tau_box_limit hT

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) (hT : Stmt_sub_tau_trace_limit) :
    Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_trace hK hE hH hU hF hI hT

end Virasoro.P2
