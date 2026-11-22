import Virasoro.Sphere.Proofs.Sec3LamData

/-!
# Sphere paper Lemma 3.3: parts (i), (ii) and the reduction of (iii)

sphere/paper.tex l.506–711.  Parts (i) and (ii) of Lemma 3.3 are proved
(`sub_lam_ward`, `sub_lam_regular`, `sub_lam_order_zero`, `sub_lam_orders`); the lemma follows
from them and the Gaussian evaluation of part (iii), `Stmt_sub_lam_limit` (l.637–711).
-/

namespace Virasoro.Sphere

/-- Lemma 3.3 from its part (iii) (the limit (3.5) at the saddle point, l.637–711), with the
cited inputs of Lemma 3.2 and of Lemma 3.4. -/
theorem lem_lambda_expansion_of_limit (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ2 : Cited_JacobiIdentities2) (h5 : Stmt_sub_lam_limit) :
    Stmt_lem_lambda_expansion :=
  lem_lambda_expansion_of_steps hJ2 (sub_lam_ward hF hK) sub_lam_regular sub_lam_order_zero
    (sub_lam_orders hF hK) h5

example (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ2 : Cited_JacobiIdentities2) (h5 : Stmt_sub_lam_limit) : Stmt_lem_lambda_expansion :=
  lem_lambda_expansion_of_limit hF hK hJ2 h5

end Virasoro.Sphere

