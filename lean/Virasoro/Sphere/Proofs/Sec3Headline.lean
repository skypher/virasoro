import Virasoro.Sphere.Proofs.Sec3C2DiagNorm
import Virasoro.Sphere.Proofs.Sec3C2Assembly
import Virasoro.Sphere.Proofs.Sec3CentralFinal
import Virasoro.Sphere.Proofs.Sec3RationalC
import Virasoro.Sphere.Proofs.Sec3LargeDelta

/-!
# Lemma 3.7, Lemma 3.3 and Theorem 3.1 (sphere paper)

sphere/paper.tex l.1013–1203.  Steps 1–3 of the proof of Lemma 3.7 give the `c = 2`
decomposition with its limit coefficients; Step 4 gives Lemma 3.7; Lemma 3.3(iii) and
Theorem 3.1 follow.
-/

namespace Virasoro.Sphere

/-- Steps 1–3 of the proof of Lemma 3.7 (sphere/paper.tex l.1029–1156). -/
theorem sub_c2_decomp (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) :
    Stmt_sub_c2_decomp :=
  sub_c2_decomp_of_diag hF hK (sub_c2_diag hF) sub_c2_diag_norm

/-- Lemma 3.7 (sphere/paper.tex l.1013–1181).
Paper label: lem:central-charge -/
theorem lem_central_charge_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_lem_central_charge :=
  lem_central_charge_of_c2 hF hK hJ1 hJ2 (sub_c2_decomp hF hK)

/-- Lemma 3.3 (sphere/paper.tex l.506–709).
Paper label: lem:lambda-expansion -/
theorem lem_lambda_expansion_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_lem_lambda_expansion :=
  lem_lambda_expansion_of_central hF hK hJ1 hJ2 (lem_central_charge_of_cited hF hK hJ1 hJ2)

/-- Theorem 3.1 (sphere/paper.tex l.406–415, proof l.1183–1203).
Paper label: thm:large-delta -/
theorem thm_large_delta_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_thm_large_delta :=
  thm_large_delta_of_central hF hK hJ1 hJ2 (lem_central_charge_of_cited hF hK hJ1 hJ2)

end Virasoro.Sphere
