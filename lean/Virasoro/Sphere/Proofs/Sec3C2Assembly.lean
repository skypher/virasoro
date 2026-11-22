import Virasoro.Sphere.Proofs.Sec3C2Wick
import Virasoro.Sphere.Proofs.Sec3C2Step3Subs

/-!
# Lemma 3.7, Steps 1–3: what is proved (sphere paper)

sphere/paper.tex l.1029–1156.  Steps 1 and 2 are proved; Step 3 is reduced to
`Stmt_sub_c2_diag` (l.1111–1149) and `Stmt_sub_c2_diag_norm` (l.1150–1156).
-/

namespace Virasoro.Sphere

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- Lemma 3.7, Step 2 (sphere/paper.tex l.1073–1109). -/
theorem sub_c2_step2 : Stmt_sub_c2_step2 :=
  sub_c2_step2_of hF (sub_c2_primaries hF hK) sub_c2_wick

include hF hK in
/-- Steps 1–2 of the proof of Lemma 3.7 with Step 3 give `Stmt_sub_c2_decomp`. -/
theorem sub_c2_decomp_of_step3 (h3 : Stmt_sub_c2_step3) : Stmt_sub_c2_decomp :=
  sub_c2_decomp_of_steps (sub_c2_step1 hF hK) (sub_c2_step2 hF hK) h3

include hF hK in
theorem sub_c2_decomp_of_diag (h1 : Stmt_sub_c2_diag) (h2 : Stmt_sub_c2_diag_norm) :
    Stmt_sub_c2_decomp :=
  sub_c2_decomp_of_step3 hF hK (sub_c2_step3_of h1 h2)

end Virasoro.Sphere
