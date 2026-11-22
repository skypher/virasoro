import Virasoro.Proofs.P2Sec9OrbitReg
import Virasoro.Proofs.P2Sec9PoleOut
import Virasoro.Proofs.P2Sec9IrrTrace

/-!
# Theorem 9.1 (fusion-descent and exact Verma regularity), paper.tex l.1836–1869, proof l.2554–2606

Assembly of `thm_descent_regularity_of_subs` with Lemma 11.3 and the three steps
`sub_irr_trace_unique`, `sub_pole_outside`, `sub_orbit_regular`.
-/

namespace Virasoro

/-- Paper label: thm:descent-regularity -/
theorem thm_descent_regularity_of_cited (hJ : Cited_JantzenLayersOrbit)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hK : Cited_KacDeterminant) (hI : Cited_VermaHomInjective) : Stmt_thm_descent_regularity :=
  thm_descent_regularity_of_subs hJ hH hU hF (lem_joint_holomorphicity_of_cited hK hH)
    sub_irr_trace_unique (sub_pole_outside hJ hI hH hU) (sub_orbit_regular hK hH)

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hK : Cited_KacDeterminant)
    (hI : Cited_VermaHomInjective) : Stmt_thm_descent_regularity :=
  thm_descent_regularity_of_cited hJ hH hU hF hK hI

end Virasoro
