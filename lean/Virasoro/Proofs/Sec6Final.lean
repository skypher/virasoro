import Virasoro.Proofs.GenericH
import Virasoro.Proofs.Sec4PFKac
import Virasoro.Proofs.Sec11

/-!
# Proposition 6.5 and its consequences, from the cited literature only

With the generic recursion proved from the Kac determinant formula and the imported
normalization identities, Proposition 6.5, Theorem 4.3, Corollary 4.4, Corollary 7.6 and
Proposition 11.1 depend only on these two cited results.
-/

namespace Virasoro

/-- Proposition 6.5 (`prop:generic-recursion`), from the Kac determinant formula and the
imported normalization identities. -/
theorem prop_generic_recursion (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_generic_recursion :=
  prop_generic_recursion_of_uniform (genericRecursionUniform hK hH)

/-- Theorem 4.3 (`thm:general-confluence`), from the two cited results. -/
theorem thm_general_confluence_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_thm_general_confluence :=
  thm_general_confluence (genericRecursionUniform hK hH)

/-- Corollary 4.4 (`cor:ising-confluence`), from the two cited results. -/
theorem cor_ising_confluence_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_cor_ising_confluence :=
  cor_ising_confluence (genericRecursionUniform hK hH)

/-- Corollary 7.6 (`cor:class-regular`), from the two cited results. -/
theorem cor_class_regular_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_cor_class_regular :=
  cor_class_regular (genericRecursionUniform hK hH)

/-- Proposition 11.1 (`prop:identity-verma`), from the two cited results. -/
theorem prop_identity_verma_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_prop_identity_verma :=
  prop_identity_verma (genericRecursionUniform hK hH)

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_generic_recursion := prop_generic_recursion hK hH

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_thm_general_confluence := thm_general_confluence_of_cited hK hH

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_cor_ising_confluence := cor_ising_confluence_of_cited hK hH

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_cor_class_regular := cor_class_regular_of_cited hK hH

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_identity_verma := prop_identity_verma_of_cited hK hH

end Virasoro
