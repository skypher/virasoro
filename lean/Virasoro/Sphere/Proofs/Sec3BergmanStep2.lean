import Virasoro.Sphere.Proofs.Sec3BergmanLiouville
import Virasoro.Sphere.Proofs.Sec3BergmanHolo
import Virasoro.Sphere.Proofs.Sec3BergmanInner

/-!
# Sphere paper Lemma 3.5, Steps 1–2 (`sphere/paper.tex` l.867–929)

The formula `W = S/(Y₁Y₂(x₁-x₂)²) + 2C(z)/(Y₁Y₂)` for some `C(z)`, from the holomorphy of the
coefficients of `W_no`, the inner patch, the outer patch, Liouville's theorem and the symmetry of
`W`.

Consumer: `Stmt_lem_bergman_det`.
-/

namespace Virasoro.Sphere

/-- Lemma 3.5, Steps 1–2 (sphere/paper.tex l.867–929). -/
theorem sub_bergman_liouville : Stmt_sub_bergman_liouville :=
  sub_bergman_liouville_of_patches sub_bergman_holo sub_bergman_inner sub_bergman_outer

/-- Lemma 3.5 from the cited Jacobi identity and the zero-mode condition of Step 3. -/
theorem lem_bergman_det_of_zero_mode (hJ2 : Cited_JacobiIdentities2)
    (hZ : Stmt_sub_bergman_zero_mode) : Stmt_lem_bergman_det :=
  lem_bergman_det_of_liouville_zero_mode hJ2 sub_bergman_liouville hZ

end Virasoro.Sphere
