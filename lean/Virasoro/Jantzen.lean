import Virasoro.Block
import Virasoro.Smith
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Jantzen layers in the internal weight (paper Definition 5.5)
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The Shapovalov matrix `G_N(c, h + x)` over `K⟦X⟧`, in the local parameter `x`. -/
noncomputable def gramLocal (c h : K) (N : ℕ) :
    Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries K) :=
  gram (PowerSeries.C c) (PowerSeries.C h + PowerSeries.X) N

/-- The Shapovalov matrix `G_N(c, h + x)` over `K[x]`. -/
noncomputable def gramShift (c h : K) (N : ℕ) :
    Matrix (Nat.Partition N) (Nat.Partition N) K[X] :=
  gram (C c) (C h + X) N

/-- The Jantzen layer `J^i_N(c,h)` in Poincaré–Birkhoff–Witt coordinates (paper Definition 5.5):
the vectors `v` for which there is a polynomial family `v(x)` with `v(0) = v` and
`G_N(c, h + x) v(x) ∈ x^i K[x]^{p(N)}`. -/
noncomputable def jantzenLayer (c h : K) (N i : ℕ) : Submodule K (Nat.Partition N → K) where
  carrier := {v | ∃ w : Nat.Partition N → K[X], (∀ Y, (w Y).eval 0 = v Y) ∧
      ∀ Y, (X : K[X]) ^ i ∣ ((gramShift c h N).mulVec w) Y}
  add_mem' := by
    rintro v v' ⟨w, hw, hd⟩ ⟨w', hw', hd'⟩
    refine ⟨w + w', fun Y => by simp [hw, hw'], fun Y => ?_⟩
    rw [Matrix.mulVec_add]
    exact dvd_add (hd Y) (hd' Y)
  zero_mem' := ⟨0, fun Y => by simp, fun Y => by simp⟩
  smul_mem' := by
    rintro a v ⟨w, hw, hd⟩
    refine ⟨C a • w, fun Y => by simp [hw], fun Y => ?_⟩
    rw [Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hd Y) _

/-- The Jantzen layer `J^i(c,h) = ⨁_N J^i_N(c,h)` inside the Verma module `M(c,h)`. -/
noncomputable def jantzen (c h : K) (i : ℕ) : Submodule K (Verma K c h) :=
  ⨆ N : ℕ, (jantzenLayer c h N i).map (Verma.pbwCoord N)

end Virasoro
