import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.CharP.Algebra

/-!
# Shared instances
-/

namespace Virasoro

open scoped LaurentSeries

/-- Laurent series over a field of characteristic zero have characteristic zero. -/
instance instCharZeroLaurent {K : Type*} [Field K] [CharZero K] : CharZero K⸨X⸩ :=
  charZero_of_injective_algebraMap (R := K) (A := K⸨X⸩) (algebraMap K K⸨X⸩).injective

end Virasoro
