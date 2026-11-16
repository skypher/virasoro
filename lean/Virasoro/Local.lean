import Mathlib.FieldTheory.Laurent
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Laurent expansion of a rational function at a point (paper Remark 2.5)

For a rational function `f` of `Δ` over a field `K` and a point `a : K`, `lcoeff f a n` is the
coefficient of `(Δ - a)^n` in the Laurent expansion of `f` at `a`.  The principal part
`PP_{Δ=a} f` is the sum of the negative-power terms, `Res_{Δ=a} f` is the coefficient of
`(Δ - a)⁻¹`, and the pole order is the largest `k` with a nonzero coefficient of `(Δ - a)^{-k}`.
-/

namespace Virasoro

open scoped LaurentSeries
open RatFunc

variable {K : Type*} [Field K]

/-- The Laurent expansion of `f` at `a`, in the variable `x = Δ - a`. -/
noncomputable def expandAt (f : RatFunc K) (a : K) : K⸨X⸩ :=
  algebraMap (RatFunc K) K⸨X⸩ (RatFunc.laurent a f)

/-- The coefficient of `(Δ - a)^n` in the Laurent expansion of `f` at `a`. -/
noncomputable def lcoeff (f : RatFunc K) (a : K) (n : ℤ) : K := (expandAt f a).coeff n

/-- The coefficient of `(Δ - a)^{-k}` in the Laurent expansion of `f` at `a`;
`ppCoeff f a 1 = Res_{Δ=a} f`. -/
noncomputable def ppCoeff (f : RatFunc K) (a : K) (k : ℕ) : K := lcoeff f a (-(k : ℤ))

/-- The order of the pole of `f` at `a` (zero if `f` is regular at `a`). -/
noncomputable def poleOrder (f : RatFunc K) (a : K) : ℕ := (-(expandAt f a).order).toNat

/-- The principal part `PP_{Δ=a} f = ∑_{k ≥ 1} ppCoeff f a k / (Δ - a)^k`. -/
noncomputable def PP (f : RatFunc K) (a : K) : RatFunc K :=
  ∑ k ∈ Finset.Icc 1 (poleOrder f a), RatFunc.C (ppCoeff f a k) / (RatFunc.X - RatFunc.C a) ^ k

end Virasoro
