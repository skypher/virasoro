import Virasoro.Proofs.Germs
import Virasoro.Proofs.GenPZero

/-!
# Proposition 6.7, the chain limit (a): `φ(x)` at the germ `b = b⋆ + t` (paper.tex l.1127–1131)

`φ(x,y) = xb + yb⁻¹`.  At `b⋆` with `p b⋆² + p' = 0` (that is `ν⋆ = −p'/p`), `φ(x)(b⋆) = 0` exactly
for `x ∈ ℤ(p,p')`; there the zero is simple: `φ(jp,jp')(b⋆ + t)/t → 2jp`.
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries

variable {K : Type} [Field K] [CharZero K]

/-- The uniformizer `t` of `K⸨X⸩`. -/
noncomputable abbrev tX : K⸨X⸩ := HahnSeries.single (1 : ℤ) (1 : K)

theorem tX_ne_zero : (tX : K⸨X⸩) ≠ 0 := by
  simp [tX, HahnSeries.single_eq_zero_iff]

omit [CharZero K] in
theorem bGerm_eq (bs : K) : bGerm bs = HahnSeries.C bs + tX := by
  rw [bGerm]

omit [CharZero K] in
theorem bGerm_ne_zero {bs : K} (hbs : bs ≠ 0) : bGerm bs ≠ 0 := by
  intro h
  have := bGerm_coeff_zero bs
  rw [h] at this
  exact hbs (by simpa using this.symm)

omit [CharZero K] in
theorem regVal_phiL {bs : K} (hbs : bs ≠ 0) (x : ℤ × ℤ) :
    RegVal (phiL (bGerm bs) x) (phiL bs x) := by
  have hb := regVal_bGerm bs
  exact ((regVal_intCast x.1).mul hb).add ((regVal_intCast x.2).mul (hb.inv hbs))

/-- `φ(jp,jp')(b⋆ + t) = t · j(2pb⋆ + pt)/(b⋆ + t)` when `p b⋆² + p' = 0`. -/
theorem phiL_germ_mult {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hrel : (p : K) * bs ^ 2 + p' = 0)
    (j : ℤ) :
    phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) =
      tX * ((j : K⸨X⸩) * (2 * (p : K⸨X⸩) * HahnSeries.C bs + (p : K⸨X⸩) * tX) *
        (bGerm bs)⁻¹) := by
  have hb := bGerm_ne_zero hbs
  have hrel' : (p : K⸨X⸩) * HahnSeries.C bs ^ 2 + (p' : K⸨X⸩) = 0 := by
    have := congrArg (HahnSeries.C (Γ := ℤ) (R := K)) hrel
    simpa [map_add, map_mul, map_pow, map_natCast] using this
  unfold phiL
  rw [bGerm_eq] at hb ⊢
  field_simp
  push_cast
  linear_combination (j : K⸨X⸩) * hrel'

/-- The simple zero: `φ(jp,jp')(b⋆ + t)/t` is regular with value `2jp`. -/
theorem regVal_phiL_mult_div {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hrel : (p : K) * bs ^ 2 + p' = 0)
    (j : ℤ) :
    RegVal (phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) / tX) (2 * (j : K) * (p : K)) := by
  rw [phiL_germ_mult hbs hrel j, mul_div_cancel_left₀ _ tX_ne_zero]
  have hb := regVal_bGerm (K := K) bs
  have ht : RegVal (tX : K⸨X⸩) 0 := by
    refine ⟨ordGE_single_one, ?_⟩
    simp [tX]
  have h1 := ((regVal_intCast j).mul ((((regVal_ofNat 2).mul (regVal_natCast p)).mul
    (regVal_C bs)).add ((regVal_natCast p).mul ht))).mul (hb.inv hbs)
  convert h1 using 1
  field_simp
  ring

omit [CharZero K] in
/-- `φ(x)(b⋆) = 0` exactly on `ℤ(p,p')`: `φ(x)(b⋆) = (p x₂ − p' x₁)/(p b⋆)`. -/
theorem phiL_star {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0)
    (hrel : (p : K) * bs ^ 2 + p' = 0) (x : ℤ × ℤ) :
    phiL bs x = (((p : ℤ) * x.2 - (p' : ℤ) * x.1 : ℤ) : K) / ((p : K) * bs) := by
  unfold phiL
  field_simp
  push_cast
  linear_combination (x.1 : K) * hrel

theorem phiL_star_ne {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0)
    (hrel : (p : K) * bs ^ 2 + p' = 0) {x : ℤ × ℤ} (hx : (p : ℤ) * x.2 ≠ (p' : ℤ) * x.1) :
    phiL bs x ≠ 0 := by
  rw [phiL_star hbs hp hrel]
  refine div_ne_zero ?_ (mul_ne_zero hp hbs)
  exact Int.cast_ne_zero.2 (sub_ne_zero.2 hx)

end Virasoro.ChainLim
