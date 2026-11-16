import Virasoro.Proofs.TwoBranchB

/-!
# Proposition 7.7, third part: the expansion of `B_{κ,N}(t)`

`B_{κ,N}(t) = f(0)/(ζ̇ t) + R_κ(0) Q + T + O(t)` with `f = R_κ R_τ`, from
`S_{κ,M}(t) = R_τ(t)/ζ(t) + Q + O(t)` and the expansions `f = f(0) + ḟ t + O(t²)`,
`ζ = ζ̇ t + ζ̈ t²/2 + O(t³)`.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

section Laurent

variable {K : Type*} [Field K]

theorem ordGE_single (n : ℤ) (r : K) : OrdGE (HahnSeries.single n r : K⸨X⸩) n :=
  ordGE_iff.2 fun _ hm => HahnSeries.coeff_single_of_ne (ne_of_lt hm)

/-- The two lowest coefficients of a product of Laurent series. -/
theorem coeff_mul_two {x y : K⸨X⸩} {a b : ℤ} (hx : OrdGE x a) (hy : OrdGE y b) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b ∧
      (x * y).coeff (a + b + 1) = x.coeff a * y.coeff (b + 1) + x.coeff (a + 1) * y.coeff b := by
  set x' : K⸨X⸩ := HahnSeries.single a (x.coeff a) + HahnSeries.single (a + 1) (x.coeff (a + 1))
    with hx'
  set y' : K⸨X⸩ := HahnSeries.single b (y.coeff b) + HahnSeries.single (b + 1) (y.coeff (b + 1))
    with hy'
  have hy'o : OrdGE y' b := (ordGE_single b _).add ((ordGE_single (b + 1) _).mono (by omega))
  have hxx : ∀ n : ℤ, n ≤ a + b + 1 - b → x'.coeff n = x.coeff n := by
    intro n hn
    rw [hx', HahnSeries.coeff_add]
    rcases lt_trichotomy n a with h | h | h
    · rw [HahnSeries.coeff_single_of_ne (by omega), HahnSeries.coeff_single_of_ne (by omega),
        hx.coeff_eq_zero h, add_zero]
    · subst h
      rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne (by omega), add_zero]
    · have : n = a + 1 := by omega
      subst this
      rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne (by omega), zero_add]
  have hyy : ∀ n : ℤ, n ≤ a + b + 1 - a → y'.coeff n = y.coeff n := by
    intro n hn
    rw [hy', HahnSeries.coeff_add]
    rcases lt_trichotomy n b with h | h | h
    · rw [HahnSeries.coeff_single_of_ne (by omega), HahnSeries.coeff_single_of_ne (by omega),
        hy.coeff_eq_zero h, add_zero]
    · subst h
      rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne (by omega), add_zero]
    · have : n = b + 1 := by omega
      subst this
      rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne (by omega), zero_add]
  have key := coeff_mul_congr (A := x) (A' := x') (S := y) (S' := y') (a := a) (s := b)
    (U := a + b + 1) hx hy'o hxx hyy
  have hprod : x' * y' = HahnSeries.single (a + b) (x.coeff a * y.coeff b)
      + HahnSeries.single (a + (b + 1)) (x.coeff a * y.coeff (b + 1))
      + (HahnSeries.single (a + 1 + b) (x.coeff (a + 1) * y.coeff b)
        + HahnSeries.single (a + 1 + (b + 1)) (x.coeff (a + 1) * y.coeff (b + 1))) := by
    rw [hx', hy', add_mul, mul_add, mul_add, HahnSeries.single_mul_single,
      HahnSeries.single_mul_single, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
  constructor
  · rw [← key (a + b) (by omega), hprod]
    simp only [HahnSeries.coeff_add]
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_of_ne (by omega),
      HahnSeries.coeff_single_of_ne (by omega), HahnSeries.coeff_single_of_ne (by omega)]
    ring
  · rw [← key (a + b + 1) le_rfl, hprod]
    simp only [HahnSeries.coeff_add]
    rw [HahnSeries.coeff_single_of_ne (by omega),
      show a + b + 1 = a + (b + 1) by ring, HahnSeries.coeff_single_same,
      show a + (b + 1) = a + 1 + b by ring, HahnSeries.coeff_single_same,
      HahnSeries.coeff_single_of_ne (by omega)]
    ring

/-- The expansion of `f/ζ` for `f` regular and `ζ` with a simple zero at `t = 0`. -/
theorem coeff_div_simple_zero {f ζ : K⸨X⸩} (hf : OrdGE f 0)
    (hζ : ζ.orderTop = ((1 : ℤ) : WithTop ℤ)) :
    OrdGE (f / ζ) (-1) ∧ (f / ζ).coeff (-1) = f.coeff 0 / ζ.coeff 1 ∧
      (f / ζ).coeff 0 = f.coeff 1 / ζ.coeff 1 - f.coeff 0 * ζ.coeff 2 / ζ.coeff 1 ^ 2 := by
  have hζ1 : ζ.coeff 1 ≠ 0 := HahnSeries.coeff_orderTop_ne hζ
  have hζne : ζ ≠ 0 := by
    intro h
    rw [h] at hζ1
    exact hζ1 rfl
  have hζo : OrdGE ζ 1 := le_of_eq hζ.symm
  have hord : ζ.order = 1 := by
    have := HahnSeries.order_eq_orderTop_of_ne_zero hζne
    rw [hζ] at this
    exact_mod_cast this
  have hg : OrdGE (f / ζ) (-1) := by
    have := hf.div ζ
    rw [hord] at this
    exact this.mono (by norm_num)
  have hmul : f / ζ * ζ = f := div_mul_cancel₀ f hζne
  obtain ⟨h0, h1⟩ := coeff_mul_two hg hζo
  rw [hmul] at h0 h1
  norm_num at h0 h1
  refine ⟨hg, ?_, ?_⟩
  · rw [h0]
    field_simp
  · have e : (f / ζ).coeff (-1) = f.coeff 0 / ζ.coeff 1 := by
      rw [h0]
      field_simp
    rw [e] at h1
    rw [h1]
    field_simp
    ring

/-- If `S = R_τ/ζ + Q + O(t)` with `ζ` having a simple zero, then
`R_κ S = f(0)/(ζ̇ t) + R_κ(0) Q + T + O(t)`, `f = R_κ R_τ`. -/
theorem branch_BG [CharZero K] {Rκ Rτ ζ S : K⸨X⸩} {Q : K} (hRκ : OrdGE Rκ 0)
    (hRτ : OrdGE Rτ 0)
    (hζ : ζ.orderTop = ((1 : ℤ) : WithTop ℤ)) (hS : RegVal (S - Rτ / ζ) Q) :
    OrdGE (Rκ * S) (-1) ∧
      (Rκ * S).coeff (-1) = Rκ.coeff 0 * Rτ.coeff 0 / ζ.coeff 1 ∧
      (Rκ * S).coeff 0 = Rκ.coeff 0 * Q
        + ((Rκ.coeff 1 * Rτ.coeff 0 + Rκ.coeff 0 * Rτ.coeff 1) / ζ.coeff 1
          - Rκ.coeff 0 * Rτ.coeff 0 * (2 * ζ.coeff 2) / (2 * ζ.coeff 1 ^ 2)) := by
  have hζ1 : ζ.coeff 1 ≠ 0 := HahnSeries.coeff_orderTop_ne hζ
  have hsplit : Rκ * S = Rκ * Rτ / ζ + Rκ * (S - Rτ / ζ) := by ring
  have hf : OrdGE (Rκ * Rτ) 0 := (hRκ.mul hRτ).mono (by norm_num)
  obtain ⟨hf0, hf1⟩ := coeff_mul_two hRκ hRτ
  norm_num at hf0 hf1
  obtain ⟨hd, hd0, hd1⟩ := coeff_div_simple_zero hf hζ
  have hY : RegVal (Rκ * (S - Rτ / ζ)) (Rκ.coeff 0 * Q) := RegVal.mul ⟨hRκ, rfl⟩ hS
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    exact hd.add (hY.1.mono (by norm_num))
  · rw [hsplit, HahnSeries.coeff_add, hd0, hf0, hY.1.coeff_eq_zero (by norm_num), add_zero]
  · rw [hsplit, HahnSeries.coeff_add, hd1, hf0, hf1, hY.2]
    field_simp
    ring

end Laurent

/-- The expansion of `B_{κ,N}(t)` on a branch `(κ, τ)` satisfying (i)–(iii) of
Proposition 7.7. -/
theorem branch_data {K : Type} [Field K] [CharZero K] (hK : Cited_KacDeterminant)
    (hrec : GenericRecursionUniform) {bs : K} (hbs : bs ≠ 0) (d : K) {N : ℕ} {κ τ : Label}
    (hκ1 : 0 < κ.1) (hκ2 : 0 < κ.2) (hτ : τ ∈ labels (N - κ.lvl)) (hτlvl : τ.lvl = N - κ.lvl)
    (huniq : ∀ g ∈ labels (N - κ.lvl), kacHL g bs = kacHL κ bs + (κ.lvl : K) ↔ g = τ)
    (hRκ : OrdGE (RG bs d κ) 0) (hRτ : OrdGE (RG bs d τ) 0)
    (hζ : (zG bs κ - hG bs τ).orderTop = ((1 : ℤ) : WithTop ℤ)) :
    OrdGE (BG bs d N κ) (-1) ∧
      (BG bs d N κ).coeff (-1)
        = (RG bs d κ).coeff 0 * (RG bs d τ).coeff 0 / (zG bs κ - hG bs τ).coeff 1 ∧
      (BG bs d N κ).coeff 0
        = (RG bs d κ).coeff 0
            * lcoeff (Hrat (kacC bs) d (N - κ.lvl)) (kacHL κ bs + (κ.lvl : K)) 0
          + (((RG bs d κ).coeff 1 * (RG bs d τ).coeff 0
                + (RG bs d κ).coeff 0 * (RG bs d τ).coeff 1) / (zG bs κ - hG bs τ).coeff 1
              - (RG bs d κ).coeff 0 * (RG bs d τ).coeff 0 * (2 * (zG bs κ - hG bs τ).coeff 2)
                / (2 * (zG bs κ - hG bs τ).coeff 1 ^ 2)) := by
  have hζne : zG bs κ - hG bs τ ≠ 0 := by
    intro h
    rw [h, HahnSeries.orderTop_zero] at hζ
    exact WithTop.top_ne_coe hζ
  exact branch_BG hRκ hRτ hζ (shifted_branch hK hrec hbs d hκ1 hκ2 hτ hτlvl huniq hRτ hζne)

end Virasoro

