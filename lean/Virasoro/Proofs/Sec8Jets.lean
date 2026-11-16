import Virasoro.Proofs.Jets
import Virasoro.Proofs.Sec8Const
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Jets of the residue data at `b₀`

Over `K = ℂ(d)` with `β = b₀` (so `β² = -4/3`), the germs at `b = β + t` of the factors of
`𝒜_{r,s}`, `𝒫_{r,s}` and `h_{r,s}` have explicit first jets:
`pβ + qβ⁻¹ = β(4p - 3q)/4 + (4p + 3q)/4 · t + O(t²)`,
`(Λ² - (kb ± lb⁻¹)²)/4 = λ_{|4k ∓ 3l|} - d + β(7 - 16k² + 9l²)/32 · t + O(t²)`, and
`h_{r,s} = h_{r,s}(β) + β(7 - 16r² + 9s²)/32 · t + ((1 - r²) + 27(1 - s²)/16)/4 · t² + O(t³)`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- `β = b₀` as an element of `ℂ(d)`. -/
noncomputable abbrev βd : Kd := RatFunc.C b0

theorem βd_ne_zero : βd ≠ 0 := by
  rw [βd, Ne, map_eq_zero_iff _ (RatFunc.C_injective)]
  exact b0_ne_zero

theorem βd_sq : βd ^ 2 = -4 / 3 := by
  rw [βd, ← map_pow, b0_sq]
  simp only [map_div₀, map_neg, map_ofNat]

theorem βd_inv : βd⁻¹ = -(3 / 4) * βd := by
  have h : βd * (-(3 / 4) * βd) = 1 := by linear_combination (-(3 / 4) : Kd) * βd_sq
  exact inv_eq_of_mul_eq_one_right h

/-- The germ `b = β + t`. -/
noncomputable abbrev bG : Kd⸨X⸩ := bGerm βd

theorem j2_bG : J2 bG βd 1 0 := j2_bGerm βd

theorem j2_bG_inv : J2 bG⁻¹ (-(3 / 4) * βd) (3 / 4) ((9 / 16) * βd) := by
  refine (j2_bGerm_inv βd_ne_zero).congr βd_inv ?_ ?_
  · rw [βd_sq]
    norm_num
  · rw [one_div, ← inv_pow, βd_inv]
    linear_combination (-(27 : Kd) / 64 * βd) * βd_sq


theorem j1_intCast (n : ℤ) : J1 ((n : Kd⸨X⸩)) (n : Kd) 0 := (j2_intCast n).toJ1

theorem j1_natCast (n : ℕ) : J1 ((n : Kd⸨X⸩)) (n : Kd) 0 := (j2_natCast n).toJ1

theorem J1.add {x y : Kd⸨X⸩} {a b a' b' : Kd} (hx : J1 x a b) (hy : J1 y a' b') :
    J1 (x + y) (a + a') (b + b') :=
  ⟨hx.1.add hy.1, by rw [HahnSeries.coeff_add, hx.2.1, hy.2.1],
    by rw [HahnSeries.coeff_add, hx.2.2, hy.2.2]⟩

theorem J1.sub {x y : Kd⸨X⸩} {a b a' b' : Kd} (hx : J1 x a b) (hy : J1 y a' b') :
    J1 (x - y) (a - a') (b - b') :=
  ⟨hx.1.sub hy.1, by rw [HahnSeries.coeff_sub, hx.2.1, hy.2.1],
    by rw [HahnSeries.coeff_sub, hx.2.2, hy.2.2]⟩

/-- An `𝒜`-factor `p b + q b⁻¹` at `b = β + t`. -/
theorem j1_Afactor (p q : ℤ) :
    J1 ((p : Kd⸨X⸩) * bG + (q : Kd⸨X⸩) * bG⁻¹) ((p : Kd) * βd + (q : Kd) * βd⁻¹)
      ((p : Kd) + 3 / 4 * (q : Kd)) := by
  have h := ((j1_intCast p).mul j2_bG.toJ1).add ((j1_intCast q).mul j2_bG_inv.toJ1)
  refine h.congr ?_ ?_
  · rw [βd_inv]
  · ring

/-- Its value in the form `β (4p - 3q)/4`. -/
theorem Afactor_value (p q : ℤ) :
    (p : Kd) * βd + (q : Kd) * βd⁻¹ = βd * ((4 * (p : Kd) - 3 * (q : Kd)) / 4) := by
  rw [βd_inv]; ring

/-- The square-root-free part of the fusion factors: `(b + b⁻¹)²` and `Λ²`. -/
theorem j1_lamSq :
    J1 (lamSq bG (HahnSeries.C dvar)) (-1 / 12 - 4 * dvar) (7 / 8 * βd) := by
  have hs := (j2_bG.add j2_bG_inv)
  have hsq := (hs.mul hs).toJ1
  have h4 := ((j2_ofNat 4 : J2 (4 : Kd⸨X⸩) 4 0 0).mul (j2_C dvar)).toJ1
  have h := hsq.sub h4
  unfold lamSq
  rw [pow_two]
  refine h.congr ?_ ?_
  · linear_combination (1 / 16 : Kd) * βd_sq
  · ring

/-- A fusion factor `(Λ² - (k b + ε l b⁻¹)²)/4`, `ε = ±1`, at `b = β + t`. -/
theorem j1_Pfactor (k l : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    J1 ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG + (ε : Kd⸨X⸩) * (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4)
      (((4 * (k : Kd) - 3 * (ε : Kd) * (l : Kd)) ^ 2 - 1) / 48 - dvar)
      (βd * ((7 - 16 * (k : Kd) ^ 2 + 9 * (l : Kd) ^ 2) / 32)) := by
  have hu := ((j1_natCast k).mul j2_bG.toJ1).add
    (((j1_intCast ε).mul (j1_natCast l)).mul j2_bG_inv.toJ1)
  have hsq := hu.mul hu
  have h := (j1_lamSq.sub hsq)
  have h4 : J1 ((4 : Kd⸨X⸩)⁻¹) (4 : Kd)⁻¹ 0 := by
    have := ((j2_ofNat 4 : J2 (4 : Kd⸨X⸩) 4 0 0).inv (by norm_num)).toJ1
    exact this.congr rfl (by ring)
  have h' := h.mul h4
  rw [div_eq_mul_inv, pow_two]
  have hε2 : (ε : Kd) ^ 2 = 1 := by rcases hε with h | h <;> subst h <;> norm_num
  refine h'.congr ?_ ?_
  · linear_combination (-(((k : Kd) - 3 / 4 * ε * l)) ^ 2 / 4) * βd_sq
  · linear_combination (9 * (l : Kd) ^ 2 * βd / 32) * hε2


/-- `q - d ≠ 0` in `ℂ(d)` for every rational `q`. -/
theorem ratCast_sub_dvar_ne (q : ℚ) : ((q : ℚ) : Kd) - dvar ≠ 0 := by
  intro h
  have h1 := congrArg RatFunc.intDegree (sub_eq_zero.1 h)
  have hq : ((q : ℚ) : Kd) = RatFunc.C (q : ℂ) := (map_ratCast (RatFunc.C : ℂ →+* Kd) q).symm
  rw [hq, RatFunc.intDegree_C, dvar, RatFunc.intDegree_X] at h1
  exact absurd h1 (by norm_num)

/-- The value of a fusion factor, `λ_{|4k ∓ 3l|} - d`. -/
noncomputable def pval (k l : ℕ) (ε : ℤ) : Kd :=
  (((4 * (k : Kd) - 3 * (ε : Kd) * (l : Kd)) ^ 2 - 1) / 48 - dvar)

theorem pval_ne (k l : ℕ) (ε : ℤ) : pval k l ε ≠ 0 := by
  have := ratCast_sub_dvar_ne (((4 * (k : ℚ) - 3 * (ε : ℚ) * (l : ℚ)) ^ 2 - 1) / 48)
  unfold pval
  push_cast at this
  exact this

/-- `D_{k,l} = (7 - 16k² + 9l²)/32`. -/
noncomputable def pD (k l : ℕ) : Kd := (7 - 16 * (k : Kd) ^ 2 + 9 * (l : Kd) ^ 2) / 32

theorem j1_Pplus (k l : ℕ) :
    J1 ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG + (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4)
      (pval k l 1) (βd * pD k l) := by
  have h := j1_Pfactor k l 1 (Or.inl rfl)
  have e : ((k : Kd⸨X⸩) * bG + ((1 : ℤ) : Kd⸨X⸩) * (l : Kd⸨X⸩) * bG⁻¹)
      = (k : Kd⸨X⸩) * bG + (l : Kd⸨X⸩) * bG⁻¹ := by push_cast; ring
  rw [e] at h
  exact h

theorem j1_Pminus (k l : ℕ) :
    J1 ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG - (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4)
      (pval k l (-1)) (βd * pD k l) := by
  have h := j1_Pfactor k l (-1) (Or.inr rfl)
  have e : ((k : Kd⸨X⸩) * bG + ((-1 : ℤ) : Kd⸨X⸩) * (l : Kd⸨X⸩) * bG⁻¹)
      = (k : Kd⸨X⸩) * bG - (l : Kd⸨X⸩) * bG⁻¹ := by push_cast; ring
  rw [e] at h
  exact h

/-- The value of `𝒫_{r,s}` at `b₀` as a product of fusion values. -/
noncomputable def Pval (r s : ℕ) : Kd :=
  ∏ k ∈ oddsBelow r, ∏ l ∈ oddsBelow s, pval k l 1 * pval k l (-1)

/-- The logarithmic derivative of `𝒫_{r,s}` divided by `β`. -/
noncomputable def sigP (r s : ℕ) : Kd :=
  ∑ k ∈ oddsBelow r, ∑ l ∈ oddsBelow s, (pD k l / pval k l 1 + pD k l / pval k l (-1))

theorem j1_genP (r s : ℕ) :
    J1 (genP r s bG (HahnSeries.C dvar)) (Pval r s) (Pval r s * (βd * sigP r s)) := by
  unfold genP Pval sigP
  have hin : ∀ k ∈ oddsBelow r, J1 (∏ l ∈ oddsBelow s,
      ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG + (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4) *
      ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG - (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4))
      (∏ l ∈ oddsBelow s, pval k l 1 * pval k l (-1))
      ((∏ l ∈ oddsBelow s, pval k l 1 * pval k l (-1)) *
        (βd * ∑ l ∈ oddsBelow s, (pD k l / pval k l 1 + pD k l / pval k l (-1)))) := by
    intro k _
    have h := J1.prod (s := oddsBelow s)
      (f := fun l => ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG + (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4) *
        ((lamSq bG (HahnSeries.C dvar) - ((k : Kd⸨X⸩) * bG - (l : Kd⸨X⸩) * bG⁻¹) ^ 2) / 4))
      (fun l _ => (j1_Pplus k l).mul (j1_Pminus k l))
      (fun l _ => mul_ne_zero (pval_ne k l 1) (pval_ne k l (-1)))
    refine h.congr rfl ?_
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 := pval_ne k l 1
    have h2 := pval_ne k l (-1)
    field_simp
    ring
  have h := J1.prod hin (fun k _ => Finset.prod_ne_zero_iff.2 fun l _ =>
    mul_ne_zero (pval_ne k l 1) (pval_ne k l (-1)))
  refine h.congr rfl ?_
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hne : (∏ l ∈ oddsBelow s, pval k l 1 * pval k l (-1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => mul_ne_zero (pval_ne k l 1) (pval_ne k l (-1))
  field_simp

/-- The logarithmic derivative of `𝒜_{r,s}` divided by `β`. -/
noncomputable def sigA (r s : ℕ) : Kd :=
  ∑ pq ∈ genAIndex r s, 3 / 4 * ((4 * (pq.1 : Kd) + 3 * (pq.2 : Kd)) / (4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)))

theorem j1_genA (r s : ℕ) (hne : ∀ pq ∈ genAIndex r s, 4 * pq.1 ≠ 3 * pq.2) :
    J1 (genA r s bG) (genA r s βd) (genA r s βd * (βd * sigA r s)) := by
  have hu0 : ∀ pq ∈ genAIndex r s, (pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹ ≠ 0 := by
    intro pq hpq
    rw [Afactor_value]
    refine mul_ne_zero βd_ne_zero (div_ne_zero ?_ (by norm_num))
    have : (4 * pq.1 - 3 * pq.2 : ℤ) ≠ 0 := sub_ne_zero.2 (hne pq hpq)
    exact_mod_cast this
  have hfac : ∀ pq ∈ genAIndex r s,
      J1 (((pq.1 : Kd⸨X⸩) * bG + (pq.2 : Kd⸨X⸩) * bG⁻¹)⁻¹)
        (((pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹)⁻¹)
        (-((pq.1 : Kd) + 3 / 4 * (pq.2 : Kd)) / ((pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹) ^ 2) :=
    fun pq hpq => (j1_Afactor pq.1 pq.2).inv (hu0 pq hpq)
  have hp := J1.prod (s := genAIndex r s)
    (f := fun pq => (((pq.1 : Kd⸨X⸩) * bG + (pq.2 : Kd⸨X⸩) * bG⁻¹)⁻¹))
    (a := fun pq => (((pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹)⁻¹))
    (b := fun pq => (-((pq.1 : Kd) + 3 / 4 * (pq.2 : Kd)) /
      ((pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹) ^ 2)) hfac fun pq hpq => inv_ne_zero (hu0 pq hpq)
  have h2 : J1 ((2 : Kd⸨X⸩)⁻¹) (2 : Kd)⁻¹ 0 :=
    (((j2_ofNat 2 : J2 (2 : Kd⸨X⸩) 2 0 0).inv (by norm_num)).toJ1).congr rfl (by ring)
  have h := h2.mul hp
  have hterm : ∀ pq ∈ genAIndex r s,
      (-((pq.1 : Kd) + 3 / 4 * (pq.2 : Kd)) / ((pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹) ^ 2) /
        (((pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹)⁻¹)
      = βd * (3 / 4 * ((4 * (pq.1 : Kd) + 3 * (pq.2 : Kd)) /
          (4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)))) := by
    intro pq hpq
    have h4 : (4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)) ≠ 0 := by
      have : (4 * pq.1 - 3 * pq.2 : ℤ) ≠ 0 := sub_ne_zero.2 (hne pq hpq)
      exact_mod_cast this
    set u1 : Kd := (pq.1 : Kd) + 3 / 4 * (pq.2 : Kd) with hu1
    set w : Kd := (4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)) / 4 with hw
    have hw0 : w ≠ 0 := div_ne_zero h4 (by norm_num)
    have hβ := βd_ne_zero
    rw [Afactor_value]
    calc -u1 / (βd * w) ^ 2 / (βd * w)⁻¹ = -u1 * βd⁻¹ / w := by field_simp
      _ = -u1 * (-(3 / 4) * βd) / w := by rw [βd_inv]
      _ = βd * (3 / 4 * ((4 * (pq.1 : Kd) + 3 * (pq.2 : Kd)) /
            (4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)))) := by
          rw [hu1, hw]
          field_simp
  unfold genA
  refine h.congr rfl ?_
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  unfold sigA
  ring


theorem j1_RG (a : Label) (hne : ∀ pq ∈ genAIndex a.1 a.2, 4 * pq.1 ≠ 3 * pq.2) :
    J1 (RG βd dvar a) (genA a.1 a.2 βd * Pval a.1 a.2)
      (genA a.1 a.2 βd * Pval a.1 a.2 * (βd * (sigA a.1 a.2 + sigP a.1 a.2))) := by
  have h := (j1_genA a.1 a.2 hne).mul (j1_genP a.1 a.2)
  unfold RG genR
  exact h.congr rfl (by ring)

/-- `D_{r,s} = (7 - 16r² + 9s²)/32`, so that `ḣ_{r,s}(b₀) = β D_{r,s}`. -/
noncomputable def hD (a : Label) : Kd := (7 - 16 * (a.1 : Kd) ^ 2 + 9 * (a.2 : Kd) ^ 2) / 32

/-- The `t²` coefficient of `h_{r,s}(β + t)`: `((1 - r²) + 27(1 - s²)/16)/4`. -/
noncomputable def hE (a : Label) : Kd := ((1 - (a.1 : Kd) ^ 2) + 27 * (1 - (a.2 : Kd) ^ 2) / 16) / 4

theorem j2_hG (a : Label) : J2 (hG βd a) (kacHL a βd) (βd * hD a) (hE a) := by
  have hs := j2_bG.add j2_bG_inv
  have hsq := hs.mul hs
  have hu := ((j2_intCast (a.1 : ℤ)).mul j2_bG).add ((j2_intCast (a.2 : ℤ)).mul j2_bG_inv)
  have husq := hu.mul hu
  have h := (hsq.sub husq).div (j2_ofNat 4) (by norm_num)
  unfold hG kacHL kacH
  rw [pow_two, pow_two]
  refine h.congr ?_ ?_ ?_
  · rw [βd_inv]
    push_cast
    ring
  · unfold hD
    push_cast
    ring
  · unfold hE
    push_cast
    linear_combination ((9 / 32 - 9 * (a.2 : Kd) / 8 * ((a.1 : Kd) - 3 * (a.2 : Kd) / 4)) / 4) *
      βd_sq

theorem j2_zeta (κ τ : Label) :
    J2 (zetaG b0 κ τ) (kacHL κ βd + (κ.lvl : Kd) - kacHL τ βd) (βd * (hD κ - hD τ))
      (hE κ - hE τ) := by
  have h := ((j2_hG κ).add (j2_natCast κ.lvl)).sub (j2_hG τ)
  unfold zetaG zG
  exact h.congr rfl (by ring) (by ring)


/-- The derivative term of Proposition 7.7 at `b₀`, in terms of the jets. -/
theorem Tterm_b0 (κ τ : Label) (hκ : ∀ pq ∈ genAIndex κ.1 κ.2, 4 * pq.1 ≠ 3 * pq.2)
    (hτ : ∀ pq ∈ genAIndex τ.1 τ.2, 4 * pq.1 ≠ 3 * pq.2) (hc : hD κ - hD τ ≠ 0) :
    Tterm b0 κ τ =
      genA κ.1 κ.2 βd * Pval κ.1 κ.2 * (genA τ.1 τ.2 βd * Pval τ.1 τ.2) *
        ((sigA κ.1 κ.2 + sigP κ.1 κ.2 + (sigA τ.1 τ.2 + sigP τ.1 τ.2)) / (hD κ - hD τ)
          + 3 * (hE κ - hE τ) / (4 * (hD κ - hD τ) ^ 2)) := by
  have Rκ := j1_RG κ hκ
  have Rτ := j1_RG τ hτ
  have Z := j2_zeta κ τ
  unfold Tterm germ0 germDot germDDot
  dsimp only
  rw [show (RatFunc.C b0 : Kd) = βd from rfl, Rκ.2.1, Rκ.2.2, Rτ.2.1, Rτ.2.2, Z.2.2.1, Z.2.2.2]
  have hβ := βd_ne_zero
  rw [mul_pow, βd_sq]
  field_simp
  ring


theorem βd_inv_sq : βd⁻¹ ^ 2 = -3 / 4 := by
  rw [inv_pow, βd_sq]
  norm_num

theorem genA_βd_prod (r s : ℕ) : genA r s βd
    = 2⁻¹ * ((∏ pq ∈ genAIndex r s, ((4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)) / 4)⁻¹)
        * βd⁻¹ ^ (genAIndex r s).card) := by
  unfold genA
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun pq _ => ?_
  have e : (pq.1 : Kd) * βd + (pq.2 : Kd) * βd⁻¹ = (4 * (pq.1 : Kd) - 3 * (pq.2 : Kd)) / 4 * βd := by
    rw [βd_inv]
    ring
  rw [e, mul_inv]

/-- The derivative term with the products of fusion values and their log-derivatives separated. -/
theorem Tterm_b0_split (κ τ : Label) (hκ : ∀ pq ∈ genAIndex κ.1 κ.2, 4 * pq.1 ≠ 3 * pq.2)
    (hτ : ∀ pq ∈ genAIndex τ.1 τ.2, 4 * pq.1 ≠ 3 * pq.2) (hc : hD κ - hD τ ≠ 0) :
    Tterm b0 κ τ =
      genA κ.1 κ.2 βd * genA τ.1 τ.2 βd *
        ((Pval κ.1 κ.2 * Pval τ.1 τ.2 * (sigA κ.1 κ.2 + sigA τ.1 τ.2)
            + Pval κ.1 κ.2 * sigP κ.1 κ.2 * Pval τ.1 τ.2
            + Pval κ.1 κ.2 * (Pval τ.1 τ.2 * sigP τ.1 τ.2)) / (hD κ - hD τ)
          + Pval κ.1 κ.2 * Pval τ.1 τ.2 * (3 * (hE κ - hE τ)) / (4 * (hD κ - hD τ) ^ 2)) := by
  rw [Tterm_b0 κ τ hκ hτ hc]
  ring

end Virasoro
