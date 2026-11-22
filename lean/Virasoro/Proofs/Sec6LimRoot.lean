import Virasoro.Proofs.Sec6LimPhi

/-!
# Proposition 6.7, the chain limit (a): the roots of `𝒫_g` at the germ (paper.tex l.1127–1135)

Each `d`-root of `𝒫_g` is `φ(x₁)φ(x₂)` with `x₁ + x₂ = (1,1)` (`genPpoly_eq`).  At the germ
`b = b⋆ + t`, `d = tY`, the factor `1 − d/(φ(x₁)φ(x₂))` is regular with value `w(x₁)w(x₂)`, where
`w(x) = 1 − Y/(2x₁ φ((1,1) − x)(b⋆))` for `x ∈ ℤ(p,p') ∖ {0}` and `w(x) = 1` otherwise (at most one
of `x₁, x₂` lies in `ℤ(p,p')`, as their sum `(1,1)` does not).
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries
open Finset

variable {K : Type} [Field K] [CharZero K]

/-- `x ∈ ℤ(p,p') ∖ {0}`. -/
def IsZ (p p' : ℕ) (x : ℤ × ℤ) : Prop := (p : ℤ) * x.2 = (p' : ℤ) * x.1 ∧ x ≠ (0, 0)

instance (p p' : ℕ) : DecidablePred (IsZ p p') := fun _ => by unfold IsZ; infer_instance

/-- The value `w(x)` of the factor contributed by `φ(x)`. -/
noncomputable def wv (p p' : ℕ) (bs Y : K) (x : ℤ × ℤ) : K :=
  if IsZ p p' x then 1 - Y / (2 * (x.1 : K) * phiL bs (1 - x.1, 1 - x.2)) else 1

theorem IsZ.mult {p p' : ℕ} (hp : p ≠ 0) (hcop : Nat.Coprime p p') {x : ℤ × ℤ}
    (h : IsZ p p' x) : ∃ j : ℤ, j ≠ 0 ∧ x = (j * p, j * p') := by
  obtain ⟨h1, h2⟩ := h
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hd : (p : ℤ) ∣ (p' : ℤ) * x.1 := ⟨x.2, h1.symm⟩
  obtain ⟨j, hj⟩ := hc.dvd_of_dvd_mul_left hd
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  refine ⟨j, ?_, ?_⟩
  · rintro rfl
    apply h2
    have hx1 : x.1 = 0 := by rw [hj]; ring
    have hx2 : x.2 = 0 := by
      have : (p : ℤ) * x.2 = 0 := by rw [h1, hx1]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hp0
      · exact h
    exact Prod.ext hx1 hx2
  · have hx1 : x.1 = j * p := by rw [hj]; ring
    have hx2 : x.2 = j * p' := by
      have : (p : ℤ) * x.2 = (p : ℤ) * (j * p') := by rw [h1, hx1]; ring
      exact mul_left_cancel₀ hp0 this
    exact Prod.ext hx1 hx2

/-- `x` and `(1,1) − x` are not both in `ℤ(p,p')` when `p ≠ p'`. -/
theorem not_both_IsZ {p p' : ℕ} (hne : p ≠ p') {x : ℤ × ℤ} (h1 : IsZ p p' x) :
    ¬ IsZ p p' (1 - x.1, 1 - x.2) := by
  rintro ⟨h2, _⟩
  obtain ⟨h1, _⟩ := h1
  dsimp only at h2
  have : (p : ℤ) = p' := by linarith
  exact hne (by exact_mod_cast this)

omit [CharZero K] in
theorem wv_zero (p p' : ℕ) (bs Y : K) : wv p p' bs Y (0, 0) = 1 := by
  rw [wv, if_neg (fun h => h.2 rfl)]

omit [CharZero K] in
theorem wv_one (p p' : ℕ) (hne : p ≠ p') (bs Y : K) : wv p p' bs Y (1, 1) = 1 := by
  rw [wv, if_neg]
  rintro ⟨h, _⟩
  apply hne
  have : (p : ℤ) = p' := by simpa using h
  exact_mod_cast this

/-- The value of one root factor `1 − tY/(φ(x)φ((1,1) − x))` at the germ. -/
theorem regVal_root {bs Y : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0) (hne : p ≠ p')
    (hcop : Nat.Coprime p p') (hrel : (p : K) * bs ^ 2 + p' = 0) (x : ℤ × ℤ)
    (hx0 : x ≠ (0, 0)) (hx1 : (1 - x.1, 1 - x.2) ≠ ((0 : ℤ), (0 : ℤ))) :
    phiL (bGerm bs) x * phiL (bGerm bs) (1 - x.1, 1 - x.2) ≠ 0 ∧
      RegVal (1 - tX * HahnSeries.C Y / (phiL (bGerm bs) x * phiL (bGerm bs) (1 - x.1, 1 - x.2)))
        (wv p p' bs Y x * wv p p' bs Y (1 - x.1, 1 - x.2)) := by
  have hp0 : p ≠ 0 := fun h0 => hp (by rw [h0]; simp)
  have regVal_one' : RegVal (1 : K⸨X⸩) 1 := by simpa using regVal_C (1 : K)
  have hCY : RegVal (tX * HahnSeries.C Y : K⸨X⸩) 0 := by
    have ht : RegVal (tX : K⸨X⸩) 0 := ⟨ordGE_single_one, by simp [tX]⟩
    have := ht.mul (regVal_C Y)
    simpa using this
  have hne0 : ∀ {u : K⸨X⸩} {v : K}, RegVal u v → v ≠ 0 → u ≠ 0 := by
    intro u v hu hv h0
    rw [h0] at hu
    exact hv (by simpa using hu.2.symm)
  by_cases hz1 : IsZ p p' x
  · -- `x = j(p,p')`: a simple zero
    have hz2 := not_both_IsZ hne hz1
    obtain ⟨j, hj, rfl⟩ := hz1.mult hp0 hcop
    have hφ1 := regVal_phiL_mult_div hbs hrel j
    have hφ2 := regVal_phiL hbs (1 - j * (p : ℤ), 1 - j * (p' : ℤ))
    have hv2 : phiL bs (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) ≠ 0 := by
      refine phiL_star_ne hbs hp hrel ?_
      intro h
      exact hz2 ⟨by dsimp only; linarith, hx1⟩
    have hj2 : 2 * (j : K) * (p : K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) hp
      exact_mod_cast hj
    have hq := hφ1.mul hφ2
    have hqv : 2 * (j : K) * (p : K) * phiL bs (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) ≠ 0 :=
      mul_ne_zero hj2 hv2
    have hc0 : phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) *
        phiL (bGerm bs) (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) ≠ 0 := by
      intro h0
      apply hne0 hq hqv
      rw [div_mul_eq_mul_div, h0, zero_div]
    refine ⟨hc0, ?_⟩
    have e1 : tX * HahnSeries.C Y / (phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) *
        phiL (bGerm bs) (1 - j * (p : ℤ), 1 - j * (p' : ℤ))) =
        HahnSeries.C Y / (phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) / tX *
          phiL (bGerm bs) (1 - j * (p : ℤ), 1 - j * (p' : ℤ))) := by
      field_simp [tX_ne_zero]
    rw [e1]
    have h3 := regVal_one'.sub ((regVal_C Y).div hq hqv)
    convert h3 using 1
    rw [wv, if_pos ⟨by ring, hx0⟩, wv, if_neg hz2]
    simp only [mul_one]
    congr 2
    push_cast
    ring
  · by_cases hz2 : IsZ p p' (1 - x.1, 1 - x.2)
    · -- `(1,1) − x = j(p,p')`
      have hz1' : ¬ IsZ p p' (1 - (1 - x.1), 1 - (1 - x.2)) := by
        simp only [sub_sub_cancel]
        exact hz1
      obtain ⟨j, hj, hjx⟩ := hz2.mult hp0 hcop
      have hx' : x = (1 - j * p, 1 - j * p') := by
        rw [Prod.mk.injEq] at hjx
        exact Prod.ext (by linarith [hjx.1]) (by linarith [hjx.2])
      subst hx'
      simp only [sub_sub_cancel] at hjx hz2 ⊢
      have hφ1 := regVal_phiL_mult_div hbs hrel j
      have hφ2 := regVal_phiL hbs (1 - j * (p : ℤ), 1 - j * (p' : ℤ))
      have hv2 : phiL bs (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) ≠ 0 := by
        refine phiL_star_ne hbs hp hrel ?_
        intro h
        exact hz1 ⟨by dsimp only; linarith, hx0⟩
      have hj2 : 2 * (j : K) * (p : K) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) hp
        exact_mod_cast hj
      have hq := hφ2.mul hφ1
      have hqv : phiL bs (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) * (2 * (j : K) * (p : K)) ≠ 0 :=
        mul_ne_zero hv2 hj2
      have hc0 : phiL (bGerm bs) (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) *
          phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) ≠ 0 := by
        intro h0
        apply hne0 hq hqv
        rw [mul_div_assoc', h0, zero_div]
      refine ⟨hc0, ?_⟩
      have e1 : tX * HahnSeries.C Y / (phiL (bGerm bs) (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) *
          phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ))) =
          HahnSeries.C Y / (phiL (bGerm bs) (1 - j * (p : ℤ), 1 - j * (p' : ℤ)) *
            (phiL (bGerm bs) ((j * p : ℤ), (j * p' : ℤ)) / tX)) := by
        field_simp [tX_ne_zero]
      rw [e1]
      have h3 := regVal_one'.sub ((regVal_C Y).div hq hqv)
      convert h3 using 1
      rw [wv, if_neg hz1, wv, if_pos ⟨by ring, by simpa using hx1⟩]
      simp only [one_mul]
      congr 2
      push_cast
      ring
    · -- neither is a zero
      have hφ1 := regVal_phiL hbs x
      have hφ2 := regVal_phiL hbs (1 - x.1, 1 - x.2)
      have hv1 : phiL bs x ≠ 0 := phiL_star_ne hbs hp hrel (fun h => hz1 ⟨h, hx0⟩)
      have hv2 : phiL bs (1 - x.1, 1 - x.2) ≠ 0 :=
        phiL_star_ne hbs hp hrel (fun h => hz2 ⟨h, hx1⟩)
      have hq := hφ1.mul hφ2
      have hqv := mul_ne_zero hv1 hv2
      refine ⟨hne0 hq hqv, ?_⟩
      have h3 := regVal_one'.sub (hCY.div hq hqv)
      convert h3 using 1
      rw [wv, if_neg hz1, wv, if_neg hz2]
      simp

end Virasoro.ChainLim
