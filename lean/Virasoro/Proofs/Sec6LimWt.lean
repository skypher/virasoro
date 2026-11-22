import Virasoro.Proofs.Sec6LimR2
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.TwoBranchA

/-!
# Proposition 6.7, the chain limit (a): weights, slopes and the Taylor step (paper.tex l.1136–1141)

At `b⋆` (`p b⋆² + p' = 0`) the weight of momentum `m` is `wt(m²) = (m² − (p'−p)²)/(4pp')`, so
`h_g(b⋆) = wt((p'u − pv)²)` and `h_g(b⋆) + ℓ_g = wt((p'u + pv)²)`.  At the germ `b = b⋆ + t`,
`(h_g(b) − h_g(b⋆))/t → h'_g = 2b⋆ ḣ_g`.  Consecutive slopes of a chain differ: after `g`, every
step `g'` with `(p'u' − pv')² = (p'u + pv)²` has `ḣ_{g'} ≠ ḣ_g` (l.1155).
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries
open Finset

variable {K : Type} [Field K] [CharZero K]

/-- The weight of squared momentum `m2` at `c⋆`. -/
noncomputable def wtK (p p' : ℕ) (m2 : ℤ) : K := ((m2 : K) - ((p' : K) - p) ^ 2) / (4 * p * p')

/-- `ḣ_g` (the ν-derivative) in `K`. -/
noncomputable def hdotK (p p' : ℕ) (g : Label) : K :=
  ((1 - (g.1 : K) ^ 2) - (1 - (g.2 : K) ^ 2) * (p : K) ^ 2 / (p' : K) ^ 2) / 4

theorem kacHL_star {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0)
    (hrel : (p : K) * bs ^ 2 + p' = 0) (g : Label) :
    kacHL g bs = wtK p p' (((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2) := by
  have e : (p' : K) = -(p : K) * bs ^ 2 := by linear_combination hrel
  unfold kacHL kacH wtK
  push_cast
  rw [e]
  field_simp
  ring

theorem wtK_add_lvl {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0) (g : Label) :
    wtK (K := K) p p' (((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2) + (g.lvl : K) =
      wtK p p' (((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2) := by
  unfold wtK Label.lvl
  push_cast
  field_simp
  ring

theorem wtK_inj {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0) {m m' : ℤ}
    (h : wtK (K := K) p p' m = wtK p p' m') : m = m' := by
  unfold wtK at h
  have h4 : (4 * (p : K) * p') ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp) hp'
  rw [div_left_inj' h4, sub_left_inj] at h
  exact_mod_cast h

/-- The Taylor step: `(h_{r,s}(b⋆ + t) − h_{r,s}(b⋆))/t → 2b⋆ ḣ`. -/
theorem regVal_kacH_slope {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0)
    (hp' : (p' : K) ≠ 0) (hrel : (p : K) * bs ^ 2 + p' = 0) (g : Label) :
    RegVal ((kacHL g (bGerm bs) - HahnSeries.C (kacHL g bs)) / tX) (2 * bs * hdotK p p' g) := by
  have hb := regVal_bGerm (K := K) bs
  have hbne := bGerm_ne_zero hbs
  have e1 : (kacHL g (bGerm bs) - HahnSeries.C (kacHL g bs)) / tX =
      (2 * HahnSeries.C bs + tX) *
        ((1 - (g.1 : K⸨X⸩) ^ 2) -
          (1 - (g.2 : K⸨X⸩) ^ 2) / (HahnSeries.C bs ^ 2 * bGerm bs ^ 2)) / 4 := by
    have hC : HahnSeries.C (kacHL g bs) = kacHL g (HahnSeries.C bs : K⸨X⸩) := by
      unfold kacHL kacH
      simp [map_div₀, map_sub, map_pow, map_add, map_mul, map_inv₀, map_ofNat]
    have hCs : (HahnSeries.C bs : K⸨X⸩) ≠ 0 := by simpa using hbs
    rw [hC]
    unfold kacHL kacH
    rw [bGerm_eq] at hbne ⊢
    field_simp [tX_ne_zero]
    push_cast
    ring
  rw [e1]
  have hv := (((regVal_ofNat 2).mul (regVal_C bs)).add
    (⟨ordGE_single_one, by simp [tX]⟩ : RegVal (tX : K⸨X⸩) 0)).mul
    ((((regVal_C (1 : K)).sub ((regVal_natCast g.1).pow 2)).sub
      (((regVal_C (1 : K)).sub ((regVal_natCast g.2).pow 2)).div
        ((regVal_C bs).pow 2 |>.mul (hb.pow 2)) (by positivity))))
  have hv' := hv.div (regVal_ofNat 4) (by norm_num)
  convert hv' using 1
  · simp
  · have e : (p' : K) = -(p : K) * bs ^ 2 := by linear_combination hrel
    unfold hdotK
    rw [e]
    field_simp
    ring

/-- Consecutive slopes differ (paper.tex l.1155): after a step `a`, a step `g` with
`(p'g₁ − pg₂)² = (p'a₁ + pa₂)²` and `ℓ_g ≥ 1` has `ḣ_g ≠ ḣ_a`. -/
theorem hdotK_ne {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0) (hp0 : 0 < p) (hp'0 : 0 < p')
    (a g : Label) (ha1 : 1 ≤ a.1) (ha2 : 1 ≤ a.2) (hg1 : 1 ≤ g.1) (hg2 : 1 ≤ g.2)
    (hc : ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = ((p' : ℤ) * a.1 + (p : ℤ) * a.2) ^ 2) :
    hdotK (K := K) p p' a ≠ hdotK p p' g := by
  intro he
  have key : ((p' : ℤ) * a.1 - (p : ℤ) * a.2) * ((p' : ℤ) * a.1 + (p : ℤ) * a.2) =
      ((p' : ℤ) * g.1 - (p : ℤ) * g.2) * ((p' : ℤ) * g.1 + (p : ℤ) * g.2) := by
    unfold hdotK at he
    have he' : (((p' : ℤ) * a.1 - (p : ℤ) * a.2) * ((p' : ℤ) * a.1 + (p : ℤ) * a.2) : ℤ) =
        ((((p' : ℤ) * g.1 - (p : ℤ) * g.2) * ((p' : ℤ) * g.1 + (p : ℤ) * g.2) : ℤ) : K) := by
      push_cast
      field_simp at he
      linear_combination (-(1 : K)) * he
    exact_mod_cast he'
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
  have hpz' : (0 : ℤ) < p' := by exact_mod_cast hp'0
  have ha1' : (1 : ℤ) ≤ a.1 := by exact_mod_cast ha1
  have ha2' : (1 : ℤ) ≤ a.2 := by exact_mod_cast ha2
  have hg1' : (1 : ℤ) ≤ g.1 := by exact_mod_cast hg1
  have hg2' : (1 : ℤ) ≤ g.2 := by exact_mod_cast hg2
  set x := (p' : ℤ) * a.1 + (p : ℤ) * a.2 with hx
  set m := (p' : ℤ) * a.1 - (p : ℤ) * a.2 with hm
  set y := (p' : ℤ) * g.1 + (p : ℤ) * g.2 with hy
  have hxpos : 0 < x := by positivity
  have hmx : m ^ 2 < x ^ 2 := by
    have : 0 < 4 * ((p : ℤ) * p' * (a.1 * a.2)) := by positivity
    have : x ^ 2 - m ^ 2 = 4 * ((p : ℤ) * p' * (a.1 * a.2)) := by rw [hx, hm]; ring
    linarith
  have hxy : x ^ 2 < y ^ 2 := by
    have : 0 < 4 * ((p : ℤ) * p' * (g.1 * g.2)) := by positivity
    have : y ^ 2 - ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = 4 * ((p : ℤ) * p' * (g.1 * g.2)) := by
      rw [hy]; ring
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hc with h1 | h1
  · rw [h1] at key
    have : x * (y - m) = 0 := by linear_combination -key
    rcases mul_eq_zero.1 this with h2 | h2
    · linarith
    · have : y = m := by linarith
      rw [this] at hxy
      linarith
  · rw [h1] at key
    have : x * (y + m) = 0 := by linear_combination key
    rcases mul_eq_zero.1 this with h2 | h2
    · linarith
    · have : y = -m := by linarith
      rw [this, neg_sq] at hxy
      linarith

end Virasoro.ChainLim
