import Virasoro.Proofs.Sec6LimR

/-!
# Proposition 6.7, the chain limit (a): `ℛ_g/t → ρ_g Y ∏_j (1 − Y/(2b⋆ jκ₀))` (l.1129–1135)

The product over the box `B_g` reduces to the `j ∈ boxMults g` (the points `(jp, jp') ∈ B_g`,
`j ≠ 0`), each giving `1 − Y/(2b⋆ jκ₀)` with `κ₀ = p(p'−p)/p'`; and
`E(b⋆) = −(ub⋆² + v)/(2(b⋆² + 1)) = ρ_g = −(p'u − pv)/(2(p'−p))`.
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries
open Finset

variable {K : Type} [Field K] [CharZero K]

/-- `κ₀ = p(p'−p)/p'` in `K`. -/
noncomputable def kap (p p' : ℕ) : K := (p : K) * ((p' : K) - p) / p'

theorem wv_mult {bs Y : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0)
    (hrel : (p : K) * bs ^ 2 + p' = 0) (j : ℤ) (hj : j ≠ 0) :
    wv p p' bs Y (j * p, j * p') = 1 - Y / (2 * bs * j * kap p p') := by
  have hp0 : p ≠ 0 := fun h0 => hp (by rw [h0]; simp)
  have hz : IsZ p p' ((j * p : ℤ), (j * p' : ℤ)) := by
    refine ⟨by ring, ?_⟩
    intro h
    rw [Prod.mk.injEq] at h
    have := h.1
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hj h1
    · exact hp0 (by exact_mod_cast h1)
  rw [wv, if_pos hz]
  congr 2
  have e : (p' : K) = -(p : K) * bs ^ 2 := by linear_combination hrel
  unfold kap phiL
  push_cast
  rw [e]
  have hj' : (j : K) ≠ 0 := by exact_mod_cast hj
  field_simp
  ring

theorem prod_box_wv {bs Y : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0)
    (hpn : 1 ≤ p) (hcop : Nat.Coprime p p') (hrel : (p : K) * bs ^ 2 + p' = 0) (u v : ℕ) :
    ∏ x ∈ Icc (1 - (u : ℤ)) u ×ˢ Icc (1 - (v : ℤ)) v, wv p p' bs Y x =
      ∏ j ∈ boxMults p p' (u, v), (1 - Y / (2 * bs * j * kap p p')) := by
  have hp0 : p ≠ 0 := by omega
  have hpz : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [← prod_filter_of_ne (p := IsZ p p')]
  · have hS : (Icc (1 - (u : ℤ)) u ×ˢ Icc (1 - (v : ℤ)) v).filter (IsZ p p') =
        (boxMults p p' (u, v)).image (fun j : ℤ => ((j * p : ℤ), (j * p' : ℤ))) := by
      ext x
      simp only [mem_filter, mem_product, mem_Icc, mem_image, boxMults]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hz⟩
        obtain ⟨j, hj, rfl⟩ := hz.mult hp0 hcop
        refine ⟨j, ⟨⟨?_, ?_⟩, hj, h1, h2, h3, h4⟩, rfl⟩
        · dsimp only at h1 h2
          have : -((u : ℤ)) ≤ j := by
            by_contra hc
            have hc : j ≤ -((u : ℤ)) - 1 := by omega
            have : j * p ≤ (-((u : ℤ)) - 1) * p := mul_le_mul_of_nonneg_right hc hpz.le
            nlinarith
          have hv0 : (0 : ℤ) ≤ v := Int.natCast_nonneg v
          linarith
        · dsimp only at h1 h2
          have : j ≤ (u : ℤ) := by
            by_contra hc
            have hc : (u : ℤ) + 1 ≤ j := by omega
            have : ((u : ℤ) + 1) * p ≤ j * p := mul_le_mul_of_nonneg_right hc hpz.le
            nlinarith
          have hv0 : (0 : ℤ) ≤ v := Int.natCast_nonneg v
          linarith
      · rintro ⟨j, ⟨_, hj, h1, h2, h3, h4⟩, rfl⟩
        refine ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨by ring, ?_⟩⟩
        intro h
        rw [Prod.mk.injEq] at h
        rcases mul_eq_zero.1 h.1 with h5 | h5
        · exact hj h5
        · exact hp0 (by exact_mod_cast h5)
    rw [hS, prod_image]
    · refine prod_congr rfl fun j hj => ?_
      have hj0 : j ≠ 0 := (mem_filter.1 hj).2.1
      exact wv_mult hbs hp hp' hrel j hj0
    · intro j1 _ j2 _ he
      have := congrArg Prod.fst he
      dsimp only at this
      exact mul_right_cancel₀ (by exact_mod_cast hp0) this
  · intro x _ hx
    by_contra hz
    exact hx (by rw [wv, if_neg hz])

/-- `E(b⋆) = ρ_g`. -/
theorem E_star {bs : K} {p p' : ℕ} (hp : (p : K) ≠ 0) (hne : (p' : K) - p ≠ 0)
    (hrel : (p : K) * bs ^ 2 + p' = 0) (hb1 : bs ^ 2 + 1 ≠ 0) (u v : ℕ) :
    -(((u : K) * bs ^ 2 + (v : K)) / (2 * (bs ^ 2 + 1))) =
      -((p' : K) * u - (p : K) * v) / (2 * ((p' : K) - p)) := by
  have e : (p' : K) = -(p : K) * bs ^ 2 := by linear_combination hrel
  have h2 : -(p : K) * bs ^ 2 - p ≠ 0 := by rw [← e]; exact hne
  rw [e]
  have h3 : -(p : K) * bs ^ 2 - p = -(p : K) * (bs ^ 2 + 1) := by ring
  rw [h3]
  field_simp
  ring

/-- `ℛ_g/t` at the germ (paper.tex l.1134–1135, in the coordinate `b`). -/
theorem regVal_genR {bs Y : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0)
    (hpn : 1 ≤ p) (hne : p ≠ p') (hne' : (p' : K) - p ≠ 0) (hcop : Nat.Coprime p p')
    (hrel : (p : K) * bs ^ 2 + p' = 0) (hb1 : bs ^ 2 + 1 ≠ 0) (u v : ℕ) (hu : 0 < u)
    (hv : 0 < v) :
    RegVal (genR u v (bGerm bs) (tX * HahnSeries.C Y) / tX)
      (-((p' : K) * u - (p : K) * v) / (2 * ((p' : K) - p)) * Y *
        ∏ j ∈ boxMults p p' (u, v), (1 - Y / (2 * bs * j * kap p p'))) := by
  have h := regVal_genR_box (Y := Y) hbs hp hne hcop hrel hb1 u v hu hv
  rw [prod_box_wv hbs hp hp' hpn hcop hrel, E_star hp hne' hrel hb1] at h
  exact h

end Virasoro.ChainLim
