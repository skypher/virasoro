import Virasoro.Proofs.Sec6LimWt
import Virasoro.Proofs.Sec4Core1

/-!
# Proposition 6.7, the chain limit (a): `H_N` along the germ tends to the chain sum (l.1136–1141)

Along `b = b⋆ + t`, `Δ = Z(t)` with `Z(0) = wt(m²)`, `Z'(0) = ζ`, and `d = tY`, the generic
recursion (Proposition 6.4, over the field `K⸨X⸩` at the transcendental germ) expands
`H_M(c(b), Z, d)` into chains; a step `g` colliding with the current momentum contributes
`(ℛ_g/t)/((Z − h_g)/t) → lead_g/(ζ − h'_g)`, any other step contributes `t · (regular)`.  The limit
is `chainK`, the chain sum with b-slopes `h'_g = 2b⋆ḣ_g` (paper.tex l.1139–1141).
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries
open Finset

variable {K : Type} [Field K] [CharZero K]

/-- The limit of `ℛ_g/t` (b-coordinate): `ρ_g Y ∏_j (1 − Y/(2b⋆ jκ₀))`. -/
noncomputable def leadK (p p' : ℕ) (bs Y : K) (g : Label) : K :=
  -((p' : K) * g.1 - (p : K) * g.2) / (2 * ((p' : K) - p)) * Y *
    ∏ j ∈ boxMults p p' g, (1 - Y / (2 * bs * j * kap p p'))

/-- The chain sum at the germ: from squared momentum `m2` and slope `ζ`, at level `M`. -/
noncomputable def chainK (p p' : ℕ) (bs Y : K) : ℕ → ℕ → ℤ → K → K
  | 0, M, _, _ => if M = 0 then 1 else 0
  | fuel + 1, M, m2, ζ =>
      if M = 0 then 1
      else ∑ g ∈ labels M,
        if ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = m2 then
          (ζ - 2 * bs * hdotK p p' g)⁻¹ * leadK p p' bs Y g *
            chainK p p' bs Y fuel (M - g.lvl) (((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2)
              (2 * bs * hdotK p p' g)
        else 0

theorem RegVal.sum' {α : Type*} {s : Finset α} {f : α → K⸨X⸩} {v : α → K}
    (h : ∀ i ∈ s, RegVal (f i) (v i)) : RegVal (∑ i ∈ s, f i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨OrdGE.zero 0, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem regVal_ne_zero {u : K⸨X⸩} {v : K} (hu : RegVal u v) (hv : v ≠ 0) : u ≠ 0 := by
  intro h0
  rw [h0] at hu
  exact hv (by simpa using hu.2.symm)

/-- `H_M` along the germ (paper.tex l.1136–1141). -/
theorem germ_chain (hrec : GenericRecursionUniform) {bs Y : K} (hbs : bs ≠ 0) {p p' : ℕ}
    (hp : (p : K) ≠ 0) (hp' : (p' : K) ≠ 0) (hp0 : 0 < p) (hp'0 : 0 < p') (hne : p ≠ p')
    (hne' : (p' : K) - p ≠ 0) (hcop : Nat.Coprime p p') (hrel : (p : K) * bs ^ 2 + p' = 0)
    (hb1 : bs ^ 2 + 1 ≠ 0) :
    ∀ (M fuel : ℕ), M ≤ fuel → ∀ (m2 : ℤ) (Z : K⸨X⸩) (ζ : K),
      RegVal Z (wtK p p' m2) → RegVal ((Z - HahnSeries.C (wtK p p' m2)) / tX) ζ →
      (∀ g ∈ labels M, ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = m2 → ζ ≠ 2 * bs * hdotK p p' g) →
      RegVal (evalAt Z (Hrat (kacC (bGerm bs)) (tX * HahnSeries.C Y) M))
        (chainK p p' bs Y fuel M m2 ζ) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro fuel hMf m2 Z ζ hZ hZs hsl
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [Hrat_zero]
    have h1 : evalAt Z (1 : RatFunc K⸨X⸩) = 1 := by simp [evalAt]
    rw [h1]
    have hc : chainK p p' bs Y fuel 0 m2 ζ = 1 := by
      cases fuel <;> simp [chainK]
    rw [hc]
    simpa using regVal_C (1 : K)
  · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨S, hS, hall⟩ := hrec M hM
    have hGR := hall (K⸨X⸩) (bGerm bs) (tX * HahnSeries.C Y) (bGerm_ne_zero hbs)
      (fun P hP => aeval_bGerm_ne_zero bs (hS P hP))
    have hb := regVal_bGerm (K := K) bs
    have hX : RegVal (tX : K⸨X⸩) 0 := ⟨ordGE_single_one, by simp [tX]⟩
    -- the facts for one label
    have hlab : ∀ a ∈ labels M, Z ≠ kacHL a (bGerm bs) ∧
        RegVal (genR a.1 a.2 (bGerm bs) (tX * HahnSeries.C Y) / (Z - kacHL a (bGerm bs)) *
            evalAt (kacHL a (bGerm bs) + (a.lvl : K⸨X⸩))
              (Hrat (kacC (bGerm bs)) (tX * HahnSeries.C Y) (M - a.lvl)))
          (if ((p' : ℤ) * a.1 - (p : ℤ) * a.2) ^ 2 = m2 then
            (ζ - 2 * bs * hdotK p p' a)⁻¹ * leadK p p' bs Y a *
              chainK p p' bs Y f (M - a.lvl) (((p' : ℤ) * a.1 + (p : ℤ) * a.2) ^ 2)
                (2 * bs * hdotK p p' a)
          else 0) := by
      intro a ha
      obtain ⟨ha1, ha2, ha3⟩ := (ChainEval.mem_labels_iff M a).1 ha
      have hlv : 1 ≤ a.lvl := by
        have := Nat.mul_le_mul ha1 ha2
        unfold Label.lvl
        exact this
      -- the inner evaluation, by the induction hypothesis
      have hstar := kacHL_star hbs hp hp' hrel a
      have hwt := wtK_add_lvl (K := K) hp hp' a
      have hZ' : RegVal (kacHL a (bGerm bs) + (a.lvl : K⸨X⸩))
          (wtK p p' (((p' : ℤ) * a.1 + (p : ℤ) * a.2) ^ 2)) := by
        rw [← hwt, ← hstar]
        exact (regVal_kacH hbs _ _).add (regVal_natCast a.lvl)
      have hZs' : RegVal ((kacHL a (bGerm bs) + (a.lvl : K⸨X⸩) -
          HahnSeries.C (wtK p p' (((p' : ℤ) * a.1 + (p : ℤ) * a.2) ^ 2))) / tX)
          (2 * bs * hdotK p p' a) := by
        have e : kacHL a (bGerm bs) + (a.lvl : K⸨X⸩) -
            HahnSeries.C (wtK p p' (((p' : ℤ) * a.1 + (p : ℤ) * a.2) ^ 2)) =
            kacHL a (bGerm bs) - HahnSeries.C (kacHL a bs) := by
          rw [← hwt, ← hstar, map_add, map_natCast]
          ring
        rw [e]
        exact regVal_kacH_slope hbs hp hp' hrel a
      have hsl' : ∀ g ∈ labels (M - a.lvl),
          ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = ((p' : ℤ) * a.1 + (p : ℤ) * a.2) ^ 2 →
            2 * bs * hdotK p p' a ≠ 2 * bs * hdotK p p' g := by
        intro g hg hc he
        obtain ⟨hg1, hg2, _⟩ := (ChainEval.mem_labels_iff _ g).1 hg
        have h2 : (2 * bs) ≠ 0 := mul_ne_zero two_ne_zero hbs
        exact hdotK_ne hp hp' hp0 hp'0 a g ha1 ha2 hg1 hg2 hc (mul_left_cancel₀ h2 he)
      have hIH := ih (M - a.lvl) (by omega) f (by omega) _ _ _ hZ' hZs' hsl'
      -- the factor `ℛ_a/(Z − h_a)`
      have hR := regVal_genR (Y := Y) hbs hp hp' (by omega) hne hne' hcop hrel hb1 a.1 a.2
        (by omega) (by omega)
      by_cases hc : ((p' : ℤ) * a.1 - (p : ℤ) * a.2) ^ 2 = m2
      · rw [if_pos hc]
        have hz0 : wtK (K := K) p p' m2 = kacHL a bs := by rw [hstar, hc]
        have hD : RegVal ((Z - kacHL a (bGerm bs)) / tX) (ζ - 2 * bs * hdotK p p' a) := by
          have e : (Z - kacHL a (bGerm bs)) / tX =
              (Z - HahnSeries.C (wtK p p' m2)) / tX -
                (kacHL a (bGerm bs) - HahnSeries.C (kacHL a bs)) / tX := by
            rw [hz0]
            field_simp [tX_ne_zero]
            ring
          rw [e]
          exact hZs.sub (regVal_kacH_slope hbs hp hp' hrel a)
        have hDv : ζ - 2 * bs * hdotK p p' a ≠ 0 := sub_ne_zero.2 (hsl a ha hc)
        have hZne : Z ≠ kacHL a (bGerm bs) := by
          intro he
          apply regVal_ne_zero hD hDv
          rw [he, sub_self, zero_div]
        refine ⟨hZne, ?_⟩
        have e2 : genR a.1 a.2 (bGerm bs) (tX * HahnSeries.C Y) / (Z - kacHL a (bGerm bs)) =
            (genR a.1 a.2 (bGerm bs) (tX * HahnSeries.C Y) / tX) /
              ((Z - kacHL a (bGerm bs)) / tX) := by
          field_simp [tX_ne_zero, sub_ne_zero.2 hZne]
        rw [e2]
        have := ((hR.div hD hDv).mul hIH)
        convert this using 1
        simp only [Prod.mk.eta]
        unfold leadK
        ring
      · rw [if_neg hc]
        have hDv : wtK (K := K) p p' m2 - kacHL a bs ≠ 0 := by
          rw [hstar]
          intro h0
          exact hc (wtK_inj hp hp' (sub_eq_zero.1 h0)).symm
        have hD : RegVal (Z - kacHL a (bGerm bs)) (wtK p p' m2 - kacHL a bs) :=
          hZ.sub (regVal_kacH hbs _ _)
        have hZne : Z ≠ kacHL a (bGerm bs) := by
          intro he
          apply regVal_ne_zero hD hDv
          rw [he, sub_self]
        refine ⟨hZne, ?_⟩
        have e2 : genR a.1 a.2 (bGerm bs) (tX * HahnSeries.C Y) =
            tX * (genR a.1 a.2 (bGerm bs) (tX * HahnSeries.C Y) / tX) := by
          field_simp [tX_ne_zero]
        rw [e2]
        have := ((hX.mul hR).div hD hDv).mul hIH
        convert this using 1
        simp
    rw [evalAt_recursion hGR (fun a ha => (hlab a ha).1)]
    have hsum := RegVal.sum' (fun a ha => (hlab a ha).2)
    convert hsum using 1
    rw [chainK, if_neg (by omega)]

end Virasoro.ChainLim
