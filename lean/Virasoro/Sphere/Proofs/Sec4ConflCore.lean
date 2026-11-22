import Virasoro.Proofs.Sec4Core1
import Virasoro.Sphere.Proofs.Sec4GermRec
import Virasoro.Sphere.Proofs.Sec4Precision

/-!
# Sphere paper Theorem 4.7: `S_{a,M}(t) = H_M(c(b⋆+t), z_a(t), Δ_i)` and the grouped identity

`sphere/paper.tex` l.1392–1399.  By Proposition 4.4 for the germ `b = b⋆ + t` and induction on
`M`, `S_{a,M}(t) = H_M(c(b⋆+t), z_a(t), Δ_i)`; then
`H_N(c(b⋆+t),Δ,Δ_i) = ∑_a B_{a,N}(t)/(Δ - h_a(t))`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

section Hom

variable {F F' : Type*} [Field F] [Field F'] (φ : F →+* F')

theorem map_fusP (r s : ℕ) (b Δa Δb : F) :
    φ (fusP r s b Δa Δb) = fusP r s (φ b) (φ Δa) (φ Δb) := by
  unfold fusP
  simp only [map_mul, map_prod, map_div₀, map_sub, map_add, map_pow, map_inv₀, map_intCast,
    map_ofNat, apply_ite φ, map_one]

theorem map_Rsph (r s : ℕ) (b : F) (Δe : Fin 4 → F) :
    φ (Rsph r s b Δe) = Rsph r s (φ b) (fun i => φ (Δe i)) := by
  rw [Rsph, map_mul, map_mul, map_genA, map_fusP, map_fusP, Rsph]

end Hom

section General

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- The identity (4.3) over a field `𝔽`. -/
def SphRecursionAtF (b : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) : Prop :=
  Hsph (kacC b) Δe N =
    ∑ a ∈ labels N,
      RatFunc.C (Rsph a.1 a.2 b Δe) / (RatFunc.X - RatFunc.C (kacHL a b)) *
        RatFunc.C (evalAt (kacHL a b + (a.lvl : 𝔽)) (Hsph (kacC b) Δe (N - a.lvl)))

theorem evalAt_sph_recursion {b z : 𝔽} {Δe : Fin 4 → 𝔽} {M : ℕ}
    (hrec : SphRecursionAtF b Δe M) (hz : ∀ a ∈ labels M, z ≠ kacHL a b) :
    evalAt z (Hsph (kacC b) Δe M) =
      ∑ a ∈ labels M, Rsph a.1 a.2 b Δe / (z - kacHL a b) *
        evalAt (kacHL a b + (a.lvl : 𝔽)) (Hsph (kacC b) Δe (M - a.lvl)) := by
  unfold SphRecursionAtF at hrec
  rw [hrec]
  have hterm : ∀ a ∈ labels M,
      RatFunc.C (Rsph a.1 a.2 b Δe) / (RatFunc.X - RatFunc.C (kacHL a b)) *
          RatFunc.C (evalAt (kacHL a b + (a.lvl : 𝔽)) (Hsph (kacC b) Δe (M - a.lvl))) =
        algebraMap 𝔽[X] (RatFunc 𝔽) (C (Rsph a.1 a.2 b Δe)) /
            algebraMap 𝔽[X] (RatFunc 𝔽) (X - C (kacHL a b)) *
          algebraMap 𝔽[X] (RatFunc 𝔽) (C (evalAt (kacHL a b + (a.lvl : 𝔽))
            (Hsph (kacC b) Δe (M - a.lvl)))) := by
    intro a _
    simp [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [Finset.sum_congr rfl hterm]
  have hq : ∀ a ∈ labels M, (X - C (kacHL a b) : 𝔽[X]).eval z ≠ 0 := by
    intro a ha
    simpa [sub_ne_zero] using hz a ha
  rw [evalAt_sum fun a ha => (regAt_div z _ (hq a ha)).mul (regAt_algebraMap z _)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [evalAt_mul (regAt_div z _ (hq a ha)) (regAt_algebraMap z _), evalAt_div z _ (hq a ha),
    evalAt_algebraMap]
  simp

end General

section Germ

variable {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] {ι : K →+* L}

/-- The residue germs `R_a(t) = ℛ^sph_{r,s}(b⋆+t,Δ_i)` over a field `K`, the external weights
being constants. -/
noncomputable def RgK (bs : K) (Δe : Fin 4 → K) (a : Label) : K⸨X⸩ :=
  Rsph a.1 a.2 (bGerm bs) (fun i => HahnSeries.C (Δe i))

variable (bs : K) (Δe : Fin 4 → K) (N : ℕ)

/-- Under the generic recursion for the germ `b⋆ + t` (transported to `L⸨t⸩`),
`S_{a,M}(t) = H_M(c(b), z_a(t), Δ_i)`. -/
theorem SGg_eq_eval (hbs : bs ≠ 0)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      SphRecursionAtF (mapL ι (bGerm bs)) (fun i => mapL ι (HahnSeries.C (Δe i))) M) :
    ∀ M, M ≤ N → ∀ a : Label, 0 < a.1 → 0 < a.2 →
      mapL ι (SGg bs (RgK bs Δe) M a) =
        evalAt (mapL ι (zG bs a))
          (Hsph (kacC (mapL ι (bGerm bs))) (fun i => mapL ι (HahnSeries.C (Δe i))) M) := by
  have hb'ne : mapL ι (bGerm bs) ≠ 0 := (map_ne_zero (mapL ι)).2 (bGerm_ne_zero hbs)
  have hirr : SqIrrational (mapL ι (bGerm bs)) := sqIrrational_map _ (sqIrrational_bGerm bs)
  have hzG : ∀ a : Label, mapL ι (zG bs a) =
      kacHL a (mapL ι (bGerm bs)) + ((a.lvl : ℕ) : L⸨X⸩) := by
    intro a
    rw [zG, map_add, map_natCast, hG, map_kacHL]
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM a ha1 ha2
    cases M with
    | zero =>
      rw [SGg_zero, Hsph_zero, map_one]
      simp [evalAt]
    | succ M =>
      have hne : ∀ g ∈ labels (M + 1), mapL ι (zG bs a) ≠ kacHL g (mapL ι (bGerm bs)) := by
        intro g hg
        have hg' := hg
        simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg'
        have := kacH_shift_ne hb'ne hirr (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
          (by exact_mod_cast ha1) (by exact_mod_cast ha2) (by exact_mod_cast hg'.1.1.1)
          (by exact_mod_cast hg'.1.2.1)
        rw [hzG]
        intro heq
        apply this
        rw [sub_eq_zero]
        simpa [kacHL, Label.lvl] using heq
      rw [evalAt_sph_recursion (hrec (M + 1) (by omega) hM) hne, SGg_succ, map_sum,
        ← Finset.sum_attach (labels (M + 1))]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hglvl := lvl_pos_of_mem_labels g.2
      have hg' := g.2
      simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg'
      rw [map_mul, map_div₀, map_sub, ih (M + 1 - g.1.lvl) (by omega) (by omega) g.1
        hg'.1.1.1 hg'.1.2.1, hzG g.1]
      congr 2
      · rw [RgK, map_Rsph]
      · rw [hG, map_kacHL]

/-- The grouped identity at a point `z` away from the Kac weights:
`H_N(c(b⋆+t),z,Δ_i) = ∑_a B_{a,N}(t)/(z - h_a(t))`. -/
theorem grouped_at_sph (hbs : bs ≠ 0) (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      SphRecursionAtF (mapL ι (bGerm bs)) (fun i => mapL ι (HahnSeries.C (Δe i))) M)
    {z : L⸨X⸩} (hz : ∀ a ∈ labels N, z ≠ mapL ι (hG bs a)) :
    evalAt z (Hsph (kacC (mapL ι (bGerm bs))) (fun i => mapL ι (HahnSeries.C (Δe i))) N) =
      ∑ a ∈ labels N, mapL ι (BGg bs (RgK bs Δe) N a) / (z - mapL ι (hG bs a)) := by
  have hhG : ∀ a : Label, mapL ι (hG bs a) = kacHL a (mapL ι (bGerm bs)) := by
    intro a; rw [hG, map_kacHL]
  rw [evalAt_sph_recursion (hrec N hN le_rfl) (fun a ha => by rw [← hhG]; exact hz a ha)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := ha
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha'
  have hS := SGg_eq_eval bs Δe N hbs hrec (N - a.lvl) (Nat.sub_le _ _) a ha'.1.1.1 ha'.1.2.1
  have hzG : mapL ι (zG bs a) = kacHL a (mapL ι (bGerm bs)) + ((a.lvl : ℕ) : L⸨X⸩) := by
    rw [zG, map_add, map_natCast, hG, map_kacHL]
  rw [← hzG, ← hS, BGg, map_mul, RgK, map_Rsph, hhG]
  ring

/-- Proposition 4.4 for the germ `b = b⋆ + t` over `K(Δ)⸨t⸩`. -/
theorem germ_sph_recursion (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) (M : ℕ) (hM : 1 ≤ M) :
    SphRecursionAtF (mapL ι (bGerm bs)) (fun i => mapL ι (HahnSeries.C (Δe i))) M :=
  sph_recursion_of_transcendental hF hK hJ1 hJ2 hH hFus
    (fun _ hP => aeval_map_ne_zero (mapL ι) (aeval_bGerm_ne_zero bs hP)) _ hM

end Germ

end Virasoro.Sphere
