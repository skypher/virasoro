import Virasoro.Shifted
import Virasoro.Irreducible
import Virasoro.Sphere.Defs

/-!
# Sphere residue data and the shifted Laurent recursion (sphere paper Definitions 4.1, 4.5)

The recursion of Definition 4.5 has the same shape as the torus recursion of
`Virasoro/Shifted.lean`, with the residue germs `R_a(t)` as a parameter `Rg`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

/-- `ℛ^sph_{r,s}(b,Δ_i) = 𝒜_{r,s}(b) P_{r,s}(b,Δ₄,Δ₃) P_{r,s}(b,Δ₁,Δ₂)` (sphere paper
Definition 4.1); `P_{r,s}` is `fusP`. -/
noncomputable def Rsph {𝔽 : Type*} [Field 𝔽] (r s : ℕ) (b : 𝔽) (Δe : Fin 4 → 𝔽) : 𝔽 :=
  genA r s b * fusP r s b (Δe 3) (Δe 2) * fusP r s b (Δe 0) (Δe 1)

variable {K : Type*} [Field K] (bs : K) (Rg : Label → K⸨X⸩)

/-- The shifted Laurent coefficients `S_{a,M}(t)` for the residue germs `Rg`. -/
noncomputable def SGg : ℕ → Label → K⸨X⸩
  | 0, _ => 1
  | M + 1, a =>
      ∑ g ∈ (labels (M + 1)).attach,
        Rg g.1 / (zG bs a - hG bs g.1) * SGg (M + 1 - g.1.lvl) g.1
termination_by M => M
decreasing_by
  have := lvl_pos_of_mem_labels g.2
  omega

/-- `π_g = max{0, -ord_t R_g(t)}`. -/
noncomputable def piGg (g : Label) : ℕ := (-(Rg g).order).toNat

/-- The valuation majorant `W_{a,M}`. -/
noncomputable def WGg : ℕ → Label → ℕ
  | 0, _ => 0
  | M + 1, a =>
      (labels (M + 1)).attach.sup fun g =>
        piGg Rg g.1 + sigmaG bs a g.1 + WGg (M + 1 - g.1.lvl) g.1
termination_by M => M
decreasing_by
  have := lvl_pos_of_mem_labels g.2
  omega

/-- `B_{a,N}(t) = R_a(t) S_{a,N-ℓ_a}(t)`. -/
noncomputable def BGg (N : ℕ) (a : Label) : K⸨X⸩ := Rg a * SGg bs Rg (N - a.lvl) a

/-- `v̂_{a,N} = π_a + W_{a,N-ℓ_a}`. -/
noncomputable def vhatg (N : ℕ) (a : Label) : ℕ := piGg Rg a + WGg bs Rg (N - a.lvl) a

open Classical in
/-- The a priori pole bound `M̂⋆_{λ,N}`. -/
noncomputable def Mhatg (N : ℕ) (lam : K) : ℕ :=
  (collClass N bs lam).sup fun a =>
    if deltaG bs lam a = 0 then 1 else 1 + vhatg bs Rg N a / ((deltaG bs lam a).order).toNat

/-- The collision moments `Ã⋆_{λ,k,N} = CT_t ∑_{a ∈ C⋆_{λ,N}} B_{a,N}(t) δ_a(t)^{k-1}`. -/
noncomputable def Atildeg (N : ℕ) (lam : K) (k : ℕ) : K :=
  (∑ a ∈ collClass N bs lam, BGg bs Rg N a * deltaG bs lam a ^ (k - 1)).coeff 0

/-- The sphere residue germs `R_a(t) = ℛ^sph_{r,s}(b⋆+t,Δ_i)` over `K⋆ = ℂ(Δ₁,…,Δ₄)`, with the
external weights constant in `t`. -/
noncomputable def RgSph (b : ℂ) (a : Label) : K4⸨X⸩ :=
  Rsph a.1 a.2 (bGerm (cK b)) (fun i => HahnSeries.C (ΔK i))

end Virasoro.Sphere
