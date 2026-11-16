import Virasoro.Residue
import Mathlib.RingTheory.LaurentSeries

/-!
# The shifted Laurent recursion and collision moments (paper Definitions 7.1 and 7.3)

`K` is the coefficient field of the Laurent germs (the paper's `K⋆ = ℚ(b⋆, d)`; in the
statements it is realised inside `ℂ(d)`), `bs : K` is the base point `b⋆`, and `d : K` is the
external weight.  All germs are Laurent series in `t = b - b⋆` over `K`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {K : Type*} [Field K] (bs d : K)

/-- The germ `b = b⋆ + t`. -/
noncomputable def bGerm : K⸨X⸩ := HahnSeries.C bs + HahnSeries.single 1 1

/-- `h_a(t) = h_{r,s}(b⋆ + t)`. -/
noncomputable def hG (a : Label) : K⸨X⸩ := kacHL a (bGerm bs)

/-- `R_a(t) = ℛ_{r,s}(b⋆ + t, d)`. -/
noncomputable def RG (a : Label) : K⸨X⸩ := genR a.1 a.2 (bGerm bs) (HahnSeries.C d)

/-- `z_a(t) = h_a(t) + ℓ_a`. -/
noncomputable def zG (a : Label) : K⸨X⸩ := hG bs a + (a.lvl : K⸨X⸩)

theorem lvl_pos_of_mem_labels {N : ℕ} {g : Label} (hg : g ∈ labels N) : 0 < g.lvl := by
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg
  exact Nat.mul_pos hg.1.1.1 hg.1.2.1

/-- The shifted Laurent coefficients `S_{a,M}(t)` (paper Definition 7.1):
`S_{a,0} = 1` and `S_{a,M} = ∑_{ℓ_g ≤ M} R_g / (z_a - h_g) · S_{g,M-ℓ_g}`. -/
noncomputable def SG : ℕ → Label → K⸨X⸩
  | 0, _ => 1
  | M + 1, a =>
      ∑ g ∈ (labels (M + 1)).attach,
        RG bs d g.1 / (zG bs a - hG bs g.1) * SG (M + 1 - g.1.lvl) g.1
termination_by M => M
decreasing_by
  have := lvl_pos_of_mem_labels g.2
  omega

/-- `π_g = max{0, -ord_t R_g(t)}`. -/
noncomputable def piG (g : Label) : ℕ := (-(RG bs d g).order).toNat

/-- `σ_{a,g} = max{0, ord_t (z_a(t) - h_g(t))}`. -/
noncomputable def sigmaG (a g : Label) : ℕ := ((zG bs a - hG bs g).order).toNat

/-- The valuation majorant `W_{a,M}` (paper Lemma 7.2): `W_{a,0} = 0` and
`W_{a,M} = max({0} ∪ {π_g + σ_{a,g} + W_{g,M-ℓ_g} : ℓ_g ≤ M})`. -/
noncomputable def WG : ℕ → Label → ℕ
  | 0, _ => 0
  | M + 1, a =>
      (labels (M + 1)).attach.sup fun g =>
        piG bs d g.1 + sigmaG bs a g.1 + WG (M + 1 - g.1.lvl) g.1
termination_by M => M
decreasing_by
  have := lvl_pos_of_mem_labels g.2
  omega

/-- `B_{a,N}(t) = R_a(t) S_{a,N-ℓ_a}(t)`. -/
noncomputable def BG (N : ℕ) (a : Label) : K⸨X⸩ := RG bs d a * SG bs d (N - a.lvl) a

/-- `δ_a(t) = h_a(t) - λ`. -/
noncomputable def deltaG (lam : K) (a : Label) : K⸨X⸩ := hG bs a - HahnSeries.C lam

/-- `v̂_{a,N} = π_a + W_{a,N-ℓ_a}`. -/
noncomputable def vhat (N : ℕ) (a : Label) : ℕ := piG bs d a + WG bs d (N - a.lvl) a

open Classical in
/-- The a priori pole bound `M̂⋆_{λ,N}` (paper Definition 7.3): the maximum over the collision
class of `1 + ⌊v̂_{a,N}/ε_a⌋`, with `ε_a = ord_t δ_a`, and of `1` when `δ_a = 0`. -/
noncomputable def Mhat (N : ℕ) (lam : K) : ℕ :=
  (collClass N bs lam).sup fun a =>
    if deltaG bs lam a = 0 then 1 else 1 + vhat bs d N a / ((deltaG bs lam a).order).toNat

/-- The collision moments (paper equation (7.1)):
`Ã⋆_{λ,k,N}(d) = CT_t ∑_{a ∈ C⋆_{λ,N}} B_{a,N}(t) δ_a(t)^{k-1}`. -/
noncomputable def Atilde (N : ℕ) (lam : K) (k : ℕ) : K :=
  (∑ a ∈ collClass N bs lam, BG bs d N a * deltaG bs lam a ^ (k - 1)).coeff 0

end Virasoro
