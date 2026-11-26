import Virasoro.Shifted

/-!
# Chains of colliding labels (paper Section 7.2, Definition 7.9)

`K` is the coefficient field of the Laurent germs in `t = b - b⋆` (as in `Virasoro.Shifted`),
`bs : K` is `b⋆` and `d : K` the external weight.

* `delG bs g` is `δ_g(t) = h_g(t) - w_g`, with `w_g = h_g(b⋆)` the weight of the label `g`.
* A chain from `λ` of level `D` is a sequence `(g₀, …, g_L)` with `w_{g₀} = λ`,
  `w_{gᵢ} = w_{gᵢ₋₁} + ℓ_{gᵢ₋₁}` and `∑ ℓ_{gᵢ} = D`; it ends at `μ = λ + D`.
  `chainFn bs d λ D k j` is the chain function `c^{(k)}_{λ→λ+D,j}`, the sum over these chains of
  `R_{g₀} δ_{g₀}^{k-1} ∏_{i ≥ 1} R_{gᵢ}/(δ_{gᵢ₋₁} - δ_{gᵢ}) · δ_{g_L}^j / j!`.  It is defined by
  recursion on the level: `chainTail bs d j D ν y` is the same sum over the chains that start at
  the weight `ν` with total level `D`, entered from a label whose coordinate is `y`, so that the
  first link contributes `R_{g₁}/(y - δ_{g₁})`.
* `phiRem bs d M μ j` is `∂_Δ^j Reg^{(M)}_μ(b⋆+t, μ)`, where
  `Reg^{(M)}_μ = ∑_{ℓ_g ≤ M, w_g ≠ μ} B_{g,M}(t)/(Δ - h_g(t))` is the sum of the collision groups of
  `H_M` other than the one at `μ` (Lemma 7.11): `∂_Δ^j` of `B/(Δ - h)` at `μ` is
  `B (-1)^j j!/(μ - h)^{j+1}`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {K : Type*} [Field K] (bs d : K)

/-- `δ_g(t) = h_g(t) - w_g` with `w_g = h_g(b⋆)`. -/
noncomputable def delG (g : Label) : K⸨X⸩ := deltaG bs (kacHL g bs) g

theorem lvl_le_of_mem_labels {D : ℕ} {g : Label} (hg : g ∈ labels D) : g.lvl ≤ D := by
  simp only [labels, Finset.mem_filter] at hg
  exact hg.2

open Classical in
/-- The labels `g` with `ℓ_g ≤ D` and weight `w_g = ν`. -/
noncomputable def labelsAt (D : ℕ) (ν : K) : Finset Label :=
  (labels D).filter fun g => kacHL g bs = ν

theorem mem_labels_of_mem_labelsAt {D : ℕ} {ν : K} {g : Label} (hg : g ∈ labelsAt bs D ν) :
    g ∈ labels D := by
  classical
  unfold labelsAt at hg
  exact (Finset.mem_filter.1 hg).1

/-- Sum over the chains starting at weight `ν` with total level `D`, entered from a label with
coordinate `y`, of `R_{g₁}/(y - δ_{g₁}) ∏_{i ≥ 2} R_{gᵢ}/(δ_{gᵢ₋₁} - δ_{gᵢ}) · δ_{g_L}^j/j!`. -/
noncomputable def chainTail (j : ℕ) : ℕ → K → K⸨X⸩ → K⸨X⸩
  | D, ν, y =>
      ∑ g ∈ (labelsAt bs D ν).attach,
        RG bs d g.1 / (y - delG bs g.1) *
          (if g.1.lvl = D then delG bs g.1 ^ j / (j.factorial : K⸨X⸩)
            else chainTail j (D - g.1.lvl) (ν + (g.1.lvl : K)) (delG bs g.1))
termination_by D => D
decreasing_by
  have h1 := lvl_pos_of_mem_labels (mem_labels_of_mem_labelsAt bs g.2)
  have h2 := lvl_le_of_mem_labels (mem_labels_of_mem_labelsAt bs g.2)
  omega

/-- The chain function `c^{(k)}_{λ→λ+D,j}` (paper Definition 7.9). -/
noncomputable def chainFn (lam : K) (D k j : ℕ) : K⸨X⸩ :=
  ∑ a ∈ labelsAt bs D lam,
    RG bs d a * delG bs a ^ (k - 1) *
      (if a.lvl = D then delG bs a ^ j / (j.factorial : K⸨X⸩)
        else chainTail bs d j (D - a.lvl) (lam + (a.lvl : K)) (delG bs a))

/-- The full moment `C_{λ,k,N}(t) = ∑_{a ∈ C⋆_{λ,N}} B_{a,N}(t) δ_a(t)^{k-1}` (Lemma 7.8). -/
noncomputable def fullMoment (N : ℕ) (lam : K) (k : ℕ) : K⸨X⸩ :=
  ∑ a ∈ collClass N bs lam, BG bs d N a * deltaG bs lam a ^ (k - 1)

open Classical in
/-- `φ^{(M)}_{μ,j}(t) = ∂_Δ^j Reg^{(M)}_μ(b⋆+t, μ)
= ∑_{ℓ_g ≤ M, w_g ≠ μ} B_{g,M}(t) (-1)^j j!/(μ - h_g(t))^{j+1}` (Lemmas 7.11 and 7.12). -/
noncomputable def phiRem (M : ℕ) (mu : K) (j : ℕ) : K⸨X⸩ :=
  ∑ g ∈ (labels M).filter (fun g => kacHL g bs ≠ mu),
    BG bs d M g * ((-1 : K⸨X⸩) ^ j * (j.factorial : K⸨X⸩)) /
      (HahnSeries.C mu - hG bs g) ^ (j + 1)

end Virasoro
