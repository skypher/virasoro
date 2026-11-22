import Virasoro.Proofs.P2Sec11LayerSum3

/-!
# Proposition 11.2(ii), second step: reduction to the layers `i ≥ 1` (paper.tex l.2486–2495)

`J^i_N(c⋆,μ) = 0` for `i > N` (the levels of `w^±_{k₀+i}` are at least `i`), so the sum over the
layers stops at `N`.  The identification of the layer `i = 0` (l.2486) and of the layers `i ≥ 1`
(l.2487–2495) are the sub-statements `Stmt_sub_vertex_layer_zero`, `Stmt_sub_vertex_layer_pos`.
-/

namespace Virasoro

open Polynomial Verma

variable {p p' r s : ℕ}

/-- `ℓ^{ε'}_{k₀+i} - ℓ^ε_{k₀} ≥ i`. -/
theorem ellOrb_add_le (hp : 0 < p) (hp' : 0 < p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') (ε : Bool) (k₀ : ℕ) :
    ∀ i : ℕ, 1 ≤ i → ∀ ε' : Bool, ellOrb p p' r s ε k₀ + i ≤ ellOrb p p' r s ε' (k₀ + i) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact fun ε' => ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε k₀ ε'
  | succ i _ ih =>
    intro ε'
    have h1 := ih true
    have h2 := ellOrb_lt_succ hp hp' hr0 hr hs0 hs true (k₀ + i) ε'
    have e : k₀ + (i + 1) = k₀ + i + 1 := rfl
    rw [e]
    omega

/-- `J^i_N(c⋆,μ) = 0` for `i > N`. -/
theorem jantzenLayer_eq_bot {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) (k₀ : ℕ)
    {wp wm : ℕ → Verma ℂ (kacC b) (muOrb p p' r s ε k₀)}
    (hw : OrbitLayerSetting p p' r s b ε k₀ wp wm) {N i : ℕ} (hi : N < i) :
    jantzenLayer (kacC b) (muOrb p p' r s ε k₀) N i = ⊥ := by
  obtain ⟨hp2, hp2', -, hr0, hr, hs0, hs, -, -⟩ := id hset
  have hi1 : 1 ≤ i := by omega
  obtain ⟨hsing, hlayer⟩ := hw
  obtain ⟨hsp, hsm⟩ := hsing i hi1
  have hlev : ∀ ε', N < ellOrb p p' r s ε' (k₀ + i) - ellOrb p p' r s ε k₀ := fun ε' => by
    have := ellOrb_add_le (by omega) (by omega) hr0 hr hs0 hs ε k₀ i hi1 ε'
    omega
  rw [eq_bot_iff]
  intro u hu
  have hx : pbwCoord (c := kacC b) (h := muOrb p p' r s ε k₀) N u ∈
      jantzen (kacC b) (muOrb p p' r s ε k₀) i := pbwCoord_mem_jantzen hu
  rw [hlayer i hi1, Submodule.mem_sup] at hx
  obtain ⟨x₁, h1, x₂, h2, e⟩ := hx
  have e' := congrArg (Verma.comp N) e
  rw [map_add, comp_negSpan_eq_zero (mem_level_of_L_zero hsp.2.1) (hlev true) h1,
    comp_negSpan_eq_zero (mem_level_of_L_zero hsm.2.1) (hlev false) h2, add_zero,
    comp_pbwCoord_same] at e'
  rw [Submodule.mem_bot, ← e']

/-- The layer `i = 0` in the proof of Proposition 11.2(ii), paper.tex l.2486:
"`J⁰/J¹ = L(c⋆,μ)` gives `T^irr_N(c⋆,μ,d)`".

Demand sheet: `MinimalSetting`, node `μ^ε_{k₀}`, `(k,m)` in the fusion box; every `N`; every
layer trace `t` of the layer `0` (any basis of `M(c⋆,μ)_N/J¹_N`) and every irreducible trace
`T₀`. -/
def Stmt_sub_vertex_layer_zero : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let μ : ℂ := muOrb p p' r s ε k₀
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      ∀ (N : ℕ) (t T₀ : ℂ), IsLayerTrace c μ d N 0 t → IsIrrTrace c μ d N T₀ → t = T₀

/-- Identification of the layers `i ≥ 1` in the proof of Proposition 11.2(ii), paper.tex
l.2487–2495: `J^i/J^{i+1} ≅ L(c⋆,μ⁺_{k₀+i}) ⊕ L(c⋆,μ⁻_{k₀+i})` is `B̄^{(i)}`-orthogonal,
`B̄^{(i)} = γ^±_i B̄_L` and `ρ̄^{(i)} = σ^±_i ρ̄_L` on the summands, so
`Tr_{J^i_N/J^{i+1}_N}((B̄^{(i)}_N)⁻¹ρ̄^{(i)}_N) =
∑_± σ^±_i/γ^±_i · T^irr_{N-(μ^±_{k₀+i}-μ)}(c⋆,μ^±_{k₀+i},d)`.

Demand sheet: as in `Stmt_sub_vertex_layer_ident`, for `i ≥ 1` only; every layer trace `t` and
all irreducible traces `Tp`, `Tm`; a summand is absent when its level is negative. -/
def Stmt_sub_vertex_layer_pos : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let μ : ℂ := muOrb p p' r s ε k₀
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      let lev : Bool → ℕ → ℕ := fun ε' i => ellOrb p p' r s ε' (k₀ + i) - ellOrb p p' r s ε k₀
      ∀ wp wm : ℕ → Verma ℂ c μ, OrbitLayerSetting p p' r s b ε k₀ wp wm →
        ∀ (xp : (i : ℕ) → Nat.Partition (lev true i) → ℂ)
            (xm : (i : ℕ) → Nat.Partition (lev false i) → ℂ),
          (∀ i, 1 ≤ i → Verma.pbwCoord (lev true i) (xp i) = wp i ∧
            Verma.pbwCoord (lev false i) (xm i) = wm i) →
          ∀ N i : ℕ, 1 ≤ i → ∀ t Tp Tm : ℂ, IsLayerTrace c μ d N i t →
            (lev true i ≤ N →
              IsIrrTrace c (muOrb p p' r s true (k₀ + i)) d (N - lev true i) Tp) →
            (lev false i ≤ N →
              IsIrrTrace c (muOrb p p' r s false (k₀ + i)) d (N - lev false i) Tm) →
              t = (if lev true i ≤ N then
                    vform c μ d (lev true i) i (xp i) (xp i) /
                      jform c μ (lev true i) i (xp i) (xp i) * Tp else 0) +
                  (if lev false i ≤ N then
                    vform c μ d (lev false i) i (xm i) (xm i) /
                      jform c μ (lev false i) i (xm i) (xm i) * Tm else 0)

/-- The second step of Proposition 11.2(ii) from its two layer identifications. -/
theorem sub_vertex_layer_ident_of_layers (h0 : Stmt_sub_vertex_layer_zero)
    (h1 : Stmt_sub_vertex_layer_pos) : Stmt_sub_vertex_layer_ident := by
  intro p p' r s b hset ε k₀ k m hk hm c μ d lev wp wm hw xp xm hx N
  refine ⟨fun t T₀ ht hT => h0 p p' r s b hset ε k₀ k m hk hm N t T₀ ht hT,
    fun i hi t Tp Tm ht hTp hTm =>
      h1 p p' r s b hset ε k₀ k m hk hm wp wm hw xp xm hx N i hi t Tp Tm ht hTp hTm,
    fun i hi => jantzenLayer_eq_bot hset ε k₀ hw hi⟩

end Virasoro
