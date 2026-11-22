import Virasoro.Proofs.P2Sec11VertexII

/-!
# Proposition 11.2(ii): the two steps of the trace decomposition (paper.tex l.2461–2495)

The proof computes `F_N(c⋆,μ+x,d)` in a basis adapted to the Jantzen filtration and obtains
`F_N(c⋆,μ,d) = ∑_i Tr_{J^i_N/J^{i+1}_N}((B̄^{(i)}_N)⁻¹ ρ̄^{(i)}_N)` (l.2461–2485); it then
identifies the trace of each layer (l.2486–2495).  The two steps are the sub-statements below,
and `sub_vertex_trace_of_layers` composes them.
-/

namespace Virasoro

open Polynomial

/-- `t = Tr_{J^i_N/J^{i+1}_N}((B̄^{(i)}_N)⁻¹ ρ̄^{(i)}_N)`, computed in a finite family `E` of vectors of
`J^i_N(c,μ)` whose classes form a basis of `J^i_N/J^{i+1}_N`: with `A = (B^{(i)}(E_a,E_b))`,
which is then invertible, `t = ∑_{a,b} (A⁻¹)_{ab} ρ^{(i)}(E_b,E_a)`. -/
def IsLayerTrace (c μ d : ℂ) (N i : ℕ) (t : ℂ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (E : κ → (Nat.Partition N → ℂ)),
    (∀ a, E a ∈ jantzenLayer c μ N i) ∧ LinearIndependent ℂ E ∧
    Disjoint (Submodule.span ℂ (Set.range E)) (jantzenLayer c μ N (i + 1)) ∧
    Submodule.span ℂ (Set.range E) ⊔ jantzenLayer c μ N (i + 1) = jantzenLayer c μ N i ∧
    (Matrix.of fun a b => jform c μ N i (E a) (E b)).det ≠ 0 ∧
    t = ∑ a, ∑ b, (Matrix.of fun a b => jform c μ N i (E a) (E b))⁻¹ a b *
      vform c μ d N i (E b) (E a)

/-- First step of the proof of Proposition 11.2(ii), paper.tex l.2461–2485: `F_N(c⋆,μ+x,d)` is
regular at `x = 0` and `F_N(c⋆,μ,d) = ∑_i Tr_{J^i_N/J^{i+1}_N}((B̄^{(i)}_N)⁻¹ ρ̄^{(i)}_N)`.

Demand sheet: `MinimalSetting`, node `μ^ε_{k₀}`, `(k,m)` in the fusion box; every `N ≥ 0`; pole
order `0`; a layer trace `t i` exists for every `i ≥ 0` (in the basis `{v_a(0) : e_a = i}` of
the proof); the sum runs over `0 ≤ i ≤ M` for every `M` beyond which the layers `J^i_N` vanish
(the paper's `j_N(μ)`). -/
def Stmt_sub_vertex_layer_sum : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      let c : ℂ := kacC b
      let μ : ℂ := muOrb p p' r s ε k₀
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      ∀ N : ℕ, poleOrder (Frat c d N) μ = 0 ∧
        ∃ t : ℕ → ℂ, (∀ i, IsLayerTrace c μ d N i (t i)) ∧
          ∀ M : ℕ, (∀ i, M < i → jantzenLayer c μ N i = ⊥) →
            FvalAt c d N μ = ∑ i ∈ Finset.range (M + 1), t i

/-- Second step of the proof of Proposition 11.2(ii), paper.tex l.2486–2495: the trace of the
layer `i = 0` is `T^irr_N(c⋆,μ,d)`; for `i ≥ 1`, `J^i/J^{i+1} ≅ L(c⋆,μ⁺_{k₀+i}) ⊕
L(c⋆,μ⁻_{k₀+i})` is `B̄^{(i)}`-orthogonal, `B̄^{(i)} = γ^±_i B̄_L` and `ρ̄^{(i)} = σ^±_i ρ̄_L` on
the summands, so the trace of the layer is
`∑_± σ^±_i/γ^±_i · T^irr_{N-(μ^±_{k₀+i}-μ)}(c⋆,μ^±_{k₀+i},d)`; and `J^i_N = 0` for `i > N`.

Demand sheet: as in `Stmt_sub_vertex_trace`; every layer trace `t` (any basis of
`J^i_N/J^{i+1}_N`) and all irreducible traces; a summand is absent when its level
`N - (ℓ^±_{k₀+i} - ℓ^ε_{k₀})` is negative. -/
def Stmt_sub_vertex_layer_ident : Prop :=
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
          ∀ N : ℕ,
            (∀ t T₀ : ℂ, IsLayerTrace c μ d N 0 t → IsIrrTrace c μ d N T₀ → t = T₀) ∧
            (∀ i, 1 ≤ i → ∀ t Tp Tm : ℂ, IsLayerTrace c μ d N i t →
              (lev true i ≤ N →
                IsIrrTrace c (muOrb p p' r s true (k₀ + i)) d (N - lev true i) Tp) →
              (lev false i ≤ N →
                IsIrrTrace c (muOrb p p' r s false (k₀ + i)) d (N - lev false i) Tm) →
                t = (if lev true i ≤ N then
                      vform c μ d (lev true i) i (xp i) (xp i) /
                        jform c μ (lev true i) i (xp i) (xp i) * Tp else 0) +
                    (if lev false i ≤ N then
                      vform c μ d (lev false i) i (xm i) (xm i) /
                        jform c μ (lev false i) i (xm i) (xm i) * Tm else 0)) ∧
            (∀ i, N < i → jantzenLayer c μ N i = ⊥)

/-- The second half of Proposition 11.2(ii) from the two steps of its proof. -/
theorem sub_vertex_trace_of_layers (h1 : Stmt_sub_vertex_layer_sum)
    (h2 : Stmt_sub_vertex_layer_ident) : Stmt_sub_vertex_trace := by
  intro p p' r s b hset ε k₀ k m hk hm c μ d lev wp wm hset' xp xm hx N
  obtain ⟨hpole, t, ht, hsum⟩ := h1 p p' r s b hset ε k₀ k m hk hm N
  obtain ⟨h0, hi, hvan⟩ := h2 p p' r s b hset ε k₀ k m hk hm wp wm hset' xp xm hx N
  refine ⟨hpole, fun T₀ Tp Tm hT₀ hTp hTm => ?_⟩
  rw [hsum N hvan, Finset.sum_range_succ', add_comm, h0 (t 0) T₀ (ht 0) hT₀]
  congr 1
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun i => t i) 0 N 1]
  refine Finset.sum_congr (by ext i; simp [Finset.mem_Ico, Finset.mem_Icc]) fun i hi' => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi').1
  exact hi i hi1 (t i) (Tp i) (Tm i) (ht i) (hTp i hi1) (hTm i hi1)

end Virasoro
