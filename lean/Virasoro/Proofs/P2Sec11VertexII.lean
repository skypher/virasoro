import Virasoro.Proofs.P2Sec11VertexStep

/-!
# Proposition 11.2 from part (i) and the two halves of part (ii) (paper.tex l.2461–2495)

Part (i) is `vertex_part_i`.  Part (ii) is recorded as two sub-statements: the nonvanishing of
`γ^±_i(μ)` (l.2492–2493) and the regularity of `F_N(c⋆,μ+x,d)` at `x = 0` with the Jantzen
trace decomposition (11.3) (l.2461–2495).
-/

namespace Virasoro

open Polynomial

/-- "`γ^±_i(μ) ≠ 0` because `B̄^{(i)}` is nondegenerate" (Proposition 11.2(ii), paper.tex
l.2395, 2492–2493): `γ^±_i(μ) = B^{(i)}(w^±_{k₀+i},w^±_{k₀+i}) ≠ 0` for every `i ≥ 1`.

Demand sheet: `MinimalSetting`; every node `μ = μ^ε_{k₀}`; every family `w^±` with
`OrbitLayerSetting`, in coordinates `xp i`, `xm i` at the levels `ℓ^±_{k₀+i} - ℓ^ε_{k₀}`; every
`i ≥ 1`; both signs.  The external weight `d` does not enter. -/
def Stmt_sub_vertex_gamma : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ : ℕ),
    let c : ℂ := kacC b
    let μ : ℂ := muOrb p p' r s ε k₀
    let lev : Bool → ℕ → ℕ := fun ε' i => ellOrb p p' r s ε' (k₀ + i) - ellOrb p p' r s ε k₀
    ∀ wp wm : ℕ → Verma ℂ c μ, OrbitLayerSetting p p' r s b ε k₀ wp wm →
      ∀ (xp : (i : ℕ) → Nat.Partition (lev true i) → ℂ)
          (xm : (i : ℕ) → Nat.Partition (lev false i) → ℂ),
        (∀ i, 1 ≤ i → Verma.pbwCoord (lev true i) (xp i) = wp i ∧
          Verma.pbwCoord (lev false i) (xm i) = wm i) →
        ∀ i, 1 ≤ i → jform c μ (lev true i) i (xp i) (xp i) ≠ 0 ∧
          jform c μ (lev false i) i (xm i) (xm i) ≠ 0

/-- Regularity of `F_N(c⋆,μ+x,d)` at `x = 0` and the Jantzen trace decomposition (11.3)
(Proposition 11.2(ii), paper.tex l.2385–2396, proof l.2461–2495).

Demand sheet: the hypotheses of `Stmt_prop_jantzen_vertex` (`MinimalSetting`, node `μ^ε_{k₀}`,
`(k,m)` in the fusion box, a family `w^±` with `OrbitLayerSetting` in coordinates); every
`N ≥ 0`; pole order `0` at `μ`; the decomposition for all irreducible traces `T₀`, `Tp i`,
`Tm i`, with the sum over `1 ≤ i ≤ N` and absent terms for negative levels, as in the frozen
statement. -/
def Stmt_sub_vertex_trace : Prop :=
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
          ∀ N : ℕ, poleOrder (Frat c d N) μ = 0 ∧
            ∀ (T₀ : ℂ) (Tp Tm : ℕ → ℂ), IsIrrTrace c μ d N T₀ →
              (∀ i, 1 ≤ i → lev true i ≤ N →
                IsIrrTrace c (muOrb p p' r s true (k₀ + i)) d (N - lev true i) (Tp i)) →
              (∀ i, 1 ≤ i → lev false i ≤ N →
                IsIrrTrace c (muOrb p p' r s false (k₀ + i)) d (N - lev false i) (Tm i)) →
                FvalAt c d N μ = T₀ + ∑ i ∈ Finset.Icc 1 N,
                  ((if lev true i ≤ N then
                      vform c μ d (lev true i) i (xp i) (xp i) /
                        jform c μ (lev true i) i (xp i) (xp i) * Tp i else 0) +
                    (if lev false i ≤ N then
                      vform c μ d (lev false i) i (xm i) (xm i) /
                        jform c μ (lev false i) i (xm i) (xm i) * Tm i else 0))

set_option maxHeartbeats 800000 in
/-- Proposition 11.2 from the two halves of its part (ii). -/
theorem prop_jantzen_vertex_of_subs (hJ : Cited_JantzenLayersOrbit)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) (hA : Stmt_sub_vertex_gamma) (hB : Stmt_sub_vertex_trace) :
    Stmt_prop_jantzen_vertex := by
  intro p p' r s b hset ε k₀ k m hk hm
  refine ⟨fun T hT i N₁ N₂ a a₂ wa wb ha hb => ?_, fun wp wm hset' xp xm hx => ⟨?_, ?_⟩⟩
  · have h := vertex_part_i hJ hH hU hF hI p p' r s b hset ε k₀ k m hk hm T hT i N₁ N₂ a a₂ wa wb
      ha hb
    unfold VertexClausesAt at h
    exact h
  · exact hA p p' r s b hset ε k₀ wp wm hset' xp xm hx
  · exact hB p p' r s b hset ε k₀ k m hk hm wp wm hset' xp xm hx

end Virasoro
