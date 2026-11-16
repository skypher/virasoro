import Virasoro.Proofs.Ising3Mat

/-!
# Proposition 5.11: the earliest Ising collision
-/

namespace Virasoro

open Polynomial

theorem word_one (Y : Nat.Partition 1) : Y.word = [1] := by
  have := isEnum_one.word_mem Y
  simpa using this

/-- The earliest Ising collision: `Δ_{2,1} = Δ_{1,3} = 1/2`; `ξ₂`, `ξ₃` are singular in
`M(1/2,1/2)`; `ker G_3(1/2,1/2) = span{L_{-1}ξ₂, ξ₃}` with Smith exponents `(0,1,1)`; the
crossing scalars and the level-three crossing form; the torus polynomials `E₂`, `E₃`.

Paper label: prop:first-collision -/
theorem prop_first_collision : Stmt_prop_first_collision := by
  refine ⟨⟨by norm_num [isingDelta], by norm_num [isingDelta], ?_⟩, xi2_singular ℂ,
    xi3_singular ℂ, toVerma_L1xi2 ℂ, ker_gram3 ℂ, isSmith_gram3 ℂ, crossScalar_xi2 ℂ,
    crossScalar_xi3 ℂ, ⟨cross1_11 ℂ, cross1_12 ℂ, cross1_21 ℂ, cross1_22 ℂ⟩, ?_,
    torusForm_poly_eq (torus_xi2 ℂ), torusForm_poly_eq (torus_xi3 ℂ)⟩
  · intro a ha a' ha' h
    simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha ha'
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := a'
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := ha
    obtain ⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩ := ha'
    simp only at h1 h2 h3 h4 h5 g1 g2 g3 g4 g5 h
    interval_cases a1 <;> interval_cases a2 <;> interval_cases b1 <;> interval_cases b2 <;>
      simp_all [isingDelta] <;> norm_num at h
  · simp [gram, word_one, gramWord, actSt, actWord, vac]
    norm_num

example : Stmt_prop_first_collision := prop_first_collision

end Virasoro
