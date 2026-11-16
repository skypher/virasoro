import Virasoro.Proofs.GenericF
import Virasoro.Proofs.EtaPartition
import Virasoro.Statements.Sec6

/-!
# Proposition 6.5: the generic eta-reduced recursion, uniformly in the field

For generic `b`, multiplying the partial-fraction expansions of `F_{N-j}` by the Euler
coefficients and summing gives
`H_N(c(b),Δ,d) = ∑_{ℓ_a ≤ N} ℛ_a(b,d)/(Δ - h_a(b)) · H_{N-ℓ_a}(c(b), h_a(b)+ℓ_a, d)`.
The genericity conditions are the nonvanishing at `b` of finitely many nonzero polynomials
over `ℚ`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] {hN : NormalizationIdentities} {N : ℕ} {b : 𝔽}

/-- The generic recursion at a generic value of `b`. -/
theorem GenericAt.recursion (hK : Cited_KacDeterminant) (hgen : GenericAt hN N b)
    (hN1 : 1 ≤ N) (d : 𝔽) : GenericRecursionAt 𝔽 b d N := by
  classical
  unfold GenericRecursionAt
  have hHval : ∀ a ∈ labels N,
      RatFunc.eval (RingHom.id 𝔽) (kacHL a b + (a.lvl : 𝔽)) (Hrat (kacC b) d (N - a.lvl))
        = Hval (kacC b) d (kacHL a b + (a.lvl : 𝔽)) (N - a.lvl) := by
    intro a ha
    exact evalAt_Hrat fun M hM => hgen.gram_det_shift_ne hK ha (by omega)
  have heta : (∑ j ∈ Finset.range (N + 1),
      (eta j : RatFunc 𝔽) * (Fintype.card (Nat.Partition (N - j)) : RatFunc 𝔽)) = 0 := by
    have := congrArg (Int.cast : ℤ → RatFunc 𝔽) (eta_partition N)
    push_cast at this
    rw [this, if_neg (by omega)]
  have hF : ∀ j ∈ Finset.range (N + 1), (eta j : RatFunc 𝔽) * Frat (kacC b) d (N - j)
      = (eta j : RatFunc 𝔽) * (Fintype.card (Nat.Partition (N - j)) : RatFunc 𝔽)
        + ∑ a ∈ labels (N - j), (eta j : RatFunc 𝔽) *
            (RatFunc.C (genR a.1 a.2 b d *
                Fval (kacC b) d (kacHL a b + (a.lvl : 𝔽)) (N - j - a.lvl))
              / (RatFunc.X - RatFunc.C (kacHL a b))) := by
    intro j _
    rw [hgen.Frat_eq hK (Nat.sub_le N j) d, mul_add, Finset.mul_sum]
  rw [Hrat, Finset.sum_congr rfl hF, Finset.sum_add_distrib, heta, zero_add]
  have hcomm : ∀ (j : ℕ) (a : Label), j ∈ Finset.range (N + 1) ∧ a ∈ labels (N - j)
      ↔ j ∈ Finset.range (N - a.lvl + 1) ∧ a ∈ labels N := by
    intro j a
    simp only [Finset.mem_range, mem_labels, Label.lvl]
    omega
  rw [Finset.sum_comm' hcomm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hHval a ha, Hval, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.sub_right_comm, map_mul, map_mul, map_intCast]
  ring

/-- The polynomials `m X² + n` over `ℚ` with small integer coefficients, not both zero. -/
noncomputable def linPolys (N : ℕ) : Finset ℚ[X] :=
  open Classical in
  ((Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) ×ˢ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))).filter
    fun mn => mn.1 ≠ 0 ∨ mn.2 ≠ 0).image fun mn => C (mn.1 : ℚ) * X ^ 2 + C (mn.2 : ℚ)

/-- The denominators of the coordinates of the normalized singular vectors of level at most
`N`. -/
noncomputable def denomPolys (hN : NormalizationIdentities) (N : ℕ) : Finset ℚ[X] :=
  open Classical in
  (labels N).biUnion fun a =>
    Finset.univ.image fun Y : Nat.Partition (a.1 * a.2) => RatFunc.denom (normP hN a.1 a.2 Y)

/-- Proposition 6.5 in the form used by its consumers: for each `N ≥ 1` the generic recursion
holds over every field of characteristic zero at every `b ≠ 0` that is a root of none of
finitely many nonzero polynomials over `ℚ`. -/
theorem genericRecursionUniform (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    GenericRecursionUniform := by
  classical
  intro N hN1
  refine ⟨linPolys N ∪ denomPolys hH N, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.1 hP with hP | hP
    · simp only [linPolys, Finset.mem_image, Finset.mem_filter] at hP
      obtain ⟨mn, ⟨-, hmn⟩, rfl⟩ := hP
      intro h0
      have h2 := congrArg (fun P : ℚ[X] => P.coeff 2) h0
      have h3 := congrArg (fun P : ℚ[X] => P.coeff 0) h0
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_zero] at h2 h3
      norm_num at h2 h3
      rcases hmn with h | h
      · exact h h2
      · exact h h3
    · simp only [denomPolys, Finset.mem_biUnion, Finset.mem_image] at hP
      obtain ⟨a, -, Y, -, rfl⟩ := hP
      exact RatFunc.denom_ne_zero _
  · intro 𝔽 _ _ b d hb hS
    have hgen : GenericAt hH N b := by
      refine ⟨hb, ?_, ?_⟩
      · intro m n hm hn hmn h0
        have hmem : (C (m : ℚ) * X ^ 2 + C (n : ℚ) : ℚ[X]) ∈ linPolys N := by
          simp only [linPolys, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
            Finset.mem_Icc]
          rw [abs_le] at hm hn
          exact ⟨(m, n), ⟨⟨⟨hm.1, hm.2⟩, ⟨hn.1, hn.2⟩⟩, hmn⟩, rfl⟩
        apply hS _ (Finset.mem_union_left _ hmem)
        simp only [map_add, map_mul, map_pow, aeval_X, map_intCast]
        exact h0
      · intro a ha Y h0
        have hmem : RatFunc.denom (normP hH a.1 a.2 Y) ∈ denomPolys hH N := by
          simp only [denomPolys, Finset.mem_biUnion, Finset.mem_image]
          exact ⟨a, ha, Y, Finset.mem_univ _, rfl⟩
        apply hS _ (Finset.mem_union_right _ hmem)
        rw [Polynomial.aeval_def]
        exact h0
    exact hgen.recursion hK hN1 d

end Virasoro
