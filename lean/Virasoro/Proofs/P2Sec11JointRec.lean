import Virasoro.Proofs.Sec6H13Poles
import Virasoro.Proofs.EtaPartition
import Virasoro.Proofs.P2Sec9Main

/-!
# Lemma 11.3 (joint regularity), proof, second paragraph (paper.tex l.2521–2540)

At `d(b) = h_{2k+1,ε(2m+1)}(b)` the multiplier `ℛ_{R,S}(b,d(b))` vanishes identically in `b` when
`R ≥ k+1` and `S ≥ m+1`, so by the generic recursion the inactive Kac factors cancel from the
denominator of `H_M(c(b),Δ,d(b))` and therefore from `F_N = ∑_j p(j) H_{N-j}`: the product of
`F_N` with `∏_{(R,S) ∈ 𝒦_N} (Δ - h_{R,S}(b))` is a polynomial in `Δ`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- The active labels `𝒦_N = {(R,S) : RS ≤ N, R ≤ k or S ≤ m}` (paper.tex l.2536). -/
def activeLabels (k m N : ℕ) : Finset Label := (labels N).filter fun a => a.1 ≤ k ∨ a.2 ≤ m

theorem activeLabels_mono (k m : ℕ) {M N : ℕ} (h : M ≤ N) :
    activeLabels k m M ⊆ activeLabels k m N := by
  intro a ha
  rw [activeLabels, Finset.mem_filter] at ha ⊢
  obtain ⟨h1, h2, h3⟩ := label_pos ha.1
  refine ⟨mem_labels.2 ?_, ha.2⟩
  have := mem_labels.1 ha.1
  omega

/-- `𝒫_{R,S}(b,d)` vanishes at `d = h_{2k+1,±(2m+1)}(b)` when `k < R` and `m < S`
(paper.tex l.2527–2531). -/
theorem genP_inactive {R S k m : ℕ} (hk : k < R) (hm : m < S) (ε : Bool) (b : 𝔽) :
    genP R S b (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) b) = 0 := by
  unfold genP
  refine Finset.prod_eq_zero (i := 2 * k + 1) (mem_oddsBelow.2 ⟨by omega, by omega⟩) ?_
  refine Finset.prod_eq_zero (i := 2 * m + 1) (mem_oddsBelow.2 ⟨by omega, by omega⟩) ?_
  cases ε
  · refine mul_eq_zero_of_right _ ?_
    simp only [lamSq, kacH, sgnInt, Bool.false_eq_true, if_false]
    push_cast
    ring
  · refine mul_eq_zero_of_left ?_ _
    simp only [lamSq, kacH, sgnInt, if_true]
    push_cast
    ring

/-- `F_N = ∑_{j=0}^N p(j) H_{N-j}` (paper.tex l.2534). -/
theorem Frat_eq_sum_Hrat (c d : 𝔽) (N : ℕ) :
    Frat c d N = ∑ j ∈ Finset.range (N + 1),
      (Fintype.card (Nat.Partition j) : RatFunc 𝔽) * Hrat c d (N - j) := by
  have h1 : ∀ j ∈ Finset.range (N + 1),
      (Fintype.card (Nat.Partition j) : RatFunc 𝔽) * Hrat c d (N - j) =
        ∑ n ∈ Finset.Ico j (N + 1), (Fintype.card (Nat.Partition j) : RatFunc 𝔽) *
          ((eta (n - j) : RatFunc 𝔽) * Frat c d (N - n)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Hrat, Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
      show N + 1 - j = N - j + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show j + i - j = i by omega, show N - (j + i) = N - j - i by omega]
  rw [Finset.sum_congr rfl h1,
    Finset.sum_comm' (s' := fun n => Finset.range (n + 1)) (t' := Finset.range (N + 1))
      (by intro j n; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have h2 : ∀ n ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range (n + 1), (Fintype.card (Nat.Partition j) : RatFunc 𝔽) *
          ((eta (n - j) : RatFunc 𝔽) * Frat c d (N - n)) =
        ((if n = 0 then 1 else 0 : ℤ) : RatFunc 𝔽) * Frat c d (N - n) := by
    intro n _
    rw [← eta_partition n, ← Finset.sum_range_reflect, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
    push_cast
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    simp [hn]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

/-- The inactive Kac factors cancel from the denominator of `H_M(c(b),Δ,d(b))`
(paper.tex l.2531–2534). -/
theorem Hrat_active_poly {b : 𝔽} (k m : ℕ) (ε : Bool) {M : ℕ}
    (hrec : 1 ≤ M → GenericRecursionAt 𝔽 b
      (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) b) M) :
    ∃ Q : 𝔽[X], Hrat (kacC b) (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) b) M *
        algebraMap 𝔽[X] (RatFunc 𝔽) (∏ a ∈ activeLabels k m M, (X - C (kacHL a b))) =
      algebraMap 𝔽[X] (RatFunc 𝔽) Q := by
  classical
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨_, by rw [Hrat_zero, one_mul]⟩
  set d : 𝔽 := kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) b with hd
  let cf : Label → 𝔽 := fun a => genR a.1 a.2 b d *
    RatFunc.eval (RingHom.id 𝔽) (kacHL a b + (a.lvl : 𝔽)) (Hrat (kacC b) d (M - a.lvl))
  refine ⟨∑ a ∈ activeLabels k m M,
      C (cf a) * ∏ a' ∈ (activeLabels k m M).erase a, (X - C (kacHL a' b)), ?_⟩
  rw [hrec hM, Finset.sum_mul, map_sum, activeLabels, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨h1, h2, h3⟩ := label_pos ha
  split_ifs with hact
  · have hmem : a ∈ (labels M).filter fun a => a.1 ≤ k ∨ a.2 ≤ m :=
      Finset.mem_filter.2 ⟨ha, hact⟩
    have hne : (RatFunc.X : RatFunc 𝔽) - RatFunc.C (kacHL a b) ≠ 0 := by
      intro h0
      have h4 : algebraMap 𝔽[X] (RatFunc 𝔽) (X - C (kacHL a b)) = 0 := by
        rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
        exact h0
      exact X_sub_C_ne_zero _ ((map_eq_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).1 h4)
    rw [← Finset.mul_prod_erase _ _ hmem, map_mul, map_mul, map_sub, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, RatFunc.algebraMap_C]
    show _ = RatFunc.C (genR a.1 a.2 b d * RatFunc.eval (RingHom.id 𝔽)
      (kacHL a b + (a.lvl : 𝔽)) (Hrat (kacC b) d (M - a.lvl))) * _
    rw [map_mul]
    field_simp
  · have hz : genR a.1 a.2 b d = 0 := by
      rw [genR, hd, genP_inactive (by omega) (by omega), mul_zero]
    rw [hz, map_zero, zero_div, zero_mul, zero_mul]

/-- A nonzero polynomial over `ℚ` does not vanish at the indeterminate `b` of `ℂ(b)`. -/
theorem aeval_ratFuncX_ne_zero {P : ℚ[X]} (hP : P ≠ 0) :
    aeval (RatFunc.X : RatFunc ℂ) P ≠ 0 := by
  have h1 : aeval (RatFunc.X : RatFunc ℂ) P =
      algebraMap ℂ[X] (RatFunc ℂ) (P.map (algebraMap ℚ ℂ)) := by
    rw [aeval_def, ← RatFunc.algebraMap_X, Polynomial.map, hom_eval₂]
    congr 1
    · exact RingHom.ext fun q => by simp
  rw [h1]
  intro h0
  have h2 := (map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).1 h0
  exact hP (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [h2, Polynomial.map_zero]))

/-- Over `ℂ(b)`, the product of `F_N(c(b),Δ,d(b))` with the active Kac factors is a polynomial
in `Δ` (paper.tex l.2531–2536). -/
theorem Frat_active_poly (hrec : GenericRecursionUniform) (k m : ℕ) (ε : Bool) (N : ℕ) :
    ∃ Q : (RatFunc ℂ)[X],
      Frat (kacC (RatFunc.X : RatFunc ℂ))
          (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) (RatFunc.X : RatFunc ℂ)) N *
        algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ))
          (∏ a ∈ activeLabels k m N, (X - C (kacHL a (RatFunc.X : RatFunc ℂ)))) =
      algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ)) Q := by
  classical
  have hH : ∀ M : ℕ, ∃ Q : (RatFunc ℂ)[X],
      Hrat (kacC (RatFunc.X : RatFunc ℂ))
          (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) (RatFunc.X : RatFunc ℂ)) M *
        algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ))
          (∏ a ∈ activeLabels k m M, (X - C (kacHL a (RatFunc.X : RatFunc ℂ)))) =
      algebraMap (RatFunc ℂ)[X] (RatFunc (RatFunc ℂ)) Q := by
    intro M
    refine Hrat_active_poly k m ε fun hM => ?_
    obtain ⟨S, hS0, hS⟩ := hrec M hM
    exact hS (RatFunc ℂ) RatFunc.X _ RatFunc.X_ne_zero
      fun P hP => aeval_ratFuncX_ne_zero (hS0 P hP)
  choose Q hQ using hH
  refine ⟨∑ j ∈ Finset.range (N + 1), C (Fintype.card (Nat.Partition j) : RatFunc ℂ) *
    (Q (N - j) * ∏ a ∈ activeLabels k m N \ activeLabels k m (N - j),
      (X - C (kacHL a (RatFunc.X : RatFunc ℂ)))), ?_⟩
  rw [Frat_eq_sum_Hrat, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_sdiff (activeLabels_mono k m (Nat.sub_le N j)), map_mul, map_mul, map_mul,
    ← hQ (N - j)]
  simp only [map_natCast]
  ring

end Virasoro
