import Virasoro.Proofs.TorusDegree
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.EtaPartition
import Virasoro.Proofs.PBWIndep
import Virasoro.Proofs.Levels

/-!
# The torus matrix at `d = 0`

At `d = 0` the Ward recursion for `⟨Δ|L_Y V_d(1) L_{-w}|Δ⟩` is the recursion of the Shapovalov
form: `ρ_M(c,Δ,0) = G_M(c,Δ)`.  Hence `F_M(c,Δ,0) = p(M)` and `H_N(c,Δ,0) = 0` for `N ≥ 1` at every
point where the Shapovalov determinants of level at most `N` do not vanish (the value at `d = 0`
of paper Lemma 6.5, used at `(c⋆, μ)` in the proofs of Corollary 5.10 and Proposition 6.7).
-/

namespace Virasoro

section Words

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem phi_zero : ∀ w : List ℕ, phi (0 : R) w = if w = [] then 1 else 0
  | [] => by simp [phi]
  | m :: w => by
    rw [phi, phi_zero w]
    by_cases hw : w = []
    · subst hw
      simp
    · simp [hw]

theorem gramWord_nil (c h : R) (w : List ℕ) : gramWord c h [] w = if w = [] then 1 else 0 := by
  cases w <;> simp [gramWord, vac]

/-- At `d = 0` the torus entry is the Shapovalov entry on words of equal level and `0`
otherwise. -/
theorem torusWord_zero (c h : R) : ∀ Y : List ℕ, PosWord Y → ∀ w : List ℕ, PosWord w →
    torusWord c h 0 Y w = if Y.sum = w.sum then gramWord c h Y w else 0
  | [], _, w => by
    intro hw
    rw [torusWord, phi_zero, gramWord_nil]
    by_cases hw0 : w = []
    · subst hw0
      simp
    · have : ¬ ([] : List ℕ).sum = w.sum := by
        cases w with
        | nil => exact absurd rfl hw0
        | cons a w =>
          have ha : 0 < a := hw a List.mem_cons_self
          simp only [List.sum_nil, List.sum_cons]
          omega
      simp [hw0, this]
  | y :: Y, hY, w => by
    intro hw
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    have hfirst : ((actWord c h (y : ℤ) w).map fun t => t.2 * torusWord c h 0 Y t.1).sum =
        if (y :: Y).sum = w.sum then gramWord c h (y :: Y) w else 0 := by
      by_cases hs : (y :: Y).sum = w.sum
      · rw [if_pos hs, gramWord_cons _ _ y Y w hw]
        congr 1
        refine List.map_congr_left fun t ht => ?_
        have hsum := actWord_sum c h w (y : ℤ) t ht
        have hpos := posSt_actWord c h hw (y : ℤ) t ht
        rw [torusWord_zero c h Y hY' t.1 hpos, if_pos]
        rw [List.sum_cons] at hs
        omega
      · rw [if_neg hs]
        refine List.sum_eq_zero fun x hx => ?_
        rw [List.mem_map] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        have hsum := actWord_sum c h w (y : ℤ) t ht
        have hpos := posSt_actWord c h hw (y : ℤ) t ht
        rw [torusWord_zero c h Y hY' t.1 hpos, if_neg, mul_zero]
        rw [List.sum_cons] at hs
        omega
    rw [torusWord, hfirst, torusWord_zero c h Y hY' w hw]
    by_cases hs : Y.sum = w.sum
    · rw [if_pos hs, hs]
      simp
    · rw [if_neg hs]
      simp

theorem torus_zero (c h : R) (M : ℕ) : torus c h 0 M = gram c h M := by
  ext Y Y'
  simp only [torus, gram, Matrix.of_apply]
  rw [torusWord_zero c h _ (Verma.posWord_word Y) _ (Verma.posWord_word Y'), if_pos]
  rw [Verma.word_sum', Verma.word_sum']

theorem gram_transpose (c h : R) (M : ℕ) : (gram c h M).transpose = gram c h M := by
  ext Y Y'
  simp only [gram, Matrix.transpose_apply, Matrix.of_apply]
  exact gramWord_symm c h (Verma.posWord_word Y') (Verma.posWord_word Y)

end Words

section Values

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `F_M(c,z,0) = p(M)` where `det G_M(c,z) ≠ 0`. -/
theorem Fval_zero_d {c z : 𝔽} {M : ℕ} (h : (gram c z M).det ≠ 0) :
    Fval c 0 z M = (Fintype.card (Nat.Partition M) : 𝔽) := by
  unfold Fval
  rw [torus_zero]
  have h1 : ∀ Y : Nat.Partition M,
      ∑ Y', (gram c z M).adjugate Y Y' * gram c z M Y Y' = (gram c z M).det := by
    intro Y
    have h2 := congrFun (congrFun (Matrix.adjugate_mul (gram c z M)) Y) Y
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [← gram_transpose c z M, Matrix.transpose_apply, gram_transpose]
  rw [Finset.sum_congr rfl fun Y _ => h1 Y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_assoc, div_self h, mul_one]

/-- `H_N(c,z,0) = 0` for `N ≥ 1` where no Shapovalov determinant of level at most `N`
vanishes. -/
theorem Hval_zero_d {c z : 𝔽} {N : ℕ} (hN : 1 ≤ N) (h : ∀ M ≤ N, (gram c z M).det ≠ 0) :
    Hval c 0 z N = 0 := by
  unfold Hval
  rw [Finset.sum_congr rfl fun j _ => by rw [Fval_zero_d (h _ (Nat.sub_le N j))]]
  have h1 := congrArg (Int.cast : ℤ → 𝔽) (eta_partition N)
  rw [if_neg (by omega)] at h1
  push_cast at h1
  exact h1

end Values

end Virasoro
