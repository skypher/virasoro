import Virasoro.Proofs.Sec6H13TPart

/-!
# Proposition 6.8(ii): one step of the chain, `1 − G̃D₀⁻¹` (paper.tex l.1313–1332)

For admissible `μ', μ` (`w' = |μ'|`, `w = |μ|`), the entry of `1 − G̃D₀⁻¹` at
`((1^{M−w'}, μ'), (1^{M−w}, μ))` is `δ − ∑_p C(M−w', p) · stepT`; it is good from the level `w'`
on, with valuation `max(0, w − w')`: the binomial `C(M−w',p)` vanishes on `[w', w'+p)` and the
`p`-term is nonzero only when `w ≤ w' + p` (l.1366–1378).
-/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Finset

/-- A family that agrees coefficientwise from the level `W` on with good families. -/
theorem GF.of_cf_eq {G : ℕ → LL} {W : ℕ} {D V : ℤ}
    (hord : ∃ b : ℤ, ∀ M : ℕ, W ≤ M → ∀ n < b, (G M).coeff n = 0)
    (h : ∀ i j : ℤ, ∃ H : ℕ → LL, GF H W D V ∧ ∀ M : ℕ, W ≤ M → cfL (G M) i j = cfL (H M) i j) :
    GF G W D V := by
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ?_⟩
  · obtain ⟨H, hH, hHe⟩ := h i j
    exact (hH.poly i j).congr fun M => hHe (M + W) (by omega)
  · obtain ⟨H, hH, hHe⟩ := h i j
    rw [hHe (M + W) (by omega)]
    exact hH.val M i j hij
  · obtain ⟨b, hb⟩ := hord
    exact ⟨b, fun M n hn => hb (M + W) (by omega) n hn⟩

theorem jL_cQ (q : ℚ) : jL (cQ q) = cL q := by
  rw [jL, cQ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C]
  rfl

theorem jL_Yp (k : ℤ) : jL (Yp k) = mono 0 k 1 := by
  rw [jL, Yp, HahnSeries.ofPowerSeries_C, mono, map_one, one_mul]
  rfl

theorem jL_coeff_neg (F : LS) (n : ℤ) (hn : n < 0) : (jL F).coeff n = 0 := by
  rw [jL, HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  have h2 : ((m : ℕ) : ℤ) = n := hm
  omega

theorem Good.neg {G : ℕ → LL} {D V : ℤ} (h : Good G D V) : Good (fun M => -G M) D V := by
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ?_⟩
  · obtain ⟨f, h1, h2⟩ := h.poly i j
    exact ⟨-f, fun n hn => by rw [Polynomial.coeff_neg, h1 n hn, neg_zero], fun M => by
      beta_reduce
      rw [Polynomial.eval_neg, ← h2 M]
      simp [cfL]⟩
  · rw [cfL, HahnSeries.coeff_neg]
    have := h.val M i j hij
    rw [cfL] at this
    simp [this]
  · obtain ⟨b, hb⟩ := h.ord
    exact ⟨b, fun M n hn => by rw [HahnSeries.coeff_neg, hb M n hn, neg_zero]⟩

theorem GF.neg {G : ℕ → LL} {W : ℕ} {D V : ℤ} (h : GF G W D V) : GF (fun M => -G M) W D V :=
  Good.neg h

/-! ### The entries of `1 − G̃D₀⁻¹` -/

theorem jL_Em (M : ℕ) (Y Y' : Nat.Partition M) :
    jL (Em M Y Y') = (if Y = Y' then 1 else 0) -
      fL (gramT tS cS Polynomial.X Y.word Y'.word) *
        (cL (1 / (topNat Y'.word Y'.word : ℚ)) * mono 0 (-(Y'.word.length : ℤ)) 1) := by
  rw [Em, D0i, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.one_apply, map_sub, map_mul, map_mul,
    jL_cQ, jL_Yp]
  congr 1
  split_ifs <;> simp

/-- The step entry along the levels (zero when a partition does not exist). -/
noncomputable def Ehat (μ' μ : List ℕ) (M : ℕ) : LL := by
  classical
  exact if μ'.sum ≤ M ∧ μ.sum ≤ M then jL (Em M (lamOf μ' M) (lamOf μ M)) else 0

theorem lamOf_inj {μ' μ : List ℕ} (h' : Adm μ') (h : Adm μ) {M : ℕ} (hM' : μ'.sum ≤ M)
    (hM : μ.sum ≤ M) : lamOf μ' M = lamOf μ M ↔ μ' = μ := by
  constructor
  · intro he
    rw [← big_lamOf h' hM', ← big_lamOf h hM, he]
  · rintro rfl
    rfl

theorem Ehat_eq {μ' μ : List ℕ} (h' : Adm μ') (h : Adm μ) {M : ℕ} (hM' : μ'.sum ≤ M)
    (hM : μ.sum ≤ M) :
    Ehat μ' μ M = (if μ' = μ then 1 else 0) - ∑ p ∈ range (M - μ'.sum + 1),
      cL ((M - μ'.sum).choose p : ℚ) * stepT μ' μ (M - μ'.sum) (M - μ.sum) p := by
  classical
  rw [Ehat, if_pos ⟨hM', hM⟩, jL_Em, lamOf_word h' hM', lamOf_word h hM, ← gram_step μ' μ h'.2 h.2]
  congr 1
  · rw [if_congr (lamOf_inj h' h hM' hM) rfl rfl]
  · rw [List.length_append, List.length_replicate, mul_assoc]

/-! ### The binomial as a polynomial in the level -/

/-- `C(M − w', p)` as a polynomial in `M`. -/
noncomputable def binP (w' p : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / (p.factorial : ℚ)) *
    (descPochhammer ℚ p).comp (Polynomial.X - Polynomial.C (w' : ℚ))

theorem binP_eval {w' p M : ℕ} (hM : w' ≤ M) :
    (binP w' p).eval (M : ℚ) = ((M - w').choose p : ℚ) := by
  rw [binP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, ← Nat.cast_sub hM, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have : (p.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem binP_natDegree (w' p : ℕ) : (binP w' p).natDegree ≤ p := by
  rw [binP]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_comp_le.trans ?_
  rw [descPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one]

theorem binP_zero {w' p M : ℕ} (h1 : w' ≤ M) (h2 : M < w' + p) : (binP w' p).eval (M : ℚ) = 0 := by
  rw [binP_eval h1, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-! ### The step is good from `w'` on -/

/-- The `p`-term of the step, zero unless `w ≤ w' + p`. -/
noncomputable def stepS (μ' μ : List ℕ) (p M : ℕ) : LL :=
  if μ.sum ≤ μ'.sum + p then stepT μ' μ (M - μ'.sum) (M - μ.sum) p else 0

theorem good_stepS (μ' μ : List ℕ) (hμ : ∀ y ∈ μ, 2 ≤ y) (p : ℕ) :
    GF (stepS μ' μ p) (μ'.sum + p) p p := by
  by_cases hle : μ.sum ≤ μ'.sum + p
  · have h := good_stepT μ' μ hμ p (μ'.sum + p - μ.sum)
    have e : (fun M => stepS μ' μ p (M + (μ'.sum + p))) =
        fun M => stepT μ' μ (M + p) (M + (μ'.sum + p - μ.sum)) p := by
      funext M
      rw [stepS, if_pos hle]
      congr 1 <;> omega
    show Good (fun M => stepS μ' μ p (M + (μ'.sum + p))) p p
    rw [e]
    exact h
  · have e : (fun M => stepS μ' μ p (M + (μ'.sum + p))) = fun _ => 0 := by
      funext M
      rw [stepS, if_neg hle]
    show Good (fun M => stepS μ' μ p (M + (μ'.sum + p))) p p
    rw [e]
    exact good_zero p p

/-- The step family: `δ − ∑_{p ≤ P} C(M−w',p) stepS`. -/
noncomputable def stepH (μ' μ : List ℕ) (P : ℕ) (M : ℕ) : LL := by
  classical
  exact (if μ' = μ then 1 else 0) -
    ∑ p ∈ range (P + 1), cL ((binP μ'.sum p).eval (M : ℚ)) * stepS μ' μ p M

theorem good_stepH (μ' μ : List ℕ) (hμ : ∀ y ∈ μ, 2 ≤ y) (P : ℕ) :
    GF (stepH μ' μ P) μ'.sum 0 (max 0 ((μ.sum : ℤ) - μ'.sum)) := by
  classical
  unfold stepH
  have hδ : GF (fun _ => if μ' = μ then (1 : LL) else 0) μ'.sum 0 (max 0 ((μ.sum : ℤ) - μ'.sum)) := by
    split_ifs with he
    · subst he
      simpa [GF] using good_one
    · simpa [GF] using good_zero 0 (max 0 ((μ.sum : ℤ) - μ'.sum))
  have hsum : GF (fun M : ℕ => ∑ p ∈ range (P + 1), cL ((binP μ'.sum p).eval (M : ℚ)) *
      stepS μ' μ p M)
      μ'.sum 0 (max 0 ((μ.sum : ℤ) - μ'.sum)) := by
    refine GF.sum _ fun p _ => ?_
    by_cases hle : μ.sum ≤ μ'.sum + p
    · have h := GF.pi_mul (binP μ'.sum p) (binP_natDegree μ'.sum p) (W₀ := μ'.sum)
        (W := μ'.sum + p) (by omega) (fun M h1 h2 => binP_zero h1 h2) (good_stepS μ' μ hμ p)
      refine h.mono (by simp) (by omega)
    · have e : (fun M : ℕ => cL ((binP μ'.sum p).eval (M : ℚ)) * stepS μ' μ p M) = fun _ => 0 := by
        funext M
        rw [stepS, if_neg hle, mul_zero]
      rw [e]
      simpa [GF] using good_zero 0 (max 0 ((μ.sum : ℤ) - μ'.sum))
  have := hδ.add ((GF.neg hsum))
  simpa [sub_eq_add_neg] using this

theorem cfL_neg_eq (F : LL) (i j : ℤ) : cfL (-F) i j = -cfL F i j := by
  simp [cfL]

theorem stepT_zero {μ' μ : List ℕ} {M p : ℕ} (hM : μ.sum ≤ M) (hlt : μ'.sum + p < μ.sum) :
    stepT μ' μ (M - μ'.sum) (M - μ.sum) p = 0 := by
  rw [stepT, if_neg (by omega)]

theorem stepT_val {μ' μ : List ℕ} (hμ : ∀ y ∈ μ, 2 ≤ y) {M p : ℕ} (hM : μ'.sum + p ≤ M)
    (hle : μ.sum ≤ μ'.sum + p) (i j : ℤ) (hij : 2 * i + 2 * j < p) :
    cfL (stepT μ' μ (M - μ'.sum) (M - μ.sum) p) i j = 0 := by
  have h := (good_stepT μ' μ hμ p (μ'.sum + p - μ.sum)).val (M - (μ'.sum + p)) i j (by omega)
  have e1 : M - (μ'.sum + p) + p = M - μ'.sum := by omega
  have e2 : M - (μ'.sum + p) + (μ'.sum + p - μ.sum) = M - μ.sum := by omega
  rw [e1, e2] at h
  exact h

/-- The step entry is good from the level `w'` on, with valuation `max(0, w − w')`
(paper.tex l.1366–1378). -/
theorem good_Ehat {μ' μ : List ℕ} (h' : Adm μ') (h : Adm μ) :
    GF (Ehat μ' μ) μ'.sum 0 (max 0 ((μ.sum : ℤ) - μ'.sum)) := by
  classical
  refine GF.of_cf_eq ⟨0, fun M _ n hn => ?_⟩ fun i j => ⟨stepH μ' μ (2 * i + 2 * j).toNat,
    good_stepH μ' μ h.2 _, fun M hM => ?_⟩
  · unfold Ehat
    split_ifs
    · exact jL_coeff_neg _ n hn
    · rfl
  · set P := (2 * i + 2 * j).toNat with hP
    by_cases hw : μ.sum ≤ M
    · rw [Ehat_eq h' h hM hw, stepH, sub_eq_add_neg, sub_eq_add_neg, cfL_add, cfL_add,
        cfL_neg_eq, cfL_neg_eq, cfL_sum, cfL_sum]
      congr 2
      have key : ∀ p, cfL (cL ((M - μ'.sum).choose p : ℚ) *
          stepT μ' μ (M - μ'.sum) (M - μ.sum) p) i j =
          cfL (cL ((binP μ'.sum p).eval (M : ℚ)) * stepS μ' μ p M) i j := by
        intro p
        by_cases hp : p ≤ M - μ'.sum
        · rw [binP_eval hM, stepS]
          split_ifs with hle
          · rfl
          · rw [stepT_zero hw (by omega)]
        · rw [binP_zero hM (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, map_zero,
            zero_mul, zero_mul]
      have hz1 : ∀ p ∈ range (M - μ'.sum + 1) ∪ range (P + 1), p ∉ range (M - μ'.sum + 1) →
          cfL (cL ((M - μ'.sum).choose p : ℚ) * stepT μ' μ (M - μ'.sum) (M - μ.sum) p) i j = 0 := by
        intro p _ hp'
        have : M - μ'.sum < p := by simpa using hp'
        rw [Nat.choose_eq_zero_of_lt this, Nat.cast_zero, map_zero, zero_mul, cfL_zero]
      have hz2 : ∀ p ∈ range (M - μ'.sum + 1) ∪ range (P + 1), p ∉ range (P + 1) →
          cfL (cL ((binP μ'.sum p).eval (M : ℚ)) * stepS μ' μ p M) i j = 0 := by
        intro p hp hp'
        have hpP : P < p := by simpa using hp'
        rcases mem_union.1 hp with hp | hp
        · have hpM : p ≤ M - μ'.sum := Nat.lt_succ_iff.1 (mem_range.1 hp)
          rw [← key p, cfL_cL_mul]
          by_cases hle : μ.sum ≤ μ'.sum + p
          · rw [stepT_val h.2 (by omega) hle i j (by omega), mul_zero]
          · rw [stepT_zero hw (by omega), cfL_zero, mul_zero]
        · exact absurd hp hp'
      rw [sum_subset subset_union_left hz1, sum_subset subset_union_right hz2]
      exact sum_congr rfl fun p _ => key p
    · have hne : μ' ≠ μ := fun he => by rw [he] at hM; omega
      rw [Ehat, if_neg (by omega), stepH, if_neg hne, zero_sub, cfL_neg_eq, cfL_sum, cfL_zero]
      refine (neg_eq_zero.2 (sum_eq_zero fun p _ => ?_)).symm
      by_cases hp : p ≤ M - μ'.sum
      · rw [stepS, if_neg (by omega), mul_zero, cfL_zero]
      · rw [binP_zero hM (by omega), map_zero, zero_mul, cfL_zero]

end Virasoro.H13T
