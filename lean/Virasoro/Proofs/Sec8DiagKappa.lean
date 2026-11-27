import Virasoro.Proofs.Sec8DiagRec

/-!
# Theorem 8.8, second part: the sums of `κ̂` over the two nodes of a layer

For `θ_± = (±, L)` at odd distance from `a` and `L < L_μ`: the numerator of `κ̂(a,θ,μ)` is the
product over `FS(θ→μ)`, pairs `±m/2` over the layers `m` at odd distance from `L` (contributing
`π_a² - m²/4`) and `μ` when `L_μ - L` is odd; the denominator is the product over
`FS(a→μ) ∖ FS(a→θ)`: the other node of layer `L` (contributing `-2π_θ`), pairs over the layers at
even distance from `L` (contributing `L²/4 - m²/4`), and `μ` when `L_μ - L_a` is odd.
-/

namespace Virasoro

/-- The layers in `(L, U)` at odd distance from `L`. -/
def TA (L U : ℕ) : Finset ℕ := (Finset.Ioo L U).filter (fun m => (m - L) % 2 = 1)

/-- The layers in `(L, U)` at even distance from `L`. -/
def TB (L U : ℕ) : Finset ℕ := (Finset.Ioo L U).filter (fun m => (m - L) % 2 = 0)

theorem prod_univ_product (T : Finset ℕ) (f : Node → ℚ) :
    ∏ x ∈ (Finset.univ : Finset Bool) ×ˢ T, f x = ∏ m ∈ T, (f (true, m) * f (false, m)) := by
  rw [Finset.prod_product, Fintype.prod_bool, Finset.prod_mul_distrib]

theorem pos_true (m : ℕ) : nodePos (true, m) = (m : ℚ) / 2 := by simp [nodePos]

theorem pos_false (m : ℕ) : nodePos (false, m) = -((m : ℚ) / 2) := by simp [nodePos]

theorem pos_sq (x : Node) : nodePos x ^ 2 = (x.2 : ℚ) ^ 2 / 4 := by
  unfold nodePos; split_ifs <;> ring

theorem pair_prod (m : ℕ) (c : ℚ) :
    (nodePos (true, m) - c) * (nodePos (false, m) - c) = c ^ 2 - (m : ℚ) ^ 2 / 4 := by
  rw [pos_true, pos_false]; ring

/-- The numerator of `κ̂(a,θ,μ)`. -/
theorem kappa_num (a θ μ : Node) :
    ∏ x ∈ firstSteps θ μ, (nodePos x - nodePos a) =
      (∏ m ∈ TA θ.2 μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) *
        (if (μ.2 - θ.2) % 2 = 1 then nodePos μ - nodePos a else 1) := by
  unfold firstSteps
  rw [Finset.prod_union]
  · rw [prod_univ_product]
    congr 1
    · exact Finset.prod_congr rfl fun m _ => pair_prod m _
    · split_ifs <;> simp
  · rw [Finset.disjoint_left]
    intro x hx hx2
    split_ifs at hx2
    · rw [Finset.mem_singleton.1 hx2] at hx
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_Ioo] at hx
      omega
    · simp at hx2

theorem fs_diff {a μ : Node} {ε : Bool} {L : ℕ} (h1 : a.2 < L) (h2 : L < μ.2)
    (hodd : (L - a.2) % 2 = 1) :
    firstSteps a μ \ firstSteps a (ε, L) =
      ({(!ε, L)} ∪ (Finset.univ : Finset Bool) ×ˢ TB L μ.2) ∪
        (if (μ.2 - a.2) % 2 = 1 then {μ} else ∅) := by
  obtain ⟨εμ, U⟩ := μ
  simp only at h2 ⊢
  ext ⟨ε', m⟩
  rw [Finset.mem_sdiff, mem_firstSteps, mem_firstSteps]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_product, Finset.mem_univ,
    true_and, TB, Finset.mem_filter, Finset.mem_Ioo, Prod.mk.injEq]
  split_ifs with ho
  · simp only [Finset.mem_singleton, Prod.mk.injEq]
    cases ε <;> cases ε' <;> cases εμ <;>
      simp only [Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, true_and,
        and_true, false_and, and_false, or_false, false_or, not_or, not_and] <;> omega
  · simp only [Finset.notMem_empty, or_false]
    cases ε <;> cases ε' <;> cases εμ <;>
      simp only [Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, true_and,
        and_true, false_and, and_false, or_false, false_or, not_or, not_and] <;> omega

/-- The denominator of `κ̂(a,θ,μ)`. -/
theorem kappa_den {a μ : Node} {ε : Bool} {L : ℕ} (h1 : a.2 < L) (h2 : L < μ.2)
    (hodd : (L - a.2) % 2 = 1) :
    ∏ x ∈ firstSteps a μ \ firstSteps a (ε, L), (nodePos x - nodePos (ε, L)) =
      (nodePos (!ε, L) - nodePos (ε, L)) *
        (∏ m ∈ TB L μ.2, ((L : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4)) *
          (if (μ.2 - a.2) % 2 = 1 then nodePos μ - nodePos (ε, L) else 1) := by
  have hd1 : Disjoint ({(!ε, L)} : Finset Node) ((Finset.univ : Finset Bool) ×ˢ TB L μ.2) := by
    rw [Finset.disjoint_singleton_left]
    simp [TB, Finset.mem_product]
  have hd2 : Disjoint ({(!ε, L)} ∪ (Finset.univ : Finset Bool) ×ˢ TB L μ.2)
      (if (μ.2 - a.2) % 2 = 1 then {μ} else ∅) := by
    split_ifs
    · rw [Finset.disjoint_singleton_right, Finset.mem_union, Finset.mem_singleton]
      rintro (h | h)
      · rw [h] at h2; simp at h2
      · simp only [TB, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter,
          Finset.mem_Ioo] at h
        omega
    · exact Finset.disjoint_empty_right _
  rw [fs_diff h1 h2 hodd, Finset.prod_union hd2, Finset.prod_union hd1, Finset.prod_singleton,
    prod_univ_product]
  congr 1
  · congr 1
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [pair_prod, pos_sq]
  · split_ifs <;> simp

theorem TB_prod_ne {L U : ℕ} : ∏ m ∈ TB L U, ((L : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun m hm e => ?_
  simp only [TB, Finset.mem_filter, Finset.mem_Ioo] at hm
  have h1 : (L : ℚ) < m := by exact_mod_cast hm.1.1
  have h0 : (0 : ℚ) ≤ L := by positivity
  nlinarith

theorem ksum_odd_alg (N Q P L : ℚ) (hQ : Q ≠ 0) (hL : L ≠ 0) (h1 : P - L / 2 ≠ 0)
    (h2 : P - -(L / 2) ≠ 0) :
    N / ((-(L / 2) - L / 2) * Q * (P - L / 2)) + N / ((L / 2 - -(L / 2)) * Q * (P - -(L / 2))) =
      -N / (Q * (P ^ 2 - L ^ 2 / 4)) := by
  have e1 : -(L / 2) - L / 2 = -L := by ring
  have e2 : L / 2 - -(L / 2) = L := by ring
  have e3 : P ^ 2 - L ^ 2 / 4 = (P - L / 2) * (P - -(L / 2)) := by ring
  have d1 : (-(L / 2) - L / 2) * Q * (P - L / 2) ≠ 0 := by
    rw [e1]; exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hL) hQ) h1
  have d2 : (L / 2 - -(L / 2)) * Q * (P - -(L / 2)) ≠ 0 := by
    rw [e2]; exact mul_ne_zero (mul_ne_zero hL hQ) h2
  have d3 : Q * (P ^ 2 - L ^ 2 / 4) ≠ 0 := by
    rw [e3]; exact mul_ne_zero hQ (mul_ne_zero h1 h2)
  rw [div_add_div _ _ d1 d2, div_eq_div_iff (mul_ne_zero d1 d2) d3]
  ring

/-- `D(a,μ)` odd, `D(θ,μ)` even: `∑_± κ̂(a,θ_±,μ) = -N/(Q (π_μ² - L²/4))`. -/
theorem kappa_sum_odd {a μ : Node} {L : ℕ} (h1 : a.2 < L) (h2 : L < μ.2) (hodd : (L - a.2) % 2 = 1)
    (hD : (μ.2 - a.2) % 2 = 1) :
    ∑ ε : Bool, kappaHat a (ε, L) μ =
      -(∏ m ∈ TA L μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) /
        ((∏ m ∈ TB L μ.2, ((L : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4)) *
          (nodePos μ ^ 2 - (L : ℚ) ^ 2 / 4)) := by
  have hj : (μ.2 - L) % 2 = 0 := by omega
  have hQ := TB_prod_ne (L := L) (U := μ.2)
  have hL : (L : ℚ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hμ1 : nodePos μ - (L : ℚ) / 2 ≠ 0 := by
    have := nodePos_ne (x := μ) (y := (true, L)) h2; rw [pos_true] at this
    exact sub_ne_zero.2 this
  have hμ2 : nodePos μ - -((L : ℚ) / 2) ≠ 0 := by
    have := nodePos_ne (x := μ) (y := (false, L)) h2; rw [pos_false] at this
    exact sub_ne_zero.2 this
  unfold kappaHat
  rw [Fintype.sum_bool, kappa_num, kappa_num, kappa_den h1 h2 hodd, kappa_den h1 h2 hodd,
    if_neg (show ¬ (μ.2 - (true, L).2) % 2 = 1 by simp only; omega), if_pos hD, if_pos hD]
  simp only [mul_one, Bool.not_true, Bool.not_false, pos_true, pos_false]
  generalize (∏ m ∈ TA L μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) = N
  generalize (∏ m ∈ TB L μ.2, ((L : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4)) = Q at hQ ⊢
  generalize nodePos μ = P at hμ1 hμ2 ⊢
  exact ksum_odd_alg N Q P L hQ hL hμ1 hμ2

/-- `D(a,μ)` even, `D(θ,μ)` odd: `∑_± κ̂(a,θ_±,μ) π_{θ_±} = -N (π_μ - π_a)/Q`. -/
theorem kappa_sum_even {a μ : Node} {L : ℕ} (h1 : a.2 < L) (h2 : L < μ.2)
    (hodd : (L - a.2) % 2 = 1) (hD : (μ.2 - a.2) % 2 = 0) :
    ∑ ε : Bool, kappaHat a (ε, L) μ * nodePos (ε, L) =
      -(∏ m ∈ TA L μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) * (nodePos μ - nodePos a) /
        (∏ m ∈ TB L μ.2, ((L : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4)) := by
  have hj : (μ.2 - L) % 2 = 1 := by omega
  unfold kappaHat
  rw [Fintype.sum_bool, kappa_num, kappa_num, kappa_den h1 h2 hodd, kappa_den h1 h2 hodd]
  simp only [if_pos (show (μ.2 - (true, L).2) % 2 = 1 by simp only; omega),
    if_pos (show (μ.2 - (false, L).2) % 2 = 1 by simp only; omega),
    if_neg (show ¬ (μ.2 - a.2) % 2 = 1 by omega), mul_one, Bool.not_true, Bool.not_false,
    pos_true, pos_false]
  have hQ := TB_prod_ne (L := L) (U := μ.2)
  have hL : (L : ℚ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  field_simp
  ring

end Virasoro
