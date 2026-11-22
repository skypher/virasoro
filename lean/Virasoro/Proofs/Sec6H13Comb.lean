import Virasoro.Proofs.Sec6H13IntA
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Int.NatAbs

/-!
# Proposition 6.8(i): the two combinatorial facts (paper.tex l.1270–1271, 1283–1285)

For `λ ⊢ N` with multiplicities `m_n`: `|D_λ| = ∏_n m_n! n^{m_n}` divides `N!` (Lagrange's theorem
for the centralizer of cycle type `λ` in `S_N`, in the form of Mathlib's count of the
permutations of a given cycle type), and `K_λ = 2^{ℓ(λ)} ∏_n m_n! n^{m_n}` for the constant
`K_λ = topNat λ λ` of the determinant formula.
-/

namespace Virasoro.H13C

open Virasoro Virasoro.TFock

/-- `∏_n m_n!` for the multiset with multiplicities `m_n`. -/
def facs (s : Multiset ℕ) : ℕ := ∏ n ∈ s.toFinset, (s.count n).factorial

theorem facs_eq_of_subset (s : Multiset ℕ) (T : Finset ℕ) (h : s.toFinset ⊆ T) :
    facs s = ∏ n ∈ T, (s.count n).factorial := by
  unfold facs
  refine Finset.prod_subset h fun n _ hn => ?_
  rw [Multiset.mem_toFinset] at hn
  rw [Multiset.count_eq_zero_of_notMem hn, Nat.factorial_zero]

theorem facs_cons (y : ℕ) (s : Multiset ℕ) : facs (y ::ₘ s) = (s.count y + 1) * facs s := by
  classical
  have hy : y ∈ (y ::ₘ s).toFinset := by simp
  have hsub : s.toFinset ⊆ (y ::ₘ s).toFinset := by
    intro n hn
    rw [Multiset.mem_toFinset] at hn ⊢
    exact Multiset.mem_cons_of_mem hn
  rw [facs_eq_of_subset s _ hsub]
  unfold facs
  rw [← Finset.mul_prod_erase _ _ hy, ← Finset.mul_prod_erase _ _ hy, Multiset.count_cons_self,
    Nat.factorial_succ, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun n hn => ?_
  rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hn)]

/-! ### The constant `K_λ` (l.1257, l.1270–1271) -/

theorem delOne_length_count (k : ℕ) : ∀ w : List ℕ, (delOne k w).length = w.count k
  | [] => by simp [delOne]
  | y :: w => by
    rw [delOne, List.length_append, List.length_map, delOne_length_count k w]
    by_cases h : y = k
    · subst h
      rw [if_pos rfl, List.count_cons_self, List.length_singleton]
      omega
    · rw [if_neg h, List.count_cons_of_ne h, List.length_nil]
      omega

/-- The weighted matching count of a word with a rearrangement of itself:
`2^{ℓ} ∏ y_i ∏_n m_n!`. -/
theorem topNat_perm : ∀ (Y w : List ℕ), List.Perm w Y →
    topNat Y w = 2 ^ Y.length * Y.prod * facs (Y : Multiset ℕ)
  | [], w, _ => by simp [topNat, facs]
  | y :: Y, w, h => by
    have h1 : ∀ u ∈ delOne y w,
        2 * y * topNat Y u = 2 * y * (2 ^ Y.length * Y.prod * facs (Y : Multiset ℕ)) := by
      intro u hu
      have hp : List.Perm u Y := List.Perm.cons_inv ((delOne_perm hu).symm.trans h)
      rw [topNat_perm Y u hp]
    rw [topNat, List.map_congr_left h1, List.map_const', List.sum_replicate, delOne_length_count,
      h.count_eq, List.count_cons_self, smul_eq_mul, ← Multiset.cons_coe, facs_cons,
      Multiset.coe_count, List.length_cons, List.prod_cons]
    ring

/-! ### `|D_λ| = ∏_n m_n! n^{m_n}` (l.1267) -/

theorem natAbs_wgt (e : ℕ+ →₀ ℕ) :
    (wgt e).natAbs = e.prod fun n a => a.factorial * (n : ℕ) ^ a := by
  unfold wgt Finsupp.prod
  change Int.natAbsHom _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  change Int.natAbs _ = _
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem natAbs_Dm {N : ℕ} (Z : Nat.Partition N) :
    (Dm Z).natAbs = facs Z.parts * Z.parts.prod := by
  classical
  set P : Multiset ℕ+ := Z.parts.map Nat.toPNat' with hP
  have h2 : P.map (fun m : ℕ+ => (m : ℕ)) = Z.parts := by
    rw [hP, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id Z.parts]
    apply Multiset.map_congr rfl
    intro m hm
    exact PNat.toPNat'_coe (Z.parts_pos hm)
  have h3 : facs (P.map fun m : ℕ+ => (m : ℕ)) = ∏ a ∈ P.toFinset, (P.count a).factorial := by
    unfold facs
    rw [Multiset.toFinset_map, Finset.prod_image (fun a _ b _ h => PNat.coe_injective h)]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Multiset.count_map_eq_count' _ _ PNat.coe_injective]
  rw [Dm, natAbs_wgt, expOf, ← hP, Finsupp.prod, Multiset.toFinsupp_support,
    Finset.prod_mul_distrib, ← h2, Finset.prod_multiset_map_count, h3]
  simp only [Multiset.toFinsupp_apply]

/-! ### Lagrange's theorem for the centralizer (l.1283–1285) -/

/-- `∏_n m_n! n^{m_n} ∣ N!`: the index of the centralizer of a permutation of cycle type `λ` in
`S_N` is the number of permutations of that cycle type. -/
theorem facs_mul_prod_dvd (m : Multiset ℕ) (hpos : ∀ a ∈ m, 0 < a) :
    facs m * m.prod ∣ m.sum.factorial := by
  classical
  set m' : Multiset ℕ := m.filter (2 ≤ ·) with hm'
  have h1 : m.filter (fun a => ¬ 2 ≤ a) = Multiset.replicate (m.count 1) 1 := by
    rw [← Multiset.filter_eq']
    refine Multiset.filter_congr fun a ha => ?_
    have := hpos a ha
    omega
  have hdec : m' + Multiset.replicate (m.count 1) 1 = m := by
    rw [← h1]
    exact Multiset.filter_add_not _ _
  have hsum : m.sum = m'.sum + m.count 1 := by
    conv_lhs => rw [← hdec]
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
  have hprod : m.prod = m'.prod := by
    conv_lhs => rw [← hdec]
    rw [Multiset.prod_add, Multiset.prod_replicate, one_pow, mul_one]
  have h1n : (1 : ℕ) ∉ m'.toFinset := by
    rw [Multiset.mem_toFinset, hm', Multiset.mem_filter]
    rintro ⟨_, h⟩
    omega
  have hsub : m.toFinset ⊆ insert 1 m'.toFinset := by
    intro n hn
    rw [Multiset.mem_toFinset] at hn
    rw [Finset.mem_insert, Multiset.mem_toFinset, hm', Multiset.mem_filter]
    have := hpos n hn
    by_cases h : n = 1
    · left; exact h
    · right; exact ⟨hn, by omega⟩
  have hfacs : facs m = (m.count 1).factorial * facs m' := by
    rw [facs_eq_of_subset m _ hsub, Finset.prod_insert h1n]
    congr 1
    unfold facs
    refine Finset.prod_congr rfl fun n hn => ?_
    rw [Multiset.mem_toFinset, hm', Multiset.mem_filter] at hn
    rw [hm', Multiset.count_filter_of_pos hn.2]
  have hc := Equiv.Perm.card_of_cycleType_mul_eq (Fin m.sum) m'
  rw [if_pos ⟨by rw [Fintype.card_fin]; omega, fun a ha => (Multiset.mem_filter.1 ha).2⟩,
    Fintype.card_fin] at hc
  have h3 : m.sum - m'.sum = m.count 1 := by omega
  rw [h3] at hc
  rw [← hc, hfacs, hprod]
  unfold facs
  exact Dvd.dvd.mul_left (dvd_of_eq (by ring)) _

end Virasoro.H13C

namespace Virasoro

open H13C

/-- `∏_n m_n! n^{m_n} ∣ N!` (paper.tex l.1283–1285). -/
theorem sub_h13_lagrange : Stmt_sub_h13_lagrange := by
  intro N Z
  rw [← Int.natAbs_dvd, natAbs_Dm, Int.natCast_dvd_natCast]
  have h := facs_mul_prod_dvd Z.parts fun a ha => Z.parts_pos ha
  rwa [Z.parts_sum] at h

example : Stmt_sub_h13_lagrange := sub_h13_lagrange

/-- `|det D_N| = 2^{−∑ℓ(λ)} K_N` (paper.tex l.1270–1271). -/
theorem sub_h13_detD : Stmt_sub_h13_detD := by
  intro N
  rw [kacK, lenSum, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum, Nat.cast_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun Y _ => ?_
  have hw : ((Y.word : List ℕ) : Multiset ℕ) = Y.parts := by
    rw [Nat.Partition.word, Multiset.sort_eq]
  have hpr : Y.word.prod = Y.parts.prod := by rw [← hw, Multiset.prod_coe]
  rw [topNat_perm Y.word Y.word (List.Perm.refl _), Int.abs_eq_natAbs, natAbs_Dm, hw, hpr]
  push_cast
  ring

example : Stmt_sub_h13_detD := sub_h13_detD

end Virasoro
