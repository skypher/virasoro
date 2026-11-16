import Virasoro.Proofs.Sec5Smith
import Virasoro.Proofs.SmithExist

/-!
# The Smith profile when the determinant valuation equals the nullity

If `ord_x det G = dim ker G(0) = k`, then (Lemma 5.1) every positive Smith exponent is `1`, so
the multiset of exponents is `{0, …, 0, 1, …, 1}` with `k` ones.
-/

namespace Virasoro

open PowerSeries Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem multiset_eq_zeros_ones (s : Multiset ℕ) {n k : ℕ} (hcard : s.card = n)
    (hpos : (s.filter fun e => 0 < e).card = k) (hone : ∀ e ∈ s, 0 < e → e = 1) :
    s = Multiset.replicate (n - k) 0 + Multiset.replicate k 1 := by
  have hsplit := Multiset.filter_add_not (fun e : ℕ => 0 < e) s
  have h1 : s.filter (fun e => 0 < e) = Multiset.replicate k 1 :=
    Multiset.eq_replicate.2 ⟨hpos, fun e he =>
      hone e (Multiset.mem_of_mem_filter he) (Multiset.of_mem_filter he)⟩
  have hc : (s.filter fun e => ¬ 0 < e).card = n - k := by
    have := congrArg Multiset.card hsplit
    rw [Multiset.card_add, hpos, hcard] at this
    omega
  have h2 : s.filter (fun e => ¬ 0 < e) = Multiset.replicate (n - k) 0 :=
    Multiset.eq_replicate.2 ⟨hc, fun e he => by
      have := Multiset.of_mem_filter he
      omega⟩
  rw [← hsplit, h1, h2, add_comm]

/-- If `ord_x det G = dim ker G(0) = k`, the Smith exponents are `k` ones and zeros. -/
theorem isSmith_of_order_eq_nullity {G : Matrix ι ι K⟦X⟧} (hdet : G.det ≠ 0) {k : ℕ}
    (hord : G.det.order = (k : ℕ∞)) (hker : finrank K (ker0 G) = k) :
    IsSmith G (Multiset.replicate (Fintype.card ι - k) 0 + Multiset.replicate k 1) := by
  obtain ⟨s, hs⟩ := exists_isSmith hdet
  obtain ⟨h1, h2, -⟩ := smith_main hs
  have hcard : s.card = Fintype.card ι := by
    obtain ⟨e, U, V, -, -, -, rfl⟩ := hs
    simp
  have hsum : s.sum = k := by
    rw [hord] at h1
    exact_mod_cast h1.symm
  have hpos : (s.filter fun e => 0 < e).card = k := by rw [← h2, hker]
  have hcount : s.sum = s.countP fun e => e ≠ 0 := by
    rw [hsum, Multiset.countP_eq_card_filter, ← hpos]
    congr 1
    exact Multiset.filter_congr fun e _ => Nat.pos_iff_ne_zero
  have hone : ∀ e ∈ s, 0 < e → e = 1 := fun e he h0 =>
    multiset_pos_eq_one s hcount e he (Nat.pos_iff_ne_zero.1 h0)
  rw [← multiset_eq_zeros_ones s hcard hpos hone]
  exact hs

end Virasoro
