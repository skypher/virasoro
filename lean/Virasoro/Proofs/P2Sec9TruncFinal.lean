import Virasoro.Proofs.P2Sec9Trunc

/-!
# Corollary 9.4 (collision-free single-index recursion), paper.tex l.1967–1979, 3123–3157
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- `Stmt_sub_truncated_recursion` (l.1975–1978, 3153–3157): the truncated recursion at `b⋆`
in both cases, from obstructions 1 and 3 and the vanishing of the inactive multipliers
(l.3125–3127). -/
theorem sub_truncated_recursion_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_sub_truncated_recursion := by
  intro p p' r s b hset
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  have hbi := dual_sq hp hp' hb
  refine ⟨fun m hm => ?_, fun k hk => ?_⟩
  · refine truncRec_of_obstructions hK hH hb0 1 (2 * (m : ℤ) + 1) (fun a => a.2 ≤ m) ?_ ?_ ?_
    · intro a p1 p2 hact
      have h := genP_inactive (R := a.1) (S := a.2) (k := 0) (m := m) p1 (by omega) true
        (RatFunc.X : RatFunc ℂ)
      simp only [sgnInt, if_true, Nat.cast_zero, mul_zero, zero_add] at h
      rw [genR, h, mul_zero]
    · intro a h1 h2 hact
      refine (evToK_genR hb0 a.1 a.2 _ _ fun pq hpq => ?_).1
      rw [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpq
      refine lin_ne_minimal hp hp' hcop hb _ _ (abs_lt.2 ⟨by omega, by omega⟩) ?_
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact hpq.2.1 (Prod.ext hcon.1 hcon.2)
    · intro a a' h1 h2 hact h1' h2' hact'
      exact no_secondary_collision hp hp' hcop hb h1 h2 h1' h2' (by omega) (by omega)
  · refine truncRec_of_obstructions hK hH hb0 (2 * (k : ℤ) + 1) 1 (fun a => a.1 ≤ k) ?_ ?_ ?_
    · intro a p1 p2 hact
      have h := genP_inactive (R := a.1) (S := a.2) (k := k) (m := 0) (by omega) p2 true
        (RatFunc.X : RatFunc ℂ)
      simp only [sgnInt, if_true, Nat.cast_zero, mul_zero, zero_add] at h
      rw [genR, h, mul_zero]
    · intro a h1 h2 hact
      refine (evToK_genR hb0 a.1 a.2 _ _ fun pq hpq => ?_).1
      rw [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpq
      have := lin_ne_minimal hp' hp hcop.symm hbi pq.2 pq.1 (abs_lt.2 ⟨by omega, by omega⟩) (by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hpq.2.1 (Prod.ext hcon.2 hcon.1))
      rw [inv_inv] at this
      rwa [add_comm]
    · intro a a' h1 h2 hact h1' h2' hact' heq
      have hneg : kacH (-(a.2 : ℤ)) (a.1 : ℤ) b⁻¹ = kacH (a.2 : ℤ) (-(a.1 : ℤ)) b⁻¹ := by
        simp only [kacH]; push_cast; ring
      refine no_secondary_collision hp' hp hcop.symm hbi h2 h1 h2' h1' (by omega) (by omega) ?_
      rw [← hneg, ← kacH_swap, ← kacH_swap]
      exact heq

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_sub_truncated_recursion := sub_truncated_recursion_of_cited hK hH

/-- Corollary 9.4.

Paper label: cor:collision-free -/
theorem cor_collision_free_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_cor_collision_free :=
  cor_collision_free_of_trunc (sub_truncated_recursion_of_cited hK hH)

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) : Stmt_cor_collision_free :=
  cor_collision_free_of_cited hK hH

end Virasoro.P2
