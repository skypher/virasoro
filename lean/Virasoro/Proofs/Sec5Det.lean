import Virasoro.Proofs.GramDet
import Virasoro.Proofs.Sec5TwoStep

/-!
# Proofs: Corollary 5.4 (determinant multiplicity versus pole order)
-/

namespace Virasoro

open Polynomial

theorem multiset_filter_pos_sum (s : Multiset ℕ) : (s.filter fun e => 0 < e).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    by_cases h : 0 < a
    · rw [Multiset.filter_cons_of_pos (p := fun e : ℕ => 0 < e) t h, Multiset.sum_cons,
        Multiset.sum_cons, ih]
    · rw [Multiset.filter_cons_of_neg (p := fun e : ℕ => 0 < e) t h, Multiset.sum_cons, ih]
      omega

/-- Paper label: cor:det-overcounts -/
theorem cor_det_overcounts : Stmt_cor_det_overcounts := by
  intro b _ N lam _ s hs
  obtain ⟨h1, -, h3⟩ := smith_main hs
  refine ⟨?_, h3⟩
  rw [gramLocal_det_order] at h1
  rw [multiset_filter_pos_sum]
  exact_mod_cast h1

example : Stmt_cor_det_overcounts := cor_det_overcounts

end Virasoro
