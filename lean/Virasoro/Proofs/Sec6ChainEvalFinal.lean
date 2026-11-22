import Virasoro.Proofs.Sec6ChainEven
import Virasoro.Proofs.Sec6Chains

/-!
# Proposition 6.7: `Stmt_sub_layer_chain_eval` (paper.tex l.1150–1173)

The four cases (odd and even `k`, both signs) give the frozen sub-statement; Proposition 6.7
then rests on `Stmt_sub_layer_chain_limit` alone.
-/

namespace Virasoro

open ChainEval

/-- `Stmt_sub_layer_chain_eval` (paper.tex l.1150–1173). -/
theorem sub_layer_chain_eval : Stmt_sub_layer_chain_eval := by
  intro p p' r s hp hp' hcop hr hrp hs hsp hlt k hk
  have h : Setup p p' r s := ⟨hp, hp', hcop, hr, hrp, hs, hsp⟩
  have hlt' : 2 * n1 p p' r s < N0 p p' := by
    have : ((p' * r + p * s : ℕ) : ℤ) < ((p * p' : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at this
    unfold n1 N0
    linarith
  have hρ : (-((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p))) = rho p p' r s := by
    unfold rho n0
    push_cast
    ring
  dsimp only
  rw [hρ]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (q + 1) = 2 * q + 2 by ring]
    constructor
    · intro a e he hT
      exact h.eval_even q 1 (Or.inl rfl) _
        (h.ell_even q 1 (Or.inl rfl) _ (ellPlus_even p p' r s q h)) a e he hT
    · intro a e he hT
      rw [Even.neg_pow ⟨q + 1, by ring⟩]
      exact h.eval_even q (-1) (Or.inr rfl) _
        (h.ell_even q (-1) (Or.inr rfl) _ (ellMinus_even p p' r s q h)) a e he hT
  · constructor
    · intro a e he hT
      exact h.eval_plus_odd hlt' j a e he hT
    · intro a e he hT
      exact h.eval_minus_odd hlt' j a e he hT

/-- Proposition 6.7 from `Stmt_sub_layer_chain_limit` and the cited injectivity. -/
theorem prop_layer_coefficients_of_limit (hI : Cited_VermaHomInjective)
    (h1 : Stmt_sub_layer_chain_limit) : Stmt_prop_layer_coefficients :=
  prop_layer_coefficients_of_chain hI h1 sub_layer_chain_eval

end Virasoro
