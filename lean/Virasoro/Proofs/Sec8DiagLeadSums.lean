import Virasoro.Proofs.Sec8DiagChains

/-!
# Lemma 8.5(i): leading terms of the chains and the vanishing moments
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

section Sums

variable (hset : MinimalSetting p p' r s b)
include hset

/-- The leading term of `P^{(k)}_γ δ_{g_n}^j/j!`. -/
theorem chainProd_lead {a μ : Node} {γ : List Node} (hγ : γ ∈ nodeChains a μ) (k j : ℕ)
    (hk : 1 ≤ k) :
    LV (chainProd p p' r s b k j γ) ((k : ℤ) + j - (μ.2 - a.2))
      (chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j /
        (j.factorial : Kd)) := by
  obtain ⟨x, l, rfl, hlt, hodd, hok⟩ := stepsOK_of_mem hγ
  have hR := lem_node_poles p p' r s b hset a x hlt hodd
  have hRv : LV (nodeR p p' r s b a x) (1 - ((x.2 : ℤ) - a.2)) (nodeRho p p' r s b a x) :=
    ⟨by simpa [OrdGE] using hR.1, rfl⟩
  have hd := (lv_nodeDel hset hlt hodd).pow (k - 1)
  have ht := tail_lead hset j μ l a x hok hlt hodd
  have h := (hRv.mul hd).mul ht
  simp only [chainProd]
  refine h.congr ?_ ?_
  · have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [this]; ring
  · simp only [chainW, chainRho, chainH0]
    ring

/-- The coefficient of `t^{k+j-D}` in `c^{(k)}_{a→μ,j}` is the sum of the leading terms. -/
theorem nodeChain_coeff {a μ : Node} (haμ : a.2 < μ.2) (k j : ℕ) (hk : 1 ≤ k) :
    (nodeChain p p' r s b a μ k j).coeff ((k : ℤ) + j - (μ.2 - a.2)) =
      ∑ γ ∈ nodeChains a μ, chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) *
        chainHn p p' r s b γ ^ j / (j.factorial : Kd) := by
  rw [head_bridge hset haμ k j, HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun γ hγ => (chainProd_lead hset hγ k j hk).2

end Sums

/-- Lemma 8.5(i), the vanishing and the value (from Lemma 7.13). -/
theorem node_leading_sums (hreg : Stmt_lem_chain_regular) (hset : MinimalSetting p p' r s b)
    {a μ : Node} (haμ : a.2 < μ.2) :
    (∀ k j : ℕ, 1 ≤ k → k + j < μ.2 - a.2 →
      ∑ γ ∈ nodeChains a μ,
        chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j = 0) ∧
    (∀ k j : ℕ, 1 ≤ k → k + j = μ.2 - a.2 →
      (nodeChain p p' r s b a μ k j).coeff 0 =
        (∑ γ ∈ nodeChains a μ,
          chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j) /
          (j.factorial : Kd)) := by
  have hb0 := b_ne_zero_of hset
  have hlev := nodeLev_lt_of_lt hset haμ
  have hfact : ∀ j : ℕ, (j.factorial : Kd) ≠ 0 := fun j => by
    exact_mod_cast (Nat.factorial_pos j).ne'
  refine ⟨fun k j hk hkj => ?_, fun k j hk hkj => ?_⟩
  · have hr := hreg b hb0 (nodeWt p p' r s a) (nodeLev p p' r s μ - nodeLev p p' r s a) k j
      (by omega) hk
    have hz : (nodeChain p p' r s b a μ k j).coeff ((k : ℤ) + j - (μ.2 - a.2)) = 0 := by
      have hneg : (k : ℤ) + j - (μ.2 - a.2) < 0 := by omega
      exact (show OrdGE (nodeChain p p' r s b a μ k j) 0 by unfold nodeChain; simpa [OrdGE] using hr).coeff_eq_zero
        hneg
    rw [nodeChain_coeff hset haμ k j hk] at hz
    have : (∑ γ ∈ nodeChains a μ, chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) *
        chainHn p p' r s b γ ^ j) / (j.factorial : Kd) = 0 := by
      rw [Finset.sum_div]; exact hz
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h (hfact j)
  · have h0 : (k : ℤ) + j - (μ.2 - a.2) = 0 := by omega
    have := nodeChain_coeff hset haμ k j hk
    rw [h0] at this
    rw [this, Finset.sum_div]

end Virasoro
