import Virasoro.Proofs.JantzenLevel
import Virasoro.Orbit

/-!
# The levels `ℓ^±_k` (proof of Theorem 5.9, paper.tex l.838–848)

Direct expansion gives, for the upper and lower signs respectively,
`ℓ⁺_{2j+1} - ℓ^±_{2j} = s(r+2jp), r(s+2jp')`,
`ℓ⁻_{2j+1} - ℓ^±_{2j} = (p-r)((2j+1)p'-s), (p'-s)((2j+1)p-r)`,
`ℓ^±_{2j+2} - ℓ⁺_{2j+1} = (p'-s)((2j+1)p+r), (p-r)((2j+1)p'+s)`,
`ℓ^±_{2j+2} - ℓ⁻_{2j+1} = r(2(j+1)p'-s), s(2(j+1)p-r)`, all positive.  Hence
`max(ℓ⁺_k, ℓ⁻_k) < ℓ_{k+1}` and `j_N(λ) = k` for `ℓ_k ≤ N < ℓ_{k+1}`.  Moreover
`ℓ⁺_{2j} - ℓ⁻_{2j} = 2j n₀ ≠ 0` and `ℓ⁺_{2j+1} - ℓ⁻_{2j+1} = (2j+1)(n₁ - pp') ≠ 0`.

Consumer: `thm_top_layer_of_subs` in `Virasoro/Proofs/Sec5TopLayer.lean`.
-/

namespace Virasoro

variable {p p' r s : ℕ}

theorem ellPlus_even_cast (hsp : s < p') (j : ℕ) :
    ((ellPlus p p' r s (2 * j) : ℕ) : ℤ) =
      (j : ℤ) * ((j : ℤ) * p * p' + ((p' : ℤ) * r - (p : ℤ) * s)) := by
  unfold ellPlus
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]
  refine Int.toNat_of_nonneg ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have h1 : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have h2 : (s : ℤ) ≤ p' := by exact_mod_cast hsp.le
    have h3 : (0 : ℤ) ≤ (p : ℤ) * p' := by positivity
    have h4 : (0 : ℤ) ≤ (p : ℤ) * (p' - s) := mul_nonneg (by positivity) (by linarith)
    have h5 : (0 : ℤ) ≤ (p' : ℤ) * r := by positivity
    have h6 : (0 : ℤ) ≤ ((j : ℤ) - 1) * (p * p') := mul_nonneg (by linarith) h3
    refine mul_nonneg (by positivity) ?_
    nlinarith

theorem ellMinus_even_cast (hrp : r < p) (j : ℕ) :
    ((ellMinus p p' r s (2 * j) : ℕ) : ℤ) =
      (j : ℤ) * ((j : ℤ) * p * p' - ((p' : ℤ) * r - (p : ℤ) * s)) := by
  unfold ellMinus
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]
  refine Int.toNat_of_nonneg ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have h1 : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have h2 : (r : ℤ) ≤ p := by exact_mod_cast hrp.le
    have h3 : (0 : ℤ) ≤ (p : ℤ) * p' := by positivity
    have h4 : (0 : ℤ) ≤ (p' : ℤ) * (p - r) := mul_nonneg (by positivity) (by linarith)
    have h5 : (0 : ℤ) ≤ (p : ℤ) * s := by positivity
    have h6 : (0 : ℤ) ≤ ((j : ℤ) - 1) * (p * p') := mul_nonneg (by linarith) h3
    refine mul_nonneg (by positivity) ?_
    nlinarith

theorem ellPlus_odd_cast (j : ℕ) :
    ((ellPlus p p' r s (2 * j + 1) : ℕ) : ℤ) =
      ((r : ℤ) + (j : ℤ) * p) * ((s : ℤ) + (j : ℤ) * p') := by
  unfold ellPlus
  rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]
  push_cast
  ring

theorem ellMinus_odd_cast (hrp : r < p) (hsp : s < p') (j : ℕ) :
    ((ellMinus p p' r s (2 * j + 1) : ℕ) : ℤ) =
      (((j : ℤ) + 1) * p - r) * (((j : ℤ) + 1) * p' - s) := by
  unfold ellMinus
  rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]
  have h1 : r ≤ (j + 1) * p := hrp.le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos j))
  have h2 : s ≤ (j + 1) * p' := hsp.le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos j))
  rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2]
  push_cast
  ring

/-- `max(ℓ⁺_k, ℓ⁻_k) < ℓ_{k+1}` for `k ≥ 1`. -/
theorem ell_max_lt_succ (hr : 0 < r) (hrp : r < p) (hs : 0 < s) (hsp : s < p') {k : ℕ}
    (hk : 1 ≤ k) :
    max (ellPlus p p' r s k) (ellMinus p p' r s k) < ellMin p p' r s (k + 1) := by
  have hR : (0 : ℤ) < r := by exact_mod_cast hr
  have hS : (0 : ℤ) < s := by exact_mod_cast hs
  have hRP : (0 : ℤ) < (p : ℤ) - r := by
    have : (r : ℤ) < p := by exact_mod_cast hrp
    linarith
  have hSP : (0 : ℤ) < (p' : ℤ) - s := by
    have : (s : ℤ) < p' := by exact_mod_cast hsp
    linarith
  have hP : (0 : ℤ) < p := by linarith
  have hP' : (0 : ℤ) < p' := by linarith
  have hjP : ∀ j : ℕ, (0 : ℤ) ≤ (j : ℤ) * p := fun j => by positivity
  have hjP' : ∀ j : ℕ, (0 : ℤ) ≤ (j : ℤ) * p' := fun j => by positivity
  rw [max_lt_iff, ellMin, lt_min_iff, lt_min_iff]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hj : (1 : ℤ) ≤ j := by
      have : 1 ≤ j := by omega
      exact_mod_cast this
    have e1 := ellPlus_even_cast (p := p) (r := r) hsp j
    have e2 := ellMinus_even_cast (p' := p') (s := s) hrp j
    have e3 := ellPlus_odd_cast (p := p) (p' := p') (r := r) (s := s) j
    have e4 := ellMinus_odd_cast hrp hsp j
    have a1 : (0 : ℤ) < (r : ℤ) + 2 * j * p := by linarith [hjP j, hjP' j]
    have a2 : (0 : ℤ) < (s : ℤ) + 2 * j * p' := by linarith [hjP j, hjP' j]
    have a3 : (0 : ℤ) < (2 * (j : ℤ) + 1) * p' - s := by linarith [hjP j, hjP' j]
    have a4 : (0 : ℤ) < (2 * (j : ℤ) + 1) * p - r := by linarith [hjP j, hjP' j]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have : ((ellPlus p p' r s (2 * j) : ℕ) : ℤ) < (ellPlus p p' r s (2 * j + 1) : ℕ) := by
        rw [e1, e3]
        linarith [mul_pos hS a1]
      exact_mod_cast this
    · have : ((ellPlus p p' r s (2 * j) : ℕ) : ℤ) < (ellMinus p p' r s (2 * j + 1) : ℕ) := by
        rw [e1, e4]
        linarith [mul_pos hRP a3]
      exact_mod_cast this
    · have : ((ellMinus p p' r s (2 * j) : ℕ) : ℤ) < (ellPlus p p' r s (2 * j + 1) : ℕ) := by
        rw [e2, e3]
        linarith [mul_pos hR a2]
      exact_mod_cast this
    · have : ((ellMinus p p' r s (2 * j) : ℕ) : ℤ) < (ellMinus p p' r s (2 * j + 1) : ℕ) := by
        rw [e2, e4]
        linarith [mul_pos hSP a4]
      exact_mod_cast this
  · have hj : (0 : ℤ) ≤ j := by positivity
    have e1 := ellPlus_odd_cast (p := p) (p' := p') (r := r) (s := s) j
    have e2 := ellMinus_odd_cast hrp hsp j
    have e3 := ellPlus_even_cast (p := p) (r := r) hsp (j + 1)
    have e4 := ellMinus_even_cast (p' := p') (s := s) hrp (j + 1)
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    push_cast at e3 e4
    have a1 : (0 : ℤ) < (2 * (j : ℤ) + 1) * p + r := by linarith [hjP j, hjP' j]
    have a2 : (0 : ℤ) < (2 * (j : ℤ) + 1) * p' + s := by linarith [hjP j, hjP' j]
    have a3 : (0 : ℤ) < 2 * ((j : ℤ) + 1) * p' - s := by linarith [hjP j, hjP' j]
    have a4 : (0 : ℤ) < 2 * ((j : ℤ) + 1) * p - r := by linarith [hjP j, hjP' j]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have : ((ellPlus p p' r s (2 * j + 1) : ℕ) : ℤ) < (ellPlus p p' r s (2 * (j + 1)) : ℕ) := by
        rw [e1, e3]
        linarith [mul_pos hSP a1]
      exact_mod_cast this
    · have : ((ellPlus p p' r s (2 * j + 1) : ℕ) : ℤ) < (ellMinus p p' r s (2 * (j + 1)) : ℕ) := by
        rw [e1, e4]
        linarith [mul_pos hRP a2]
      exact_mod_cast this
    · have : ((ellMinus p p' r s (2 * j + 1) : ℕ) : ℤ) < (ellPlus p p' r s (2 * (j + 1)) : ℕ) := by
        rw [e2, e3]
        linarith [mul_pos hR a3]
      exact_mod_cast this
    · have : ((ellMinus p p' r s (2 * j + 1) : ℕ) : ℤ) < (ellMinus p p' r s (2 * (j + 1)) : ℕ) := by
        rw [e2, e4]
        linarith [mul_pos hS a4]
      exact_mod_cast this

/-- `ℓ⁺_k ≠ ℓ⁻_k` for `k ≥ 1`. -/
theorem ellPlus_ne_ellMinus (hcop : Nat.Coprime p p') (hr : 0 < r) (hrp : r < p) (hsp : s < p')
    (hlt : p' * r + p * s < p * p') {k : ℕ} (hk : 1 ≤ k) :
    ellPlus p p' r s k ≠ ellMinus p p' r s k := by
  intro h
  have hc : ((ellPlus p p' r s k : ℕ) : ℤ) = (ellMinus p p' r s k : ℕ) := by exact_mod_cast h
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [ellPlus_even_cast hsp j, ellMinus_even_cast hrp j] at hc
    have h2 : (j : ℤ) * ((p' : ℤ) * r - (p : ℤ) * s) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have : j = 0 := by exact_mod_cast h3
      omega
    · have h4 : p' * r = p * s := by
        have : (p' : ℤ) * r = (p : ℤ) * s := by linarith
        exact_mod_cast this
      have h5 : p ∣ r := hcop.dvd_of_dvd_mul_left ⟨s, h4⟩
      have := Nat.le_of_dvd hr h5
      omega
  · rw [ellPlus_odd_cast j, ellMinus_odd_cast hrp hsp j] at hc
    have h1 : (0 : ℤ) < (p : ℤ) * p' - ((p' : ℤ) * r + (p : ℤ) * s) := by
      have : ((p' * r + p * s : ℕ) : ℤ) < ((p * p' : ℕ) : ℤ) := by exact_mod_cast hlt
      push_cast at this
      linarith
    have h2 : (0 : ℤ) < 2 * (j : ℤ) + 1 := by positivity
    linarith [mul_pos h2 h1]

theorem ellMin_mono (hr : 0 < r) (hrp : r < p) (hs : 0 < s) (hsp : s < p') {i : ℕ} (hi : 1 ≤ i)
    (m : ℕ) : ellMin p p' r s i ≤ ellMin p p' r s (i + m) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    have h1 := ell_max_lt_succ (p := p) (p' := p') hr hrp hs hsp (show 1 ≤ i + m by omega)
    have h2 : ellMin p p' r s (i + m) ≤
        max (ellPlus p p' r s (i + m)) (ellMinus p p' r s (i + m)) :=
      (min_le_left _ _).trans (le_max_left _ _)
    rw [← Nat.add_assoc]
    omega

/-- `j_N(λ) = k` for `ℓ_k ≤ N < ℓ_{k+1}`. -/
theorem jDepth_eq_of_range (hp : 2 ≤ p) (hp' : 2 ≤ p') (hr : 0 < r) (hrp : r < p) (hs : 0 < s)
    (hsp : s < p') {k N : ℕ} (hk : 1 ≤ k) (h1 : ellMin p p' r s k ≤ N)
    (h2 : N < ellMin p p' r s (k + 1)) : jDepth p p' r s N = k := by
  unfold jDepth
  apply le_antisymm
  · refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    by_contra hcon
    have hik : k + 1 ≤ i := by
      simp only [id] at hcon
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hik
    have h3 := ellMin_mono (p := p) (p' := p') hr hrp hs hsp (show 1 ≤ k + 1 by omega) m
    have h4 : ellMin p p' r s (k + 1 + m) ≤ N := hi.2
    omega
  · have h3 := le_ellPlus (r := r) hp hp' hr hs hsp hk
    have h4 := le_ellMinus (r := r) hp hp' hrp hs hsp hk
    have h5 : k ≤ N := by
      have : k ≤ ellMin p p' r s k := le_min h3 h4
      omega
    exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk, h5⟩, h1⟩)

end Virasoro
